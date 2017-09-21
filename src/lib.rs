extern crate libc;

use std::cmp;
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct PrefixShareableString(*mut u8);
impl PrefixShareableString {
    pub fn new(s: &str) -> Self {
        assert!(s.len() <= 0xFFFF);

        let ptr = unsafe { libc::malloc(8 + s.len()) } as *mut u8;
        assert_ne!(ptr, ptr::null_mut());

        let header = Header::new(s.len() as u16, 0);
        unsafe {
            ptr::write(ptr as _, header);
            ptr::copy_nonoverlapping(s.as_ptr(), ptr.offset(8), s.len());
        }

        PrefixShareableString(ptr)
    }
    pub fn with_base(s: &str, mut base: &Self) -> Self {
        assert!(s.len() <= 0xFFFF);

        let common_prefix = s.bytes()
            .zip(base.bytes())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| cmp::min(s.len(), base.len()));

        if let Some(parent) = base.base() {
            if common_prefix == base.header().offset() as usize {
                base = parent;
            }
        }

        if common_prefix == s.len() && s.len() == base.len() {
            base.clone()
        } else if common_prefix <= 8 {
            Self::new(s)
        } else {
            let ptr = unsafe { libc::malloc(8 + mem::size_of::<usize>() + s.len()) } as *mut u8;
            assert_ne!(ptr, ptr::null_mut());

            base.header().acquire();
            let header = Header::new(s.len() as u16, common_prefix as u16);
            unsafe {
                ptr::write(ptr as _, header);
                ptr::write(ptr.offset(8) as _, base.0);
                ptr::copy_nonoverlapping(
                    s.as_ptr().offset(common_prefix as isize),
                    ptr.offset(8 + mem::size_of::<usize>() as isize),
                    s.len() - common_prefix,
                );
            }

            PrefixShareableString(ptr)
        }
    }

    pub fn header(&self) -> &Header {
        unsafe { mem::transmute(&*self.0) }
    }
    pub fn len(&self) -> usize {
        self.header().len() as usize
    }
    pub fn suffix(&self) -> &str {
        unsafe {
            let ptr = self.0.offset(self.suffix_offset() as isize);
            let size = (self.header().len() - self.header().offset()) as usize;
            let slice = std::slice::from_raw_parts(ptr, size);
            std::str::from_utf8_unchecked(slice)
        }
    }
    fn suffix_offset(&self) -> usize {
        if self.header().offset() == 0 {
            8
        } else {
            8 + mem::size_of::<usize>()
        }
    }
    pub fn base(&self) -> Option<&Self> {
        if self.header().offset() == 0 {
            None
        } else {
            let base = unsafe { mem::transmute(self.0.offset(8)) };
            Some(base)
        }
    }
    pub fn bytes(&self) -> Bytes {
        if let Some(base) = self.base() {
            let prefix_len = self.header().offset() as usize;
            Bytes(Box::new(
                base.bytes().take(prefix_len).chain(self.suffix().bytes()),
            ))
        } else {
            Bytes(Box::new(self.suffix().bytes()))
        }
    }
    fn release(&self) {
        if self.header().release() {
            if let Some(base) = self.base() {
                base.release();
            }
            unsafe { libc::free(self.0 as *mut libc::c_void) };
        }
    }
}
impl Clone for PrefixShareableString {
    fn clone(&self) -> Self {
        self.header().acquire();
        PrefixShareableString(self.0)
    }
}
impl Drop for PrefixShareableString {
    fn drop(&mut self) {
        self.release()
    }
}

pub struct Bytes<'a>(Box<Iterator<Item = u8> + 'a>);
impl<'a> Iterator for Bytes<'a> {
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

#[derive(Debug)]
#[cfg(target_pointer_width = "64")]
pub struct Header {
    value: AtomicUsize,
}
#[cfg(target_pointer_width = "64")]
impl Header {
    pub fn new(len: u16, offset: u16) -> Self {
        let value = AtomicUsize::new(1 + ((len as usize) << 32) + ((offset as usize) << 48));
        Header { value }
    }

    pub fn acquire(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }
    pub fn release(&self) -> bool {
        (self.value.fetch_sub(1, Ordering::SeqCst) & 0xFFFF_FFFF) == 1
    }

    pub fn rc(&self) -> u32 {
        self.value.load(Ordering::SeqCst) as u32
    }
    pub fn len(&self) -> u16 {
        (self.value.load(Ordering::SeqCst) >> 32) as u16
    }
    pub fn offset(&self) -> u16 {
        (self.value.load(Ordering::SeqCst) >> 48) as u16
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let s0 = PrefixShareableString::new("0123456789");
        assert_eq!(s0.len(), 10);
        assert_eq!(s0.suffix(), "0123456789");
        assert!(s0.bytes().eq("0123456789".bytes()));
        {
            let s1 = PrefixShareableString::with_base("012345678abcd", &s0);
            assert_eq!(s1.len(), 13);
            assert_eq!(s1.suffix(), "abcd");
            assert!(s1.bytes().eq("012345678abcd".bytes()));
            assert_eq!(s0.header().rc(), 2);
            assert_eq!(s1.header().rc(), 1);

            let s2 = PrefixShareableString::with_base("012345678ABCD", &s1);
            assert_eq!(s2.len(), 13);
            assert_eq!(s2.suffix(), "ABCD");
            assert!(s2.bytes().eq("012345678ABCD".bytes()));
            assert_eq!(s0.header().rc(), 3);
            assert_eq!(s2.header().rc(), 1);
        }
        assert_eq!(s0.header().rc(), 1);
    }
}
