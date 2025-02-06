#![no_std]
extern crate alloc;
// use core::range::Range;

use core::ops::Range;

use alloc::boxed::Box;
use embedded_io::ErrorType;

pub unsafe trait Emitter: ErrorType {
    ///SAFETY: the memory addresses in `a`'s range may eventually be unable to be written to, if this method succeeds. Because of that, NO mutable reference to that range of data should be given out EVER, as they ALL are invalidated by a successful call. Failed calls MUST NOT impact memory
    unsafe fn emit(&mut self, a: Range<u64>) -> Result<(), Self::Error>;
}
pub trait Bake {
    fn bake<E: Emitter>(self: Box<Self>, m: &mut E)
        -> Result<&'static Self, (E::Error, Box<Self>)>;
}
impl<T> Bake for T {
    fn bake<E: Emitter>(
        self: Box<Self>,
        m: &mut E,
    ) -> Result<&'static Self, (E::Error, Box<Self>)> {
        let l = Box::leak(self);
        match unsafe {
            m.emit(
                (l as *mut Self as usize as u64)
                    ..((l as *mut Self as usize + size_of::<Self>()) as u64),
            )
        } {
            Ok(_) => Ok(l),
            Err(e) => Err((e, unsafe { Box::from_raw(l as *mut Self) })),
        }
    }
}
impl<T> Bake for [T] {
    fn bake<E: Emitter>(
        self: Box<Self>,
        m: &mut E,
    ) -> Result<&'static Self, (E::Error, Box<Self>)> {
        let l = Box::leak(self);
        match unsafe {
            m.emit(
                (l.as_mut_ptr() as usize as u64)
                    ..((l.as_mut_ptr() as usize + size_of::<T>() * l.len()) as u64),
            )
        } {
            Ok(_) => Ok(l),
            Err(e) => Err((e, unsafe { Box::from_raw(l as *mut Self) })),
        }
    }
}
