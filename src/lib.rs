#![crate_type = "lib"]
#![feature(const_fn)]
#![warn(missing_docs)]

//! Synchronization primitives based on spinning

#![no_std]

#[cfg(test)]
#[macro_use]
extern crate std;

pub use mutex::*;
pub use once::*;
pub use rw_lock::*;
pub use scheduler::*;

mod mutex;
mod once;
mod rw_lock;
mod scheduler;
