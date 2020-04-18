use core::sync::atomic::{AtomicBool, Ordering, spin_loop_hint as cpu_relax};
use core::cell::UnsafeCell;
use core::marker::{Sync, PhantomData};
use core::ops::{Drop, Deref, DerefMut};
use core::fmt;
use core::option::Option::{self, None, Some};
use core::default::Default;
use scheduler::SchedulerInfluence;

/// This type provides MUTual EXclusion based on spinning.
///
/// # Description
///
/// The behaviour of these lock is similar to their namesakes in `std::sync`. they
/// differ on the following:
///
/// - The lock will not be poisoned in case of failure;
///
/// # Simple examples
///
/// ```
/// use spin;
/// use spin::NoOpSchedulerInfluence;
/// let spin_mutex: spin::Mutex<_, NoOpSchedulerInfluence> = spin::Mutex::new(0);
///
/// // Modify the data
/// {
///     let mut data = spin_mutex.lock();
///     *data = 2;
/// }
///
/// // Read the data
/// let answer =
/// {
///     let data = spin_mutex.lock();
///     *data
/// };
///
/// assert_eq!(answer, 2);
/// ```
///
/// # Thread-safety example
///
/// ```
/// use spin;
/// use std::sync::{Arc, Barrier};
/// use spin::NoOpSchedulerInfluence;
///
/// let numthreads = 1000;
/// let spin_mutex: Arc<spin::Mutex<_, NoOpSchedulerInfluence>> = Arc::new(spin::Mutex::new(0));
///
/// // We use a barrier to ensure the readout happens after all writing
/// let barrier = Arc::new(Barrier::new(numthreads + 1));
///
/// for _ in (0..numthreads)
/// {
///     let my_barrier = barrier.clone();
///     let my_lock = spin_mutex.clone();
///     std::thread::spawn(move||
///     {
///         let mut guard = my_lock.lock();
///         *guard += 1;
///
///         // Release the lock to prevent a deadlock
///         drop(guard);
///         my_barrier.wait();
///     });
/// }
///
/// barrier.wait();
///
/// let answer = { *spin_mutex.lock() };
/// assert_eq!(answer, numthreads);
/// ```
pub struct Mutex<T: ?Sized, S: SchedulerInfluence>
{
    lock: AtomicBool,
    _marker: PhantomData<S>,
    data: UnsafeCell<T>,
}

/// A guard to which the protected data can be accessed
///
/// When the guard falls out of scope it will release the lock.
#[derive(Debug)]
pub struct MutexGuard<'a, T: ?Sized + 'a, S: SchedulerInfluence>
{
    lock: &'a AtomicBool,
    data: &'a mut T,
    state: S,
}

// Same unsafe impls as `std::sync::Mutex`
unsafe impl<T: ?Sized + Send, S: SchedulerInfluence> Sync for Mutex<T, S> {}
unsafe impl<T: ?Sized + Send, S: SchedulerInfluence> Send for Mutex<T, S> {}

impl<T, S: SchedulerInfluence> Mutex<T, S>
{
    /// Creates a new spinlock wrapping the supplied data.
    ///
    /// May be used statically:
    ///
    /// ```
    /// use spin::{self, NoOpSchedulerInfluence};
    ///
    /// static MUTEX: spin::Mutex<(), NoOpSchedulerInfluence> = spin::Mutex::new(());
    ///
    /// fn demo() {
    ///     let lock = MUTEX.lock();
    ///     // do something with lock
    ///     drop(lock);
    /// }
    /// ```
    pub const fn new(user_data: T) -> Mutex<T, S>
    {
        Mutex
        {
            lock: AtomicBool::new(false),
            _marker: PhantomData,
            data: UnsafeCell::new(user_data),
        }
    }

    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T {
        // We know statically that there are no outstanding references to
        // `self` so there's no need to lock.
        let Mutex { data, .. } = self;
        data.into_inner()
    }
}

impl<T: ?Sized, S: SchedulerInfluence> Mutex<T, S>
{
    fn obtain_lock(&self) -> S
    {
        let mut state = S::activate();

        while self.lock.compare_and_swap(false, true, Ordering::Acquire) != false
        {
            drop(state);

            // Wait until the lock looks unlocked before retrying
            while self.lock.load(Ordering::Relaxed)
            {
                cpu_relax();
            }

            state = S::activate();
        }

        state
    }

    /// Locks the spinlock and returns a guard.
    ///
    /// The returned value may be dereferenced for data access
    /// and the lock will be dropped when the guard falls out of scope.
    ///
    /// ```
    /// use spin::NoOpSchedulerInfluence;
    /// let mylock: spin::Mutex<_, NoOpSchedulerInfluence> = spin::Mutex::new(0);
    /// {
    ///     let mut data = mylock.lock();
    ///     // The lock is now locked and the data can be accessed
    ///     *data += 1;
    ///     // The lock is implicitly dropped
    /// }
    ///
    /// ```
    pub fn lock(&self) -> MutexGuard<T, S>
    {
        let state = self.obtain_lock();
        MutexGuard
        {
            lock: &self.lock,
            data: unsafe { &mut *self.data.get() },
            state,
        }
    }

    /// Force unlock the spinlock.
    ///
    /// This is *extremely* unsafe if the lock is not held by the current
    /// thread. However, this can be useful in some instances for exposing the
    /// lock to FFI that doesn't know how to deal with RAII.
    ///
    /// If the lock isn't held, this is a no-op.
    pub unsafe fn force_unlock(&self) {
        self.lock.store(false, Ordering::Release);
    }

    /// Tries to lock the mutex. If it is already locked, it will return None. Otherwise it returns
    /// a guard within Some.
    pub fn try_lock(&self) -> Option<MutexGuard<T, S>>
    {
        let state = S::activate();
        if self.lock.compare_and_swap(false, true, Ordering::Acquire) == false
        {
            Some(
                MutexGuard {
                    lock: &self.lock,
                    data: unsafe { &mut *self.data.get() },
                    state,
                }
            )
        }
        else
        {
            None
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place -- the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use spin::NoOpSchedulerInfluence;
    /// let mut my_lock: spin::Mutex<_, NoOpSchedulerInfluence> = spin::Mutex::new(0);
    /// *my_lock.get_mut() = 10;
    /// assert_eq!(*my_lock.lock(), 10);
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        // We know statically that there are no other references to `self`, so
        // there's no need to lock the inner mutex.
        unsafe { &mut *self.data.get() }
    }

    /// Returns a reference to the cell containing the underlying data.
    pub unsafe fn get_cell(&self) -> &UnsafeCell<T> {
        &self.data
    }
}

impl<T: ?Sized + fmt::Debug, S: SchedulerInfluence> fmt::Debug for Mutex<T, S>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result
    {
        match self.try_lock()
        {
            Some(guard) => write!(f, "Mutex {{ data: ")
				.and_then(|()| (&*guard).fmt(f))
				.and_then(|()| write!(f, "}}")),
            None => write!(f, "Mutex {{ <locked> }}"),
        }
    }
}

impl<T: ?Sized + Default, S: SchedulerInfluence> Default for Mutex<T, S> {
    fn default() -> Mutex<T, S> {
        Mutex::new(Default::default())
    }
}

impl<'a, T: ?Sized, S: SchedulerInfluence> Deref for MutexGuard<'a, T, S>
{
    type Target = T;
    fn deref(&self) -> &T { &*self.data }
}

impl<'a, T: ?Sized, S: SchedulerInfluence> DerefMut for MutexGuard<'a, T, S>
{
    fn deref_mut(&mut self) -> &mut T { &mut *self.data }
}

impl<'a, T: ?Sized, S: SchedulerInfluence> Drop for MutexGuard<'a, T, S>
{
    /// The dropping of the MutexGuard will release the lock it was created from.
    fn drop(&mut self)
    {
        self.lock.store(false, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use std::prelude::v1::*;

    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    use super::*;
    use NoOpSchedulerInfluence;

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    #[test]
    fn smoke() {
        let m: Mutex<(), NoOpSchedulerInfluence> = Mutex::new(());
        drop(m.lock());
        drop(m.lock());
    }

    #[test]
    fn lots_and_lots() {
        static M: Mutex<(), NoOpSchedulerInfluence>  = Mutex::new(());
        static mut CNT: u32 = 0;
        const J: u32 = 1000;
        const K: u32 = 3;

        fn inc() {
            for _ in 0..J {
                unsafe {
                    let _g = M.lock();
                    CNT += 1;
                }
            }
        }

        let (tx, rx) = channel();
        for _ in 0..K {
            let tx2 = tx.clone();
            thread::spawn(move|| { inc(); tx2.send(()).unwrap(); });
            let tx2 = tx.clone();
            thread::spawn(move|| { inc(); tx2.send(()).unwrap(); });
        }

        drop(tx);
        for _ in 0..2 * K {
            rx.recv().unwrap();
        }
        assert_eq!(unsafe {CNT}, J * K * 2);
    }

    #[test]
    fn try_lock() {
        let mutex: Mutex<i32, NoOpSchedulerInfluence> = Mutex::new(42);

        // First lock succeeds
        let a = mutex.try_lock();
        assert_eq!(a.as_ref().map(|r| **r), Some(42));

        // Additional lock failes
        let b = mutex.try_lock();
        assert!(b.is_none());

        // After dropping lock, it succeeds again
        ::core::mem::drop(a);
        let c = mutex.try_lock();
        assert_eq!(c.as_ref().map(|r| **r), Some(42));
    }

    #[test]
    fn test_into_inner() {
        let m: Mutex<NonCopy, NoOpSchedulerInfluence> = Mutex::new(NonCopy(10));
        assert_eq!(m.into_inner(), NonCopy(10));
    }

    #[test]
    fn test_into_inner_drop() {
        struct Foo(Arc<AtomicUsize>);
        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let num_drops = Arc::new(AtomicUsize::new(0));
        let m: Mutex<Foo, NoOpSchedulerInfluence> = Mutex::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = m.into_inner();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_mutex_arc_nested() {
        // Tests nested mutexes and access
        // to underlying data.
        let arc = Arc::new(Mutex::<i32, NoOpSchedulerInfluence>::new(1));
        let arc2 = Arc::new(Mutex::<_, NoOpSchedulerInfluence>::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move|| {
            let lock = arc2.lock();
            let lock2 = lock.lock();
            assert_eq!(*lock2, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    #[test]
    fn test_mutex_arc_access_in_unwind() {
        let arc = Arc::new(Mutex::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move|| -> () {
            struct Unwinder {
                i: Arc<Mutex<i32, NoOpSchedulerInfluence>>,
            }
            impl Drop for Unwinder {
                fn drop(&mut self) {
                    *self.i.lock() += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        }).join();
        let lock = arc.lock();
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_mutex_unsized() {
        let mutex: &Mutex<[i32], NoOpSchedulerInfluence> = &Mutex::new([1, 2, 3]);
        {
            let b = &mut *mutex.lock();
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*mutex.lock(), comp);
    }

    #[test]
    fn test_mutex_force_lock() {
        let lock: Mutex<_, NoOpSchedulerInfluence> = Mutex::new(());
        ::std::mem::forget(lock.lock());
        unsafe {
            lock.force_unlock();
        } 
        assert!(lock.try_lock().is_some());
    }
}
