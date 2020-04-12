extern crate spin;

use spin::NoOpSchedulerInfluence;

fn main() {
    let mutex: spin::Mutex<i32, NoOpSchedulerInfluence> = spin::Mutex::new(42);
    println!("{:?}", mutex);
    {
        let x = mutex.lock();
        println!("{:?}, {:?}", mutex, *x);
    }

    let rwlock = spin::RwLock::<_, NoOpSchedulerInfluence>::new(42);
    println!("{:?}", rwlock);
    {
        let x = rwlock.read();
        println!("{:?}, {:?}", rwlock, *x);
    }
    {
        let x = rwlock.write();
        println!("{:?}, {:?}", rwlock, *x);
    }
}
