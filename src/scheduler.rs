/// Defines what influence taking a lock should have on the scheduler.
pub trait SchedulerInfluence: Sized {
    /// Enable preemption.
    fn preempt_enable(&self);

    /// Disable preemption.
    fn preempt_disable() -> Self;

    /// Check schedule flag.
    fn check_schedule_flag();
}

/// No-op influence on taking a lock.
pub struct NoOpSchedulerInfluence {}

impl SchedulerInfluence for NoOpSchedulerInfluence {
    fn preempt_enable(&self) {}

    fn preempt_disable() -> Self { Self {} }

    fn check_schedule_flag() {}
}
