/// Defines what influence taking a lock should have on the scheduler.
pub trait SchedulerInfluence: Sized {
    /// Enable preemption.
    fn preempt_enable();

    /// Disable preemption.
    fn preempt_disable();
}

/// No-op influence on taking a lock.
pub struct NoOpSchedulerInfluence {}

impl SchedulerInfluence for NoOpSchedulerInfluence {
    fn preempt_enable() {}

    fn preempt_disable() {}
}
