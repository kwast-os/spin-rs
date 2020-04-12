/// Defines what influence taking a lock should have on the scheduler.
pub trait SchedulerInfluence: Sized + Copy {
    /// Enable preemption.
    fn preempt_enable(&self);

    /// Disable preemption.
    fn preempt_disable() -> Self;
}

/// No-op influence on taking a lock.
#[derive(Copy, Clone)]
pub struct NoOpSchedulerInfluence {}

impl SchedulerInfluence for NoOpSchedulerInfluence {
    fn preempt_enable(&self) {}

    fn preempt_disable() -> Self { Self {} }
}
