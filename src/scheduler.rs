/// Defines what influence taking a lock should have on the scheduler.
/// Should deactivate on drop.
pub trait SchedulerInfluence: Sized {
    /// Activate new influence.
    fn activate() -> Self;
}

/// No-op influence on taking a lock.
pub struct NoOpSchedulerInfluence {}

impl SchedulerInfluence for NoOpSchedulerInfluence {
    fn activate() -> Self { Self {} }
}
