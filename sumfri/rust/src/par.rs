//! Optional parallelism (feature `parallel`, with rayon). Without the feature every helper runs
//! the same computation serially; the results are identical in both cases, since the work is
//! split into independent pieces whose outputs do not depend on the split.

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Grain of the parallel loops (elements per task).
pub(crate) const GRAIN: usize = 1 << 12;

/// `(0..n).map(f).collect()`.
pub(crate) fn map_range<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync + Send) -> Vec<T> {
    #[cfg(feature = "parallel")]
    {
        (0..n).into_par_iter().with_min_len(GRAIN).map(f).collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        (0..n).map(f).collect()
    }
}
