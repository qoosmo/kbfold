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

/// Apply `f` to consecutive pairs of chunks `(lo, hi)` of two slices of equal length, with the
/// starting index of the chunk.
pub(crate) fn zip_chunks<T: Send>(
    lo: &mut [T],
    hi: &mut [T],
    f: impl Fn(usize, &mut [T], &mut [T]) + Sync + Send,
) {
    #[cfg(feature = "parallel")]
    {
        lo.par_chunks_mut(GRAIN)
            .zip(hi.par_chunks_mut(GRAIN))
            .enumerate()
            .for_each(|(c, (a, b))| f(c * GRAIN, a, b));
    }
    #[cfg(not(feature = "parallel"))]
    {
        f(0, lo, hi)
    }
}

/// Apply `f` to every chunk of length `len` of `v` (independent blocks).
pub(crate) fn for_blocks<T: Send>(v: &mut [T], len: usize, f: impl Fn(&mut [T]) + Sync + Send) {
    #[cfg(feature = "parallel")]
    {
        v.par_chunks_exact_mut(len).for_each(f);
    }
    #[cfg(not(feature = "parallel"))]
    {
        v.chunks_exact_mut(len).for_each(f);
    }
}
