//! Errors returned by the verifiers and by parameter validation.

use core::fmt;

/// Why a proof was rejected, or why parameters are invalid.
///
/// Every verifier of the crate returns `Result<(), Error>` and never panics on a malformed proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The parameters are invalid; the message names the violated condition.
    Params(&'static str),
    /// The proof has the wrong shape (lengths, counts, sizes of caps, salts or openings).
    Shape,
    /// A Merkle opening does not authenticate against its root or cap.
    Merkle,
    /// A fold check or the final-polynomial check of the folding test failed.
    Fold,
    /// The prover was called with inputs that do not match the parameters (lengths, counts).
    Input(&'static str),
    /// The operating system's random number generator failed.
    Randomness,
    /// A protocol equation other than the folding test failed; the message names it
    /// (for instance `"outer sumcheck"` or `"row lookup"`).
    Check(&'static str),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Params(m) => write!(f, "invalid parameters: {m}"),
            Error::Shape => f.write_str("malformed proof: wrong shape"),
            Error::Merkle => f.write_str("invalid Merkle opening"),
            Error::Fold => f.write_str("folding test failed"),
            Error::Input(m) => write!(f, "invalid prover input: {m}"),
            Error::Randomness => f.write_str("the system random number generator failed"),
            Error::Check(m) => write!(f, "check failed: {m}"),
        }
    }
}

impl std::error::Error for Error {}
