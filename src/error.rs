use thiserror::Error;

/// Errors returned by fallible operations of this crate.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum Error {
    /// The requested operation is not (yet) implemented for the given input.
    #[error("not yet implemented: {0}")]
    NotYetImplemented(&'static str),
    /// The input does not satisfy a precondition of the operation, which is described.
    #[error("invalid input: {0}")]
    InvalidInput(&'static str),
    /// An alphabet could not be converted into a propositional alphabet.
    #[error(transparent)]
    PropAlphabet(#[from] crate::alphabet::PropAlphabetError),
    /// A reduced omega word has a non-empty prefix and cannot be turned into a periodic one.
    #[error(transparent)]
    NotPeriodic(#[from] crate::word::NotPeriodicError),
    /// An error occurred when reading an automaton in the HOA format.
    #[cfg(feature = "hoa")]
    #[error(transparent)]
    Hoa(#[from] crate::hoa::HoaError),
    /// An error occurred when running Spot.
    #[cfg(feature = "spot")]
    #[error(transparent)]
    Spot(#[from] crate::spot::SpotError),
}

/// Shorthand for results whose error type is [`enum@Error`].
pub type Result<T, E = Error> = std::result::Result<T, E>;

#[cfg(test)]
mod tests {
    use super::Error;
    use crate::alphabet::PropAlphabetError;
    use crate::word::NotPeriodicError;

    #[test]
    fn domain_errors_convert_into_the_crate_error() {
        assert_eq!(
            Error::from(PropAlphabetError::InvalidSize(3)),
            Error::PropAlphabet(PropAlphabetError::InvalidSize(3))
        );
        assert_eq!(
            Error::from(NotPeriodicError),
            Error::NotPeriodic(NotPeriodicError)
        );
    }

    #[test]
    fn errors_have_readable_messages() {
        assert_eq!(
            Error::from(PropAlphabetError::InvalidSize(3)).to_string(),
            PropAlphabetError::InvalidSize(3).to_string()
        );
        assert!(Error::NotYetImplemented("foo").to_string().contains("foo"));
    }
}
