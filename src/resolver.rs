use crate::error::VarResolveError;

/// A trait for resolving variable names from an expression string into a custom key type `K`.
///
/// Implement this trait to define how variable identifiers in the source expression
/// are mapped to the keys you use to manage variables in your application.
/// For example, you could map string names to integer IDs, enums, or any other type.
pub trait VarResolver<K> {
    /// Resolves a variable identifier string into a key of type `K`.
    ///
    /// If the identifier is known, return `Ok(K)`. If it's unknown, return `Err(VarResolveError::Unknown)`.
    fn resolve(&self, ident: &str) -> Result<K, VarResolveError>;
}

/// The default `VarResolver` that treats variable names as their own keys.
///
/// This resolver maps an identifier `&str` directly to a `String` key.
pub struct IdentityResolver;
impl VarResolver<String> for IdentityResolver {
    fn resolve(&self, ident: &str) -> Result<String, VarResolveError> {
        Ok(ident.to_string())
    }
}
