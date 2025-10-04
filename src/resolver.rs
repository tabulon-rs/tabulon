use crate::error::VarResolveError;

pub trait VarResolver<K> {
    fn resolve(&self, ident: &str) -> Result<K, VarResolveError>;
}

pub struct IdentityResolver;
impl VarResolver<String> for IdentityResolver {
    fn resolve(&self, ident: &str) -> Result<String, VarResolveError> {
        Ok(ident.to_string())
    }
}
