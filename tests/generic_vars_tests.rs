use std::collections::HashMap;
use std::hash::{Hash};

use tabulon::{Tabula, VarResolver, VarResolveError};

// -----------------------------
// u64 key resolver and test
// -----------------------------
struct U64Resolver {
    map: HashMap<String, u64>,
}

impl VarResolver<u64> for U64Resolver {
    fn resolve(&self, ident: &str) -> Result<u64, VarResolveError> {
        self.map
            .get(ident)
            .copied()
            .ok_or_else(|| VarResolveError::Unknown(ident.to_string()))
    }
}

#[test]
fn u64_var_keys_work() {
    // Map string variable names to numeric IDs
    let mut reg: HashMap<String, u64> = HashMap::new();
    reg.insert("A".to_string(), 1);
    reg.insert("B".to_string(), 2);
    reg.insert("C".to_string(), 3);

    let resolver = U64Resolver { map: reg };
    let mut eng: Tabula<u64, _> = Tabula::with_resolver(resolver);

    let compiled = eng.compile("(A + B) * C").unwrap();

    // Provide values by u64 key
    let mut values_by_id: HashMap<u64, f64> = HashMap::new();
    values_by_id.insert(1, 100.0);
    values_by_id.insert(2, 20.0);
    values_by_id.insert(3, 1.5);

    // Build &[&f64] in compiler-determined order (Vec<K> is u64 here)
    let ordered_values: Vec<&f64> = compiled
        .vars()
        .iter()
        .map(|k| values_by_id.get(k).expect("missing value for key"))
        .collect();

    let out = compiled.eval(&ordered_values).unwrap();
    assert!((out - 180.0).abs() < 1e-9);
}

// -----------------------------
// enum key resolver and test
// -----------------------------
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum VarKey {
    Str,
    BonusStr,
    MulStr,
}

struct EnumResolver;
impl VarResolver<VarKey> for EnumResolver {
    fn resolve(&self, ident: &str) -> Result<VarKey, VarResolveError> {
        match ident {
            "A" => Ok(VarKey::Str),
            "B" => Ok(VarKey::BonusStr),
            "C" => Ok(VarKey::MulStr),
            other => Err(VarResolveError::Invalid(other.to_string())),
        }
    }
}

#[test]
fn enum_var_keys_work() {
    let mut eng: Tabula<VarKey, _> = Tabula::with_resolver(EnumResolver);
    let compiled = eng.compile("(A + B) * C").unwrap();

    let mut values: HashMap<VarKey, f64> = HashMap::new();
    values.insert(VarKey::Str, 100.0);
    values.insert(VarKey::BonusStr, 20.0);
    values.insert(VarKey::MulStr, 1.5);

    let ordered_values: Vec<&f64> = compiled
        .vars()
        .iter()
        .map(|k| values.get(k).expect("missing value for enum key"))
        .collect();

    let out = compiled.eval(&ordered_values).unwrap();
    assert!((out - 180.0).abs() < 1e-9);
}
