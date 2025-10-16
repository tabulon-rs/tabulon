use tabulon::{Parser, PreparedExpr, Tabula, IdentityResolver, VarResolver, VarResolveError};

#[test]
fn prepared_expr_pipeline_string() {
    let parser = Parser::new("(Str + BonusStr) * MulStr").unwrap();
    let prepared: PreparedExpr<String> = parser.parse_with_var_resolver(&IdentityResolver).unwrap();
    assert_eq!(prepared.ordered_vars, vec!["Str".to_string(), "BonusStr".to_string(), "MulStr".to_string()]);

    let mut eng = Tabula::new();
    let compiled = eng.compile_prepared(&prepared).unwrap();

    let str_v = 100.0;
    let bonus_str = 20.0;
    let mul_str = 1.5;
    let out = compiled.eval(&[str_v, bonus_str, mul_str]).unwrap();
    assert!((out - 180.0).abs() < 1e-9);
}

struct U32Resolver;
impl VarResolver<u32> for U32Resolver {
    fn resolve(&self, ident: &str) -> Result<u32, VarResolveError> {
        match ident {
            "A" | "a" => Ok(10),
            "B" | "b" => Ok(20),
            "C" | "c" => Ok(30),
            other => Err(VarResolveError::Unknown(other.to_string())),
        }
    }
}

#[test]
fn prepared_expr_custom_key_u32() {
    let parser = Parser::new("(A + B) * C").unwrap();
    let prepared_u32: PreparedExpr<u32> = parser.parse_with_var_resolver(&U32Resolver).unwrap();
    assert_eq!(prepared_u32.ordered_vars, vec![10, 20, 30]);

    // Engine is independent of K; PreparedExpr<K> drives the compiled type.
    let mut eng = Tabula::new();
    let compiled = eng.compile_prepared(&prepared_u32).unwrap();

    let a = 2.0;
    let b = 3.0;
    let c = 4.0;
    let out = compiled.eval(&[a, b, c]).unwrap();
    assert!((out - 20.0).abs() < 1e-9);

    // The compiled expression should expose the resolved variable order (K = u32)
    assert_eq!(compiled.var_names(), &[10, 20, 30]);
}
