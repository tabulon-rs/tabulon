use tabulon::Tabula;

#[test]
fn parses_m_suffix_as_million() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("1M").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), 1_000_000.0);
}

#[test]
fn parses_fractional_m_suffix() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("0.5M").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), 500_000.0);
}

#[test]
fn parses_negative_m_suffix() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("-1M").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), -1_000_000.0);
}

#[test]
fn parses_scientific_notation_basic() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("1e3").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), 1000.0);
}

#[test]
fn parses_scientific_notation_with_negative_exponent() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("2.5e-4").unwrap();
    let out = e.eval(&[]).unwrap();
    assert!((out - 0.00025).abs() < 1e-12);
}

#[test]
fn parses_scientific_notation_with_plus_exponent() {
    let mut eng = Tabula::new();
    let e = eng.compile_ref("3.2E+2").unwrap();
    assert_eq!(e.eval(&[]).unwrap(), 320.0);
}
