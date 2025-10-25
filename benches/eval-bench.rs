use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use fasteval::{Compiler, Evaler, Parser, Slab, eval_compiled_ref};
use foldhash::{HashMap, HashMapExt};
use rand::Rng;
use std::hint::black_box;
use tabulon::function;
use tabulon::{Tabula, VarResolveError, VarResolver, register_functions};

const DEFAULT_F64: f64 = 0.0f64;

#[function]
fn dice(min: f64, max: f64) -> f64 {
    let mut rng = rand::thread_rng();
    rng.gen_range(min..=max)
}

// String-keyed map for fasteval path
fn create_string_map() -> HashMap<String, f64> {
    let mut vars: HashMap<String, f64> = HashMap::new();
    vars.insert("a".to_string(), 2.0);
    vars.insert("b".to_string(), 3.0);
    vars.insert("power".to_string(), 100.0);
    vars.insert("defense".to_string(), 50.0);
    vars.insert("critical_bonus".to_string(), 0.5);
    vars.insert("skill_modifier".to_string(), 1.2);
    vars.insert("threat".to_string(), 1000.0);
    vars.insert("distance".to_string(), 20.0);
    vars.insert("is_taunted".to_string(), 1.0);
    vars.insert("crit_chance".to_string(), 20.0);
    vars.insert("agility".to_string(), 15.0);
    vars.insert("intelligence".to_string(), 25.0);
    vars.insert("mana_pool".to_string(), 500.0);
    vars.insert("rage_level".to_string(), 75.0);
    vars.insert("haste_rating".to_string(), 1.1);

    vars
}

// u64-key support for tabulon path
struct U64Resolver;
impl VarResolver<u64> for U64Resolver {
    fn resolve(&self, ident: &str) -> Result<u64, VarResolveError> {
        let id = match ident {
            "a" => 1,
            "b" => 2,
            "power" => 3,
            "defense" => 4,
            "critical_bonus" => 5,
            "skill_modifier" => 6,
            "threat" => 7,
            "distance" => 8,
            "is_taunted" => 9,
            "crit_chance" => 10,
            "agility" => 11,
            "intelligence" => 12,
            "mana_pool" => 13,
            "rage_level" => 14,
            "haste_rating" => 15,
            _ => return Err(VarResolveError::Unknown(ident.to_string())),
        };
        Ok(id)
    }
}

fn create_u64_map() -> HashMap<u64, f64> {
    let mut vars: HashMap<u64, f64> = HashMap::new();
    vars.insert(1, 2.0); // a
    vars.insert(2, 3.0); // b
    vars.insert(3, 100.0); // power
    vars.insert(4, 50.0); // defense
    vars.insert(5, 0.5); // critical_bonus
    vars.insert(6, 1.2); // skill_modifier
    vars.insert(7, 1000.0); // threat
    vars.insert(8, 20.0); // distance
    vars.insert(9, 1.0); // is_taunted
    vars.insert(10, 20.0); // crit_chance
    vars.insert(11, 15.0); // agility
    vars.insert(12, 25.0); // intelligence
    vars.insert(13, 500.0); // mana_pool
    vars.insert(14, 75.0); // rage_level
    vars.insert(15, 1.1); // haste_rating
    vars
}

fn create_u64_box_map() -> HashMap<u64, Box<f64>> {
    let mut vars: HashMap<u64, Box<f64>> = HashMap::new();
    let map = create_u64_map();
    map.iter().for_each(|(k, v)| {
        vars.insert(*k, Box::new(*v));
    });
    vars
}

fn benchmark_eval(c: &mut Criterion) {
    let mut slab = Slab::new();
    let parser = Parser::new();

    let expressions = vec![
        // Basic & Simple
        ("constant", "123.45"),
        ("variable", "a"),
        ("simple_add", "a + b"),
        ("simple_mul", "a * b"),
        (
            "multiple_same_var",
            "a + a + a + a + a + a + a + a + a + a * a * a * a",
        ),
        ("simple_comparison", "a > b"),
        ("simple_and", "1.0 && 1.0"),
        ("simple_or", "0.0 || 1.0"),
        // Intermediate
        ("complex_arithmetic", "(a * a + b * b) / 2.0"),
        ("builtin_func_max", "max(a, b)"),
        ("custom_func_if", "if(a > b, a, b)"),
        ("simple_dice", "dice(1, 6)"),
        ("dice_with_op", "dice(1, 20) + defense"),
        // Complex & Game-Oriented
        (
            "damage_calculation",
            "(power - defense) * (1.0 + critical_bonus) * skill_modifier",
        ),
        (
            "targeting_priority",
            "(threat * 0.8) + (distance * -0.2) + is_taunted * 100.0",
        ),
        (
            "crit_hit_check",
            "if(dice(0, 100) < crit_chance, power * (1.5 + critical_bonus), power)",
        ),
        (
            "nested_logic",
            "max(a, b) + if(power > defense, dice(5, 10), dice(1, 4)) * skill_modifier",
        ),
        (
            "full_combat_formula",
            "((power * skill_modifier) - (defense / 2.0)) * (1.0 + if(dice(0, 100) < crit_chance, critical_bonus, 0.0)) + (threat / distance)",
        ),
        (
            "hyper_complex_mmo_calc",
            "max(0, ( (power/defense) * (skill_modifier + intelligence/100.0) + if(dice(0,100)<(crit_chance+agility/10), critical_bonus*100, 0) + (threat/max(1,distance)) + a - b ) * if(is_taunted>0, 1.5, 1.0) * haste_rating + if(rage_level > 50, rage_level/50, -mana_pool/500) )",
        ),
    ];

    for (name, expr_str) in expressions.clone() {
        c.bench_function(&format!("eval_{}", name), |b| {
            let compiled = parser
                .parse(expr_str, &mut slab.ps)
                .unwrap()
                .from(&slab.ps)
                .compile(&slab.ps, &mut slab.cs);

            // Setup: Create the variables map and the namespace closure for each batch.
            b.iter_batched(
                || {
                    let vars = create_string_map();

                    // The namespace `ns` is a closure that implements `fasteval::EvalNamespace`.
                    // It returns `Option<f64>`. Errors are signaled by returning `Some(f64::NAN)`.
                    let ns = move |name: &str, args: Vec<f64>| -> Option<f64> {
                        match name {
                            "dice" => {
                                if args.len() != 2 {
                                    return Some(f64::NAN); // Signal error
                                }
                                let min = args[0];
                                let max = args[1];
                                if min > max {
                                    return Some(f64::NAN); // Signal error
                                }
                                let mut rng = rand::thread_rng();
                                Some(rng.gen_range(min..=max))
                            }
                            "if" => {
                                if args.len() != 3 {
                                    return Some(f64::NAN);
                                }
                                if args[0] > 0.0 {
                                    Some(args[1])
                                } else {
                                    Some(args[2])
                                }
                            }
                            "a" => Some(2.0),
                            "b" => Some(3.0),
                            "power" => Some(100.0),
                            "defense" => Some(50.0),
                            "critical_bonus" => Some(0.5),
                            "skill_modifier" => Some(1.2),
                            "threat" => Some(1000.0),
                            "distance" => Some(20.0),
                            "is_taunted" => Some(1.0),
                            "crit_chance" => Some(20.0),
                            "agility" => Some(15.0),
                            "intelligence" => Some(25.0),
                            "mana_pool" => Some(500.0),
                            "rage_level" => Some(75.0),
                            "haste_rating" => Some(1.1),
                            _ => None,
                        }
                    };
                    ns
                },
                |mut eval_ns| {
                    let mut eval = || -> Result<f64, fasteval::Error> {
                        Ok(eval_compiled_ref!(&compiled, &slab, &mut eval_ns))
                    };
                    let _ = black_box(
                        eval().unwrap_or_else(|e| panic!("Error evaluating expression: {}", e)),
                    );
                },
                BatchSize::SmallInput,
            )
        });

        c.bench_function(&format!("tabulon_eval_{}", name), |b| {
            // Use u64-keyed resolver and map for tabulon
            let mut eng: Tabula<u64, _> = Tabula::with_resolver(U64Resolver);
            register_functions!(eng, dice).unwrap();
            let compiled = eng.compile(expr_str).unwrap();
            let vars = create_u64_map();

            // The values must be supplied in the order that the compiler determined.
            // We create a Vec of references here to match the `eval` signature.
            let ordered_values: Vec<f64> = compiled
                .vars()
                .iter()
                .map(|key| *vars.get(key).unwrap_or(&DEFAULT_F64))
                .collect();

            b.iter(|| {
                let _ = black_box(compiled.eval(&ordered_values));
            });
        });

        c.bench_function(&format!("tabulon_eval_ref_{}", name), |b| {
            // Use u64-keyed resolver and map for tabulon
            let mut eng: Tabula<u64, _> = Tabula::with_resolver(U64Resolver);
            register_functions!(eng, dice).unwrap();
            let compiled = eng.compile_ref(expr_str).unwrap();
            let vars = create_u64_box_map();
            let box_default = Box::new(DEFAULT_F64);
            let ordered_ptrs = compiled
                .vars()
                .iter()
                .map(|key| vars.get(key).unwrap_or(&box_default).as_ref() as *const f64)
                .collect::<Vec<*const f64>>();

            b.iter(|| {
                let _ = black_box(compiled.eval_ptrs(&ordered_ptrs));
            });
        });
    }
}

criterion_group!(benches, benchmark_eval);
criterion_main!(benches);
