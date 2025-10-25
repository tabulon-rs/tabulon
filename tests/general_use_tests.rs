use foldhash::{HashMap, HashMapExt};
use shipyard::{Component, IntoIter, Unique, UniqueView, ViewMut, World};
use tabulon::{CompiledExprRef, Parser, PreparedExpr, Tabula, VarResolveError};

struct U64Resolver;

impl tabulon::VarResolver<usize> for U64Resolver {
    fn resolve(&self, ident: &str) -> Result<usize, VarResolveError> {
        if ident == "a" {
            Ok(1)
        } else {
            Err(VarResolveError::Unknown(ident.to_string()))
        }
    }
}

struct Namespace {
    map: HashMap<usize, Box<f64>>,         // Box to keep addresses stable
    var_cache: HashMap<usize, Vec<usize>>, // cache raw addresses as usize (Send + Sync)
}

#[derive(Component)]
struct PropertyBag {
    ns: Namespace,
}

#[derive(Unique)]
struct Compiled {
    compiled_expr: CompiledExprRef<usize>,
}

impl Namespace {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            var_cache: HashMap::new(),
        }
    }
}

#[test]
fn test() {
    let mut ns = Namespace::new();
    ns.map.insert(1, Box::new(2f64));
    let resolver = U64Resolver;

    // Build a PreparedExpr using the resolver, then compile with an engine that does not own the resolver
    let parser = Parser::new("a + 10").unwrap();
    let prepared: PreparedExpr<usize> = parser.parse_with_var_resolver(&resolver).unwrap();
    let mut engine = Tabula::new();
    let compiled = engine
        .compile_prepared_ref(&prepared)
        .expect("TODO: panic message");

    let mut world = World::new();
    let compiled = Compiled {
        compiled_expr: compiled,
    };

    world.add_unique(compiled);

    world.add_entity((PropertyBag { ns },));

    world.run(eval_system);
    world.run(change_property_bag_system);
    world.run(eval_system);
}

fn eval_system(mut property_bag: ViewMut<PropertyBag>, compiled: UniqueView<Compiled>) {
    (&mut property_bag).iter().for_each(move |p| {
        if let Some(cached) = p.ns.var_cache.get(&1) {
            // turn cached addresses back into pointers
            let ptrs: Vec<*const f64> = cached.iter().copied().map(|u| u as *const f64).collect();
            let result = compiled.compiled_expr.eval_ptrs(&ptrs).unwrap();
            assert_eq!(result, 14.0);
        } else {
            // collect addresses for the variables in the compiled expression
            let addrs: Vec<usize> = compiled
                .compiled_expr
                .vars()
                .iter()
                .map(|v| {
                    let bx: &Box<f64> = p.ns.map.get(v).unwrap();
                    bx.as_ref() as *const f64 as usize
                })
                .collect();
            // cache the addresses for reuse
            p.ns.var_cache.insert(1, addrs.clone());
            // convert to pointers for this evaluation call
            let ptrs: Vec<*const f64> = addrs.iter().copied().map(|u| u as *const f64).collect();
            let result = compiled.compiled_expr.eval_ptrs(&ptrs).unwrap();
            assert_eq!(result, 12.0);
        }
    })
}

fn change_property_bag_system(mut property_bag: ViewMut<PropertyBag>) {
    (&mut property_bag).iter().for_each(|p| {
        if let Some(v) = p.ns.map.get_mut(&1) {
            **v = 4f64; // update in-place to keep Box allocation (and address) stable
        } else {
            p.ns.map.insert(1, Box::new(4f64));
        }
    })
}

#[test]
fn cache_ptr_test() {
    let mut map = HashMap::new();
    map.insert(1, Box::new(2f64));
    let mut cache = Vec::new();
    let resolver = U64Resolver;

    let parser = Parser::new("a + 10").unwrap();
    let prepared: PreparedExpr<usize> = parser.parse_with_var_resolver(&resolver).unwrap();
    let mut engine = Tabula::new();
    let compiled = engine
        .compile_prepared_ref(&prepared)
        .expect("TODO: panic message");
    let vec = compiled
        .vars()
        .iter()
        .map(|v| {
            let bx: &Box<f64> = map.get(v).unwrap();
            bx.as_ref() as *const f64 as usize
        })
        .collect::<Vec<_>>();
    cache.extend(vec.iter().copied());

    let vars = vec.iter().map(|v| *v as *const f64).collect::<Vec<_>>();

    let result = compiled.eval_ptrs(&vars).unwrap();

    assert_eq!(result, 12.0);

    map.entry(1).and_modify(|v| **v = 4f64);

    let result = compiled.eval_ptrs(&vars).unwrap();

    assert_eq!(result, 14.0);
}
