use foldhash::{HashMap, HashMapExt};
use shipyard::{Component, EntitiesViewMut, IntoIter, Unique, UniqueView, View, ViewMut};
use tabulon::{CompiledExprRef, JitError, Tabula};

// A practical, non-ECS example that demonstrates how to reuse a stable array of values
// and build raw pointers right before calling `eval_ptrs`.
//
// This pattern keeps memory addresses stable and avoids caching pointers long-term.
// It also shows how to update values in place and re-evaluate without reallocations.
#[test]
fn eval_ptrs_with_stable_boxed_slice_and_rebuilt_ptrs() -> Result<(), JitError> {
    let mut engine = Tabula::new();
    let compiled = engine.compile_ref("a + b * 2")?;

    // Fixed-size set of variables -> store them in Box<[f64]> so addresses are stable.
    let mut values: Box<[f64]> = vec![3.0, 4.5].into_boxed_slice();

    // Build pointers just-in-time for the call based on compiled.vars() order.
    let ptrs: Vec<*const f64> = (0..compiled.vars().len())
        .map(|i| &values[i] as *const f64)
        .collect();
    let out1 = compiled.eval_ptrs(&ptrs)?;
    assert!((out1 - (3.0 + 4.5 * 2.0)).abs() < 1e-12);

    // Update values in place to keep addresses stable.
    values[0] = 5.0; // a
    values[1] = 10.0; // b

    // Rebuild pointers just before the second evaluation.
    let ptrs2: Vec<*const f64> = (0..compiled.vars().len())
        .map(|i| &values[i] as *const f64)
        .collect();
    let out2 = compiled.eval_ptrs(&ptrs2)?;
    assert!((out2 - (5.0 + 10.0 * 2.0)).abs() < 1e-12);

    Ok(())
}

// Pointer safety tips when using eval_ptrs (summary):
// - Build pointers right before calling eval_ptrs; avoid caching long-term.
// - If you must cache, keep values in Box<f64>/Box<[f64]> (or an arena) and update in place.
// - Do not use pointers after freeing/invalidation (see Tabula::free_memory).

#[test]
fn eval_ptrs_with_stable_boxed_slice_and_rebuilt_ptrs2() -> Result<(), JitError> {
    let mut engine = Tabula::new();
    let compiled = engine.compile_ref("a + b * 2")?;

    let mut map = HashMap::new();

    map.insert("a", Box::new(1f64));
    map.insert("b", Box::new(2f64));

    let vec = compiled
        .vars()
        .iter()
        .map(|var| map.get(var.as_str()).unwrap().as_ref() as *const f64)
        .collect::<Vec<_>>();

    let result = compiled.eval_ptrs(&vec)?;
    assert_eq!(result, 5.0);
    map.entry("a").and_modify(|v| **v = 3f64);
    let result = compiled.eval_ptrs(&vec)?;
    assert_eq!(result, 7.0);

    Ok(())
}

#[derive(Component)]
struct PropertyBag {
    map: HashMap<String, Box<f64>>,
    vec: Vec<*const f64>,
}

#[derive(Unique)]
struct Compiled(CompiledExprRef);

unsafe impl Send for PropertyBag {}
unsafe impl Sync for PropertyBag {}

impl PropertyBag {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            vec: vec![],
        }
    }
}

fn insert_property_bag(
    property_bags: ViewMut<PropertyBag>,
    compiled: UniqueView<Compiled>,
    mut entities_view_mut: EntitiesViewMut,
) {
    let mut property_bag = PropertyBag::new();
    property_bag.map.insert("a".into(), Box::new(1f64));
    property_bag.map.insert("b".into(), Box::new(2f64));

    property_bag.vec = compiled
        .0
        .vars()
        .iter()
        .map(|var| property_bag.map.get(var.as_str()).unwrap().as_ref() as *const f64)
        .collect::<Vec<_>>();
    entities_view_mut.add_entity(property_bags, property_bag);
}

fn system_eval(property_bag: View<PropertyBag>, compiled: UniqueView<Compiled>) {
    (property_bag).iter().for_each(|pb| {
        let result = compiled.0.eval_ptrs(&pb.vec).unwrap();
        println!("result: {result}");
    });
}

fn upsert_pb(mut property_bag: ViewMut<PropertyBag>) {
    (&mut property_bag).iter().for_each(|pb| {
        pb.map.entry("a".into()).and_modify(|v| **v = 10f64);
        pb.map.entry("b".into()).and_modify(|v| **v = 10f64);
    });
}

#[test]
fn eval_ptrs_with_stable_boxed_slice_and_rebuilt_ptrs3() {
    let mut engine = Tabula::new();
    let compiled = engine.compile_ref("a + b * 2").unwrap();

    let unique_compiled = Compiled(compiled);

    let world = shipyard::World::new();
    world.add_unique(unique_compiled);
    world.run(insert_property_bag);
    world.run(system_eval);
    world.run(upsert_pb);
    world.run(system_eval);
}
