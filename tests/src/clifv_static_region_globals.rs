//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Globals whose type contains `'static` borrows outside of ADTs, in the shape
// of Cranelift's settings `TEMPLATE` (cranelift/codegen/src/settings.rs):
// `static ENUMERATORS: [&'static str; N]` referenced from another static.

pub struct Template {
    pub name: &'static str,
    pub enumerators: &'static [&'static str],
    pub defaults: &'static [u8],
}

static ENUMERATORS: [&'static str; 3] = ["none", "speed", "size"];
static EMPTY: [&'static str; 0] = [];
static DEFAULTS: [u8; 2] = [7, 9];

pub static TEMPLATE: Template = Template {
    name: "shared",
    enumerators: &ENUMERATORS,
    defaults: &DEFAULTS,
};

pub static EMPTY_TEMPLATE: Template = Template {
    name: "empty",
    enumerators: &EMPTY,
    defaults: &DEFAULTS,
};

pub fn num_enumerators(t: &Template) -> usize {
    t.enumerators.len()
}

pub fn first_default(t: &Template) -> u8 {
    t.defaults[0]
}

#[verify::test]
fn test_templates() {
    assert!(num_enumerators(&TEMPLATE) == 3);
    assert!(num_enumerators(&EMPTY_TEMPLATE) == 0);
    assert!(first_default(&TEMPLATE) == 7);
}
