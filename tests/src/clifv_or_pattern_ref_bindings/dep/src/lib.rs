// Or-patterns binding references to fields of different variants, in the
// shape of Cranelift's generated `InstructionData::arguments` and
// `InstructionData::arguments_mut` (cranelift-codegen build output
// `opcodes.rs`). The functions are in a dependency crate, as in Cranelift:
// with the code duplication limit, the control-flow reconstruction makes the
// bindings of each or-pattern fall through to a common use.

pub enum Data {
    Nullary { x: u32 },
    Unary { arg: u32, imm: u8 },
    Load { arg: u32 },
    Binary { args: [u32; 2] },
    Store { args: [u32; 2], off: i32 },
    Compare { args: [u32; 2], cc: u8 },
    Shuffle { args: [u32; 2] },
    Ternary { args: [u32; 3] },
    Cas { args: [u32; 3] },
    Select { args: [u32; 3] },
    Multi { args: Vec<u32> },
    Call { args: Vec<u32>, callee: u32 },
}

pub fn arguments(d: &Data) -> &[u32] {
    match *d {
        Data::Binary { args: ref args_arity2, .. }
        | Data::Store { args: ref args_arity2, .. }
        | Data::Compare { args: ref args_arity2, .. }
        | Data::Shuffle { args: ref args_arity2, .. } => args_arity2,
        Data::Ternary { args: ref args_arity3, .. }
        | Data::Cas { args: ref args_arity3, .. }
        | Data::Select { args: ref args_arity3, .. } => args_arity3,
        Data::Unary { ref arg, .. } | Data::Load { ref arg, .. } => core::slice::from_ref(arg),
        Data::Multi { ref args, .. } | Data::Call { ref args, .. } => args.as_slice(),
        Data::Nullary { .. } => &[],
    }
}

pub fn arguments_mut(d: &mut Data) -> &mut [u32] {
    // The long common suffix makes the code duplication exceed its budget:
    // the control-flow reconstruction then uses forward breaks
    let a: &mut [u32] = match *d {
        Data::Binary { args: ref mut args_arity2, .. }
        | Data::Store { args: ref mut args_arity2, .. }
        | Data::Compare { args: ref mut args_arity2, .. }
        | Data::Shuffle { args: ref mut args_arity2, .. } => args_arity2,
        Data::Ternary { args: ref mut args_arity3, .. }
        | Data::Cas { args: ref mut args_arity3, .. }
        | Data::Select { args: ref mut args_arity3, .. } => args_arity3,
        Data::Unary { ref mut arg, .. } | Data::Load { ref mut arg, .. } => {
            core::slice::from_mut(arg)
        }
        Data::Multi { ref mut args, .. } | Data::Call { ref mut args, .. } => args.as_mut_slice(),
        Data::Nullary { .. } => &mut [],
    };
    if a.len() > 10 {
        a[0] = a[1];
    }
    if a.len() > 11 {
        a[1] = a[2];
    }
    if a.len() > 12 {
        a[2] = a[3];
    }
    if a.len() > 13 {
        a[3] = a[4];
    }
    a
}

pub fn sum_args(d: &Data) -> u32 {
    let a = arguments(d);
    let mut s = 0;
    let mut i = 0;
    while i < a.len() {
        s += a[i];
        i += 1;
    }
    s
}

pub fn bump_args(mut d: Data) -> u32 {
    let a = arguments_mut(&mut d);
    let mut i = 0;
    while i < a.len() {
        a[i] += 1;
        i += 1;
    }
    sum_args(&d)
}
