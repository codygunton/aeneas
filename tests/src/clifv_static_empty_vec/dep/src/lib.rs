// Statics initialized by a `const fn` building an empty `Vec`, in the shape of
// Cranelift's AArch64 `get_machine_env` (cranelift/codegen/src/isa/aarch64/
// abi.rs): `static MACHINE_ENV: MachineEnv = create_reg_env(..)` where the
// environment has a `fixed_stack_slots: vec![]` field. The static is in a
// dependency crate: Charon only has its evaluated value, which builds the
// fields of the empty `Vec` (raw pointers) directly.

pub struct Env {
    pub preferred: [u64; 2],
    pub fixed: Vec<u8>,
    // Evaluated to the constant repetition `[const Option::None {}; 3usize]`
    pub scratch: [Option<u8>; 3],
}

const fn create_env(pinned: bool) -> Env {
    Env {
        preferred: if pinned { [1, 2] } else { [3, 4] },
        fixed: vec![],
        scratch: [None; 3],
    }
}

pub fn get_env(pinned: bool) -> &'static Env {
    if pinned {
        static ENV: Env = create_env(true);
        &ENV
    } else {
        static ENV: Env = create_env(false);
        &ENV
    }
}
