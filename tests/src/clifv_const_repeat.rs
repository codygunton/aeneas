//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
// Constant array repetitions in the values of statics (the shape of
// `AArch64MachineDeps::get_machine_env`'s `MACHINE_ENV`, whose `PRegSet`s hold
// `[0u64; 4]`).

#[derive(Clone, Copy)]
pub struct Set {
    pub bits: [u64; 4],
}

pub struct Env {
    pub sets: [Set; 2],
    pub flag: bool,
}

const fn mk_env(flag: bool) -> Env {
    let mut sets = [Set { bits: [0u64; 4] }; 2];
    if flag {
        sets[1].bits[2] = 5;
    }
    Env { sets, flag }
}

pub fn get_env(flag: bool) -> &'static Env {
    if flag {
        static ENV: Env = mk_env(true);
        &ENV
    } else {
        static ENV: Env = mk_env(false);
        &ENV
    }
}

pub fn sum(flag: bool) -> u64 {
    let env = get_env(flag);
    env.sets[0].bits[0] + env.sets[1].bits[2] + env.sets[1].bits[3]
}

#[verify::test]
pub fn test_sum() {
    assert!(sum(false) == 0);
    assert!(sum(true) == 5);
    assert!(get_env(true).flag);
}
