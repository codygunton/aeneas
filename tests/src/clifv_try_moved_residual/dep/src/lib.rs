// The `?` operator in a function with drop flags (an argument moved on one
// path only), in the shape of Cranelift's
// `SigSet::make_abi_sig_from_ir_signature` (cranelift/codegen/src/machinst/
// abi.rs): the `Break` branch of the match on `Try::branch` moves the residual
// out of the scrutinee and returns, the `Continue` branch falls through to a
// read of the scrutinee. The function is in a dependency crate, whose MIR
// (from the crate metadata) has its drops elaborated with drop flags and
// unwinding paths, as for the Cranelift crates.

pub struct Sig {
    pub params: Vec<u32>,
}

pub struct SigSet {
    pub sigs: Vec<u32>,
    pub keys: Vec<Sig>,
}

pub enum Error {
    TooMany(String),
}

impl SigSet {
    fn have(&self, sig: &Sig) -> bool {
        let mut i = 0;
        while i < self.keys.len() {
            if self.keys[i].params.len() == sig.params.len() {
                return true;
            }
            i += 1;
        }
        false
    }

    fn from_sig(&mut self, sig: &Sig) -> Result<u32, Error> {
        if sig.params.len() > 3 {
            Err(Error::TooMany(String::new()))
        } else {
            Ok(sig.params.len() as u32)
        }
    }

    pub fn make(&mut self, sig: Sig) -> Result<usize, Error> {
        debug_assert!(!self.have(&sig));
        let data = self.from_sig(&sig)?;
        let id = self.sigs.len();
        self.sigs.push(data);
        self.keys.push(sig);
        Ok(id)
    }
}

pub fn run(n: u32) -> u32 {
    let mut s = SigSet { sigs: Vec::new(), keys: Vec::new() };
    let mut params = Vec::new();
    let mut i = 0;
    while i < n {
        params.push(i);
        i += 1;
    }
    match s.make(Sig { params }) {
        Ok(id) => id as u32 + 10 * s.sigs[0],
        Err(Error::TooMany(_)) => 100,
    }
}

// Two `?` in sequence on values with drop glue, then a partial move out of
// the result, in the shape of Cranelift's `AArch64Backend::compile_function`
// (cranelift/codegen/src/isa/aarch64/mod.rs). The cleanup blocks of the
// unwinding paths end with `UnwindResume`.
pub struct VCode {
    pub insts: Vec<u32>,
}

pub struct EmitResult {
    pub buffer: Vec<u8>,
    pub offsets: Vec<u32>,
    pub disasm: Option<String>,
}

pub struct Compiled {
    pub buffer: Vec<u8>,
    pub disasm: Option<String>,
    pub offsets: Vec<u32>,
}

fn compile_vcode(n: u32) -> Result<VCode, Error> {
    if n > 3 {
        return Err(Error::TooMany(String::new()));
    }
    let mut insts = Vec::new();
    insts.push(n);
    Ok(VCode { insts })
}

fn emit(vcode: VCode, want_disasm: bool) -> Result<EmitResult, Error> {
    if vcode.insts[0] == 3 {
        return Err(Error::TooMany(String::new()));
    }
    let mut buffer = Vec::new();
    buffer.push(vcode.insts[0] as u8);
    let mut offsets = Vec::new();
    offsets.push(7);
    let disasm = if want_disasm { Some(String::new()) } else { None };
    Ok(EmitResult { buffer, offsets, disasm })
}

pub fn compile_function(n: u32, want_disasm: bool) -> Result<Compiled, Error> {
    let vcode = compile_vcode(n)?;
    let emit_result = emit(vcode, want_disasm)?;
    let buffer = emit_result.buffer;
    if let Some(disasm) = emit_result.disasm.as_ref() {
        if disasm.len() > 100 {
            return Err(Error::TooMany(String::new()));
        }
    }
    Ok(Compiled { buffer, disasm: emit_result.disasm, offsets: emit_result.offsets })
}

pub fn compile_summary(n: u32, want_disasm: bool) -> u32 {
    match compile_function(n, want_disasm) {
        Ok(c) => {
            c.buffer[0] as u32 + 10 * c.offsets[0] + if c.disasm.is_some() { 100 } else { 0 }
        }
        Err(_) => 1000,
    }
}
