use crate::{
    ir::{Instruction, Procedure},
    vm::{Chunk, Opcode, Value},
};

pub fn compile(ir: &[Procedure]) -> Box<[Chunk]> {
    let mut chunks: Vec<Chunk> = Vec::with_capacity(ir.len());

    // compile
    for (cur, proc) in ir.iter().enumerate() {
        let mut bytecode = Vec::new();
        let mut constants = Vec::new();

        for block in proc.blocks.values() {
            for instr in block.instructions.iter() {
                use Instruction as I;
                match *instr {
                    I::PushInt(i) => {
                        let idx = constants.len();
                        constants.push(Value::Int(i));
                        bytecode.push(Opcode::Push as u8);
                        bytecode.push(idx as u8);
                    }
                    I::PushString(ref s) => {
                        let idx = constants.len();
                        constants.push(Value::Str(s.clone()));
                        bytecode.push(Opcode::Push as u8);
                        bytecode.push(idx as u8);
                    }
                    I::PushParam(p) => {
                        bytecode.push(Opcode::PushParam as u8);
                        bytecode.push(p as u8);
                    }
                    I::Pop => {
                        bytecode.push(Opcode::Pop as u8);
                    }
                    I::Jmp(_) => todo!(),
                    I::JmpNonzero(_) => todo!(),
                    I::Equals => todo!(),
                    I::Div => todo!(),
                    I::Mul => todo!(),
                    I::Add => todo!(),
                    I::Reset(_) => todo!(),
                    I::Shift(proc) => {
                        let params = ir[usize::from(proc)].inputs;

                        let rel = usize::from(proc) as isize - cur as isize;
                        bytecode.push(Opcode::ShiftRel as u8);
                        bytecode.push(params as u8);
                        bytecode.push(rel as i8 as u8);
                    }
                    I::Call(proc) => {
                        let params = ir[usize::from(proc)].inputs;

                        let rel = usize::from(proc) as isize - cur as isize;
                        bytecode.push(Opcode::CallRel as u8);
                        bytecode.push(params as u8);
                        bytecode.push(rel as i8 as u8);
                    }
                    I::Continue(_) => todo!(),
                    I::Return(out) => {
                        let op = match out {
                            0 => Opcode::Return,
                            1 => Opcode::ReturnVal,
                            _ => todo!(),
                        };
                        bytecode.push(op as u8);
                    }
                    I::Print => {
                        bytecode.push(Opcode::Print as u8);
                    }
                }
            }
        }

        chunks.push(Chunk {
            bytecode: bytecode.into_boxed_slice(),
            constants: constants.into_boxed_slice(),
        })
    }

    // replace last chunk's (main) last instruction (return) with halt
    *chunks.last_mut().unwrap().bytecode.last_mut().unwrap() = Opcode::Halt as u8;

    chunks.into_boxed_slice()
}
