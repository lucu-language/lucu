#[derive(Clone, Debug)]
pub enum Value {
    Str(String),
    Int(i64),

    FrameIndex(usize),
    Continuation(Vec<Value>),

    Address(u32, u32), // block, byte
}

#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum Opcode {
    Push,    // () -> a
    PushRel, // () -> a
    Pop,     // a -> ()

    JmpRel,        // () -> ()
    JmpRelNonzero, // bool -> ()

    Equals, // int int -> bool
    Div,    // int int -> int
    Mul,
    Add,

    ResetRel, // () -> FrameIndex
    ShiftRel, // FrameIndex -> Address Continuation

    CallRel,   // () -> Address
    Return,    //  Address -> ()
    ReturnVal, // Address a -> a

    Print, // a -> ()
    Halt,  // !
}

pub struct Chunk {
    pub bytecode: Box<[u8]>,
    pub constants: Box<[Value]>,
}

pub struct VM {
    stack: Vec<Value>,
    chunks: Box<[Chunk]>,
    ip: (u32, u32),
    halted: bool,
}

fn to_opcode(byte: u8) -> Opcode {
    unsafe { std::mem::transmute(byte) }
}

impl VM {
    fn next_byte(&mut self) -> u8 {
        let byte = self.chunks[self.ip.0 as usize].bytecode[self.ip.1 as usize];
        self.ip.1 += 1;
        byte
    }
    fn next_opcode(&mut self) -> Opcode {
        to_opcode(self.next_byte())
    }
    fn next_rel(&mut self) -> i8 {
        self.next_byte() as i8
    }
    fn next_val(&mut self) -> Value {
        let byte = self.next_byte();
        self.chunks[self.ip.0 as usize].constants[byte as usize].clone()
    }

    fn push_val(&mut self, val: Value) {
        self.stack.push(val);
    }
    fn pop_val(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    pub fn new(chunks: Box<[Chunk]>) -> Self {
        VM {
            stack: Vec::new(),
            chunks,
            ip: (0, 0),
            halted: false,
        }
    }

    pub fn dump(&self) {
        println!("{:?} {:?}", self.ip, self.stack);
    }

    pub fn halted(&self) -> bool {
        self.halted
    }

    pub fn next_instruction(&mut self) {
        if self.halted {
            return;
        }
        match self.next_opcode() {
            Opcode::Push => {
                let val = self.next_val();
                self.push_val(val);
            }
            Opcode::PushRel => {
                let rel = self.next_byte() as usize;
                let val = self.stack[self.stack.len() - rel - 1].clone();
                self.push_val(val);
            }
            Opcode::Pop => {
                self.pop_val();
            }
            Opcode::JmpRel => {
                let rel = self.next_rel();
                self.ip.1 = self.ip.1.wrapping_add_signed(rel as i32);
            }
            Opcode::JmpRelNonzero => {
                let Value::Int(val) = self.pop_val() else { panic!(); };
                let rel = self.next_rel();
                if val != 0 {
                    self.ip.1 = self.ip.1.wrapping_add_signed(rel as i32);
                }
            }
            Opcode::Equals => {
                let Value::Int(b) = self.pop_val() else { panic!(); };
                let Value::Int(a) = self.pop_val() else { panic!(); };
                self.push_val(Value::Int(if a == b { 1 } else { 0 }));
            }
            Opcode::Div => {
                let Value::Int(b) = self.pop_val() else { panic!(); };
                let Value::Int(a) = self.pop_val() else { panic!(); };
                self.push_val(Value::Int(a.wrapping_div(b)));
            }
            Opcode::Mul => {
                let Value::Int(b) = self.pop_val() else { panic!(); };
                let Value::Int(a) = self.pop_val() else { panic!(); };
                self.push_val(Value::Int(a.wrapping_mul(b)));
            }
            Opcode::Add => {
                let Value::Int(b) = self.pop_val() else { panic!(); };
                let Value::Int(a) = self.pop_val() else { panic!(); };
                self.push_val(Value::Int(a.wrapping_add(b)));
            }
            Opcode::ResetRel => {
                let rel = self.next_rel();
                let ret = Value::Address(self.ip.0, self.ip.1);
                let num = self.stack.len();
                self.push_val(Value::FrameIndex(num));
                self.push_val(ret);
                self.ip = (self.ip.0.wrapping_add_signed(rel as i32), 0);
            }
            Opcode::ShiftRel => {
                let rel = self.next_rel();
                let Value::FrameIndex(frame) = self.pop_val() else { panic!(); };

                let ret = self.stack[frame + 1].clone();
                let cont = Value::Continuation(self.stack.split_off(frame));

                self.push_val(ret);
                self.push_val(cont);

                self.ip = (self.ip.0.wrapping_add_signed(rel as i32), 0);
            }
            Opcode::CallRel => {
                let rel = self.next_rel();
                let ret = Value::Address(self.ip.0, self.ip.1);
                self.push_val(ret);
                self.ip = (self.ip.0.wrapping_add_signed(rel as i32), 0);
            }
            Opcode::Return => {
                let Value::Address(block, byte) = self.pop_val() else { panic!(); };
                self.ip = (block, byte);
            }
            Opcode::ReturnVal => {
                let val = self.pop_val();
                let Value::Address(block, byte) = self.pop_val() else { panic!(); };
                self.ip = (block, byte);
                self.push_val(val);
            }
            Opcode::Print => {
                println!("{:?}", self.pop_val());
            }
            Opcode::Halt => {
                self.halted = true;
            }
        }
    }
}
