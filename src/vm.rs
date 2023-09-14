use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Value {
    Str(String),
    Int(i64),

    FrameIndex(usize),
    Continuation(Box<Continuation>),

    Address(u32, u32), // block, byte

    Empty,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum Opcode {
    Push,      // () -> a
    PushParam, // () -> a
    Pop,       // a -> ()

    JmpRel,        // () -> ()
    JmpRelNonzero, // bool -> ()

    Equals, // int int -> bool
    Div,    // int int -> int
    Mul,
    Add,

    ResetRel, // a, b, .. -> | a, b, .., FrameIndex
    ShiftRel, // a, b, .., FrameIndex -> | a, b, .., Continuation

    CallRel,   // a, b, .. -> | a, b, ..
    Return,    // () | -> ()
    ReturnVal, // a  | -> a

    Continue,    // Continuation -> | ()
    ContinueVal, // a, Continuation -> | a

    Print, // a -> ()
    Halt,  // !
}

#[derive(Debug, Clone)]
pub struct Continuation {
    callstack: Box<[CallStack]>,
    frame: usize,
    ret: (u32, u32),
}

#[derive(Debug, Clone)]
pub struct CallStack {
    parameters: Rc<[Value]>,
    stack: Vec<Value>,
    ret: (u32, u32),
}

#[derive(Debug)]
pub struct Chunk {
    pub bytecode: Box<[u8]>,
    pub constants: Box<[Value]>,
}

pub struct VM {
    callstack: Vec<CallStack>,
    reset_frames: Vec<usize>,

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
        self.callstack.last_mut().unwrap().stack.push(val);
    }
    fn pop_val(&mut self) -> Value {
        self.callstack.last_mut().unwrap().stack.pop().unwrap()
    }

    pub fn new(chunks: Box<[Chunk]>) -> Self {
        VM {
            callstack: vec![CallStack {
                parameters: Rc::new([]),
                stack: Vec::new(),
                ret: (0, 0),
            }],
            reset_frames: Vec::new(),

            chunks,
            ip: (0, 0),
            halted: false,
        }
    }
    pub fn new_back(chunks: Box<[Chunk]>, initial_params: Rc<[Value]>) -> Self {
        VM {
            callstack: vec![CallStack {
                parameters: initial_params,
                stack: Vec::new(),
                ret: (0, 0),
            }],
            reset_frames: Vec::new(),

            ip: (chunks.len() as u32 - 1, 0),
            chunks,
            halted: false,
        }
    }

    pub fn dump(&self) {
        println!("{:?} {:?}", self.ip, self.callstack);
    }

    pub fn halted(&self) -> bool {
        self.halted
    }

    pub fn call(&mut self, addr: u32, params: usize) {
        // split off parameters
        let stack = &mut self.callstack.last_mut().unwrap().stack;
        let parameters: Rc<[Value]> = stack
            .split_off(stack.len() - params)
            .into_boxed_slice()
            .into();

        // call function
        self.callstack.push(CallStack {
            parameters,
            stack: Vec::new(),
            ret: self.ip,
        });
        self.ip = (addr, 0);
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
            Opcode::PushParam => {
                let idx = self.next_byte() as usize;
                let val = self.callstack.last_mut().unwrap().parameters[idx].clone();
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
                let params = self.next_byte() as usize;
                let rel = self.next_rel() as i32;

                let num = self.callstack.len();
                let frame = self.reset_frames.len();
                self.reset_frames.push(num);
                self.push_val(Value::FrameIndex(frame));

                self.call(self.ip.0.wrapping_add_signed(rel), params + 1);
            }
            Opcode::ShiftRel => {
                let params = self.next_byte() as usize;
                let rel = self.next_rel() as i32;

                // get continuation stack
                let Value::FrameIndex(frame) = self.pop_val() else { panic!() };
                let start = self.reset_frames[frame];
                let cont = self.callstack.split_off(start).into_boxed_slice();

                // get return address of reset frame
                let ret = cont[0].ret;

                // create parameter list
                let stack = &mut self.callstack.last_mut().unwrap().stack;
                let mut parameters = stack.split_off(stack.len() - params);
                parameters.push(Value::Continuation(Box::new(Continuation {
                    callstack: cont,
                    frame,
                    ret: self.ip,
                })));
                let parameters: Rc<[Value]> = parameters.into_boxed_slice().into();

                // call function
                self.callstack.push(CallStack {
                    parameters,
                    stack: Vec::new(),
                    ret,
                });
                self.ip = (self.ip.0.wrapping_add_signed(rel), 0);
            }
            Opcode::CallRel => {
                let params = self.next_byte() as usize;
                let rel = self.next_rel() as i32;
                self.call(self.ip.0.wrapping_add_signed(rel), params);
            }
            Opcode::Return => {
                self.ip = self.callstack.pop().unwrap().ret;
            }
            Opcode::ReturnVal => {
                let val = self.pop_val();
                self.ip = self.callstack.pop().unwrap().ret;
                self.push_val(val);
            }
            Opcode::Continue => {
                let Value::Continuation(mut cont) = self.pop_val() else { panic!() };

                // new reset frame
                self.reset_frames[cont.frame] = self.callstack.len();

                // add continuation to call stack (return to here)
                cont.callstack[0].ret = self.ip;
                self.callstack.extend(cont.callstack.into_vec());

                // call continuation
                self.ip = cont.ret;
            }
            Opcode::ContinueVal => {
                let Value::Continuation(mut cont) = self.pop_val() else { panic!() };
                let val = self.pop_val();

                // new reset frame
                self.reset_frames[cont.frame] = self.callstack.len();

                // add continuation to call stack (return to here)
                cont.callstack[0].ret = self.ip;
                self.callstack.extend(cont.callstack.into_vec());

                // call continuation
                self.ip = cont.ret;
                self.push_val(val);
            }
            Opcode::Print => match self.pop_val() {
                Value::Str(s) => println!("{}", s),
                Value::Int(i) => println!("{}", i),
                _ => todo!(),
            },
            Opcode::Halt => {
                self.halted = true;
            }
        }
    }
}
