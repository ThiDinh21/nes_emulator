pub struct CPU {
    /// https://www.nesdev.org/wiki/CPU_registers
    /// reg x, y, a: 1 byte
    /// status register: 1 byte
    /// stack pointer: 1 byte
    /// program counter: 2 bytes
    pub register_a: u8,
    pub status: u8,
    pub program_counter: u16,
}

impl CPU {
    pub fn mew() -> Self {
        CPU {
            register_a: 0,
            status: 0,
            program_counter: 0,
        }
    }

    pub fn interpret(&mut self, program: Vec<u8>) {
        //  The CPU works in a constant cycle:
        // - Fetch next execution instruction from the instruction memory
        // - Decode the instruction
        // - Execute the instruction
        // - Repeat the cycle
        self.program_counter = 0;

        loop {
            let opscode = program[self.program_counter as usize];
            self.program_counter += 1;

            match opscode {
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#LDA
                // LDA 0xnn
                // LDA - Load Accumulator
                // Loads a byte of memory into the accumulator setting the zero and negative flags as appropriate.
                0xA9 => {
                    let param = program[self.program_counter as usize];
                    self.program_counter += 1;

                    self.register_a = param;

                    if self.register_a == 0 {
                        self.status = self.status | 0b0000_0010;
                    } else {
                        self.status = self.status & 0b1111_1101;
                    }

                    if self.register_a & 0b1000_0000 != 0 {
                        self.status = self.status | 0b1000_0000;
                    } else {
                        self.status = self.status & 0b0111_1111;
                    }
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#BRK
                // BRK
                // BRK - Force Interrupt
                // The BRK instruction forces the generation of an interrupt request.
                // The program counter and processor status are pushed on the stack then
                // the IRQ interrupt vector at $FFFE/F is loaded into the PC and the break
                // flag in the status set to one.
                0x00 => {
                    self.status = self.status | 0b0001_0000;

                    return;
                }
                _ => todo!(""),
            }
        }
    }
}

fn main() {
    println!("Hello, world!");
}
