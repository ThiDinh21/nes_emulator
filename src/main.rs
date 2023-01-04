pub struct CPU {
    /// https://www.nesdev.org/wiki/CPU_registers
    /// reg x, y, a: 1 byte
    /// status register: 1 byte
    /// stack pointer: 1 byte
    /// program counter: 2 bytes
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    pub program_counter: u16,
    /// https://www.nesdev.org/wiki/CPU_memory_map
    pub memory: [u8; 0xFFFF],
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    //  The CPU works in a constant cycle:
    // - Fetch next execution instruction from the instruction memory
    // - Decode the instruction
    // - Execute the instruction
    // - Repeat the cycle
    pub fn run(&mut self) {
        loop {
            let opscode = self.mem_read(self.program_counter);
            self.program_counter += 1;

            match opscode {
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#BRK
                // BRK - Force Interrupt
                // The BRK instruction forces the generation of an interrupt request.
                // The program counter and processor status are pushed on the stack then
                // the IRQ interrupt vector at $FFFE/F is loaded into the PC and the break
                // flag in the status set to one.
                0x00 => {
                    self.status = self.status | 0b0001_0000;

                    return;
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#INX
                // INX - Increment X Register
                // Adds one to the X register setting the zero and negative flags as appropriate.
                0xE8 => {
                    (self.register_x, _) = self.register_x.overflowing_add(1);
                    self.update_zero_and_negative_flag(self.register_x);
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#LDA
                // LDA 0xnn - Load Accumulator
                0xA9 => {
                    let param = self.mem_read(self.program_counter);
                    self.program_counter += 1;

                    self.lda(param);
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#TAX
                // TAX - Transfer Accumulator to X
                0xAA => self.tax(),
                _ => todo!(""),
            }
        }
    }

    /// reset the state (registers and flags)
    /// set program_counter to the 16-bit address that is stored at 0xFFFC
    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = 0;
        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    pub fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    pub fn mem_read_u16(&self, addr: u16) -> u16 {
        let index = addr as usize;
        let bytes = self.memory[index..=index + 1]
            .try_into()
            .expect("slice with incorect length");

        return u16::from_le_bytes(bytes);
    }

    pub fn mem_write_u16(&mut self, addr: u16, data: u16) {
        let bytes = data.to_le_bytes();

        self.mem_write(addr, bytes[0]);
        self.mem_write(addr + 1, bytes[1]);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        // [0x8000 .. 0xFFFF] is reserved for program's ROM
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    // Load Accumulator
    // Loads a byte of memory into the accumulator setting the zero and negative flags as appropriate.
    fn lda(&mut self, value: u8) {
        self.register_a = value;

        self.update_zero_and_negative_flag(self.register_a);
    }

    // Transfer Accumulator to X
    // Copies the current contents of the accumulator into the X register and sets the zero and negative
    // flags as appropriate.
    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flag(self.register_x);
    }

    // set bit 2 of status register if result == 0.
    // set last bit of status register if bit 7 of result is set.
    fn update_zero_and_negative_flag(&mut self, result: u8) {
        if result == 0 {
            self.status = self.status | 0b0000_0010;
        } else {
            self.status = self.status & 0b1111_1101;
        }

        if result & 0b1000_0000 != 0 {
            self.status = self.status | 0b1000_0000;
        } else {
            self.status = self.status & 0b0111_1111;
        }
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immidiate_load_data() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        // zero flag should be 0
        assert!(cpu.status & 0b0000_0010 == 0);
        // negative flag should be 0
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
        // zero flag should be 1
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xaa_tax_transfer_a_to_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x69, 0xaa, 0x00]);
        assert_eq!(cpu.register_x, 0x69);
        // zero flag should be 0
        assert!(cpu.status & 0b0000_0010 == 0);
        // negative flag should be 0
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 2)
    }
}
