use bitflags::bitflags;

use crate::opcodes;

bitflags! {
    /// https://www.nesdev.org/wiki/Status_flags
    /// 7  bit  0
    /// ---- ----
    /// NVss DIZC
    /// |||| ||||
    /// |||| |||+- Carry
    /// |||| ||+-- Zero
    /// |||| |+--- Interrupt Disable
    /// |||| +---- Decimal (not used on NES)
    /// ||++------ B flag, No CPU effect
    /// |+-------- Overflow
    /// +--------- Negative
    pub struct StatusFlags: u8 {
        const CARRY = 0b0000_0001;
        const ZERO = 0b0000_0010;
        const INTERUPT = 0b0000_0100;
        const DECIMAL = 0b0000_1000;
        const BREAK1  = 0b0001_0000;
        const BREAK2  = 0b0010_0000;
        const OVERFLOW = 0b0100_0000;
        const NEGATIVE = 0b1000_0000;
    }
}

/// See more: https://skilldrick.github.io/easy6502/#addressing
/// The addressing mode is a property of an instruction that defines how the CPU should
/// interpret the next 1 or 2 bytes in the instruction stream.
/// For example, a single mnemonic (LDA) actually can be translated into 8 different machine
/// instructions depending on the type of the parameter.
#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    // TODO: implement Indirect, Relative, Implicit and Accumulator
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

pub struct CPU {
    /// https://www.nesdev.org/wiki/CPU_registers
    /// reg x, y, a: 1 byte
    /// status register: 1 byte
    /// stack pointer: 1 byte
    /// program counter: 2 bytes
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: StatusFlags,
    pub program_counter: u16,
    /// https://www.nesdev.org/wiki/CPU_memory_map
    pub memory: [u8; 0xFFFF],
}

trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, addr: u16) -> u16 {
        let lo = self.mem_read(addr) as u16;
        let hi = self.mem_read(addr + 1) as u16;

        (hi << 8) | lo
    }

    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        let bytes = data.to_le_bytes();

        self.mem_write(addr, bytes[0]);
        self.mem_write(addr + 1, bytes[1]);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: StatusFlags::from_bits_truncate(0b0010_0100),
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    //  The CPU works in a constant cycle:
    // - Fetch next execution instruction from the instruction memory
    // - Decode the instruction
    // - Execute the instruction
    // - Repeat the cycle
    pub fn run(&mut self) {
        let ref opcodes = *opcodes::OPCODES_MAP;
        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode {:x} is not recognized", code));

            match code {
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#ADC
                // ADC - Add with Carry
                // This instruction adds the contents of a memory location to the accumulator
                // together with the carry bit. If overflow occurs the carry bit is set, this enables
                // multiple byte addition to be performed.
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#BRK
                // BRK - Force Interrupt
                // The BRK instruction forces the generation of an interrupt request.
                // The program counter and processor status are pushed on the stack then
                // the IRQ interrupt vector at $FFFE/F is loaded into the PC and the break
                // flag in the status set to one.
                0x00 => {
                    self.status.insert(StatusFlags::BREAK1);
                    return;
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#INX
                // INX - Increment X Register
                // Adds one to the X register setting the zero and negative flags as appropriate.
                0xE8 => {
                    self.register_x = self.register_x.wrapping_add(1);
                    self.update_zero_and_negative_flag(self.register_x);
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#LDA
                // LDA - Load Accumulator
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(&opcode.mode);
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#STA
                // STA - Store Accumulator
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }
                // https://www.nesdev.org/obelisk-6502-guide/reference.html#TAX
                // TAX - Transfer Accumulator to X
                0xAA => self.tax(),
                _ => todo!(""),
            }

            if self.program_counter == program_counter_state {
                self.program_counter += (opcode.bytes - 1) as u16;
            }
        }
    }

    /// reset the state (registers and flags)
    /// set program_counter to the 16-bit address that is stored at 0xFFFC
    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = StatusFlags::from_bits_truncate(0b0010_0100);
        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        // [0x8000 .. 0xFFFF] is reserved for program's ROM
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    /// ADC - Add with Carry
    /// This instruction adds the contents of a memory location to the accumulator
    /// together with the carry bit. If overflow occurs the carry bit is set,
    /// this enables multiple byte addition to be performed.
    pub fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);
        self.add_to_register_a(operand);
    }

    /// Load Accumulator
    /// Loads a byte of memory into the accumulator setting the zero and negative flags as appropriate.
    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let value = self.mem_read(addr);
        self.set_register_a(value);
    }

    /// Store Accumulator
    /// Stores the contents of the accumulator into memory.
    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        self.mem_write(addr, self.register_a);
    }

    // Transfer Accumulator to X
    // Copies the current contents of the accumulator into the X register and sets the zero and negative
    // flags as appropriate.
    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flag(self.register_x);
    }

    /// See more: https://skilldrick.github.io/easy6502/#addressing
    fn get_operand_addr(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => return self.program_counter,
            AddressingMode::ZeroPage => return self.mem_read(self.program_counter) as u16,
            AddressingMode::ZeroPage_X => {
                let param = self.mem_read(self.program_counter);
                let addr = param.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let param = self.mem_read(self.program_counter);
                let addr = param.wrapping_add(self.register_y) as u16;
                addr
            }
            AddressingMode::Absolute => return self.mem_read_u16(self.program_counter),
            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);
                let ptr_lo = base.wrapping_add(self.register_x);
                let ptr_hi = ptr_lo.wrapping_add(1);

                let lo = self.mem_read(ptr_lo as u16);
                let hi = self.mem_read(ptr_hi as u16);

                return u16::from_le_bytes([lo, hi]);
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);
                let deref_base = self.mem_read_u16(base as u16);

                deref_base.wrapping_add(self.register_y as u16)
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {mode:?} is not supported");
            }
        }
    }

    /// add value to register A, set Carry and Overflow , Zero, Negative
    /// flags if needed,
    fn add_to_register_a(&mut self, value: u8) {
        let carry_val = self.status.contains(StatusFlags::CARRY);
        let mut sum = self.register_a;
        let carry_1: bool;
        let carry_2: bool;

        (sum, carry_1) = sum.overflowing_add(value);
        (sum, carry_2) = sum.overflowing_add(carry_val as u8);

        if carry_1 || carry_2 {
            self.status.insert(StatusFlags::CARRY);
        } else {
            self.status.remove(StatusFlags::CARRY);
        }

        // http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
        if (self.register_a ^ sum) & (value ^ sum) & 0x80 != 0 {
            self.status.insert(StatusFlags::OVERFLOW);
        } else {
            self.status.remove(StatusFlags::OVERFLOW);
        }

        self.set_register_a(sum);
    }

    /// set value to register A and set Zero and Negative flag if needed
    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flag(self.register_a);
    }

    // set bit 2 of status register if result == 0.
    // set last bit of status register if bit 7 of result is set.
    fn update_zero_and_negative_flag(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(StatusFlags::ZERO);
        } else {
            self.status.remove(StatusFlags::ZERO);
        }

        if result & 0b1000_0000 != 0 {
            self.status.insert(StatusFlags::NEGATIVE);
        } else {
            self.status.remove(StatusFlags::NEGATIVE);
        }
    }
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
        assert!(!cpu.status.contains(StatusFlags::ZERO));
        // negative flag should be 0
        assert!(!cpu.status.contains(StatusFlags::NEGATIVE));
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
        // zero flag should be 1
        assert!(cpu.status.contains(StatusFlags::ZERO));
    }

    #[test]
    fn test_0xaa_tax_transfer_a_to_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x69, 0xaa, 0x00]);
        assert_eq!(cpu.register_x, 0x69);
        // zero flag should be 0
        assert!(!cpu.status.contains(StatusFlags::ZERO));
        // negative flag should be 0
        assert!(!cpu.status.contains(StatusFlags::NEGATIVE));
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

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_adc_0x69() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x50);
        // set reg_a to 0x55
        // add reg_a with 0xFF
        cpu.load_and_run(vec![0xa5, 0x10, 0x69, 0x50, 0x00]);

        assert_eq!(cpu.register_a, 0xa0);
        assert!(cpu.status.contains(StatusFlags::OVERFLOW));
        assert!(!cpu.status.contains(StatusFlags::CARRY));
    }
}
