use bitflags::bitflags;
use crate::{opcodes, bus};
use bus::Bus;

// https://www.nesdev.org/wiki/Stack
const STACK_BOTTOM: u16 = 0x0100;
const STACK_PTR_RESET: u8 = 0xFD;

bitflags! {
    /// https://www.nesdev.org/wiki/Status_flags
    /// 
    /// 7     bit     0
    /// ----       ----
    /// N V s s D I Z C
    /// | | | | | | | |
    /// | | | | | | | +- Carry
    /// | | | | | | +--- Zero
    /// | | | | | +----- Interrupt Disable
    /// | | | | +------- Decimal (not used on NES)
    /// | | + +--------- B flag, No CPU effect
    /// | +------------- Overflow
    /// +--------------- Negative
    pub struct StatusFlags: u8 {
        const CARRY = 0b0000_0001;
        const ZERO = 0b0000_0010;
        const INTERUPT_DISABLE = 0b0000_0100;
        const DECIMAL_MODE = 0b0000_1000;
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
    pub stack_ptr: u8,
    pub bus: Bus,
}

pub trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, addr: u16) -> u16 {
        let lsb = self.mem_read(addr);
        let msb = self.mem_read(addr + 1);

        u16::from_le_bytes([lsb, msb])
    }

    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        let bytes: [u8; 2] = data.to_le_bytes();

        self.mem_write(addr, bytes[0]);
        self.mem_write(addr + 1, bytes[1]);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.bus.mem_write(addr, data);
    }

    fn mem_read_u16(&self, addr: u16) -> u16 {
        self.bus.mem_read_u16(addr)
    }

    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        self.bus.mem_write_u16(addr, data);
    }
}

impl CPU {
    pub fn new(bus: Bus) -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: StatusFlags::from_bits_truncate(0b0010_0100),
            program_counter: 0,
            stack_ptr: STACK_PTR_RESET,
            bus,
        }
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F) 
    where 
        F: FnMut(&mut CPU),
    {
        let ref all_opcodes = *opcodes::OPCODES_MAP;

        //  The CPU works in a constant cycle:
        // - Fetch next execution instruction from the instruction memory
        // - Decode the instruction
        // - Execute the instruction
        // - Repeat the cycle
        loop {
            callback(self);

            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = all_opcodes
                .get(&code)
                .expect(&format!("OpCode {:x} is not recognized", code));

            // All opcodes:
            // https://www.nesdev.org/obelisk-6502-guide/reference.html
            match code {
                // ADC - Add with Carry
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }

                // AND - Logical AND
                0x29 | 0x25 | 0x35 | 0x2D | 0x3D | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }

                // ASL - Arithmetic Shift Left
                0x0A /* Accumulator mode */ => {
                    self.asl_accumulator();
                }
                0x06 | 0x16 | 0x0E | 0x1E => {
                    self.asl(&opcode.mode);
                }

                // BCC - Branch if Carry Clear
                // If the carry flag is clear then add the relative displacement to the program counter to
                // cause a branch to a new location.
                0x90 => {
                    self.branch(!self.status.contains(StatusFlags::CARRY));                        
                }

                // BCS - Branch if Carry Set
                // If the carry flag is set then add the relative displacement to the program counter to
                // cause a branch to a new location.
                0xB0 => {
                    self.branch(self.status.contains(StatusFlags::CARRY));                        
                }

                // BEQ - Branch if Equal
                // If the zero flag is set then add the relative displacement to the program counter to 
                // cause a branch to a new location.
                0xF0 => {
                    self.branch(self.status.contains(StatusFlags::ZERO));
                }

                // BIT - Bit Test
                0x24 | 0x2C => {
                    self.bit(&opcode.mode);
                }

                // BMI - Branch if Minus
                // If the negative flag is set then add the relative displacement to the program counter 
                // to cause a branch to a new location.
                0x30 => {
                    self.branch(self.status.contains(StatusFlags::NEGATIVE));
                }

                // BNE - Branch if Not Equal
                // If the zero flag is clear then add the relative displacement to the program counter to 
                // cause a branch to a new location.
                0xD0 => {
                    self.branch(!self.status.contains(StatusFlags::ZERO));
                }

                // BPL - Branch if Positive
                // If the negative flag is clear then add the relative displacement to the program counter 
                // to cause a branch to a new location.
                0x10 => {
                    self.branch(!self.status.contains(StatusFlags::NEGATIVE));
                }

                // BRK - Force Interrupt
                // The BRK instruction forces the generation of an interrupt request.
                // The program counter and processor status are pushed on the stack then
                // the IRQ interrupt vector at $FFFE/F is loaded into the PC and the break
                // flag in the status set to one.
                0x00 => {
                    self.status.insert(StatusFlags::BREAK1);
                    return;
                }

                // BVC - Branch if Overflow Clear
                // If the overflow flag is clear then add the relative displacement to the program counter 
                // to cause a branch to a new location.
                0x50 => {
                    self.branch(!self.status.contains(StatusFlags::OVERFLOW));
                }

                // BVS - Branch if Overflow Set
                // If the overflow flag is set then add the relative displacement to the program counter 
                // to cause a branch to a new location.
                0x70 => {
                    self.branch(self.status.contains(StatusFlags::OVERFLOW));
                }

                // CLC - Clear Carry Flag
                // Set the carry flag to zero.
                0x18 => self.clear_carry_flag(),

                // CLD - Clear Decimal Mode
                // Set the decimal flag to zero.
                0xD8 => self.status.remove(StatusFlags::DECIMAL_MODE),

                // CLI - Clear Interrupt Disable
                // Clears the interrupt disable flag allowing normal interrupt requests to be serviced.
                0x58 => self.status.remove(StatusFlags::INTERUPT_DISABLE),

                // CLV - Clear Overflow Flag
                // Clears the overflow flag.
                0xB8 => self.status.remove(StatusFlags::OVERFLOW),

                // CMP - Compare
                // Compares the contents of the accumulator with another memory held value and sets
                // the zero and carry flags as appropriate.
                0xC9 | 0xC5 |0xD5 |0xCD |0xDD | 0xD9 | 0xC1 | 0xD1 => {
                    self.compare(&opcode.mode, self.register_a);
                }

                // CPX - Compare X Register
                // Compares the contents of the X register with another memory held value and sets
                // the zero and carry flags as appropriate.
                0xE0 | 0xE4 | 0xEC => {
                    self.compare(&opcode.mode, self.register_x);
                }

                // CPY - Compare Y Register
                // Compares the contents of the Y register with another memory held value and sets
                // the zero and carry flags as appropriate.
                0xC0 | 0xC4 | 0xCC => {
                    self.compare(&opcode.mode, self.register_y);
                }

                // DEC - Decrement Memory
                0xC6 | 0xD6 | 0xCE | 0xDE => {
                    self.dec(&opcode.mode);
                }

                // DEX - Decrement X Register
                0xCA => self.dex(),

                // DEY - Decrement Y Register
                0x88 => self.dey(),

                // EOR - Exclusive OR
                0x49 | 0x45 | 0x55 | 0x4D | 0x5D | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }

                // INC - Increment Memory
                0xE6 | 0xF6 | 0xEE |0xFE  => {
                    self.inc(&opcode.mode);
                }

                // INX - Increment X Register
                0xE8 => {
                    self.register_x = self.register_x.wrapping_add(1);
                    self.update_zero_and_negative_flags(self.register_x);
                }

                // INY - Increment Y Register
                0xC8 => {
                    self.register_y = self.register_y.wrapping_add(1);
                    self.update_zero_and_negative_flags(self.register_y);
                }
                
                // JMP - Jump
                // Sets the program counter to the address specified by the operand.
                0x4C /* Absolute */ => {
                    let jump_addr  = self.mem_read_u16(self.program_counter);
                    self.program_counter = jump_addr;
                }
                0x6C /* Indirect */ => self.indirect_jmp(),

                // JSR - Jump to Subroutine
                0x20 => {
                    // + 2 - 1 to get to the last byte of the JSR opcode
                    self.stack_push_u16(self.program_counter + 2 - 1);
                    let jump_addr  = self.mem_read_u16(self.program_counter);
                    self.program_counter = jump_addr;
                },

                // LDA - Load Accumulator
                // The JSR instruction pushes the address (minus one) of the return point on to the stack
                // and then sets the program counter to the target memory address.
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(&opcode.mode);
                }

                // LDX - Load X Register
                0xA2 | 0xA6 | 0xB6 | 0xAE | 0xBE => {
                    self.ldx(&opcode.mode);
                }

                // LDY - Load Y Register
                0xA0 | 0xA4 | 0xB4 | 0xAC | 0xBC => {
                    self.ldy(&opcode.mode);
                }

                // LSR - Logical Shift Right
                0x4A /* Accumulator mode */  => self.lsr_accumulator(),
                0x46 | 0x56 | 0x4E | 0x5E => {
                    self.lsr(&opcode.mode);
                }

                // NOP - No Operation
                0xEA => {
                    /* Do nothing */
                }

                // ORA - Logical Inclusive OR
                0x09 | 0x05 | 0x15 | 0x0D | 0x1D | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }

                // PHA - Push Accumulator
                // Pushes a copy of the accumulator on to the stack.
                0x48 => self.stack_push(self.register_a),

                // PHP - Push Processor Status
                0x08 => self.php(),

                // PLA - Pull Accumulator
                0x68 => self.pla(),

                // PLP - Pull Processor Status
                0x28 => self.plp(),

                // ROL - Rotate Left
                0x2A /* Accumulator mode */ => {
                    self.rol_accumulator();
                }
                0x26 | 0x36 | 0x2E | 0x3E => {
                    self.rol(&opcode.mode);
                }

                // ROR - Rotate Right
                0x6A /* Accumulator mode */ => {
                    self.ror_accumulator();
                }
                0x66 | 0x76 | 0x6E | 0x7E => {
                    self.ror(&opcode.mode);
                }

                // RTI - Return from Interrupt
                0x40 => self.rti(),

                // RTS - Return from Subroutine
                0x60 => self.rts(),

                // SBC - Subtract with Carry
                0xE9 | 0xE5 | 0xF5 | 0xED | 0xFD | 0xF9 | 0xE1 | 0xF1 => {
                    self.sbc(&opcode.mode);
                }

                // SEC - Set Carry Flag
                0x38 => self.set_carry_flag(),

                // SED - Set Decimal Flag
                0xF8 => self.status.insert(StatusFlags::DECIMAL_MODE),

                // SEI - Set Interrupt Disable
                0x78 => self.status.insert(StatusFlags::INTERUPT_DISABLE),

                // STA - Store Accumulator
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                // STX - Store X Register
                0x86 | 0x96 | 0x8E => {
                    self.stx(&opcode.mode);
                }

                // STY - Store Y Register
                0x84 | 0x94 | 0x8C => {
                    self.sty(&opcode.mode);
                }

                // TAX - Transfer Accumulator to X
                0xAA => self.tax(),

                // TAY - Transfer Accumulator to Y
                0xA8 => self.tay(),

                // TSX - Transfer Stack Pointer to X
                0xBA => self.tsx(),

                // TXA - Transfer X to Accumulator
                0x8A => self.txa(),

                // TXS - Transfer X to Stack Pointer
                0x9A => self.txs(),

                // TYA - Transfer Y to Accumulator
                0x98 => self.tya(),

                _ => todo!(""),
            }

            if self.program_counter == program_counter_state {
                self.program_counter += (opcode.bytes - 1) as u16;
            }
        }
    }

    /// Reset the state (registers and flags)
    /// Set program_counter to the 16-bit address that is stored at 0xFFFC
    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = StatusFlags::from_bits_truncate(0b0010_0100);
        self.program_counter = self.mem_read_u16(0xFFFC);
        self.stack_ptr = STACK_PTR_RESET;
    }

    /// Load catridge's program to memory
    pub fn load(&mut self, program: Vec<u8>) {
        // [0x8000 .. 0xFFFF] is reserved for program's ROM
        for i in 0..(program.len() as u16) {
            self.mem_write(0x0600 + i, program[i as usize]);
        }
        // self.memory[0x0600..(0x0600 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x0600);
    }

    /* STACK FUNCTIONS */
    fn stack_push(&mut self, data: u8) {
        let stack_addr = STACK_BOTTOM.wrapping_add(self.stack_ptr as u16);
        self.mem_write(stack_addr, data);

        let (new_stack_ptr,is_overflowed) = self.stack_ptr.overflowing_sub(1);
        if is_overflowed {
            panic!("Stack overflowed!!!");
        }
        
        self.stack_ptr = new_stack_ptr;
    }

    fn stack_pop(&mut self) -> u8 {
        let (new_stack_ptr,is_underflowed) = self.stack_ptr.overflowing_add(1);
        if is_underflowed {
            panic!("Stack underflowed!!!");
        }
        
        self.stack_ptr = new_stack_ptr;

        let stack_addr = STACK_BOTTOM.wrapping_add(self.stack_ptr as u16);
        self.mem_read(stack_addr)
    }

    fn stack_push_u16(&mut self, data: u16) {
        let msb = (data >> 8) as u8;
        let lsb = (data & 0x00FF) as u8;

        self.stack_push(msb);
        self.stack_push(lsb);
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lsb = self.stack_pop();
        let msb = self.stack_pop();

        u16::from_le_bytes([lsb, msb])
    }

    /* OPCODES */

    /// Add with Carry
    /// This instruction adds the contents of a memory location to the accumulator
    /// together with the carry bit. If overflow occurs the carry bit is set,
    /// this enables multiple byte addition to be performed.
    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);
        self.add_to_register_a(operand);
    }

    /// Logical AND
    /// A logical AND is performed, bit by bit, on the accumulator contents using the
    /// contents of a byte of memory.
    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);
        self.set_register_a(self.register_a & operand);
    }

    /// Arithmetic Shift Left
    /// This operation shifts all the bits of the accumulator one bit left.
    /// Bit 0 is set to 0 and bit 7 is placed in the carry flag. The effect of this operation is
    /// to multiply the memory contents by 2 (ignoring 2's complement considerations), setting
    /// the carry if the result will not fit in 8 bits.
    fn asl_accumulator(&mut self) {
        if self.register_a >> 7 == 0 {
            self.clear_carry_flag();
        } else {
            self.set_carry_flag();
        }
        self.set_register_a(self.register_a << 1);
    }

    /// Arithmetic Shift Left
    /// This operation shifts all the bits of memory contents one bit left.
    /// Bit 0 is set to 0 and bit 7 is placed in the carry flag. The effect of this operation is
    /// to multiply the memory contents by 2 (ignoring 2's complement considerations), setting
    /// the carry if the result will not fit in 8 bits.
    fn asl(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_addr(mode);
        let mut operand = self.mem_read(addr);

        if operand >> 7 == 0 {
            self.clear_carry_flag();
        } else {
            self.set_carry_flag();
        }

        operand = operand << 1;
        self.mem_write(addr, operand as u8);
        self.update_zero_and_negative_flags(operand);

        operand
    }

    /// Bit Test
    /// This instructions is used to test if one or more bits are set in a target memory location. 
    /// The mask pattern in A is ANDed with the value in memory to set or clear the zero flag, but
    /// the result is not kept. Bits 7 and 6 of the value from memory are copied into the N and V flags.
    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);

        if self.register_a & operand == 0 {
            self.status.insert(StatusFlags::ZERO);
        }
        else {
            self.status.remove(StatusFlags::ZERO);
        }

        self.status.set(StatusFlags::OVERFLOW, operand & 0b0100_0000 > 0);
        self.status.set(StatusFlags::NEGATIVE, operand & 0b1000_0000 > 0);
    }

    /// Decrement Memory
    /// Subtracts one from the value held at a specified memory location setting 
    /// the zero and negative flags as appropriate.
    fn dec(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_addr(mode);
        let mut operand = self.mem_read(addr);

        operand = operand.wrapping_sub(1);

        self.mem_write(addr, operand);
        self.update_zero_and_negative_flags(operand);

        operand
    }

    /// Decrement X Register
    /// Subtracts one from the X register setting the zero and negative flags as appropriate.
    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// Decrement Y Register
    /// Subtracts one from the Y register setting the zero and negative flags as appropriate.
    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    /// Exclusive OR
    /// An exclusive OR is performed, bit by bit, on the accumulator contents using the contents 
    /// of a byte of memory.
    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);
        self.set_register_a(self.register_a ^ operand);
    }

    /// Increment Memory
    /// Adds one to the value held at a specified memory location setting the zero and negative 
    /// flags as appropriate.
    fn inc(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_addr(mode);
        let mut operand = self.mem_read(addr);

        operand = operand.wrapping_add(1);

        self.mem_write(addr, operand);
        self.update_zero_and_negative_flags(operand);

        operand
    }

    /// Jump indirect
    /// Sets the program counter to the address specified by the operand.
    fn indirect_jmp(&mut self) {
        // Indirect addressing: https://www.nesdev.org/obelisk-6502-guide/addressing.html#IND
        let indirect_addr  = self.mem_read_u16(self.program_counter);
        let msb_addr: u16;

        // An original 6502 bug:
        // If the indirect vector falls on a page boundary (e.g. $xxFF where xx is any value from $00 to $FF):
        // Fetches the LSB from $xxFF as expected but takes the MSB from $xx00.
        msb_addr = if indirect_addr & 0x00FF == 0x00FF {
             indirect_addr & 0xFF00
        }
        else {
            indirect_addr.wrapping_add(1)
        };

        let lsb = self.mem_read(indirect_addr);
        let msb = self.mem_read(msb_addr);

        self.program_counter = u16::from_le_bytes([lsb, msb]);
    }

    /// Load Accumulator
    /// Loads a byte of memory into the accumulator setting the zero and negative
    /// flags as appropriate.
    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let value = self.mem_read(addr);
        self.set_register_a(value);
    }

    /// Load X Register
    /// Loads a byte of memory into the X register setting the zero and negative
    /// flags as appropriate.
    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let value = self.mem_read(addr);
        self.set_register_x(value);
    }

    /// Load Y Register
    /// Loads a byte of memory into the Y register setting the zero and negative
    /// flags as appropriate.
    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let value = self.mem_read(addr);
        self.set_register_y(value);
    }

    /// Logical Shift Right
    /// Each of the bits in A is shift one place to the right. The bit that was in bit 0 is 
    /// shifted into the carry flag. Bit 7 is set to zero.
    fn lsr_accumulator(&mut self) {
        let bit_0 = self.register_a & 0b0000_0001;

        if bit_0 == 0 {
            self.clear_carry_flag();
        }
        else {
            self.set_carry_flag();
        }

        self.set_register_a(self.register_a >> 1);
    }

    /// Logical Shift Right
    /// Each of the bits of a memory content is shift one place to the right. The bit that was in bit 0 is 
    /// shifted into the carry flag. Bit 7 is set to zero.
    fn lsr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);

        let bit_0 = operand & 0b0000_0001;

        if bit_0 == 0 {
            self.clear_carry_flag();
        }
        else {
            self.set_carry_flag();
        }

        self.mem_write(addr, operand >> 1);
    }

    /// Logical Inclusive OR
    /// An inclusive OR is performed, bit by bit, on the accumulator contents using the contents of a byte of memory.
    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);

        self.set_register_a(self.register_a | operand);
    }

    /// Push Processor Status
    /// Pushes a copy of the status flags on to the stack.
    fn php(&mut self) {
        // https://www.nesdev.org/wiki/Status_flags#The_B_flag
        self.status.insert(StatusFlags::BREAK1);
        self.status.insert(StatusFlags::BREAK2);
        self.stack_push(self.status.bits());
    }

    /// Pull Accumulator
    /// Pulls an 8 bit value from the stack and into the accumulator. 
    /// The zero and negative flags are set as appropriate.
    fn pla(&mut self) {
        let data = self.stack_pop();
        self.set_register_a(data);
    }

    /// Pull Processor Status
    /// Pulls an 8 bit value from the stack and into the processor flags. 
    /// The flags will take on new states as determined by the value pulled.
    fn plp(&mut self) {
        self.status.bits = self.stack_pop();
        self.status.remove(StatusFlags::BREAK1);
        self.status.insert(StatusFlags::BREAK2);
    }

    /// Rotate Left
    /// Move each of the bits in register A place to the left. 
    /// Bit 0 is filled with the current value of the carry flag whilst the old bit 7 becomes the new carry flag value.
    fn rol_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry_flag = self.status.contains(StatusFlags::CARRY);

        if data >> 7 == 1 {
            self.set_carry_flag();
        }
        else {
            self.clear_carry_flag();
        }

        data = data << 1;

        if old_carry_flag {
            data |= 1;
        }

        self.set_register_a(data);
    }

    /// Rotate Left
    /// Move each of the bits in a memory content place to the left. 
    /// Bit 0 is filled with the current value of the carry flag whilst the old bit 7 becomes the new carry flag value.
    fn rol(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_addr(mode);
        let mut data = self.mem_read(addr);
        let old_carry_flag = self.status.contains(StatusFlags::CARRY);

        if data >> 7 == 1 {
            self.set_carry_flag();
        }
        else {
            self.clear_carry_flag();
        }

        data = data << 1;

        if old_carry_flag {
            data |= 1;
        }

        self.mem_write(addr, data);
        self.update_negative_flag(data);
        data
    }

    /// Rotate Right
    /// Move each of the bits in register A place to the right. 
    /// Bit 7 is filled with the current value of the carry flag whilst the old bit 0 becomes the new carry flag value.
    fn ror_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry_flag = self.status.contains(StatusFlags::CARRY);

        if data & 0x1 == 1 {
            self.set_carry_flag();
        }
        else {
            self.clear_carry_flag();
        }

        data = data >> 1;

        if old_carry_flag {
            data |= 0b1000_0000;
        }

        self.set_register_a(data);
    }

    /// Rotate Right
    /// Move each of the bits in a memory content place to the right. 
    /// Bit 7 is filled with the current value of the carry flag whilst the old bit 0 becomes the new carry flag value.
    fn ror(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_addr(mode);
        let mut data = self.mem_read(addr);
        let old_carry_flag = self.status.contains(StatusFlags::CARRY);

        if data & 0x1 == 1 {
            self.set_carry_flag();
        }
        else {
            self.clear_carry_flag();
        }

        data = data >> 1;

        if old_carry_flag {
            data |= 0b1000_0000;
        }

        self.mem_write(addr, data);
        self.update_negative_flag(data);
        data
    }

    /// Return from Interrupt
    /// The RTI instruction is used at the end of an interrupt processing routine. 
    /// It pulls the processor flags from the stack followed by the program counter.
    fn rti(&mut self) {
        self.status.bits = self.stack_pop();
        self.status.remove(StatusFlags::BREAK1);
        self.status.insert(StatusFlags::BREAK2);
        self.program_counter = self.stack_pop_u16();
    }

    /// Return from Subroutine
    /// The RTS instruction is used at the end of a subroutine to return to the calling routine. 
    /// It pulls the program counter (minus one) from the stack.
    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() + 1;
    }

    /// Subtract with Carry
    /// This instruction subtracts the contents of a memory location to the accumulator together 
    /// with the not of the carry bit. If overflow occurs the carry bit is clear, this enables 
    /// multiple byte subtraction to be performed.
    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);
        let operand = (operand as i8).wrapping_neg().wrapping_sub(1);
        self.add_to_register_a(operand as u8);
    }

    /// Store Accumulator
    /// Stores the contents of the accumulator into memory.
    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        self.mem_write(addr, self.register_a);
    }

    /// Store X Register
    /// Stores the contents of the X register into memory.
    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        self.mem_write(addr, self.register_x);
    }

    /// Store Y Register
    /// Stores the contents of the Y register into memory.
    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_addr(mode);
        self.mem_write(addr, self.register_y);
    }

    /// Transfer Accumulator to X
    /// Copies the current contents of the accumulator into the X register and sets
    /// the zero and negative flags as appropriate.
    fn tax(&mut self) {
        self.set_register_x(self.register_a);
    }

    /// Transfer Accumulator to Y
    /// Copies the current contents of the accumulator into the Y register and sets
    /// the zero and negative flags as appropriate.
    fn tay(&mut self) {
        self.set_register_y(self.register_a);
    }

    /// Transfer Stack Pointer to X
    /// Copies the current contents of the stack register into the X register and sets 
    /// the zero and negative flags as appropriate.
    fn tsx(&mut self) {
        self.set_register_x(self.stack_ptr);
    }

    /// Transfer X to Accumulator
    /// Copies the current contents of the X register into the accumulator and sets the 
    /// zero and negative flags as appropriate.
    fn txa(&mut self) {
        self.set_register_a(self.register_x);
    }

    /// Transfer X to Stack Pointer
    /// Copies the current contents of the X register into the stack register.
    fn txs(&mut self) {
        self.stack_ptr = self.register_x;
    }

    /// Transfer Y to Accumulator
    /// Copies the current contents of the Y register into the accumulator and sets the 
    /// zero and negative flags as appropriate.
    fn tya(&mut self) {
        self.set_register_a(self.register_y);
    }

    /* OPCODE HELPERS */

    /// See more: https://skilldrick.github.io/easy6502/#addressing
    fn get_operand_addr(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
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
                let ptr_lsb = base.wrapping_add(self.register_x);
                let ptr_msb = ptr_lsb.wrapping_add(1);

                let lsb = self.mem_read(ptr_lsb as u16);
                let msb = self.mem_read(ptr_msb as u16);

                u16::from_le_bytes([lsb, msb])
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

    /// Add value to register A, set Carry and Overflow , Zero, Negative flags if needed.
    fn add_to_register_a(&mut self, value: u8) {
        let carry_val = self.status.contains(StatusFlags::CARRY);
        let mut sum = self.register_a;
        let carry_1: bool;
        let carry_2: bool;

        (sum, carry_1) = sum.overflowing_add(value);
        (sum, carry_2) = sum.overflowing_add(carry_val as u8);

        if carry_1 || carry_2 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }

        // http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
        if (self.register_a ^ sum) & (value ^ sum) & 0x80 != 0 {
            self.status.insert(StatusFlags::OVERFLOW);
        } else {
            self.status.remove(StatusFlags::OVERFLOW);
        }

        self.set_register_a(sum);
    }

    /// Set value to register A and set Zero and Negative flag if needed.
    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// Set value to register X and set Zero and Negative flag if needed.
    fn set_register_x(&mut self, value: u8) {
        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// Set value to register X and set Zero and Negative flag if needed.
    fn set_register_y(&mut self, value: u8) {
        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    /// Compare a memory held value with some data (e.g. registers) and
    /// sets the zero, negative and carry flags as appropriate.
    fn compare(&mut self, mode: &AddressingMode, compare_with: u8) {
        let addr = self.get_operand_addr(mode);
        let operand = self.mem_read(addr);


        if operand <= compare_with {
            self.set_carry_flag();
        } 
        else {
            self.clear_carry_flag();
        }

        self.update_zero_and_negative_flags(compare_with.wrapping_sub(operand));
    }


    /// Use for branching opcodes (e.g. BEQ, BNE, etc.) that use Relative Adressing Mode. 
    /// Such opcodes will contain a signed 8 bit relative offset (e.g. -128 to +127) which is 
    /// added to program counter if the condition is true. As the program counter itself is 
    /// incremented during instruction execution by two the effective address range for the 
    /// target instruction must be with -126 to +129 bytes of the branch.
    fn branch(&mut self, condition: bool) {
        if condition {
            let displacement = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                    .program_counter
                    .wrapping_add(1)
                    .wrapping_add(displacement as u16);
            self.program_counter = jump_addr;
        }
    }

    /// Set bit 2 of status register if result == 0.
    /// Set last bit of status register if bit 7 of result is set.
    fn update_zero_and_negative_flags(&mut self, result: u8) {
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

    fn update_negative_flag(&mut self, result: u8) {
        if result >> 7 == 1 {
            self.status.insert(StatusFlags::NEGATIVE)
        } else {
            self.status.remove(StatusFlags::NEGATIVE)
        }
    }

    fn set_carry_flag(&mut self) {
        self.status.insert(StatusFlags::CARRY);
    }

    fn clear_carry_flag(&mut self) {
        self.status.remove(StatusFlags::CARRY);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cartridge::test::test_rom;

    #[test]
    fn test_0xa9_lda_immidiate_load_data() {
        let bus = Bus::new(test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 5);
        assert!(cpu.status.bits() & 0b0000_0010 == 0b00);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let bus = Bus::new(test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 10;
        cpu.load_and_run(vec![0xaa, 0x00]);

        assert_eq!(cpu.register_x, 10)
    }

    #[test]
    fn test_5_ops_working_together() {
        let bus = Bus::new(test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let bus = Bus::new(test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_x = 0xff;
        cpu.load_and_run(vec![0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_lda_from_memory() {
        let bus = Bus::new(test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }
}
