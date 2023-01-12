use crate::cpu::AddressingMode;
use lazy_static::lazy_static;
use std::collections::HashMap;

pub struct OpCode {
    pub code: u8,
    pub abbrv: &'static str,
    pub bytes: u8,
    pub cycles: u8,
    pub mode: AddressingMode,
}

impl OpCode {
    fn new(code: u8, abbrv: &'static str, bytes: u8, cycles: u8, mode: AddressingMode) -> Self {
        OpCode {
            code,
            abbrv,
            bytes,
            cycles,
            mode,
        }
    }
}

lazy_static! {
    pub static ref CPU_OPCODES: Vec<OpCode> = vec![
        // ADC
        OpCode::new(0x69, "ADC", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x65, "ADC", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x75, "ADC", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x6D, "ADC", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x7D, "ADC", 3, 4 /* +1 if page crossed */, AddressingMode::Absolute_X),
        OpCode::new(0x79, "ADC", 3, 4 /* +1 if page crossed */, AddressingMode::Absolute_Y),
        OpCode::new(0x61, "ADC", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x71, "ADC", 2, 5 /* +1 if page crossed */, AddressingMode::Indirect_Y),
        // AND
        OpCode::new(0x29, "AND", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x25, "AND", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x35, "AND", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x2D, "AND", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x3D, "AND", 3, 4 /* +1 if page crossed */, AddressingMode::Absolute_X),
        OpCode::new(0x39, "AND", 3, 4 /* +1 if page crossed */, AddressingMode::Absolute_Y),
        OpCode::new(0x21, "AND", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x31, "AND", 2, 5 /* +1 if page crossed */, AddressingMode::Indirect_Y),
        // ASL
        OpCode::new(0x0A, "ASL", 1, 2, AddressingMode::NoneAddressing),
        OpCode::new(0x06, "ASL", 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0x16, "ASL", 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0x0E, "ASL", 3, 6, AddressingMode::Absolute),
        OpCode::new(0x1E, "ASL", 3, 7, AddressingMode::Absolute_X),
        // BCC
        OpCode::new(0x90, "BCC", 2, 2 /* +1 if branch succeeds
                                         +2 if to a new page */, AddressingMode::NoneAddressing),
        // BRK
        OpCode::new(0x00, "BRK", 1, 7, AddressingMode::NoneAddressing),
        // INX
        OpCode::new(0xE8, "INX", 1, 2, AddressingMode::NoneAddressing),
        // LDA
        OpCode::new(0xA9, "LDA", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xA5, "LDA", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xB5, "LDA", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xAD, "LDA", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xBD, "LDA", 3, 4 /* +1 if page crossed */, AddressingMode::Absolute_X),
        OpCode::new(0xB9, "LDA", 3, 4 /* +1 if page crossed */, AddressingMode::Indirect_X),
        OpCode::new(0xA1, "LDA", 2, 6, AddressingMode::Immediate),
        OpCode::new(0xB1, "LDA", 2, 5 /* +1 if page crossed */, AddressingMode::Indirect_Y),
        // STA
        OpCode::new(0x85, "STA", 2, 2, AddressingMode::ZeroPage),
        OpCode::new(0x95, "STA", 2, 2, AddressingMode::ZeroPage_X),
        OpCode::new(0x8D, "STA", 3, 3, AddressingMode::Absolute),
        OpCode::new(0x9D, "STA", 3, 3, AddressingMode::Absolute_X),
        OpCode::new(0x99, "STA", 3, 3, AddressingMode::Absolute_Y),
        OpCode::new(0x81, "STA", 2, 2, AddressingMode::Indirect_X),
        OpCode::new(0x91, "STA", 2, 2, AddressingMode::Indirect_Y),
        // TAX
        OpCode::new(0xAA, "TAX", 1, 2, AddressingMode::NoneAddressing),
    ];

    pub static ref OPCODES_MAP: HashMap<u8, &'static OpCode> = {
        let mut map = HashMap::new();
        for cpu_op in CPU_OPCODES.iter() {
            map.insert(cpu_op.code, cpu_op);
        }
        map
    };
}
