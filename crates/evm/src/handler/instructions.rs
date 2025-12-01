use reth_revm::{
    bytecode::opcode::{BLOBBASEFEE, BLOBHASH},
    context::Host,
    handler::instructions::{EthInstructions, InstructionProvider},
    interpreter::{
        Instruction, InstructionContext, InstructionTable, InterpreterTypes, instruction_table,
    },
};

/// Taiko instruction contains list of mainnet instructions that is used for Interpreter
/// execution, contains custom Taiko instructions as well.
#[derive(Debug)]
pub struct TaikoInstructions<WIRE: InterpreterTypes, HOST: ?Sized> {
    /// Table containing instruction implementations indexed by opcode.
    inner: EthInstructions<WIRE, HOST>,
}

impl<WIRE, HOST: Host + ?Sized> Clone for TaikoInstructions<WIRE, HOST>
where
    WIRE: InterpreterTypes,
{
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone() }
    }
}

impl<WIRE, HOST> TaikoInstructions<WIRE, HOST>
where
    WIRE: InterpreterTypes,
    HOST: Host,
{
    /// Returns `TaikoInstructions` with mainnet spec.
    /// This function also customizes the instruction table by replacing
    /// the BLOBBASEFEE instruction with Taiko's custom implementation.
    pub fn new_taiko_mainnet() -> Self {
        let mut table = instruction_table::<WIRE, HOST>();

        table[BLOBBASEFEE as usize] = Instruction::new(blob_basefee, 2);
        table[BLOBHASH as usize] = Instruction::new(blob_hash, 3);

        Self::new(table)
    }

    /// Returns a new instance of `TaikoInstructions` with custom instruction table.
    #[inline]
    pub fn new(base_table: InstructionTable<WIRE, HOST>) -> Self {
        Self { inner: EthInstructions::new(base_table) }
    }

    /// Inserts a new instruction into the instruction table.
    #[inline]
    pub fn insert_instruction(&mut self, opcode: u8, instruction: Instruction<WIRE, HOST>) {
        self.inner.insert_instruction(opcode, instruction);
    }
}

impl<IT, CTX> InstructionProvider for TaikoInstructions<IT, CTX>
where
    IT: InterpreterTypes,
    CTX: Host,
{
    type InterpreterTypes = IT;
    type Context = CTX;

    fn instruction_table(&self) -> &InstructionTable<Self::InterpreterTypes, Self::Context> {
        self.inner.instruction_table()
    }
}

impl<WIRE, HOST> Default for TaikoInstructions<WIRE, HOST>
where
    WIRE: InterpreterTypes,
    HOST: Host,
{
    fn default() -> Self {
        Self::new_taiko_mainnet()
    }
}

/// Custom implementation of BLOBBASEFEE instruction for Taiko EVM.
/// In Taiko, the BLOBBASEFEE instruction is not activated,
/// so it halts the interpreter when executed.
pub fn blob_basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    context.interpreter.halt_not_activated();

    return;
}

/// Custom implementation of BLOBHASH instruction for Taiko EVM.
/// In Taiko, the BLOBHASH instruction is not activated,
/// so it halts the interpreter when executed.
pub fn blob_hash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    context: InstructionContext<'_, H, WIRE>,
) {
    context.interpreter.halt_not_activated();

    return;
}
