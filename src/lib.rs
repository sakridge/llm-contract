use bytemuck::{Pod, PodCastError, Zeroable};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    hash::Hash,
    msg,
    program_error::ProgramError,
    pubkey::{Pubkey, PUBKEY_BYTES},
};
use std::{
    io::{Cursor, Read, Write},
    mem::size_of,
};

#[cfg(feature = "serde-traits")]
use {
    crate::serialization::coption_fromstr,
    serde::{Deserialize, Serialize},
    serde_with::{As, DisplayFromStr},
};

// TODO: gen new
solana_program::declare_id!("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");

#[derive(Default)]
struct MLJobPoolState {
    jobs: Vec<MLJob>,
    validator_whitelist: Vec<Pubkey>,
}

struct MLJob {
    parameters: Vec<u8>,
    attestations: Vec<(Pubkey, Hash)>,
}

struct JobParameters {
    job_type: u32,
    job_paramters: Vec<u8>,
}

struct LlamaJobParameters {
    seed: u64,
    input: Vec<u8>,
    output_len: u32,
}

impl MLJobPoolState {
    pub fn unpack(data: &[u8]) -> Result<Self, MLPoolError> {
        let mut reader = Cursor::new(data);
        let initialized = reader
            .read_u8()
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        if initialized != 1 {
            return Err(MLPoolError::InvalidPoolState);
        }
        let jobs_len = reader
            .read_u64::<LittleEndian>()
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        for i in 0..jobs_len { /* read job */ }
        let validator_whitelist_len = reader
            .read_u64::<LittleEndian>()
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        if reader.get_ref().len()
            < validator_whitelist_len as usize * size_of::<Pubkey>() + reader.position() as usize
        {
            return Err(MLPoolError::InvalidInstruction);
        }
        let mut validator_whitelist = Vec::with_capacity(validator_whitelist_len as usize);
        for i in 0..validator_whitelist_len {
            let mut bytes = [0u8; 32];
            let bytes_read = reader
                .read_exact(&mut bytes)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            let key = Pubkey::from(bytes);
            validator_whitelist.push(key);
        }
        Ok(MLJobPoolState {
            jobs: vec![],
            validator_whitelist,
        })
    }
}

#[repr(C)]
#[cfg_attr(feature = "serde-traits", derive(Serialize, Deserialize))]
enum MLPoolInstruction {
    /* Initialize an ml pool with a whitelist starting with the key
     * accounts:
     *   0 - new vaults manager account
     */
    InitializePool { key: Pubkey },
    AddPoolMember { key: Pubkey },
    RemovePoolMember { key: Pubkey },

    /* ValidateJob
     * accounts:
     *    0 - Vaults manager account - signed: no, ro: yes
     *        Manager account, checks that the creator is in the whitelist
     *    1 - Vault creator - signed: yes: ro: yes
     *    2 - Vault account - signed: yes: ro: no
     *        Account to write the new vault into
     */
    PostJob { parameters: Vec<u8> },
    ValidateJob { parameters: Vec<u8> },
}

#[derive(Debug)]
enum MLPoolError {
    InvalidInstruction,
    InvalidPoolCreator,
    InvalidPoolState,
    InvalidValidator,
}

impl From<MLPoolError> for ProgramError {
    fn from(error: MLPoolError) -> Self {
        match error {
            MLPoolError::InvalidInstruction => ProgramError::Custom(0),
            MLPoolError::InvalidPoolCreator => ProgramError::Custom(1),
            MLPoolError::InvalidValidator => ProgramError::Custom(2),
            MLPoolError::InvalidPoolState => ProgramError::Custom(3),
        }
    }
}

impl MLPoolInstruction {
    #[allow(deprecated)] // for Pubkey::new
    pub(crate) fn unpack_pubkey(input: &[u8]) -> Result<(Pubkey, &[u8]), ProgramError> {
        let pk = input
            .get(..PUBKEY_BYTES)
            .map(Pubkey::new)
            .ok_or(MLPoolError::InvalidInstruction)?;
        Ok((pk, &input[PUBKEY_BYTES..]))
    }

    fn pack_pubkey(key: &Pubkey, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&key.to_bytes());
    }

    pub fn pack(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(size_of::<Self>());
        msg!("buf.len(): {}", buf.len());
        match self {
            &Self::InitializePool { key } => {
                buf.push(0);
                Self::pack_pubkey(&key, &mut buf);
            }
            &Self::AddPoolMember { key } => {
                buf.push(1);
                Self::pack_pubkey(&key, &mut buf);
            }
            &Self::RemovePoolMember { key } => {
                buf.push(2);
                Self::pack_pubkey(&key, &mut buf);
            }
            Self::ValidateJob { parameters } => {}
            Self::PostJob { parameters } => {}
            _ => {
                todo!()
            }
        }
        buf
    }

    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        use MLPoolError::InvalidInstruction;

        let (&tag, rest) = input.split_first().ok_or(InvalidInstruction)?;
        Ok(match tag {
            0 => {
                let (key, _rest) = Self::unpack_pubkey(rest)?;
                MLPoolInstruction::InitializePool { key }
            }
            1 => {
                let (key, _rest) = Self::unpack_pubkey(rest)?;
                MLPoolInstruction::AddPoolMember { key }
            }
            2 => {
                let (key, _rest) = Self::unpack_pubkey(rest)?;
                MLPoolInstruction::RemovePoolMember { key }
            }
            3 => {
                let parameters = vec![];
                MLPoolInstruction::PostJob { parameters }
            }
            4 => {
                let parameters = vec![];
                MLPoolInstruction::ValidateJob { parameters }
            }
            _ => return Err(MLPoolError::InvalidInstruction.into()),
        })
    }
}

impl From<PodCastError> for MLPoolError {
    fn from(e: PodCastError) -> Self {
        MLPoolError::InvalidInstruction
    }
}

// declare and export the program's entrypoint
entrypoint!(process_instruction);

// program entrypoint's implementation
pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    // log a message to the blockchain
    match MLPoolInstruction::unpack(instruction_data)? {
        MLPoolInstruction::InitializePool { key } => {
            let account_info_iter = &mut accounts.iter();
            let new_pool = next_account_info(account_info_iter)?;
            let mut new_pool_data = new_pool.data.borrow_mut();
            let (initialized, new_pool_data) = new_pool_data
                .split_first_mut()
                .ok_or(MLPoolError::InvalidInstruction)?;
            if *initialized != 0 {
                msg!("already initialized, aborting");
                Err(MLPoolError::InvalidInstruction)?;
            }
            msg!("initializing new");
            *initialized = 1;
            let mut cursor = Cursor::new(new_pool_data);
            cursor
                .write_u64::<LittleEndian>(0)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            cursor
                .write_u64::<LittleEndian>(1)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            cursor
                .write(&key.to_bytes())
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
        }
        MLPoolInstruction::AddPoolMember { key: _ } => {}
        MLPoolInstruction::RemovePoolMember { key: _ } => {}
        MLPoolInstruction::PostJob { parameters } => {
            let account_info_iter = &mut accounts.iter();
            let vault_creator_info = next_account_info(account_info_iter)?;
        }
        MLPoolInstruction::ValidateJob { parameters } => {
            let account_info_iter = &mut accounts.iter();
            let vault_creator_info = next_account_info(account_info_iter)?;
        }
    }

    // gracefully exit the program
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_sdk::account::{Account, ReadableAccount};

    fn job_pool_size() -> usize {
        /* jobs */
        size_of::<usize>() + 10 * 50
            /* whitelist */
            + size_of::<usize>() + 10 * size_of::<Pubkey>()
    }

    #[test]
    fn test_initialize_pool() {
        let creator = Pubkey::new_unique();
        let instruction = MLPoolInstruction::InitializePool { key: creator };
        let packed = instruction.pack();

        let mut pool_account = Account::new(42, job_pool_size(), &crate::id());
        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();

        let accounts = vec![pool_account_info];

        process_instruction(&id(), &accounts, &packed).unwrap();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
    }
}
