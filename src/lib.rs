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

#[derive(Debug)]
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
    pub fn pack(&self, data: &mut [u8]) -> Result<(), MLPoolError> {
        let mut cursor = Cursor::new(data);
        cursor
            .write_u8(1)
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        msg!("writing jobs len: {}", self.jobs.len());
        cursor
            .write_u64::<LittleEndian>(self.jobs.len() as u64)
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        for job in &self.jobs {
            msg!("writing job: {}", job.parameters.len());
            cursor
                .write_u64::<LittleEndian>(job.parameters.len() as u64)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            cursor
                .write(&job.parameters)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            cursor
                .write_u64::<LittleEndian>(job.attestations.len() as u64)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            for attestation in &job.attestations {
                cursor
                    .write(&attestation.0.to_bytes())
                    .map_err(|_e| MLPoolError::InvalidInstruction)?;
                cursor
                    .write(&attestation.1.to_bytes())
                    .map_err(|_e| MLPoolError::InvalidInstruction)?;
            }
        }
        cursor
            .write_u64::<LittleEndian>(self.validator_whitelist.len() as u64)
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        for key in self.validator_whitelist.iter() {
            cursor
                .write(&key.to_bytes())
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
        }
        Ok(())
    }

    pub fn unpack(data: &[u8]) -> Result<Self, MLPoolError> {
        let mut reader = Cursor::new(data);
        let initialized = reader
            .read_u8()
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        msg!("init'ed?");
        if initialized != 1 {
            return Err(MLPoolError::InvalidPoolState);
        }
        msg!("init'ed");
        let jobs_len = reader
            .read_u64::<LittleEndian>()
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        let mut jobs = Vec::with_capacity(jobs_len as usize);
        msg!("jobs_len: {}", jobs_len);
        for i in 0..jobs_len {
            let parameters_len = reader
                .read_u64::<LittleEndian>()
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            let mut parameters = vec![0u8; parameters_len as usize];
            reader
                .read_exact(&mut parameters)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;

            let attestations_len = reader
                .read_u64::<LittleEndian>()
                .map_err(|_e| MLPoolError::InvalidInstruction)?;

            let mut attestations = Vec::with_capacity(attestations_len as usize);
            for j in 0..attestations_len {
                let mut bytes = [0u8; 32];

                let bytes_read = reader
                    .read_exact(&mut bytes)
                    .map_err(|_e| MLPoolError::InvalidInstruction)?;
                let key = Pubkey::from(bytes);

                reader
                    .read_exact(&mut bytes)
                    .map_err(|_e| MLPoolError::InvalidInstruction)?;
                let hash = Hash::from(bytes);
                attestations.push((key, hash));
            }

            msg!("{} job: {}", i, parameters.len());
            jobs.push(MLJob {
                parameters,
                attestations,
            });
        }
        let validator_whitelist_len = reader
            .read_u64::<LittleEndian>()
            .map_err(|_e| MLPoolError::InvalidInstruction)?;
        if reader.get_ref().len()
            < validator_whitelist_len as usize * size_of::<Pubkey>() + reader.position() as usize
        {
            msg!("bad len");
            return Err(MLPoolError::InvalidInstruction);
        }
        let mut validator_whitelist = Vec::with_capacity(validator_whitelist_len as usize);
        for i in 0..validator_whitelist_len {
            msg!("reading key {}", i);
            let mut bytes = [0u8; 32];
            let bytes_read = reader
                .read_exact(&mut bytes)
                .map_err(|_e| MLPoolError::InvalidInstruction)?;
            let key = Pubkey::from(bytes);
            validator_whitelist.push(key);
        }
        msg!("done!");
        Ok(MLJobPoolState {
            jobs,
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
    ValidateJob { job_index: u16, hash: Hash },
}

#[derive(Debug)]
enum MLPoolError {
    InvalidInstruction = 0,
    InvalidPoolCreator = 1,
    InvalidPoolState = 2,
    InvalidValidator = 3,
    InvalidStateSize = 4,
    AlreadyExists = 5,
    BadJobIndex = 6,
    ValidatorNotOnWhitelist = 7,
}

impl From<MLPoolError> for ProgramError {
    fn from(error: MLPoolError) -> Self {
        match error {
            MLPoolError::InvalidInstruction => {
                ProgramError::Custom(MLPoolError::InvalidInstruction as u32)
            }
            MLPoolError::InvalidPoolCreator => {
                ProgramError::Custom(MLPoolError::InvalidPoolCreator as u32)
            }
            MLPoolError::InvalidValidator => {
                ProgramError::Custom(MLPoolError::InvalidValidator as u32)
            }
            MLPoolError::InvalidPoolState => ProgramError::Custom(3),
            MLPoolError::InvalidStateSize => ProgramError::Custom(4),
            MLPoolError::AlreadyExists => ProgramError::Custom(5),
            MLPoolError::BadJobIndex => ProgramError::Custom(6),
            MLPoolError::ValidatorNotOnWhitelist => ProgramError::Custom(6),
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
        msg!("packing buf.len(): {}", buf.len());
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
            Self::ValidateJob { job_index, hash } => {
                buf.push(4);
                let bl = job_index.to_le_bytes();
                buf.extend_from_slice(&bl);
                buf.extend_from_slice(&hash.to_bytes());
            }
            Self::PostJob { parameters } => {
                buf.push(3);
                buf.extend_from_slice(&parameters);
            }
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
            3 => MLPoolInstruction::PostJob {
                parameters: rest.to_vec(),
            },
            4 => {
                let mut cursor = Cursor::new(rest);
                let job_index = cursor
                    .read_u16::<LittleEndian>()
                    .map_err(|_e| MLPoolError::InvalidInstruction)?;
                let mut bytes: [u8; 32] = [0u8; 32];
                cursor
                    .read_exact(&mut bytes)
                    .map_err(|_e| MLPoolError::InvalidInstruction)?;
                MLPoolInstruction::ValidateJob {
                    job_index,
                    hash: Hash::from(bytes),
                }
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
            if new_pool_data.len() <= 2 {
                Err(MLPoolError::InvalidInstruction)?;
            }
            if new_pool_data[0] != 0 {
                msg!("already initialized, aborting");
                Err(MLPoolError::InvalidInstruction)?;
            }
            msg!("initializing new");
            let state = MLJobPoolState {
                jobs: vec![],
                validator_whitelist: vec![key],
            };
            state.pack(&mut new_pool_data)?;
        }
        MLPoolInstruction::AddPoolMember { key: new_key } => {
            // TODO: check that super-user is a signer
            let account_info_iter = &mut accounts.iter();
            let new_pool = next_account_info(account_info_iter)?;
            let mut new_pool_data = new_pool.data.borrow_mut();
            msg!("unpacking..");
            let mut state = MLJobPoolState::unpack(&mut new_pool_data)?;
            msg!("done unpacking..");
            for key in &state.validator_whitelist {
                if *key == new_key {
                    Err(MLPoolError::AlreadyExists)?;
                }
            }
            state.validator_whitelist.push(new_key);
            msg!("packing..");
            state.pack(&mut new_pool_data)?;
        }
        MLPoolInstruction::RemovePoolMember { key: key_to_remove } => {
            // TODO: check that super-user is a signer
            let account_info_iter = &mut accounts.iter();
            let pool = next_account_info(account_info_iter)?;
            let mut pool_data = pool.data.borrow_mut();
            msg!("unpacking..");
            let mut state = MLJobPoolState::unpack(&mut pool_data)?;
            msg!("done unpacking..");
            let mut to_remove = None;
            for (i, key) in state.validator_whitelist.iter().enumerate() {
                if *key == key_to_remove {
                    to_remove = Some(i);
                    break;
                }
            }
            if let Some(to_remove) = to_remove {
                state.validator_whitelist.remove(to_remove);
            } else {
                Err(MLPoolError::InvalidInstruction)?;
            }
            msg!("packing..");
            state.pack(&mut pool_data)?;
        }
        MLPoolInstruction::PostJob { parameters } => {
            let account_info_iter = &mut accounts.iter();
            let pool = next_account_info(account_info_iter)?;
            let mut pool_data = pool.data.borrow_mut();
            msg!("post job: {}", parameters.len());
            let mut state = MLJobPoolState::unpack(&mut pool_data)?;
            state.jobs.push(MLJob {
                parameters,
                attestations: vec![],
            });
            state.pack(&mut pool_data)?;
        }
        MLPoolInstruction::ValidateJob { job_index, hash } => {
            let account_info_iter = &mut accounts.iter();
            let pool = next_account_info(account_info_iter)?;
            let validator = next_account_info(account_info_iter)?;
            msg!("validate");
            if !validator.is_signer {
                msg!("signer error");
                Err(MLPoolError::InvalidInstruction)?;
            }
            let mut pool_data = pool.data.borrow_mut();
            let mut state = MLJobPoolState::unpack(&mut pool_data)?;
            let mut found = false;
            for wl_validator in &state.validator_whitelist {
                msg!("{} .. {}", wl_validator, validator.key);
                if wl_validator == validator.key {
                    found = true;
                    break;
                }
            }
            if !found {
                msg!("whitelist error");
                Err(MLPoolError::ValidatorNotOnWhitelist)?;
            }
            let job_index = job_index as usize;
            msg!("{} {}", job_index, state.jobs.len());
            if job_index >= state.jobs.len() {
                msg!("bad job index");
                Err(MLPoolError::BadJobIndex)?;
            }
            for attestation in &state.jobs[job_index].attestations {
                if attestation.0 == *validator.key {
                    Err(MLPoolError::InvalidInstruction)?;
                }
            }
            state.jobs[job_index]
                .attestations
                .push((*validator.key, hash));
            state.pack(&mut pool_data)?;
        }
    }

    // gracefully exit the program
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use rand::{thread_rng, Rng};
    use solana_sdk::account::{Account, ReadableAccount};

    fn job_pool_size() -> usize {
        /* jobs */
        size_of::<usize>() + 10 * 50
            /* whitelist */
            + size_of::<usize>() + 10 * size_of::<Pubkey>()
    }

    fn initialize_pool() -> (Pubkey, Account) {
        let creator = Pubkey::new_unique();
        let instruction = MLPoolInstruction::InitializePool { key: creator };
        let packed = instruction.pack();

        let mut pool_account = Account::new(42, job_pool_size(), &crate::id());
        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();

        let accounts = vec![pool_account_info];

        process_instruction(&id(), &accounts, &packed).unwrap();

        (creator, pool_account)
    }

    #[test]
    fn test_initialize_pool() {
        let (_creator, pool_account) = initialize_pool();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
    }

    #[test]
    fn test_add_validator() {
        let (creator, mut pool_account) = initialize_pool();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);

        let new_validator = Pubkey::new_unique();
        let instruction = MLPoolInstruction::AddPoolMember { key: new_validator };
        let packed = instruction.pack();

        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();

        let accounts = vec![pool_account_info];
        process_instruction(&id(), &accounts, &packed).unwrap();
        {
            let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
            assert_eq!(pool_state.jobs.len(), 0);
            assert_eq!(pool_state.validator_whitelist.len(), 2);
            assert_eq!(pool_state.validator_whitelist[0], creator);
            assert_eq!(pool_state.validator_whitelist[1], new_validator);
        }

        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();
        let accounts = vec![pool_account_info];
        // Add another
        assert_matches!(
            process_instruction(&id(), &accounts, &packed),
            Err(ProgramError::Custom(5))
        );
    }

    fn add_whitelist_validator(
        new_validator: Pubkey,
        creator: &Pubkey,
        pool_account: &mut Account,
    ) -> Result<Pubkey, ProgramError> {
        let instruction = MLPoolInstruction::AddPoolMember { key: new_validator };
        let packed = instruction.pack();

        let pool_account_info: AccountInfo = (creator, true, pool_account).into();

        // add another
        let accounts = vec![pool_account_info];
        process_instruction(&id(), &accounts, &packed)?;

        Ok(new_validator)
    }

    fn remove_whitelist_validator(
        new_validator: Pubkey,
        creator: &Pubkey,
        pool_account: &mut Account,
    ) -> Result<Pubkey, ProgramError> {
        let instruction = MLPoolInstruction::RemovePoolMember { key: new_validator };
        let packed = instruction.pack();

        let pool_account_info: AccountInfo = (creator, true, pool_account).into();

        // add another
        let accounts = vec![pool_account_info];
        process_instruction(&id(), &accounts, &packed)?;

        Ok(new_validator)
    }

    #[test]
    fn test_remove_validator() {
        let (creator, mut pool_account) = initialize_pool();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);

        let new_validator = Pubkey::new_unique();
        add_whitelist_validator(new_validator, &creator, &mut pool_account).unwrap();
        {
            let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
            assert_eq!(pool_state.jobs.len(), 0);
            assert_eq!(pool_state.validator_whitelist.len(), 2);
            assert_eq!(pool_state.validator_whitelist[0], creator);
            assert_eq!(pool_state.validator_whitelist[1], new_validator);
        }

        // Add another, should fail from already being there
        assert_matches!(
            add_whitelist_validator(new_validator, &creator, &mut pool_account),
            Err(ProgramError::Custom(5))
        );

        // Remove one successfully
        remove_whitelist_validator(new_validator, &creator, &mut pool_account).unwrap();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
        assert_eq!(pool_state.validator_whitelist[0], creator);

        // Remove again, should not find it
        assert_matches!(
            remove_whitelist_validator(new_validator, &creator, &mut pool_account),
            Err(ProgramError::Custom(0))
        );

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
        assert_eq!(pool_state.validator_whitelist[0], creator);
    }

    #[test]
    fn test_add_job() {
        let (creator, mut pool_account) = initialize_pool();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);

        let new_validator = Pubkey::new_unique();
        let mut parameters: [u8; 10] = rand::random();
        let instruction = MLPoolInstruction::PostJob {
            parameters: parameters.to_vec(),
        };
        let packed = instruction.pack();

        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();

        // add a job
        let accounts = vec![pool_account_info];
        process_instruction(&id(), &accounts, &packed).unwrap();
        {
            let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
            assert_eq!(pool_state.jobs.len(), 1);
            assert_eq!(pool_state.jobs[0].parameters, parameters);
            assert_eq!(pool_state.jobs[0].attestations.len(), 0);
            assert_eq!(pool_state.validator_whitelist.len(), 1);
            assert_eq!(pool_state.validator_whitelist[0], creator);
        }

        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();
        let accounts = vec![pool_account_info];
        // Add another
        process_instruction(&id(), &accounts, &packed).unwrap();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 2);
        assert_eq!(pool_state.jobs[0].parameters, parameters);
        assert_eq!(pool_state.jobs[1].parameters, parameters);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
        assert_eq!(pool_state.validator_whitelist[0], creator);

        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();
        let accounts = vec![pool_account_info];

        let parameters2: [u8; 15] = rand::random();
        let instruction = MLPoolInstruction::PostJob {
            parameters: parameters2.to_vec(),
        };
        let packed = instruction.pack();

        // add again
        process_instruction(&id(), &accounts, &packed).unwrap();

        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 3);
        assert_eq!(pool_state.jobs[0].parameters, parameters);
        assert_eq!(pool_state.jobs[1].parameters, parameters);
        assert_eq!(pool_state.jobs[2].parameters, parameters2);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
        assert_eq!(pool_state.validator_whitelist[0], creator);
    }

    #[test]
    fn test_validate_job() {
        let (creator, mut pool_account) = initialize_pool();

        msg!("creator: {}", creator);
        let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
        assert_eq!(pool_state.jobs.len(), 0);
        assert_eq!(pool_state.validator_whitelist.len(), 1);
        assert_eq!(pool_state.validator_whitelist[0], creator);

        let instruction = MLPoolInstruction::ValidateJob {
            job_index: 0,
            hash: Hash::default(),
        };
        let packed = instruction.pack();

        // bad job index since no jobs
        let validator = Pubkey::new_unique();
        let mut validator_account = Account::new(10, 0, &validator);
        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();
        let validator_account_info: AccountInfo = (&creator, true, &mut validator_account).into();
        let accounts = vec![pool_account_info, validator_account_info];
        assert_matches!(
            process_instruction(&id(), &accounts, &packed),
            Err(ProgramError::Custom(6))
        );

        // add a job
        let new_validator = Pubkey::new_unique();
        let mut parameters: [u8; 10] = rand::random();
        let instruction = MLPoolInstruction::PostJob {
            parameters: parameters.to_vec(),
        };
        let packed = instruction.pack();
        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();

        let accounts = vec![pool_account_info];
        process_instruction(&id(), &accounts, &packed).unwrap();

        let instruction = MLPoolInstruction::ValidateJob {
            job_index: 0,
            hash: Hash::default(),
        };
        let packed = instruction.pack();

        // validate it
        let pool_account_info: AccountInfo = (&creator, true, &mut pool_account).into();
        let validator_account_info: AccountInfo = (&creator, true, &mut validator_account).into();
        let accounts = vec![pool_account_info, validator_account_info];
        process_instruction(&id(), &accounts, &packed).unwrap();
        {
            let pool_state = MLJobPoolState::unpack(&pool_account.data()).unwrap();
            assert_eq!(pool_state.jobs.len(), 1);
            assert_eq!(pool_state.jobs[0].parameters, parameters);
            assert_eq!(pool_state.jobs[0].attestations.len(), 1);
            assert_eq!(pool_state.jobs[0].attestations[0].0, creator);
            assert_eq!(pool_state.jobs[0].attestations[0].1, Hash::default());
            assert_eq!(pool_state.validator_whitelist.len(), 1);
            assert_eq!(pool_state.validator_whitelist[0], creator);
        }
    }
}
