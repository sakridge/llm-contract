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
use std::{io::Cursor, mem::size_of};

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

impl MLJobPoolState {}

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
    InvalidValidator,
}

impl From<MLPoolError> for ProgramError {
    fn from(error: MLPoolError) -> Self {
        match error {
            MLPoolError::InvalidInstruction => ProgramError::Custom(0),
            MLPoolError::InvalidPoolCreator => ProgramError::Custom(1),
            MLPoolError::InvalidValidator => ProgramError::Custom(2),
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
        MLPoolInstruction::InitializePool { key } => {}
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

    fn initialize_vault(creator: Pubkey) -> Account {
        let mut vault_creator_account =
            Account::new(42, LendingState::get_packed_len(), &crate::id());
        let vault_creator_account_info: AccountInfo =
            (&creator, true, &mut vault_creator_account).into();
        let id =
            MLPoolInstruction::pack(&MLPoolInstruction::InitializeVaultCreator { key: creator });
        let accounts = vec![vault_creator_account_info];
        process_instruction(&crate::id(), &accounts, &id).unwrap();
        vault_creator_account
    }

    #[test]
    fn test_initialize_vault_creator() {
        let creator = Pubkey::new_unique();
        let account = initialize_vault(creator);
        let lending_state = LendingState::unpack(&account.data()).unwrap();
        assert_eq!(lending_state.vault_creators.len(), 1);
        assert_eq!(lending_state.vault_creators[0], creator);
    }

    #[test]
    fn test_create_vault() {
        let vaults_manager = Pubkey::new_unique();
        let vault_owner = Pubkey::new_unique();
        let new_vault = Pubkey::new_unique();
        let mut vaults_manager_account = initialize_vault(vault_owner);

        let instruction = LendingInstruction::pack(&LendingInstruction::CreateVault {});

        //todo: should the owner be the crate::id? does it matter?
        let mut vault_creator_account = Account::new(42, 0, &crate::id());

        let mut new_vault_account = Account::new(42, VaultState::get_packed_len(), &crate::id());

        let vault_creator_account_info: AccountInfo =
            (&vault_owner, true, &mut vault_creator_account).into();

        let vaults_manager_account_info: AccountInfo =
            (&vaults_manager, true, &mut vaults_manager_account).into();

        let new_vault_account_info: AccountInfo = (&new_vault, true, &mut new_vault_account).into();

        let accounts = vec![
            vaults_manager_account_info,
            vault_creator_account_info,
            new_vault_account_info,
        ];
        process_instruction(&crate::id(), &accounts, &instruction).unwrap();
    }

    #[test]
    fn test_lender_deposit() {
        let instruction = LendingInstruction::pack(&LendingInstruction::LenderDeposit {});
        let accounts = vec![];
        process_instruction(&crate::id(), &accounts, &instruction).unwrap();
        assert!(accounts[0].data.borrow().is_empty());
    }

    // A test to
    #[test]
    fn test_something() {}
}
