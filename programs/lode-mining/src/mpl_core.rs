//! Metaplex Core CPI module for Pinocchio
//!
//! Custom CPI implementation for interacting with Metaplex Core program.
//! Based on mpl-core IDL: https://github.com/metaplex-foundation/mpl-core

use pinocchio::{
    account_info::AccountInfo,
    instruction::{AccountMeta, Instruction, Signer},
    pubkey::Pubkey,
    ProgramResult,
};

/// Metaplex Core program ID
pub const MPL_CORE_ID: Pubkey =
    pinocchio_pubkey::pubkey!("CoREENxT6tW1HoK8ypY1SxRMZTcVPm7R94rH4PZNhX7d");

/// Instruction discriminators
pub mod discriminator {
    pub const CREATE_V1: u8 = 0;
    pub const UPDATE_V1: u8 = 15;
    pub const UPDATE_PLUGIN_V1: u8 = 8;
    pub const ADD_PLUGIN_V1: u8 = 2;
}

/// DataState enum for CreateV1
#[repr(u8)]
pub enum DataState {
    AccountState = 0,
    #[allow(dead_code)]
    LedgerState = 1,
}

/// Plugin type enum
#[repr(u8)]
#[allow(dead_code)]
pub enum PluginType {
    Royalties = 0,
    FreezeDelegate = 1,
    BurnDelegate = 2,
    TransferDelegate = 3,
    UpdateDelegate = 4,
    PermanentFreezeDelegate = 5,
    Attributes = 6,
    PermanentTransferDelegate = 7,
    PermanentBurnDelegate = 8,
    Edition = 9,
    MasterEdition = 10,
    AddBlocker = 11,
    ImmutableMetadata = 12,
    VerifiedCreators = 13,
    Autograph = 14,
}

/// Serialize a string in Borsh format (u32 length + bytes)
fn serialize_string(data: &mut Vec<u8>, s: &str) {
    let bytes = s.as_bytes();
    data.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    data.extend_from_slice(bytes);
}

/// Serialize Option<T> in Borsh format
fn serialize_option_none(data: &mut Vec<u8>) {
    data.push(0); // None
}

/// Serialize CreateV1 instruction data
pub fn serialize_create_v1(name: &str, uri: &str, hashrate: u64, created_epoch: u64) -> Vec<u8> {
    let mut data = Vec::with_capacity(256);

    // Discriminator
    data.push(discriminator::CREATE_V1);

    // DataState::AccountState
    data.push(DataState::AccountState as u8);

    // name (string)
    serialize_string(&mut data, name);

    // uri (string)
    serialize_string(&mut data, uri);

    // plugins: Option<Vec<PluginAuthorityPair>> - Some with Attributes plugin
    data.push(1); // Some

    // Vec length = 1 (one plugin)
    data.extend_from_slice(&1u32.to_le_bytes());

    // PluginAuthorityPair {
    //   plugin: Plugin::Attributes { attribute_list: Vec<Attribute> },
    //   authority: Option<PluginAuthority>
    // }

    // Plugin::Attributes variant (index 6)
    data.push(PluginType::Attributes as u8);

    // attribute_list: Vec<Attribute> - 4 attributes
    data.extend_from_slice(&4u32.to_le_bytes());

    // Attribute 1: hashrate
    serialize_string(&mut data, "hashrate");
    serialize_string(&mut data, &hashrate.to_string());

    // Attribute 2: total_burned
    serialize_string(&mut data, "total_burned");
    serialize_string(&mut data, "0");

    // Attribute 3: created_epoch
    serialize_string(&mut data, "created_epoch");
    serialize_string(&mut data, &created_epoch.to_string());

    // Attribute 4: last_upgraded_epoch
    serialize_string(&mut data, "last_upgraded_epoch");
    serialize_string(&mut data, &created_epoch.to_string());

    // authority: Option<PluginAuthority> - None (defaults to owner)
    serialize_option_none(&mut data);

    // external_plugin_adapters: Option<Vec<ExternalPluginAdapterInitInfo>> - None
    serialize_option_none(&mut data);

    data
}

/// Serialize UpdatePluginV1 instruction data for updating Attributes
pub fn serialize_update_attributes(
    hashrate: u64,
    total_burned: u64,
    created_epoch: u64,
    last_upgraded_epoch: u64,
) -> Vec<u8> {
    let mut data = Vec::with_capacity(256);

    // Discriminator
    data.push(discriminator::UPDATE_PLUGIN_V1);

    // Plugin::Attributes variant (index 6)
    data.push(PluginType::Attributes as u8);

    // attribute_list: Vec<Attribute> - 4 attributes
    data.extend_from_slice(&4u32.to_le_bytes());

    // Attribute 1: hashrate
    serialize_string(&mut data, "hashrate");
    serialize_string(&mut data, &hashrate.to_string());

    // Attribute 2: total_burned
    serialize_string(&mut data, "total_burned");
    serialize_string(&mut data, &total_burned.to_string());

    // Attribute 3: created_epoch
    serialize_string(&mut data, "created_epoch");
    serialize_string(&mut data, &created_epoch.to_string());

    // Attribute 4: last_upgraded_epoch
    serialize_string(&mut data, "last_upgraded_epoch");
    serialize_string(&mut data, &last_upgraded_epoch.to_string());

    data
}

/// Create a new Metaplex Core asset with initial hashrate
///
/// Accounts:
/// 0. asset (signer, writable) - The new asset keypair
/// 1. collection (optional) - Collection to add to
/// 2. authority (optional, signer) - Authority for collection
/// 3. payer (signer, writable) - Pays for account creation
/// 4. owner (optional) - Asset owner (defaults to payer)
/// 5. update_authority (optional) - Update authority
/// 6. system_program
/// 7. log_wrapper (optional)
pub struct CreateV1<'a> {
    pub asset: &'a AccountInfo,
    pub payer: &'a AccountInfo,
    pub owner: Option<&'a AccountInfo>,
    pub update_authority: Option<&'a AccountInfo>,
    pub system_program: &'a AccountInfo,
    pub mpl_core_program: &'a AccountInfo,
    pub name: &'a str,
    pub uri: &'a str,
    pub hashrate: u64,
    pub created_epoch: u64,
}

impl<'a> CreateV1<'a> {
    pub fn invoke(&self) -> ProgramResult {
        let data = serialize_create_v1(self.name, self.uri, self.hashrate, self.created_epoch);

        // CreateV1 expects:
        // 0. asset (signer, writable)
        // 1. collection (optional)
        // 2. authority (optional, signer)
        // 3. payer (signer, writable)
        // 4. owner (optional)
        // 5. update_authority (optional)
        // 6. system_program
        let accounts = [
            AccountMeta::writable_signer(self.asset.key()),  // asset (signer, writable)
            AccountMeta::readonly(self.payer.key()),         // collection (skip with payer as placeholder)
            AccountMeta::readonly_signer(self.payer.key()),  // authority (signer)
            AccountMeta::writable_signer(self.payer.key()),  // payer (signer, writable)
            AccountMeta::readonly(self.owner.map(|o| o.key()).unwrap_or(self.payer.key())), // owner
            AccountMeta::readonly(self.update_authority.map(|u| u.key()).unwrap_or(self.payer.key())), // update_authority
            AccountMeta::readonly(self.system_program.key()), // system_program
        ];

        let ix = Instruction {
            program_id: &MPL_CORE_ID,
            accounts: &accounts,
            data: &data,
        };

        let account_infos = &[
            self.asset,
            self.payer,
            self.payer,
            self.payer,
            self.owner.unwrap_or(self.payer),
            self.update_authority.unwrap_or(self.payer),
            self.system_program,
        ];

        pinocchio::program::invoke(&ix, account_infos)
    }

    #[allow(dead_code)]
    pub fn invoke_signed(&self, signers: &[Signer]) -> ProgramResult {
        let data = serialize_create_v1(self.name, self.uri, self.hashrate, self.created_epoch);

        let accounts = [
            AccountMeta::writable_signer(self.asset.key()),
            AccountMeta::readonly(self.payer.key()),
            AccountMeta::readonly_signer(self.payer.key()),
            AccountMeta::writable_signer(self.payer.key()),
            AccountMeta::readonly(self.owner.map(|o| o.key()).unwrap_or(self.payer.key())),
            AccountMeta::readonly(self.update_authority.map(|u| u.key()).unwrap_or(self.payer.key())),
            AccountMeta::readonly(self.system_program.key()),
        ];

        let ix = Instruction {
            program_id: &MPL_CORE_ID,
            accounts: &accounts,
            data: &data,
        };

        let account_infos = &[
            self.asset,
            self.payer,
            self.payer,
            self.payer,
            self.owner.unwrap_or(self.payer),
            self.update_authority.unwrap_or(self.payer),
            self.system_program,
        ];

        pinocchio::program::invoke_signed(&ix, account_infos, signers)
    }
}

/// Update attributes plugin on an existing asset
pub struct UpdateAttributesV1<'a> {
    pub asset: &'a AccountInfo,
    pub payer: &'a AccountInfo,
    pub authority: &'a AccountInfo,
    pub system_program: &'a AccountInfo,
    #[allow(dead_code)]
    pub mpl_core_program: &'a AccountInfo,
    pub hashrate: u64,
    pub total_burned: u64,
    pub created_epoch: u64,
    pub last_upgraded_epoch: u64,
}

impl<'a> UpdateAttributesV1<'a> {
    pub fn invoke(&self) -> ProgramResult {
        let data = serialize_update_attributes(
            self.hashrate,
            self.total_burned,
            self.created_epoch,
            self.last_upgraded_epoch,
        );

        // UpdatePluginV1 expects:
        // 0. asset (writable)
        // 1. collection (optional)
        // 2. payer (signer, writable)
        // 3. authority (optional, signer)
        // 4. system_program
        let accounts = [
            AccountMeta::writable(self.asset.key()),          // asset (writable)
            AccountMeta::readonly(self.payer.key()),          // collection (skip)
            AccountMeta::writable_signer(self.payer.key()),   // payer (signer, writable)
            AccountMeta::readonly_signer(self.authority.key()), // authority (signer)
            AccountMeta::readonly(self.system_program.key()), // system_program
        ];

        let ix = Instruction {
            program_id: &MPL_CORE_ID,
            accounts: &accounts,
            data: &data,
        };

        let account_infos = &[self.asset, self.payer, self.payer, self.authority, self.system_program];

        pinocchio::program::invoke(&ix, account_infos)
    }

    #[allow(dead_code)]
    pub fn invoke_signed(&self, signers: &[Signer]) -> ProgramResult {
        let data = serialize_update_attributes(
            self.hashrate,
            self.total_burned,
            self.created_epoch,
            self.last_upgraded_epoch,
        );

        let accounts = [
            AccountMeta::writable(self.asset.key()),
            AccountMeta::readonly(self.payer.key()),
            AccountMeta::writable_signer(self.payer.key()),
            AccountMeta::readonly_signer(self.authority.key()),
            AccountMeta::readonly(self.system_program.key()),
        ];

        let ix = Instruction {
            program_id: &MPL_CORE_ID,
            accounts: &accounts,
            data: &data,
        };

        let account_infos = &[self.asset, self.payer, self.payer, self.authority, self.system_program];

        pinocchio::program::invoke_signed(&ix, account_infos, signers)
    }
}

/// Parse hashrate from asset account data
/// Returns (hashrate, total_burned, created_epoch, last_upgraded_epoch)
pub fn parse_miner_attributes(data: &[u8]) -> Option<(u64, u64, u64, u64)> {
    // This is a simplified parser. In production, we'd need to properly
    // deserialize the Core asset format and find the Attributes plugin.
    // For now, we'll scan for our attribute keys.

    let data_str = core::str::from_utf8(data).ok()?;

    let mut hashrate = 0u64;
    let mut total_burned = 0u64;
    let mut created_epoch = 0u64;
    let mut last_upgraded_epoch = 0u64;

    // Simple pattern matching for attribute values
    // In production, this should properly deserialize the binary format
    if let Some(pos) = data_str.find("hashrate") {
        // Find the value after the key
        let after_key = &data_str[pos + 8..];
        if let Some(end) = after_key.find(|c: char| !c.is_ascii_digit()) {
            if let Ok(val) = after_key[..end].parse::<u64>() {
                hashrate = val;
            }
        }
    }

    if let Some(pos) = data_str.find("total_burned") {
        let after_key = &data_str[pos + 12..];
        if let Some(end) = after_key.find(|c: char| !c.is_ascii_digit()) {
            if let Ok(val) = after_key[..end].parse::<u64>() {
                total_burned = val;
            }
        }
    }

    if let Some(pos) = data_str.find("created_epoch") {
        let after_key = &data_str[pos + 13..];
        if let Some(end) = after_key.find(|c: char| !c.is_ascii_digit()) {
            if let Ok(val) = after_key[..end].parse::<u64>() {
                created_epoch = val;
            }
        }
    }

    if let Some(pos) = data_str.find("last_upgraded_epoch") {
        let after_key = &data_str[pos + 19..];
        if let Some(end) = after_key.find(|c: char| !c.is_ascii_digit()) {
            if let Ok(val) = after_key[..end].parse::<u64>() {
                last_upgraded_epoch = val;
            }
        }
    }

    Some((hashrate, total_burned, created_epoch, last_upgraded_epoch))
}
