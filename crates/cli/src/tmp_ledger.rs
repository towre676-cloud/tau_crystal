fn ledger_seal(args: SealArgs) {
    #[derive(Serialize, Deserialize)]
    struct Leaf { name: String, sha256_hex: String }
    #[derive(Serialize, Deserialize)]
