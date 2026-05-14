/- Port of execution/test/LocalBlockchain.v.

   Concrete blockchain instance with `BoundedN AddrSize` addresses,
   FMap-backed account balances / contracts / contract states, and an
   executable block builder. Parameterized by `AddrSize` and a `DepthFirst`
   flag for action execution order. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.BlockchainBuilder
import ConCert.Execution.BoundedN
import ConCert.Execution.ChainedList
import ConCert.Execution.Containers
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Utils.Extras

namespace ConCert.Execution.Test.LocalBlockchain

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
open ConCert.Execution.BoundedN
open ConCert.Execution.SerializableBase
open ConCert.Execution.Containers
open ConCert.Execution.ChainedList
open ConCert.Execution.ResultMonad

variable (AddrSize : Nat) (DepthFirst : Bool)

def ContractAddrBase : Nat := AddrSize / 2

abbrev LocalAddress := BoundedN AddrSize

instance local_address_serializable : Serializable (BoundedN AddrSize) where
  serialize := ConCert.Execution.SerializableInstances.BoundedN_equivalence.serialize
  deserialize := ConCert.Execution.SerializableInstances.BoundedN_equivalence.deserialize
  deserialize_serialize :=
    ConCert.Execution.SerializableInstances.BoundedN_equivalence.deserialize_serialize

def address_is_contract_local (a : LocalAddress AddrSize) : Bool :=
  ContractAddrBase AddrSize ≤ a.val

theorem local_address_eqb_spec
    (a b : BoundedN AddrSize) : BoundedN.eqb a b = true ↔ a = b := by
  unfold BoundedN.eqb
  rw [beq_iff_eq]
  constructor
  · exact BoundedN.to_N_inj
  · intro h; rw [h]

instance local_address_decEq : DecidableEq (BoundedN AddrSize) := fun a b =>
  if h : a.val = b.val then
    .isTrue (by cases a; cases b; congr)
  else .isFalse (fun heq => h (by rw [heq]))

@[reducible] def LocalChainBase : ChainBase where
  Address := LocalAddress AddrSize
  address_eqb := BoundedN.eqb
  address_eqb_spec := local_address_eqb_spec AddrSize
  address_eqdec := local_address_decEq AddrSize
  address_ord := BoundedN.instOrd
  address_ord_lawful := BoundedN.instLawfulOrd
  address_serializable := local_address_serializable AddrSize
  address_is_contract := address_is_contract_local AddrSize

/-! This file works under `LocalChainBase AddrSize`. The following
    abbreviations shorten the noisy `@Foo (LocalChainBase AddrSize)`
    spellings. -/
abbrev LCEnv  := @Environment             (LocalChainBase AddrSize)
abbrev LCChainSt := @ChainState           (LocalChainBase AddrSize)
abbrev LCAct  := @Action                  (LocalChainBase AddrSize)
abbrev LCActBody := @ActionBody           (LocalChainBase AddrSize)
abbrev LCWC   := @WeakContract            (LocalChainBase AddrSize)
abbrev LCBH   := @BlockHeader             (LocalChainBase AddrSize)
abbrev LCCtx  := @ContractCallContext     (LocalChainBase AddrSize)
abbrev LCAEErr := @ActionEvaluationError  (LocalChainBase AddrSize)
abbrev LCABErr := @AddBlockError          (LocalChainBase AddrSize)
abbrev LCCBT  := @ChainBuilderType        (LocalChainBase AddrSize)

structure LocalChain where
  lc_height        : Nat
  lc_slot          : Nat
  lc_fin_height    : Nat
  lc_account_balances : FMap (LocalAddress AddrSize) Amount
  lc_contract_state   : FMap (LocalAddress AddrSize) SerializedValue
  lc_contracts        : FMap (LocalAddress AddrSize) (LCWC AddrSize)

def lc_to_env (lc : LocalChain AddrSize) : LCEnv AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  { toChain :=
      { chain_height := lc.lc_height,
        current_slot := lc.lc_slot,
        finalized_height := lc.lc_fin_height },
    env_account_balances := fun a =>
      (FMap.find a lc.lc_account_balances).getD 0,
    env_contract_states  := fun a => FMap.find a lc.lc_contract_state,
    env_contracts        := fun a => FMap.find a lc.lc_contracts }

def lc_initial : LocalChain AddrSize :=
  { lc_height := 0, lc_slot := 0, lc_fin_height := 0,
    lc_account_balances := FMap.empty,
    lc_contract_state   := FMap.empty,
    lc_contracts        := FMap.empty }

/-! ### Executable surface -/

def add_balance (addr : LocalAddress AddrSize) (amt : Amount) (lc : LocalChain AddrSize) :
    LocalChain AddrSize :=
  { lc with
    lc_account_balances :=
      FMap.partial_alter (fun opt => some (amt + opt.getD 0)) addr lc.lc_account_balances }

def transfer_balance (frm to_ : LocalAddress AddrSize) (amount : Amount)
    (lc : LocalChain AddrSize) : LocalChain AddrSize :=
  add_balance AddrSize to_ amount (add_balance AddrSize frm (-amount) lc)

def get_new_contract_addr (lc : LocalChain AddrSize) : Option (LocalAddress AddrSize) :=
  BoundedN.of_N (ContractAddrBase AddrSize + FMap.size lc.lc_contracts)

def add_contract (addr : LocalAddress AddrSize) (wc : LCWC AddrSize)
    (lc : LocalChain AddrSize) : LocalChain AddrSize :=
  { lc with lc_contracts := FMap.add addr wc lc.lc_contracts }

def set_contract_state (addr : LocalAddress AddrSize) (state : SerializedValue)
    (lc : LocalChain AddrSize) : LocalChain AddrSize :=
  { lc with lc_contract_state := FMap.add addr state lc.lc_contract_state }

def weak_error_to_error_init (r : Result SerializedValue SerializedValue) :
    Result SerializedValue (LCAEErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  bind_error (fun err => .init_failed err) r

def weak_error_to_error_receive
    (r : Result (SerializedValue × List (LCActBody AddrSize)) SerializedValue) :
    Result (SerializedValue × List (LCActBody AddrSize)) (LCAEErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  bind_error (fun err => .receive_failed err) r

def send_or_call (origin frm to_ : LocalAddress AddrSize) (amount : Amount)
    (msg : Option SerializedValue) (lc : LocalChain AddrSize) :
    Result (List (LCAct AddrSize) × LocalChain AddrSize) (LCAEErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  if amount < 0 then .Err (.amount_negative amount)
  else if amount > (lc_to_env AddrSize lc).env_account_balances frm then
    .Err (.amount_too_high amount)
  else
    match FMap.find to_ lc.lc_contracts with
    | none =>
      if (LocalChainBase AddrSize).address_is_contract to_ then
        .Err (.no_such_contract to_)
      else
        match msg with
        | none => .Ok ([], transfer_balance AddrSize frm to_ amount lc)
        | some _ => .Err (.no_such_contract to_)
    | some wc =>
      match (lc_to_env AddrSize lc).env_contract_states to_ with
      | none => .Err .internal_error
      | some state =>
        let lc' := transfer_balance AddrSize frm to_ amount lc
        let ctx : LCCtx AddrSize :=
          { ctx_origin := origin, ctx_from := frm,
            ctx_contract_address := to_,
            ctx_contract_balance := (lc_to_env AddrSize lc').env_account_balances to_,
            ctx_amount := amount }
        match weak_error_to_error_receive AddrSize
                (wc_receive wc (lc_to_env AddrSize lc').toChain ctx state msg) with
        | .Err e => .Err e
        | .Ok (new_state, new_actions) =>
          let lc'' := set_contract_state AddrSize to_ new_state lc'
          .Ok (new_actions.map (fun b => { act_origin := origin, act_from := to_, act_body := b }), lc'')

def deploy_contract (origin frm : LocalAddress AddrSize) (amount : Amount)
    (wc : LCWC AddrSize) (setup : SerializedValue)
    (lc : LocalChain AddrSize) :
    Result (List (LCAct AddrSize) × LocalChain AddrSize) (LCAEErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  if amount < 0 then .Err (.amount_negative amount)
  else if amount > (lc_to_env AddrSize lc).env_account_balances frm then
    .Err (.amount_too_high amount)
  else
    match get_new_contract_addr AddrSize lc with
    | none => .Err .too_many_contracts
    | some contract_addr =>
      match FMap.find contract_addr lc.lc_contracts with
      | some _ => .Err .internal_error
      | none =>
        let lc' := transfer_balance AddrSize frm contract_addr amount lc
        let ctx : LCCtx AddrSize :=
          { ctx_origin := origin, ctx_from := frm,
            ctx_contract_address := contract_addr,
            ctx_contract_balance := amount, ctx_amount := amount }
        match weak_error_to_error_init AddrSize
                (wc_init wc (lc_to_env AddrSize lc').toChain ctx setup) with
        | .Err e => .Err e
        | .Ok state =>
          let lc'' := add_contract AddrSize contract_addr wc lc'
          let lc''' := set_contract_state AddrSize contract_addr state lc''
          .Ok ([], lc''')

def execute_action (act : LCAct AddrSize) (lc : LocalChain AddrSize) :
    Result (List (LCAct AddrSize) × LocalChain AddrSize) (LCAEErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  match act.act_body with
  | .act_transfer to_ amount =>
    send_or_call AddrSize act.act_origin act.act_from to_ amount none lc
  | .act_deploy amount wc setup =>
    deploy_contract AddrSize act.act_origin act.act_from amount wc setup lc
  | .act_call to_ amount msg =>
    send_or_call AddrSize act.act_origin act.act_from to_ amount (some msg) lc

def execute_actions :
    (count : Nat) → (acts : List (LCAct AddrSize)) → LocalChain AddrSize → Bool →
    Result (LocalChain AddrSize) (LCABErr AddrSize)
  | _, [], lc, _ => .Ok lc
  | 0, _ :: _, _, _ =>
    letI : ChainBase := LocalChainBase AddrSize
    .Err .action_evaluation_depth_exceeded
  | c + 1, act :: rest, lc, depth_first =>
    letI : ChainBase := LocalChainBase AddrSize
    match execute_action AddrSize act lc with
    | .Ok (next_acts, lc') =>
      let acts' := if depth_first then next_acts ++ rest else rest ++ next_acts
      execute_actions c acts' lc' depth_first
    | .Err act_err => .Err (.action_evaluation_error act act_err)

/-! ### Block validation -/

def validate_header (header : LCBH AddrSize) (chain : Chain) : Bool :=
  letI : ChainBase := LocalChainBase AddrSize
  decide (header.block_height = chain.chain_height + 1) &&
  decide (chain.current_slot < header.block_slot) &&
  decide (chain.finalized_height ≤ header.block_finalized_height) &&
  decide (header.block_finalized_height < header.block_height) &&
  !((LocalChainBase AddrSize).address_is_contract header.block_creator) &&
  decide (header.block_reward ≥ 0)

def find_origin_neq_from (actions : List (LCAct AddrSize)) : Option (LCAct AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  actions.find? (fun act =>
    !((LocalChainBase AddrSize).address_eqb act.act_origin act.act_from))

def find_invalid_root_action (actions : List (LCAct AddrSize)) : Option (LCAct AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  actions.find? (fun act => (LocalChainBase AddrSize).address_is_contract act.act_from)

def add_new_block (header : LCBH AddrSize) (lc : LocalChain AddrSize) : LocalChain AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  let lc' := add_balance AddrSize header.block_creator header.block_reward lc
  { lc' with
    lc_height := header.block_height,
    lc_slot   := header.block_slot,
    lc_fin_height := header.block_finalized_height }

theorem validate_header_valid
    (header : LCBH AddrSize) (chain : Chain) :
    validate_header AddrSize header chain = true →
    @IsValidNextBlock (LocalChainBase AddrSize) header chain := by
  letI : ChainBase := LocalChainBase AddrSize
  intro h
  unfold validate_header at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact
    { valid_height := h.1.1.1.1.1,
      valid_slot := h.1.1.1.1.2,
      valid_finalized_height := ⟨h.1.1.1.2, h.1.1.2⟩,
      valid_creator := h.1.2,
      valid_reward := h.2 }

theorem validate_origin_neq_from_valid
    (actions : List (LCAct AddrSize)) :
    find_origin_neq_from AddrSize actions = none →
    actions.Forall (@act_origin_is_eq_from (LocalChainBase AddrSize)) := by
  letI : ChainBase := LocalChainBase AddrSize
  intro h
  rw [List.forall_iff_forall_mem]
  intro act hin
  have hnone := (List.find?_eq_none).mp h act hin
  simpa using hnone

theorem validate_actions_valid
    (actions : List (LCAct AddrSize)) :
    find_invalid_root_action AddrSize actions = none →
    actions.Forall (@act_is_from_account (LocalChainBase AddrSize)) := by
  intro h
  rw [List.forall_iff_forall_mem]
  intro act hin
  have hnone := (List.find?_eq_none).mp h act hin
  simpa [act_is_from_account] using hnone

theorem add_new_block_equiv
    (header : LCBH AddrSize) (lc : LocalChain AddrSize) :
    @EnvironmentEquiv (LocalChainBase AddrSize)
      (lc_to_env AddrSize (add_new_block AddrSize header lc))
      (@add_new_block_to_env (LocalChainBase AddrSize) header (lc_to_env AddrSize lc)) := by
  letI : ChainBase := LocalChainBase AddrSize
  constructor
  · rfl
  · intro addr
    by_cases h : addr = header.block_creator
    · subst h
      simp [lc_to_env, add_new_block, add_balance, BlockchainBase.add_new_block_to_env,
        BlockchainBase.add_balance, FMap.find_partial_alter, Address.address_eq_refl]
    · have h' : header.block_creator ≠ addr := fun heq => h heq.symm
      simp [lc_to_env, add_new_block, add_balance, BlockchainBase.add_new_block_to_env,
        BlockchainBase.add_balance, FMap.find_partial_alter_ne, h, h', Address.address_eq_ne]
  · intro addr
    rfl
  · intro addr
    rfl

theorem transfer_balance_equiv
    (frm to_ : LocalAddress AddrSize) (amount : Amount) (lc : LocalChain AddrSize) :
    @EnvironmentEquiv (LocalChainBase AddrSize)
      (lc_to_env AddrSize (transfer_balance AddrSize frm to_ amount lc))
      (@BlockchainBase.transfer_balance (LocalChainBase AddrSize) frm to_ amount
        (lc_to_env AddrSize lc)) := by
  letI : ChainBase := LocalChainBase AddrSize
  constructor
  · rfl
  · intro addr
    by_cases hfrm : addr = frm
    · subst addr
      by_cases hto : frm = to_
      · subst to_
        simp [lc_to_env, transfer_balance, add_balance, BlockchainBase.transfer_balance,
          BlockchainBase.add_balance, FMap.find_partial_alter, Address.address_eq_refl]
      · have hto' : to_ ≠ frm := fun h => hto h.symm
        simp [lc_to_env, transfer_balance, add_balance, BlockchainBase.transfer_balance,
          BlockchainBase.add_balance, FMap.find_partial_alter, FMap.find_partial_alter_ne,
          hto, hto', Address.address_eq_refl, Address.address_eq_ne]
    · by_cases hto : addr = to_
      · subst addr
        have hfrm' : frm ≠ to_ := fun h => hfrm h.symm
        simp [lc_to_env, transfer_balance, add_balance, BlockchainBase.transfer_balance,
          BlockchainBase.add_balance, FMap.find_partial_alter, FMap.find_partial_alter_ne,
          hfrm, hfrm', Address.address_eq_refl, Address.address_eq_ne]
      · have hfrm' : frm ≠ addr := fun h => hfrm h.symm
        have hto' : to_ ≠ addr := fun h => hto h.symm
        simp [lc_to_env, transfer_balance, add_balance, BlockchainBase.transfer_balance,
          BlockchainBase.add_balance, FMap.find_partial_alter_ne,
          hfrm, hfrm', hto, hto', Address.address_eq_ne]
  · intro addr
    rfl
  · intro addr
    rfl

theorem add_contract_equiv
    (addr : LocalAddress AddrSize) (wc : LCWC AddrSize) (lc : LocalChain AddrSize) :
    @EnvironmentEquiv (LocalChainBase AddrSize)
      (lc_to_env AddrSize (add_contract AddrSize addr wc lc))
      (@BlockchainBase.add_contract (LocalChainBase AddrSize) addr wc
        (lc_to_env AddrSize lc)) := by
  letI : ChainBase := LocalChainBase AddrSize
  constructor
  · rfl
  · intro a
    rfl
  · intro a
    by_cases h : a = addr
    · subst a
      simp [lc_to_env, add_contract, BlockchainBase.add_contract,
        FMap.find_add, Address.address_eq_refl]
    · have h' : addr ≠ a := fun heq => h heq.symm
      simp [lc_to_env, add_contract, BlockchainBase.add_contract,
        FMap.find_add_ne, h, h', Address.address_eq_ne]
  · intro a
    rfl

theorem set_contract_state_equiv
    (addr : LocalAddress AddrSize) (state : SerializedValue) (lc : LocalChain AddrSize) :
    @EnvironmentEquiv (LocalChainBase AddrSize)
      (lc_to_env AddrSize (set_contract_state AddrSize addr state lc))
      (@BlockchainBase.set_contract_state (LocalChainBase AddrSize) addr state
        (lc_to_env AddrSize lc)) := by
  letI : ChainBase := LocalChainBase AddrSize
  constructor
  · rfl
  · intro a
    rfl
  · intro a
    rfl
  · intro a
    by_cases h : a = addr
    · subst a
      simp [lc_to_env, set_contract_state, BlockchainBase.set_contract_state,
        BlockchainBase.set_chain_contract_state, FMap.find_add, Address.address_eq_refl]
    · have h' : addr ≠ a := fun heq => h heq.symm
      simp [lc_to_env, set_contract_state, BlockchainBase.set_contract_state,
        BlockchainBase.set_chain_contract_state, FMap.find_add_ne, h, h', Address.address_eq_ne]

theorem set_contract_state_preserves_equiv
    (addr : LocalAddress AddrSize) (state : SerializedValue)
    (env₁ env₂ : LCEnv AddrSize) :
    @EnvironmentEquiv (LocalChainBase AddrSize) env₁ env₂ →
    @EnvironmentEquiv (LocalChainBase AddrSize)
      (@BlockchainBase.set_contract_state (LocalChainBase AddrSize) addr state env₁)
      (@BlockchainBase.set_contract_state (LocalChainBase AddrSize) addr state env₂) := by
  letI : ChainBase := LocalChainBase AddrSize
  intro henv
  exact
    { chain_eq := henv.chain_eq,
      account_balances_eq := fun a => henv.account_balances_eq a,
      contracts_eq := fun a => henv.contracts_eq a,
      contract_states_eq := by
        intro a
        by_cases h : a = addr
        · subst a
          simp [BlockchainBase.set_contract_state, BlockchainBase.set_chain_contract_state,
            Address.address_eq_refl]
        · simp [BlockchainBase.set_contract_state, BlockchainBase.set_chain_contract_state,
            Address.address_eq_ne, h, henv.contract_states_eq a] }

theorem add_contract_preserves_equiv
    (addr : LocalAddress AddrSize) (wc : LCWC AddrSize)
    (env₁ env₂ : LCEnv AddrSize) :
    @EnvironmentEquiv (LocalChainBase AddrSize) env₁ env₂ →
    @EnvironmentEquiv (LocalChainBase AddrSize)
      (@BlockchainBase.add_contract (LocalChainBase AddrSize) addr wc env₁)
      (@BlockchainBase.add_contract (LocalChainBase AddrSize) addr wc env₂) := by
  letI : ChainBase := LocalChainBase AddrSize
  intro henv
  exact
    { chain_eq := henv.chain_eq,
      account_balances_eq := fun a => henv.account_balances_eq a,
      contracts_eq := by
        intro a
        by_cases h : a = addr
        · subst a
          simp [BlockchainBase.add_contract, Address.address_eq_refl]
        · simp [BlockchainBase.add_contract, Address.address_eq_ne, h,
            henv.contracts_eq a],
      contract_states_eq := fun a => henv.contract_states_eq a }

def add_block_exec (depth_first : Bool) (lc : LocalChain AddrSize)
    (header : LCBH AddrSize) (actions : List (LCAct AddrSize)) :
    Result (LocalChain AddrSize) (LCABErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  if !validate_header AddrSize header (lc_to_env AddrSize lc).toChain then
    .Err (.invalid_header header)
  else
    match find_origin_neq_from AddrSize actions with
    | some act => .Err (.origin_from_mismatch act)
    | none =>
      match find_invalid_root_action AddrSize actions with
      | some act => .Err (.invalid_root_action act)
      | none =>
        let lc' := add_new_block AddrSize header lc
        execute_actions AddrSize 1000 actions lc' depth_first

def send_or_call_step
    (origin frm to_ : LocalAddress AddrSize) (amount : Amount)
    (msg : Option SerializedValue) (act : LCAct AddrSize)
    (lc_before lc_after : LocalChain AddrSize) (new_acts : List (LCAct AddrSize)) :
    @Action.act_origin (LocalChainBase AddrSize) act = origin →
    @Action.act_from (LocalChainBase AddrSize) act = frm →
    @Action.act_body (LocalChainBase AddrSize) act =
      (match msg with
       | none => @ActionBody.act_transfer (LocalChainBase AddrSize) to_ amount
       | some msg => @ActionBody.act_call (LocalChainBase AddrSize) to_ amount msg) →
    send_or_call AddrSize origin frm to_ amount msg lc_before = .Ok (new_acts, lc_after) →
    @ActionEvaluation (LocalChainBase AddrSize)
      (lc_to_env AddrSize lc_before) act (lc_to_env AddrSize lc_after) new_acts := by
  letI : ChainBase := LocalChainBase AddrSize
  intro horigin hfrom hbody
  have hact : act = @Action.mk (LocalChainBase AddrSize) origin frm
      (match msg with
        | none => @ActionBody.act_transfer (LocalChainBase AddrSize) to_ amount
        | some msg => @ActionBody.act_call (LocalChainBase AddrSize) to_ amount msg) := by
    cases act
    simp at horigin hfrom hbody
    subst_vars
    cases msg <;> rfl
  intro h
  unfold send_or_call at h
  by_cases hneg : amount < 0
  · simp [hneg] at h
  · simp [hneg] at h
    by_cases hbal : amount > (lc_to_env AddrSize lc_before).env_account_balances frm
    · simp [hbal] at h
    · simp [hbal] at h
      cases hcontract : FMap.find to_ lc_before.lc_contracts with
      | none =>
          simp [hcontract] at h
          cases hfmt : (LocalChainBase AddrSize).address_is_contract to_ <;> simp [hfmt] at h
          cases msg with
          | none =>
              simp at h
              cases h
              subst new_acts
              subst lc_after
              exact .eval_transfer origin frm to_ amount
                (not_lt.mp hneg) (not_lt.mp hbal) hfmt hact
                (transfer_balance_equiv AddrSize frm to_ amount lc_before)
                rfl
          | some msg =>
              simp at h
      | some wc =>
          simp [hcontract] at h
          cases hstate : (lc_to_env AddrSize lc_before).env_contract_states to_ with
          | none =>
              simp [hstate] at h
          | some prev_state =>
              simp [hstate] at h
              let lc' := transfer_balance AddrSize frm to_ amount lc_before
              cases hrecv :
                  weak_error_to_error_receive AddrSize
                    (wc_receive wc (lc_to_env AddrSize lc').toChain
                      { ctx_origin := origin, ctx_from := frm,
                        ctx_contract_address := to_,
                        ctx_contract_balance := (lc_to_env AddrSize lc').env_account_balances to_,
                        ctx_amount := amount }
                      prev_state msg) with
              | Err e =>
                  simp [lc', hrecv] at h
              | Ok pair =>
                  rcases pair with ⟨new_state, resp_acts⟩
                  simp [lc', hrecv] at h
                  have hrecv_raw :
                      wc_receive wc (lc_to_env AddrSize lc').toChain
                        { ctx_origin := origin, ctx_from := frm,
                          ctx_contract_address := to_,
                          ctx_contract_balance := (lc_to_env AddrSize lc').env_account_balances to_,
                          ctx_amount := amount }
                        prev_state msg = .Ok (new_state, resp_acts) := by
                    unfold weak_error_to_error_receive bind_error at hrecv
                    cases hwc :
                        wc_receive wc (lc_to_env AddrSize lc').toChain
                          { ctx_origin := origin, ctx_from := frm,
                            ctx_contract_address := to_,
                            ctx_contract_balance := (lc_to_env AddrSize lc').env_account_balances to_,
                            ctx_amount := amount }
                          prev_state msg with
                    | Ok pair =>
                        cases pair
                        simp [hwc] at hrecv
                        cases hrecv
                        subst_vars
                        rfl
                    | Err err =>
                        simp [hwc] at hrecv
                  rcases h with ⟨hacts, hlc⟩
                  subst new_acts
                  subst lc_after
                  exact .eval_call origin frm to_ amount wc msg prev_state new_state resp_acts
                    (not_lt.mp hneg) (not_lt.mp hbal) hcontract hstate
                    (by cases act; cases msg <;> simp_all)
                    hrecv_raw rfl
                    (environment_equiv_trans _ _ _
                      (set_contract_state_equiv AddrSize to_ new_state lc')
                      (set_contract_state_preserves_equiv AddrSize to_ new_state
                        (lc_to_env AddrSize lc')
                        (@BlockchainBase.transfer_balance (LocalChainBase AddrSize)
                          frm to_ amount (lc_to_env AddrSize lc_before))
                        (transfer_balance_equiv AddrSize frm to_ amount lc_before)))

theorem get_new_contract_addr_is_contract_addr
    (lc : LocalChain AddrSize) (addr : LocalAddress AddrSize) :
    get_new_contract_addr AddrSize lc = some addr →
    (LocalChainBase AddrSize).address_is_contract addr = true := by
  intro h
  unfold get_new_contract_addr at h
  have hval := BoundedN.of_N_some h
  change addr.val = ContractAddrBase AddrSize + lc.lc_contracts.size at hval
  unfold LocalChainBase address_is_contract_local
  exact decide_eq_true (by rw [hval]; omega)

def deploy_contract_step
    (origin frm : LocalAddress AddrSize) (amount : Amount)
    (wc : LCWC AddrSize) (setup : SerializedValue) (act : LCAct AddrSize)
    (lc_before lc_after : LocalChain AddrSize) (new_acts : List (LCAct AddrSize)) :
    @Action.act_origin (LocalChainBase AddrSize) act = origin →
    @Action.act_from (LocalChainBase AddrSize) act = frm →
    @Action.act_body (LocalChainBase AddrSize) act =
      @ActionBody.act_deploy (LocalChainBase AddrSize) amount wc setup →
    deploy_contract AddrSize origin frm amount wc setup lc_before = .Ok (new_acts, lc_after) →
    @ActionEvaluation (LocalChainBase AddrSize)
      (lc_to_env AddrSize lc_before) act (lc_to_env AddrSize lc_after) new_acts := by
  letI : ChainBase := LocalChainBase AddrSize
  intro horigin hfrom hbody
  have hact : act = @Action.mk (LocalChainBase AddrSize) origin frm
      (@ActionBody.act_deploy (LocalChainBase AddrSize) amount wc setup) := by
    cases act
    simp at horigin hfrom hbody
    subst_vars
    rfl
  intro h
  unfold deploy_contract at h
  by_cases hneg : amount < 0
  · simp [hneg] at h
  · simp [hneg] at h
    by_cases hbal : amount > (lc_to_env AddrSize lc_before).env_account_balances frm
    · simp [hbal] at h
    · simp [hbal] at h
      cases haddr : get_new_contract_addr AddrSize lc_before with
      | none =>
          simp [haddr] at h
      | some contract_addr =>
          simp [haddr] at h
          cases hcontract : FMap.find contract_addr lc_before.lc_contracts with
          | some old =>
              simp [hcontract] at h
          | none =>
              simp [hcontract] at h
              let lc' := transfer_balance AddrSize frm contract_addr amount lc_before
              cases hinit :
                  weak_error_to_error_init AddrSize
                    (wc_init wc (lc_to_env AddrSize lc').toChain
                      { ctx_origin := origin, ctx_from := frm,
                        ctx_contract_address := contract_addr,
                        ctx_contract_balance := amount, ctx_amount := amount }
                      setup) with
              | Err e =>
                  simp [lc', hinit] at h
              | Ok state =>
                  simp [lc', hinit] at h
                  have hinit_raw :
                      wc_init wc (lc_to_env AddrSize lc').toChain
                        { ctx_origin := origin, ctx_from := frm,
                          ctx_contract_address := contract_addr,
                          ctx_contract_balance := amount, ctx_amount := amount }
                        setup = .Ok state := by
                    unfold weak_error_to_error_init bind_error at hinit
                    cases hwc :
                        wc_init wc (lc_to_env AddrSize lc').toChain
                          { ctx_origin := origin, ctx_from := frm,
                            ctx_contract_address := contract_addr,
                            ctx_contract_balance := amount, ctx_amount := amount }
                          setup with
                    | Ok st =>
                        simp [hwc] at hinit
                        subst_vars
                        rfl
                    | Err err =>
                        simp [hwc] at hinit
                  rcases h with ⟨hacts, hlc⟩
                  subst new_acts
                  subst lc_after
                  exact .eval_deploy origin frm contract_addr amount wc setup state
                    (not_lt.mp hneg) (not_lt.mp hbal)
                    (get_new_contract_addr_is_contract_addr AddrSize lc_before contract_addr haddr)
                    hcontract hact hinit_raw
                    (environment_equiv_trans _ _ _
                      (environment_equiv_trans _ _ _
                        (set_contract_state_equiv AddrSize contract_addr state
                          (add_contract AddrSize contract_addr wc lc'))
                        (set_contract_state_preserves_equiv AddrSize contract_addr state
                          (lc_to_env AddrSize (add_contract AddrSize contract_addr wc lc'))
                          (@BlockchainBase.add_contract (LocalChainBase AddrSize) contract_addr wc
                            (lc_to_env AddrSize lc'))
                          (add_contract_equiv AddrSize contract_addr wc lc')))
                      (set_contract_state_preserves_equiv AddrSize contract_addr state
                        (@BlockchainBase.add_contract (LocalChainBase AddrSize) contract_addr wc
                          (lc_to_env AddrSize lc'))
                        (@BlockchainBase.add_contract (LocalChainBase AddrSize) contract_addr wc
                          (@BlockchainBase.transfer_balance (LocalChainBase AddrSize)
                            frm contract_addr amount (lc_to_env AddrSize lc_before)))
                        (add_contract_preserves_equiv AddrSize contract_addr wc
                          (lc_to_env AddrSize lc')
                          (@BlockchainBase.transfer_balance (LocalChainBase AddrSize)
                            frm contract_addr amount (lc_to_env AddrSize lc_before))
                          (transfer_balance_equiv AddrSize frm contract_addr amount lc_before))))
                    rfl

def execute_action_step
    (act : LCAct AddrSize) (new_acts : List (LCAct AddrSize))
    (lc_before lc_after : LocalChain AddrSize) :
    execute_action AddrSize act lc_before = .Ok (new_acts, lc_after) →
    @ActionEvaluation (LocalChainBase AddrSize)
      (lc_to_env AddrSize lc_before) act (lc_to_env AddrSize lc_after) new_acts := by
  letI : ChainBase := LocalChainBase AddrSize
  intro h
  cases act with
  | mk origin frm body =>
      cases body with
      | act_transfer to_ amount =>
          exact send_or_call_step AddrSize origin frm to_ amount none
            { act_origin := origin, act_from := frm, act_body := .act_transfer to_ amount }
            lc_before lc_after new_acts rfl rfl rfl h
      | act_deploy amount wc setup =>
          exact deploy_contract_step AddrSize origin frm amount wc setup
            { act_origin := origin, act_from := frm, act_body := .act_deploy amount wc setup }
            lc_before lc_after new_acts rfl rfl rfl h
      | act_call to_ amount msg =>
          exact send_or_call_step AddrSize origin frm to_ amount (some msg)
            { act_origin := origin, act_from := frm, act_body := .act_call to_ amount msg }
            lc_before lc_after new_acts rfl rfl rfl h

/-! ### Chain builder

    The builder pairs a `LocalChain` with a *propositional* trace
    existence-witness from `empty_state`. Coq stores the trace as data
    (proved via tactics, `Defined.`); this port stores `Nonempty` of the trace
    type so that `add_block` stays computable. A concrete trace can be
    extracted from `Nonempty.some` using classical choice. -/

def empty_state_LCB : LCChainSt AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  @empty_state (LocalChainBase AddrSize)

def lc_to_chain_state (lc : LocalChain AddrSize) (acts : List (LCAct AddrSize)) :
    LCChainSt AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  { toEnvironment := lc_to_env AddrSize lc, chain_state_queue := acts }

theorem lc_to_chain_state_initial :
    lc_to_chain_state AddrSize (lc_initial AddrSize) [] = empty_state_LCB AddrSize := by
  letI : ChainBase := LocalChainBase AddrSize
  show
    ({ toEnvironment := lc_to_env AddrSize (lc_initial AddrSize),
       chain_state_queue := [] } : LCChainSt AddrSize) = empty_state
  rfl

abbrev LCTrace (frm to_ : LCChainSt AddrSize) : Type :=
  @ChainTrace (LocalChainBase AddrSize) frm to_

theorem execute_actions_trace
    (count : Nat) (acts : List (LCAct AddrSize))
    (lc lc_final : LocalChain AddrSize) (depth_first : Bool)
    (trace : LCTrace AddrSize (empty_state_LCB AddrSize)
      (lc_to_chain_state AddrSize lc acts)) :
    execute_actions AddrSize count acts lc depth_first = .Ok lc_final →
    Nonempty (LCTrace AddrSize (empty_state_LCB AddrSize)
      (lc_to_chain_state AddrSize lc_final [])) := by
  revert acts lc lc_final depth_first trace
  induction count with
  | zero =>
      intro acts lc lc_final depth_first trace h
      cases acts with
      | nil =>
          simp [execute_actions] at h
          exact ⟨h ▸ trace⟩
      | cons act rest =>
          simp [execute_actions] at h
  | succ count ih =>
      intro acts lc lc_final depth_first trace h
      letI : ChainBase := LocalChainBase AddrSize
      cases acts with
      | nil =>
          simp [execute_actions] at h
          subst lc_final
          exact ⟨trace⟩
      | cons act rest =>
          simp [execute_actions] at h
          cases hexec : execute_action AddrSize act lc with
          | Err e =>
              simp [hexec] at h
          | Ok pair =>
              rcases pair with ⟨new_acts, lc_after⟩
              simp [hexec] at h
              have eval := execute_action_step AddrSize act new_acts lc lc_after hexec
              let step : @ChainStep (LocalChainBase AddrSize)
                  (lc_to_chain_state AddrSize lc (act :: rest))
                  (lc_to_chain_state AddrSize lc_after (new_acts ++ rest)) :=
                .step_action act rest new_acts rfl eval rfl
              by_cases hdf : depth_first = true
              · simp [hdf] at h
                exact ih (new_acts ++ rest) lc_after lc_final true
                  (ChainedList.snoc trace step) h
              · have hdfFalse : depth_first = false := by
                  cases depth_first <;> simp_all
                simp [hdfFalse] at h
                let perm_step : @ChainStep (LocalChainBase AddrSize)
                    (lc_to_chain_state AddrSize lc_after (new_acts ++ rest))
                    (lc_to_chain_state AddrSize lc_after (rest ++ new_acts)) :=
                  .step_permute (environment_equiv_refl _)
                    (List.perm_append_comm :
                      (new_acts ++ rest).Perm (rest ++ new_acts))
                exact ih (rest ++ new_acts) lc_after lc_final false
                  (ChainedList.snoc (ChainedList.snoc trace step) perm_step) h

/-- Executable local-chain state plus a proof-carrying trace witness.

    The witness is `Nonempty` rather than direct trace data because the builder
    is used computationally, while the trace is only consumed propositionally by
    `ChainBuilderType.builder_trace`. Storing the concrete trace would thread
    larger proof terms through the executable builder without changing public
    execution behavior. -/
structure LocalChainBuilder where
  lcb_lc : LocalChain AddrSize
  lcb_trace :
    Nonempty (LCTrace AddrSize (empty_state_LCB AddrSize)
                        (lc_to_chain_state AddrSize lcb_lc []))

def lcb_initial : LocalChainBuilder AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  { lcb_lc := lc_initial AddrSize,
    lcb_trace := ⟨lc_to_chain_state_initial AddrSize ▸ ChainedList.clnil⟩ }

theorem add_block_trace :
  ∀ (depth_first : Bool) (lcb : LocalChainBuilder AddrSize)
    (header : LCBH AddrSize) (actions : List (LCAct AddrSize)) (lc' : LocalChain AddrSize),
    add_block_exec AddrSize depth_first lcb.lcb_lc header actions = .Ok lc' →
    Nonempty (LCTrace AddrSize (empty_state_LCB AddrSize)
                       (lc_to_chain_state AddrSize lc' [])) := by
  intro depth_first lcb header actions lc' h
  letI : ChainBase := LocalChainBase AddrSize
  unfold add_block_exec at h
  by_cases hv : validate_header AddrSize header (lc_to_env AddrSize lcb.lcb_lc).toChain
  · simp [hv] at h
    cases ho : find_origin_neq_from AddrSize actions with
    | some act =>
        simp [ho] at h
    | none =>
        simp [ho] at h
        cases hi : find_invalid_root_action AddrSize actions with
        | some act =>
            simp [hi] at h
        | none =>
            simp [hi] at h
            obtain ⟨prev_trace⟩ := lcb.lcb_trace
            let lc0 := add_new_block AddrSize header lcb.lcb_lc
            have step : @ChainStep (LocalChainBase AddrSize)
                (lc_to_chain_state AddrSize lcb.lcb_lc [])
                (lc_to_chain_state AddrSize lc0 actions) := by
              letI : ChainBase := LocalChainBase AddrSize
              refine .step_block header rfl ?_ ?_ ?_ ?_
              · exact validate_header_valid AddrSize header
                  (lc_to_env AddrSize lcb.lcb_lc).toChain hv
              · exact validate_actions_valid AddrSize actions hi
              · exact validate_origin_neq_from_valid AddrSize actions ho
              · exact add_new_block_equiv AddrSize header lcb.lcb_lc
            exact execute_actions_trace AddrSize 1000 actions lc0 lc' depth_first
              (ChainedList.snoc prev_trace step) h
  · simp [hv] at h

def add_block (depth_first : Bool) (lcb : LocalChainBuilder AddrSize)
    (header : LCBH AddrSize) (actions : List (LCAct AddrSize)) :
    Result (LocalChainBuilder AddrSize) (LCABErr AddrSize) :=
  letI : ChainBase := LocalChainBase AddrSize
  match h : add_block_exec AddrSize depth_first lcb.lcb_lc header actions with
  | .Ok lc' =>
    .Ok { lcb_lc := lc',
          lcb_trace := add_block_trace AddrSize depth_first lcb header actions lc' h }
  | .Err e => .Err e

/-- Concrete `ChainBuilderType` instance. `builder_trace` extracts the witness
    from `Nonempty` via `Classical.choice`. -/
@[reducible] noncomputable def LocalChainBuilderImpl : LCCBT AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  { builder_type    := LocalChainBuilder AddrSize,
    builder_initial := lcb_initial AddrSize,
    builder_env     := fun lcb => lc_to_env AddrSize lcb.lcb_lc,
    builder_add_block := add_block AddrSize DepthFirst,
    builder_trace   := fun b => b.lcb_trace.some }

end ConCert.Execution.Test.LocalBlockchain
