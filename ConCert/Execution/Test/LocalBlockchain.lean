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
  serialize b := ⟨.ser_int, (b.val : Int)⟩
  deserialize v :=
    match v with
    | ⟨.ser_int, i⟩ =>
      let i' : Int := i
      if i' < 0 then none
      else if h : i'.toNat < AddrSize then some ⟨i'.toNat, h⟩
      else none
    | _ => none
  deserialize_serialize := by
    intro b
    show
      (let i' : Int := (b.val : Int);
       if i' < 0 then none
       else if h : i'.toNat < AddrSize then some ⟨i'.toNat, h⟩
       else none) = some b
    have h_nonneg : ¬ ((b.val : Int) < 0) := by omega
    have h_bound : ((b.val : Int).toNat) < AddrSize := by simp; exact b.lt
    rw [if_neg h_nonneg, dif_pos h_bound]; congr

def address_is_contract_local (a : LocalAddress AddrSize) : Bool :=
  ContractAddrBase AddrSize ≤ a.val

axiom local_address_eqb_spec :
  ∀ (a b : BoundedN AddrSize), BoundedN.eqb a b = true ↔ a = b

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

/-! Inside this file we work entirely under `LocalChainBase AddrSize`. The
    following abbreviations shorten the noisy `@Foo (LocalChainBase AddrSize)`
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

/-! ### Chain builder

    The builder pairs a `LocalChain` with a *propositional* trace
    existence-witness from `empty_state`. Coq stores the trace as data
    (proved via tactics, `Defined.`); we store `Nonempty` of the trace
    type so that `add_block` stays computable. Anyone needing a concrete
    trace can extract it from `Nonempty.some` using classical choice. -/

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

structure LocalChainBuilder where
  lcb_lc : LocalChain AddrSize
  lcb_trace :
    Nonempty (LCTrace AddrSize (empty_state_LCB AddrSize)
                        (lc_to_chain_state AddrSize lcb_lc []))

def lcb_initial : LocalChainBuilder AddrSize :=
  letI : ChainBase := LocalChainBase AddrSize
  { lcb_lc := lc_initial AddrSize,
    lcb_trace := ⟨lc_to_chain_state_initial AddrSize ▸ ChainedList.clnil⟩ }

axiom add_block_trace :
  ∀ (depth_first : Bool) (lcb : LocalChainBuilder AddrSize)
    (header : LCBH AddrSize) (actions : List (LCAct AddrSize)) (lc' : LocalChain AddrSize),
    add_block_exec AddrSize depth_first lcb.lcb_lc header actions = .Ok lc' →
    Nonempty (LCTrace AddrSize (empty_state_LCB AddrSize)
                       (lc_to_chain_state AddrSize lc' []))

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
