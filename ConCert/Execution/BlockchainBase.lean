/- Port of execution/theories/BlockchainBase.v -/

import ConCert.Execution.ChainedList
import ConCert.Execution.Containers
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable

namespace ConCert.Execution.BlockchainBase

open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.ChainedList
open ConCert.Execution.Containers

abbrev Amount := Int

/-- Basic assumptions on any blockchain. -/
class ChainBase where
  Address : Type
  address_eqb : Address → Address → Bool
  address_eqb_spec : ∀ (a b : Address), (address_eqb a b = true) ↔ (a = b)
  address_eqdec : DecidableEq Address
  address_ord : Ord Address
  address_ord_lawful : @LawfulOrd Address address_ord
  address_serializable : Serializable Address
  address_is_contract : Address → Bool

attribute [reducible] ChainBase.address_serializable
                      ChainBase.address_eqdec
                      ChainBase.address_ord
attribute [instance] ChainBase.address_serializable
                     ChainBase.address_eqdec
                     ChainBase.address_ord
                     ChainBase.address_ord_lawful

namespace Address

variable [Base : ChainBase]

def address_neqb (x y : Base.Address) : Bool :=
  !(Base.address_eqb x y)

def address_not_contract (x : Base.Address) : Bool :=
  !(Base.address_is_contract x)

theorem address_eq_refl (x : Base.Address) : Base.address_eqb x x = true :=
  (Base.address_eqb_spec x x).mpr rfl

theorem address_eq_ne (x y : Base.Address)
    (h : x ≠ y) : Base.address_eqb x y = false := by
  cases hk : Base.address_eqb x y with
  | true => exact absurd ((Base.address_eqb_spec x y).mp hk) h
  | false => rfl

theorem address_eq_ne' (x y : Base.Address) :
    x ≠ y ↔ Base.address_eqb x y = false := by
  refine ⟨address_eq_ne x y, fun h heq => ?_⟩
  rw [heq, address_eq_refl] at h
  cases h

theorem address_eq_sym (x y : Base.Address) :
    Base.address_eqb x y = Base.address_eqb y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [address_eq_ne x y h, address_eq_ne y x (Ne.symm h)]

theorem address_neqb_eq (x y : Base.Address) :
    address_neqb x y = false ↔ x = y := by
  unfold address_neqb
  rw [show ((!Base.address_eqb x y) = false) ↔ (Base.address_eqb x y = true) by
        cases Base.address_eqb x y <;> simp]
  exact Base.address_eqb_spec x y

theorem address_neq_sym (x y : Base.Address) :
    address_neqb x y = address_neqb y x := by
  unfold address_neqb
  rw [address_eq_sym]

end Address

variable [Base : ChainBase]

/-- The view of the blockchain visible to a contract. -/
structure Chain where
  chain_height     : Nat
  current_slot     : Nat
  finalized_height : Nat

structure ContractCallContext where
  ctx_origin : Base.Address
  ctx_from : Base.Address
  ctx_contract_address : Base.Address
  ctx_contract_balance : Amount
  ctx_amount : Amount

structure ValidChain (chain : Chain) : Prop where
  chain_height_valid     : chain.chain_height ≤ chain.current_slot
  finalized_height_valid : chain.finalized_height < chain.chain_height + 1

structure ValidContext (ctx : @ContractCallContext Base) : Prop where
  ctx_origin_valid           : Base.address_is_contract ctx.ctx_origin = false
  ctx_contract_address_valid : Base.address_is_contract ctx.ctx_contract_address = true
  ctx_contract_balance_valid : 0 ≤ ctx.ctx_contract_balance
  ctx_amount_valid           : 0 ≤ ctx.ctx_amount

-- Operations a contract may return / a user may interact with.
mutual
inductive ActionBody where
  | act_transfer (to_ : Base.Address) (amount : Amount) : ActionBody
  | act_call (to_ : Base.Address) (amount : Amount) (msg : SerializedValue) : ActionBody
  | act_deploy (amount : Amount) (c : WeakContract) (setup : SerializedValue) : ActionBody

inductive WeakContract where
  | build_weak_contract
      (init :
        Chain →
        @ContractCallContext Base →
        SerializedValue →
        Result SerializedValue SerializedValue)
      (receive :
        Chain →
        @ContractCallContext Base →
        SerializedValue →
        Option SerializedValue →
        Result (SerializedValue × List ActionBody) SerializedValue)
      : WeakContract
end

def act_body_amount : @ActionBody Base → Int
  | .act_transfer _ amount   => amount
  | .act_call _ amount _     => amount
  | .act_deploy amount _ _   => amount

def wc_init (wc : @WeakContract Base) :
    Chain → @ContractCallContext Base → SerializedValue →
    Result SerializedValue SerializedValue :=
  match wc with
  | .build_weak_contract i _ => i

def wc_receive (wc : @WeakContract Base) :
    Chain → @ContractCallContext Base → SerializedValue →
    Option SerializedValue → Result (SerializedValue × List (@ActionBody Base)) SerializedValue :=
  match wc with
  | .build_weak_contract _ r => r

structure Action where
  act_origin : Base.Address
  act_from   : Base.Address
  act_body   : @ActionBody Base

def act_amount (a : @Action Base) : Amount := act_body_amount a.act_body

/-- A strongly typed contract. -/
structure Contract
    (Setup Msg State Error : Type)
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error] where
  init :
    Chain →
    @ContractCallContext Base →
    Setup →
    Result State Error
  receive :
    Chain →
    @ContractCallContext Base →
    State →
    Option Msg →
    Result (State × List (@ActionBody Base)) Error

/-- Sentinel returned when (de)serialization of contract inputs fails. -/
def deser_error : SerializedValue := serialize "Deserialization failed"

def error_to_weak_error {T E : Type} [Serializable E]
    (r : Result T E) : Result T SerializedValue :=
  bind_error (fun err => serialize err) r

/-- A strongly typed contract becomes a weak one by serializing its
    inputs/outputs and wrapping errors. A failed deserialization of the
    setup, state, or message produces `Err deser_error` — failed message
    deserialization is *rejected*, not silently converted to `none`. -/
def contract_to_weak_contract
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (c : @Contract Base Setup Msg State Error _ _ _ _) : @WeakContract Base :=
  let init_w : Chain → @ContractCallContext Base → SerializedValue →
                Result SerializedValue SerializedValue :=
    fun chain ctx setup_ser =>
      match deserialize setup_ser with
      | some setup =>
          match c.init chain ctx setup with
          | .Ok state => .Ok (serialize state)
          | .Err err  => .Err (serialize err)
      | none => .Err deser_error
  let receive_w : Chain → @ContractCallContext Base → SerializedValue →
                   Option SerializedValue →
                   Result (SerializedValue × List (@ActionBody Base)) SerializedValue :=
    fun chain ctx state_ser msg_ser =>
      match deserialize state_ser with
      | some state =>
          match msg_ser with
          | some m =>
            match (deserialize m : Option Msg) with
            | some msg =>
              match c.receive chain ctx state (some msg) with
              | .Ok (new_state, acts) => .Ok (serialize new_state, acts)
              | .Err err              => .Err (serialize err)
            | none => .Err deser_error
          | none =>
            match c.receive chain ctx state none with
            | .Ok (new_state, acts) => .Ok (serialize new_state, acts)
            | .Err err              => .Err (serialize err)
      | none => .Err deser_error
  .build_weak_contract init_w receive_w

/-- Deploy a strongly typed contract with some amount and setup. -/
def create_deployment
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (amount : Amount)
    (contract : Contract Setup Msg State Error)
    (setup : Setup) : @ActionBody Base :=
  .act_deploy amount (contract_to_weak_contract contract) (serialize setup)

structure ContractInterface (Msg : Type) where
  contract_address : Base.Address
  send : Amount → Option Msg → @ActionBody Base

def get_contract_interface
    (_chain : Chain) (addr : Base.Address) (Msg : Type) [Serializable Msg] :
    Option (@ContractInterface Base Msg) :=
  let ifc_send (amount : Amount) (msg : Option Msg) : @ActionBody Base :=
    match msg with
    | none     => .act_transfer addr amount
    | some msg => .act_call addr amount (serialize msg)
  some { contract_address := addr, send := ifc_send }

/-! ### Semantics -/

def add_balance
    (addr : Base.Address) (amount : Amount)
    (map : Base.Address → Amount) : Base.Address → Amount :=
  fun a => if Base.address_eqb a addr then amount + map a else map a

def set_chain_contract_state
    (addr : Base.Address) (state : SerializedValue)
    (map : Base.Address → Option SerializedValue) :
    Base.Address → Option SerializedValue :=
  fun a => if Base.address_eqb a addr then some state else map a

structure Environment extends Chain where
  env_account_balances : Base.Address → Amount
  env_contracts        : Base.Address → Option (@WeakContract Base)
  env_contract_states  : Base.Address → Option SerializedValue

def env_chain (e : @Environment Base) : Chain := e.toChain

/-- Two environments are equivalent if they are extensionally equal. -/
structure EnvironmentEquiv (e1 e2 : @Environment Base) : Prop where
  chain_eq : env_chain e1 = env_chain e2
  account_balances_eq :
    ∀ a, e1.env_account_balances a = e2.env_account_balances a
  contracts_eq :
    ∀ a, e1.env_contracts a = e2.env_contracts a
  contract_states_eq :
    ∀ addr, e1.env_contract_states addr = e2.env_contract_states addr

/-- Strongly typed view of contract state. -/
def contract_state
    {A : Type} [Serializable A]
    (env : @Environment Base) (addr : Base.Address) : Option A :=
  env.env_contract_states addr >>= deserialize

theorem environment_equiv_refl (e : @Environment Base) : EnvironmentEquiv e e where
  chain_eq := rfl
  account_balances_eq _ := rfl
  contracts_eq _ := rfl
  contract_states_eq _ := rfl

theorem environment_equiv_symm
    (e1 e2 : @Environment Base) (h : EnvironmentEquiv e1 e2) :
    EnvironmentEquiv e2 e1 where
  chain_eq := h.chain_eq.symm
  account_balances_eq a := (h.account_balances_eq a).symm
  contracts_eq a := (h.contracts_eq a).symm
  contract_states_eq a := (h.contract_states_eq a).symm

theorem environment_equiv_trans
    (e1 e2 e3 : @Environment Base)
    (h12 : EnvironmentEquiv e1 e2) (h23 : EnvironmentEquiv e2 e3) :
    EnvironmentEquiv e1 e3 where
  chain_eq := h12.chain_eq.trans h23.chain_eq
  account_balances_eq a := (h12.account_balances_eq a).trans (h23.account_balances_eq a)
  contracts_eq a := (h12.contracts_eq a).trans (h23.contracts_eq a)
  contract_states_eq a := (h12.contract_states_eq a).trans (h23.contract_states_eq a)

def transfer_balance (frm to_ : Base.Address)
    (amount : Amount) (env : @Environment Base) : @Environment Base :=
  { env with
    env_account_balances :=
      add_balance frm (-amount) (add_balance to_ amount env.env_account_balances) }

def add_contract (addr : Base.Address)
    (contract : @WeakContract Base) (env : @Environment Base) : @Environment Base :=
  { env with
    env_contracts := fun a =>
      if Base.address_eqb a addr then some contract else env.env_contracts a }

def set_contract_state (addr : Base.Address) (state : SerializedValue)
    (env : @Environment Base) : @Environment Base :=
  { env with
    env_contract_states := set_chain_contract_state addr state env.env_contract_states }

/-- How a single action evaluates against the chain. -/
inductive ActionEvaluation :
    (prev_env : @Environment Base) → (act : @Action Base) →
    (new_env : @Environment Base) → (new_acts : List (@Action Base)) → Type
  | eval_transfer :
      ∀ {prev_env new_env : @Environment Base} {act : @Action Base} {new_acts : List (@Action Base)}
        (origin from_addr to_addr : Base.Address)
        (amount : Amount),
        amount ≥ 0 →
        amount ≤ prev_env.env_account_balances from_addr →
        Base.address_is_contract to_addr = false →
        act = { act_origin := origin, act_from := from_addr,
                 act_body := .act_transfer to_addr amount } →
        EnvironmentEquiv new_env (transfer_balance from_addr to_addr amount prev_env) →
        new_acts = [] →
        ActionEvaluation prev_env act new_env new_acts
  | eval_deploy :
      ∀ {prev_env new_env : @Environment Base} {act : @Action Base} {new_acts : List (@Action Base)}
        (origin from_addr to_addr : Base.Address)
        (amount : Amount)
        (wc : @WeakContract Base)
        (setup state : SerializedValue),
        amount ≥ 0 →
        amount ≤ prev_env.env_account_balances from_addr →
        Base.address_is_contract to_addr = true →
        prev_env.env_contracts to_addr = none →
        act = { act_origin := origin, act_from := from_addr,
                 act_body := .act_deploy amount wc setup } →
        wc_init wc
          (transfer_balance from_addr to_addr amount prev_env).toChain
          { ctx_origin := origin, ctx_from := from_addr,
            ctx_contract_address := to_addr,
            ctx_contract_balance := amount, ctx_amount := amount }
          setup = Ok state →
        EnvironmentEquiv new_env
          (set_contract_state to_addr state
            (add_contract to_addr wc
              (transfer_balance from_addr to_addr amount prev_env))) →
        new_acts = [] →
        ActionEvaluation prev_env act new_env new_acts
  | eval_call :
      ∀ {prev_env new_env : @Environment Base} {act : @Action Base} {new_acts : List (@Action Base)}
        (origin from_addr to_addr : Base.Address)
        (amount : Amount)
        (wc : @WeakContract Base)
        (msg : Option SerializedValue)
        (prev_state new_state : SerializedValue)
        (resp_acts : List (@ActionBody Base)),
        amount ≥ 0 →
        amount ≤ prev_env.env_account_balances from_addr →
        prev_env.env_contracts to_addr = some wc →
        prev_env.env_contract_states to_addr = some prev_state →
        act = { act_origin := origin, act_from := from_addr,
                 act_body :=
                   (match msg with
                    | none => .act_transfer to_addr amount
                    | some m => .act_call to_addr amount m) } →
        wc_receive wc
          (transfer_balance from_addr to_addr amount prev_env).toChain
          { ctx_origin := origin, ctx_from := from_addr,
            ctx_contract_address := to_addr,
            ctx_contract_balance := new_env.env_account_balances to_addr,
            ctx_amount := amount }
          prev_state msg = Ok (new_state, resp_acts) →
        new_acts = resp_acts.map (fun b => { act_origin := origin, act_from := to_addr, act_body := b }) →
        EnvironmentEquiv new_env
          (set_contract_state to_addr new_state
            (transfer_balance from_addr to_addr amount prev_env)) →
        ActionEvaluation prev_env act new_env new_acts

namespace ActionEvaluation

def eval_origin {prev_env new_env : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (e : ActionEvaluation prev_env act new_env new_acts) : Base.Address :=
  match e with
  | .eval_transfer o _ _ _ _ _ _ _ _ _ => o
  | .eval_deploy o _ _ _ _ _ _ _ _ _ _ _ _ _ _ => o
  | .eval_call o _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => o

def eval_from {prev_env new_env : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (e : ActionEvaluation prev_env act new_env new_acts) : Base.Address :=
  match e with
  | .eval_transfer _ f _ _ _ _ _ _ _ _ => f
  | .eval_deploy _ f _ _ _ _ _ _ _ _ _ _ _ _ _ => f
  | .eval_call _ f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => f

def eval_to {prev_env new_env : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (e : ActionEvaluation prev_env act new_env new_acts) : Base.Address :=
  match e with
  | .eval_transfer _ _ t _ _ _ _ _ _ _ => t
  | .eval_deploy _ _ t _ _ _ _ _ _ _ _ _ _ _ _ => t
  | .eval_call _ _ t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => t

def eval_amount {prev_env new_env : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (e : ActionEvaluation prev_env act new_env new_acts) : Amount :=
  match e with
  | .eval_transfer _ _ _ a _ _ _ _ _ _ => a
  | .eval_deploy _ _ _ a _ _ _ _ _ _ _ _ _ _ _ => a
  | .eval_call _ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ _ => a

end ActionEvaluation

structure BlockHeader where
  block_height           : Nat
  block_slot             : Nat
  block_finalized_height : Nat
  block_reward           : Amount
  block_creator          : Base.Address

def add_new_block_to_env (header : @BlockHeader Base) (env : @Environment Base) :
    @Environment Base :=
  { env with
    toChain :=
      { chain_height := header.block_height,
        current_slot := header.block_slot,
        finalized_height := header.block_finalized_height },
    env_account_balances :=
      add_balance header.block_creator header.block_reward env.env_account_balances }

def act_is_from_account (act : @Action Base) : Prop :=
  Base.address_is_contract act.act_from = false

def act_origin_is_account (act : @Action Base) : Prop :=
  Base.address_is_contract act.act_origin = false

def act_origin_is_eq_from (act : @Action Base) : Prop :=
  Base.address_eqb act.act_origin act.act_from = true

structure IsValidNextBlock (header : @BlockHeader Base) (chain : Chain) : Prop where
  valid_height : header.block_height = chain.chain_height + 1
  valid_slot   : header.block_slot > chain.current_slot
  valid_finalized_height :
    header.block_finalized_height ≥ chain.finalized_height ∧
    header.block_finalized_height < header.block_height
  valid_creator : Base.address_is_contract header.block_creator = false
  valid_reward  : header.block_reward ≥ 0

structure ChainState extends Environment where
  chain_state_queue : List (@Action Base)

def chain_state_env (cs : @ChainState Base) : @Environment Base := cs.toEnvironment

inductive ChainStep (prev_bstate next_bstate : @ChainState Base) where
  | step_block :
      ∀ (header : @BlockHeader Base),
        prev_bstate.chain_state_queue = [] →
        IsValidNextBlock header (env_chain prev_bstate.toEnvironment) →
        next_bstate.chain_state_queue.Forall act_is_from_account →
        next_bstate.chain_state_queue.Forall act_origin_is_eq_from →
        EnvironmentEquiv next_bstate.toEnvironment
          (add_new_block_to_env header prev_bstate.toEnvironment) →
        ChainStep prev_bstate next_bstate
  | step_action :
      ∀ (act : @Action Base) (acts new_acts : List (@Action Base)),
        prev_bstate.chain_state_queue = act :: acts →
        ActionEvaluation prev_bstate.toEnvironment act next_bstate.toEnvironment new_acts →
        next_bstate.chain_state_queue = new_acts ++ acts →
        ChainStep prev_bstate next_bstate
  | step_action_invalid :
      ∀ (act : @Action Base) (acts : List (@Action Base)),
        EnvironmentEquiv next_bstate.toEnvironment prev_bstate.toEnvironment →
        prev_bstate.chain_state_queue = act :: acts →
        next_bstate.chain_state_queue = acts →
        act_is_from_account act →
        (∀ bstate new_acts,
          ActionEvaluation prev_bstate.toEnvironment act bstate new_acts → False) →
        ChainStep prev_bstate next_bstate
  | step_permute :
        EnvironmentEquiv next_bstate.toEnvironment prev_bstate.toEnvironment →
        List.Perm prev_bstate.chain_state_queue next_bstate.chain_state_queue →
        ChainStep prev_bstate next_bstate

theorem origin_is_account
    (acts : List (@Action Base))
    (hfrom : acts.Forall act_is_from_account)
    (heq : acts.Forall act_origin_is_eq_from) :
    acts.Forall act_origin_is_account := by
  -- Translate Forall ↔ ∀ x ∈ l via direct induction on acts.
  have lift_forall : ∀ {P : @Action Base → Prop} {l : List (@Action Base)},
      l.Forall P → (∀ a, a ∈ l → P a) := by
    intro P l hP a ha
    induction l with
    | nil => cases ha
    | cons hd tl ih =>
      match tl, hP with
      | [], hP =>
        rw [List.mem_singleton] at ha
        subst ha; exact hP
      | hd' :: tl', ⟨hhd, htl⟩ =>
        rw [List.mem_cons] at ha
        cases ha with
        | inl heq => subst heq; exact hhd
        | inr hx => exact ih htl hx
  have build_forall : ∀ {P : @Action Base → Prop} {l : List (@Action Base)},
      (∀ a, a ∈ l → P a) → l.Forall P := by
    intro P l hP
    induction l with
    | nil => exact trivial
    | cons hd tl ih =>
      match tl with
      | [] =>
        show P hd
        exact hP hd List.mem_cons_self
      | hd' :: tl' =>
        refine ⟨hP hd List.mem_cons_self, ?_⟩
        exact ih (fun a ha => hP a (List.mem_cons_of_mem _ ha))
  apply build_forall
  intro a ha
  have hf := lift_forall hfrom a ha
  have he := lift_forall heq a ha
  unfold act_origin_is_account
  unfold act_is_from_account at hf
  unfold act_origin_is_eq_from at he
  have horiginEq : a.act_origin = a.act_from :=
    (Base.address_eqb_spec _ _).mp he
  rw [horiginEq]; exact hf

/-! ### Reachability -/

def empty_state : @ChainState Base :=
  { toChain :=
      { chain_height := 0, current_slot := 0, finalized_height := 0 },
    env_account_balances := fun _ => 0,
    env_contract_states  := fun _ => none,
    env_contracts        := fun _ => none,
    chain_state_queue    := [] }

abbrev ChainTrace := ChainedList (@ChainStep Base)

def reachable (to_ : @ChainState Base) : Prop :=
  Nonempty (ChainTrace empty_state to_)

def reachable_through (mid to_ : @ChainState Base) : Prop :=
  reachable mid ∧ Nonempty (ChainTrace mid to_)

def outgoing_acts (state : @ChainState Base) (addr : Base.Address) :
    List (@ActionBody Base) :=
  (state.chain_state_queue.filter
    (fun act => Base.address_eqb act.act_from addr)).map (·.act_body)

/-! ### Transactions -/

inductive TxBody where
  | tx_empty : TxBody
  | tx_deploy (wc : @WeakContract Base) (setup : SerializedValue) : TxBody
  | tx_call (msg : Option SerializedValue) : TxBody

structure Tx where
  tx_origin : Base.Address
  tx_from   : Base.Address
  tx_to     : Base.Address
  tx_amount : Amount
  tx_body   : @TxBody Base

/-- Extract the `Tx` summary from a single action evaluation. -/
def eval_tx {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (eval : ActionEvaluation pre act post new_acts) : @Tx Base :=
  match eval with
  | .eval_transfer origin frm to_ amount _ _ _ _ _ _ =>
      { tx_origin := origin, tx_from := frm, tx_to := to_,
        tx_amount := amount, tx_body := .tx_empty }
  | .eval_deploy origin frm to_ amount wc setup _ _ _ _ _ _ _ _ _ =>
      { tx_origin := origin, tx_from := frm, tx_to := to_,
        tx_amount := amount, tx_body := .tx_deploy wc setup }
  | .eval_call origin frm to_ amount _ msg _ _ _ _ _ _ _ _ _ _ _ =>
      { tx_origin := origin, tx_from := frm, tx_to := to_,
        tx_amount := amount, tx_body := .tx_call msg }

/-- Per-step transaction extractor. -/
def step_txs {prev next : @ChainState Base} (step : ChainStep prev next) :
    List (@Tx Base) :=
  match step with
  | .step_action _ _ _ _ eval _ => [eval_tx eval]
  | _ => []

/-- Flatten a trace into all its transactions, newest first. -/
def trace_txs : ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → List (@Tx Base)
  | _, _, .clnil      => []
  | _, _, .snoc xs step => step_txs step ++ trace_txs xs

def incoming_txs {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (addr : Base.Address) : List (@Tx Base) :=
  (trace_txs trace).filter (fun tx => Base.address_eqb tx.tx_to addr)

def outgoing_txs {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (addr : Base.Address) : List (@Tx Base) :=
  (trace_txs trace).filter (fun tx => Base.address_eqb tx.tx_from addr)

structure ContractCallInfo (Msg : Type) where
  call_origin : Base.Address
  call_from   : Base.Address
  call_amount : Amount
  call_msg    : Option Msg

/-- Extract calls to `addr` recorded in a single chain step. Returns
    `Option (List _)` because deserialization of the message may fail. -/
def step_incoming_calls (Msg : Type) [Serializable Msg]
    {prev next : @ChainState Base} (step : ChainStep prev next) (addr : Base.Address) :
    Option (List (@ContractCallInfo Base Msg)) :=
  match step with
  | .step_action _ _ _ _ eval _ =>
    let tx := eval_tx eval
    if Base.address_eqb tx.tx_to addr then
      match tx.tx_body with
      | .tx_call (some ser_msg) =>
        match (deserialize ser_msg : Option Msg) with
        | some m => some [{ call_origin := tx.tx_origin, call_from := tx.tx_from,
                            call_amount := tx.tx_amount, call_msg := some m }]
        | none   => none
      | .tx_call none =>
        some [{ call_origin := tx.tx_origin, call_from := tx.tx_from,
                call_amount := tx.tx_amount, call_msg := none }]
      | _ => some []
    else some []
  | _ => some []

/-- Newest first. -/
def incoming_calls (Msg : Type) [Serializable Msg]
    {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (addr : Base.Address) :
    Option (List (@ContractCallInfo Base Msg)) :=
  match trace with
  | .clnil      => some []
  | .snoc xs s  =>
    match step_incoming_calls Msg s addr, incoming_calls Msg xs addr with
    | some now, some prior => some (now ++ prior)
    | _, _ => none

structure DeploymentInfo (Setup : Type) where
  deployment_origin : Base.Address
  deployment_from   : Base.Address
  deployment_amount : Amount
  deployment_setup  : Setup

/-- A single step's contribution to deployment info for `addr`. -/
def step_deployment_info (Setup : Type) [Serializable Setup]
    {prev next : @ChainState Base} (step : ChainStep prev next) (addr : Base.Address) :
    Option (@DeploymentInfo Base Setup) :=
  match step with
  | .step_action _ _ _ _ eval _ =>
    let tx := eval_tx eval
    if Base.address_eqb tx.tx_to addr then
      match tx.tx_body with
      | .tx_deploy _ ser_setup =>
        (deserialize ser_setup : Option Setup).map (fun s =>
          { deployment_origin := tx.tx_origin, deployment_from := tx.tx_from,
            deployment_amount := tx.tx_amount, deployment_setup := s })
      | _ => none
    else none
  | _ => none

/-- The deployment info for `addr`, if any. Picks the *latest* deployment
    in the trace. -/
def deployment_info (Setup : Type) [Serializable Setup]
    {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (addr : Base.Address) :
    Option (@DeploymentInfo Base Setup) :=
  match trace with
  | .clnil      => none
  | .snoc xs s  =>
    match step_deployment_info Setup s addr with
    | some d => some d
    | none   => deployment_info Setup xs addr

def step_blocks {prev next : @ChainState Base} (step : ChainStep prev next) :
    List (@BlockHeader Base) :=
  match step with
  | .step_block hdr _ _ _ _ _ => [hdr]
  | _ => []

/-- Newest first. -/
def trace_blocks : ∀ {frm to_ : @ChainState Base},
    ChainTrace frm to_ → List (@BlockHeader Base)
  | _, _, .clnil      => []
  | _, _, .snoc xs step => step_blocks step ++ trace_blocks xs

def created_blocks {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (creator : Base.Address) : List (@BlockHeader Base) :=
  (trace_blocks trace).filter
    (fun b => Base.address_eqb b.block_creator creator)

def is_deploy : @ActionBody Base → Bool
  | .act_deploy _ _ _ => true
  | _ => false

def is_call : @ActionBody Base → Bool
  | .act_call _ _ _ => true
  | _ => false

def is_transfer : @ActionBody Base → Bool
  | .act_transfer _ _ => true
  | _ => false

syntax "destruct_address_eq" : tactic
syntax "destruct_chain_step" : tactic
syntax "destruct_action_eval" : tactic
syntax "rewrite_environment_equiv" : tactic
syntax "solve_proper" : tactic

macro_rules
  | `(tactic| destruct_address_eq) =>
      `(tactic| first | split <;> simp_all | simp_all)
  | `(tactic| destruct_chain_step) =>
      `(tactic| casesm* ChainStep _ _ <;> simp_all)
  | `(tactic| destruct_action_eval) =>
      `(tactic| casesm* ActionEvaluation _ _ _ _ <;> simp_all)
  | `(tactic| rewrite_environment_equiv) =>
      `(tactic| simp_all [EnvironmentEquiv])
  | `(tactic| solve_proper) =>
      `(tactic| first | rfl | simp_all)

end ConCert.Execution.BlockchainBase
