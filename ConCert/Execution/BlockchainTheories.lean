/- Port of execution/theories/BlockchainTheories.v. -/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ConCert.Execution.ChainedList
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.BlockchainBase

namespace ConCert.Execution.BlockchainTheories

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.ChainedList

variable [Base : ChainBase]

/-! ### Action evaluation facts -/

/-- Computing a balance through `transfer_balance`. -/
private theorem balance_after_transfer
    (from_ to_ : Base.Address) (amount : Amount)
    (env : @Environment Base) (addr : Base.Address) :
    (transfer_balance from_ to_ amount env).env_account_balances addr =
      env.env_account_balances addr
      + (if Base.address_eqb addr to_ then amount else 0)
      - (if Base.address_eqb addr from_ then amount else 0) := by
  show add_balance from_ (-amount) (add_balance to_ amount env.env_account_balances) addr = _
  unfold add_balance
  set b : Int := env.env_account_balances addr with hb
  by_cases hf : Base.address_eqb addr from_ = true
  · by_cases ht : Base.address_eqb addr to_ = true
    · simp only [if_pos hf, if_pos ht]; ring
    · simp only [if_pos hf, if_neg ht]; ring
  · by_cases ht : Base.address_eqb addr to_ = true
    · simp only [if_neg hf, if_pos ht]; ring
    · simp only [if_neg hf, if_neg ht]; ring

/-- The `set_contract_state` and `add_contract` wrappers preserve balances. -/
private theorem balance_set_contract_state
    (cs_addr : Base.Address) (state : SerializedValue) (env : @Environment Base)
    (addr : Base.Address) :
    (set_contract_state cs_addr state env).env_account_balances addr =
      env.env_account_balances addr := rfl

private theorem balance_add_contract
    (ca_addr : Base.Address) (wc : @WeakContract Base) (env : @Environment Base)
    (addr : Base.Address) :
    (add_contract ca_addr wc env).env_account_balances addr =
      env.env_account_balances addr := rfl

theorem account_balance_post
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (addr : Base.Address) :
    post.env_account_balances addr =
      pre.env_account_balances addr
      + (if Base.address_eqb addr (ActionEvaluation.eval_to eval)
         then ActionEvaluation.eval_amount eval else 0)
      - (if Base.address_eqb addr (ActionEvaluation.eval_from eval)
         then ActionEvaluation.eval_amount eval else 0) := by
  cases eval with
  | eval_transfer _ from_ to_ amount _ _ _ _ henv _ =>
    show post.env_account_balances addr = _
    rw [henv.account_balances_eq addr, balance_after_transfer]
    rfl
  | eval_deploy _ from_ to_ amount wc _ state _ _ _ _ _ _ henv _ =>
    show post.env_account_balances addr = _
    rw [henv.account_balances_eq addr, balance_set_contract_state,
        balance_add_contract, balance_after_transfer]
    rfl
  | eval_call _ from_ to_ amount _ _ _ new_state _ _ _ _ _ _ _ _ henv =>
    show post.env_account_balances addr = _
    rw [henv.account_balances_eq addr, balance_set_contract_state,
        balance_after_transfer]
    rfl

theorem account_balance_post_to
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (h : ActionEvaluation.eval_from eval ≠ ActionEvaluation.eval_to eval) :
    post.env_account_balances (ActionEvaluation.eval_to eval) =
      pre.env_account_balances (ActionEvaluation.eval_to eval) +
        ActionEvaluation.eval_amount eval := by
  rw [account_balance_post eval (ActionEvaluation.eval_to eval)]
  have h_to : Base.address_eqb (ActionEvaluation.eval_to eval) (ActionEvaluation.eval_to eval) = true :=
    Address.address_eq_refl _
  have h_from : Base.address_eqb (ActionEvaluation.eval_to eval) (ActionEvaluation.eval_from eval) = false :=
    Address.address_eq_ne _ _ (Ne.symm h)
  rw [h_to, h_from]; simp

theorem account_balance_post_from
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (h : ActionEvaluation.eval_from eval ≠ ActionEvaluation.eval_to eval) :
    post.env_account_balances (ActionEvaluation.eval_from eval) =
      pre.env_account_balances (ActionEvaluation.eval_from eval) -
        ActionEvaluation.eval_amount eval := by
  rw [account_balance_post eval (ActionEvaluation.eval_from eval)]
  have h_from : Base.address_eqb (ActionEvaluation.eval_from eval) (ActionEvaluation.eval_from eval) = true :=
    Address.address_eq_refl _
  have h_to : Base.address_eqb (ActionEvaluation.eval_from eval) (ActionEvaluation.eval_to eval) = false :=
    Address.address_eq_ne _ _ h
  rw [h_to, h_from]; simp

theorem account_balance_post_irrelevant
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (addr : Base.Address)
    (h_from : addr ≠ ActionEvaluation.eval_from eval)
    (h_to : addr ≠ ActionEvaluation.eval_to eval) :
    post.env_account_balances addr = pre.env_account_balances addr := by
  rw [account_balance_post eval addr]
  rw [Address.address_eq_ne _ _ h_from, Address.address_eq_ne _ _ h_to]
  simp

private theorem chain_eq_set_contract_state
    (cs_addr : Base.Address) (state : SerializedValue) (env : @Environment Base) :
    env_chain (set_contract_state cs_addr state env) = env_chain env := rfl

private theorem chain_eq_add_contract
    (ca_addr : Base.Address) (wc : @WeakContract Base) (env : @Environment Base) :
    env_chain (add_contract ca_addr wc env) = env_chain env := rfl

private theorem chain_eq_transfer_balance
    (from_ to_ : Base.Address) (amount : Amount) (env : @Environment Base) :
    env_chain (transfer_balance from_ to_ amount env) = env_chain env := rfl

theorem chain_height_post_action
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts) :
    (env_chain post).chain_height = (env_chain pre).chain_height := by
  cases eval with
  | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]
  | eval_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ henv _ =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]
  | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]

theorem current_slot_post_action
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts) :
    (env_chain post).current_slot = (env_chain pre).current_slot := by
  cases eval with
  | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]
  | eval_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ henv _ =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]
  | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]

theorem finalized_height_post_action
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts) :
    (env_chain post).finalized_height = (env_chain pre).finalized_height := by
  cases eval with
  | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]
  | eval_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ henv _ =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]
  | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
    rw [show env_chain post = env_chain pre from henv.chain_eq]

theorem contracts_post_pre_none
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (contract : Base.Address)
    (h : post.env_contracts contract = none) : pre.env_contracts contract = none := by
  cases eval with
  | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
    rw [henv.contracts_eq contract] at h
    -- (transfer_balance ...).env_contracts = pre.env_contracts
    exact h
  | eval_deploy _ from_ to_ _ wc _ state _ _ _ _ _ _ henv _ =>
    rw [henv.contracts_eq contract] at h
    -- (set_contract_state _ _ (add_contract to wc (transfer ...))).env_contracts contract = none
    -- set_contract_state doesn't touch env_contracts; add_contract sets it at to_
    show pre.env_contracts contract = none
    simp [set_contract_state, add_contract] at h
    by_cases haddr : Base.address_eqb contract to_ = true
    · rw [if_pos haddr] at h; cases h
    · rw [if_neg haddr] at h
      exact h
  | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
    rw [henv.contracts_eq contract] at h
    exact h

theorem eval_amount_nonnegative
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts) :
    ActionEvaluation.eval_amount eval ≥ 0 := by
  cases eval with
  | eval_transfer _ _ _ _ h _ _ _ _ _ => exact h
  | eval_deploy _ _ _ _ _ _ _ h _ _ _ _ _ _ _ => exact h
  | eval_call _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ => exact h

theorem eval_amount_le_account_balance
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts) :
    ActionEvaluation.eval_amount eval ≤
      pre.env_account_balances (ActionEvaluation.eval_from eval) := by
  cases eval with
  | eval_transfer _ _ _ _ _ h _ _ _ _ => exact h
  | eval_deploy _ _ _ _ _ _ _ _ h _ _ _ _ _ _ => exact h
  | eval_call _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ => exact h

/-! ### Init / receive facts -/

theorem wc_init_strong
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : SerializedValue} {res : SerializedValue}
    (h : wc_init (contract_to_weak_contract contract) chain ctx setup = Ok res) :
    ∃ setup_strong result_strong,
      deserialize setup = some setup_strong ∧
      serialize result_strong = res ∧
      contract.init chain ctx setup_strong = Ok result_strong := by
  simp only [contract_to_weak_contract, wc_init] at h
  -- destruct deserialize without substituting in the goal
  cases hd_eq : (deserialize setup : Option Setup) with
  | none =>
    rw [hd_eq] at h
    cases h
  | some s =>
    rw [hd_eq] at h
    simp only at h
    cases hi : contract.init chain ctx s with
    | Err _ =>
      rw [hi] at h
      simp only at h
      cases h
    | Ok st =>
      rw [hi] at h
      simp only at h
      cases h
      exact ⟨s, st, rfl, rfl, hi⟩

theorem wc_receive_strong
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state : SerializedValue} {msg : Option SerializedValue}
    {new_state : SerializedValue} {new_acts : List (@ActionBody Base)}
    (h : wc_receive (contract_to_weak_contract contract) chain ctx prev_state msg =
          Ok (new_state, new_acts)) :
    ∃ prev_state_strong msg_strong new_state_strong,
      deserialize prev_state = some prev_state_strong ∧
      (match msg_strong with
       | some m => (msg >>= deserialize) = some m
       | none => msg = none) ∧
      serialize new_state_strong = new_state ∧
      contract.receive chain ctx prev_state_strong msg_strong =
        Ok (new_state_strong, new_acts) := by
  simp only [contract_to_weak_contract, wc_receive] at h
  cases hps : (deserialize prev_state : Option State) with
  | none => rw [hps] at h; cases h
  | some ps =>
    rw [hps] at h; simp only at h
    cases hmsg : msg with
    | none =>
      rw [hmsg] at h; simp only at h
      cases hr : contract.receive chain ctx ps none with
      | Err _ => rw [hr] at h; simp only at h; cases h
      | Ok st =>
        rw [hr] at h; simp only at h
        obtain ⟨ns, na⟩ := st
        cases h
        exact ⟨ps, none, ns, rfl, rfl, rfl, hr⟩
    | some m =>
      rw [hmsg] at h; simp only at h
      cases hmd : (deserialize m : Option Msg) with
      | none => rw [hmd] at h; simp only at h; cases h
      | some msg_s =>
        rw [hmd] at h; simp only at h
        cases hr : contract.receive chain ctx ps (some msg_s) with
        | Err _ => rw [hr] at h; simp only at h; cases h
        | Ok st =>
          rw [hr] at h; simp only at h
          obtain ⟨ns, na⟩ := st
          cases h
          refine ⟨ps, some msg_s, ns, rfl, ?_, rfl, hr⟩
          show (some m >>= deserialize : Option Msg) = some msg_s
          simp [hmd]

theorem wc_init_to_init
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (chain : Chain) (cctx : @ContractCallContext Base) (setup : Setup) (state : State) :
    contract.init chain cctx setup = Ok state ↔
    wc_init (contract_to_weak_contract contract) chain cctx (serialize setup) =
      Ok (serialize state) := by
  constructor
  · intro hi
    simp only [contract_to_weak_contract, wc_init]
    simp only [Serializable.deserialize_serialize, hi]
  · intro hwc
    obtain ⟨setup_s, state_s, hds, hss, hi⟩ := wc_init_strong hwc
    rw [Serializable.deserialize_serialize] at hds
    cases hds
    have : state_s = state := serialize_injective _ _ hss
    rw [this] at hi
    exact hi

theorem wc_receive_to_receive
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (chain : Chain) (cctx : @ContractCallContext Base) (cstate : State) (msg : Msg)
    (new_cstate : State) (new_acts : List (@ActionBody Base)) :
    contract.receive chain cctx cstate (some msg) = Ok (new_cstate, new_acts) ↔
    wc_receive (contract_to_weak_contract contract) chain cctx
      (serialize cstate) (some (serialize msg)) =
      Ok (serialize new_cstate, new_acts) := by
  constructor
  · intro hr
    simp only [contract_to_weak_contract, wc_receive]
    simp only [Serializable.deserialize_serialize, hr]
  · intro hwc
    obtain ⟨ps, ms, ns, hps, hms, hns, hr⟩ := wc_receive_strong hwc
    rw [Serializable.deserialize_serialize] at hps
    cases hps
    cases ms with
    | none => cases hms
    | some m_s =>
      show contract.receive chain cctx cstate (some msg) = Ok (new_cstate, new_acts)
      have hmd : (deserialize (serialize msg) : Option Msg) = some m_s := by
        have : ((some (serialize msg)) >>= (deserialize : SerializedValue → Option Msg)) = some m_s := hms
        simpa using this
      rw [Serializable.deserialize_serialize] at hmd
      cases hmd
      have : ns = new_cstate := serialize_injective _ _ hns
      rw [this] at hr
      exact hr

/-! ### Reachability facts -/

theorem trace_reachable {to_ : @ChainState Base}
    (t : ChainTrace empty_state to_) : reachable to_ := ⟨t⟩

theorem reachable_empty_state : reachable (@empty_state Base) :=
  ⟨ChainedList.clnil⟩

theorem reachable_trans {frm to_ : @ChainState Base}
    (h1 : reachable frm) (h2 : Nonempty (ChainTrace frm to_)) : reachable to_ := by
  obtain ⟨t1⟩ := h1
  obtain ⟨t2⟩ := h2
  exact ⟨clist_app t1 t2⟩

theorem reachable_step {frm to_ : @ChainState Base}
    (h : reachable frm) (step : ChainStep frm to_) : reachable to_ := by
  obtain ⟨t⟩ := h
  exact ⟨ChainedList.snoc t step⟩

theorem reachable_through_refl
    (bstate : @ChainState Base) (h : reachable bstate) :
    reachable_through bstate bstate :=
  ⟨h, ⟨ChainedList.clnil⟩⟩

theorem reachable_through_trans'
    (frm mid to_ : @ChainState Base)
    (h : reachable_through frm mid) (step : ChainStep mid to_) :
    reachable_through frm to_ := by
  obtain ⟨hr, ⟨t⟩⟩ := h
  exact ⟨hr, ⟨ChainedList.snoc t step⟩⟩

theorem reachable_through_trans
    (frm mid to_ : @ChainState Base)
    (h1 : reachable_through frm mid) (h2 : reachable_through mid to_) :
    reachable_through frm to_ := by
  obtain ⟨hr, ⟨t1⟩⟩ := h1
  obtain ⟨_, ⟨t2⟩⟩ := h2
  exact ⟨hr, ⟨clist_app t1 t2⟩⟩

theorem reachable_through_step
    (frm to_ : @ChainState Base)
    (h : reachable frm) (step : ChainStep frm to_) :
    reachable_through frm to_ :=
  ⟨h, ⟨ChainedList.snoc ChainedList.clnil step⟩⟩

theorem reachable_through_reachable
    (frm to_ : @ChainState Base) (h : reachable_through frm to_) :
    reachable to_ := reachable_trans h.1 h.2

/-- Chains a "future state from `mid`" existential through to a future
    from `frm`. -/
theorem step_reachable_through_exists
    (frm mid : @ChainState Base) (P : @ChainState Base → Prop)
    (hrt : reachable_through frm mid)
    (hex : ∃ to_, reachable_through mid to_ ∧ P to_) :
    ∃ to_, reachable_through frm to_ ∧ P to_ := by
  obtain ⟨to_, htm, hp⟩ := hex
  exact ⟨to_, reachable_through_trans frm mid to_ hrt htm, hp⟩

/-! ### Trace facts (selected) -/

theorem contract_addr_format
    {to_ : @ChainState Base} (addr : Base.Address) (wc : @WeakContract Base)
    (hr : reachable to_) (hc : to_.env_contracts addr = some wc) :
    Base.address_is_contract addr = true := by
  obtain ⟨t⟩ := hr
  induction t with
  | clnil =>
    -- empty_state.env_contracts addr = none
    show Base.address_is_contract addr = true
    have : (empty_state : @ChainState Base).env_contracts addr = none := rfl
    rw [this] at hc
    cases hc
  | snoc tail s ih =>
    cases s with
    | step_block _ _ _ _ _ henv =>
      rw [henv.contracts_eq addr] at hc
      exact ih hc
    | step_action _ _ _ _ eval _ =>
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
        rw [henv.contracts_eq addr] at hc
        exact ih hc
      | eval_deploy _ _ to_addr _ _ _ _ _ _ hcontract _ _ _ henv _ =>
        rw [henv.contracts_eq addr] at hc
        show Base.address_is_contract addr = true
        simp [set_contract_state, add_contract] at hc
        by_cases haddr : Base.address_eqb addr to_addr = true
        · have heq := (Base.address_eqb_spec _ _).mp haddr
          rw [heq]; exact hcontract
        · rw [if_neg haddr] at hc
          exact ih hc
      | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
        rw [henv.contracts_eq addr] at hc
        exact ih hc
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [henv.contracts_eq addr] at hc
      exact ih hc
    | step_permute henv _ =>
      rw [henv.contracts_eq addr] at hc
      exact ih hc

/-- If `new_acts` is the result of mapping `resp_acts` to actions from
    `addr2`, and `addr1 ≠ addr2`, then no element of `new_acts` is from
    `addr1`. -/
theorem new_acts_no_out_queue
    (orig addr1 addr2 : Base.Address)
    (new_acts : List (@Action Base)) (resp_acts : List (@ActionBody Base))
    (hne : addr1 ≠ addr2)
    (hmap : new_acts = resp_acts.map
      (fun b => { act_origin := orig, act_from := addr2, act_body := b })) :
    new_acts.Forall (fun a => Base.address_eqb a.act_from addr1 = false) := by
  subst hmap
  have hcons : Base.address_eqb addr2 addr1 = false :=
    Address.address_eq_ne addr2 addr1 (Ne.symm hne)
  -- Map every body to an action with act_from = addr2, all satisfy predicate.
  induction resp_acts with
  | nil => exact trivial
  | cons hd tl ih =>
    match tl with
    | [] =>
      show Base.address_eqb addr2 addr1 = false
      exact hcons
    | _ :: _ =>
      refine ⟨hcons, ?_⟩
      exact ih

theorem undeployed_contract_no_out_queue
    (contract : Base.Address) (state : @ChainState Base)
    (hr : reachable state)
    (hc : Base.address_is_contract contract = true)
    (hno : state.env_contracts contract = none) :
    state.chain_state_queue.Forall
      (fun a => Base.address_eqb a.act_from contract = false) := by
  obtain ⟨t⟩ := hr
  -- Generalise over `hno` so IH can be reused at the pre-state.
  induction t with
  | clnil =>
    show ([] : List _).Forall _
    trivial
  | @snoc mid _ tail s ih =>
    cases s with
    | step_block hdr _ _ hfrom _ henv =>
      have hpre : mid.env_contracts contract = none := by
        rw [henv.contracts_eq contract] at hno; exact hno
      have _ : mid.chain_state_queue.Forall _ := ih hpre
      have lift : ∀ {l : List (@Action Base)},
          l.Forall act_is_from_account →
          l.Forall (fun a => Base.address_eqb a.act_from contract = false) := by
        intro l hF
        induction l with
        | nil => trivial
        | cons hd tl ih2 =>
          match tl, hF with
          | [], h =>
            show Base.address_eqb hd.act_from contract = false
            have : Base.address_is_contract hd.act_from = false := h
            apply Address.address_eq_ne
            intro heq; rw [heq, hc] at this; cases this
          | _ :: _, ⟨hhd, htl⟩ =>
            refine ⟨?_, ih2 htl⟩
            have : Base.address_is_contract hd.act_from = false := hhd
            apply Address.address_eq_ne
            intro heq; rw [heq, hc] at this; cases this
      exact lift hfrom
    | step_action act acts new_acts hqprev eval hqnext =>
      have hpre : mid.env_contracts contract = none :=
        contracts_post_pre_none eval contract hno
      have ihspec := ih hpre
      rw [hqprev] at ihspec
      have hacts_pred : acts.Forall (fun a => Base.address_eqb a.act_from contract = false) := by
        match acts, ihspec with
        | [], _ => trivial
        | _ :: _, ⟨_, htl⟩ => exact htl
      rw [hqnext]
      rw [← ConCert.Utils.Extras.Forall_app]
      refine ⟨?_, hacts_pred⟩
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ _ hne =>
        rw [hne]; trivial
      | eval_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne =>
        rw [hne]; trivial
      | eval_call _ _ to_addr _ _ _ _ _ resp_acts _ _ hcontract _ _ _ hnew _ =>
        have hne : to_addr ≠ contract := by
          intro heq; rw [heq] at hcontract; rw [hcontract] at hpre; cases hpre
        exact new_acts_no_out_queue _ contract to_addr _ _ hne.symm hnew
    | step_action_invalid act acts henv hqprev hqnext _ _ =>
      have hpre : mid.env_contracts contract = none := by
        rw [henv.contracts_eq contract] at hno; exact hno
      have ihspec := ih hpre
      rw [hqprev] at ihspec
      rw [hqnext]
      match acts, ihspec with
      | [], _ => trivial
      | _ :: _, ⟨_, htl⟩ => exact htl
    | step_permute henv hperm =>
      have hpre : mid.env_contracts contract = none := by
        rw [henv.contracts_eq contract] at hno; exact hno
      have ihspec := ih hpre
      exact ConCert.Utils.Extras.forall_respects_permutation _ _ _ hperm ihspec

theorem undeployed_contract_no_out_txs :
  ∀ (contract : Base.Address) {to_ : @ChainState Base} (trace : ChainTrace empty_state to_),
    Base.address_is_contract contract = true →
    to_.env_contracts contract = none →
    outgoing_txs trace contract = [] := by
  intro contract to_ trace his_contract hnone
  induction trace with
  | clnil =>
      simp [outgoing_txs, trace_txs]
  | @snoc mid _ tail step ih =>
      cases step with
      | step_block _ _ _ _ _ henv =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simpa [outgoing_txs, trace_txs, step_txs] using ih hpre
      | step_action act acts new_acts hqueue eval hqueue' =>
          have hpre : mid.env_contracts contract = none :=
            contracts_post_pre_none eval contract hnone
          have hqueue_no_out :=
            undeployed_contract_no_out_queue contract mid ⟨tail⟩ his_contract hpre
          rw [hqueue] at hqueue_no_out
          have hhead : Base.address_eqb act.act_from contract = false := by
            rw [← ConCert.Utils.Extras.All_Forall] at hqueue_no_out
            exact hqueue_no_out.1
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              rw [hact] at hhead
              simpa [outgoing_txs, trace_txs, step_txs, eval_tx, hhead] using
                ih hpre
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew =>
              rw [hact] at hhead
              simpa [outgoing_txs, trace_txs, step_txs, eval_tx, hhead] using
                ih hpre
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              rw [hact] at hhead
              simpa [outgoing_txs, trace_txs, step_txs, eval_tx, hhead] using
                ih hpre
      | step_action_invalid _ _ henv _ _ _ _ =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simpa [outgoing_txs, trace_txs, step_txs] using ih hpre
      | step_permute henv _ =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simpa [outgoing_txs, trace_txs, step_txs] using ih hpre

theorem undeployed_contract_no_in_txs :
  ∀ (contract : Base.Address) {to_ : @ChainState Base} (trace : ChainTrace empty_state to_),
    Base.address_is_contract contract = true →
    to_.env_contracts contract = none →
    incoming_txs trace contract = [] := by
  intro contract to_ trace his_contract hnone
  induction trace with
  | clnil =>
      simp [incoming_txs, trace_txs]
  | @snoc mid _ tail step ih =>
      cases step with
      | step_block _ _ _ _ _ henv =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simpa [incoming_txs, trace_txs, step_txs] using ih hpre
      | step_action act acts new_acts hqueue eval hqueue' =>
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              have hpre : mid.env_contracts contract = none := by
                rw [henv.contracts_eq contract] at hnone
                exact hnone
              have hto : Base.address_eqb to_addr contract = false := by
                apply Address.address_eq_ne
                intro heq
                rw [heq, his_contract] at hnot_contract
                cases hnot_contract
              simpa [incoming_txs, trace_txs, step_txs, eval_tx, hto] using
                ih hpre
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew =>
              rw [henv.contracts_eq contract] at hnone
              by_cases hneq : Base.address_eqb to_addr contract = false
              · have hneq_sym : Base.address_eqb contract to_addr = false := by
                  rw [Address.address_eq_sym]
                  exact hneq
                have hpre : mid.env_contracts contract = none := by
                  simpa [set_contract_state, add_contract, hneq_sym] using hnone
                simpa [incoming_txs, trace_txs, step_txs, eval_tx, hneq] using
                  ih hpre
              · have heq_true : Base.address_eqb to_addr contract = true := by
                  cases h : Base.address_eqb to_addr contract
                  · exact False.elim (hneq h)
                  · rfl
                have hcontract_eq : contract = to_addr :=
                  ((Base.address_eqb_spec _ _).mp heq_true).symm
                subst hcontract_eq
                simp [set_contract_state, add_contract, Address.address_eq_refl] at hnone
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              rw [henv.contracts_eq contract] at hnone
              by_cases heq : to_addr = contract
              · subst heq
                simp [set_contract_state, transfer_balance, hcontract] at hnone
              · have hneq : Base.address_eqb to_addr contract = false :=
                  Address.address_eq_ne _ _ heq
                have hpre : mid.env_contracts contract = none := by
                  simpa [set_contract_state, transfer_balance] using hnone
                simpa [incoming_txs, trace_txs, step_txs, eval_tx, hneq] using
                  ih hpre
      | step_action_invalid _ _ henv _ _ _ _ =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simpa [incoming_txs, trace_txs, step_txs] using ih hpre
      | step_permute henv _ =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simpa [incoming_txs, trace_txs, step_txs] using ih hpre

/-- Coq direction: if a setup-deserialization yielded a deployment, then
    the contract is deployed. The reverse is *not* true: the contract may
    have been deployed with a different setup type, in which case
    `deserialize`-as-`Setup` fails and `deployment_info` returns `none`. -/
theorem deployment_info_some :
  ∀ (Setup : Type) [Serializable Setup]
    {to_ : @ChainState Base} (trace : ChainTrace empty_state to_)
    (caddr : Base.Address),
    deployment_info Setup trace caddr ≠ none →
    to_.env_contracts caddr ≠ none := by
  intro Setup _ to_ trace caddr hdep hnone
  induction trace with
  | clnil =>
      simp [deployment_info] at hdep
  | snoc tail step ih =>
      cases step with
      | step_block _ _ _ _ _ henv =>
          rw [henv.contracts_eq caddr] at hnone
          exact ih (by simpa [deployment_info, step_deployment_info] using hdep) hnone
      | step_action act acts new_acts hqueue eval hqueue' =>
          cases eval with
          | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
              rw [henv.contracts_eq caddr] at hnone
              exact ih (by simpa [deployment_info, step_deployment_info, eval_tx] using hdep) hnone
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew_acts =>
              rw [henv.contracts_eq caddr] at hnone
              by_cases heq : caddr = to_addr
              · subst heq
                simp [set_contract_state, add_contract, Address.address_eq_refl] at hnone
              · have hneq : Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne _ _ heq
                have hneq_sym : Base.address_eqb to_addr caddr = false := by
                  rw [Address.address_eq_sym]
                  exact hneq
                simp [set_contract_state, add_contract, hneq] at hnone
                exact ih
                  (by simpa [deployment_info, step_deployment_info, eval_tx, hneq_sym] using hdep)
                  hnone
          | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
              rw [henv.contracts_eq caddr] at hnone
              exact ih (by simpa [deployment_info, step_deployment_info, eval_tx] using hdep) hnone
      | step_action_invalid _ _ henv _ _ _ _ =>
          rw [henv.contracts_eq caddr] at hnone
          exact ih (by simpa [deployment_info, step_deployment_info] using hdep) hnone
      | step_permute henv _ =>
          rw [henv.contracts_eq caddr] at hnone
          exact ih (by simpa [deployment_info, step_deployment_info] using hdep) hnone

theorem deployment_info_addr_format :
  ∀ (Setup : Type) [Serializable Setup]
    {to_ : @ChainState Base} (trace : ChainTrace empty_state to_)
    (addr : Base.Address) (dep : @DeploymentInfo Base Setup),
    deployment_info Setup trace addr = some dep →
    Base.address_is_contract addr = true := by
  intro Setup _ to_ trace addr dep hdep
  have hsome : to_.env_contracts addr ≠ none :=
    deployment_info_some Setup trace addr (by rw [hdep]; simp)
  cases hcontract : to_.env_contracts addr with
  | none => exact False.elim (hsome hcontract)
  | some wc =>
      exact contract_addr_format addr wc (trace_reachable trace) hcontract

theorem undeployed_contract_no_in_calls :
  ∀ {Msg : Type} [Serializable Msg]
    (contract : Base.Address) {frm to_ : @ChainState Base} (trace : ChainTrace frm to_),
    Base.address_is_contract contract = true →
    to_.env_contracts contract = none →
    incoming_calls Msg trace contract = some [] := by
  intro Msg _ contract frm to_ trace his_contract hnone
  induction trace with
  | clnil =>
      simp [incoming_calls]
  | @snoc mid _ tail step ih =>
      cases step with
      | step_block _ _ _ _ _ henv =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simp [incoming_calls, step_incoming_calls, ih hpre]
      | step_action act acts new_acts hqueue eval hqueue' =>
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              have hpre : mid.env_contracts contract = none := by
                rw [henv.contracts_eq contract] at hnone
                exact hnone
              simp [incoming_calls, step_incoming_calls, eval_tx, ih hpre]
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew =>
              rw [henv.contracts_eq contract] at hnone
              by_cases hneq : Base.address_eqb to_addr contract = false
              · have hneq_sym : Base.address_eqb contract to_addr = false := by
                  rw [Address.address_eq_sym]
                  exact hneq
                have hpre : mid.env_contracts contract = none := by
                  simpa [set_contract_state, add_contract, hneq_sym] using hnone
                simp [incoming_calls, step_incoming_calls, eval_tx, hneq, ih hpre]
              · have heq_true : Base.address_eqb to_addr contract = true := by
                  cases h : Base.address_eqb to_addr contract
                  · exact False.elim (hneq h)
                  · rfl
                have hcontract_eq : contract = to_addr :=
                  ((Base.address_eqb_spec _ _).mp heq_true).symm
                subst hcontract_eq
                simp [set_contract_state, add_contract, Address.address_eq_refl] at hnone
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              rw [henv.contracts_eq contract] at hnone
              by_cases hneq : Base.address_eqb to_addr contract = false
              · have hpre : mid.env_contracts contract = none := by
                  simpa [set_contract_state, transfer_balance] using hnone
                simp [incoming_calls, step_incoming_calls, eval_tx, hneq, ih hpre]
              · have heq_true : Base.address_eqb to_addr contract = true := by
                  cases h : Base.address_eqb to_addr contract
                  · exact False.elim (hneq h)
                  · rfl
                have hcontract_eq : contract = to_addr :=
                  ((Base.address_eqb_spec _ _).mp heq_true).symm
                subst hcontract_eq
                simp [set_contract_state, transfer_balance, hcontract] at hnone
      | step_action_invalid _ _ henv _ _ _ _ =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simp [incoming_calls, step_incoming_calls, ih hpre]
      | step_permute henv _ =>
          have hpre : mid.env_contracts contract = none := by
            rw [henv.contracts_eq contract] at hnone
            exact hnone
          simp [incoming_calls, step_incoming_calls, ih hpre]

theorem incoming_txs_contract :
  ∀ (caddr : Base.Address) (bstate : @ChainState Base)
    (trace : ChainTrace empty_state bstate)
    (Setup : Type) [Serializable Setup] (depinfo : @DeploymentInfo Base Setup)
    (Msg : Type) [Serializable Msg] (msgs : List (@ContractCallInfo Base Msg)),
    deployment_info Setup trace caddr = some depinfo →
    incoming_calls Msg trace caddr = some msgs →
    (incoming_txs trace caddr).map (fun tx => (tx.tx_from, tx.tx_to, tx.tx_amount)) =
      msgs.map (fun call => (call.call_from, caddr, call.call_amount))
      ++ [(depinfo.deployment_from, caddr, depinfo.deployment_amount)] := by
  intro caddr bstate trace Setup _ depinfo Msg _ msgs hdep hcalls
  induction trace generalizing depinfo msgs with
  | clnil =>
      simp [deployment_info] at hdep
  | @snoc mid _ tail step ih =>
      cases step with
      | step_block _ _ _ _ _ _ =>
          have hcalls_tail : incoming_calls Msg tail caddr = some msgs := by
            simp [incoming_calls, step_incoming_calls] at hcalls
            cases htail : incoming_calls Msg tail caddr with
            | none => simp [htail] at hcalls
            | some prior =>
                simp [htail] at hcalls
                cases hcalls
                simp
          simpa [incoming_txs, trace_txs, step_txs] using
            ih depinfo msgs
              (by simpa [deployment_info, step_deployment_info] using hdep)
              hcalls_tail
      | step_action act acts new_acts hqueue eval hqueue' =>
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              by_cases hto : Base.address_eqb to_addr caddr = true
              · have hdep_tail : deployment_info Setup tail caddr = some depinfo := by
                  simpa [deployment_info, step_deployment_info, eval_tx, hto] using hdep
                have his_contract :
                    Base.address_is_contract caddr = true :=
                  deployment_info_addr_format Setup tail caddr depinfo hdep_tail
                have heq : to_addr = caddr := (Base.address_eqb_spec _ _).mp hto
                rw [heq, his_contract] at hnot_contract
                cases hnot_contract
              · have hto_false : Base.address_eqb to_addr caddr = false := by
                  cases h : Base.address_eqb to_addr caddr
                  · rfl
                  · exact False.elim (hto h)
                have hcalls_tail : incoming_calls Msg tail caddr = some msgs := by
                  simp [incoming_calls, step_incoming_calls, eval_tx, hto_false] at hcalls
                  cases htail : incoming_calls Msg tail caddr with
                  | none => simp [htail] at hcalls
                  | some prior =>
                      simp [htail] at hcalls
                      cases hcalls
                      simp
                simpa [incoming_txs, trace_txs, step_txs, eval_tx, hto_false] using
                  ih depinfo msgs
                    (by simpa [deployment_info, step_deployment_info, eval_tx, hto_false] using hdep)
                    hcalls_tail
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew =>
              by_cases hto : Base.address_eqb to_addr caddr = true
              · have heq : to_addr = caddr := (Base.address_eqb_spec _ _).mp hto
                subst caddr
                have htail_txs :
                    incoming_txs tail to_addr = [] :=
                  undeployed_contract_no_in_txs to_addr tail haddr hnot_deployed
                have htail_calls :
                    incoming_calls Msg tail to_addr = some [] :=
                  undeployed_contract_no_in_calls to_addr tail haddr hnot_deployed
                cases hsetup : (deserialize setup : Option Setup) with
                | none =>
                    have hdep_tail :
                        deployment_info Setup tail to_addr = some depinfo := by
                      simpa [deployment_info, step_deployment_info, eval_tx, hto, hsetup] using hdep
                    have hsome : mid.env_contracts to_addr ≠ none :=
                      deployment_info_some Setup tail to_addr (by rw [hdep_tail]; simp)
                    exact False.elim (hsome hnot_deployed)
                | some setup' =>
                    simp [deployment_info, step_deployment_info, eval_tx, hto, hsetup] at hdep
                    cases hdep
                    simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                      htail_calls] at hcalls
                    cases hcalls
                    unfold incoming_txs at htail_txs
                    simp [incoming_txs, trace_txs, step_txs, eval_tx, hto, htail_txs]
              · have hto_false : Base.address_eqb to_addr caddr = false := by
                  cases h : Base.address_eqb to_addr caddr
                  · rfl
                  · exact False.elim (hto h)
                have hcalls_tail : incoming_calls Msg tail caddr = some msgs := by
                  simp [incoming_calls, step_incoming_calls, eval_tx, hto_false] at hcalls
                  cases htail : incoming_calls Msg tail caddr with
                  | none => simp [htail] at hcalls
                  | some prior =>
                      simp [htail] at hcalls
                      cases hcalls
                      simp
                simpa [incoming_txs, trace_txs, step_txs, eval_tx, hto_false] using
                  ih depinfo msgs
                    (by simpa [deployment_info, step_deployment_info, eval_tx, hto_false] using hdep)
                    hcalls_tail
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              by_cases hto : Base.address_eqb to_addr caddr = true
              · have heq : to_addr = caddr := (Base.address_eqb_spec _ _).mp hto
                subst caddr
                have hdep_tail : deployment_info Setup tail to_addr = some depinfo := by
                  simpa [deployment_info, step_deployment_info, eval_tx, hto] using hdep
                cases htail_calls : incoming_calls Msg tail to_addr with
                | none =>
                    cases msg with
                    | none =>
                        simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                          htail_calls] at hcalls
                    | some ser_msg =>
                        cases hmsg : (deserialize ser_msg : Option Msg) with
                        | none =>
                            simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                              htail_calls, hmsg] at hcalls
                        | some msg' =>
                            simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                              htail_calls, hmsg] at hcalls
                | some prior_calls =>
                    have ih_tail := ih depinfo prior_calls hdep_tail htail_calls
                    cases msg with
                    | none =>
                        simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                          htail_calls] at hcalls
                        cases hcalls
                        unfold incoming_txs at ih_tail
                        simp [incoming_txs, trace_txs, step_txs, eval_tx, hto, ih_tail]
                    | some ser_msg =>
                        cases hmsg : (deserialize ser_msg : Option Msg) with
                        | none =>
                            simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                              htail_calls, hmsg] at hcalls
                        | some msg' =>
                            simp [incoming_calls, step_incoming_calls, eval_tx, hto,
                              htail_calls, hmsg] at hcalls
                            cases hcalls
                            unfold incoming_txs at ih_tail
                            simp [incoming_txs, trace_txs, step_txs, eval_tx, hto, ih_tail]
              · have hto_false : Base.address_eqb to_addr caddr = false := by
                  cases h : Base.address_eqb to_addr caddr
                  · rfl
                  · exact False.elim (hto h)
                have hcalls_tail : incoming_calls Msg tail caddr = some msgs := by
                  simp [incoming_calls, step_incoming_calls, eval_tx, hto_false] at hcalls
                  cases htail : incoming_calls Msg tail caddr with
                  | none => simp [htail] at hcalls
                  | some prior =>
                      simp [htail] at hcalls
                      cases hcalls
                      simp
                simpa [incoming_txs, trace_txs, step_txs, eval_tx, hto_false] using
                  ih depinfo msgs
                    (by simpa [deployment_info, step_deployment_info, eval_tx, hto_false] using hdep)
                    hcalls_tail
      | step_action_invalid _ _ _ _ _ _ _ =>
          have hcalls_tail : incoming_calls Msg tail caddr = some msgs := by
            simp [incoming_calls, step_incoming_calls] at hcalls
            cases htail : incoming_calls Msg tail caddr with
            | none => simp [htail] at hcalls
            | some prior =>
                simp [htail] at hcalls
                cases hcalls
                simp
          simpa [incoming_txs, trace_txs, step_txs] using
            ih depinfo msgs
              (by simpa [deployment_info, step_deployment_info] using hdep)
              hcalls_tail
      | step_permute _ _ =>
          have hcalls_tail : incoming_calls Msg tail caddr = some msgs := by
            simp [incoming_calls, step_incoming_calls] at hcalls
            cases htail : incoming_calls Msg tail caddr with
            | none => simp [htail] at hcalls
            | some prior =>
                simp [htail] at hcalls
                cases hcalls
                simp
          simpa [incoming_txs, trace_txs, step_txs] using
            ih depinfo msgs
              (by simpa [deployment_info, step_deployment_info] using hdep)
              hcalls_tail

theorem account_balance_trace :
  ∀ (state : @ChainState Base) (trace : ChainTrace empty_state state) (addr : Base.Address),
    state.env_account_balances addr =
      ConCert.Utils.Extras.sumZ (fun tx => tx.tx_amount) (incoming_txs trace addr)
      + ConCert.Utils.Extras.sumZ (fun b => b.block_reward) (created_blocks trace addr)
      - ConCert.Utils.Extras.sumZ (fun tx => tx.tx_amount) (outgoing_txs trace addr) := by
  intro state trace addr
  induction trace with
  | clnil =>
      simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
        ConCert.Utils.Extras.sumZ, empty_state]
  | @snoc mid _ tail step ih =>
      cases step with
      | step_block hdr _ _ _ _ henv =>
          rw [henv.account_balances_eq addr]
          unfold add_new_block_to_env add_balance
          by_cases hcreator : Base.address_eqb addr hdr.block_creator = true
          · have hcreator_sym : Base.address_eqb hdr.block_creator addr = true := by
              rw [Address.address_eq_sym]
              exact hcreator
            simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
              step_txs, step_blocks, ConCert.Utils.Extras.sumZ, hcreator, hcreator_sym, ih]
            ring_nf
          · have hcreator_sym : Base.address_eqb hdr.block_creator addr = false := by
              rw [Address.address_eq_sym]
              cases h : Base.address_eqb addr hdr.block_creator
              · rfl
              · exact False.elim (hcreator h)
            simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
              step_txs, step_blocks, hcreator, hcreator_sym, ih]
      | step_action act acts new_acts hqueue eval hqueue' =>
          rw [account_balance_post eval addr]
          rw [ih]
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              by_cases hto : Base.address_eqb to_addr addr = true
              · have hto_sym : Base.address_eqb addr to_addr = true := by
                  rw [Address.address_eq_sym]
                  exact hto
                by_cases hfrom : Base.address_eqb from_addr addr = true
                · have hfrom_sym : Base.address_eqb addr from_addr = true := by
                    rw [Address.address_eq_sym]
                    exact hfrom
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
                · have hfrom_sym : Base.address_eqb addr from_addr = false := by
                    rw [Address.address_eq_sym]
                    cases h : Base.address_eqb from_addr addr
                    · rfl
                    · exact False.elim (hfrom h)
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
              · have hto_sym : Base.address_eqb addr to_addr = false := by
                  rw [Address.address_eq_sym]
                  cases h : Base.address_eqb to_addr addr
                  · rfl
                  · exact False.elim (hto h)
                by_cases hfrom : Base.address_eqb from_addr addr = true
                · have hfrom_sym : Base.address_eqb addr from_addr = true := by
                    rw [Address.address_eq_sym]
                    exact hfrom
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
                · have hfrom_sym : Base.address_eqb addr from_addr = false := by
                    rw [Address.address_eq_sym]
                    cases h : Base.address_eqb from_addr addr
                    · rfl
                    · exact False.elim (hfrom h)
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from,
                    hto, hto_sym, hfrom, hfrom_sym]
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew =>
              by_cases hto : Base.address_eqb to_addr addr = true
              · have hto_sym : Base.address_eqb addr to_addr = true := by
                  rw [Address.address_eq_sym]
                  exact hto
                by_cases hfrom : Base.address_eqb from_addr addr = true
                · have hfrom_sym : Base.address_eqb addr from_addr = true := by
                    rw [Address.address_eq_sym]
                    exact hfrom
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
                · have hfrom_sym : Base.address_eqb addr from_addr = false := by
                    rw [Address.address_eq_sym]
                    cases h : Base.address_eqb from_addr addr
                    · rfl
                    · exact False.elim (hfrom h)
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
              · have hto_sym : Base.address_eqb addr to_addr = false := by
                  rw [Address.address_eq_sym]
                  cases h : Base.address_eqb to_addr addr
                  · rfl
                  · exact False.elim (hto h)
                by_cases hfrom : Base.address_eqb from_addr addr = true
                · have hfrom_sym : Base.address_eqb addr from_addr = true := by
                    rw [Address.address_eq_sym]
                    exact hfrom
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
                · have hfrom_sym : Base.address_eqb addr from_addr = false := by
                    rw [Address.address_eq_sym]
                    cases h : Base.address_eqb from_addr addr
                    · rfl
                    · exact False.elim (hfrom h)
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from,
                    hto, hto_sym, hfrom, hfrom_sym]
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              by_cases hto : Base.address_eqb to_addr addr = true
              · have hto_sym : Base.address_eqb addr to_addr = true := by
                  rw [Address.address_eq_sym]
                  exact hto
                by_cases hfrom : Base.address_eqb from_addr addr = true
                · have hfrom_sym : Base.address_eqb addr from_addr = true := by
                    rw [Address.address_eq_sym]
                    exact hfrom
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
                · have hfrom_sym : Base.address_eqb addr from_addr = false := by
                    rw [Address.address_eq_sym]
                    cases h : Base.address_eqb from_addr addr
                    · rfl
                    · exact False.elim (hfrom h)
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
              · have hto_sym : Base.address_eqb addr to_addr = false := by
                  rw [Address.address_eq_sym]
                  cases h : Base.address_eqb to_addr addr
                  · rfl
                  · exact False.elim (hto h)
                by_cases hfrom : Base.address_eqb from_addr addr = true
                · have hfrom_sym : Base.address_eqb addr from_addr = true := by
                    rw [Address.address_eq_sym]
                    exact hfrom
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from, ActionEvaluation.eval_amount,
                    ConCert.Utils.Extras.sumZ,
                    hto, hto_sym, hfrom, hfrom_sym]
                  ring_nf
                · have hfrom_sym : Base.address_eqb addr from_addr = false := by
                    rw [Address.address_eq_sym]
                    cases h : Base.address_eqb from_addr addr
                    · rfl
                    · exact False.elim (hfrom h)
                  simp [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
                    step_txs, step_blocks, eval_tx, ActionEvaluation.eval_to,
                    ActionEvaluation.eval_from,
                    hto, hto_sym, hfrom, hfrom_sym]
      | step_action_invalid _ _ henv _ _ _ _ =>
          rw [henv.account_balances_eq addr]
          simpa [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
            step_txs, step_blocks] using ih
      | step_permute henv _ =>
          rw [henv.account_balances_eq addr]
          simpa [incoming_txs, outgoing_txs, created_blocks, trace_txs, trace_blocks,
            step_txs, step_blocks] using ih

theorem contract_no_created_blocks
    (state : @ChainState Base) (addr : Base.Address) {frm : @ChainState Base}
    (trace : ChainTrace frm state)
    (h : Base.address_is_contract addr = true) :
    created_blocks trace addr = [] := by
  unfold created_blocks
  induction trace with
  | clnil => simp [trace_blocks]
  | snoc tail s ih =>
    simp only [trace_blocks, List.filter_append, step_blocks]
    cases s with
    | step_block hdr _ hvalid _ _ _ =>
      have h_creator_ne_addr : hdr.block_creator ≠ addr := by
        intro heq
        have hcv := hvalid.valid_creator
        rw [heq] at hcv
        rw [h] at hcv
        cases hcv
      have h_eqb : Base.address_eqb hdr.block_creator addr = false :=
        Address.address_eq_ne _ _ h_creator_ne_addr
      simp [List.filter, h_eqb, ih]
    | step_action _ _ _ _ _ _ => simp [List.filter, ih]
    | step_action_invalid _ _ _ _ _ _ _ => simp [List.filter, ih]
    | step_permute _ _ => simp [List.filter, ih]

theorem undeployed_contract_balance_0 :
  ∀ (state : @ChainState Base) (addr : Base.Address),
    reachable state →
    Base.address_is_contract addr = true →
    state.env_contracts addr = none →
    state.env_account_balances addr = 0 := by
  intro state addr hreach his_contract hnone
  rcases hreach with ⟨trace⟩
  rw [account_balance_trace state trace addr]
  rw [undeployed_contract_no_in_txs addr trace his_contract hnone]
  rw [undeployed_contract_no_out_txs addr trace his_contract hnone]
  rw [contract_no_created_blocks state addr trace his_contract]
  simp [ConCert.Utils.Extras.sumZ]

theorem account_balance_nonnegative
    (state : @ChainState Base) (addr : Base.Address) (h : reachable state) :
    state.env_account_balances addr ≥ 0 := by
  obtain ⟨t⟩ := h
  induction t with
  | clnil =>
    -- empty_state has all balances = 0
    show (0 : Amount) ≥ 0
    rfl
  | snoc _ s ih =>
    cases s with
    | step_block hdr _ hvalid _ _ henv =>
      rw [henv.account_balances_eq addr]
      show add_balance hdr.block_creator hdr.block_reward _ addr ≥ 0
      unfold add_balance
      have hr : (0 : Int) ≤ hdr.block_reward := hvalid.valid_reward
      by_cases hbr : Base.address_eqb addr hdr.block_creator = true
      · rw [if_pos hbr]
        change (0 : Int) ≤ hdr.block_reward + _
        have hih_i : (0 : Int) ≤ _ := ih
        omega
      · rw [if_neg hbr]
        exact ih
    | step_action _ _ _ _ eval _ =>
      rw [account_balance_post eval addr]
      have hnn : (0 : Int) ≤ ActionEvaluation.eval_amount eval :=
        eval_amount_nonnegative eval
      have hle : (ActionEvaluation.eval_amount eval : Int) ≤ _ :=
        eval_amount_le_account_balance eval
      have hih_i : (0 : Int) ≤ _ := ih
      by_cases hfrom : Base.address_eqb addr (ActionEvaluation.eval_from eval) = true
      · have hfrom_eq : addr = ActionEvaluation.eval_from eval :=
          (Base.address_eqb_spec _ _).mp hfrom
        by_cases hto : Base.address_eqb addr (ActionEvaluation.eval_to eval) = true
        · rw [if_pos hto, if_pos hfrom]
          show (0 : Int) ≤ _
          omega
        · rw [if_neg hto, if_pos hfrom]
          have hle_addr := hle
          rw [← hfrom_eq] at hle_addr
          show (0 : Int) ≤ _
          linarith
      · by_cases hto : Base.address_eqb addr (ActionEvaluation.eval_to eval) = true
        · rw [if_pos hto, if_neg hfrom]
          show (0 : Int) ≤ _
          omega
        · rw [if_neg hto, if_neg hfrom]
          show (0 : Int) ≤ _
          omega
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [henv.account_balances_eq addr]
      exact ih
    | step_permute henv _ =>
      rw [henv.account_balances_eq addr]
      exact ih

private theorem contract_state_env_equiv
    {State : Type} [Serializable State]
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env')
    (addr : Base.Address) :
    @contract_state Base State _ env addr =
      @contract_state Base State _ env' addr := by
  unfold contract_state
  rw [henv.contract_states_eq addr]

theorem deployed_contract_state_typed :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    {bstate : @ChainState Base} (caddr : Base.Address),
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    reachable bstate →
    ∃ cstate, @contract_state Base State _ bstate.toEnvironment caddr = some cstate := by
  intro Setup Msg State Error _ _ _ _ contract bstate caddr hdeployed hreachable
  obtain ⟨trace⟩ := hreachable
  induction trace with
  | clnil =>
      simp [empty_state] at hdeployed
  | @snoc mid _ tail step ih =>
      cases step with
      | step_block _ _ _ _ _ henv =>
          rw [henv.contracts_eq caddr] at hdeployed
          obtain ⟨cstate, hcstate⟩ := ih hdeployed
          refine ⟨cstate, ?_⟩
          rw [contract_state_env_equiv henv caddr]
          simpa using hcstate
      | step_action act acts new_acts hqueue eval hqueue' =>
          cases eval with
          | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
              rw [henv.contracts_eq caddr] at hdeployed
              obtain ⟨cstate, hcstate⟩ := ih hdeployed
              refine ⟨cstate, ?_⟩
              rw [contract_state_env_equiv henv caddr]
              simpa using hcstate
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew =>
              rw [henv.contracts_eq caddr] at hdeployed
              by_cases heq : caddr = to_addr
              · subst heq
                have hdeployed_here : wc = contract_to_weak_contract contract := by
                  simpa [set_contract_state, add_contract, Address.address_eq_refl] using hdeployed
                subst hdeployed_here
                obtain ⟨setup_strong, result_strong, hsetup, hser, hinit_strong⟩ :=
                  wc_init_strong (contract := contract) hinit
                refine ⟨result_strong, ?_⟩
                rw [contract_state_env_equiv henv caddr]
                simp [contract_state, set_contract_state, set_chain_contract_state,
                  Address.address_eq_refl, ← hser, Serializable.deserialize_serialize]
              · have hneq : Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne _ _ heq
                have hdeployed_pre : mid.env_contracts caddr =
                    some (contract_to_weak_contract contract) := by
                  simpa [set_contract_state, add_contract, hneq] using hdeployed
                obtain ⟨cstate, hcstate⟩ := ih hdeployed_pre
                refine ⟨cstate, ?_⟩
                rw [contract_state_env_equiv henv caddr]
                simpa [contract_state, set_contract_state, set_chain_contract_state,
                  hneq, add_contract, transfer_balance] using hcstate
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              rw [henv.contracts_eq caddr] at hdeployed
              by_cases heq : caddr = to_addr
              · subst heq
                have hwc : wc = contract_to_weak_contract contract := by
                  exact Option.some.inj (hcontract.symm.trans hdeployed)
                subst hwc
                obtain ⟨prev_state_strong, msg_strong, new_state_strong,
                  hprev, hmsg, hser, hreceive_strong⟩ :=
                  wc_receive_strong (contract := contract) hreceive
                refine ⟨new_state_strong, ?_⟩
                rw [contract_state_env_equiv henv caddr]
                simp [contract_state, set_contract_state, set_chain_contract_state,
                  Address.address_eq_refl, ← hser, Serializable.deserialize_serialize]
              · have hneq : Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne _ _ heq
                have hdeployed_pre : mid.env_contracts caddr =
                    some (contract_to_weak_contract contract) := by
                  simpa [set_contract_state, transfer_balance] using hdeployed
                obtain ⟨cstate, hcstate⟩ := ih hdeployed_pre
                refine ⟨cstate, ?_⟩
                rw [contract_state_env_equiv henv caddr]
                simpa [contract_state, set_contract_state, set_chain_contract_state,
                  hneq, transfer_balance] using hcstate
      | step_action_invalid _ _ henv _ _ _ _ =>
          rw [henv.contracts_eq caddr] at hdeployed
          obtain ⟨cstate, hcstate⟩ := ih hdeployed
          refine ⟨cstate, ?_⟩
          rw [contract_state_env_equiv henv caddr]
          simpa using hcstate
      | step_permute henv _ =>
          rw [henv.contracts_eq caddr] at hdeployed
          obtain ⟨cstate, hcstate⟩ := ih hdeployed
          refine ⟨cstate, ?_⟩
          rw [contract_state_env_equiv henv caddr]
          simpa using hcstate

omit Base in
private theorem forall_cons_head
    {A : Type} {P : A → Prop} {x : A} {xs : List A}
    (h : (x :: xs).Forall P) : P x := by
  rw [← ConCert.Utils.Extras.All_Forall] at h
  exact h.1

omit Base in
private theorem forall_cons_tail
    {A : Type} {P : A → Prop} {x : A} {xs : List A}
    (h : (x :: xs).Forall P) : xs.Forall P := by
  rw [← ConCert.Utils.Extras.All_Forall] at h ⊢
  exact h.2

private theorem action_bodies_origin_account
    (origin to_addr : Base.Address) (bodies : List (@ActionBody Base))
    (horigin : Base.address_is_contract origin = false) :
    (bodies.map
      (fun body => { act_origin := origin, act_from := to_addr, act_body := body })).Forall
        act_origin_is_account := by
  rw [← ConCert.Utils.Extras.All_Forall]
  induction bodies with
  | nil => trivial
  | cons _ _ ih =>
    exact ⟨horigin, ih⟩

theorem origin_is_always_account :
  ∀ {bstate : @ChainState Base},
    reachable bstate →
    bstate.chain_state_queue.Forall act_origin_is_account := by
  intro bstate hreach
  obtain ⟨trace⟩ := hreach
  induction trace with
  | clnil =>
    show ([] : List (@Action Base)).Forall act_origin_is_account
    trivial
  | snoc tail step ih =>
    cases step with
    | step_block _ _ _ hfrom heq _ =>
      exact origin_is_account _ hfrom heq
    | step_action act acts new_acts hqprev eval hqnext =>
      have hprev : (act :: acts).Forall act_origin_is_account := by
        rw [← hqprev]
        exact ih
      have hact : act_origin_is_account act := forall_cons_head hprev
      have hacts : acts.Forall act_origin_is_account := forall_cons_tail hprev
      have hnew : new_acts.Forall act_origin_is_account := by
        cases eval with
        | eval_transfer _ _ _ _ _ _ _ _ _ hnew_nil =>
          rw [hnew_nil]
          trivial
        | eval_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnew_nil =>
          rw [hnew_nil]
          trivial
        | eval_call origin _ to_addr _ _ _ _ _ resp_acts _ _ _ _ hact_eq _ hnew_eq _ =>
          rw [hact_eq] at hact
          rw [hnew_eq]
          exact action_bodies_origin_account origin to_addr resp_acts hact
      rw [hqnext]
      exact (ConCert.Utils.Extras.Forall_app _ _ _).mp ⟨hnew, hacts⟩
    | step_action_invalid act acts _ hqprev hqnext _ _ =>
      have hprev : (act :: acts).Forall act_origin_is_account := by
        rw [← hqprev]
        exact ih
      rw [hqnext]
      exact forall_cons_tail hprev
    | step_permute _ hperm =>
      exact ConCert.Utils.Extras.forall_respects_permutation _ _ _ hperm ih

private theorem trace_finalized_height_le_chain_height
    {bstate : @ChainState Base} (t : ChainTrace empty_state bstate) :
    (env_chain bstate.toEnvironment).finalized_height ≤
      (env_chain bstate.toEnvironment).chain_height := by
  induction t with
  | clnil => exact Nat.le_refl _
  | snoc tail s ih =>
    cases s with
    | step_block hdr _ hvalid _ _ henv =>
      rw [henv.chain_eq]
      show hdr.block_finalized_height ≤ hdr.block_height
      exact Nat.le_of_lt hvalid.valid_finalized_height.2
    | step_action _ _ _ _ eval _ =>
      rw [chain_height_post_action eval, finalized_height_post_action eval]
      exact ih
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [henv.chain_eq]
      exact ih
    | step_permute henv _ =>
      rw [henv.chain_eq]
      exact ih

theorem finalized_heigh_chain_height
    (bstate : @ChainState Base) (h : reachable bstate) :
    (env_chain bstate.toEnvironment).finalized_height <
      (env_chain bstate.toEnvironment).chain_height + 1 := by
  obtain ⟨t⟩ := h
  exact Nat.lt_succ_of_le (trace_finalized_height_le_chain_height t)

theorem contract_states_deployed
    (to_ : @ChainState Base) (addr : Base.Address) (state : SerializedValue)
    (hr : reachable to_) (hs : to_.env_contract_states addr = some state) :
    ∃ wc, to_.env_contracts addr = some wc := by
  obtain ⟨t⟩ := hr
  induction t generalizing state with
  | clnil =>
    -- empty_state.env_contract_states addr = none
    have : (empty_state : @ChainState Base).env_contract_states addr = none := rfl
    rw [this] at hs
    cases hs
  | snoc tail s ih =>
    cases s with
    | step_block _ _ _ _ _ henv =>
      rw [henv.contract_states_eq addr] at hs
      rw [henv.contracts_eq addr]
      exact ih state hs
    | step_action _ _ _ _ eval _ =>
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
        rw [henv.contract_states_eq addr] at hs
        rw [henv.contracts_eq addr]
        exact ih state hs
      | eval_deploy _ _ to_addr _ wc _ state' _ _ _ _ _ _ henv _ =>
        rw [henv.contracts_eq addr]
        rw [henv.contract_states_eq addr] at hs
        show ∃ w, (set_contract_state _ _ (add_contract _ _ _)).env_contracts addr = some w
        unfold set_contract_state set_chain_contract_state at hs
        simp only at hs
        unfold add_contract set_contract_state
        simp only
        by_cases haddr : Base.address_eqb addr to_addr = true
        · rw [if_pos haddr]
          exact ⟨wc, rfl⟩
        · rw [if_neg haddr]
          rw [if_neg haddr] at hs
          exact ih state hs
      | eval_call _ _ to_addr _ wc _ _ _ _ _ _ hcontract _ _ _ _ henv =>
        rw [henv.contracts_eq addr]
        rw [henv.contract_states_eq addr] at hs
        show ∃ w, (set_contract_state _ _ _).env_contracts addr = some w
        unfold set_contract_state set_chain_contract_state at hs
        simp only at hs
        unfold set_contract_state
        simp only
        by_cases haddr : Base.address_eqb addr to_addr = true
        · have heq := (Base.address_eqb_spec _ _).mp haddr
          rw [heq]
          exact ⟨wc, hcontract⟩
        · rw [if_neg haddr] at hs
          exact ih state hs
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [henv.contract_states_eq addr] at hs
      rw [henv.contracts_eq addr]
      exact ih state hs
    | step_permute henv _ =>
      rw [henv.contract_states_eq addr] at hs
      rw [henv.contracts_eq addr]
      exact ih state hs

theorem contract_states_addr_format
    (to_ : @ChainState Base) (addr : Base.Address) (state : SerializedValue)
    (hr : reachable to_) (hs : to_.env_contract_states addr = some state) :
    Base.address_is_contract addr = true := by
  obtain ⟨wc, hwc⟩ := contract_states_deployed to_ addr state hr hs
  exact contract_addr_format addr wc hr hwc

theorem deployment_amount_nonnegative :
  ∀ {Setup : Type} [Serializable Setup]
    {to_ : @ChainState Base} (trace : ChainTrace empty_state to_)
    (caddr : Base.Address) (dep : @DeploymentInfo Base Setup),
    deployment_info Setup trace caddr = some dep → dep.deployment_amount ≥ 0 := by
  intro Setup _ to_ trace caddr dep hdep
  induction trace with
  | clnil =>
    simp [deployment_info] at hdep
  | snoc tail step ih =>
    cases step with
    | step_block _ _ _ _ _ _ =>
      simp [deployment_info, step_deployment_info] at hdep
      exact ih hdep
    | step_action _ _ _ _ eval _ =>
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ _ _ =>
        simp [deployment_info, step_deployment_info, eval_tx] at hdep
        exact ih hdep
      | eval_deploy origin from_addr to_addr amount wc setup state hamount _ _ _ _ _ _ _ =>
        simp [deployment_info, step_deployment_info, eval_tx] at hdep
        by_cases haddr : Base.address_eqb to_addr caddr = true
        · rw [if_pos haddr] at hdep
          cases hsetup : (deserialize setup : Option Setup) with
          | none =>
            rw [hsetup] at hdep
            exact ih hdep
          | some setup' =>
            rw [hsetup] at hdep
            cases hdep
            exact hamount
        · rw [if_neg haddr] at hdep
          exact ih hdep
      | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        simp [deployment_info, step_deployment_info, eval_tx] at hdep
        exact ih hdep
    | step_action_invalid _ _ _ _ _ _ _ =>
      simp [deployment_info, step_deployment_info] at hdep
      exact ih hdep
    | step_permute _ _ =>
      simp [deployment_info, step_deployment_info] at hdep
      exact ih hdep

theorem origin_user_address :
  ∀ (bstate : @ChainState Base),
    reachable bstate →
    bstate.chain_state_queue.Forall act_origin_is_account := by
  intro bstate hreach
  exact origin_is_always_account hreach

private theorem trace_chain_height_le_current_slot
    {bstate : @ChainState Base} (t : ChainTrace empty_state bstate) :
    (env_chain bstate.toEnvironment).chain_height ≤
      (env_chain bstate.toEnvironment).current_slot := by
  induction t with
  | clnil => exact Nat.le_refl _
  | snoc tail s ih =>
    cases s with
    | step_block hdr _ hvalid _ _ henv =>
      rw [henv.chain_eq]
      show hdr.block_height ≤ hdr.block_slot
      have h1 := hvalid.valid_height
      have h2 := hvalid.valid_slot
      omega
    | step_action _ _ _ _ eval _ =>
      rw [chain_height_post_action eval, current_slot_post_action eval]
      exact ih
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [henv.chain_eq]
      exact ih
    | step_permute henv _ =>
      rw [henv.chain_eq]
      exact ih

theorem current_slot_chain_height
    (bstate : @ChainState Base) (h : reachable bstate) :
    (env_chain bstate.toEnvironment).chain_height ≤
      (env_chain bstate.toEnvironment).current_slot := by
  obtain ⟨t⟩ := h
  exact trace_chain_height_le_current_slot t

/-- Validity contribution from a single chain step.
    For action evaluations: transfer contributes `True`, deploy/call contribute
    `ValidContext ctx` where `ctx` is the context passed to `wc_init`/`wc_receive`.
    Block/permute/invalid steps contribute `True`. -/
def step_context_valid {prev next : @ChainState Base} (step : ChainStep prev next) : Prop :=
  match step with
  | .step_action _ _ _ _ eval _ =>
    let tx := eval_tx eval
    match tx.tx_body with
    | .tx_empty       => True
    | .tx_deploy _ _  =>
      ValidContext { ctx_origin := tx.tx_origin, ctx_from := tx.tx_from,
                     ctx_contract_address := tx.tx_to,
                     ctx_contract_balance := tx.tx_amount,
                     ctx_amount := tx.tx_amount }
    | .tx_call _      =>
      ValidContext { ctx_origin := tx.tx_origin, ctx_from := tx.tx_from,
                     ctx_contract_address := tx.tx_to,
                     ctx_contract_balance := next.env_account_balances tx.tx_to,
                     ctx_amount := tx.tx_amount }
  | _ => True

/-- Every step in the trace has a valid context. -/
def context_valid' : ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | _, _, .clnil      => True
  | _, _, .snoc xs s  => context_valid' xs ∧ step_context_valid s

theorem context_valid :
  ∀ (bstate : @ChainState Base) (trace : ChainTrace empty_state bstate),
    context_valid' trace := by
  intro bstate trace
  induction trace with
  | clnil =>
    simp [context_valid']
  | snoc tail step ih =>
    simp only [context_valid']
    refine ⟨ih, ?_⟩
    have hnext_reachable : reachable _ := ⟨ChainedList.snoc tail step⟩
    cases step with
    | step_block _ _ _ _ _ _ => trivial
    | step_action act acts _ hqprev eval _ =>
      have hqueue : (act :: acts).Forall act_origin_is_account := by
        rw [← hqprev]
        exact origin_user_address _ ⟨tail⟩
      have hact_origin : act_origin_is_account act := forall_cons_head hqueue
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ _ _ => trivial
      | eval_deploy origin _ to_addr amount _ _ _ hamount _ hcontract_addr _ hact_eq _ _ _ =>
        rw [hact_eq] at hact_origin
        exact
          { ctx_origin_valid := hact_origin
            ctx_contract_address_valid := hcontract_addr
            ctx_contract_balance_valid := hamount
            ctx_amount_valid := hamount }
      | eval_call origin _ to_addr amount wc _ _ _ _ hamount _ hcontract _ hact_eq _ _ _ =>
        rw [hact_eq] at hact_origin
        exact
          { ctx_origin_valid := hact_origin
            ctx_contract_address_valid := contract_addr_format to_addr wc ⟨tail⟩ hcontract
            ctx_contract_balance_valid := account_balance_nonnegative _ to_addr hnext_reachable
            ctx_amount_valid := hamount }
    | step_action_invalid _ _ _ _ _ _ _ => trivial
    | step_permute _ _ => trivial

/-- Validity contribution of a single step for the chain at that step's
    pre-state. -/
def step_chain_valid {prev next : @ChainState Base} (step : ChainStep prev next) : Prop :=
  match step with
  | .step_action _ _ _ _ eval _ =>
    let tx := eval_tx eval
    match tx.tx_body with
    | .tx_empty       => True
    | .tx_deploy _ _  => ValidChain (env_chain prev.toEnvironment)
    | .tx_call _      => ValidChain (env_chain prev.toEnvironment)
  | _ => True

def chain_valid' : ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | _, _, .clnil      => True
  | _, _, .snoc xs s  => chain_valid' xs ∧ step_chain_valid s

theorem chain_valid :
  ∀ (bstate : @ChainState Base) (trace : ChainTrace empty_state bstate),
    chain_valid' trace := by
  intro bstate trace
  induction trace with
  | clnil =>
    simp [chain_valid']
  | snoc tail step ih =>
    simp only [chain_valid']
    refine ⟨ih, ?_⟩
    cases step with
    | step_block _ _ _ _ _ _ => trivial
    | step_action _ _ _ _ eval _ =>
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ _ _ => trivial
      | eval_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact
          { chain_height_valid := current_slot_chain_height _ ⟨tail⟩
            finalized_height_valid := finalized_heigh_chain_height _ ⟨tail⟩ }
      | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact
          { chain_height_valid := current_slot_chain_height _ ⟨tail⟩
            finalized_height_valid := finalized_heigh_chain_height _ ⟨tail⟩ }
    | step_action_invalid _ _ _ _ _ _ _ => trivial
    | step_permute _ _ => trivial

/-! ### Reachable-through facts -/

theorem reachable_through_contract_deployed
    (frm to_ : @ChainState Base) (addr : Base.Address) (wc : @WeakContract Base)
    (h : reachable_through frm to_)
    (hd : frm.env_contracts addr = some wc) :
    to_.env_contracts addr = some wc := by
  obtain ⟨_, ⟨t⟩⟩ := h
  induction t with
  | clnil => exact hd
  | snoc tail s ih =>
    cases s with
    | step_block _ _ _ _ _ henv =>
      rw [henv.contracts_eq addr]
      show (add_new_block_to_env _ _).env_contracts addr = some wc
      exact ih
    | step_action _ _ _ _ eval _ =>
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
        rw [henv.contracts_eq addr]
        exact ih
      | eval_deploy _ _ to_addr _ wc' _ _ _ _ _ hno _ _ henv _ =>
        rw [henv.contracts_eq addr]
        show (set_contract_state _ _ (add_contract _ _ _)).env_contracts addr = some wc
        simp [set_contract_state, add_contract]
        by_cases haddr : Base.address_eqb addr to_addr = true
        · rw [if_pos haddr]
          -- but then ih says pre.env_contracts addr = some wc, while hno says pre.env_contracts to_addr = none, and addr = to_addr
          have heq := (Base.address_eqb_spec _ _).mp haddr
          rw [heq] at ih
          rw [hno] at ih
          cases ih
        · rw [if_neg haddr]
          exact ih
      | eval_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henv =>
        rw [henv.contracts_eq addr]
        exact ih
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [henv.contracts_eq addr]
      exact ih
    | step_permute henv _ =>
      rw [henv.contracts_eq addr]
      exact ih

theorem reachable_through_contract_state
    (frm to_ : @ChainState Base) (addr : Base.Address) (cstate : SerializedValue)
    (h : reachable_through frm to_)
    (hd : frm.env_contract_states addr = some cstate) :
    ∃ cstate', to_.env_contract_states addr = some cstate' := by
  obtain ⟨_, ⟨t⟩⟩ := h
  induction t with
  | clnil => exact ⟨cstate, hd⟩
  | snoc tail s ih =>
    obtain ⟨cs, hcs⟩ := ih
    cases s with
    | step_block _ _ _ _ _ henv =>
      refine ⟨cs, ?_⟩
      rw [henv.contract_states_eq addr]
      exact hcs
    | step_action _ _ _ _ eval _ =>
      cases eval with
      | eval_transfer _ _ _ _ _ _ _ _ henv _ =>
        refine ⟨cs, ?_⟩
        rw [henv.contract_states_eq addr]
        exact hcs
      | eval_deploy _ _ to_addr _ _ _ state _ _ _ _ _ _ henv _ =>
        rw [henv.contract_states_eq addr]
        show ∃ cs', (set_contract_state _ _ _).env_contract_states addr = some cs'
        unfold set_contract_state set_chain_contract_state
        simp only
        by_cases haddr : Base.address_eqb addr to_addr = true
        · rw [if_pos haddr]; exact ⟨state, rfl⟩
        · rw [if_neg haddr]; exact ⟨cs, hcs⟩
      | eval_call _ _ to_addr _ _ _ _ new_state _ _ _ _ _ _ _ _ henv =>
        rw [henv.contract_states_eq addr]
        show ∃ cs', (set_contract_state _ _ _).env_contract_states addr = some cs'
        unfold set_contract_state set_chain_contract_state
        simp only
        by_cases haddr : Base.address_eqb addr to_addr = true
        · rw [if_pos haddr]; exact ⟨new_state, rfl⟩
        · rw [if_neg haddr]; exact ⟨cs, hcs⟩
    | step_action_invalid _ _ henv _ _ _ _ =>
      refine ⟨cs, ?_⟩
      rw [henv.contract_states_eq addr]
      exact hcs
    | step_permute henv _ =>
      refine ⟨cs, ?_⟩
      rw [henv.contract_states_eq addr]
      exact hcs

/-- A single `ChainStep` never decreases chain height. -/
private theorem step_chain_height_le {prev next : @ChainState Base}
    (step : ChainStep prev next) :
    (env_chain prev.toEnvironment).chain_height ≤
      (env_chain next.toEnvironment).chain_height := by
  cases step with
  | step_block hdr _ hvalid _ _ henv =>
    -- next.chain_height = (add_new_block_to_env hdr prev).chain_height = hdr.block_height
    -- = prev.chain_height + 1
    rw [show env_chain next.toEnvironment = env_chain (add_new_block_to_env hdr prev.toEnvironment)
        from henv.chain_eq]
    show _ ≤ hdr.block_height
    rw [hvalid.valid_height]; omega
  | step_action _ _ _ _ eval _ =>
    rw [chain_height_post_action eval]
  | step_action_invalid _ _ henv _ _ _ _ =>
    rw [show env_chain next.toEnvironment = env_chain prev.toEnvironment from henv.chain_eq]
  | step_permute henv _ =>
    rw [show env_chain next.toEnvironment = env_chain prev.toEnvironment from henv.chain_eq]

/-- A single `ChainStep` never decreases current slot. -/
private theorem step_current_slot_le {prev next : @ChainState Base}
    (step : ChainStep prev next) :
    (env_chain prev.toEnvironment).current_slot ≤
      (env_chain next.toEnvironment).current_slot := by
  cases step with
  | step_block hdr _ hvalid _ _ henv =>
    rw [show env_chain next.toEnvironment = env_chain (add_new_block_to_env hdr prev.toEnvironment)
        from henv.chain_eq]
    show _ ≤ hdr.block_slot
    exact Nat.le_of_lt hvalid.valid_slot
  | step_action _ _ _ _ eval _ =>
    rw [current_slot_post_action eval]
  | step_action_invalid _ _ henv _ _ _ _ =>
    rw [show env_chain next.toEnvironment = env_chain prev.toEnvironment from henv.chain_eq]
  | step_permute henv _ =>
    rw [show env_chain next.toEnvironment = env_chain prev.toEnvironment from henv.chain_eq]

/-- A single `ChainStep` never decreases finalized height. -/
private theorem step_finalized_height_le {prev next : @ChainState Base}
    (step : ChainStep prev next) :
    (env_chain prev.toEnvironment).finalized_height ≤
      (env_chain next.toEnvironment).finalized_height := by
  cases step with
  | step_block hdr _ hvalid _ _ henv =>
    rw [show env_chain next.toEnvironment = env_chain (add_new_block_to_env hdr prev.toEnvironment)
        from henv.chain_eq]
    show _ ≤ hdr.block_finalized_height
    exact hvalid.valid_finalized_height.1
  | step_action _ _ _ _ eval _ =>
    rw [finalized_height_post_action eval]
  | step_action_invalid _ _ henv _ _ _ _ =>
    rw [show env_chain next.toEnvironment = env_chain prev.toEnvironment from henv.chain_eq]
  | step_permute henv _ =>
    rw [show env_chain next.toEnvironment = env_chain prev.toEnvironment from henv.chain_eq]

private theorem trace_chain_height_le {frm to_ : @ChainState Base}
    (t : ChainTrace frm to_) :
    (env_chain frm.toEnvironment).chain_height ≤
      (env_chain to_.toEnvironment).chain_height := by
  induction t with
  | clnil => exact Nat.le_refl _
  | snoc _ step ih => exact ih.trans (step_chain_height_le step)

private theorem trace_current_slot_le {frm to_ : @ChainState Base}
    (t : ChainTrace frm to_) :
    (env_chain frm.toEnvironment).current_slot ≤
      (env_chain to_.toEnvironment).current_slot := by
  induction t with
  | clnil => exact Nat.le_refl _
  | snoc _ step ih => exact ih.trans (step_current_slot_le step)

private theorem trace_finalized_height_le {frm to_ : @ChainState Base}
    (t : ChainTrace frm to_) :
    (env_chain frm.toEnvironment).finalized_height ≤
      (env_chain to_.toEnvironment).finalized_height := by
  induction t with
  | clnil => exact Nat.le_refl _
  | snoc _ step ih => exact ih.trans (step_finalized_height_le step)

theorem reachable_through_chain_height
    (frm to_ : @ChainState Base) (h : reachable_through frm to_) :
    (env_chain frm.toEnvironment).chain_height ≤
      (env_chain to_.toEnvironment).chain_height := by
  obtain ⟨_, ⟨t⟩⟩ := h
  exact trace_chain_height_le t

theorem reachable_through_current_slot
    (frm to_ : @ChainState Base) (h : reachable_through frm to_) :
    (env_chain frm.toEnvironment).current_slot ≤
      (env_chain to_.toEnvironment).current_slot := by
  obtain ⟨_, ⟨t⟩⟩ := h
  exact trace_current_slot_le t

theorem reachable_through_finalized_height
    (frm to_ : @ChainState Base) (h : reachable_through frm to_) :
    (env_chain frm.toEnvironment).finalized_height ≤
      (env_chain to_.toEnvironment).finalized_height := by
  obtain ⟨_, ⟨t⟩⟩ := h
  exact trace_finalized_height_le t

/-! ### Misc -/

theorem outgoing_acts_after_block_nil
    (bstate : @ChainState Base) (addr : Base.Address)
    (hall : bstate.chain_state_queue.Forall act_is_from_account)
    (h_contract : Base.address_is_contract addr = true) :
    outgoing_acts bstate addr = [] := by
  unfold outgoing_acts
  suffices hf : bstate.chain_state_queue.filter
      (fun act => Base.address_eqb act.act_from addr) = [] by
    rw [hf]; rfl
  apply ConCert.Utils.Extras.Forall_false_filter_nil
  rw [← ConCert.Utils.Extras.All_Forall] at hall ⊢
  apply ConCert.Utils.Extras.All_ext_in _ _ _ hall
  intro a _ hfrom
  unfold act_is_from_account at hfrom
  have hne : a.act_from ≠ addr := by
    intro heq
    rw [heq, h_contract] at hfrom
    cases hfrom
  exact Address.address_eq_ne _ _ hne

theorem outgoing_acts_after_deploy_nil
    (bstate : @ChainState Base) (addr : Base.Address)
    (h : bstate.chain_state_queue.Forall
          (fun act => Base.address_eqb act.act_from addr = false)) :
    outgoing_acts bstate addr = [] := by
  unfold outgoing_acts
  suffices hf : bstate.chain_state_queue.filter
      (fun act => Base.address_eqb act.act_from addr) = [] by
    rw [hf]; rfl
  -- All queue elements fail the filter predicate, so filter returns [].
  have lift : ∀ {P : @Action Base → Prop} {l : List (@Action Base)},
      l.Forall P → (∀ a ∈ l, P a) := by
    intro P l hP a ha
    induction l with
    | nil => cases ha
    | cons hd tl ih =>
      match tl, hP with
      | [], hP =>
        rw [List.mem_singleton] at ha; subst ha; exact hP
      | hd' :: tl', ⟨hhd, htl⟩ =>
        rw [List.mem_cons] at ha
        cases ha with
        | inl heq => subst heq; exact hhd
        | inr hx => exact ih htl hx
  apply List.filter_eq_nil_iff.mpr
  intro a ha hb
  have hne := lift h a ha
  rw [hne] at hb
  exact Bool.false_ne_true hb

end ConCert.Execution.BlockchainTheories
