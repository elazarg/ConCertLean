/- Port of execution/theories/BlockchainTheories.v
   All contents are lemmas/theorems; axiomatized here. -/

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

axiom account_balance_post :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (addr : Base.Address),
    post.env_account_balances addr =
      pre.env_account_balances addr
      + (if Base.address_eqb addr (ActionEvaluation.eval_to eval)
         then ActionEvaluation.eval_amount eval else 0)
      - (if Base.address_eqb addr (ActionEvaluation.eval_from eval)
         then ActionEvaluation.eval_amount eval else 0)

axiom account_balance_post_to :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts),
    ActionEvaluation.eval_from eval ≠ ActionEvaluation.eval_to eval →
    post.env_account_balances (ActionEvaluation.eval_to eval) =
      pre.env_account_balances (ActionEvaluation.eval_to eval) +
        ActionEvaluation.eval_amount eval

axiom account_balance_post_from :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts),
    ActionEvaluation.eval_from eval ≠ ActionEvaluation.eval_to eval →
    post.env_account_balances (ActionEvaluation.eval_from eval) =
      pre.env_account_balances (ActionEvaluation.eval_from eval) -
        ActionEvaluation.eval_amount eval

axiom account_balance_post_irrelevant :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts)
    (addr : Base.Address),
    addr ≠ ActionEvaluation.eval_from eval →
    addr ≠ ActionEvaluation.eval_to eval →
    post.env_account_balances addr = pre.env_account_balances addr

axiom chain_height_post_action :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (_eval : ActionEvaluation pre act post new_acts),
    (env_chain post).chain_height = (env_chain pre).chain_height

axiom current_slot_post_action :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (_eval : ActionEvaluation pre act post new_acts),
    (env_chain post).current_slot = (env_chain pre).current_slot

axiom finalized_height_post_action :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (_eval : ActionEvaluation pre act post new_acts),
    (env_chain post).finalized_height = (env_chain pre).finalized_height

axiom contracts_post_pre_none :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (_eval : ActionEvaluation pre act post new_acts)
    (contract : Base.Address),
    post.env_contracts contract = none → pre.env_contracts contract = none

axiom eval_amount_nonnegative :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts),
    ActionEvaluation.eval_amount eval ≥ 0

axiom eval_amount_le_account_balance :
  ∀ {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)} (eval : ActionEvaluation pre act post new_acts),
    ActionEvaluation.eval_amount eval ≤
      pre.env_account_balances (ActionEvaluation.eval_from eval)

/-! ### Init / receive facts -/

axiom wc_init_strong :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : SerializedValue} {res : SerializedValue},
    wc_init (contract_to_weak_contract contract) chain ctx setup = Ok res →
    ∃ setup_strong result_strong,
      deserialize setup = some setup_strong ∧
      serialize result_strong = res ∧
      contract.init chain ctx setup_strong = Ok result_strong

axiom wc_receive_strong :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state : SerializedValue} {msg : Option SerializedValue}
    {new_state : SerializedValue} {new_acts : List (@ActionBody Base)},
    wc_receive (contract_to_weak_contract contract) chain ctx prev_state msg =
      Ok (new_state, new_acts) →
    ∃ prev_state_strong msg_strong new_state_strong,
      deserialize prev_state = some prev_state_strong ∧
      (match msg_strong with
       | some m => (msg >>= deserialize) = some m
       | none => msg = none) ∧
      serialize new_state_strong = new_state ∧
      contract.receive chain ctx prev_state_strong msg_strong =
        Ok (new_state_strong, new_acts)

axiom wc_receive_to_receive :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    chain cctx (cstate : State) (msg : Msg) (new_cstate : State)
    (new_acts : List (@ActionBody Base)),
    contract.receive chain cctx cstate (some msg) = Ok (new_cstate, new_acts) ↔
    wc_receive (contract_to_weak_contract contract) chain cctx
      (serialize cstate) (some (serialize msg)) =
      Ok (serialize new_cstate, new_acts)

axiom wc_init_to_init :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    chain cctx (setup : Setup) (state : State),
    contract.init chain cctx setup = Ok state ↔
    wc_init (contract_to_weak_contract contract) chain cctx (serialize setup) =
      Ok (serialize state)

/-! ### Reachability facts -/

axiom trace_reachable :
  ∀ {to_ : @ChainState Base}, ChainTrace empty_state to_ → reachable to_

axiom reachable_empty_state : reachable (@empty_state Base)

axiom reachable_trans :
  ∀ {frm to_ : @ChainState Base},
    reachable frm → Nonempty (ChainTrace frm to_) → reachable to_

axiom reachable_step :
  ∀ {frm to_ : @ChainState Base},
    reachable frm → ChainStep frm to_ → reachable to_

axiom reachable_through_refl :
  ∀ (bstate : @ChainState Base), reachable bstate → reachable_through bstate bstate

axiom reachable_through_trans' :
  ∀ (frm mid to_ : @ChainState Base),
    reachable_through frm mid → ChainStep mid to_ → reachable_through frm to_

axiom reachable_through_trans :
  ∀ (frm mid to_ : @ChainState Base),
    reachable_through frm mid → reachable_through mid to_ → reachable_through frm to_

axiom reachable_through_step :
  ∀ (frm to_ : @ChainState Base),
    reachable frm → ChainStep frm to_ → reachable_through frm to_

axiom reachable_through_reachable :
  ∀ (frm to_ : @ChainState Base),
    reachable_through frm to_ → reachable to_

/-- Chains a "future state from `mid`" existential through to a future
    from `frm`, matching `BlockchainTheories.v:323`. -/
axiom step_reachable_through_exists :
  ∀ (frm mid : @ChainState Base) (P : @ChainState Base → Prop),
    reachable_through frm mid →
    (∃ to_, reachable_through mid to_ ∧ P to_) →
    ∃ to_, reachable_through frm to_ ∧ P to_

/-! ### Trace facts (selected) -/

axiom contract_addr_format :
  ∀ {to_ : @ChainState Base} (addr : Base.Address) (wc : @WeakContract Base),
    reachable to_ → to_.env_contracts addr = some wc →
    Base.address_is_contract addr = true

/-- If `new_acts` is the result of mapping `resp_acts` to actions from
    `addr2`, and `addr1 ≠ addr2`, then no element of `new_acts` is from
    `addr1`. -/
axiom new_acts_no_out_queue :
  ∀ (orig addr1 addr2 : Base.Address)
    (new_acts : List (@Action Base)) (resp_acts : List (@ActionBody Base)),
    addr1 ≠ addr2 →
    new_acts = resp_acts.map
      (fun b => { act_origin := orig, act_from := addr2, act_body := b }) →
    new_acts.Forall (fun a => Base.address_eqb a.act_from addr1 = false)

axiom undeployed_contract_no_out_queue :
  ∀ (contract : Base.Address) (state : @ChainState Base),
    reachable state →
    Base.address_is_contract contract = true →
    state.env_contracts contract = none →
    state.chain_state_queue.Forall
      (fun a => Base.address_eqb a.act_from contract = false)

axiom undeployed_contract_no_out_txs :
  ∀ (contract : Base.Address) {frm to_ : @ChainState Base} (trace : ChainTrace frm to_),
    Base.address_is_contract contract = true →
    to_.env_contracts contract = none →
    outgoing_txs trace contract = []

axiom undeployed_contract_no_in_txs :
  ∀ (contract : Base.Address) {frm to_ : @ChainState Base} (trace : ChainTrace frm to_),
    Base.address_is_contract contract = true →
    to_.env_contracts contract = none →
    incoming_txs trace contract = []

/-- Coq direction: if a setup-deserialization yielded a deployment, then
    the contract is deployed. The reverse is *not* true: the contract may
    have been deployed with a different setup type, in which case
    `deserialize`-as-`Setup` fails and `deployment_info` returns `none`. -/
axiom deployment_info_some :
  ∀ (Setup : Type) [Serializable Setup]
    {to_ : @ChainState Base} (trace : ChainTrace empty_state to_)
    (caddr : Base.Address),
    deployment_info Setup trace caddr ≠ none →
    to_.env_contracts caddr ≠ none

axiom deployment_info_addr_format :
  ∀ (Setup : Type) [Serializable Setup]
    {to_ : @ChainState Base} (trace : ChainTrace empty_state to_)
    (addr : Base.Address) (dep : @DeploymentInfo Base Setup),
    deployment_info Setup trace addr = some dep →
    Base.address_is_contract addr = true

axiom incoming_txs_contract :
  ∀ (caddr : Base.Address) (bstate : @ChainState Base)
    (trace : ChainTrace empty_state bstate)
    (Setup : Type) [Serializable Setup] (depinfo : @DeploymentInfo Base Setup)
    (Msg : Type) [Serializable Msg] (msgs : List (@ContractCallInfo Base Msg)),
    deployment_info Setup trace caddr = some depinfo →
    incoming_calls Msg trace caddr = some msgs →
    (incoming_txs trace caddr).map (fun tx => (tx.tx_from, tx.tx_to, tx.tx_amount)) =
      msgs.map (fun call => (call.call_from, caddr, call.call_amount))
      ++ [(depinfo.deployment_from, caddr, depinfo.deployment_amount)]

axiom undeployed_contract_no_in_calls :
  ∀ {Msg : Type} [Serializable Msg]
    (contract : Base.Address) {frm to_ : @ChainState Base} (trace : ChainTrace frm to_),
    Base.address_is_contract contract = true →
    to_.env_contracts contract = none →
    incoming_calls Msg trace contract = some []

axiom account_balance_trace :
  ∀ (state : @ChainState Base) (trace : ChainTrace empty_state state) (addr : Base.Address),
    state.env_account_balances addr =
      ConCert.Utils.Extras.sumZ (fun tx => tx.tx_amount) (incoming_txs trace addr)
      + ConCert.Utils.Extras.sumZ (fun b => b.block_reward) (created_blocks trace addr)
      - ConCert.Utils.Extras.sumZ (fun tx => tx.tx_amount) (outgoing_txs trace addr)

axiom contract_no_created_blocks :
  ∀ (state : @ChainState Base) (addr : Base.Address) {frm : @ChainState Base}
    (trace : ChainTrace frm state),
    Base.address_is_contract addr = true →
    created_blocks trace addr = []

axiom undeployed_contract_balance_0 :
  ∀ (state : @ChainState Base) (addr : Base.Address),
    reachable state →
    Base.address_is_contract addr = true →
    state.env_contracts addr = none →
    state.env_account_balances addr = 0

axiom account_balance_nonnegative :
  ∀ (state : @ChainState Base) (addr : Base.Address),
    reachable state → state.env_account_balances addr ≥ 0

axiom deployed_contract_state_typed :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    {bstate : @ChainState Base} (caddr : Base.Address),
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    reachable bstate →
    ∃ cstate, @contract_state Base State _ bstate.toEnvironment caddr = some cstate

axiom origin_is_always_account :
  ∀ {bstate : @ChainState Base},
    reachable bstate →
    bstate.chain_state_queue.Forall act_origin_is_account

axiom finalized_heigh_chain_height :
  ∀ (bstate : @ChainState Base),
    reachable bstate →
    (env_chain bstate.toEnvironment).finalized_height <
      (env_chain bstate.toEnvironment).chain_height + 1

axiom contract_states_deployed :
  ∀ (to_ : @ChainState Base) (addr : Base.Address) (state : SerializedValue),
    reachable to_ →
    to_.env_contract_states addr = some state →
    ∃ wc, to_.env_contracts addr = some wc

axiom contract_states_addr_format :
  ∀ (to_ : @ChainState Base) (addr : Base.Address) (state : SerializedValue),
    reachable to_ →
    to_.env_contract_states addr = some state →
    Base.address_is_contract addr = true

axiom deployment_amount_nonnegative :
  ∀ {Setup : Type} [Serializable Setup]
    {to_ : @ChainState Base} (trace : ChainTrace empty_state to_)
    (caddr : Base.Address) (dep : @DeploymentInfo Base Setup),
    deployment_info Setup trace caddr = some dep → dep.deployment_amount ≥ 0

axiom origin_user_address :
  ∀ (bstate : @ChainState Base),
    reachable bstate →
    bstate.chain_state_queue.Forall act_origin_is_account

axiom current_slot_chain_height :
  ∀ (bstate : @ChainState Base),
    reachable bstate →
    (env_chain bstate.toEnvironment).chain_height ≤
      (env_chain bstate.toEnvironment).current_slot

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

axiom context_valid :
  ∀ (bstate : @ChainState Base) (trace : ChainTrace empty_state bstate),
    context_valid' trace

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

axiom chain_valid :
  ∀ (bstate : @ChainState Base) (trace : ChainTrace empty_state bstate),
    chain_valid' trace

/-! ### Reachable-through facts -/

axiom reachable_through_contract_deployed :
  ∀ (frm to_ : @ChainState Base) (addr : Base.Address) (wc : @WeakContract Base),
    reachable_through frm to_ →
    frm.env_contracts addr = some wc →
    to_.env_contracts addr = some wc

axiom reachable_through_contract_state :
  ∀ (frm to_ : @ChainState Base) (addr : Base.Address) (cstate : SerializedValue),
    reachable_through frm to_ →
    frm.env_contract_states addr = some cstate →
    ∃ cstate', to_.env_contract_states addr = some cstate'

axiom reachable_through_chain_height :
  ∀ (frm to_ : @ChainState Base),
    reachable_through frm to_ →
    (env_chain frm.toEnvironment).chain_height ≤
      (env_chain to_.toEnvironment).chain_height

axiom reachable_through_current_slot :
  ∀ (frm to_ : @ChainState Base),
    reachable_through frm to_ →
    (env_chain frm.toEnvironment).current_slot ≤
      (env_chain to_.toEnvironment).current_slot

axiom reachable_through_finalized_height :
  ∀ (frm to_ : @ChainState Base),
    reachable_through frm to_ →
    (env_chain frm.toEnvironment).finalized_height ≤
      (env_chain to_.toEnvironment).finalized_height

/-! ### Misc -/

axiom outgoing_acts_after_block_nil :
  ∀ (bstate : @ChainState Base) (addr : Base.Address),
    bstate.chain_state_queue.Forall act_is_from_account →
    Base.address_is_contract addr = true →
    outgoing_acts bstate addr = []

axiom outgoing_acts_after_deploy_nil :
  ∀ (bstate : @ChainState Base) (addr : Base.Address),
    bstate.chain_state_queue.Forall (fun act => Base.address_eqb act.act_from addr = false) →
    outgoing_acts bstate addr = []

end ConCert.Execution.BlockchainTheories
