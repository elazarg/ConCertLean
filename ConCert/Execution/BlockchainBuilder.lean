/- Port of execution/theories/BlockchainBuilder.v -/

import ConCert.Execution.ChainedList
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.Finite
import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories

namespace ConCert.Execution.BlockchainBuilder

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.ChainedList
open ConCert.Execution.Finite

variable [Base : ChainBase]

inductive ActionEvaluationError where
  | amount_negative (amount : Amount)
  | amount_too_high (amount : Amount)
  | no_such_contract (addr : Base.Address)
  | too_many_contracts
  | init_failed (err : SerializedValue)
  | receive_failed (err : SerializedValue)
  | deserialization_failed (val : SerializedValue)
  | internal_error

inductive AddBlockError where
  | invalid_header (header : @BlockHeader Base)
  | invalid_root_action (act : @Action Base)
  | origin_from_mismatch (act : @Action Base)
  | action_evaluation_depth_exceeded
  | action_evaluation_error (act : @Action Base) (err : @ActionEvaluationError Base)

class ChainBuilderType where
  builder_type : Type
  builder_initial : builder_type
  builder_env : builder_type → @Environment Base
  builder_add_block :
    builder_type → @BlockHeader Base → List (@Action Base) →
    Result builder_type (@AddBlockError Base)
  builder_trace :
    ∀ (b : builder_type),
      ChainTrace (@empty_state Base)
        { toEnvironment := builder_env b, chain_state_queue := [] }

namespace BuildUtils

def receiver_can_receive_transfer (bstate : @ChainState Base) (act_body : @ActionBody Base) : Prop :=
  match act_body with
  | .act_transfer to_ _ =>
      Base.address_is_contract to_ = false ∨
      (∃ wc state,
        bstate.env_contracts to_ = some wc ∧
        bstate.env_contract_states to_ = some state ∧
        ∀ (bstate_new : @ChainState Base) (ctx : @ContractCallContext Base),
          ∃ new_state,
            wc_receive wc bstate_new.toEnvironment.toChain ctx state none = Ok (new_state, []))
  | _ => True

/-- A candidate fresh contract address at which deployment initialization
    succeeds. This isolates the only non-structural search assumption needed by
    the generic builder decidability proof. -/
abbrev DeployableAddressCandidate
    (bstate : @ChainState Base) (wc : @WeakContract Base)
    (setup : SerializedValue) (act_origin act_from : Base.Address)
    (amount : Amount) (addr : Base.Address) (state : SerializedValue) : Prop :=
  Base.address_is_contract addr = true ∧
  bstate.env_contracts addr = none ∧
  wc_init wc
    (transfer_balance act_from addr amount bstate.toEnvironment).toChain
    { ctx_origin := act_origin, ctx_from := act_from,
      ctx_contract_address := addr,
      ctx_contract_balance := amount, ctx_amount := amount }
    setup = .Ok state

/-- The deploy search proposition: there exists some fresh contract address at
    which deployment initialization succeeds. -/
abbrev DeployableAddressExists
    (bstate : @ChainState Base) (wc : @WeakContract Base)
    (setup : SerializedValue) (act_origin act_from : Base.Address)
    (amount : Amount) : Prop :=
  ∃ addr state,
    DeployableAddressCandidate bstate wc setup act_origin act_from amount addr state

/-- Assumption required by the generic blockchain builder: deployability of a
    weak contract at some fresh address must be decidable in reachable states.

    Concrete builders can discharge this by exposing a finite fresh-address
    search. The generic `ChainBase` interface alone does not provide enough
    structure to prove it. -/
abbrev DeployableAddressDecidableAssumption : Prop :=
  ∀ (bstate : @ChainState Base) (wc : @WeakContract Base)
    (setup : SerializedValue) (act_origin act_from : Base.Address)
    (amount : Amount),
    reachable bstate →
    DeployableAddressExists bstate wc setup act_origin act_from amount ∨
    ¬ DeployableAddressExists bstate wc setup act_origin act_from amount

/-- Prop-level deployability decision.

    The upstream Rocq development states this as an axiom. In Lean this
    statement lives in `Prop`, so standard classical excluded middle discharges
    it without a project-specific axiom. Executable fresh-address search is
    still available separately as `deployable_address_decidable_of_finite`. -/
theorem deployable_address_decidable :
    DeployableAddressDecidableAssumption (Base := Base) := by
  intro bstate wc setup act_origin act_from amount _reachable
  exact Classical.em
    (DeployableAddressExists bstate wc setup act_origin act_from amount)

def deployable_address_candidate_result
    (bstate : @ChainState Base) (wc : @WeakContract Base)
    (setup : SerializedValue) (act_origin act_from : Base.Address)
    (amount : Amount) (addr : Base.Address) : Option SerializedValue :=
  if Base.address_is_contract addr = true then
    match bstate.env_contracts addr with
    | none =>
        match wc_init wc
            (transfer_balance act_from addr amount bstate.toEnvironment).toChain
            { ctx_origin := act_origin, ctx_from := act_from,
              ctx_contract_address := addr,
              ctx_contract_balance := amount, ctx_amount := amount }
            setup with
        | .Ok state => some state
        | .Err _ => none
    | some _ => none
  else
    none

theorem deployable_address_candidate_result_some
    {bstate : @ChainState Base} {wc : @WeakContract Base}
    {setup : SerializedValue} {act_origin act_from : Base.Address}
    {amount : Amount} {addr : Base.Address} {state : SerializedValue} :
    deployable_address_candidate_result bstate wc setup act_origin act_from amount addr =
      some state →
    DeployableAddressCandidate bstate wc setup act_origin act_from amount addr state := by
  intro h
  unfold deployable_address_candidate_result at h
  split at h
  · rename_i hcontract
    cases hcontracts : bstate.env_contracts addr with
    | some old =>
        simp [hcontracts] at h
    | none =>
        simp [hcontracts] at h
        cases hinit :
            wc_init wc
              (transfer_balance act_from addr amount bstate.toEnvironment).toChain
              { ctx_origin := act_origin, ctx_from := act_from,
                ctx_contract_address := addr,
                ctx_contract_balance := amount, ctx_amount := amount }
              setup with
        | Ok st =>
            simp [hinit] at h
            cases h
            exact ⟨hcontract, hcontracts, hinit⟩
        | Err err =>
            simp [hinit] at h
  · simp at h

theorem deployable_address_candidate_result_none
    {bstate : @ChainState Base} {wc : @WeakContract Base}
    {setup : SerializedValue} {act_origin act_from : Base.Address}
    {amount : Amount} {addr : Base.Address} :
    deployable_address_candidate_result bstate wc setup act_origin act_from amount addr = none →
    ¬ ∃ state,
      DeployableAddressCandidate bstate wc setup act_origin act_from amount addr state := by
  intro hnone
  rintro ⟨state, hcontract, hcontracts, hinit⟩
  unfold deployable_address_candidate_result at hnone
  simp [hcontract, hcontracts, hinit] at hnone

def find_deployable_address_in
    (addrs : List Base.Address)
    (bstate : @ChainState Base) (wc : @WeakContract Base)
    (setup : SerializedValue) (act_origin act_from : Base.Address)
    (amount : Amount) : Option (Base.Address × SerializedValue) :=
  match addrs with
  | [] => none
  | addr :: rest =>
      match deployable_address_candidate_result
          bstate wc setup act_origin act_from amount addr with
      | some state => some (addr, state)
      | none =>
          find_deployable_address_in rest bstate wc setup act_origin act_from amount

theorem find_deployable_address_in_sound
    {addrs : List Base.Address}
    {bstate : @ChainState Base} {wc : @WeakContract Base}
    {setup : SerializedValue} {act_origin act_from : Base.Address}
    {amount : Amount} {addr : Base.Address} {state : SerializedValue} :
    find_deployable_address_in addrs bstate wc setup act_origin act_from amount =
      some (addr, state) →
    DeployableAddressCandidate bstate wc setup act_origin act_from amount addr state := by
  induction addrs with
  | nil =>
      intro h
      simp [find_deployable_address_in] at h
  | cons hd tl ih =>
      intro h
      unfold find_deployable_address_in at h
      cases hcand :
          deployable_address_candidate_result bstate wc setup act_origin act_from amount hd with
      | some st =>
          have hpair : (hd, st) = (addr, state) := by
            simpa [hcand] using h
          have haddr : hd = addr := congrArg Prod.fst hpair
          have hstate : st = state := congrArg Prod.snd hpair
          subst addr
          subst state
          exact deployable_address_candidate_result_some hcand
      | none =>
          simp [hcand] at h
          exact ih h

theorem find_deployable_address_in_none
    {addrs : List Base.Address}
    {bstate : @ChainState Base} {wc : @WeakContract Base}
    {setup : SerializedValue} {act_origin act_from : Base.Address}
    {amount : Amount} :
    find_deployable_address_in addrs bstate wc setup act_origin act_from amount = none →
    ∀ addr, addr ∈ addrs →
      ¬ ∃ state,
        DeployableAddressCandidate bstate wc setup act_origin act_from amount addr state := by
  induction addrs with
  | nil =>
      intro _ addr hin
      cases hin
  | cons hd tl ih =>
      intro hfind addr hin
      unfold find_deployable_address_in at hfind
      cases hcand :
          deployable_address_candidate_result bstate wc setup act_origin act_from amount hd with
      | some st =>
          simp [hcand] at hfind
      | none =>
          simp [hcand] at hfind
          cases hin with
          | head =>
              exact deployable_address_candidate_result_none hcand
          | tail _ hmem =>
              exact ih hfind addr hmem

theorem deployable_address_decidable_of_finite [Finite Base.Address] :
    DeployableAddressDecidableAssumption (Base := Base) := by
  intro bstate wc setup act_origin act_from amount _reachable
  cases hfind :
      find_deployable_address_in (Finite.elements (T := Base.Address))
        bstate wc setup act_origin act_from amount with
  | some pair =>
      rcases pair with ⟨addr, state⟩
      left
      exact ⟨addr, state, find_deployable_address_in_sound hfind⟩
  | none =>
      right
      rintro ⟨addr, state, hcand⟩
      have hno := find_deployable_address_in_none hfind addr (Finite.elements_all addr)
      exact hno ⟨state, hcand⟩

private theorem action_evaluation_amount_nonnegative
    {env new_env : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (eval : ActionEvaluation env act new_env new_acts) :
    act_body_amount act.act_body ≥ 0 := by
  cases eval with
  | eval_transfer _ _ _ _ hamount _ _ hact _ _ =>
      cases hact
      simpa [act_body_amount] using hamount
  | eval_deploy _ _ _ _ _ _ _ hamount _ _ _ hact _ _ _ =>
      cases hact
      simpa [act_body_amount] using hamount
  | eval_call _ _ _ _ _ msg _ _ _ hamount _ _ _ hact _ _ _ =>
      cases msg <;> cases hact <;> simpa [act_body_amount] using hamount

private theorem action_evaluation_amount_le_account_balance
    {env new_env : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (eval : ActionEvaluation env act new_env new_acts) :
    act_body_amount act.act_body ≤ env.env_account_balances act.act_from := by
  cases eval with
  | eval_transfer _ _ _ _ _ hbalance _ hact _ _ =>
      cases hact
      simpa [act_body_amount] using hbalance
  | eval_deploy _ _ _ _ _ _ _ _ hbalance _ _ hact _ _ _ =>
      cases hact
      simpa [act_body_amount] using hbalance
  | eval_call _ _ _ _ _ msg _ _ _ _ hbalance _ _ hact _ _ _ =>
      cases msg <;> cases hact <;> simpa [act_body_amount] using hbalance

/-- For any reachable state and an action it is decidable if the action can
    be evaluated in that state. This follows the original Coq proof: split on
    the action shape and evaluator preconditions, using
    `deployable_address_decidable` only for fresh deploy addresses. -/
theorem action_evaluation_decidable_of_deployable_address_decidable
    (hdeploy_decidable : DeployableAddressDecidableAssumption (Base := Base)) :
  ∀ (bstate : @ChainState Base) (act : @Action Base),
    reachable bstate →
    (∃ bstate' new_acts, Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts))
    ∨ ¬ ∃ bstate' new_acts, Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts) := by
  intro bstate act h_reach
  cases act with
  | mk act_origin act_from act_body =>
      cases act_body with
      | act_transfer to_addr amount =>
          by_cases hamount : amount ≥ 0
          · by_cases hbalance : amount ≤ bstate.env_account_balances act_from
            · by_cases hto_contract : Base.address_is_contract to_addr = true
              · cases hcontract : bstate.env_contracts to_addr with
                | none =>
                    right
                    rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                    cases eval with
                    | eval_transfer _ _ _ _ _ _ hnot_contract hact _ _ =>
                        cases hact
                        rw [hto_contract] at hnot_contract
                        cases hnot_contract
                    | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                        cases hact
                    | eval_call _ _ _ _ wc msg _ _ _ _ _ hdeployed _ hact _ _ _ =>
                        cases msg
                        · cases hact
                          rw [hcontract] at hdeployed
                          cases hdeployed
                        · cases hact
                | some wc =>
                    cases hstate : bstate.env_contract_states to_addr with
                    | none =>
                        right
                        rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                        cases eval with
                        | eval_transfer _ _ _ _ _ _ hnot_contract hact _ _ =>
                            cases hact
                            rw [hto_contract] at hnot_contract
                            cases hnot_contract
                        | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                            cases hact
                        | eval_call _ _ _ _ wc' msg prev_state _ _ _ _ _ hstate' hact _ _ _ =>
                            cases msg
                            · cases hact
                              rw [hstate] at hstate'
                              cases hstate'
                            · cases hact
                    | some prev_state =>
                        let call_balance :=
                          (transfer_balance act_from to_addr amount bstate.toEnvironment).env_account_balances to_addr
                        cases hreceive :
                            wc_receive wc
                              (transfer_balance act_from to_addr amount bstate.toEnvironment).toChain
                              { ctx_origin := act_origin, ctx_from := act_from,
                                ctx_contract_address := to_addr,
                                ctx_contract_balance := call_balance,
                                ctx_amount := amount }
                              prev_state none with
                        | Ok result =>
                            obtain ⟨new_state, resp_acts⟩ := result
                            let new_env :=
                              set_contract_state to_addr new_state
                                (transfer_balance act_from to_addr amount bstate.toEnvironment)
                            let produced : List (@Action Base) :=
                              resp_acts.map (fun b =>
                                { act_origin := act_origin, act_from := to_addr, act_body := b })
                            left
                            refine ⟨new_env, produced, ⟨?_⟩⟩
                            apply ActionEvaluation.eval_call act_origin act_from to_addr amount wc none
                              prev_state new_state resp_acts hamount hbalance
                            · exact hcontract
                            · exact hstate
                            · rfl
                            · simpa [new_env, call_balance, set_contract_state] using hreceive
                            · rfl
                            · exact environment_equiv_refl _
                        | Err err =>
                            right
                            rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                            cases eval with
                            | eval_transfer _ _ _ _ _ _ hnot_contract hact _ _ =>
                                cases hact
                                rw [hto_contract] at hnot_contract
                                cases hnot_contract
                            | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                                cases hact
                            | eval_call _ _ _ _ wc' msg prev_state' new_state' resp_acts' _ _ hcontract' hstate' hact hreceive' _ henv' =>
                                cases msg
                                · cases hact
                                  rw [hcontract] at hcontract'
                                  cases hcontract'
                                  rw [hstate] at hstate'
                                  cases hstate'
                                  have hbal_ctx :
                                      new_env.env_account_balances to_addr = call_balance := by
                                    rw [henv'.account_balances_eq to_addr]
                                    simp [set_contract_state, call_balance]
                                  have hreceive_same :
                                      wc_receive wc
                                        (transfer_balance act_from to_addr amount
                                          bstate.toEnvironment).toChain
                                        { ctx_origin := act_origin, ctx_from := act_from,
                                          ctx_contract_address := to_addr,
                                          ctx_contract_balance := call_balance,
                                          ctx_amount := amount }
                                        prev_state none =
                                      .Ok (new_state', resp_acts') := by
                                    simpa [hbal_ctx, call_balance] using hreceive'
                                  rw [hreceive] at hreceive_same
                                  cases hreceive_same
                                · cases hact
              · left
                refine ⟨transfer_balance act_from to_addr amount bstate.toEnvironment, [], ⟨?_⟩⟩
                exact ActionEvaluation.eval_transfer act_origin act_from to_addr amount
                  hamount hbalance (by simpa using hto_contract) rfl
                  (environment_equiv_refl _) rfl
            · right
              rintro ⟨new_env, new_acts, ⟨eval⟩⟩
              have hle := action_evaluation_amount_le_account_balance eval
              simp [act_body_amount] at hle
              exact hbalance hle
          · right
            rintro ⟨new_env, new_acts, ⟨eval⟩⟩
            have hnonneg := action_evaluation_amount_nonnegative eval
            simp [act_body_amount] at hnonneg
            exact hamount hnonneg
      | act_call to_addr amount msg_ser =>
          by_cases hamount : amount ≥ 0
          · by_cases hbalance : amount ≤ bstate.env_account_balances act_from
            · by_cases hto_contract : Base.address_is_contract to_addr = true
              · cases hcontract : bstate.env_contracts to_addr with
                | none =>
                    right
                    rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                    cases eval with
                    | eval_transfer _ _ _ _ _ _ _ hact _ _ =>
                        cases hact
                    | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                        cases hact
                    | eval_call _ _ _ _ wc msg _ _ _ _ _ hdeployed _ hact _ _ _ =>
                        cases msg
                        · cases hact
                        · cases hact
                          rw [hcontract] at hdeployed
                          cases hdeployed
                | some wc =>
                    cases hstate : bstate.env_contract_states to_addr with
                    | none =>
                        right
                        rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                        cases eval with
                        | eval_transfer _ _ _ _ _ _ _ hact _ _ =>
                            cases hact
                        | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                            cases hact
                        | eval_call _ _ _ _ wc' msg prev_state _ _ _ _ _ hstate' hact _ _ _ =>
                            cases msg
                            · cases hact
                            · cases hact
                              rw [hstate] at hstate'
                              cases hstate'
                    | some prev_state =>
                        let call_balance :=
                          (transfer_balance act_from to_addr amount bstate.toEnvironment).env_account_balances to_addr
                        cases hreceive :
                            wc_receive wc
                              (transfer_balance act_from to_addr amount bstate.toEnvironment).toChain
                              { ctx_origin := act_origin, ctx_from := act_from,
                                ctx_contract_address := to_addr,
                                ctx_contract_balance := call_balance,
                                ctx_amount := amount }
                              prev_state (some msg_ser) with
                        | Ok result =>
                            obtain ⟨new_state, resp_acts⟩ := result
                            let new_env :=
                              set_contract_state to_addr new_state
                                (transfer_balance act_from to_addr amount bstate.toEnvironment)
                            let produced : List (@Action Base) :=
                              resp_acts.map (fun b =>
                                { act_origin := act_origin, act_from := to_addr, act_body := b })
                            left
                            refine ⟨new_env, produced, ⟨?_⟩⟩
                            apply ActionEvaluation.eval_call act_origin act_from to_addr amount wc
                              (some msg_ser) prev_state new_state resp_acts hamount hbalance
                            · exact hcontract
                            · exact hstate
                            · rfl
                            · simpa [new_env, call_balance, set_contract_state] using hreceive
                            · rfl
                            · exact environment_equiv_refl _
                        | Err err =>
                            right
                            rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                            cases eval with
                            | eval_transfer _ _ _ _ _ _ _ hact _ _ =>
                                cases hact
                            | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                                cases hact
                            | eval_call _ _ _ _ wc' msg prev_state' new_state' resp_acts' _ _ hcontract' hstate' hact hreceive' _ henv' =>
                                cases msg
                                · cases hact
                                · cases hact
                                  rw [hcontract] at hcontract'
                                  cases hcontract'
                                  rw [hstate] at hstate'
                                  cases hstate'
                                  have hbal_ctx :
                                      new_env.env_account_balances to_addr = call_balance := by
                                    rw [henv'.account_balances_eq to_addr]
                                    simp [set_contract_state, call_balance]
                                  have hreceive_same :
                                      wc_receive wc
                                        (transfer_balance act_from to_addr amount
                                          bstate.toEnvironment).toChain
                                        { ctx_origin := act_origin, ctx_from := act_from,
                                          ctx_contract_address := to_addr,
                                          ctx_contract_balance := call_balance,
                                          ctx_amount := amount }
                                        prev_state (some msg_ser) =
                                      .Ok (new_state', resp_acts') := by
                                    simpa [hbal_ctx, call_balance] using hreceive'
                                  rw [hreceive] at hreceive_same
                                  cases hreceive_same
              · right
                rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                cases eval with
                | eval_transfer _ _ _ _ _ _ _ hact _ _ =>
                    cases hact
                | eval_deploy _ _ _ _ _ _ _ _ _ _ _ hact _ _ _ =>
                    cases hact
                | eval_call _ _ _ _ wc msg _ _ _ _ _ hcontract _ hact _ _ _ =>
                    cases msg
                    · cases hact
                    · cases hact
                      have hto_contract' : Base.address_is_contract to_addr = true :=
                        contract_addr_format to_addr wc h_reach hcontract
                      exact hto_contract hto_contract'
            · right
              rintro ⟨new_env, new_acts, ⟨eval⟩⟩
              have hle := action_evaluation_amount_le_account_balance eval
              simp [act_body_amount] at hle
              exact hbalance hle
          · right
            rintro ⟨new_env, new_acts, ⟨eval⟩⟩
            have hnonneg := action_evaluation_amount_nonnegative eval
            simp [act_body_amount] at hnonneg
            exact hamount hnonneg
      | act_deploy amount wc setup =>
          by_cases hamount : amount ≥ 0
          · by_cases hbalance : amount ≤ bstate.env_account_balances act_from
            · cases hdeploy_decidable bstate wc setup act_origin act_from amount h_reach with
              | inl hdeploy =>
                  obtain ⟨to_addr, state, hto_contract, hnot_deployed, hinit⟩ := hdeploy
                  let new_env :=
                    set_contract_state to_addr state
                      (add_contract to_addr wc
                        (transfer_balance act_from to_addr amount bstate.toEnvironment))
                  left
                  refine ⟨new_env, [], ⟨?_⟩⟩
                  exact ActionEvaluation.eval_deploy act_origin act_from to_addr amount wc setup state
                    hamount hbalance hto_contract hnot_deployed rfl hinit
                    (environment_equiv_refl _) rfl
              | inr hno_deploy =>
                  right
                  rintro ⟨new_env, new_acts, ⟨eval⟩⟩
                  cases eval with
                  | eval_transfer _ _ _ _ _ _ _ hact _ _ =>
                      cases hact
                  | eval_deploy _ _ to_addr _ wc' setup' state _ _ hto_contract hnot_deployed hact hinit _ _ =>
                      cases hact
                      exact hno_deploy ⟨to_addr, state, hto_contract, hnot_deployed, hinit⟩
                  | eval_call _ _ _ _ _ msg _ _ _ _ _ _ _ hact _ _ _ =>
                      cases msg <;> cases hact
            · right
              rintro ⟨new_env, new_acts, ⟨eval⟩⟩
              have hle := action_evaluation_amount_le_account_balance eval
              simp [act_body_amount] at hle
              exact hbalance hle
          · right
            rintro ⟨new_env, new_acts, ⟨eval⟩⟩
            have hnonneg := action_evaluation_amount_nonnegative eval
            simp [act_body_amount] at hnonneg
            exact hamount hnonneg

/-- Axiom-free action-evaluation decidability for finite-address chain bases. -/
theorem action_evaluation_decidable_of_finite [Finite Base.Address] :
  ∀ (bstate : @ChainState Base) (act : @Action Base),
    reachable bstate →
    (∃ bstate' new_acts, Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts))
    ∨ ¬ ∃ bstate' new_acts,
        Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts) :=
  action_evaluation_decidable_of_deployable_address_decidable
    (Base := Base) deployable_address_decidable_of_finite

/-- Source-name theorem using the classical deployability decision above. -/
theorem action_evaluation_decidable :
  ∀ (bstate : @ChainState Base) (act : @Action Base),
    reachable bstate →
    (∃ bstate' new_acts, Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts))
    ∨ ¬ ∃ bstate' new_acts,
        Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts) :=
  action_evaluation_decidable_of_deployable_address_decidable
    (Base := Base) deployable_address_decidable

/-- An action never produces new actions when evaluated. -/
def produces_no_new_acts (act : @Action Base) : Prop :=
  ∀ bstate bstate' new_acts,
    ActionEvaluation bstate act bstate' new_acts → new_acts = []

/-- A queue is emptyable: all acts originate from accounts AND none of them
    produce new acts when evaluated. Together this guarantees that the queue
    can be fully drained. -/
def emptyable (queue : List (@Action Base)) : Prop :=
  queue.Forall act_is_from_account ∧ queue.Forall produces_no_new_acts

theorem empty_queue_is_emptyable : @emptyable Base [] :=
  ⟨trivial, trivial⟩

theorem emptyable_cons
    (x : @Action Base) (l : List (@Action Base)) (h : emptyable (x :: l)) :
    emptyable l := by
  obtain ⟨h1, h2⟩ := h
  -- Both h1, h2 are List.Forall over (x :: l).
  -- For non-singleton (l ≠ []) Forall unfolds to ∧; for [] it's True.
  refine ⟨?_, ?_⟩
  · match l, h1 with
    | [], _ => exact trivial
    | _ :: _, ⟨_, ht⟩ => exact ht
  · match l, h2 with
    | [], _ => exact trivial
    | _ :: _, ⟨_, ht⟩ => exact ht

theorem empty_queue :
  ∀ (bstate : @ChainState Base) (P : @ChainState Base → Prop),
    reachable bstate →
    emptyable bstate.chain_state_queue →
    P bstate →
    (∀ (b b' : @ChainState Base) (act : @Action Base) (acts : List (@Action Base)),
      reachable b → reachable b' → P b →
      b.chain_state_queue = act :: acts → b'.chain_state_queue = acts →
      (Nonempty (ActionEvaluation b.toEnvironment act b'.toEnvironment []) ∨
       EnvironmentEquiv b.toEnvironment b'.toEnvironment) → P b') →
    ∃ bstate', reachable_through bstate bstate' ∧ P bstate' ∧ bstate'.chain_state_queue = [] := by
  intro bstate P h_reach h_empty hP h_preserved
  have aux :
      ∀ (queue : List (@Action Base)) (bstate : @ChainState Base),
        bstate.chain_state_queue = queue →
        reachable bstate →
        emptyable queue →
        P bstate →
        ∃ bstate', reachable_through bstate bstate' ∧
          P bstate' ∧ bstate'.chain_state_queue = [] := by
    intro queue
    induction queue with
    | nil =>
        intro bstate hq hr _ hp
        refine ⟨bstate, reachable_through_refl bstate hr, hp, ?_⟩
        exact hq
    | cons act acts ih =>
        intro bstate hq hr h_empty hp
        obtain ⟨h_from_all, h_no_new_all⟩ := h_empty
        have h_from : act_is_from_account act := by
          rw [List.forall_iff_forall_mem] at h_from_all
          exact h_from_all act List.mem_cons_self
        have h_no_new : produces_no_new_acts act := by
          rw [List.forall_iff_forall_mem] at h_no_new_all
          exact h_no_new_all act List.mem_cons_self
        have h_empty_tail : emptyable acts := by
          refine ⟨?_, ?_⟩
          · rw [List.forall_iff_forall_mem] at h_from_all ⊢
            intro a ha
            exact h_from_all a (List.mem_cons_of_mem act ha)
          · rw [List.forall_iff_forall_mem] at h_no_new_all ⊢
            intro a ha
            exact h_no_new_all a (List.mem_cons_of_mem act ha)
        cases action_evaluation_decidable bstate act hr with
        | inl h_eval =>
            obtain ⟨mid_env, new_acts, ⟨eval⟩⟩ := h_eval
            let mid : @ChainState Base :=
              { toEnvironment := mid_env, chain_state_queue := new_acts ++ acts }
            have step : ChainStep bstate mid :=
              .step_action act acts new_acts hq eval rfl
            have hrt_mid : reachable_through bstate mid :=
              reachable_through_step bstate mid hr step
            have h_reach_mid : reachable mid :=
              reachable_step hr step
            have h_new_acts : new_acts = [] :=
              h_no_new bstate.toEnvironment mid_env new_acts eval
            subst new_acts
            have hP_mid : P mid :=
              h_preserved bstate mid act acts hr h_reach_mid hp hq rfl
                (Or.inl ⟨eval⟩)
            obtain ⟨to_, hrt_to, hP_to, hq_to⟩ :=
              ih mid rfl h_reach_mid h_empty_tail hP_mid
            exact ⟨to_, reachable_through_trans bstate mid to_ hrt_mid hrt_to, hP_to, hq_to⟩
        | inr h_no_eval =>
            let mid : @ChainState Base :=
              { toEnvironment := bstate.toEnvironment, chain_state_queue := acts }
            have henv : EnvironmentEquiv mid.toEnvironment bstate.toEnvironment :=
              environment_equiv_refl _
            have no_eval : ∀ mid_env new_acts,
                ActionEvaluation bstate.toEnvironment act mid_env new_acts → False := by
              intro mid_env new_acts eval
              exact h_no_eval ⟨mid_env, new_acts, ⟨eval⟩⟩
            have step : ChainStep bstate mid :=
              .step_action_invalid act acts henv hq rfl h_from no_eval
            have hrt_mid : reachable_through bstate mid :=
              reachable_through_step bstate mid hr step
            have h_reach_mid : reachable mid :=
              reachable_step hr step
            have hP_mid : P mid :=
              h_preserved bstate mid act acts hr h_reach_mid hp hq rfl
                (Or.inr henv)
            obtain ⟨to_, hrt_to, hP_to, hq_to⟩ :=
              ih mid rfl h_reach_mid h_empty_tail hP_mid
            exact ⟨to_, reachable_through_trans bstate mid to_ hrt_mid hrt_to, hP_to, hq_to⟩
  exact aux bstate.chain_state_queue bstate rfl h_reach h_empty hP

theorem add_block
    (bstate : @ChainState Base) (reward : Amount) (creator : Base.Address)
    (acts : List (@Action Base)) (slot_incr : Nat)
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue = [])
    (h_not_contract : Base.address_is_contract creator = false)
    (h_reward : reward ≥ 0) (h_slot : slot_incr > 0)
    (h_from : acts.Forall act_is_from_account)
    (h_origin : acts.Forall act_origin_is_eq_from) :
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (add_new_block_to_env
          { block_height := bstate.chain_height + 1,
            block_slot := bstate.current_slot + slot_incr,
            block_finalized_height := bstate.finalized_height,
            block_creator := creator,
            block_reward := reward } bstate.toEnvironment) := by
  let header : @BlockHeader Base :=
    { block_height := bstate.chain_height + 1,
      block_slot := bstate.current_slot + slot_incr,
      block_finalized_height := bstate.finalized_height,
      block_creator := creator,
      block_reward := reward }
  let bstate' : @ChainState Base :=
    { toEnvironment := add_new_block_to_env header bstate.toEnvironment,
      chain_state_queue := acts }
  have hvalid : IsValidNextBlock header (env_chain bstate.toEnvironment) :=
    { valid_height := rfl,
      valid_slot := by show bstate.current_slot + slot_incr > bstate.current_slot; omega,
      valid_finalized_height := by
        refine ⟨Nat.le_refl _, ?_⟩
        show bstate.finalized_height < bstate.chain_height + 1
        exact finalized_heigh_chain_height bstate h_reach,
      valid_creator := h_not_contract,
      valid_reward := h_reward }
  have henv : EnvironmentEquiv bstate'.toEnvironment
                (add_new_block_to_env header bstate.toEnvironment) :=
    environment_equiv_refl _
  have step : ChainStep bstate bstate' :=
    .step_block header h_queue hvalid h_from h_origin henv
  refine ⟨bstate', reachable_through_step bstate bstate' h_reach step, rfl, henv⟩

theorem forward_time_exact
    (bstate : @ChainState Base) (reward : Amount) (creator : Base.Address) (slot : Nat)
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue = [])
    (h_not_contract : Base.address_is_contract creator = false)
    (h_reward : reward ≥ 0)
    (h_slot : bstate.current_slot < slot) :
    ∃ bstate' header,
      reachable_through bstate bstate' ∧
      IsValidNextBlock header (env_chain bstate.toEnvironment) ∧
      slot = bstate'.current_slot ∧
      bstate'.chain_state_queue = [] ∧
      EnvironmentEquiv bstate'.toEnvironment
        (add_new_block_to_env header bstate.toEnvironment) := by
  obtain ⟨bstate', hrt, hq', henv⟩ :=
    add_block bstate reward creator [] (slot - bstate.current_slot)
      h_reach h_queue h_not_contract h_reward (by omega) trivial trivial
  let header : @BlockHeader Base :=
    { block_height := bstate.chain_height + 1,
      block_slot := bstate.current_slot + (slot - bstate.current_slot),
      block_finalized_height := bstate.finalized_height,
      block_creator := creator,
      block_reward := reward }
  have hvalid : IsValidNextBlock header (env_chain bstate.toEnvironment) :=
    { valid_height := rfl,
      valid_slot := by show bstate.current_slot + (slot - bstate.current_slot) > bstate.current_slot; omega,
      valid_finalized_height := by
        refine ⟨Nat.le_refl _, ?_⟩
        show bstate.finalized_height < bstate.chain_height + 1
        exact finalized_heigh_chain_height bstate h_reach,
      valid_creator := h_not_contract,
      valid_reward := h_reward }
  refine ⟨bstate', header, hrt, hvalid, ?_, hq', henv⟩
  show slot = bstate'.current_slot
  have hslot_eq : bstate'.current_slot =
      (add_new_block_to_env header bstate.toEnvironment).current_slot :=
    congrArg Chain.current_slot henv.chain_eq
  rw [hslot_eq]
  show slot = bstate.current_slot + (slot - bstate.current_slot)
  omega

theorem forward_time
    (bstate : @ChainState Base) (reward : Amount) (creator : Base.Address) (slot : Nat)
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue = [])
    (h_not_contract : Base.address_is_contract creator = false)
    (h_reward : reward ≥ 0) :
    ∃ bstate' header,
      reachable_through bstate bstate' ∧
      IsValidNextBlock header (env_chain bstate.toEnvironment) ∧
      slot ≤ bstate'.current_slot ∧
      bstate'.chain_state_queue = [] ∧
      EnvironmentEquiv bstate'.toEnvironment
        (add_new_block_to_env header bstate.toEnvironment) := by
  by_cases hcase : bstate.current_slot < slot
  · obtain ⟨bstate', header, hrt, hvalid, hslot_eq, hq', henv⟩ :=
      forward_time_exact bstate reward creator slot h_reach h_queue h_not_contract h_reward hcase
    exact ⟨bstate', header, hrt, hvalid, by omega, hq', henv⟩
  · -- slot ≤ current_slot already; just emit a 1-incr block to keep moving.
    obtain ⟨bstate', hrt, hq', henv⟩ :=
      add_block bstate reward creator [] 1
        h_reach h_queue h_not_contract h_reward (by omega) trivial trivial
    let header : @BlockHeader Base :=
      { block_height := bstate.chain_height + 1,
        block_slot := bstate.current_slot + 1,
        block_finalized_height := bstate.finalized_height,
        block_creator := creator,
        block_reward := reward }
    have hvalid : IsValidNextBlock header (env_chain bstate.toEnvironment) :=
      { valid_height := rfl,
        valid_slot := by show bstate.current_slot + 1 > bstate.current_slot; omega,
        valid_finalized_height := by
          refine ⟨Nat.le_refl _, ?_⟩
          show bstate.finalized_height < bstate.chain_height + 1
          exact finalized_heigh_chain_height bstate h_reach,
        valid_creator := h_not_contract,
        valid_reward := h_reward }
    refine ⟨bstate', header, hrt, hvalid, ?_, hq', henv⟩
    have hslot_eq : bstate'.current_slot =
        (add_new_block_to_env header bstate.toEnvironment).current_slot :=
      congrArg Chain.current_slot henv.chain_eq
    rw [hslot_eq]
    show slot ≤ bstate.current_slot + 1
    omega

theorem evaluate_action
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base)
    (origin frm caddr : Base.Address) (amount : Amount) (msg : Msg)
    (acts : List (@Action Base)) (new_acts : List (@ActionBody Base))
    (cstate new_cstate : State)
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue =
      { act_from := frm, act_origin := origin,
        act_body := .act_call caddr amount (serialize msg) } :: acts)
    (h_amt : amount ≥ 0)
    (h_balance : bstate.env_account_balances frm ≥ amount)
    (h_contract : bstate.env_contracts caddr = some (contract_to_weak_contract contract))
    (h_state : bstate.env_contract_states caddr = some (serialize cstate))
    (h_receive : contract.receive
      (transfer_balance frm caddr amount bstate.toEnvironment).toChain
      { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
        ctx_contract_balance :=
          if Base.address_eqb frm caddr then bstate.env_account_balances caddr
          else bstate.env_account_balances caddr + amount,
        ctx_amount := amount }
      cstate (some msg) = .Ok (new_cstate, new_acts)) :
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.env_contract_states caddr = some (serialize new_cstate) ∧
      bstate'.chain_state_queue =
        (new_acts.map (fun b => { act_origin := origin, act_from := caddr, act_body := b })) ++ acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (set_contract_state caddr (serialize new_cstate)
          (transfer_balance frm caddr amount bstate.toEnvironment)) := by
  let new_acts_full : List (@Action Base) :=
    new_acts.map (fun b => { act_origin := origin, act_from := caddr, act_body := b })
  let bstate' : @ChainState Base :=
    { toEnvironment := set_contract_state caddr (serialize new_cstate)
        (transfer_balance frm caddr amount bstate.toEnvironment),
      chain_state_queue := new_acts_full ++ acts }
  -- Compute the ctx_contract_balance from bstate' (matches the formula)
  have h_bal_eq : bstate'.env_account_balances caddr =
      if Base.address_eqb frm caddr then bstate.env_account_balances caddr
      else bstate.env_account_balances caddr + amount := by
    show (transfer_balance frm caddr amount bstate.toEnvironment).env_account_balances caddr = _
    show add_balance frm (-amount) (add_balance caddr amount bstate.env_account_balances) caddr = _
    unfold add_balance
    rw [if_pos (Address.address_eq_refl _)]
    by_cases hf : Base.address_eqb caddr frm = true
    · have hfsym : Base.address_eqb frm caddr = true := by
        rw [Address.address_eq_sym]; exact hf
      rw [if_pos hf, if_pos hfsym]; linarith
    · have hfsym : Base.address_eqb frm caddr = false := by
        rw [Address.address_eq_sym]
        cases h : Base.address_eqb caddr frm
        · rfl
        · exact absurd h hf
      rw [if_neg hf, if_neg (by simp [hfsym])]; linarith
  have henv : EnvironmentEquiv bstate'.toEnvironment
                (set_contract_state caddr (serialize new_cstate)
                  (transfer_balance frm caddr amount bstate.toEnvironment)) :=
    environment_equiv_refl _
  have h_recv_at_bstate' : contract.receive
      (transfer_balance frm caddr amount bstate.toEnvironment).toChain
      { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
        ctx_contract_balance := bstate'.env_account_balances caddr,
        ctx_amount := amount }
      cstate (some msg) = .Ok (new_cstate, new_acts) := by
    rw [h_bal_eq]; exact h_receive
  -- Translate to wc_receive via wc_receive_to_receive
  have h_wc :
      wc_receive (contract_to_weak_contract contract)
        (transfer_balance frm caddr amount bstate.toEnvironment).toChain
        { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
          ctx_contract_balance := bstate'.env_account_balances caddr,
          ctx_amount := amount }
        (serialize cstate) (some (serialize msg)) =
        .Ok (serialize new_cstate, new_acts) :=
    (wc_receive_to_receive contract _ _ cstate msg new_cstate new_acts).mp h_recv_at_bstate'
  -- Build the eval_call ActionEvaluation
  have heval : ActionEvaluation bstate.toEnvironment
      { act_from := frm, act_origin := origin,
        act_body := .act_call caddr amount (serialize msg) }
      bstate'.toEnvironment new_acts_full :=
    .eval_call origin frm caddr amount (contract_to_weak_contract contract)
      (some (serialize msg)) (serialize cstate) (serialize new_cstate) new_acts
      h_amt h_balance h_contract h_state rfl h_wc rfl henv
  -- And the ChainStep
  have step : ChainStep bstate bstate' :=
    .step_action _ acts new_acts_full h_queue heval rfl
  refine ⟨bstate', reachable_through_step bstate bstate' h_reach step, ?_, rfl, henv⟩
  -- env_contract_states bstate' caddr = some (serialize new_cstate)
  show (set_contract_state caddr (serialize new_cstate)
          (transfer_balance frm caddr amount bstate.toEnvironment)).env_contract_states caddr =
        some (serialize new_cstate)
  show set_chain_contract_state caddr (serialize new_cstate) _ caddr = some (serialize new_cstate)
  unfold set_chain_contract_state
  rw [if_pos (Address.address_eq_refl _)]

theorem evaluate_transfer
    (bstate : @ChainState Base) (origin frm to_ : Base.Address)
    (amount : Amount) (acts : List (@Action Base))
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue =
      { act_from := frm, act_origin := origin,
        act_body := .act_transfer to_ amount } :: acts)
    (h_amt : amount ≥ 0)
    (h_balance : bstate.env_account_balances frm ≥ amount)
    (h_not_contract : Base.address_is_contract to_ = false) :
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (transfer_balance frm to_ amount bstate.toEnvironment) := by
  let bstate' : @ChainState Base :=
    { toEnvironment := transfer_balance frm to_ amount bstate.toEnvironment,
      chain_state_queue := acts }
  have henv : EnvironmentEquiv bstate'.toEnvironment
                (transfer_balance frm to_ amount bstate.toEnvironment) :=
    environment_equiv_refl _
  have eval : ActionEvaluation bstate.toEnvironment
                { act_from := frm, act_origin := origin,
                  act_body := .act_transfer to_ amount }
                bstate'.toEnvironment [] :=
    .eval_transfer origin frm to_ amount h_amt h_balance h_not_contract rfl henv rfl
  have step : ChainStep bstate bstate' :=
    .step_action _ acts [] h_queue eval (by show acts = [] ++ acts; rfl)
  exact ⟨bstate', reachable_through_step bstate bstate' h_reach step, rfl, henv⟩

theorem discard_invalid_action
    (bstate : @ChainState Base) (act : @Action Base) (acts : List (@Action Base))
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue = act :: acts)
    (h_from : act_is_from_account act)
    (h_no_eval : ∀ bstate0 new_acts,
      ActionEvaluation bstate.toEnvironment act bstate0 new_acts → False) :
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment bstate.toEnvironment := by
  let bstate' : @ChainState Base :=
    { toEnvironment := bstate.toEnvironment,
      chain_state_queue := acts }
  have henv : EnvironmentEquiv bstate'.toEnvironment bstate.toEnvironment :=
    environment_equiv_refl _
  have step : ChainStep bstate bstate' :=
    .step_action_invalid act acts henv h_queue rfl h_from h_no_eval
  exact ⟨bstate', reachable_through_step bstate bstate' h_reach step, rfl, henv⟩

theorem permute_queue
    (bstate : @ChainState Base) (acts acts_permuted : List (@Action Base))
    (h_reach : reachable bstate)
    (h_queue : bstate.chain_state_queue = acts)
    (h_perm : List.Perm acts acts_permuted) :
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts_permuted ∧
      EnvironmentEquiv bstate'.toEnvironment bstate.toEnvironment := by
  let bstate' : @ChainState Base :=
    { toEnvironment := bstate.toEnvironment,
      chain_state_queue := acts_permuted }
  have henv : EnvironmentEquiv bstate'.toEnvironment bstate.toEnvironment :=
    environment_equiv_refl _
  have hp : List.Perm bstate.chain_state_queue bstate'.chain_state_queue := by
    rw [h_queue]; exact h_perm
  have step : ChainStep bstate bstate' :=
    .step_permute henv hp
  exact ⟨bstate', reachable_through_step bstate bstate' h_reach step, rfl, henv⟩

theorem deploy_contract :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base)
    (origin frm caddr : Base.Address) (amount : Amount)
    (acts : List (@Action Base)) (setup : Setup) (cstate : State),
    reachable bstate →
    bstate.chain_state_queue =
      { act_from := frm, act_origin := origin,
        act_body := .act_deploy amount (contract_to_weak_contract contract) (serialize setup) } :: acts →
    amount ≥ 0 →
    bstate.env_account_balances frm ≥ amount →
    Base.address_is_contract caddr = true →
    bstate.env_contracts caddr = none →
    contract.init (transfer_balance frm caddr amount bstate.toEnvironment).toChain
      { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
        ctx_contract_balance := amount, ctx_amount := amount } setup = .Ok cstate →
    ∃ bstate', ∃ (trace : ChainTrace empty_state bstate'),
      reachable_through bstate bstate' ∧
      bstate'.env_contracts caddr = some (contract_to_weak_contract contract) ∧
      bstate'.env_contract_states caddr = some (serialize cstate) ∧
      deployment_info Setup trace caddr =
        some { deployment_origin := origin, deployment_from := frm,
               deployment_amount := amount, deployment_setup := setup } ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (set_contract_state caddr (serialize cstate)
          (add_contract caddr (contract_to_weak_contract contract)
            (transfer_balance frm caddr amount bstate.toEnvironment))) := by
  intro Setup Msg State Error _ _ _ _ contract bstate origin frm caddr amount acts setup cstate
    h_reach h_queue h_amt h_balance h_addr h_not_deployed h_init
  let target_env : @Environment Base :=
    set_contract_state caddr (serialize cstate)
      (add_contract caddr (contract_to_weak_contract contract)
        (transfer_balance frm caddr amount bstate.toEnvironment))
  let bstate' : @ChainState Base :=
    { toEnvironment := target_env, chain_state_queue := acts }
  have henv : EnvironmentEquiv bstate'.toEnvironment target_env :=
    environment_equiv_refl _
  have h_wc_init :
      wc_init (contract_to_weak_contract contract)
        (transfer_balance frm caddr amount bstate.toEnvironment).toChain
        { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
          ctx_contract_balance := amount, ctx_amount := amount }
        (serialize setup) = .Ok (serialize cstate) :=
    (wc_init_to_init contract _ _ setup cstate).mp h_init
  let eval : ActionEvaluation bstate.toEnvironment
      { act_from := frm, act_origin := origin,
        act_body := .act_deploy amount (contract_to_weak_contract contract) (serialize setup) }
      bstate'.toEnvironment [] :=
    .eval_deploy origin frm caddr amount (contract_to_weak_contract contract)
      (serialize setup) (serialize cstate)
      h_amt h_balance h_addr h_not_deployed rfl h_wc_init henv rfl
  let step : ChainStep bstate bstate' :=
    .step_action _ acts [] h_queue eval (by show acts = [] ++ acts; rfl)
  obtain ⟨trace0⟩ := h_reach
  let trace : ChainTrace empty_state bstate' := ChainedList.snoc trace0 step
  refine ⟨bstate', trace, reachable_through_step bstate bstate' ⟨trace0⟩ step, ?_, ?_, ?_, rfl, henv⟩
  · show target_env.env_contracts caddr = some (contract_to_weak_contract contract)
    simp [target_env, set_contract_state, add_contract, Address.address_eq_refl]
  · show target_env.env_contract_states caddr = some (serialize cstate)
    simp [target_env, set_contract_state, set_chain_contract_state, Address.address_eq_refl]
  · show deployment_info Setup trace caddr =
        some { deployment_origin := origin, deployment_from := frm,
               deployment_amount := amount, deployment_setup := setup }
    simp [trace, step, eval, deployment_info, step_deployment_info, eval_tx,
      Address.address_eq_refl, Serializable.deserialize_serialize]

end BuildUtils

end ConCert.Execution.BlockchainBuilder
