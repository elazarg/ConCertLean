/- Port of execution/theories/ContractProperties.v
   The file is a long list of definitions and lemmas about non-recursive,
   non-payable, payable contracts, etc. -/

import ConCert.Utils.Extras
import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.SerializableBase

namespace ConCert.Execution.ContractProperties

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad

variable [Base : ChainBase]

/-! ### Non-recursive contracts -/

def NonRecursiveStrong
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) : Prop :=
  ∀ chain ctx prev_state msg new_state new_acts,
    contract.receive chain ctx prev_state msg = Ok (new_state, new_acts) →
    new_acts.Forall (fun act_body =>
      match act_body with
      | .act_transfer to_ _ => Base.address_eqb to_ ctx.ctx_contract_address = false
      | .act_call to_ _ _   => Base.address_eqb to_ ctx.ctx_contract_address = false
      | _ => True)

def NonRecursive
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) : Prop :=
  ∀ bstate caddr,
    reachable bstate →
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    (outgoing_acts bstate caddr).Forall (fun act_body =>
      match act_body with
      | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
      | .act_call to_ _ _   => Base.address_eqb to_ caddr = false
      | _ => True)

theorem nonrecursive_strong_nonrecursive :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error),
    NonRecursiveStrong contract → NonRecursive contract := by
  intro Setup Msg State Error _ _ _ _ contract hstrong bstate caddr hr hdeployed
  obtain ⟨trace⟩ := hr
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
      State → Amount → List (@ActionBody Base) →
      List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ caddr _ _ _ out_queue _ _ =>
      out_queue.Forall (fun act_body =>
        match act_body with
        | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
        | .act_call to_ _ _   => Base.address_eqb to_ caddr = false
        | _ => True)
  have hcases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval with
          | eval_transfer => trivial
          | eval_deploy => trivial
          | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro old_h old_s old_f new_h new_s new_f caddr dep_info state balance
        inc_calls out_txs facts ih _
      exact ih
    · intro chain ctx setup result facts hinit _
      simp [P]
    · intro height slot fin_height caddr dep_info cstate balance out_act out_acts
        inc_calls prev_out_txs tx ih hfrom hamount hmatch _
      simp only [P, List.forall_cons] at ih
      exact ih.2
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hnot_self facts ih hreceive _
      simp only [P] at ih ⊢
      exact (ConCert.Utils.Extras.Forall_app _ _ _).mp
        ⟨hstrong chain ctx prev_state msg new_state new_acts hreceive, ih⟩
    · intro chain ctx dep_info prev_state msg head prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hself facts ih haction hreceive _
      simp only [P, List.forall_cons] at ih
      simp only [P]
      exact (ConCert.Utils.Extras.Forall_app _ _ _).mp
        ⟨hstrong chain ctx prev_state msg new_state new_acts hreceive, ih.2⟩
    · intro height slot fin_height caddr dep_info cstate balance out_queue
        inc_calls out_txs out_queue' ih hperm _
      simp only [P] at ih ⊢
      exact ConCert.Utils.Extras.forall_respects_permutation _ _ _ hperm ih
  obtain ⟨_, _, _, _, _, _, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  simpa [P] using hP

/-- Non-recursive specialization of `contract_induction`: the
    recursive-call case is replaced by the `NonRecursive` hypothesis on
    the contract. Takes `NonRecursiveContractInductionCases`, which omits
    the `recursive_call_case` field. -/
theorem nonrecursive_contract_induction :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (AddBlockFacts : Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat →
       Base.Address →
       @DeploymentInfo Base Setup →
       State →
       Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop),
    NonRecursive contract →
    NonRecursiveContractInductionCases contract AddBlockFacts DeployFacts CallFacts P →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address)
      (trace : ChainTrace empty_state bstate),
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ dep cstate inc_calls,
        deployment_info Setup trace caddr = some dep ∧
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
          dep cstate (bstate.env_account_balances caddr)
          (outgoing_acts bstate caddr) inc_calls
          (outgoing_txs trace caddr) := by
  intro Setup Msg State Error _ _ _ _ contract AddBlockFacts DeployFacts CallFacts P
    hnonrecursive hcases bstate caddr trace hdeployed
  let CallFacts' :
      Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
        Option (List (@ContractCallInfo Base Msg)) → Prop :=
    fun chain ctx state out_queue inc_calls =>
      CallFacts chain ctx state out_queue inc_calls ∧
      ctx.ctx_from ≠ ctx.ctx_contract_address
  have hcases' : ContractInductionCases contract AddBlockFacts DeployFacts CallFacts' P := by
    refine
      { establish_facts := ?_, add_block_case := hcases.add_block_case,
        init_case := hcases.init_case,
        outgoing_act_case := hcases.outgoing_act_case,
        nonrecursive_call_case := ?_, recursive_call_case := ?_,
        permute_case := hcases.permute_case }
    · intro bstate_from bstate_to step from_reachable _
      cases step with
      | step_block header hqueue hvalid hfrom horigin henv =>
          exact hcases.establish_facts
            (.step_block header hqueue hvalid hfrom horigin henv) from_reachable .tag_facts
      | step_action act acts new_acts hqueue eval hqueue' =>
          cases eval with
          | eval_transfer =>
              trivial
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount hbalance haddr hnot_deployed hact hinit henv hnew_acts =>
              exact hcases.establish_facts
                (.step_action act acts new_acts hqueue
                  (.eval_deploy origin from_addr to_addr amount wc setup state
                    hamount hbalance haddr hnot_deployed hact hinit henv hnew_acts)
                  hqueue')
                from_reachable .tag_facts
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts amount_nonnegative amount_le hcontract hstate hact hreceive
              hnew_acts henv =>
              intro cstate hdeployed' hstate'
              have hfacts :
                  stepFactsPred contract AddBlockFacts DeployFacts CallFacts
                    (.step_action act acts new_acts hqueue
                      (.eval_call origin from_addr to_addr amount wc msg prev_state new_state
                        resp_acts amount_nonnegative amount_le hcontract hstate hact hreceive
                        hnew_acts henv)
                      hqueue')
                    from_reachable :=
                hcases.establish_facts _ from_reachable .tag_facts
              refine ⟨hfacts cstate hdeployed' hstate', ?_⟩
              intro hself
              have hfrom_eq : from_addr = to_addr := by
                simpa using hself
              have hout := hnonrecursive bstate_from to_addr
                (trace_reachable from_reachable) hdeployed'
              subst from_addr
              cases msg <;>
                simp [outgoing_acts, hqueue, hact, Address.address_eq_refl] at hout
      | step_action_invalid =>
          trivial
      | step_permute =>
          trivial
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hnot_self facts ih hreceive tag
      exact hcases.nonrecursive_call_case chain ctx dep_info prev_state msg
        prev_out_queue prev_inc_calls prev_out_txs new_state new_acts
        hnot_self facts.1 ih hreceive tag
    · intro chain ctx dep_info prev_state msg head prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hself facts ih haction hreceive tag
      exact False.elim (facts.2 hself)
  exact contract_induction contract AddBlockFacts DeployFacts CallFacts' P hcases'
    bstate caddr trace hdeployed

/-! ### Non-payable / payable -/

def NonPayable
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) : Prop :=
  (∀ chain ctx prev_state msg,
    ctx.ctx_amount > 0 →
    isErr (contract.receive chain ctx prev_state msg) = true) ∧
  (∀ chain ctx setup,
    ctx.ctx_amount > 0 →
    isErr (contract.init chain ctx setup) = true)

/-- `NonPayableWeak` is `NonPayable` minus the `init` clause. The receive
    clause must remain `ctx_amount > 0 → isErr (receive …) = true` (not the
    seemingly-equivalent `(∃ res, receive = Ok res) → ctx_amount = 0`,
    which is strictly stronger over `Int` and makes `NonPayable_weaken`
    derive `-1 = 0`). -/
def NonPayableWeak
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) : Prop :=
  ∀ chain ctx prev_state msg,
    ctx.ctx_amount > 0 →
    isErr (contract.receive chain ctx prev_state msg) = true

/-- Coq direction: strong ⇒ weak. NonPayable is the stronger property
    (also covers init); the weakening drops the init clause and restates
    receive's reject-when-nonzero as "if receive succeeds, amount = 0". -/
theorem NonPayable_weaken
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (h : NonPayable contract) : NonPayableWeak contract := h.1

private theorem trace_txs_amount_nonnegative :
    ∀ {frm to_ : @ChainState Base} (trace : ChainTrace frm to_),
      ∀ tx, tx ∈ trace_txs trace → tx.tx_amount ≥ 0 := by
  intro frm to_ trace
  induction trace with
  | clnil =>
      intro tx hmem
      simp [trace_txs] at hmem
  | snoc tail step ih =>
      intro tx hmem
      simp only [trace_txs, List.mem_append, step_txs] at hmem
      cases step with
      | step_block =>
          rcases hmem with hfalse | htail
          · cases hfalse
          · exact ih tx htail
      | step_action _ _ _ _ eval _ =>
          simp only [List.mem_singleton] at hmem
          rcases hmem with htx | htail
          · subst htx
            cases eval <;> simp [eval_tx] <;> assumption
          · exact ih tx htail
      | step_action_invalid =>
          rcases hmem with hfalse | htail
          · cases hfalse
          · exact ih tx htail
      | step_permute =>
          rcases hmem with hfalse | htail
          · cases hfalse
          · exact ih tx htail

private theorem outgoing_txs_amount_nonnegative
    {frm to_ : @ChainState Base} (trace : ChainTrace frm to_)
    (addr : Base.Address) :
    ∀ tx, tx ∈ outgoing_txs trace addr → tx.tx_amount ≥ 0 := by
  intro tx hmem
  exact trace_txs_amount_nonnegative trace tx
    (List.mem_of_mem_filter hmem)

theorem NonPayable_balance_zero :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error),
    NonPayable contract →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address),
      reachable bstate →
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ cstate,
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        bstate.env_account_balances caddr = 0 := by
  intro Setup Msg State Error _ _ _ _ contract hnonpayable bstate caddr hr hdeployed
  obtain ⟨trace⟩ := hr
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
      State → Amount → List (@ActionBody Base) →
      List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ dep _ _ _ inc_calls _ =>
      dep.deployment_amount = 0 ∧
      inc_calls.Forall (fun call => call.call_amount = 0)
  have hcases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True)
      (fun _ ctx => ctx.ctx_amount ≥ 0)
      (fun _ ctx _ _ _ => ctx.ctx_amount ≥ 0)
      P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval with
          | eval_transfer => trivial
          | eval_deploy origin from_addr to_addr amount wc setup state
              hamount _ _ _ _ hinit _ _ =>
              exact hamount
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state
              resp_acts hamount _ _ _ _ hreceive _ _ =>
              intro _ _ _
              exact hamount
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _
      exact ih
    · intro chain ctx setup result hctx hinit _
      have hzero : ctx.ctx_amount = 0 := by
        by_contra hne
        have hpos : ctx.ctx_amount > 0 := by
          exact lt_of_le_of_ne hctx (Ne.symm hne)
        have herr := hnonpayable.2 chain ctx setup hpos
        rw [hinit] at herr
        cases herr
      exact ⟨hzero, by simp⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      exact ih
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts _ hctx ih hreceive _
      have hzero : ctx.ctx_amount = 0 := by
        by_contra hne
        have hpos : ctx.ctx_amount > 0 := by
          exact lt_of_le_of_ne hctx (Ne.symm hne)
        have herr := hnonpayable.1 chain ctx prev_state msg hpos
        rw [hreceive] at herr
        cases herr
      exact ⟨ih.1, by simp [hzero, ih.2]⟩
    · intro chain ctx dep_info prev_state msg head prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts _ hctx ih _ hreceive _
      have hzero : ctx.ctx_amount = 0 := by
        by_contra hne
        have hpos : ctx.ctx_amount > 0 := by
          exact lt_of_le_of_ne hctx (Ne.symm hne)
        have herr := hnonpayable.1 chain ctx prev_state msg hpos
        rw [hreceive] at herr
        cases herr
      exact ⟨ih.1, by simp [hzero, ih.2]⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _
      exact ih
  obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  refine ⟨cstate, hstate, ?_⟩
  have hincoming_map :=
    incoming_txs_contract caddr bstate trace Setup dep Msg inc_calls hdep hinc
  have hincoming_sum :
      ((incoming_txs trace caddr).map (fun tx : @Tx Base => tx.tx_amount)).sum = 0 := by
    rw [show
      (incoming_txs trace caddr).map (fun tx : @Tx Base => tx.tx_amount) =
        ((incoming_txs trace caddr).map
          (fun tx : @Tx Base => (tx.tx_from, tx.tx_to, tx.tx_amount))).map
          (fun p : Base.Address × Base.Address × Amount => p.2.2) by
      simp [List.map_map]]
    rw [hincoming_map]
    have hcalls :
        (inc_calls.map (fun call : @ContractCallInfo Base Msg => call.call_amount)).sum = 0 :=
      by
        have hforall := hP.2
        clear hP hinc hincoming_map
        revert hforall
        induction inc_calls with
        | nil =>
            intro _
            rfl
        | cons call calls ih =>
            intro hforall
            simp only [List.forall_cons] at hforall
            simp [hforall.1, ih hforall.2]
    simpa [List.map_map, hP.1] using hcalls
  have hcreated :
      created_blocks trace caddr = [] :=
    contract_no_created_blocks bstate caddr trace
      (deployment_info_addr_format Setup trace caddr dep hdep)
  have houtgoing_nonneg :
      0 ≤ ((outgoing_txs trace caddr).map (fun tx : @Tx Base => tx.tx_amount)).sum :=
    by
      let txs := outgoing_txs trace caddr
      have htxs : ∀ tx, tx ∈ txs → 0 ≤ tx.tx_amount := by
        intro tx hmem
        exact outgoing_txs_amount_nonnegative trace caddr tx (by simpa [txs] using hmem)
      change 0 ≤ (txs.map (fun tx : @Tx Base => tx.tx_amount)).sum
      revert htxs
      induction txs with
      | nil =>
          intro _
          exact Int.le_refl _
      | cons tx txs ih =>
          intro htxs
          have hhead : 0 ≤ tx.tx_amount := htxs tx List.mem_cons_self
          have htail : 0 ≤ (txs.map (fun tx : @Tx Base => tx.tx_amount)).sum :=
            ih (fun x hx => htxs x (List.mem_cons_of_mem _ hx))
          simp only [List.map_cons, List.sum_cons]
          linarith
  have hbalance_nonneg : bstate.env_account_balances caddr ≥ 0 :=
    account_balance_nonnegative bstate caddr ⟨trace⟩
  rw [account_balance_trace bstate trace caddr] at hbalance_nonneg
  rw [hincoming_sum, hcreated] at hbalance_nonneg
  simp at hbalance_nonneg
  have houtgoing_zero :
      ((outgoing_txs trace caddr).map (fun tx : @Tx Base => tx.tx_amount)).sum = 0 := by
    apply le_antisymm
    · exact hbalance_nonneg
    · exact houtgoing_nonneg
  rw [account_balance_trace bstate trace caddr]
  rw [hincoming_sum, hcreated, houtgoing_zero]
  simp

def Payable
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) : Prop :=
  ¬ NonPayable contract

def ConstantField
    {Setup Msg State Error F : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) (proj : State → F) : Prop :=
  ∀ chain ctx prev_state msg new_state new_acts,
    contract.receive chain ctx prev_state msg = Ok (new_state, new_acts) →
    proj prev_state = proj new_state

def sum_acts (acts : List (@ActionBody Base)) : Amount :=
  (acts.map act_body_amount).foldl (· + ·) 0

def LocalBalance
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) (proj : State → Amount) : Prop :=
  (∀ chain ctx prev_state msg new_state new_acts,
    contract.receive chain ctx prev_state msg = Ok (new_state, new_acts) →
    proj prev_state = proj new_state - ctx.ctx_amount + sum_acts new_acts) ∧
  (∀ chain ctx setup new_state,
    contract.init chain ctx setup = Ok new_state →
    proj new_state = ctx.ctx_amount)

def LocalBalanceWeak
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) (proj : State → Amount) : Prop :=
  ∀ chain ctx prev_state msg new_state new_acts,
    contract.receive chain ctx prev_state msg = Ok (new_state, new_acts) →
    proj prev_state = proj new_state - ctx.ctx_amount + sum_acts new_acts

/-- Coq direction: strong ⇒ weak. `LocalBalance` adds an `init` clause to
    `LocalBalanceWeak`; dropping that clause gives the weak version. -/
theorem LocalBalance_weaken
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) (proj : State → Amount)
    (h : LocalBalance contract proj) : LocalBalanceWeak contract proj := h.1

def EmptyableStrong
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) : Prop :=
  ∀ chain ctx prev_state,
    ctx.ctx_contract_balance = 0 ∨
    ∃ msg new_state new_acts,
      contract.receive chain ctx prev_state msg = Ok (new_state, new_acts) ∧
      sum_acts new_acts > 0

end ConCert.Execution.ContractProperties
