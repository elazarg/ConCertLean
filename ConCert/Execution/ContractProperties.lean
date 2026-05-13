/- Port of execution/theories/ContractProperties.v
   The file is a long list of definitions and lemmas about non-recursive,
   non-payable, payable contracts, etc. Lemmas are axiomatized. -/

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

axiom nonrecursive_strong_nonrecursive :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error),
    NonRecursiveStrong contract → NonRecursive contract

/-- Non-recursive specialization of `contract_induction`: the
    recursive-call case is replaced by the `NonRecursive` hypothesis on
    the contract. Takes `NonRecursiveContractInductionCases`, which omits
    the `recursive_call_case` field. -/
axiom nonrecursive_contract_induction :
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
          (outgoing_txs trace caddr)

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
axiom NonPayable_weaken :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error),
    NonPayable contract → NonPayableWeak contract

axiom NonPayable_balance_zero :
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
        bstate.env_account_balances caddr = 0

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
axiom LocalBalance_weaken :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error) (proj : State → Amount),
    LocalBalance contract proj → LocalBalanceWeak contract proj

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
