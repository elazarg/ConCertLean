/- Port of execution/theories/ContractMonads.v -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable

namespace ConCert.Execution.ContractMonads

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

def ContractReader (T : Type) : Type :=
  Chain → @ContractCallContext Base → (Chain × @ContractCallContext Base × T)

def run_contract_reader {T : Type}
    (chain : Chain) (ctx : @ContractCallContext Base) (m : @ContractReader Base T) : T :=
  let r := m chain ctx
  r.2.2

instance : Monad (@ContractReader Base) where
  pure x := fun chain ctx => (chain, ctx, x)
  bind prev f := fun chain ctx =>
    let r := prev chain ctx
    f r.2.2 r.1 r.2.1

def ContractIniter (Setup Error T : Type) : Type :=
  Chain → @ContractCallContext Base → Setup →
    (Chain × @ContractCallContext Base × Setup × Result T Error)

def run_contract_initer {Setup Error T : Type}
    (m : @ContractIniter Base Setup Error T)
    (chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup) : Result T Error :=
  (m chain ctx setup).2.2.2

instance {Setup Error : Type} : Monad (@ContractIniter Base Setup Error) where
  pure x := fun chain ctx setup => (chain, ctx, setup, .Ok x)
  bind prev f := fun chain ctx setup =>
    let r := prev chain ctx setup
    match r.2.2.2 with
    | .Ok v  => f v r.1 r.2.1 r.2.2.1
    | .Err e => (r.1, r.2.1, r.2.2.1, .Err e)

instance contract_reader_to_contract_initer {Setup Error : Type} :
    ConCert.Execution.Monad.MonadTrans (@ContractIniter Base Setup Error) (@ContractReader Base) where
  lift reader := fun chain ctx setup =>
    let r := reader chain ctx
    (r.1, r.2.1, setup, .Ok r.2.2)

instance result_to_contract_initer {Setup Error : Type} :
    ConCert.Execution.Monad.MonadTrans
      (@ContractIniter Base Setup Error) (fun T => Result T Error) where
  lift r := fun chain ctx setup => (chain, ctx, setup, r)

def ContractReceiver (State Msg Error T : Type) : Type :=
  Chain → @ContractCallContext Base → State → Option Msg → List (@ActionBody Base) →
    (Chain × @ContractCallContext Base × State × Option Msg × List (@ActionBody Base) × Result T Error)

instance {State Msg Error : Type} : Monad (@ContractReceiver Base State Msg Error) where
  pure x := fun chain ctx state msg acts => (chain, ctx, state, msg, acts, .Ok x)
  bind prev f := fun chain ctx state msg acts =>
    let r := prev chain ctx state msg acts
    match r.2.2.2.2.2 with
    | .Ok v  => f v r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1
    | .Err e => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, .Err e)

instance contract_reader_to_receiver {State Msg Error : Type} :
    ConCert.Execution.Monad.MonadTrans
      (@ContractReceiver Base State Msg Error) (@ContractReader Base) where
  lift reader := fun chain ctx state msg acts =>
    let r := reader chain ctx
    (r.1, r.2.1, state, msg, acts, .Ok r.2.2)

instance result_to_contract_receiver {State Msg Error : Type} :
    ConCert.Execution.Monad.MonadTrans
      (@ContractReceiver Base State Msg Error) (fun T => Result T Error) where
  lift r := fun chain ctx state msg acts => (chain, ctx, state, msg, acts, r)

def run_contract_receiver {State Msg Error T : Type}
    (m : @ContractReceiver Base State Msg Error T)
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : State) (msg : Option Msg) :
    Result (T × List (@ActionBody Base)) Error :=
  let r := m chain ctx state msg []
  match r.2.2.2.2.2 with
  | .Ok v  => .Ok (v, r.2.2.2.2.1)
  | .Err e => .Err e

/-- Lives in a nested namespace to avoid colliding with `Chain.chain_height`. -/
def chain_height : @ContractReader Base Nat :=
  fun chain ctx => (chain, ctx, chain.chain_height)

def current_slot : @ContractReader Base Nat :=
  fun chain ctx => (chain, ctx, chain.current_slot)

def finalized_height : @ContractReader Base Nat :=
  fun chain ctx => (chain, ctx, chain.finalized_height)

def caller_addr : @ContractReader Base Base.Address :=
  fun chain ctx => (chain, ctx, ctx.ctx_from)

def my_addr : @ContractReader Base Base.Address :=
  fun chain ctx => (chain, ctx, ctx.ctx_contract_address)

def my_balance : @ContractReader Base Amount :=
  fun chain ctx => (chain, ctx, ctx.ctx_contract_balance)

def call_amount : @ContractReader Base Amount :=
  fun chain ctx => (chain, ctx, ctx.ctx_amount)

def deployment_setup {Setup Error : Type} :
    @ContractIniter Base Setup Error Setup :=
  fun chain ctx setup => (chain, ctx, setup, .Ok setup)

def reject_deployment {Setup State Error : Type} (err : Error) :
    @ContractIniter Base Setup Error State :=
  fun chain ctx setup => (chain, ctx, setup, .Err err)

def accept_deployment {Setup Error State : Type} (state : State) :
    @ContractIniter Base Setup Error State :=
  pure state

def call_msg {State Msg Error : Type} (err : Error) :
    @ContractReceiver Base State Msg Error Msg :=
  fun chain ctx state msg acts =>
    (chain, ctx, state, msg, acts, result_of_option msg err)

def my_state {State Msg Error : Type} :
    @ContractReceiver Base State Msg Error State :=
  fun chain ctx state msg acts => (chain, ctx, state, msg, acts, .Ok state)

def queue {State Msg Error : Type} (act : @ActionBody Base) :
    @ContractReceiver Base State Msg Error Unit :=
  fun chain ctx state msg acts =>
    (chain, ctx, state, msg, acts ++ [act], .Ok ())

def reject_call {State Msg Error : Type} (err : Error) :
    @ContractReceiver Base State Msg Error State :=
  fun chain ctx state msg _ =>
    (chain, ctx, state, msg, [], .Err err)

def accept_call {State Msg Error : Type} (new_state : State) :
    @ContractReceiver Base State Msg Error State :=
  fun chain ctx state msg acts =>
    (chain, ctx, state, msg, acts, .Ok new_state)

def build_contract
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (init : @ContractIniter Base Setup Error State)
    (receive : @ContractReceiver Base State Msg Error State) :
    @Contract Base Setup Msg State Error _ _ _ _ :=
  { init := run_contract_initer init,
    receive := run_contract_receiver receive }

end ConCert.Execution.ContractMonads
