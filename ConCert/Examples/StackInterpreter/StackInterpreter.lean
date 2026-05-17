/- Port of examples/stackInterpreter/StackInterpreter.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Containers
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive

namespace ConCert.Examples.StackInterpreter

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

abbrev MapKey := String × Int

inductive Op where
  | Add
  | Sub
  | Mult
  | Lt
  | Le
  | Equal
  deriving DecidableEq, Repr, Serializable

inductive Instruction where
  | IPushZ (i : Int)
  | IPushB (b : Bool)
  | IObs (p : MapKey)
  | IIf
  | IElse
  | IEndIf
  | IOp (op : Op)
  deriving DecidableEq, Repr, Serializable

inductive Value where
  | BVal (b : Bool)
  | ZVal (i : Int)
  deriving DecidableEq, Repr, Serializable

abbrev op := Op
abbrev instruction := Instruction
abbrev value := Value

abbrev ExtMap := FMap MapKey Value
abbrev ext_map := ExtMap

def lookup (k : MapKey) (m : ExtMap) : Option Value :=
  FMap.find k m

abbrev Storage := List Value
abbrev storage := Storage

abbrev Error : Type := Nat
def default_error : Error := 1

def init (_chain : Chain) (_ctx : @ContractCallContext Base) (_setup : Unit) :
    Result Storage Error :=
  .Ok []

abbrev Msg := List Instruction × ExtMap
abbrev msg := Msg

def continue_ (i : Int) : Bool :=
  i == 0

def bool_to_cond (b : Bool) : Int :=
  if b then 0 else 1

def flip (i : Int) : Int :=
  if i == 0 then 1 else if i == 1 then 0 else i

def reset_decrement (i : Int) : Int :=
  if i ≤ 1 then 0 else i - 1

def interp (ext : ExtMap) : List Instruction → Storage → Int → Result Storage Error
  | [], s, _ => .Ok s
  | hd :: inst0, s, cond =>
      match hd with
      | .IPushZ i =>
          if continue_ cond then
            interp ext inst0 (.ZVal i :: s) cond
          else
            interp ext inst0 s cond
      | .IPushB b =>
          if continue_ cond then
            interp ext inst0 (.BVal b :: s) cond
          else
            interp ext inst0 s cond
      | .IIf =>
          if cond == 0 then
            match s with
            | .BVal b :: s0 => interp ext inst0 s0 (bool_to_cond b)
            | _ => .Err default_error
          else
            interp ext inst0 s (1 + cond)
      | .IElse =>
          interp ext inst0 s (flip cond)
      | .IEndIf =>
          interp ext inst0 s (reset_decrement cond)
      | .IObs p =>
          if continue_ cond then
            match lookup p ext with
            | some v => interp ext inst0 (v :: s) cond
            | none => .Err default_error
          else
            interp ext inst0 s cond
      | .IOp op =>
          if continue_ cond then
            match op, s with
            | .Add, .ZVal i :: .ZVal j :: s0 =>
                interp ext inst0 (.ZVal (i + j) :: s0) cond
            | .Sub, .ZVal i :: .ZVal j :: s0 =>
                interp ext inst0 (.ZVal (i - j) :: s0) cond
            | .Mult, .ZVal i :: .ZVal j :: s0 =>
                interp ext inst0 (.ZVal (i * j) :: s0) cond
            | .Le, .ZVal i :: .ZVal j :: s0 =>
                interp ext inst0 (.BVal (i ≤ j) :: s0) cond
            | .Lt, .ZVal i :: .ZVal j :: s0 =>
                interp ext inst0 (.BVal (i < j) :: s0) cond
            | .Equal, .ZVal i :: .ZVal j :: s0 =>
                interp ext inst0 (.BVal (i == j) :: s0) cond
            | _, _ => .Err default_error
          else
            interp ext inst0 s cond

def receive
    (_chain : Chain) (_ctx : @ContractCallContext Base)
    (_s : Storage) (msg : Option Msg) :
    Result (Storage × List (@ActionBody Base)) Error :=
  match msg with
  | none => .Err default_error
  | some (insts, ext) =>
      match interp ext insts [] 0 with
      | .Ok v => .Ok (v, [])
      | .Err e => .Err e

def contract : @Contract Base Unit Msg Storage Error _ _ _ _ :=
  { init := init, receive := receive }

end ConCert.Examples.StackInterpreter
