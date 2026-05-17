/- Port of execution/theories/SerializableDerive.v. -/

import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import ConCert.Execution.SerializableInstances

open Lean Elab Command Meta Parser.Term
open Lean.Elab.Deriving

namespace ConCert.Execution.SerializableDerive

namespace Internal

open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances

private def maxConstructorArity : Nat := 10

private def serializeCtorName : Nat → Name
  | 0 => ``serialize_constructor0
  | 1 => ``serialize_constructor1
  | 2 => ``serialize_constructor2
  | 3 => ``serialize_constructor3
  | 4 => ``serialize_constructor4
  | 5 => ``serialize_constructor5
  | 6 => ``serialize_constructor6
  | 7 => ``serialize_constructor7
  | 8 => ``serialize_constructor8
  | 9 => ``serialize_constructor9
  | _ => ``serialize_constructor10

private def deserializeCtorName : Nat → Name
  | 0 => ``deserialize_constructor0
  | 1 => ``deserialize_constructor1
  | 2 => ``deserialize_constructor2
  | 3 => ``deserialize_constructor3
  | 4 => ``deserialize_constructor4
  | 5 => ``deserialize_constructor5
  | 6 => ``deserialize_constructor6
  | 7 => ``deserialize_constructor7
  | 8 => ``deserialize_constructor8
  | 9 => ``deserialize_constructor9
  | _ => ``deserialize_constructor10

private partial def mkTupleProj (base : Term) (idx arity : Nat) : TermElabM Term := do
  if arity <= 1 then
    pure base
  else if idx == 0 then
    `($base.1)
  else
    mkTupleProj (← `($base.2)) (idx - 1) (arity - 1)

private def getCtorFieldTypes (ctorInfo : ConstructorVal) : TermElabM (Array Term) := do
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let mut fieldTypes := #[]
    for i in [:ctorInfo.numFields] do
      let x := xs[ctorInfo.numParams + i]!
      fieldTypes := fieldTypes.push (← Term.exprToSyntax (← inferType x))
    return fieldTypes

private def mkSerializeAlt (ctorInfo : ConstructorVal) : TermElabM (TSyntax ``matchAlt) := do
  if ctorInfo.numFields > maxConstructorArity then
    throwError "Serializable deriving supports at most {maxConstructorArity} constructor fields"
  let mut ctorArgs : Array Term := #[]
  for _ in [:ctorInfo.numParams] do
    ctorArgs := ctorArgs.push (← `(_))
  let mut fields : Array Term := #[]
  for _ in [:ctorInfo.numFields] do
    let a := mkIdent (← mkFreshUserName `a)
    ctorArgs := ctorArgs.push a
    fields := fields.push a
  let pat ← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*)
  let fn := mkCIdent (serializeCtorName ctorInfo.numFields)
  let tag := quote ctorInfo.cidx
  let rhs ← `($fn $tag $fields:term*)
  `(matchAltExpr| | $pat:term => $rhs)

private def mkSerializeBody (indVal : InductiveVal) : TermElabM Term := do
  let x := mkIdent (← mkFreshUserName `x)
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    alts := alts.push (← mkSerializeAlt ctorInfo)
  `(fun $x => match $x:ident with $alts:matchAlt*)

private def mkCtorValue (ctorInfo : ConstructorVal) (payloadName : Name) : TermElabM Term := do
  let mut args := #[]
  let payload := mkIdent payloadName
  for i in [:ctorInfo.numFields] do
    args := args.push (← mkTupleProj payload i ctorInfo.numFields)
  `($(mkIdent ctorInfo.name) $args:term*)

private def mkDeserializeBranch (ctorInfo : ConstructorVal) (valueName : Name) (rest : Term) :
    TermElabM Term := do
  if ctorInfo.numFields > maxConstructorArity then
    throwError "Serializable deriving supports at most {maxConstructorArity} constructor fields"
  let v := mkIdent valueName
  let payloadName ← mkFreshUserName `payload
  let payload := mkIdent payloadName
  let fn := mkCIdent (deserializeCtorName ctorInfo.numFields)
  let tag := quote ctorInfo.cidx
  let ctorValue ← mkCtorValue ctorInfo payloadName
  `(match ($fn $tag $v) with
    | some $payload => some $ctorValue
    | none => $rest)

private def mkDeserializeBody (indVal : InductiveVal) : TermElabM Term := do
  let vName ← mkFreshUserName `v
  let mut body ← `(none)
  for ctorName in indVal.ctors.reverse do
    let ctorInfo ← getConstInfoCtor ctorName
    body ← mkDeserializeBranch ctorInfo vName body
  `(fun $(mkIdent vName) => $body)

private def mkSerializableInstance (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  if indVal.numIndices != 0 then
    throwError "Serializable deriving does not support indexed inductives"
  let cmd ← liftTermElabM do
    let header ← mkHeader ``Serializable 0 indVal
    let serializeBody ← mkSerializeBody indVal
    let deserializeBody ← mkDeserializeBody indVal
    `(
      instance $header.binders:bracketedBinder* :
          $(mkCIdent ``Serializable) $header.targetType where
        serialize := $serializeBody
        deserialize := $deserializeBody
        deserialize_serialize := by
          intro x
          cases x <;> simp [
            serialize_constructor0,
            serialize_constructor1,
            serialize_constructor2,
            serialize_constructor3,
            serialize_constructor4,
            serialize_constructor5,
            serialize_constructor6,
            deserialize_constructor0,
            deserialize_constructor1,
            deserialize_constructor2,
            deserialize_constructor3,
            deserialize_constructor4,
            deserialize_constructor5,
            deserialize_constructor6,
            deserialize_constructor_payload,
            deserialize_serialize,
            deserialize_constructor0_serialize_constructor0,
            deserialize_constructor1_serialize_constructor1,
            deserialize_constructor2_serialize_constructor2,
            deserialize_constructor3_serialize_constructor3,
            deserialize_constructor4_serialize_constructor4,
            deserialize_constructor5_serialize_constructor5,
            deserialize_constructor6_serialize_constructor6,
            deserialize_constructor7_serialize_constructor7,
            deserialize_constructor8_serialize_constructor8,
            deserialize_constructor9_serialize_constructor9,
            deserialize_constructor10_serialize_constructor10
          ])
  elabCommand cmd

def mkSerializableInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then
    return false
  if !(← declNames.allM isInductive) then
    return false
  for declName in declNames do
    mkSerializableInstance declName
  return true

end Internal

initialize
  registerDerivingHandler ``ConCert.Execution.SerializableBase.Serializable
    Internal.mkSerializableInstanceHandler

end ConCert.Execution.SerializableDerive
