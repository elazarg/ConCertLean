/- Port of execution/theories/SerializableBase.v -/

import ConCert.Execution.Monad
import ConCert.Execution.OptionMonad
import ConCert.Execution.Containers
import ConCert.Execution.BoundedN

namespace ConCert.Execution.SerializableBase

inductive SerializedType where
  | ser_unit : SerializedType
  | ser_int  : SerializedType
  | ser_bool : SerializedType
  | ser_pair : SerializedType → SerializedType → SerializedType
  | ser_list : SerializedType → SerializedType

namespace SerializedType

def eqb : SerializedType → SerializedType → Bool
  | ser_unit, ser_unit => true
  | ser_int, ser_int => true
  | ser_bool, ser_bool => true
  | ser_pair a1 a2, ser_pair b1 b2 => eqb a1 b1 && eqb a2 b2
  | ser_list a, ser_list b => eqb a b
  | _, _ => false

instance eq_dec : ∀ (a b : SerializedType), Decidable (a = b)
  | .ser_unit, .ser_unit => .isTrue rfl
  | .ser_int, .ser_int => .isTrue rfl
  | .ser_bool, .ser_bool => .isTrue rfl
  | .ser_pair a1 a2, .ser_pair b1 b2 =>
    match eq_dec a1 b1, eq_dec a2 b2 with
    | .isTrue h1, .isTrue h2 => .isTrue (by subst h1; subst h2; rfl)
    | .isFalse h, _ => .isFalse (fun heq => by injection heq; contradiction)
    | _, .isFalse h => .isFalse (fun heq => by injection heq; contradiction)
  | .ser_list a, .ser_list b =>
    match eq_dec a b with
    | .isTrue h => .isTrue (by subst h; rfl)
    | .isFalse h => .isFalse (fun heq => by injection heq; contradiction)
  | .ser_unit, .ser_int => .isFalse (fun h => by injection h)
  | .ser_unit, .ser_bool => .isFalse (fun h => by injection h)
  | .ser_unit, .ser_pair _ _ => .isFalse (fun h => by injection h)
  | .ser_unit, .ser_list _ => .isFalse (fun h => by injection h)
  | .ser_int, .ser_unit => .isFalse (fun h => by injection h)
  | .ser_int, .ser_bool => .isFalse (fun h => by injection h)
  | .ser_int, .ser_pair _ _ => .isFalse (fun h => by injection h)
  | .ser_int, .ser_list _ => .isFalse (fun h => by injection h)
  | .ser_bool, .ser_unit => .isFalse (fun h => by injection h)
  | .ser_bool, .ser_int => .isFalse (fun h => by injection h)
  | .ser_bool, .ser_pair _ _ => .isFalse (fun h => by injection h)
  | .ser_bool, .ser_list _ => .isFalse (fun h => by injection h)
  | .ser_pair _ _, .ser_unit => .isFalse (fun h => by injection h)
  | .ser_pair _ _, .ser_int => .isFalse (fun h => by injection h)
  | .ser_pair _ _, .ser_bool => .isFalse (fun h => by injection h)
  | .ser_pair _ _, .ser_list _ => .isFalse (fun h => by injection h)
  | .ser_list _, .ser_unit => .isFalse (fun h => by injection h)
  | .ser_list _, .ser_int => .isFalse (fun h => by injection h)
  | .ser_list _, .ser_bool => .isFalse (fun h => by injection h)
  | .ser_list _, .ser_pair _ _ => .isFalse (fun h => by injection h)

theorem eqb_spec :
  ∀ (a b : SerializedType), (eqb a b = true) ↔ (a = b) := by
  intro a
  induction a with
  | ser_unit => intro b; cases b <;> simp [eqb]
  | ser_int => intro b; cases b <;> simp [eqb]
  | ser_bool => intro b; cases b <;> simp [eqb]
  | ser_pair a1 a2 ih1 ih2 =>
      intro b
      cases b <;> simp [eqb]
      case ser_pair b1 b2 =>
        simp [ih1 b1, ih2 b2]
  | ser_list a ih =>
      intro b
      cases b <;> simp [eqb]
      case ser_list b => exact ih b

end SerializedType

def interp_type : SerializedType → Type
  | .ser_unit       => Unit
  | .ser_int        => Int
  | .ser_bool       => Bool
  | .ser_pair a b   => interp_type a × interp_type b
  | .ser_list a     => List (interp_type a)

structure SerializedValue where
  ser_value_type : SerializedType
  ser_value      : interp_type ser_value_type

theorem SerializedValue.eta (v : SerializedValue) :
    ({ ser_value_type := v.ser_value_type, ser_value := v.ser_value } : SerializedValue) = v := by
  cases v
  rfl

private def interp_type_decidableEq : (t : SerializedType) → DecidableEq (interp_type t)
  | .ser_unit => by
      change DecidableEq Unit
      infer_instance
  | .ser_int => by
      change DecidableEq Int
      infer_instance
  | .ser_bool => by
      change DecidableEq Bool
      infer_instance
  | .ser_pair a b => by
      change DecidableEq (interp_type a × interp_type b)
      haveI := interp_type_decidableEq a
      haveI := interp_type_decidableEq b
      infer_instance
  | .ser_list a => by
      change DecidableEq (List (interp_type a))
      haveI := interp_type_decidableEq a
      infer_instance

instance SerializedValue.instDecidableEq : DecidableEq SerializedValue := by
  intro x y
  cases x with
  | mk xt xv =>
    cases y with
    | mk yt yv =>
      by_cases ht : xt = yt
      · subst ht
        haveI := interp_type_decidableEq xt
        by_cases hv : xv = yv
        · exact isTrue (by subst hv; rfl)
        · exact isFalse (by
            intro h
            cases h
            exact hv rfl)
      · exact isFalse (by
          intro h
          injection h with ht'
          exact ht ht')

/-- Cast a `SerializedValue` to `interp_type t` if the tag matches. -/
def extract_ser_value (t : SerializedType) (value : SerializedValue) : Option (interp_type t) :=
  if h : value.ser_value_type = t then
    some (h ▸ value.ser_value)
  else
    none

/-- A type can be serialized into `SerializedValue` and deserialized back,
deserialization being a left inverse of serialization. -/
class Serializable (ty : Type) where
  serialize : ty → SerializedValue
  deserialize : SerializedValue → Option ty
  deserialize_serialize : ∀ x, deserialize (serialize x) = some x

export Serializable (serialize deserialize deserialize_serialize)

class SerializableComplete (ty : Type) [inst : Serializable ty] : Prop where
  complete : ∀ e : ty, @deserialize ty inst (@serialize ty inst e) = some e

class SerializableSound (ty : Type) [inst : Serializable ty] : Prop where
  sound : ∀ (e : SerializedValue) (a : ty),
    @deserialize ty inst e = some a → @serialize ty inst a = e

instance SerializableComplete_Serializable (A : Type) [inst : Serializable A] :
    SerializableComplete A where
  complete := @deserialize_serialize A inst

theorem serialize_injective :
  ∀ {T : Type} [Serializable T] (x y : T),
    serialize x = serialize y → x = y := by
  intro T inst x y h
  have hs : some x = some y := by
    rw [← Serializable.deserialize_serialize x, ← Serializable.deserialize_serialize y, h]
  injection hs

end ConCert.Execution.SerializableBase
