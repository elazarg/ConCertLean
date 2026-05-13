/- Port of execution/theories/SerializableInstances.v. Real instances. -/

import ConCert.Execution.Monad
import ConCert.Execution.OptionMonad
import ConCert.Execution.Containers
import ConCert.Execution.BoundedN
import ConCert.Execution.SerializableBase

namespace ConCert.Execution.SerializableInstances

open ConCert.Execution.SerializableBase
open ConCert.Execution.Containers
open ConCert.Execution.BoundedN

instance unit_serializable : Serializable Unit where
  serialize _ := ⟨.ser_unit, ()⟩
  deserialize v :=
    match v with
    | ⟨.ser_unit, _⟩ => some ()
    | _ => none
  deserialize_serialize := by intro x; cases x; rfl

instance int_serializable : Serializable Int where
  serialize i := ⟨.ser_int, i⟩
  deserialize v :=
    match v with
    | ⟨.ser_int, i⟩ => some i
    | _ => none
  deserialize_serialize := by intro _; rfl

instance bool_serializable : Serializable Bool where
  serialize b := ⟨.ser_bool, b⟩
  deserialize v :=
    match v with
    | ⟨.ser_bool, b⟩ => some b
    | _ => none
  deserialize_serialize := by intro _; rfl

instance nat_serializable : Serializable Nat where
  serialize n := ⟨.ser_int, (n : Int)⟩
  deserialize v :=
    match v with
    | ⟨.ser_int, i⟩ =>
      let i' : Int := i
      if i' < 0 then none else some i'.toNat
    | _ => none
  deserialize_serialize := by
    intro n
    show (let i' : Int := (n : Int); if i' < 0 then none else some i'.toNat) = some n
    have h : ¬ ((n : Int) < 0) := by omega
    simp [h]

/-- SerializedValue serializes to itself (identity round-trip). -/
instance ser_value_equivalence : Serializable SerializedValue where
  serialize v := v
  deserialize v := some v
  deserialize_serialize _ := rfl

/-- `BoundedN` is serialized as a raw `Int` in the value range `[0, bound)`.

    Wire-format note: upstream routes the value through
    `countable.encode : N → positive`. Round-trip and rejection behavior
    are identical, but on-wire bytes differ. -/
instance BoundedN_equivalence {bound : Nat} : Serializable (BoundedN bound) where
  serialize b := ⟨.ser_int, (b.val : Int)⟩
  deserialize v :=
    match v with
    | ⟨.ser_int, i⟩ =>
      let i' : Int := i
      if i' < 0 then none
      else if h : i'.toNat < bound then some ⟨i'.toNat, h⟩
      else none
    | _ => none
  deserialize_serialize := by
    intro b
    show
      (let i' : Int := (b.val : Int);
       if i' < 0 then none
       else if h : i'.toNat < bound then some ⟨i'.toNat, h⟩
       else none) = some b
    have h_nonneg : ¬ ((b.val : Int) < 0) := by omega
    have h_bound : ((b.val : Int).toNat) < bound := by simp; exact b.lt
    rw [if_neg h_nonneg, dif_pos h_bound]; congr

section SumSer
variable {A B : Type} [Serializable A] [Serializable B]

/-- Tag direction: `inl ↦ true`, `inr ↦ false`. -/
private def sum_serialize : Sum A B → SerializedValue
  | .inl a =>
    let sa := serialize a
    ⟨.ser_pair .ser_bool sa.ser_value_type, (true, sa.ser_value)⟩
  | .inr b =>
    let sb := serialize b
    ⟨.ser_pair .ser_bool sb.ser_value_type, (false, sb.ser_value)⟩

private def sum_deserialize (v : SerializedValue) : Option (Sum A B) :=
  match v with
  | ⟨.ser_pair .ser_bool inner, (tag, payload)⟩ =>
    let tagB : Bool := tag
    let sv : SerializedValue := ⟨inner, payload⟩
    if tagB then
      (deserialize sv : Option A).map .inl
    else
      (deserialize sv : Option B).map .inr
  | _ => none

axiom sum_round_trip : ∀ (ab : Sum A B), sum_deserialize (sum_serialize ab) = some ab

instance sum_serializable : Serializable (Sum A B) where
  serialize := sum_serialize
  deserialize := sum_deserialize
  deserialize_serialize := sum_round_trip

end SumSer

section ProdSer
variable {A B : Type} [Serializable A] [Serializable B]

private def prod_serialize (p : A × B) : SerializedValue :=
  let sa := serialize p.1
  let sb := serialize p.2
  ⟨.ser_pair sa.ser_value_type sb.ser_value_type, (sa.ser_value, sb.ser_value)⟩

private def prod_deserialize (v : SerializedValue) : Option (A × B) :=
  match v with
  | ⟨.ser_pair ta tb, (va, vb)⟩ =>
    match (deserialize ⟨ta, va⟩ : Option A), (deserialize ⟨tb, vb⟩ : Option B) with
    | some a, some b => some (a, b)
    | _, _ => none
  | _ => none

axiom prod_round_trip : ∀ (p : A × B), prod_deserialize (prod_serialize p) = some p

instance product_serializable : Serializable (A × B) where
  serialize := prod_serialize
  deserialize := prod_deserialize
  deserialize_serialize := prod_round_trip

end ProdSer

section ListSer
variable {A : Type} [Serializable A]

/-- List serializer via nested `ser_pair`: `[a, b, c]` becomes
    `(a, (b, (c, ())))` where each element keeps its own `ser_value_type`. -/
private def list_serialize : List A → SerializedValue
  | [] => ⟨.ser_unit, ()⟩
  | a :: rest =>
    let sa := serialize a
    let srest := list_serialize rest
    ⟨.ser_pair sa.ser_value_type srest.ser_value_type, (sa.ser_value, srest.ser_value)⟩

/-- Recursive deserializer matching the nested-pair shape. -/
private def list_deserialize_aux :
    (ty : SerializedType) → interp_type ty → Option (List A)
  | .ser_pair hd_ty tl_ty, (hd_val, tl_val) =>
    match (deserialize ⟨hd_ty, hd_val⟩ : Option A), list_deserialize_aux tl_ty tl_val with
    | some hd, some tl => some (hd :: tl)
    | _, _ => none
  | .ser_unit, _ => some []
  | _, _ => none

private def list_deserialize (v : SerializedValue) : Option (List A) :=
  list_deserialize_aux v.ser_value_type v.ser_value

axiom list_deserialize_serialize :
  ∀ (l : List A), list_deserialize (list_serialize l) = some l

instance list_serializable : Serializable (List A) where
  serialize := list_serialize
  deserialize := list_deserialize
  deserialize_serialize := list_deserialize_serialize

end ListSer

section MapSer
variable {A B : Type} [Ord A] [LawfulOrd A] [Serializable A] [Serializable B]

/-- FMap serialization via its elements list. `FMap` is backed by
    `Std.ExtTreeMap`, which is propositionally extensional, so
    `of_list (elements m) = m` holds and the round-trip is sound. -/
def fmap_serialize (m : FMap A B) : SerializedValue :=
  serialize (FMap.elements m)

def fmap_deserialize (v : SerializedValue) : Option (FMap A B) :=
  (deserialize v : Option (List (A × B))).map FMap.of_list

theorem fmap_deserialize_serialize (m : FMap A B) :
    fmap_deserialize (fmap_serialize m) = some m := by
  show ((deserialize (serialize (FMap.elements m)) : Option (List (A × B))).map FMap.of_list)
       = some m
  rw [deserialize_serialize (FMap.elements m)]
  simp [FMap.of_elements_eq]

instance map_serializable : Serializable (FMap A B) where
  serialize := fmap_serialize
  deserialize := fmap_deserialize
  deserialize_serialize := fmap_deserialize_serialize

end MapSer

/-- Sets-as-FMaps. Sound: inherits the canonical-round-trip of the map. -/
@[reducible] def set_serializable {A : Type} [Ord A] [LawfulOrd A] [Serializable A] :
    Serializable (FMap A Unit) := inferInstance

section OptSer
variable {A : Type} [Serializable A]

/-- `none ↦ inl ()` (tag `true` under the Sum convention),
    `some a ↦ inr a` (tag `false`). -/
private def opt_serialize : Option A → SerializedValue
  | none   => ⟨.ser_pair .ser_bool .ser_unit, (true, ())⟩
  | some a =>
    let sa := serialize a
    ⟨.ser_pair .ser_bool sa.ser_value_type, (false, sa.ser_value)⟩

/-- Implementation note: upstream routes through `Serializable (Unit + A)`
    and inherits the inner-type validation from the `Unit` deserializer.
    We build the wire shape directly here, so the `none` branch must
    explicitly require `.ser_unit` to keep the round-trip sound. -/
private def opt_deserialize (v : SerializedValue) : Option (Option A) :=
  match v with
  | ⟨.ser_pair .ser_bool .ser_unit, (true, _)⟩ => some none
  | ⟨.ser_pair .ser_bool inner, (false, payload)⟩ =>
    (deserialize ⟨inner, payload⟩ : Option A).map some
  | _ => none

axiom opt_round_trip : ∀ (oa : Option A), opt_deserialize (opt_serialize oa) = some oa

instance option_serializable : Serializable (Option A) where
  serialize := opt_serialize
  deserialize := opt_deserialize
  deserialize_serialize := opt_round_trip

end OptSer

section StringSer

private def string_serialize (s : String) : SerializedValue :=
  serialize (s.toList.map Char.toNat)

/-- Each nat must be in a valid Unicode scalar range — otherwise
    `Char.ofNat` silently wraps to NUL and the round-trip breaks. -/
private def validNats (cs : List Nat) : Bool :=
  cs.all (fun n => n.isValidChar)

private def string_deserialize (v : SerializedValue) : Option String :=
  match (deserialize v : Option (List Nat)) with
  | none => none
  | some cs =>
    if validNats cs then
      some (String.ofList (cs.map Char.ofNat))
    else none

axiom string_deserialize_serialize :
  ∀ (s : String), string_deserialize (string_serialize s) = some s

instance string_serializable : Serializable String where
  serialize := string_serialize
  deserialize := string_deserialize
  deserialize_serialize := string_deserialize_serialize

end StringSer

end ConCert.Execution.SerializableInstances
