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

/-! ### Positive / stdpp-countable compatibility

Rocq's `BoundedN` instance serializes through `stdpp.countable.encode`, whose
`N` instance maps `n` to the positive integer `n + 1`. The wrapper below gives
Lean a small explicit counterpart for that positive layer. -/

structure Positive where
  val : Nat
  is_pos : 0 < val

namespace Positive

def ofNat? (n : Nat) : Option Positive :=
  if h : 0 < n then some ⟨n, h⟩ else none

def predNat (p : Positive) : Nat := p.val - 1

theorem ofNat?_val (p : Positive) : ofNat? p.val = some p := by
  cases p with
  | mk val is_pos =>
      simp [ofNat?, is_pos]

theorem predNat_encodeNat (n : Nat) : predNat ⟨n + 1, by omega⟩ = n := by
  simp [predNat]

end Positive

def serialize_positive (p : Positive) : SerializedValue :=
  ⟨.ser_int, (p.val : Int)⟩

def deserialize_positive (v : SerializedValue) : Option Positive :=
  match v with
  | ⟨.ser_int, i⟩ =>
      let i' : Int := i
      if h : 0 < i' then
        some ⟨i'.toNat, by
          have hi : 0 ≤ i' := by omega
          have hcast : (i'.toNat : Int) = i' := Int.toNat_of_nonneg hi
          omega⟩
      else
        none
  | _ => none

theorem deserialize_serialize_positive (p : Positive) :
    deserialize_positive (serialize_positive p) = some p := by
  cases p with
  | mk val is_pos =>
      have hpos : 0 < (val : Int) := by omega
      unfold serialize_positive deserialize_positive
      simp only
      rw [dif_pos hpos]
      congr

instance positive_serializable : Serializable Positive where
  serialize := serialize_positive
  deserialize := deserialize_positive
  deserialize_serialize := deserialize_serialize_positive

def encode_N (n : Nat) : Positive :=
  ⟨n + 1, by omega⟩

def decode_N (p : Positive) : Nat :=
  p.predNat

theorem decode_encode_N (n : Nat) : decode_N (encode_N n) = n := by
  simp [decode_N, encode_N, Positive.predNat]

theorem encode_decode_N (p : Positive) : encode_N (decode_N p) = p := by
  cases p with
  | mk val is_pos =>
      unfold encode_N decode_N Positive.predNat
      rw [Positive.mk.injEq]
      change val - 1 + 1 = val
      omega

def encode_bounded {bound : Nat} (n : BoundedN bound) : Positive :=
  encode_N (BoundedN.to_N n)

def decode_bounded {bound : Nat} (p : Positive) : Option (BoundedN bound) :=
  BoundedN.of_N (decode_N p)

theorem decode_encode_bounded {bound : Nat} (n : BoundedN bound) :
    decode_bounded (encode_bounded n) = some n := by
  simpa [decode_bounded, encode_bounded, decode_encode_N] using
    (BoundedN.of_to_N n)

/-- Rocq-compatible `BoundedN` serialization.

    Upstream routes the value through `countable.encode : N → positive`.
    Since stdpp encodes `N` as `n + 1`, the serialized integer for value `n`
    is positive and equal to `n + 1`, not raw `n`. -/
instance BoundedN_equivalence {bound : Nat} : Serializable (BoundedN bound) where
  serialize b := serialize (encode_bounded b)
  deserialize v :=
    (deserialize v : Option Positive).bind decode_bounded
  deserialize_serialize := by
    intro b
    show Option.bind ((deserialize (serialize (encode_bounded b)) : Option Positive))
        decode_bounded = some b
    rw [deserialize_serialize (encode_bounded b)]
    exact decode_encode_bounded b

def serialize_pair_value (a b : SerializedValue) : SerializedValue :=
  ⟨.ser_pair a.ser_value_type b.ser_value_type, (a.ser_value, b.ser_value)⟩

def serialize_tagged (tag : Bool) (payload : SerializedValue) : SerializedValue :=
  ⟨.ser_pair .ser_bool payload.ser_value_type, (tag, payload.ser_value)⟩

section SumSer
variable {A B : Type} [Serializable A] [Serializable B]

/-- Tag direction: `inl ↦ true`, `inr ↦ false`. -/
def serialize_sum : Sum A B → SerializedValue
  | .inl a => serialize_tagged true (serialize a)
  | .inr b => serialize_tagged false (serialize b)

def deserialize_sum (v : SerializedValue) : Option (Sum A B) :=
  match v with
  | ⟨.ser_pair .ser_bool inner, (tag, payload)⟩ =>
    let tagB : Bool := tag
    let sv : SerializedValue := ⟨inner, payload⟩
    if tagB then
      (deserialize sv : Option A).map .inl
    else
      (deserialize sv : Option B).map .inr
  | _ => none

theorem deserialize_serialize_sum :
    ∀ (ab : Sum A B), deserialize_sum (serialize_sum ab) = some ab := by
  intro ab
  cases ab with
  | inl a =>
      simp only [serialize_sum, deserialize_sum, serialize_tagged]
      rw [SerializedValue.eta (serialize a), deserialize_serialize a]
      rfl
  | inr b =>
      simp only [serialize_sum, deserialize_sum, serialize_tagged]
      rw [SerializedValue.eta (serialize b), deserialize_serialize b]
      rfl

theorem sum_round_trip :
    ∀ (ab : Sum A B), deserialize_sum (serialize_sum ab) = some ab :=
  deserialize_serialize_sum

instance sum_serializable : Serializable (Sum A B) where
  serialize := serialize_sum
  deserialize := deserialize_sum
  deserialize_serialize := sum_round_trip

end SumSer

section ProdSer
variable {A B : Type} [Serializable A] [Serializable B]

def serialize_product (p : A × B) : SerializedValue :=
  serialize_pair_value (serialize p.1) (serialize p.2)

def deserialize_product (v : SerializedValue) : Option (A × B) :=
  match v with
  | ⟨.ser_pair ta tb, (va, vb)⟩ =>
    match (deserialize ⟨ta, va⟩ : Option A), (deserialize ⟨tb, vb⟩ : Option B) with
    | some a, some b => some (a, b)
    | _, _ => none
  | _ => none

theorem deserialize_serialize_product :
    ∀ (p : A × B), deserialize_product (serialize_product p) = some p := by
  intro p
  cases p with
  | mk a b =>
      simp only [serialize_product, deserialize_product, serialize_pair_value]
      rw [SerializedValue.eta (serialize a), SerializedValue.eta (serialize b)]
      rw [deserialize_serialize a, deserialize_serialize b]

theorem prod_round_trip :
    ∀ (p : A × B), deserialize_product (serialize_product p) = some p :=
  deserialize_serialize_product

instance product_serializable : Serializable (A × B) where
  serialize := serialize_product
  deserialize := deserialize_product
  deserialize_serialize := prod_round_trip

end ProdSer

section ListSer
variable {A : Type} [Serializable A]

/-- List serializer via nested `ser_pair`: `[a, b, c]` becomes
    `(a, (b, (c, ())))` where each element keeps its own `ser_value_type`. -/
def serialize_list : List A → SerializedValue
  | [] => ⟨.ser_unit, ()⟩
  | a :: rest =>
    serialize_pair_value (serialize a) (serialize_list rest)

/-- Recursive deserializer matching the nested-pair shape. -/
def deserialize_list_aux :
    (ty : SerializedType) → interp_type ty → Option (List A)
  | .ser_pair hd_ty tl_ty, (hd_val, tl_val) =>
    match (deserialize ⟨hd_ty, hd_val⟩ : Option A), deserialize_list_aux tl_ty tl_val with
    | some hd, some tl => some (hd :: tl)
    | _, _ => none
  | .ser_unit, _ => some []
  | _, _ => none

def deserialize_list (v : SerializedValue) : Option (List A) :=
  deserialize_list_aux v.ser_value_type v.ser_value

theorem deserialize_serialize_list :
    ∀ (l : List A), deserialize_list (serialize_list l) = some l := by
  intro l
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      unfold serialize_list deserialize_list
      simp only [serialize_pair_value, deserialize_list_aux]
      rw [SerializedValue.eta (serialize hd), deserialize_serialize hd]
      rw [show deserialize_list_aux (serialize_list tl).ser_value_type
          (serialize_list tl).ser_value = deserialize_list (serialize_list tl) by rfl]
      rw [ih]

theorem list_deserialize_serialize :
    ∀ (l : List A), deserialize_list (serialize_list l) = some l :=
  deserialize_serialize_list

instance list_serializable : Serializable (List A) where
  serialize := serialize_list
  deserialize := deserialize_list
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
def option_to_sum : Option A → Sum Unit A
  | none => .inl ()
  | some a => .inr a

def option_of_sum : Sum Unit A → Option A
  | .inl _ => none
  | .inr a => some a

def serialize_option (oa : Option A) : SerializedValue :=
  serialize_sum (option_to_sum oa)

def deserialize_option (v : SerializedValue) : Option (Option A) :=
  (deserialize_sum v : Option (Sum Unit A)).map option_of_sum

theorem deserialize_serialize_option :
    ∀ (oa : Option A), deserialize_option (serialize_option oa) = some oa := by
  intro oa
  cases oa <;> simp [serialize_option, deserialize_option, option_to_sum,
    option_of_sum, deserialize_serialize_sum]

theorem opt_round_trip :
    ∀ (oa : Option A), deserialize_option (serialize_option oa) = some oa :=
  deserialize_serialize_option

instance option_serializable : Serializable (Option A) where
  serialize := serialize_option
  deserialize := deserialize_option
  deserialize_serialize := opt_round_trip

end OptSer

/-! ### Rocq ASCII strings and Lean Unicode strings -/

structure Ascii where
  val : Nat
  lt : val < 256

namespace Ascii

def toNat (a : Ascii) : Nat := a.val

def ofNat? (n : Nat) : Option Ascii :=
  if h : n < 256 then some ⟨n, h⟩ else none

theorem of_toNat (a : Ascii) : ofNat? a.toNat = some a := by
  cases a with
  | mk val lt =>
      simp [ofNat?, toNat, lt]

end Ascii

def serialize_ascii (a : Ascii) : SerializedValue :=
  serialize a.toNat

def deserialize_ascii (v : SerializedValue) : Option Ascii :=
  (deserialize v : Option Nat).bind Ascii.ofNat?

theorem deserialize_serialize_ascii (a : Ascii) :
    deserialize_ascii (serialize_ascii a) = some a := by
  simp [serialize_ascii, deserialize_ascii, Ascii.of_toNat, deserialize_serialize]

instance ascii_serializable : Serializable Ascii where
  serialize := serialize_ascii
  deserialize := deserialize_ascii
  deserialize_serialize := deserialize_serialize_ascii

structure AsciiString where
  data : List Ascii

namespace AsciiString

def toString (s : AsciiString) : String :=
  String.ofList (s.data.map (fun a => Char.ofNat a.val))

def ofString? (s : String) : Option AsciiString :=
  (s.toList.mapM (fun c => Ascii.ofNat? c.toNat)).map (fun cs => ⟨cs⟩)

end AsciiString

def serialize_ascii_string (s : AsciiString) : SerializedValue :=
  serialize s.data

def deserialize_ascii_string (v : SerializedValue) : Option AsciiString :=
  (deserialize v : Option (List Ascii)).map (fun cs => ⟨cs⟩)

theorem deserialize_serialize_ascii_string (s : AsciiString) :
    deserialize_ascii_string (serialize_ascii_string s) = some s := by
  cases s
  simp [serialize_ascii_string, deserialize_ascii_string, deserialize_serialize]

instance ascii_string_serializable : Serializable AsciiString where
  serialize := serialize_ascii_string
  deserialize := deserialize_ascii_string
  deserialize_serialize := deserialize_serialize_ascii_string

section StringSer

def serialize_string (s : String) : SerializedValue :=
  serialize (s.toList.map Char.toNat)

/-- Each nat must be in a valid Unicode scalar range — otherwise
    `Char.ofNat` silently wraps to NUL and the round-trip breaks. -/
def validNats (cs : List Nat) : Bool :=
  cs.all (fun n => n.isValidChar)

def deserialize_string (v : SerializedValue) : Option String :=
  match (deserialize v : Option (List Nat)) with
  | none => none
  | some cs =>
    if validNats cs then
      some (String.ofList (cs.map Char.ofNat))
    else none

theorem validNats_toNat (s : String) :
    validNats (s.toList.map Char.toNat) = true := by
  rw [validNats, List.all_eq_true]
  intro n hn
  rcases List.mem_map.mp hn with ⟨c, _, rfl⟩
  exact decide_eq_true (Char.valid c)

theorem Char.toNat_ofNat_of_isValid {n : Nat} (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

theorem string_deserialize_serialize :
    ∀ (s : String), deserialize_string (serialize_string s) = some s := by
  intro s
  unfold serialize_string deserialize_string
  rw [deserialize_serialize (s.toList.map Char.toNat)]
  simp [validNats_toNat, List.map_map, Function.comp_def, Char.ofNat_toNat,
    String.ofList_toList]

instance string_serializable : Serializable String where
  serialize := serialize_string
  deserialize := deserialize_string
  deserialize_serialize := string_deserialize_serialize

end StringSer

/-! ### Rocq `Derive Ser` constructor-wire helpers

The Rocq deriving tactic serializes every constructor as a pair containing a
zero-based `Nat` tag and a `SerializedValue` payload. Constructor arguments are
stored in the payload as a right-associated chain
`(arg₁, (arg₂, ... (argₙ, ()) ...))`, where the tail is itself serialized as a
`SerializedValue`.

These helpers expose that wire shape directly so handwritten Lean instances can
match the original derived encoding without duplicating the nested product
plumbing. -/

section ConstructorWire

def serialize_constructor0 (tag : Nat) : SerializedValue :=
  serialize (tag, (serialize () : SerializedValue))

def serialize_constructor1 {A : Type} [Serializable A] (tag : Nat) (a : A) :
    SerializedValue :=
  serialize (tag, serialize (a, (serialize () : SerializedValue)))

def serialize_constructor2 {A B : Type} [Serializable A] [Serializable B]
    (tag : Nat) (a : A) (b : B) : SerializedValue :=
  serialize (tag, serialize (a, serialize (b, (serialize () : SerializedValue))))

def serialize_constructor3 {A B C : Type}
    [Serializable A] [Serializable B] [Serializable C]
    (tag : Nat) (a : A) (b : B) (c : C) : SerializedValue :=
  serialize (tag,
    serialize (a, serialize (b, serialize (c, (serialize () : SerializedValue)))))

def serialize_constructor4 {A B C D : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D]
    (tag : Nat) (a : A) (b : B) (c : C) (d : D) : SerializedValue :=
  serialize (tag,
    serialize (a,
      serialize (b,
        serialize (c, serialize (d, (serialize () : SerializedValue))))))

def serialize_constructor5 {A B C D E : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    (tag : Nat) (a : A) (b : B) (c : C) (d : D) (e : E) : SerializedValue :=
  serialize (tag,
    serialize (a,
      serialize (b,
        serialize (c,
          serialize (d, serialize (e, (serialize () : SerializedValue)))))))

def serialize_constructor6 {A B C D E F : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    [Serializable F]
    (tag : Nat) (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) :
    SerializedValue :=
  serialize (tag,
    serialize (a,
      serialize (b,
        serialize (c,
          serialize (d,
            serialize (e, serialize (f, (serialize () : SerializedValue))))))))

def deserialize_constructor_payload (expectedTag : Nat) (v : SerializedValue) :
    Option SerializedValue := do
  let pair ← (deserialize v : Option (Nat × SerializedValue))
  let tag := pair.1
  let payload := pair.2
  if tag = expectedTag then
    some payload
  else
    none

def deserialize_constructor0 (expectedTag : Nat) (v : SerializedValue) : Option Unit := do
  let payload ← deserialize_constructor_payload expectedTag v
  deserialize payload

def deserialize_constructor1 {A : Type} [Serializable A]
    (expectedTag : Nat) (v : SerializedValue) : Option A := do
  let payload ← deserialize_constructor_payload expectedTag v
  let pair ← (deserialize payload : Option (A × SerializedValue))
  let _unit ← (deserialize pair.2 : Option Unit)
  let a := pair.1
  pure a

def deserialize_constructor2 {A B : Type} [Serializable A] [Serializable B]
    (expectedTag : Nat) (v : SerializedValue) : Option (A × B) := do
  let payload ← deserialize_constructor_payload expectedTag v
  let pairA ← (deserialize payload : Option (A × SerializedValue))
  let pairB ← (deserialize pairA.2 : Option (B × SerializedValue))
  let _unit ← (deserialize pairB.2 : Option Unit)
  let a := pairA.1
  let b := pairB.1
  pure (a, b)

def deserialize_constructor3 {A B C : Type}
    [Serializable A] [Serializable B] [Serializable C]
    (expectedTag : Nat) (v : SerializedValue) : Option (A × B × C) := do
  let payload ← deserialize_constructor_payload expectedTag v
  let pairA ← (deserialize payload : Option (A × SerializedValue))
  let pairB ← (deserialize pairA.2 : Option (B × SerializedValue))
  let pairC ← (deserialize pairB.2 : Option (C × SerializedValue))
  let _unit ← (deserialize pairC.2 : Option Unit)
  let a := pairA.1
  let b := pairB.1
  let c := pairC.1
  pure (a, b, c)

def deserialize_constructor4 {A B C D : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D]
    (expectedTag : Nat) (v : SerializedValue) : Option (A × B × C × D) := do
  let payload ← deserialize_constructor_payload expectedTag v
  let pairA ← (deserialize payload : Option (A × SerializedValue))
  let pairB ← (deserialize pairA.2 : Option (B × SerializedValue))
  let pairC ← (deserialize pairB.2 : Option (C × SerializedValue))
  let pairD ← (deserialize pairC.2 : Option (D × SerializedValue))
  let _unit ← (deserialize pairD.2 : Option Unit)
  let a := pairA.1
  let b := pairB.1
  let c := pairC.1
  let d := pairD.1
  pure (a, b, c, d)

def deserialize_constructor5 {A B C D E : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    (expectedTag : Nat) (v : SerializedValue) : Option (A × B × C × D × E) := do
  let payload ← deserialize_constructor_payload expectedTag v
  let pairA ← (deserialize payload : Option (A × SerializedValue))
  let pairB ← (deserialize pairA.2 : Option (B × SerializedValue))
  let pairC ← (deserialize pairB.2 : Option (C × SerializedValue))
  let pairD ← (deserialize pairC.2 : Option (D × SerializedValue))
  let pairE ← (deserialize pairD.2 : Option (E × SerializedValue))
  let _unit ← (deserialize pairE.2 : Option Unit)
  let a := pairA.1
  let b := pairB.1
  let c := pairC.1
  let d := pairD.1
  let e := pairE.1
  pure (a, b, c, d, e)

def deserialize_constructor6 {A B C D E F : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    [Serializable F]
    (expectedTag : Nat) (v : SerializedValue) : Option (A × B × C × D × E × F) := do
  let payload ← deserialize_constructor_payload expectedTag v
  let pairA ← (deserialize payload : Option (A × SerializedValue))
  let pairB ← (deserialize pairA.2 : Option (B × SerializedValue))
  let pairC ← (deserialize pairB.2 : Option (C × SerializedValue))
  let pairD ← (deserialize pairC.2 : Option (D × SerializedValue))
  let pairE ← (deserialize pairD.2 : Option (E × SerializedValue))
  let pairF ← (deserialize pairE.2 : Option (F × SerializedValue))
  let _unit ← (deserialize pairF.2 : Option Unit)
  let a := pairA.1
  let b := pairB.1
  let c := pairC.1
  let d := pairD.1
  let e := pairE.1
  let f := pairF.1
  pure (a, b, c, d, e, f)

theorem deserialize_constructor0_serialize_constructor0 (expectedTag tag : Nat) :
    deserialize_constructor0 expectedTag (serialize_constructor0 tag) =
      if tag = expectedTag then some () else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor0, serialize_constructor0, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor0, serialize_constructor0, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_constructor1_serialize_constructor1 {A : Type} [Serializable A]
    (expectedTag tag : Nat) (a : A) :
    deserialize_constructor1 expectedTag (serialize_constructor1 tag a) =
      if tag = expectedTag then some a else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor1, serialize_constructor1, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor1, serialize_constructor1, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_constructor2_serialize_constructor2 {A B : Type}
    [Serializable A] [Serializable B]
    (expectedTag tag : Nat) (a : A) (b : B) :
    deserialize_constructor2 expectedTag (serialize_constructor2 tag a b) =
      if tag = expectedTag then some (a, b) else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor2, serialize_constructor2, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor2, serialize_constructor2, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_constructor3_serialize_constructor3 {A B C : Type}
    [Serializable A] [Serializable B] [Serializable C]
    (expectedTag tag : Nat) (a : A) (b : B) (c : C) :
    deserialize_constructor3 expectedTag (serialize_constructor3 tag a b c) =
      if tag = expectedTag then some (a, b, c) else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor3, serialize_constructor3, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor3, serialize_constructor3, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_constructor4_serialize_constructor4 {A B C D : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D]
    (expectedTag tag : Nat) (a : A) (b : B) (c : C) (d : D) :
    deserialize_constructor4 expectedTag (serialize_constructor4 tag a b c d) =
      if tag = expectedTag then some (a, b, c, d) else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor4, serialize_constructor4, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor4, serialize_constructor4, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_constructor5_serialize_constructor5 {A B C D E : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    (expectedTag tag : Nat) (a : A) (b : B) (c : C) (d : D) (e : E) :
    deserialize_constructor5 expectedTag (serialize_constructor5 tag a b c d e) =
      if tag = expectedTag then some (a, b, c, d, e) else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor5, serialize_constructor5, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor5, serialize_constructor5, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_constructor6_serialize_constructor6 {A B C D E F : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    [Serializable F]
    (expectedTag tag : Nat) (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) :
    deserialize_constructor6 expectedTag (serialize_constructor6 tag a b c d e f) =
      if tag = expectedTag then some (a, b, c, d, e, f) else none := by
  by_cases h : tag = expectedTag
  · simp [deserialize_constructor6, serialize_constructor6, deserialize_constructor_payload, h,
      deserialize_serialize]
  · simp [deserialize_constructor6, serialize_constructor6, deserialize_constructor_payload, h,
      deserialize_serialize]

theorem deserialize_serialize_constructor0 (tag : Nat) :
    deserialize_constructor0 tag (serialize_constructor0 tag) = some () := by
  simp [deserialize_constructor0_serialize_constructor0]

theorem deserialize_serialize_constructor1 {A : Type} [Serializable A]
    (tag : Nat) (a : A) :
    deserialize_constructor1 tag (serialize_constructor1 tag a) = some a := by
  simp [deserialize_constructor1_serialize_constructor1]

theorem deserialize_serialize_constructor2 {A B : Type} [Serializable A] [Serializable B]
    (tag : Nat) (a : A) (b : B) :
    deserialize_constructor2 tag (serialize_constructor2 tag a b) = some (a, b) := by
  simp [deserialize_constructor2_serialize_constructor2]

theorem deserialize_serialize_constructor3 {A B C : Type}
    [Serializable A] [Serializable B] [Serializable C]
    (tag : Nat) (a : A) (b : B) (c : C) :
    deserialize_constructor3 tag (serialize_constructor3 tag a b c) = some (a, b, c) := by
  simp [deserialize_constructor3_serialize_constructor3]

theorem deserialize_serialize_constructor4 {A B C D : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D]
    (tag : Nat) (a : A) (b : B) (c : C) (d : D) :
    deserialize_constructor4 tag (serialize_constructor4 tag a b c d) =
      some (a, b, c, d) := by
  simp [deserialize_constructor4_serialize_constructor4]

theorem deserialize_serialize_constructor5 {A B C D E : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    (tag : Nat) (a : A) (b : B) (c : C) (d : D) (e : E) :
    deserialize_constructor5 tag (serialize_constructor5 tag a b c d e) =
      some (a, b, c, d, e) := by
  simp [deserialize_constructor5_serialize_constructor5]

theorem deserialize_serialize_constructor6 {A B C D E F : Type}
    [Serializable A] [Serializable B] [Serializable C] [Serializable D] [Serializable E]
    [Serializable F]
    (tag : Nat) (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) :
    deserialize_constructor6 tag (serialize_constructor6 tag a b c d e f) =
      some (a, b, c, d, e, f) := by
  simp [deserialize_constructor6_serialize_constructor6]

end ConstructorWire

end ConCert.Execution.SerializableInstances
