/- Port of execution/theories/SerializableSound.v. -/

import ConCert.Execution.Monad
import ConCert.Execution.OptionMonad
import ConCert.Execution.Containers
import ConCert.Execution.BoundedN
import ConCert.Execution.SerializableBase
import ConCert.Execution.SerializableInstances

namespace ConCert.Execution.SerializableSound

open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances
open ConCert.Execution.BoundedN

theorem deserialize_unit_sound :
  ∀ (x : SerializedValue) (y : Unit),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change unit_serializable.deserialize x = some y at h
  cases y
  cases x with
  | mk ty val =>
      cases ty
      · cases val; rfl
      · cases h
      · cases h
      · cases h
      · cases h

instance SerializableSound_unit : SerializableSound Unit where
  sound e a h := (deserialize_unit_sound e a h).symm

theorem deserialize_Z_sound :
  ∀ (x : SerializedValue) (y : Int),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change int_serializable.deserialize x = some y at h
  cases x with
  | mk ty val =>
      cases ty
      · cases h
      · injection h with hy; subst hy; rfl
      · cases h
      · cases h
      · cases h

instance SerializableSound_Z : SerializableSound Int where
  sound e a h := (deserialize_Z_sound e a h).symm

theorem deserialize_bool_sound :
  ∀ (x : SerializedValue) (y : Bool),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change bool_serializable.deserialize x = some y at h
  cases x with
  | mk ty val =>
      cases ty
      · cases h
      · cases h
      · injection h with hy; subst hy; rfl
      · cases h
      · cases h

instance SerializableSound_bool : SerializableSound Bool where
  sound e a h := (deserialize_bool_sound e a h).symm

theorem deserialize_nat_sound :
  ∀ (x : SerializedValue) (y : Nat),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change nat_serializable.deserialize x = some y at h
  cases x with
  | mk ty val =>
      cases ty
      · cases h
      · change Int at val
        change (let i' : Int := val; if i' < 0 then none else some i'.toNat) = some y at h
        by_cases hneg : val < 0
        · simp [hneg] at h
        · simp [hneg] at h
          subst y
          have hcast : (val.toNat : Int) = val := Int.toNat_of_nonneg (by omega)
          change ({ ser_value_type := SerializedType.ser_int, ser_value := val } : SerializedValue) =
            ({ ser_value_type := SerializedType.ser_int, ser_value := (val.toNat : Int) } : SerializedValue)
          rw [hcast]
      · cases h
      · cases h
      · cases h

instance SerializableSound_nat : SerializableSound Nat where
  sound e a h := (deserialize_nat_sound e a h).symm

theorem deserialize_positive_sound :
  ∀ (x : SerializedValue) (y : Positive),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change deserialize_positive x = some y at h
  cases x with
  | mk ty val =>
      cases ty
      · cases h
      · change Int at val
        by_cases hpos : 0 < val
        · simp [deserialize_positive, hpos] at h
          cases h
          have hcast : (val.toNat : Int) = val := Int.toNat_of_nonneg (by omega)
          change ({ ser_value_type := SerializedType.ser_int, ser_value := val } : SerializedValue) =
            ({ ser_value_type := SerializedType.ser_int, ser_value := (val.toNat : Int) } : SerializedValue)
          rw [hcast]
        · simp [deserialize_positive, hpos] at h
      · cases h
      · cases h
      · cases h

instance SerializableSound_positive : SerializableSound Positive where
  sound e a h := (deserialize_positive_sound e a h).symm

theorem deserialize_boundedN_sound {bound : Nat} :
  ∀ (x : SerializedValue) (y : BoundedN bound),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change BoundedN_equivalence.deserialize x = some y at h
  unfold BoundedN_equivalence at h ⊢
  simp only at h ⊢
  cases hp : (deserialize x : Option Positive)
  · simp [hp] at h
  · rename_i p
    simp [hp] at h
    have hx : x = serialize p := deserialize_positive_sound x p hp
    have hy : BoundedN.to_N y = decode_N p := BoundedN.of_N_some h
    have hpencode : encode_bounded y = p := by
      unfold encode_bounded
      rw [hy]
      exact encode_decode_N p
    rw [hx, hpencode]

instance SerializableSound_boundedN {bound : Nat} : SerializableSound (BoundedN bound) where
  sound e a h := (deserialize_boundedN_sound e a h).symm

theorem deserialize_SerializedValue_sound :
  ∀ (x y : SerializedValue),
    deserialize x = some y → x = serialize y := by
  intro x y h
  cases h
  rfl

instance SerializableSound_SerializedValue : SerializableSound SerializedValue where
  sound e a h := (deserialize_SerializedValue_sound e a h).symm

theorem deserialize_sum_sound :
  ∀ {A B : Type} [Serializable A] [Serializable B]
    (x : SerializedValue) (y : Sum A B),
    (∀ x' (y' : A), deserialize x' = some y' → x' = serialize y') →
    (∀ x' (y' : B), deserialize x' = some y' → x' = serialize y') →
    deserialize x = some y → x = serialize y := by
  intro A B _ _ x y HA HB h
  change deserialize_sum x = some y at h
  change x = serialize_sum y
  cases x with
  | mk ty val =>
      cases ty
      · cases h
      · cases h
      · cases h
      · rename_i ty1 ty2
        cases ty1
        · cases h
        · cases h
        · rcases val with ⟨tag, payload⟩
          change Bool at tag
          cases tag
          · change ((deserialize ({ ser_value_type := ty2, ser_value := payload } : SerializedValue) :
                Option B).map Sum.inr) = some y at h
            cases hb : (deserialize ({ ser_value_type := ty2, ser_value := payload } : SerializedValue) :
                Option B) <;> simp [hb] at h
            rename_i b
            cases h
            change serialize_tagged false ({ ser_value_type := ty2, ser_value := payload } : SerializedValue) =
              serialize_tagged false (serialize b)
            rw [HB ⟨ty2, payload⟩ b hb]
          · change ((deserialize ({ ser_value_type := ty2, ser_value := payload } : SerializedValue) :
                Option A).map Sum.inl) = some y at h
            cases ha : (deserialize ({ ser_value_type := ty2, ser_value := payload } : SerializedValue) :
                Option A) <;> simp [ha] at h
            rename_i a
            cases h
            change serialize_tagged true ({ ser_value_type := ty2, ser_value := payload } : SerializedValue) =
              serialize_tagged true (serialize a)
            rw [HA ⟨ty2, payload⟩ a ha]
        · cases h
        · cases h
      · cases h

instance SerializableSound_sum
  {A B : Type} [Serializable A] [Serializable B]
  [SerializableSound A] [SerializableSound B] : SerializableSound (Sum A B) where
  sound e a h :=
    (deserialize_sum_sound e a
      (fun x' y' hy' => (SerializableSound.sound x' y' hy').symm)
      (fun x' y' hy' => (SerializableSound.sound x' y' hy').symm)
      h).symm

theorem deserialize_product_sound :
  ∀ {A B : Type} [Serializable A] [Serializable B]
    (x : SerializedValue) (y : A × B),
    (∀ x' (y' : A), deserialize x' = some y' → x' = serialize y') →
    (∀ x' (y' : B), deserialize x' = some y' → x' = serialize y') →
    deserialize x = some y → x = serialize y := by
  intro A B _ _ x y HA HB h
  change deserialize_product x = some y at h
  change x = serialize_product y
  cases x with
  | mk ty val =>
      cases ty <;> try (simp [deserialize_product] at h)
      rename_i ta tb
      rcases val with ⟨va, vb⟩
      cases haOpt : (deserialize ({ ser_value_type := ta, ser_value := va } : SerializedValue) : Option A) <;>
        simp [haOpt] at h
      rename_i a
      cases hbOpt : (deserialize ({ ser_value_type := tb, ser_value := vb } : SerializedValue) : Option B) <;>
        simp [hbOpt] at h
      rename_i b
      cases h
      change serialize_pair_value ({ ser_value_type := ta, ser_value := va } : SerializedValue)
          ({ ser_value_type := tb, ser_value := vb } : SerializedValue) =
        serialize_pair_value (serialize a) (serialize b)
      rw [HA ⟨ta, va⟩ a haOpt, HB ⟨tb, vb⟩ b hbOpt]

instance SerializableSound_product
  {A B : Type} [Serializable A] [Serializable B]
  [SerializableSound A] [SerializableSound B] : SerializableSound (A × B) where
  sound e a h :=
    (deserialize_product_sound e a
      (fun x' y' hy' => (SerializableSound.sound x' y' hy').symm)
      (fun x' y' hy' => (SerializableSound.sound x' y' hy').symm)
      h).symm

theorem deserialize_list_aux_sound
  {A : Type} [Serializable A]
  (HA : ∀ x' (l' : A), deserialize x' = some l' → x' = serialize l') :
    ∀ (ty : SerializedType) (val : interp_type ty) (l : List A),
      deserialize_list_aux ty val = some l →
      ({ ser_value_type := ty, ser_value := val } : SerializedValue) = serialize_list l := by
  intro ty
  induction ty with
  | ser_unit =>
      intro val l h
      cases val
      cases l with
      | nil => rfl
      | cons _ _ => cases h
  | ser_int =>
      intro _ _ h
      cases h
  | ser_bool =>
      intro _ _ h
      cases h
  | ser_pair hd_ty tl_ty _ ihTl =>
      intro val l h
      rcases val with ⟨hd_val, tl_val⟩
      change (match (deserialize ({ ser_value_type := hd_ty, ser_value := hd_val } : SerializedValue) : Option A),
          (deserialize_list_aux tl_ty tl_val : Option (List A)) with
        | some hd, some tl => some (hd :: tl)
        | _, _ => none) = some l at h
      cases hHead : (deserialize ({ ser_value_type := hd_ty, ser_value := hd_val } : SerializedValue) : Option A)
      · rw [hHead] at h
        cases h
      · rename_i hd
        cases hTail : (deserialize_list_aux tl_ty tl_val : Option (List A))
        · rw [hHead, hTail] at h
          cases h
        · rename_i tl
          rw [hHead, hTail] at h
          cases h
          change serialize_pair_value ({ ser_value_type := hd_ty, ser_value := hd_val } : SerializedValue)
              ({ ser_value_type := tl_ty, ser_value := tl_val } : SerializedValue) =
            serialize_pair_value (serialize hd) (serialize_list tl)
          rw [HA ⟨hd_ty, hd_val⟩ hd hHead, ihTl tl_val tl hTail]
  | ser_list _ _ =>
      intro _ _ h
      cases h

theorem deserialize_list_sound :
  ∀ {A : Type} [Serializable A] (l : List A) (x : SerializedValue),
    (∀ x' (l' : A), deserialize x' = some l' → x' = serialize l') →
    deserialize x = some l → x = serialize l := by
  intro A _ l x HA h
  change deserialize_list x = some l at h
  cases x with
  | mk ty val =>
      exact deserialize_list_aux_sound HA ty val l h

instance SerializableSound_list
  {A : Type} [Serializable A] [SerializableSound A] : SerializableSound (List A) where
  sound e a h :=
    (deserialize_list_sound a e
      (fun x' y' hy' => (SerializableSound.sound x' y' hy').symm)
      h).symm

theorem deserialize_option_sound :
  ∀ {A : Type} [Serializable A] (x : SerializedValue) (y : Option A),
    (∀ x' (y' : A), deserialize x' = some y' → x' = serialize y') →
    deserialize x = some y → x = serialize y := by
  intro A _ x y HA h
  change deserialize_option x = some y at h
  change x = serialize_option y
  unfold deserialize_option at h
  cases hs : (deserialize_sum x : Option (Sum Unit A)) <;> simp [hs] at h
  rename_i s
  have hx : x = serialize_sum s :=
    deserialize_sum_sound x s deserialize_unit_sound HA hs
  cases s with
  | inl u =>
      cases u
      cases h
      simpa [serialize_option, option_to_sum] using hx
  | inr a =>
      cases h
      simpa [serialize_option, option_to_sum] using hx

instance SerializableSound_option
  {A : Type} [Serializable A] [SerializableSound A] : SerializableSound (Option A) where
  sound e a h :=
    (deserialize_option_sound e a
      (fun x' y' hy' => (SerializableSound.sound x' y' hy').symm)
      h).symm

theorem deserialize_ascii_sound :
  ∀ (x : SerializedValue) (y : Ascii),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change deserialize_ascii x = some y at h
  unfold deserialize_ascii at h
  cases hn : (deserialize x : Option Nat) <;> simp [hn, Ascii.ofNat?] at h
  rename_i n
  rcases h with ⟨_, hy⟩
  cases hy
  exact deserialize_nat_sound x n hn

instance SerializableSound_ascii : SerializableSound Ascii where
  sound e a h := (deserialize_ascii_sound e a h).symm

theorem deserialize_ascii_string_sound :
  ∀ (x : SerializedValue) (y : AsciiString),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change deserialize_ascii_string x = some y at h
  unfold deserialize_ascii_string at h
  cases hl : (deserialize x : Option (List Ascii)) <;> simp [hl] at h
  rename_i chars
  cases h
  exact deserialize_list_sound chars x deserialize_ascii_sound hl

instance SerializableSound_ascii_string : SerializableSound AsciiString where
  sound e a h := (deserialize_ascii_string_sound e a h).symm

theorem map_toNat_ofNat_eq_self_of_validNats :
    ∀ cs, validNats cs = true → (cs.map Char.ofNat).map Char.toNat = cs := by
  intro cs
  induction cs with
  | nil => simp [validNats]
  | cons n ns ih =>
      intro h
      simp [validNats] at h
      have htail : validNats ns = true := by
        rw [validNats, List.all_eq_true]
        intro x hx
        exact decide_eq_true (h.2 x hx)
      simp [Char.toNat_ofNat_of_isValid h.1, ih htail]

theorem deserialize_string_sound :
  ∀ (x : SerializedValue) (y : String),
    deserialize x = some y → x = serialize y := by
  intro x y h
  change deserialize_string x = some y at h
  change x = serialize_string y
  unfold deserialize_string at h
  cases hlist : (deserialize x : Option (List Nat)) <;> simp [hlist] at h
  rename_i cs
  cases hv : validNats cs <;> simp [hv] at h
  cases h
  have hx : x = serialize cs := deserialize_list_sound cs x deserialize_nat_sound hlist
  rw [hx]
  unfold serialize_string
  rw [String.toList_ofList]
  rw [map_toNat_ofNat_eq_self_of_validNats cs hv]

instance SerializableSound_string : SerializableSound String where
  sound e a h := (deserialize_string_sound e a h).symm

end ConCert.Execution.SerializableSound
