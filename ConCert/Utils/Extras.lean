/- Port of utils/theories/Extras.v. Definitions ported, lemmas axiomatized. -/

import Mathlib.Data.List.Defs
import Mathlib.Data.List.Perm.Basic
import ConCert.Utils.Automation

namespace ConCert.Utils.Extras

open List

def mapOption {A B : Type} (f : A → Option B) : List A → List B
  | []      => []
  | hd :: tl =>
    match f hd with
    | some b => b :: mapOption f tl
    | none   => mapOption f tl

def withDefault {A : Type} (default : A) : Option A → A
  | some v => v
  | none   => default

def unpackOption {A : Type} : (a : Option A) →
    (match a with | some _ => A | none => Unit)
  | some x => x
  | none   => ()

def sumZ {A : Type} (f : A → Int) : List A → Int
  | []        => 0
  | x :: xs'  => f x + sumZ f xs'

def sumNat {A : Type} (f : A → Nat) : List A → Nat
  | []        => 0
  | x :: xs'  => f x + sumNat f xs'

def sumN {A : Type} (f : A → Nat) : List A → Nat
  | []        => 0
  | x :: xs'  => f x + sumN f xs'

axiom sumnat_permutation :
  ∀ {A : Type} {f : A → Nat} {xs ys : List A},
    List.Perm xs ys → sumNat f xs = sumNat f ys

axiom sumnat_map :
  ∀ {A B : Type} (f : A → B) (g : B → Nat) (xs : List A),
    sumNat g (xs.map f) = sumNat (fun a => g (f a)) xs

axiom sumZ_permutation :
  ∀ {A : Type} {f : A → Int} {xs ys : List A},
    List.Perm xs ys → sumZ f xs = sumZ f ys

axiom sumZ_app :
  ∀ {A : Type} {f : A → Int} {xs ys : List A},
    sumZ f (xs ++ ys) = sumZ f xs + sumZ f ys

axiom sumZ_map :
  ∀ {A B : Type} (f : A → B) (g : B → Int) (xs : List A),
    sumZ g (xs.map f) = sumZ (fun a => g (f a)) xs

axiom sumZ_filter :
  ∀ {A : Type} (f : A → Int) (pred : A → Bool) (xs : List A),
    sumZ f (xs.filter pred) = sumZ (fun a => if pred a then f a else 0) xs

axiom sumZ_mul :
  ∀ (f : Int → Int) (l : List Int) (z : Int),
    z * sumZ f l = sumZ (fun z' => z * f z') l

axiom incl_split :
  ∀ {A : Type} (l m n : List A),
    (l ++ m).Subset n → l.Subset n ∧ m.Subset n

axiom NoDup_incl_reorganize :
  ∀ {A : Type} (l l' : List A),
    l'.Nodup → l'.Subset l → ∃ suf, List.Perm (l' ++ suf) l

axiom in_NoDup_app :
  ∀ {A : Type} (x : A) (l m : List A),
    x ∈ l → (l ++ m).Nodup → x ∉ m

axiom seq_app :
  ∀ (start len1 len2 : Nat),
    List.range' start (len1 + len2) = List.range' start len1 ++ List.range' (start + len1) len2

axiom forall_respects_permutation :
  ∀ {A : Type} (xs ys : List A) (P : A → Prop),
    List.Perm xs ys → xs.Forall P → ys.Forall P

axiom Forall_false_filter_nil :
  ∀ {A : Type} (pred : A → Bool) (l : List A),
    (l.Forall (fun a => pred a = false)) → l.filter pred = []

axiom Forall_app :
  ∀ {A : Type} (P : A → Prop) (l l' : List A),
    (l.Forall P ∧ l'.Forall P) ↔ (l ++ l').Forall P

axiom filter_app :
  ∀ {A : Type} (pred : A → Bool) (l l' : List A),
    (l ++ l').filter pred = l.filter pred ++ l'.filter pred

axiom filter_map :
  ∀ {A B : Type} (f : A → B) (pred : B → Bool) (l : List A),
    (l.map f).filter pred = (l.filter (fun a => pred (f a))).map f

axiom filter_false :
  ∀ {A : Type} (l : List A), l.filter (fun _ => false) = []

axiom filter_true :
  ∀ {A : Type} (l : List A), l.filter (fun _ => true) = l

axiom Permutation_filter :
  ∀ {A : Type} (pred : A → Bool) (l l' : List A),
    List.Perm l l' → List.Perm (l.filter pred) (l'.filter pred)

def zip {X Y} : List X → List Y → List (X × Y)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | _, _ => []

axiom zip_app :
  ∀ {X Y : Type} (xs xs' : List X) (ys ys' : List Y),
    xs.length = ys.length →
    zip (xs ++ xs') (ys ++ ys') = zip xs ys ++ zip xs' ys'

axiom zip_map :
  ∀ {A B C D : Type} (f : A → B) (g : C → D) (xs : List A) (ys : List C),
    zip (xs.map f) (ys.map g) = (zip xs ys).map (fun p => (f p.1, g p.2))

axiom existsb_forallb :
  ∀ {A : Type} (f : A → Bool) (l : List A),
    l.any f = !(l.all (fun x => !(f x)))

def All {A : Type} (f : A → Prop) : List A → Prop
  | []      => True
  | x :: xs => f x ∧ All f xs

axiom All_app :
  ∀ {A : Type} (f : A → Prop) (l l' : List A),
    All f (l ++ l') ↔ All f l ∧ All f l'

axiom All_map :
  ∀ {A B : Type} (g : B → Prop) (f : A → B) (l : List A),
    All g (l.map f) ↔ All (fun a => g (f a)) l

axiom All_ext_in :
  ∀ {A : Type} (f g : A → Prop) (l : List A),
    All f l → (∀ a, a ∈ l → f a → g a) → All g l

axiom sumZ_seq_n :
  ∀ (f : Nat → Int) (n len : Nat),
    sumZ f (List.range' n len) = sumZ (fun i => f (i + n)) (List.range' 0 len)

axiom sumZ_zero :
  ∀ {A : Type} (l : List A), sumZ (fun _ => 0) l = 0

axiom sumZ_seq_feq :
  ∀ (f g : Nat → Int) (len : Nat),
    (∀ i, i < len → f i = g i) →
    sumZ g (List.range' 0 len) = sumZ f (List.range' 0 len)

axiom sumZ_firstn :
  ∀ {A : Type} (default : A) (f : A → Int) (n : Nat) (l : List A),
    (n ≤ l.length ∨ f default = 0) →
    sumZ f (l.take n) = sumZ (fun i => f (l.getD i default)) (List.range' 0 n)

axiom sumZ_skipn :
  ∀ {A : Type} (default : A) (f : A → Int) (n : Nat) (l : List A),
    sumZ f (l.drop n) =
      sumZ (fun i => f (l.getD (n + i) default)) (List.range' 0 (l.length - n))

axiom sumZ_add :
  ∀ {A : Type} (f g : A → Int) (l : List A),
    sumZ (fun a => f a + g a) l = sumZ f l + sumZ g l

axiom sumZ_sub :
  ∀ {A : Type} (f g : A → Int) (l : List A),
    sumZ (fun a => f a - g a) l = sumZ f l - sumZ g l

axiom sumZ_seq_split :
  ∀ (split_len : Nat) (f : Nat → Int) (start len : Nat),
    split_len ≤ len →
    sumZ f (List.range' start len) =
      sumZ f (List.range' start split_len) +
      sumZ f (List.range' (start + split_len) (len - split_len))

axiom sumZ_sumZ_swap :
  ∀ {A B : Type} (f : A → B → Int) (xs : List A) (ys : List B),
    sumZ (fun a => sumZ (f a) ys) xs = sumZ (fun b => sumZ (fun a => f a b) xs) ys

axiom All_Forall :
  ∀ {A : Type} (l : List A) (f : A → Prop), All f l ↔ l.Forall f

axiom all_incl :
  ∀ {A : Type} (l l' : List A) (f : A → Prop),
    l.Subset l' → All f l' → All f l

axiom firstn_incl :
  ∀ {A : Type} (n : Nat) (l : List A), (l.take n).Subset l

axiom skipn_incl :
  ∀ {A : Type} (n : Nat) (l : List A), (l.drop n).Subset l

axiom sumZ_map_id :
  ∀ {A : Type} (f : A → Int) (l : List A),
    sumZ f l = sumZ id (l.map f)

axiom sumZ_le :
  ∀ {A : Type} (f g : A → Int) (xs : List A),
    (∀ x, x ∈ xs → f x ≤ g x) → sumZ f xs ≤ sumZ g xs

axiom sumZ_nonnegative :
  ∀ {A : Type} (f : A → Int) (l : List A),
    (∀ x, x ∈ l → 0 ≤ f x) → 0 ≤ sumZ f l

axiom sumZ_eq :
  ∀ {A : Type} (f g : A → Int) (l : List A),
    (∀ x, x ∈ l → f x = g x) → sumZ f l = sumZ g l

axiom sumZ_in_le :
  ∀ {A : Type} (x : A) (f : A → Int) (l : List A),
    (∀ y, y ∈ l → 0 ≤ f y) → x ∈ l → f x ≤ sumZ f l

axiom firstn_map :
  ∀ {A B : Type} (f : A → B) (n : Nat) (l : List A),
    (l.map f).take n = (l.take n).map f

axiom skipn_map :
  ∀ {A B : Type} (f : A → B) (n : Nat) (l : List A),
    (l.map f).drop n = (l.drop n).map f

axiom map_nth_alt :
  ∀ {A B : Type} (n : Nat) (l : List A) (f : A → B) (d1 : B) (d2 : A),
    n < l.length → (l.map f).getD n d1 = f (l.getD n d2)

axiom sumnat_max :
  ∀ {A : Type} (f : A → Nat) (l : List A) (m : Nat),
    (∀ a, a ∈ l → f a ≤ m) → sumNat f l ≤ m * l.length

axiom list_eq_nth :
  ∀ {A : Type} (xs ys : List A),
    xs.length = ys.length →
    (∀ (i : Nat) (a a' : A),
      (xs[i]? : Option A) = some a → (ys[i]? : Option A) = some a' → a = a') →
    xs = ys

axiom nth_error_seq_in :
  ∀ (i start len : Nat),
    i < len → (List.range' start len)[i]? = some (start + i)

axiom nth_error_snoc :
  ∀ {B : Type} (l : List B) (x : B),
    (l ++ [x])[l.length]? = some x

axiom NoDup_filter :
  ∀ {A : Type} (f : A → Bool) (l : List A),
    l.Nodup → (l.filter f).Nodup

axiom NoDup_map :
  ∀ {A B : Type} (f : A → B) (l : List A),
    l.Nodup → (∀ a a', a ∈ l → a' ∈ l → f a = f a' → a = a') → (l.map f).Nodup

axiom filter_all :
  ∀ {A : Type} (f : A → Bool) (l : List A),
    (∀ a, a ∈ l → f a = true) → l.filter f = l

axiom sumN_permutation :
  ∀ {A : Type} {f : A → Nat} {xs ys : List A},
    List.Perm xs ys → sumN f xs = sumN f ys

axiom sumN_map :
  ∀ {A B : Type} (f : A → B) (g : B → Nat) (xs : List A),
    sumN g (xs.map f) = sumN (fun a => g (f a)) xs

axiom sumN_map_id :
  ∀ {A : Type} (f : A → Nat) (l : List A),
    sumN f l = sumN id (l.map f)

axiom sumN_app :
  ∀ {A : Type} {f : A → Nat} {xs ys : List A},
    sumN f (xs ++ ys) = sumN f xs + sumN f ys

axiom sumN_split :
  ∀ {A : Type} (f : A → Nat) (x y z : A) (xs : List A),
    f z = f x + f y → sumN f (z :: xs) = sumN f (x :: y :: xs)

axiom sumN_swap :
  ∀ {A : Type} (f : A → Nat) (x y : A) (xs : List A),
    sumN f (x :: y :: xs) = sumN f (y :: x :: xs)

axiom sumN_in_le :
  ∀ {A : Type} (f : A → Nat) (x : A) (xs : List A),
    x ∈ xs → f x ≤ sumN f xs

axiom sumN_inv :
  ∀ {A : Type} (f : A → Nat) (x : A) (xs : List A),
    sumN f xs + f x = sumN f (x :: xs)

def isSome {A : Type} : Option A → Bool
  | some _ => true
  | none   => false

def isNone {A : Type} : Option A → Bool
  | some _ => false
  | none   => true

axiom with_default_is_some :
  ∀ {A : Type} (x : Option A) (y : A),
    isSome x = false → withDefault y x = y

axiom with_default_indep :
  ∀ {A : Type} (o : Option A) (d d' v : A),
    o = some v → withDefault d o = withDefault d' o

axiom isSome_some :
  ∀ {A : Type} (x : Option A) (y : A),
    x = some y → isSome x = true

axiom isSome_none :
  ∀ {A : Type} (x : Option A),
    x = none → isSome x = false

axiom isSome_exists :
  ∀ {A : Type} (x : Option A),
    isSome x = true ↔ ∃ y : A, x = some y

axiom isSome_not_exists :
  ∀ {A : Type} (x : Option A),
    isSome x = false ↔ ∀ y : A, x ≠ some y

end ConCert.Utils.Extras
