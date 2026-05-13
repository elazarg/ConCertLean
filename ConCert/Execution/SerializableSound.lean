/- Port of execution/theories/SerializableSound.v
   All contents are soundness lemmas + instances; axiomatized here. -/

import ConCert.Execution.Monad
import ConCert.Execution.OptionMonad
import ConCert.Execution.Containers
import ConCert.Execution.BoundedN
import ConCert.Execution.SerializableBase
import ConCert.Execution.SerializableInstances

namespace ConCert.Execution.SerializableSound

open ConCert.Execution.SerializableBase

axiom deserialize_unit_sound :
  ∀ (x : SerializedValue) (y : Unit),
    deserialize x = some y → x = serialize y

axiom SerializableSound_unit : SerializableSound Unit
attribute [instance] SerializableSound_unit

axiom deserialize_Z_sound :
  ∀ (x : SerializedValue) (y : Int),
    deserialize x = some y → x = serialize y

axiom SerializableSound_Z : SerializableSound Int
attribute [instance] SerializableSound_Z

axiom deserialize_bool_sound :
  ∀ (x : SerializedValue) (y : Bool),
    deserialize x = some y → x = serialize y

axiom SerializableSound_bool : SerializableSound Bool
attribute [instance] SerializableSound_bool

axiom deserialize_nat_sound :
  ∀ (x : SerializedValue) (y : Nat),
    deserialize x = some y → x = serialize y

axiom SerializableSound_nat : SerializableSound Nat
attribute [instance] SerializableSound_nat

axiom deserialize_SerializedValue_sound :
  ∀ (x y : SerializedValue),
    deserialize x = some y → x = serialize y

axiom SerializableSound_SerializedValue : SerializableSound SerializedValue
attribute [instance] SerializableSound_SerializedValue

axiom deserialize_sum_sound :
  ∀ {A B : Type} [Serializable A] [Serializable B]
    (x : SerializedValue) (y : Sum A B),
    (∀ x' (y' : A), deserialize x' = some y' → x' = serialize y') →
    (∀ x' (y' : B), deserialize x' = some y' → x' = serialize y') →
    deserialize x = some y → x = serialize y

axiom SerializableSound_sum :
  ∀ {A B : Type} [Serializable A] [Serializable B]
    [SerializableSound A] [SerializableSound B], SerializableSound (Sum A B)
attribute [instance] SerializableSound_sum

axiom deserialize_product_sound :
  ∀ {A B : Type} [Serializable A] [Serializable B]
    (x : SerializedValue) (y : A × B),
    (∀ x' (y' : A), deserialize x' = some y' → x' = serialize y') →
    (∀ x' (y' : B), deserialize x' = some y' → x' = serialize y') →
    deserialize x = some y → x = serialize y

axiom SerializableSound_product :
  ∀ {A B : Type} [Serializable A] [Serializable B]
    [SerializableSound A] [SerializableSound B], SerializableSound (A × B)
attribute [instance] SerializableSound_product

axiom deserialize_list_sound :
  ∀ {A : Type} [Serializable A] (l : List A) (x : SerializedValue),
    (∀ x' (l' : A), deserialize x' = some l' → x' = serialize l') →
    deserialize x = some l → x = serialize l

axiom SerializableSound_list :
  ∀ {A : Type} [Serializable A] [SerializableSound A], SerializableSound (List A)
attribute [instance] SerializableSound_list

axiom deserialize_option_sound :
  ∀ {A : Type} [Serializable A] (x : SerializedValue) (y : Option A),
    (∀ x' (y' : A), deserialize x' = some y' → x' = serialize y') →
    deserialize x = some y → x = serialize y

axiom SerializableSound_option :
  ∀ {A : Type} [Serializable A] [SerializableSound A], SerializableSound (Option A)
attribute [instance] SerializableSound_option

axiom deserialize_string_sound :
  ∀ (x : SerializedValue) (y : String),
    deserialize x = some y → x = serialize y

axiom SerializableSound_string : SerializableSound String
attribute [instance] SerializableSound_string

end ConCert.Execution.SerializableSound
