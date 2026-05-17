/- Port of utils/theories/StringExtra.v. Definitions only; no lemmas in source. -/

namespace ConCert.Utils.StringExtra

def strRev (s : String) : String := String.ofList s.toList.reverse

/-- Rocq source-name alias. -/
abbrev str_rev (s : String) : String := strRev s

def hexDigitOfNibble : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

def hex_of_N (n : Nat) : String :=
  if n = 0 then "0" else
    let rec go (n : Nat) (acc : String) : String :=
      if h : n = 0 then acc
      else
        have : n / 16 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
        go (n / 16) (String.singleton (hexDigitOfNibble (n % 16)) ++ acc)
    go n ""

def hex_of_nat (n : Nat) : String := hex_of_N n

/-- Rocq source-name alias. Lean represents `positive` as `Nat` on this surface. -/
def hex_of_positive (p : Nat) : String := hex_of_N p

def hex_of_Z (z : Int) : String :=
  if z = 0 then "0"
  else if z > 0 then hex_of_N z.toNat
  else "-" ++ hex_of_N (-z).toNat

def Nlog2up_nat (n : Nat) : Nat :=
  if n = 0 then 1 else Nat.log2 n + 1

def string_of_N (n : Nat) : String :=
  if n = 0 then "0" else
    let rec go (n : Nat) (acc : String) : String :=
      if h : n = 0 then acc
      else
        have : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
        let d := n % 10
        let c : Char := Char.ofNat (d + '0'.toNat)
        go (n / 10) (String.singleton c ++ acc)
    go n ""

def string_of_nat (n : Nat) : String := string_of_N n

def string_of_positive (p : Nat) : String := string_of_N p

def string_of_Z (z : Int) : String :=
  if z = 0 then "0"
  else if z > 0 then string_of_N z.toNat
  else "-" ++ string_of_N (-z).toNat

def replace_char (orig : Char) (newC : Char) (s : String) : String :=
  s.map (fun c => if c == orig then newC else c)

def remove_char (orig : Char) (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c ≠ orig))

def starts_with (withStr : String) (s : String) : Bool :=
  s.startsWith withStr

/-- Rocq source-name alias for the continuation helper. -/
def starts_with_cont (withStr s : String) (k : String → Bool) : Bool :=
  if starts_with withStr s then k (String.ofList (s.toList.drop withStr.length)) else false

/-- `replace "" _ s = s` (no-op on empty pattern). Lean's
    `String.replace` doesn't special-case empty and would insert `newS`
    between every character. -/
def replace (orig : String) (newS : String) (s : String) : String :=
  if orig.isEmpty then s else s.replace orig newS

def substring_from (from_ : Nat) (s : String) : String :=
  String.ofList (s.toList.drop from_)

def substring_count (cnt : Nat) (s : String) : String :=
  String.ofList (s.toList.take cnt)

/-- Deviation: applies `f`. The upstream Coq `str_map` appears to ignore its
    function argument by mistake. -/
def str_map (f : Char → Char) (s : String) : String := s.map f

def last_index_of (c : Char) (s : String) : Option Nat :=
  let rec go (cs : List Char) (i : Nat) (acc : Option Nat) : Option Nat :=
    match cs with
    | [] => acc
    | c' :: rest => go rest (i + 1) (if c' == c then some i else acc)
  go s.toList 0 none

def is_letter (c : Char) : Bool :=
  let n := c.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)

def char_to_upper (c : Char) : Char :=
  if is_letter c then Char.ofNat (c.toNat &&& 0xDF) else c

def char_to_lower (c : Char) : Char :=
  if is_letter c then Char.ofNat (c.toNat ||| 0x20) else c

def to_upper (s : String) : String := str_map char_to_upper s
def to_lower (s : String) : String := str_map char_to_lower s

def capitalize (s : String) : String :=
  match s.toList with
  | []      => ""
  | c :: cs => String.singleton (char_to_upper c) ++ String.ofList cs

def uncapitalize (s : String) : String :=
  match s.toList with
  | []      => ""
  | c :: cs => String.singleton (char_to_lower c) ++ String.ofList cs

def str_split (on : String) (s : String) : List String := s.splitOn on

def lines (l : List String) : String := String.intercalate "\n" l

end ConCert.Utils.StringExtra
