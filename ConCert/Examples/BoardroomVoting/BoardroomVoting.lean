/- Executable port of examples/boardroomVoting/BoardroomVotingZ.v. -/

import Mathlib.Data.Int.GCD
import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Utils.Extras

namespace ConCert.Examples.BoardroomVoting

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances
open ConCert.Utils.Extras

variable [Base : ChainBase]

abbrev HashFunc : Type := List Positive → Positive

structure Params where
  hash : HashFunc
  prime : Int
  generator : Int

abbrev A : Type := Int

def elmeqb (params : Params) (a b : A) : Bool :=
  (a % params.prime) == (b % params.prime)

def mod_inv (a p : Int) : Int :=
  Int.gcdA a p % p

def mod_pow_pos (a : Int) : Nat → Int → Int
  | 0, p => 1 % p
  | n + 1, p => (a * mod_pow_pos a n p) % p

def mod_pow (a x p : Int) : Int :=
  if x < 0 then
    mod_inv (mod_pow_pos a x.natAbs p) p
  else
    mod_pow_pos a x.toNat p

def add_p (params : Params) (a b : A) : A := (a + b) % params.prime
def mul_p (params : Params) (a b : A) : A := (a * b) % params.prime
def inv_p (params : Params) (a : A) : A := mod_inv a params.prime
def pow_p (params : Params) (a e : A) : A := mod_pow a e params.prime
def order (params : Params) : Int := params.prime

structure Setup where
  eligible_voters : AddressMap.AddrMap (Base := Base) Unit
  finish_registration_by : Nat
  finish_commit_by : Option Nat
  finish_vote_by : Nat
  registration_deposit : Amount
  deriving Serializable

structure VoterInfo where
  voter_index : Nat
  vote_hash : Positive
  public_vote : A
  deriving Serializable

structure State where
  owner : Base.Address
  registered_voters : AddressMap.AddrMap (Base := Base) (@VoterInfo)
  public_keys : List A
  setup : @Setup Base
  tally : Option Nat
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

abbrev VoteProof : Type := Int × A × A × A × A × Int × Int × Int × Int

inductive Msg where
  | signup (pk : A) (proof : A × Int)
  | commit_to_vote (hash : Positive)
  | submit_vote (v : A) (proof : VoteProof)
  | tally_votes
  deriving Serializable

def encodeA (a : A) : Positive := encode_N a.natAbs
def encodeNat (n : Nat) : Positive := encode_N n

def hash_sk_data (params : Params) (gv pk : A) (i : Nat) : Positive :=
  params.hash [encodeA params.generator, encodeA gv, encodeA pk, encodeNat i]

def compute_public_key (params : Params) (sk : Int) : A :=
  pow_p params params.generator sk

def secret_key_proof (params : Params) (sk v : Int) (i : Nat) : A × Int :=
  let gv : A := pow_p params params.generator v
  let pk := compute_public_key params sk
  let z := Int.ofNat (hash_sk_data params gv pk i).val
  let r := v - sk * z
  (gv, r)

def verify_secret_key_proof
    (params : Params) (pk : A) (i : Nat) (proof : A × Int) : Bool :=
  let (gv, r) := proof
  let z := Int.ofNat (hash_sk_data params gv pk i).val
  elmeqb params gv
    (mul_p params (pow_p params params.generator r) (pow_p params pk z))

def hash_sv_data
    (params : Params) (i : Nat) (pk rk a1 b1 a2 b2 : A) : Positive :=
  params.hash (encodeNat i :: [pk, rk, a1, b1, a2, b2].map encodeA)

def prod (params : Params) : List A → A
  | [] => 1
  | x :: xs => mul_p params x (prod params xs)

def reconstructed_key (params : Params) (pks : List A) (n : Nat) : A :=
  let lprod := prod params (pks.take n)
  let rprod := inv_p params (prod params (pks.drop (n + 1)))
  mul_p params lprod rprod

def compute_public_vote (params : Params) (rk : A) (sk : Int) (sv : Bool) : A :=
  mul_p params (pow_p params rk sk) (if sv then params.generator else 1)

def secret_vote_proof
    (params : Params) (sk : Int) (rk : A) (sv : Bool) (i : Nat)
    (w r d : Int) : VoteProof :=
  let pk : A := compute_public_key params sk
  let pv : A := compute_public_vote params rk sk sv
  if sv then
    let a1 : A := mul_p params (pow_p params params.generator r) (pow_p params pk d)
    let b1 : A := mul_p params (pow_p params rk r) (pow_p params pv d)
    let a2 : A := pow_p params params.generator w
    let b2 : A := pow_p params rk w
    let c := Int.ofNat (hash_sv_data params i pk rk a1 b1 a2 b2).val
    let d2 := c - d
    let r2 := w - sk * d2
    (w, a1, b1, a2, b2, d, d2, r, r2)
  else
    let a1 := pow_p params params.generator w
    let b1 := pow_p params rk w
    let a2 := mul_p params (pow_p params params.generator r) (pow_p params pk d)
    let pvInv := mul_p params pv (inv_p params params.generator)
    let b2 := mul_p params (pow_p params rk r) (pow_p params pvInv d)
    let c := Int.ofNat (hash_sv_data params i pk rk a1 b1 a2 b2).val
    let d1 := c - d
    let r1 := w - sk * d1
    (w, a1, b1, a2, b2, d1, d, r1, r)

def verify_secret_vote_proof
    (params : Params) (pk rk pv : A) (i : Nat) (proof : VoteProof) : Bool :=
  let (_w, a1, b1, a2, b2, d1, d2, r1, r2) := proof
  let c := hash_sv_data params i pk rk a1 b1 a2 b2
  (Int.ofNat c.val == d1 + d2) &&
    elmeqb params a1
      (mul_p params (pow_p params params.generator r1) (pow_p params pk d1)) &&
    elmeqb params b1
      (mul_p params (pow_p params rk r1) (pow_p params pv d1)) &&
    elmeqb params a2
      (mul_p params (pow_p params params.generator r2) (pow_p params pk d2)) &&
    elmeqb params b2
      (mul_p params (pow_p params rk r2)
        (pow_p params (mul_p params pv (inv_p params params.generator)) d2))

def make_signup_msg (params : Params) (sk v : Int) (i : Nat) : Msg :=
  .signup (compute_public_key params sk) (secret_key_proof params sk v i)

def make_commit_msg
    (params : Params) (pks : List A) (my_index : Nat) (sk : Int) (sv : Bool) : Msg :=
  let pv := compute_public_vote params (reconstructed_key params pks my_index) sk sv
  .commit_to_vote (params.hash [encodeA pv])

def make_vote_msg
    (params : Params) (pks : List A) (my_index : Nat) (sk : Int) (sv : Bool)
    (w r d : Int) : Msg :=
  let rk := reconstructed_key params pks my_index
  .submit_vote (compute_public_vote params rk sk sv)
    (secret_vote_proof params sk rk sv my_index w r d)

def init
    (_params : Params) (_chain : Chain) (ctx : @ContractCallContext Base)
    (setup : @Setup Base) : Result (@State Base) Error :=
  if setup.finish_registration_by < setup.finish_vote_by then
    .Ok
      { owner := ctx.ctx_from,
        registered_voters := AddressMap.empty,
        public_keys := [],
        setup := setup,
        tally := none }
  else
    .Err default_error

def handle_signup
    (params : Params) (pk : A) (prf : A × Int) (state : @State Base)
    (caller : Base.Address) (cur_slot : Nat) (amount : Amount) :
    Result (@State Base) Error :=
  if state.setup.finish_registration_by < cur_slot then
    .Err default_error
  else if (AddressMap.find caller state.setup.eligible_voters).isNone then
    .Err default_error
  else if (AddressMap.find caller state.registered_voters).isSome then
    .Err default_error
  else if !(amount == state.setup.registration_deposit) then
    .Err default_error
  else if !(Int.ofNat state.public_keys.length < order params - 2) then
    .Err default_error
  else
    let index := state.public_keys.length
    if !verify_secret_key_proof params pk index prf then
      .Err default_error
    else
      let inf : VoterInfo :=
        { voter_index := index, vote_hash := encode_N 0, public_vote := 0 }
      .Ok
        { state with
          registered_voters := AddressMap.add caller inf state.registered_voters,
          public_keys := state.public_keys ++ [pk] }

def handle_commit_to_vote
    (hash : Positive) (state : @State Base)
    (caller : Base.Address) (cur_slot : Nat) : Result (@State Base) Error :=
  match state.setup.finish_commit_by with
  | none => .Err default_error
  | some commit_by =>
      if commit_by < cur_slot then
        .Err default_error
      else
        match AddressMap.find caller state.registered_voters with
        | none => .Err default_error
        | some inf =>
            let inf := { inf with vote_hash := hash }
            .Ok
              { state with
                registered_voters := AddressMap.add caller inf state.registered_voters }

def handle_submit_vote
    (params : Params) (v : A) (proof : VoteProof) (state : @State Base)
    (caller : Base.Address) (cur_slot : Nat) : Result (@State Base) Error :=
  if state.setup.finish_vote_by < cur_slot then
    .Err default_error
  else
    match AddressMap.find caller state.registered_voters with
    | none => .Err default_error
    | some inf =>
        let commitOk :=
          match state.setup.finish_commit_by with
          | none => true
          | some _ =>
              let expected := params.hash [encodeA v]
              expected.val == inf.vote_hash.val
        if !commitOk then
          .Err default_error
        else
          let pk := state.public_keys.getD inf.voter_index 0
          let rk := reconstructed_key params state.public_keys inf.voter_index
          if !verify_secret_vote_proof params pk rk v inf.voter_index proof then
            .Err default_error
          else
            let inf := { inf with public_vote := v }
            .Ok
              { state with
                registered_voters := AddressMap.add caller inf state.registered_voters }

def bruteforce_tally_aux (params : Params) : Nat → A → Result Nat Error
  | n, votes_product =>
      if elmeqb params (pow_p params params.generator (Int.ofNat n)) votes_product then
        .Ok n
      else
        match n with
        | 0 => .Err default_error
        | n + 1 => bruteforce_tally_aux params n votes_product

def bruteforce_tally (params : Params) (votes : List A) : Result Nat Error :=
  bruteforce_tally_aux params votes.length (prod params votes)

def handle_tally_votes
    (params : Params) (state : @State Base) (cur_slot : Nat) :
    Result (@State Base) Error :=
  if cur_slot < state.setup.finish_vote_by then
    .Err default_error
  else if state.tally.isSome then
    .Err default_error
  else
    let voters := AddressMap.values state.registered_voters
    if voters.any (fun vi => elmeqb params vi.public_vote 0) then
      .Err default_error
    else
      match bruteforce_tally params (voters.map (fun vi => vi.public_vote)) with
      | .Err e => .Err e
      | .Ok res => .Ok { state with tally := some res }

def receive
    (params : Params) (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match msg with
  | none => .Err default_error
  | some (.signup pk prf) =>
      match handle_signup params pk prf state ctx.ctx_from
          chain.current_slot ctx.ctx_amount with
      | .Ok st => .Ok (st, [])
      | .Err e => .Err e
  | some (.commit_to_vote hash) =>
      match handle_commit_to_vote hash state ctx.ctx_from chain.current_slot with
      | .Ok st => .Ok (st, [])
      | .Err e => .Err e
  | some (.submit_vote v proof) =>
      match handle_submit_vote params v proof state ctx.ctx_from chain.current_slot with
      | .Ok st => .Ok (st, [])
      | .Err e => .Err e
  | some .tally_votes =>
      match handle_tally_votes params state chain.current_slot with
      | .Ok st => .Ok (st, [])
      | .Err e => .Err e

def contract (params : Params) :
    @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init params, receive := receive params }

end ConCert.Examples.BoardroomVoting
