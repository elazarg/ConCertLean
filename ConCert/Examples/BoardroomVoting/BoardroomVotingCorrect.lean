/- Basic correctness facts for examples/boardroomVoting/BoardroomVotingZ.v. -/

import ConCert.Examples.BoardroomVoting.BoardroomVoting
import ConCert.Execution.BlockchainInduction

namespace ConCert.Examples.BoardroomVoting

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableInstances
open ConCert.Utils.Extras

variable [Base : ChainBase]

structure SecretVoterInfo where
  svi_index : Nat
  svi_sk : Int
  svi_sk_r : Int
  svi_sv : Bool
  svi_sv_w : Int
  svi_sv_r : Int
  svi_sv_d : Int

def MsgAssumption
    (params : Params) (pks : List A)
    (parties : Base.Address → SecretVoterInfo) :
    List (@ContractCallInfo Base Msg) → Prop
  | [] => True
  | call :: calls =>
      let party := parties call.call_from
      (match call.call_msg with
      | some (.signup pk prf) =>
          .signup pk prf =
            make_signup_msg params party.svi_sk party.svi_sk_r party.svi_index
      | some (.submit_vote _ _) =>
          call.call_msg =
            some
              (make_vote_msg params pks party.svi_index party.svi_sk
                party.svi_sv party.svi_sv_w party.svi_sv_r party.svi_sv_d)
      | _ => True) ∧ MsgAssumption params pks parties calls

def signups (calls : List (@ContractCallInfo Base Msg)) :
    List (Base.Address × A) :=
  (calls.filterMap fun call =>
    match call.call_msg with
    | some (.signup pk _) => some (call.call_from, pk)
    | _ => none).reverse

def SignupOrderAssumption
    (pks : List A) (parties : Base.Address → SecretVoterInfo)
    (calls : List (@ContractCallInfo Base Msg)) : Prop :=
  (List.zip (signups calls) (List.range (signups calls).length)).Forall
    (fun ((addr, pk), i) =>
      (parties addr).svi_index = i ∧ pks[i]? = some pk)

def has_tallied (calls : List (@ContractCallInfo Base Msg)) : Bool :=
  calls.any (fun call =>
    match call.call_msg with
    | some .tally_votes => true
    | _ => false)

def sumnat {α : Type} (f : α → Nat) (xs : List α) : Nat :=
  (xs.map f).sum

omit Base in
theorem sumnat_perm {α : Type} (f : α → Nat) {xs ys : List α}
    (hperm : xs.Perm ys) :
    sumnat f xs = sumnat f ys := by
  simpa [sumnat, List.sum_eq_foldr] using
    (List.Perm.foldr_op_eq
      (op := fun x y : Nat => x + y)
      (a := 0)
      (hperm.map f))

class BoardroomVotingProtocolCorrect (params : Params) : Prop where
  order_ge_two : 2 ≤ order params
  bruteforce_tally_correct :
    ∀ {B : Type} (bs : List B)
      (index : B → Nat) (sks : B → Int) (pks : List A)
      (svs : B → Bool) (pvs : B → A),
      Int.ofNat bs.length < order params - 1 →
      List.Perm (bs.map index) (List.range bs.length) →
      pks.length = bs.length →
      (∀ b, b ∈ bs →
        pks[index b]? = some (compute_public_key params (sks b))) →
      (∀ b, b ∈ bs →
        pvs b =
          compute_public_vote params
            (reconstructed_key params pks (index b)) (sks b) (svs b)) →
      bruteforce_tally params (bs.map pvs) =
        .Ok (sumnat (fun b => if svs b then 1 else 0) bs)

@[simp] theorem signups_nil :
    signups (Base := Base) [] = [] := by
  rfl

@[simp] theorem signups_cons_signup
    (call : @ContractCallInfo Base Msg)
    (calls : List (@ContractCallInfo Base Msg))
    {pk : A} {prf : A × Int}
    (hmsg : call.call_msg = some (.signup pk prf)) :
    signups (call :: calls) = signups calls ++ [(call.call_from, pk)] := by
  simp [signups, hmsg]

@[simp] theorem signups_cons_commit
    (call : @ContractCallInfo Base Msg)
    (calls : List (@ContractCallInfo Base Msg))
    {hash : Positive}
    (hmsg : call.call_msg = some (.commit_to_vote hash)) :
    signups (call :: calls) = signups calls := by
  simp [signups, hmsg]

@[simp] theorem signups_cons_submit
    (call : @ContractCallInfo Base Msg)
    (calls : List (@ContractCallInfo Base Msg))
    {v : A} {proof : VoteProof}
    (hmsg : call.call_msg = some (.submit_vote v proof)) :
    signups (call :: calls) = signups calls := by
  simp [signups, hmsg]

@[simp] theorem signups_cons_tally
    (call : @ContractCallInfo Base Msg)
    (calls : List (@ContractCallInfo Base Msg))
    (hmsg : call.call_msg = some .tally_votes) :
    signups (call :: calls) = signups calls := by
  simp [signups, hmsg]

@[simp] theorem signups_cons_none
    (call : @ContractCallInfo Base Msg)
    (calls : List (@ContractCallInfo Base Msg))
    (hmsg : call.call_msg = none) :
    signups (call :: calls) = signups calls := by
  simp [signups, hmsg]

theorem all_signups
    (pks : List A) (parties : Base.Address → SecretVoterInfo)
    (calls : List (@ContractCallInfo Base Msg))
    (horder : SignupOrderAssumption pks parties calls)
    (hlen : (signups calls).length = pks.length) :
    (signups calls).map Prod.snd = pks := by
  let ss := signups calls
  change ss.map Prod.snd = pks
  apply List.ext_getElem
  · simpa [ss] using hlen
  · intro i hleft hright
    have hss : i < ss.length := by
      simpa [ss] using hleft
    have hzip_get :
        (List.zip ss (List.range ss.length))[i]? = some (ss[i], i) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hss, List.getElem?_range hss⟩
    have hzip_mem :
        (ss[i], i) ∈ List.zip ss (List.range ss.length) :=
      (List.mem_iff_getElem?).mpr ⟨i, hzip_get⟩
    have hprop :
        (parties (ss[i]).fst).svi_index = i ∧ pks[i]? = some (ss[i]).snd := by
      have hforall :
          (List.zip ss (List.range ss.length)).Forall
            (fun ((addr, pk), i) =>
              (parties addr).svi_index = i ∧ pks[i]? = some pk) := by
        simpa [SignupOrderAssumption, ss] using horder
      exact (List.forall_iff_forall_mem.mp hforall) (ss[i], i) hzip_mem
    have hpks_get : pks[i]? = some pks[i] :=
      List.getElem?_eq_getElem hright
    have hpk : pks[i] = (ss[i]).snd := by
      rw [hpks_get] at hprop
      exact Option.some.inj hprop.2
    calc
      (ss.map Prod.snd)[i] = (ss[i]).snd := List.getElem_map Prod.snd
      _ = pks[i] := hpk.symm

omit Base in
private theorem forall_zip_range_snoc_prefix
    {α : Type} {P : α × Nat → Prop} {xs : List α} {x : α}
    (h :
      (List.zip (xs ++ [x]) (List.range (xs.length + 1))).Forall P) :
    (List.zip xs (List.range xs.length)).Forall P := by
  rw [List.forall_iff_forall_mem] at h ⊢
  intro z hz
  obtain ⟨i, hzget⟩ := List.mem_iff_getElem?.mp hz
  rw [List.getElem?_zip_eq_some] at hzget
  obtain ⟨hxget, hrget⟩ := hzget
  obtain ⟨hi, hxeq⟩ := List.getElem?_eq_some_iff.mp hxget
  have hleft :
      (xs ++ [x])[i]? = some z.1 := by
    rw [List.getElem?_append_left hi]
    exact hxget
  have hright :
      (List.range (xs.length + 1))[i]? = some z.2 := by
    have hirange : i < xs.length + 1 := Nat.lt_trans hi (Nat.lt_succ_self _)
    have hiz : i = z.2 := by
      rw [List.getElem?_range hi] at hrget
      exact Option.some.inj hrget
    rw [List.getElem?_range hirange, hiz]
  have hzip :
      (List.zip (xs ++ [x]) (List.range (xs.length + 1)))[i]? =
        some z := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨hleft, hright⟩
  exact h z ((List.mem_iff_getElem?).mpr ⟨i, hzip⟩)

omit Base in
private theorem forall_zip_range_snoc_last
    {α : Type} {P : α × Nat → Prop} {xs : List α} {x : α}
    (h :
      (List.zip (xs ++ [x]) (List.range (xs.length + 1))).Forall P) :
    P (x, xs.length) := by
  rw [List.forall_iff_forall_mem] at h
  have hleft : (xs ++ [x])[xs.length]? = some x := by
    simp
  have hright :
      (List.range (xs.length + 1))[xs.length]? = some xs.length :=
    List.getElem?_range (Nat.lt_succ_self xs.length)
  have hzip :
      (List.zip (xs ++ [x]) (List.range (xs.length + 1)))[xs.length]? =
        some (x, xs.length) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨hleft, hright⟩
  exact h (x, xs.length) ((List.mem_iff_getElem?).mpr ⟨xs.length, hzip⟩)

theorem SignupOrderAssumption_cons_signup_tail
    {pks : List A} {parties : Base.Address → SecretVoterInfo}
    {call : @ContractCallInfo Base Msg}
    {calls : List (@ContractCallInfo Base Msg)}
    {pk : A} {prf : A × Int}
    (hmsg : call.call_msg = some (.signup pk prf))
    (horder : SignupOrderAssumption pks parties (call :: calls)) :
    SignupOrderAssumption pks parties calls := by
  unfold SignupOrderAssumption at horder ⊢
  rw [signups_cons_signup call calls hmsg] at horder
  have horder' :
      (List.zip (signups calls ++ [(call.call_from, pk)])
        (List.range ((signups calls).length + 1))).Forall
        (fun ((addr, pk), i) =>
          (parties addr).svi_index = i ∧ pks[i]? = some pk) := by
    simpa using horder
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    forall_zip_range_snoc_prefix
      (xs := signups calls) (x := (call.call_from, pk)) horder'

theorem SignupOrderAssumption_cons_signup_last
    {pks : List A} {parties : Base.Address → SecretVoterInfo}
    {call : @ContractCallInfo Base Msg}
    {calls : List (@ContractCallInfo Base Msg)}
    {pk : A} {prf : A × Int}
    (hmsg : call.call_msg = some (.signup pk prf))
    (horder : SignupOrderAssumption pks parties (call :: calls)) :
    (parties call.call_from).svi_index = (signups calls).length ∧
      pks[(signups calls).length]? = some pk := by
  unfold SignupOrderAssumption at horder
  rw [signups_cons_signup call calls hmsg] at horder
  have horder' :
      (List.zip (signups calls ++ [(call.call_from, pk)])
        (List.range ((signups calls).length + 1))).Forall
        (fun ((addr, pk), i) =>
          (parties addr).svi_index = i ∧ pks[i]? = some pk) := by
    simpa using horder
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    forall_zip_range_snoc_last
      (xs := signups calls) (x := (call.call_from, pk)) horder'

def BoardroomVotingConditionalPost
    (params : Params) (pks : List A)
    (parties : Base.Address → SecretVoterInfo)
    (cur_slot : Nat)
    (cstate : @State Base) (inc_calls : List (@ContractCallInfo Base Msg)) :
    Prop :=
  MsgAssumption params pks parties inc_calls →
  SignupOrderAssumption pks parties inc_calls →
  (cstate.setup.finish_registration_by < cur_slot →
    pks.length = (signups inc_calls).length) →
  List.Perm
    ((FMap.elements cstate.registered_voters).map
      (fun kv => kv.2.voter_index))
    (List.range cstate.public_keys.length) ∧
  List.Perm (FMap.keys cstate.registered_voters)
    ((signups inc_calls).map Prod.fst) ∧
  (∀ addr inf,
    FMap.find addr cstate.registered_voters = some inf →
      inf.voter_index < cstate.public_keys.length ∧
      inf.voter_index = (parties addr).svi_index ∧
      cstate.public_keys[inf.voter_index]? =
        some (compute_public_key params (parties addr).svi_sk) ∧
      (inf.public_vote = 0 ∨
        inf.public_vote =
          compute_public_vote params
            (reconstructed_key params pks inf.voter_index)
            (parties addr).svi_sk (parties addr).svi_sv)) ∧
  ((has_tallied inc_calls = false → cstate.tally = none) ∧
    (has_tallied inc_calls = true →
      cstate.tally =
        some
          (sumnat
            (fun party => if (parties party).svi_sv then 1 else 0)
            ((signups inc_calls).map Prod.fst))))

def BoardroomVotingCorePost
    (params : Params) (cur_slot : Nat) (cstate : @State Base)
    (inc_calls : List (@ContractCallInfo Base Msg)) : Prop :=
  cstate.setup.finish_registration_by < cstate.setup.finish_vote_by ∧
  (cur_slot < cstate.setup.finish_vote_by → has_tallied inc_calls = false) ∧
  cstate.public_keys.length = FMap.size cstate.registered_voters ∧
  cstate.public_keys = (signups inc_calls).map Prod.snd ∧
  Int.ofNat cstate.public_keys.length < order params - 1

def BoardroomVotingStrongPost
    (params : Params) (pks : List A)
    (parties : Base.Address → SecretVoterInfo)
    (cur_slot : Nat) (cstate : @State Base)
    (inc_calls : List (@ContractCallInfo Base Msg)) : Prop :=
  BoardroomVotingCorePost params cur_slot cstate inc_calls ∧
  BoardroomVotingConditionalPost params pks parties cur_slot cstate inc_calls

theorem Permutation_modify
    (k : Base.Address) (vold vnew : @VoterInfo)
    (m : AddressMap.AddrMap (Base := Base) (@VoterInfo))
    (hfind : FMap.find k m = some vold)
    (hindex : vold.voter_index = vnew.voter_index)
    (hperm :
      List.Perm
        ((FMap.elements m).map (fun kv => kv.2.voter_index))
        (List.range (FMap.size m))) :
    List.Perm
      ((FMap.elements (FMap.add k vnew m)).map
        (fun kv => kv.2.voter_index))
      (List.range (FMap.size m)) := by
  have hnew :=
    (FMap.elements_add_existing k vold vnew m hfind).map
      (fun kv : Base.Address × @VoterInfo => kv.2.voter_index)
  have hold := FMap.elements_add_existing k vold vold m hfind
  rw [FMap.add_id k vold m hfind] at hold
  have hold' := hold.map
    (fun kv : Base.Address × @VoterInfo => kv.2.voter_index)
  have hsame :
      List.Perm
        (vnew.voter_index ::
          (FMap.elements (FMap.remove k m)).map
            (fun kv => kv.2.voter_index))
        (vold.voter_index ::
          (FMap.elements (FMap.remove k m)).map
            (fun kv => kv.2.voter_index)) := by
    rw [← hindex]
  exact hnew.trans (hsame.trans (hold'.symm.trans hperm))

theorem init_state_eq
    (params : Params) (chain : Chain) (ctx : @ContractCallContext Base)
    (setup : @Setup Base) {state : @State Base}
    (h : init params chain ctx setup = .Ok state) :
    state =
      { owner := ctx.ctx_from,
        registered_voters := AddressMap.empty,
        public_keys := [],
        setup := setup,
        tally := none } := by
  unfold init at h
  by_cases htime : setup.finish_registration_by < setup.finish_vote_by
  · rw [if_pos htime] at h
    cases h
    rfl
  · rw [if_neg htime] at h
    cases h

theorem init_is_some
    (params : Params) (chain : Chain) (ctx : @ContractCallContext Base)
    (setup : @Setup Base) :
    setup.finish_registration_by < setup.finish_vote_by ↔
      ∃ state, init params chain ctx setup = .Ok state := by
  constructor
  · intro htime
    let st : @State Base :=
      { owner := ctx.ctx_from,
        registered_voters := AddressMap.empty,
        public_keys := [],
        setup := setup,
        tally := none }
    exact ⟨st, by simp [init, htime, st]⟩
  · rintro ⟨state, h⟩
    unfold init at h
    by_cases htime : setup.finish_registration_by < setup.finish_vote_by
    · exact htime
    · rw [if_neg htime] at h
      cases h

theorem handle_commit_to_vote_is_some
    (hash : Positive) (state : @State Base)
    (caller : Base.Address) (cur_slot : Nat) :
    (∃ commit_by inf,
        state.setup.finish_commit_by = some commit_by ∧
        cur_slot ≤ commit_by ∧
        AddressMap.find caller state.registered_voters = some inf) ↔
      ∃ new_state,
        handle_commit_to_vote hash state caller cur_slot = .Ok new_state := by
  constructor
  · rintro ⟨commit_by, inf, hcommit, hslot, hfind⟩
    refine ⟨{ state with
      registered_voters :=
        AddressMap.add caller { inf with vote_hash := hash }
          state.registered_voters }, ?_⟩
    simp [handle_commit_to_vote, hcommit, not_lt.mpr hslot, hfind]
  · rintro ⟨new_state, h⟩
    unfold handle_commit_to_vote at h
    cases hcommit : state.setup.finish_commit_by with
    | none =>
        simp [hcommit] at h
    | some commit_by =>
        by_cases hslot : commit_by < cur_slot
        · simp [hcommit, hslot] at h
        · simp [hcommit, hslot] at h
          cases hfind : AddressMap.find caller state.registered_voters with
          | none =>
              simp [hfind] at h
          | some inf =>
              exact ⟨commit_by, inf, rfl, le_of_not_gt hslot, rfl⟩

theorem handle_commit_to_vote_state_eq
    {hash : Positive} {state new_state : @State Base}
    {caller : Base.Address} {cur_slot : Nat}
    (h : handle_commit_to_vote hash state caller cur_slot = .Ok new_state) :
    ∃ commit_by inf,
      state.setup.finish_commit_by = some commit_by ∧
        cur_slot ≤ commit_by ∧
        AddressMap.find caller state.registered_voters = some inf ∧
        new_state =
          { state with
            registered_voters :=
              AddressMap.add caller { inf with vote_hash := hash }
                state.registered_voters } := by
  unfold handle_commit_to_vote at h
  cases hcommit : state.setup.finish_commit_by with
  | none =>
      simp [hcommit] at h
  | some commit_by =>
      by_cases hslot : commit_by < cur_slot
      · simp [hcommit, hslot] at h
      · simp [hcommit, hslot] at h
        cases hfind : AddressMap.find caller state.registered_voters with
        | none =>
            simp [hfind] at h
        | some inf =>
            simp [hfind] at h
            cases h
            exact ⟨commit_by, inf, rfl, le_of_not_gt hslot, rfl, rfl⟩

theorem handle_signup_is_some
    (params : Params) (pk : A) (prf : A × Int)
    (state : @State Base) (caller : Base.Address)
    (cur_slot : Nat) (amount : Amount) :
    (cur_slot ≤ state.setup.finish_registration_by ∧
        (∃ eligible,
          AddressMap.find caller state.setup.eligible_voters = some eligible) ∧
        AddressMap.find caller state.registered_voters = none ∧
        (amount == state.setup.registration_deposit) = true ∧
        Int.ofNat state.public_keys.length < order params - 2 ∧
        verify_secret_key_proof params pk state.public_keys.length prf = true) ↔
      ∃ new_state,
        handle_signup params pk prf state caller cur_slot amount =
          .Ok new_state := by
  constructor
  · rintro ⟨htime, ⟨eligible, helig⟩, hregistered, hamount,
      hbound, hproof⟩
    let inf : VoterInfo :=
      { voter_index := state.public_keys.length,
        vote_hash := encode_N 0,
        public_vote := 0 }
    refine ⟨{ state with
      registered_voters := AddressMap.add caller inf state.registered_voters,
      public_keys := state.public_keys ++ [pk] }, ?_⟩
    have hbound' :
        (state.public_keys.length : Int) + 2 < order params := by
      change (state.public_keys.length : Int) <
        order params - 2 at hbound
      omega
    simp [handle_signup, not_lt.mpr htime, helig, hregistered, hamount,
      hbound', hproof, inf]
  · rintro ⟨new_state, h⟩
    unfold handle_signup at h
    by_cases htime : state.setup.finish_registration_by < cur_slot
    · simp [htime] at h
    · simp [htime] at h
      cases helig : AddressMap.find caller state.setup.eligible_voters with
      | none =>
          simp [helig] at h
      | some eligible =>
          simp [helig] at h
          cases hregistered :
              AddressMap.find caller state.registered_voters with
          | none =>
              simp [hregistered] at h
              by_cases hamount :
                  (amount == state.setup.registration_deposit) = true
              ·
                  by_cases hbound :
                      Int.ofNat state.public_keys.length <
                        order params - 2
                  · cases hproof :
                        verify_secret_key_proof params pk
                          state.public_keys.length prf with
                    | false =>
                        simp [hproof] at h
                    | true =>
                        exact
                          ⟨le_of_not_gt htime, ⟨eligible, rfl⟩,
                            rfl, hamount, hbound, rfl⟩
                  · simp_all
              · have hamount_false :
                    (amount == state.setup.registration_deposit) = false := by
                  cases hval :
                      amount == state.setup.registration_deposit <;>
                    simp [hval] at hamount ⊢
                simp_all
          | some inf =>
              simp [hregistered] at h

theorem handle_signup_state_eq
    {params : Params} {pk : A} {prf : A × Int}
    {state new_state : @State Base} {caller : Base.Address}
    {cur_slot : Nat} {amount : Amount}
    (h : handle_signup params pk prf state caller cur_slot amount =
      .Ok new_state) :
    cur_slot ≤ state.setup.finish_registration_by ∧
      (∃ eligible,
        AddressMap.find caller state.setup.eligible_voters = some eligible) ∧
      AddressMap.find caller state.registered_voters = none ∧
      (amount == state.setup.registration_deposit) = true ∧
      Int.ofNat state.public_keys.length < order params - 2 ∧
      verify_secret_key_proof params pk state.public_keys.length prf = true ∧
      new_state =
        { state with
          registered_voters :=
            AddressMap.add caller
              { voter_index := state.public_keys.length,
                vote_hash := encode_N 0,
                public_vote := 0 }
              state.registered_voters,
          public_keys := state.public_keys ++ [pk] } := by
  have hcond :=
    (handle_signup_is_some params pk prf state caller cur_slot amount).mpr
      ⟨new_state, h⟩
  obtain
    ⟨htime, ⟨eligible, helig⟩, hregistered, hamount, hbound, hproof⟩ := hcond
  have hbound_false :
      ¬ order params ≤ (state.public_keys.length : Int) + 2 := by
    change (state.public_keys.length : Int) <
      order params - 2 at hbound
    omega
  unfold handle_signup at h
  simp [not_lt.mpr htime, helig, hregistered, hamount, hbound_false,
    hproof] at h
  cases h
  exact
    ⟨htime, ⟨eligible, helig⟩, hregistered, hamount, hbound,
      hproof, rfl⟩

theorem handle_submit_vote_is_some
    (params : Params) (v : A) (proof : VoteProof)
    (state : @State Base) (caller : Base.Address)
    (cur_slot : Nat) :
    (∃ inf,
        AddressMap.find caller state.registered_voters = some inf ∧
        cur_slot ≤ state.setup.finish_vote_by ∧
        (match state.setup.finish_commit_by with
          | none => true
          | some _ =>
              (params.hash [encodeA v]).val == inf.vote_hash.val) = true ∧
        verify_secret_vote_proof params
          (state.public_keys[inf.voter_index]?.getD 0)
          (reconstructed_key params state.public_keys inf.voter_index)
          v inf.voter_index proof = true) ↔
      ∃ new_state,
        handle_submit_vote params v proof state caller cur_slot =
          .Ok new_state := by
  constructor
  · rintro ⟨inf, hfind, htime, hcommitOk, hproof⟩
    let inf' := { inf with public_vote := v }
    refine ⟨{ state with
      registered_voters := AddressMap.add caller inf'
        state.registered_voters }, ?_⟩
    have hcommitOk_not :
        ¬ (match state.setup.finish_commit_by with
          | none => true
          | some _ =>
              (params.hash [encodeA v]).val == inf.vote_hash.val) =
            false := by
      rw [hcommitOk]
      simp
    have hproof_not :
        ¬ verify_secret_vote_proof params
            (state.public_keys[inf.voter_index]?.getD 0)
            (reconstructed_key params state.public_keys inf.voter_index)
            v inf.voter_index proof = false := by
      rw [hproof]
      simp
    simp [handle_submit_vote, not_lt.mpr htime, hfind]
    split_ifs with hbad_commit
    · exact False.elim (hcommitOk_not hbad_commit)
    · simp [inf']
  · rintro ⟨new_state, h⟩
    unfold handle_submit_vote at h
    by_cases htime : state.setup.finish_vote_by < cur_slot
    · simp [htime] at h
    · simp [htime] at h
      cases hfind : AddressMap.find caller state.registered_voters with
      | none =>
          simp [hfind] at h
      | some inf =>
          simp [hfind] at h
          split_ifs at h with hbad_commit
          rename_i hbad_proof
          have hcommitOk :
              (match state.setup.finish_commit_by with
                | none => true
                | some _ =>
                    (params.hash [encodeA v]).val ==
                      inf.vote_hash.val) = true := by
            cases hval :
                (match state.setup.finish_commit_by with
                | none => true
                | some _ =>
                    (params.hash [encodeA v]).val ==
                      inf.vote_hash.val)
            · exact False.elim (hbad_commit hval)
            · rfl
          have hproof :
              verify_secret_vote_proof params
                (state.public_keys[inf.voter_index]?.getD 0)
                (reconstructed_key params state.public_keys
                  inf.voter_index)
                v inf.voter_index proof = true := by
            cases hval :
                verify_secret_vote_proof params
                  (state.public_keys[inf.voter_index]?.getD 0)
                  (reconstructed_key params state.public_keys
                    inf.voter_index)
                  v inf.voter_index proof <;>
              simp [hval] at hbad_proof ⊢
          exact ⟨inf, rfl, le_of_not_gt htime, hcommitOk, hproof⟩

theorem handle_submit_vote_state_eq
    {params : Params} {v : A} {proof : VoteProof}
    {state new_state : @State Base} {caller : Base.Address}
    {cur_slot : Nat}
    (h : handle_submit_vote params v proof state caller cur_slot =
      .Ok new_state) :
    ∃ inf,
      AddressMap.find caller state.registered_voters = some inf ∧
        cur_slot ≤ state.setup.finish_vote_by ∧
        (match state.setup.finish_commit_by with
          | none => true
          | some _ =>
              (params.hash [encodeA v]).val == inf.vote_hash.val) = true ∧
        verify_secret_vote_proof params
          (state.public_keys[inf.voter_index]?.getD 0)
          (reconstructed_key params state.public_keys inf.voter_index)
          v inf.voter_index proof = true ∧
        new_state =
          { state with
            registered_voters :=
              AddressMap.add caller { inf with public_vote := v }
                state.registered_voters } := by
  unfold handle_submit_vote at h
  by_cases htime : state.setup.finish_vote_by < cur_slot
  · simp [htime] at h
  · simp [htime] at h
    cases hfind : AddressMap.find caller state.registered_voters with
    | none =>
        simp [hfind] at h
    | some inf =>
        simp [hfind] at h
        split_ifs at h with hbad_commit
        rename_i hbad_proof
        have hcommitOk :
            (match state.setup.finish_commit_by with
              | none => true
              | some _ =>
                  (params.hash [encodeA v]).val == inf.vote_hash.val) =
              true := by
          cases hval :
              (match state.setup.finish_commit_by with
              | none => true
              | some _ =>
                  (params.hash [encodeA v]).val == inf.vote_hash.val)
          · exact False.elim (hbad_commit hval)
          · rfl
        have hproof :
            verify_secret_vote_proof params
              (state.public_keys[inf.voter_index]?.getD 0)
              (reconstructed_key params state.public_keys inf.voter_index)
              v inf.voter_index proof = true := by
          cases hval :
              verify_secret_vote_proof params
                (state.public_keys[inf.voter_index]?.getD 0)
                (reconstructed_key params state.public_keys inf.voter_index)
                v inf.voter_index proof <;>
            simp [hval] at hbad_proof ⊢
        simp at h
        cases h
        exact
          ⟨inf, rfl, le_of_not_gt htime, hcommitOk, hproof, rfl⟩

theorem handle_tally_votes_is_some
    (params : Params) (state : @State Base) (cur_slot : Nat) :
    let voters := AddressMap.values state.registered_voters
    state.setup.finish_vote_by ≤ cur_slot ∧
        state.tally = none ∧
        voters.any (fun vi => elmeqb params vi.public_vote 0) = false ∧
        (∃ res, bruteforce_tally params
          (voters.map (fun vi => vi.public_vote)) = .Ok res) ↔
      ∃ new_state,
        handle_tally_votes params state cur_slot = .Ok new_state := by
  dsimp
  constructor
  · rintro ⟨htime, htally, hany, res, hbrute⟩
    refine ⟨{ state with tally := some res }, ?_⟩
    simp [handle_tally_votes, not_lt.mpr htime, htally, hany, hbrute]
  · rintro ⟨new_state, h⟩
    unfold handle_tally_votes at h
    by_cases htime : cur_slot < state.setup.finish_vote_by
    · simp [htime] at h
    · simp [htime] at h
      cases htally : state.tally with
      | none =>
          simp [htally] at h
          let voters := AddressMap.values state.registered_voters
          split_ifs at h with hany
          have hany_false :
              voters.any (fun vi => elmeqb params vi.public_vote 0) =
                false := by
            rw [List.any_eq_false]
            intro x hx htrue
            exact hany ⟨x, by simpa [voters] using hx, htrue⟩
          cases hbrute :
              bruteforce_tally params
                (voters.map (fun vi => vi.public_vote)) with
          | Err e =>
              have hbrute' :
                  bruteforce_tally params
                    ((AddressMap.values state.registered_voters).map
                      (fun vi => vi.public_vote)) = .Err e := by
                simpa [voters] using hbrute
              rw [hbrute'] at h
              cases h
          | Ok res =>
              have hbrute' :
                  bruteforce_tally params
                    ((AddressMap.values state.registered_voters).map
                      (fun vi => vi.public_vote)) = .Ok res := by
                simpa [voters] using hbrute
              exact
                ⟨le_of_not_gt htime, rfl, hany_false, ⟨res, rfl⟩⟩
      | some t =>
          simp [htally] at h

theorem handle_tally_votes_state_eq
    {params : Params} {state new_state : @State Base} {cur_slot : Nat}
    (h : handle_tally_votes params state cur_slot = .Ok new_state) :
    let voters := AddressMap.values state.registered_voters
    state.setup.finish_vote_by ≤ cur_slot ∧
      state.tally = none ∧
      voters.any (fun vi => elmeqb params vi.public_vote 0) = false ∧
      (∃ res,
        bruteforce_tally params
          (voters.map (fun vi => vi.public_vote)) = .Ok res ∧
        new_state = { state with tally := some res }) := by
  dsimp
  unfold handle_tally_votes at h
  by_cases htime : cur_slot < state.setup.finish_vote_by
  · simp [htime] at h
  · simp [htime] at h
    cases htally : state.tally with
    | none =>
        simp [htally] at h
        let voters := AddressMap.values state.registered_voters
        split_ifs at h with hany
        cases hbrute :
            bruteforce_tally params
              (voters.map (fun vi => vi.public_vote)) with
        | Err e =>
            have hbrute' :
                bruteforce_tally params
                  ((AddressMap.values state.registered_voters).map
                    (fun vi => vi.public_vote)) = .Err e := by
              simpa [voters] using hbrute
            rw [hbrute'] at h
            cases h
        | Ok res =>
            have hany_false :
                voters.any (fun vi => elmeqb params vi.public_vote 0) =
                  false := by
              rw [List.any_eq_false]
              intro x hx htrue
              exact hany ⟨x, by simpa [voters] using hx, htrue⟩
            have hbrute' :
                bruteforce_tally params
                  ((AddressMap.values state.registered_voters).map
                    (fun vi => vi.public_vote)) = .Ok res := by
              simpa [voters] using hbrute
            rw [hbrute'] at h
            cases h
            exact
              ⟨le_of_not_gt htime, rfl, by simpa [voters] using hany_false,
                ⟨res, rfl, rfl⟩⟩
    | some t =>
        simp [htally] at h

theorem receive_new_acts_correct
    (params : Params) {chain : Chain} {ctx : @ContractCallContext Base}
    {state new_state : @State Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (h : receive params chain ctx state msg = .Ok (new_state, new_acts)) :
    new_acts = [] := by
  cases msg with
  | none =>
      simp [receive] at h
  | some msg =>
      cases msg with
      | signup pk prf =>
          simp [receive] at h
          cases hsignup :
              handle_signup params pk prf state ctx.ctx_from
                chain.current_slot ctx.ctx_amount with
          | Err e =>
              rw [hsignup] at h
              cases h
          | Ok st =>
              rw [hsignup] at h
              cases h
              rfl
      | commit_to_vote hash =>
          simp [receive] at h
          cases hcommit :
              handle_commit_to_vote hash state ctx.ctx_from
                chain.current_slot with
          | Err e =>
              rw [hcommit] at h
              cases h
          | Ok st =>
              rw [hcommit] at h
              cases h
              rfl
      | submit_vote v proof =>
          simp [receive] at h
          cases hsubmit :
              handle_submit_vote params v proof state ctx.ctx_from
                chain.current_slot with
          | Err e =>
              rw [hsubmit] at h
              cases h
          | Ok st =>
              rw [hsubmit] at h
              cases h
              rfl
      | tally_votes =>
          simp [receive] at h
          cases htally :
              handle_tally_votes params state chain.current_slot with
          | Err e =>
              rw [htally] at h
              cases h
          | Ok st =>
              rw [htally] at h
              cases h
              rfl

theorem no_outgoing
    (params : Params) (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract (contract params))) :
    outgoing_acts bstate caddr = [] := by
  exact
    ConCert.Execution.BlockchainInduction.lift_outgoing_acts_nil
      (contract params) bstate caddr hr
      (by
        intro chain ctx cstate msg new_cstate acts hreceive
        exact receive_new_acts_correct params hreceive)
      hdeployed

theorem receive_preserves_core_post
    {params : Params} {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state new_state : @State Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    {prev_inc_calls : List (@ContractCallInfo Base Msg)}
    (hcore :
      BoardroomVotingCorePost params chain.current_slot prev_state
        prev_inc_calls)
    (hreceive :
      receive params chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    BoardroomVotingCorePost params chain.current_slot new_state
      ({ call_origin := ctx.ctx_origin,
         call_from := ctx.ctx_from,
         call_amount := ctx.ctx_amount,
         call_msg := msg } :: prev_inc_calls) := by
  let callInfo : @ContractCallInfo Base Msg :=
    { call_origin := ctx.ctx_origin,
      call_from := ctx.ctx_from,
      call_amount := ctx.ctx_amount,
      call_msg := msg }
  unfold BoardroomVotingCorePost at hcore ⊢
  obtain ⟨hsetup, hnotTallied, hlen, hpubkeys, hcount⟩ := hcore
  cases msg with
  | none =>
      simp [receive] at hreceive
  | some msg =>
      cases msg with
      | signup pk prf =>
          simp [receive] at hreceive
          cases hsignup :
              handle_signup params pk prf prev_state ctx.ctx_from
                chain.current_slot ctx.ctx_amount with
          | Err e =>
              rw [hsignup] at hreceive
              cases hreceive
          | Ok st =>
              rw [hsignup] at hreceive
              cases hreceive
              have hs := handle_signup_state_eq (h := hsignup)
              obtain
                ⟨htime, _helig, hnew, _hamount, hbound, _hproof,
                  hstate⟩ := hs
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simpa [hstate] using hsetup
              · intro hslot
                have hslotPrev :
                    chain.current_slot < prev_state.setup.finish_vote_by := by
                  simpa [hstate] using hslot
                simpa [has_tallied, callInfo] using hnotTallied hslotPrev
              ·
                change FMap.find ctx.ctx_from prev_state.registered_voters =
                  none at hnew
                rw [hstate]
                simp
                rw [hlen]
                simp [AddressMap.add, FMap.size_add_new _ _ _ hnew]
              ·
                rw [hstate, signups_cons_signup callInfo prev_inc_calls rfl]
                simp [hpubkeys]
              · have hbound' :
                    Int.ofNat (prev_state.public_keys.length + 1) <
                      order params - 1 := by
                  change (prev_state.public_keys.length : Int) <
                    order params - 2 at hbound
                  norm_num
                  omega
                simpa [hstate] using hbound'
      | commit_to_vote hash =>
          simp [receive] at hreceive
          cases hcommit :
              handle_commit_to_vote hash prev_state ctx.ctx_from
                chain.current_slot with
          | Err e =>
              rw [hcommit] at hreceive
              cases hreceive
          | Ok st =>
              rw [hcommit] at hreceive
              cases hreceive
              obtain ⟨_commit_by, inf, _hcommitBy, _hslot, hfind, hstate⟩ :=
                handle_commit_to_vote_state_eq hcommit
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simpa [hstate] using hsetup
              · intro hslot
                have hslotPrev :
                    chain.current_slot < prev_state.setup.finish_vote_by := by
                  simpa [hstate] using hslot
                simpa [has_tallied, callInfo] using hnotTallied hslotPrev
              ·
                change FMap.find ctx.ctx_from prev_state.registered_voters =
                  some inf at hfind
                have hfindSome :
                    FMap.find ctx.ctx_from prev_state.registered_voters ≠
                      none := by
                  rw [hfind]
                  simp
                rw [hstate]
                simp
                change prev_state.public_keys.length =
                  FMap.size
                    (FMap.add ctx.ctx_from
                      { voter_index := inf.voter_index,
                        vote_hash := hash,
                        public_vote := inf.public_vote }
                      prev_state.registered_voters)
                rw [FMap.size_add_existing _ _ _ hfindSome]
                exact hlen
              · simpa [hstate, callInfo] using hpubkeys
              · simpa [hstate] using hcount
      | submit_vote v proof =>
          simp [receive] at hreceive
          cases hsubmit :
              handle_submit_vote params v proof prev_state ctx.ctx_from
                chain.current_slot with
          | Err e =>
              rw [hsubmit] at hreceive
              cases hreceive
          | Ok st =>
              rw [hsubmit] at hreceive
              cases hreceive
              obtain ⟨inf, hfind, _htime, _hcommitOk, _hproof, hstate⟩ :=
                handle_submit_vote_state_eq hsubmit
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simpa [hstate] using hsetup
              · intro hslot
                have hslotPrev :
                    chain.current_slot < prev_state.setup.finish_vote_by := by
                  simpa [hstate] using hslot
                simpa [has_tallied, callInfo] using hnotTallied hslotPrev
              ·
                change FMap.find ctx.ctx_from prev_state.registered_voters =
                  some inf at hfind
                have hfindSome :
                    FMap.find ctx.ctx_from prev_state.registered_voters ≠
                      none := by
                  rw [hfind]
                  simp
                rw [hstate]
                simp
                change prev_state.public_keys.length =
                  FMap.size
                    (FMap.add ctx.ctx_from
                      { voter_index := inf.voter_index,
                        vote_hash := inf.vote_hash,
                        public_vote := v }
                      prev_state.registered_voters)
                rw [FMap.size_add_existing _ _ _ hfindSome]
                exact hlen
              · simpa [hstate, callInfo] using hpubkeys
              · simpa [hstate] using hcount
      | tally_votes =>
          simp [receive] at hreceive
          cases htally :
              handle_tally_votes params prev_state chain.current_slot with
          | Err e =>
              rw [htally] at hreceive
              cases hreceive
          | Ok st =>
              rw [htally] at hreceive
              cases hreceive
              have ht := handle_tally_votes_state_eq (h := htally)
              dsimp at ht
              obtain ⟨htime, _htallyNone, _hany, _res, _hbrute, hstate⟩ := ht
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simpa [hstate] using hsetup
              · intro hslot
                have hslotPrev :
                    chain.current_slot < prev_state.setup.finish_vote_by := by
                  simpa [hstate] using hslot
                exact False.elim (by omega)
              · simpa [hstate] using hlen
              · simpa [hstate, callInfo] using hpubkeys
              · simpa [hstate] using hcount

theorem boardroom_voting_core_correct_strong
    (params : Params) [BoardroomVotingProtocolCorrect params]
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract (contract params))) :
    ∃ (cstate : @State Base)
      (depinfo : @DeploymentInfo Base (@Setup Base))
      (inc_calls : List (@ContractCallInfo Base Msg)),
      deployment_info (@Setup Base) trace caddr = some depinfo ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      incoming_calls Msg trace caddr = some inc_calls ∧
      BoardroomVotingCorePost params bstate.current_slot cstate inc_calls := by
  let P : Nat → Nat → Nat → Base.Address →
      @DeploymentInfo Base (@Setup Base) → @State Base → Amount →
      List (@ActionBody Base) → List (@ContractCallInfo Base Msg) →
      List (@Tx Base) → Prop :=
    fun _ slot _ _ _ cstate _ out_queue inc_calls _ =>
      out_queue = [] ∧
        BoardroomVotingCorePost params slot cstate inc_calls
  have hcases : ContractInductionCases
      (contract params)
      (fun _ oldSlot _ _ newSlot _ => oldSlot < newSlot)
      (fun _ _ => True)
      (fun _ _ _ _ _ => True)
      P := by
    refine
      { establish_facts := ?_, add_block_case := ?_,
        init_case := ?_, outgoing_act_case := ?_,
        nonrecursive_call_case := ?_, recursive_call_case := ?_,
        permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block header _ hvalid _ _ _ =>
          exact hvalid.valid_slot
      | step_action _ _ _ _ eval _ =>
          cases eval with
          | eval_transfer => trivial
          | eval_deploy => trivial
          | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro old_h old_s old_f new_h new_s new_f caddr dep_info state
        balance inc_calls out_txs hslot ih _
      dsimp [P] at ih ⊢
      obtain ⟨_hout, hcore⟩ := ih
      unfold BoardroomVotingCorePost at hcore ⊢
      obtain ⟨hsetup, hnotTallied, hlen, hpubkeys, hcount⟩ := hcore
      refine ⟨rfl, hsetup, ?_, hlen, hpubkeys, hcount⟩
      intro hnewSlot
      exact hnotTallied (Nat.lt_trans hslot hnewSlot)
    · intro chain ctx setup result _ hinit _
      dsimp [P]
      refine ⟨rfl, ?_⟩
      unfold BoardroomVotingCorePost
      have hstate := init_state_eq params chain ctx setup hinit
      have htime := (init_is_some params chain ctx setup).mpr
        ⟨result, hinit⟩
      rw [hstate]
      refine ⟨htime, ?_, ?_, ?_, ?_⟩
      · intro _; rfl
      · simp [AddressMap.empty, FMap.size_empty]
      · rfl
      · have hge := BoardroomVotingProtocolCorrect.order_ge_two
          (params := params)
        norm_num
        omega
    · intro height slot fin_height caddr dep_info cstate balance out_act
        out_acts inc_calls prev_out_txs tx ih _ _ _ _
      dsimp [P] at ih
      exact False.elim (by cases ih.1)
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts _ _ ih hreceive _
      dsimp [P] at ih ⊢
      obtain ⟨hout, hcore⟩ := ih
      have hacts := receive_new_acts_correct params hreceive
      refine ⟨?_, ?_⟩
      · simp [hacts, hout]
      · exact receive_preserves_core_post hcore hreceive
    · intro chain ctx dep_info prev_state msg head prev_out_queue
        prev_inc_calls prev_out_txs new_state new_acts _ _ ih _ _ _
      dsimp [P] at ih
      exact False.elim (by cases ih.1)
    · intro height slot fin_height caddr dep_info cstate balance out_queue
        inc_calls out_txs out_queue' ih hperm _
      dsimp [P] at ih ⊢
      rcases ih with ⟨hqueue, hcore⟩
      rw [hqueue] at hperm
      exact ⟨hperm.nil_eq.symm, hcore⟩
  obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, _hout, hcore⟩ :=
    contract_induction
      (contract params)
      (fun _ oldSlot _ _ newSlot _ => oldSlot < newSlot)
      (fun _ _ => True)
      (fun _ _ _ _ _ => True)
      P hcases bstate caddr trace hdeployed
  exact ⟨cstate, dep, inc_calls, hdep, hstate, hinc, hcore⟩

theorem init_conditional_post
    (params : Params) (pks : List A)
    (parties : Base.Address → SecretVoterInfo)
    (chain : Chain) (ctx : @ContractCallContext Base)
    (setup : @Setup Base) {result : @State Base}
    (hinit : init params chain ctx setup = .Ok result) :
    BoardroomVotingConditionalPost params pks parties chain.current_slot result [] := by
  intro _msgAssumption _orderAssumption _numSignups
  have hstate := init_state_eq params chain ctx setup hinit
  rw [hstate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [AddressMap.empty, FMap.elements_empty]
  · simp [AddressMap.empty, FMap.keys, FMap.elements_empty]
  · intro addr inf hfind
    simp [AddressMap.empty, FMap.find_empty] at hfind
  · constructor
    · intro _; rfl
    · intro htallied
      simp [has_tallied] at htallied

theorem commit_to_vote_preserves_conditional_post
    {params : Params} {pks : List A}
    {parties : Base.Address → SecretVoterInfo}
    {cur_slot : Nat}
    {prev_state new_state : @State Base}
    {inc_calls : List (@ContractCallInfo Base Msg)}
    {origin caller : Base.Address} {amount : Amount}
    {hash : Positive} {inf : @VoterInfo}
    (hcond :
      BoardroomVotingConditionalPost params pks parties cur_slot prev_state inc_calls)
    (hlen :
      prev_state.public_keys.length = FMap.size prev_state.registered_voters)
    (hfind : FMap.find caller prev_state.registered_voters = some inf)
    (hstate :
      new_state =
        { prev_state with
          registered_voters :=
            AddressMap.add caller { inf with vote_hash := hash }
              prev_state.registered_voters }) :
    BoardroomVotingConditionalPost params pks parties cur_slot new_state
      ({ call_origin := origin,
         call_from := caller,
         call_amount := amount,
         call_msg := some (.commit_to_vote hash) } :: inc_calls) := by
  intro hmsg horder hnum
  have hmsgTail : MsgAssumption params pks parties inc_calls := hmsg.2
  have horderTail : SignupOrderAssumption pks parties inc_calls := by
    simpa [SignupOrderAssumption, signups, has_tallied] using horder
  have hnumTail :
      prev_state.setup.finish_registration_by < cur_slot →
        pks.length = (signups inc_calls).length := by
    intro hfinish
    have hfinishNew :
        new_state.setup.finish_registration_by < cur_slot := by
      simpa [hstate] using hfinish
    simpa [signups] using hnum hfinishNew
  obtain ⟨hpermIdx, hpermKeys, hvoters, htally⟩ :=
    hcond hmsgTail horderTail hnumTail
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hpermIdxSize :
        List.Perm
          ((FMap.elements prev_state.registered_voters).map
            (fun kv => kv.2.voter_index))
          (List.range (FMap.size prev_state.registered_voters)) := by
      simpa [← hlen] using hpermIdx
    have hmodify :=
      Permutation_modify caller inf { inf with vote_hash := hash }
        prev_state.registered_voters hfind rfl hpermIdxSize
    simpa [hstate, AddressMap.add, ← hlen] using hmodify
  ·
    have hkeys :=
      FMap.keys_already caller inf { inf with vote_hash := hash }
        prev_state.registered_voters hfind
    exact by
      simpa [hstate, AddressMap.add, signups] using hkeys.trans hpermKeys
  · intro addr inf' hfindNew
    by_cases haddr : addr = caller
    · subst addr
      rw [hstate] at hfindNew
      change
        FMap.find caller
            (FMap.add caller { inf with vote_hash := hash }
              prev_state.registered_voters) = some inf' at hfindNew
      rw [FMap.find_add] at hfindNew
      cases hfindNew
      have hold := hvoters caller inf hfind
      simpa [hstate] using hold
    ·
      rw [hstate] at hfindNew
      change
        FMap.find addr
            (FMap.add caller { inf with vote_hash := hash }
              prev_state.registered_voters) = some inf' at hfindNew
      rw [FMap.find_add_ne caller addr _ _ (Ne.symm haddr)] at hfindNew
      have hold := hvoters addr inf' hfindNew
      simpa [hstate] using hold
  · constructor
    · intro hfalse
      have hfalseTail : has_tallied inc_calls = false := by
        simpa [has_tallied] using hfalse
      simpa [hstate] using htally.1 hfalseTail
    · intro htrue
      have htrueTail : has_tallied inc_calls = true := by
        simpa [has_tallied] using htrue
      simpa [hstate, signups] using htally.2 htrueTail

theorem submit_vote_preserves_conditional_post
    {params : Params} {pks : List A}
    {parties : Base.Address → SecretVoterInfo}
    {cur_slot : Nat}
    {prev_state new_state : @State Base}
    {inc_calls : List (@ContractCallInfo Base Msg)}
    {origin caller : Base.Address} {amount : Amount}
    {v : A} {proof : VoteProof} {inf : @VoterInfo}
    (hcond :
      BoardroomVotingConditionalPost params pks parties cur_slot prev_state inc_calls)
    (hlen :
      prev_state.public_keys.length = FMap.size prev_state.registered_voters)
    (hfind : FMap.find caller prev_state.registered_voters = some inf)
    (hstate :
      new_state =
        { prev_state with
          registered_voters :=
            AddressMap.add caller { inf with public_vote := v }
              prev_state.registered_voters }) :
    BoardroomVotingConditionalPost params pks parties cur_slot new_state
      ({ call_origin := origin,
         call_from := caller,
         call_amount := amount,
         call_msg := some (.submit_vote v proof) } :: inc_calls) := by
  intro hmsg horder hnum
  have hmsgHead :
      some (.submit_vote v proof) =
        some
          (make_vote_msg params pks (parties caller).svi_index
            (parties caller).svi_sk (parties caller).svi_sv
            (parties caller).svi_sv_w (parties caller).svi_sv_r
            (parties caller).svi_sv_d) := hmsg.1
  have hmsgTail : MsgAssumption params pks parties inc_calls := hmsg.2
  have horderTail : SignupOrderAssumption pks parties inc_calls := by
    simpa [SignupOrderAssumption, signups, has_tallied] using horder
  have hnumTail :
      prev_state.setup.finish_registration_by < cur_slot →
        pks.length = (signups inc_calls).length := by
    intro hfinish
    have hfinishNew :
        new_state.setup.finish_registration_by < cur_slot := by
      simpa [hstate] using hfinish
    simpa [signups] using hnum hfinishNew
  obtain ⟨hpermIdx, hpermKeys, hvoters, htally⟩ :=
    hcond hmsgTail horderTail hnumTail
  have hvoteEq :
      v =
        compute_public_vote params
          (reconstructed_key params pks (parties caller).svi_index)
          (parties caller).svi_sk (parties caller).svi_sv := by
    have hmsgEq := Option.some.inj hmsgHead
    simp [make_vote_msg] at hmsgEq
    exact hmsgEq.1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hpermIdxSize :
        List.Perm
          ((FMap.elements prev_state.registered_voters).map
            (fun kv => kv.2.voter_index))
          (List.range (FMap.size prev_state.registered_voters)) := by
      simpa [← hlen] using hpermIdx
    have hmodify :=
      Permutation_modify caller inf { inf with public_vote := v }
        prev_state.registered_voters hfind rfl hpermIdxSize
    simpa [hstate, AddressMap.add, ← hlen] using hmodify
  ·
    have hkeys :=
      FMap.keys_already caller inf { inf with public_vote := v }
        prev_state.registered_voters hfind
    exact by
      simpa [hstate, AddressMap.add, signups] using hkeys.trans hpermKeys
  · intro addr inf' hfindNew
    by_cases haddr : addr = caller
    · subst addr
      rw [hstate] at hfindNew
      change
        FMap.find caller
            (FMap.add caller { inf with public_vote := v }
              prev_state.registered_voters) = some inf' at hfindNew
      rw [FMap.find_add] at hfindNew
      cases hfindNew
      obtain ⟨hlt, hidx, hpk, _hvoteOld⟩ := hvoters caller inf hfind
      refine ⟨by simpa [hstate] using hlt, hidx, by simpa [hstate] using hpk, ?_⟩
      right
      rw [hidx]
      exact hvoteEq
    ·
      rw [hstate] at hfindNew
      change
        FMap.find addr
            (FMap.add caller { inf with public_vote := v }
              prev_state.registered_voters) = some inf' at hfindNew
      rw [FMap.find_add_ne caller addr _ _ (Ne.symm haddr)] at hfindNew
      have hold := hvoters addr inf' hfindNew
      simpa [hstate] using hold
  · constructor
    · intro hfalse
      have hfalseTail : has_tallied inc_calls = false := by
        simpa [has_tallied] using hfalse
      simpa [hstate] using htally.1 hfalseTail
    · intro htrue
      have htrueTail : has_tallied inc_calls = true := by
        simpa [has_tallied] using htrue
      simpa [hstate, signups] using htally.2 htrueTail

theorem signup_preserves_conditional_post
    {params : Params} {pks : List A}
    {parties : Base.Address → SecretVoterInfo}
    {cur_slot : Nat}
    {prev_state new_state : @State Base}
    {inc_calls : List (@ContractCallInfo Base Msg)}
    {origin caller : Base.Address} {amount : Amount}
    {pk : A} {prf : A × Int}
    (hcore :
      BoardroomVotingCorePost params cur_slot prev_state inc_calls)
    (hcond :
      BoardroomVotingConditionalPost params pks parties cur_slot prev_state inc_calls)
    (htime : cur_slot ≤ prev_state.setup.finish_registration_by)
    (hnew : FMap.find caller prev_state.registered_voters = none)
    (hstate :
      new_state =
        { prev_state with
          registered_voters :=
            AddressMap.add caller
              { voter_index := prev_state.public_keys.length,
                vote_hash := encode_N 0,
                public_vote := 0 }
              prev_state.registered_voters,
          public_keys := prev_state.public_keys ++ [pk] }) :
    BoardroomVotingConditionalPost params pks parties cur_slot new_state
      ({ call_origin := origin,
         call_from := caller,
         call_amount := amount,
         call_msg := some (.signup pk prf) } :: inc_calls) := by
  intro hmsg horder hnum
  unfold BoardroomVotingCorePost at hcore
  obtain ⟨hsetup, hnotTallied, hlen, hpubkeys, _hcount⟩ := hcore
  have hmsgHead :
      .signup pk prf =
        make_signup_msg params (parties caller).svi_sk
          (parties caller).svi_sk_r (parties caller).svi_index := hmsg.1
  have hmsgTail : MsgAssumption params pks parties inc_calls := hmsg.2
  have horderTail :
      SignupOrderAssumption pks parties inc_calls :=
    SignupOrderAssumption_cons_signup_tail (call :=
      { call_origin := origin, call_from := caller, call_amount := amount,
        call_msg := some (.signup pk prf) }) (calls := inc_calls) rfl horder
  have horderLast :
      (parties caller).svi_index = (signups inc_calls).length ∧
        pks[(signups inc_calls).length]? = some pk :=
    SignupOrderAssumption_cons_signup_last (call :=
      { call_origin := origin, call_from := caller, call_amount := amount,
        call_msg := some (.signup pk prf) }) (calls := inc_calls) rfl horder
  have hnumTail :
      prev_state.setup.finish_registration_by < cur_slot →
        pks.length = (signups inc_calls).length := by
    intro hfinish
    exact False.elim (by omega)
  obtain ⟨hpermIdx, hpermKeys, hvoters, htally⟩ :=
    hcond hmsgTail horderTail hnumTail
  have hpkEq :
      pk = compute_public_key params (parties caller).svi_sk := by
    simp [make_signup_msg] at hmsgHead
    exact hmsgHead.1
  have hsignupLen :
      (signups inc_calls).length = prev_state.public_keys.length := by
    have hlenPub := congrArg List.length hpubkeys
    simpa using hlenPub.symm
  have hcallerIndex :
      prev_state.public_keys.length = (parties caller).svi_index := by
    rw [← hsignupLen]
    exact horderLast.1.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hpermIdxSize :
        List.Perm
          ((FMap.elements prev_state.registered_voters).map
            (fun kv => kv.2.voter_index))
          (List.range (FMap.size prev_state.registered_voters)) := by
      simpa [← hlen] using hpermIdx
    have hadd :=
      (FMap.elements_add caller
        ({ voter_index := prev_state.public_keys.length,
           vote_hash := encode_N 0,
           public_vote := 0 } : @VoterInfo)
        prev_state.registered_voters hnew).map
        (fun kv : Base.Address × @VoterInfo => kv.2.voter_index)
    have hmove :
        List.Perm
          (prev_state.public_keys.length ::
            (FMap.elements prev_state.registered_voters).map
              (fun kv => kv.2.voter_index))
          (((FMap.elements prev_state.registered_voters).map
              (fun kv => kv.2.voter_index)) ++
            [prev_state.public_keys.length]) := by
      simpa using
        (List.perm_append_comm
          (l₁ := [prev_state.public_keys.length])
          (l₂ := (FMap.elements prev_state.registered_voters).map
            (fun kv => kv.2.voter_index)))
    have hrange :
        List.Perm
          (((FMap.elements prev_state.registered_voters).map
              (fun kv => kv.2.voter_index)) ++
            [prev_state.public_keys.length])
          (List.range (prev_state.public_keys.length + 1)) := by
      have htail := hpermIdx.append_right [prev_state.public_keys.length]
      rw [List.range_succ]
      exact htail
    exact by
      simpa [hstate, AddressMap.add] using hadd.trans (hmove.trans hrange)
  ·
    have hadd :=
      (FMap.elements_add caller
        ({ voter_index := prev_state.public_keys.length,
           vote_hash := encode_N 0,
           public_vote := 0 } : @VoterInfo)
        prev_state.registered_voters hnew).map
        (fun kv : Base.Address × @VoterInfo => kv.1)
    have hmove :
        List.Perm
          (caller :: FMap.keys prev_state.registered_voters)
          (FMap.keys prev_state.registered_voters ++ [caller]) := by
      simpa [FMap.keys] using
        (List.perm_append_comm
          (l₁ := [caller]) (l₂ := FMap.keys prev_state.registered_voters))
    have htarget :
        List.Perm (FMap.keys prev_state.registered_voters ++ [caller])
          ((signups inc_calls).map Prod.fst ++ [caller]) :=
      hpermKeys.append_right [caller]
    exact by
      simpa [hstate, AddressMap.add, signups] using
        hadd.trans (hmove.trans htarget)
  · intro addr inf hfindNew
    by_cases haddr : addr = caller
    · subst addr
      rw [hstate] at hfindNew
      change
        FMap.find caller
            (FMap.add caller
              ({ voter_index := prev_state.public_keys.length,
                 vote_hash := encode_N 0,
                 public_vote := 0 } : @VoterInfo)
              prev_state.registered_voters) = some inf at hfindNew
      rw [FMap.find_add] at hfindNew
      cases hfindNew
      refine ⟨?_, hcallerIndex, ?_, ?_⟩
      · simp [hstate]
      · simp [hstate, hpkEq]
      · left
        rfl
    ·
      rw [hstate] at hfindNew
      change
        FMap.find addr
            (FMap.add caller
              ({ voter_index := prev_state.public_keys.length,
                 vote_hash := encode_N 0,
                 public_vote := 0 } : @VoterInfo)
              prev_state.registered_voters) = some inf at hfindNew
      rw [FMap.find_add_ne caller addr _ _ (Ne.symm haddr)] at hfindNew
      obtain ⟨hlt, hidx, hpk, hvote⟩ := hvoters addr inf hfindNew
      refine ⟨by simpa [hstate] using Nat.lt_succ_of_lt hlt, hidx, ?_, hvote⟩
      have hnth :
          (prev_state.public_keys ++ [pk])[inf.voter_index]? =
            some (compute_public_key params (parties addr).svi_sk) := by
        rw [List.getElem?_append_left hlt]
        exact hpk
      simpa [hstate] using hnth
  · constructor
    · intro hfalse
      have hfalseTail : has_tallied inc_calls = false := by
        simpa [has_tallied] using hfalse
      simpa [hstate] using htally.1 hfalseTail
    · intro htrue
      have htrueTail : has_tallied inc_calls = true := by
        simpa [has_tallied] using htrue
      have hnot : has_tallied inc_calls = false := by
        apply hnotTallied
        omega
      rw [hnot] at htrueTail
      cases htrueTail

theorem tally_votes_preserves_conditional_post
    {params : Params} [BoardroomVotingProtocolCorrect params]
    {pks : List A}
    {parties : Base.Address → SecretVoterInfo}
    {cur_slot : Nat}
    {prev_state new_state : @State Base}
    {inc_calls : List (@ContractCallInfo Base Msg)}
    {origin caller : Base.Address} {amount : Amount}
    {res : Nat}
    (hcore :
      BoardroomVotingCorePost params cur_slot prev_state inc_calls)
    (hcond :
      BoardroomVotingConditionalPost params pks parties cur_slot prev_state inc_calls)
    (htime : prev_state.setup.finish_vote_by ≤ cur_slot)
    (hany :
      (AddressMap.values prev_state.registered_voters).any
        (fun vi => elmeqb params vi.public_vote 0) = false)
    (hbrute :
      bruteforce_tally params
        ((AddressMap.values prev_state.registered_voters).map
          (fun vi => vi.public_vote)) = .Ok res)
    (hstate : new_state = { prev_state with tally := some res }) :
    BoardroomVotingConditionalPost params pks parties cur_slot new_state
      ({ call_origin := origin,
         call_from := caller,
         call_amount := amount,
         call_msg := some .tally_votes } :: inc_calls) := by
  intro hmsg horder hnum
  unfold BoardroomVotingCorePost at hcore
  obtain ⟨hsetup, _hnotTallied, hlen, hpubkeys, hcount⟩ := hcore
  have hmsgTail : MsgAssumption params pks parties inc_calls := hmsg.2
  have horderTail : SignupOrderAssumption pks parties inc_calls := by
    simpa [SignupOrderAssumption, signups, has_tallied] using horder
  have hnumTail :
      prev_state.setup.finish_registration_by < cur_slot →
        pks.length = (signups inc_calls).length := by
    intro hfinish
    have hfinishNew :
        new_state.setup.finish_registration_by < cur_slot := by
      simpa [hstate] using hfinish
    simpa [signups] using hnum hfinishNew
  obtain ⟨hpermIdx, hpermKeys, hvoters, htally⟩ :=
    hcond hmsgTail horderTail hnumTail
  let bs := FMap.elements prev_state.registered_voters
  have hbsLen : bs.length = prev_state.public_keys.length := by
    simp [bs, FMap.length_elements, ← hlen]
  have hcurrentSignups :
      pks.length = (signups inc_calls).length := by
    apply hnumTail
    omega
  have hpublicKeysEqPks : prev_state.public_keys = pks := by
    rw [hpubkeys]
    exact all_signups pks parties inc_calls horderTail hcurrentSignups.symm
  have hbruteElems :
      bruteforce_tally params
        (bs.map (fun kv => kv.2.public_vote)) = .Ok res := by
    simpa [bs, AddressMap.values, FMap.values, List.map_map] using hbrute
  have htallyCorrect :
      bruteforce_tally params
        (bs.map (fun kv => kv.2.public_vote)) =
        .Ok
          (sumnat
            (fun kv : Base.Address × @VoterInfo =>
              if (parties kv.1).svi_sv then 1 else 0)
            bs) := by
    apply BoardroomVotingProtocolCorrect.bruteforce_tally_correct
      (bs := bs)
      (index := fun kv : Base.Address × @VoterInfo => kv.2.voter_index)
      (sks := fun kv : Base.Address × @VoterInfo => (parties kv.1).svi_sk)
      (pks := pks)
      (svs := fun kv : Base.Address × @VoterInfo => (parties kv.1).svi_sv)
      (pvs := fun kv : Base.Address × @VoterInfo => kv.2.public_vote)
    · simpa [hbsLen] using hcount
    · simpa [bs, hbsLen] using hpermIdx
    ·
      calc
        pks.length = (signups inc_calls).length := hcurrentSignups
        _ = prev_state.public_keys.length := by
          have hlenPub := congrArg List.length hpubkeys
          simpa using hlenPub.symm
        _ = bs.length := hbsLen.symm
    · intro kv hmem
      rcases kv with ⟨addr, inf⟩
      have hfind := (FMap.In_elements addr inf prev_state.registered_voters).mp hmem
      obtain ⟨_hlt, _hidx, hpk, _hvote⟩ := hvoters addr inf hfind
      simpa [hpublicKeysEqPks] using hpk
    · intro kv hmem
      rcases kv with ⟨addr, inf⟩
      have hfind := (FMap.In_elements addr inf prev_state.registered_voters).mp hmem
      obtain ⟨_hlt, _hidx, _hpk, hvote⟩ := hvoters addr inf hfind
      cases hvote with
      | inl hzero =>
          exfalso
          have hinValues :
              inf ∈ AddressMap.values prev_state.registered_voters := by
            unfold AddressMap.values FMap.values
            exact List.mem_map_of_mem (f := Prod.snd) hmem
          have hanyTrue :
              (AddressMap.values prev_state.registered_voters).any
                (fun vi => elmeqb params vi.public_vote 0) = true := by
            rw [List.any_eq_true]
            refine ⟨inf, hinValues, ?_⟩
            simp [hzero, elmeqb]
          rw [hany] at hanyTrue
          cases hanyTrue
      | inr hcomputed =>
          exact hcomputed
  have hres :
      res =
        sumnat
          (fun kv : Base.Address × @VoterInfo =>
            if (parties kv.1).svi_sv then 1 else 0)
          bs := by
    rw [htallyCorrect] at hbruteElems
    cases hbruteElems
    rfl
  have hsumKeys :
      sumnat
          (fun kv : Base.Address × @VoterInfo =>
            if (parties kv.1).svi_sv then 1 else 0)
          bs =
        sumnat (fun party => if (parties party).svi_sv then 1 else 0)
          (FMap.keys prev_state.registered_voters) := by
    unfold sumnat FMap.keys bs
    rw [List.map_map]
    rfl
  have hsumSignups :
      sumnat (fun party => if (parties party).svi_sv then 1 else 0)
          (FMap.keys prev_state.registered_voters) =
        sumnat (fun party => if (parties party).svi_sv then 1 else 0)
          ((signups inc_calls).map Prod.fst) :=
    sumnat_perm (fun party => if (parties party).svi_sv then 1 else 0)
      hpermKeys
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hstate] using hpermIdx
  · simpa [hstate, signups] using hpermKeys
  · intro addr inf hfind
    rw [hstate] at hfind
    simpa [hstate] using hvoters addr inf hfind
  · constructor
    · intro hfalse
      simp [has_tallied] at hfalse
    · intro _htrue
      rw [hstate]
      simp [signups, hres, hsumKeys, hsumSignups]

theorem receive_preserves_conditional_post
    {params : Params} [BoardroomVotingProtocolCorrect params]
    {pks : List A} {parties : Base.Address → SecretVoterInfo}
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state new_state : @State Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    {prev_inc_calls : List (@ContractCallInfo Base Msg)}
    (hcore :
      BoardroomVotingCorePost params chain.current_slot prev_state
        prev_inc_calls)
    (hcond :
      BoardroomVotingConditionalPost params pks parties chain.current_slot
        prev_state prev_inc_calls)
    (hreceive :
      receive params chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    BoardroomVotingConditionalPost params pks parties chain.current_slot
      new_state
      ({ call_origin := ctx.ctx_origin,
         call_from := ctx.ctx_from,
         call_amount := ctx.ctx_amount,
         call_msg := msg } :: prev_inc_calls) := by
  unfold BoardroomVotingCorePost at hcore
  obtain ⟨_hsetup, _hnotTallied, hlen, _hpubkeys, _hcount⟩ := hcore
  cases msg with
  | none =>
      simp [receive] at hreceive
  | some msg =>
      cases msg with
      | signup pk prf =>
          simp [receive] at hreceive
          cases hsignup :
              handle_signup params pk prf prev_state ctx.ctx_from
                chain.current_slot ctx.ctx_amount with
          | Err e =>
              rw [hsignup] at hreceive
              cases hreceive
          | Ok st =>
              rw [hsignup] at hreceive
              cases hreceive
              obtain
                ⟨htime, _helig, hnew, _hamount, _hbound, _hproof,
                  hstate⟩ := handle_signup_state_eq (h := hsignup)
              change FMap.find ctx.ctx_from prev_state.registered_voters =
                none at hnew
              exact
                signup_preserves_conditional_post
                  (cur_slot := chain.current_slot)
                  (hcore := by
                    unfold BoardroomVotingCorePost
                    exact ⟨_hsetup, _hnotTallied, hlen, _hpubkeys, _hcount⟩)
                  hcond htime hnew hstate
      | commit_to_vote hash =>
          simp [receive] at hreceive
          cases hcommit :
              handle_commit_to_vote hash prev_state ctx.ctx_from
                chain.current_slot with
          | Err e =>
              rw [hcommit] at hreceive
              cases hreceive
          | Ok st =>
              rw [hcommit] at hreceive
              cases hreceive
              obtain ⟨_commit_by, inf, _hcommitBy, _hslot, hfind, hstate⟩ :=
                handle_commit_to_vote_state_eq hcommit
              change FMap.find ctx.ctx_from prev_state.registered_voters =
                some inf at hfind
              exact
                commit_to_vote_preserves_conditional_post
                  (cur_slot := chain.current_slot)
                  hcond hlen hfind hstate
      | submit_vote v proof =>
          simp [receive] at hreceive
          cases hsubmit :
              handle_submit_vote params v proof prev_state ctx.ctx_from
                chain.current_slot with
          | Err e =>
              rw [hsubmit] at hreceive
              cases hreceive
          | Ok st =>
              rw [hsubmit] at hreceive
              cases hreceive
              obtain ⟨inf, hfind, _htime, _hcommitOk, _hproof, hstate⟩ :=
                handle_submit_vote_state_eq hsubmit
              change FMap.find ctx.ctx_from prev_state.registered_voters =
                some inf at hfind
              exact
                submit_vote_preserves_conditional_post
                  (cur_slot := chain.current_slot)
                  hcond hlen hfind hstate
      | tally_votes =>
          simp [receive] at hreceive
          cases htally :
              handle_tally_votes params prev_state chain.current_slot with
          | Err e =>
              rw [htally] at hreceive
              cases hreceive
          | Ok st =>
              rw [htally] at hreceive
              cases hreceive
              have ht := handle_tally_votes_state_eq (h := htally)
              dsimp at ht
              obtain ⟨htime, _htallyNone, hany, res, hbrute, hstate⟩ := ht
              exact
                tally_votes_preserves_conditional_post
                  (cur_slot := chain.current_slot)
                  (hcore := by
                    unfold BoardroomVotingCorePost
                    exact ⟨_hsetup, _hnotTallied, hlen, _hpubkeys, _hcount⟩)
                  hcond htime hany hbrute hstate

theorem boardroom_voting_correct_strong
    (params : Params) [BoardroomVotingProtocolCorrect params]
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (parties : Base.Address → SecretVoterInfo) (pks : List A)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract (contract params))) :
    ∃ (cstate : @State Base)
      (depinfo : @DeploymentInfo Base (@Setup Base))
      (inc_calls : List (@ContractCallInfo Base Msg)),
      deployment_info (@Setup Base) trace caddr = some depinfo ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      incoming_calls Msg trace caddr = some inc_calls ∧
      BoardroomVotingStrongPost params pks parties bstate.current_slot
        cstate inc_calls := by
  let P : Nat → Nat → Nat → Base.Address →
      @DeploymentInfo Base (@Setup Base) → @State Base → Amount →
      List (@ActionBody Base) → List (@ContractCallInfo Base Msg) →
      List (@Tx Base) → Prop :=
    fun _ slot _ _ _ cstate _ out_queue inc_calls _ =>
      out_queue = [] ∧
        BoardroomVotingStrongPost params pks parties slot cstate inc_calls
  have hcases : ContractInductionCases
      (contract params)
      (fun _ oldSlot _ _ newSlot _ => oldSlot < newSlot)
      (fun _ _ => True)
      (fun _ _ _ _ _ => True)
      P := by
    refine
      { establish_facts := ?_, add_block_case := ?_,
        init_case := ?_, outgoing_act_case := ?_,
        nonrecursive_call_case := ?_, recursive_call_case := ?_,
        permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block header _ hvalid _ _ _ =>
          exact hvalid.valid_slot
      | step_action _ _ _ _ eval _ =>
          cases eval with
          | eval_transfer => trivial
          | eval_deploy => trivial
          | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro old_h old_s old_f new_h new_s new_f caddr dep_info state
        balance inc_calls out_txs hslot ih _
      dsimp [P] at ih ⊢
      obtain ⟨_hout, hstrong⟩ := ih
      refine ⟨rfl, ?_⟩
      unfold BoardroomVotingStrongPost at hstrong ⊢
      obtain ⟨hcore, hcond⟩ := hstrong
      constructor
      ·
        unfold BoardroomVotingCorePost at hcore ⊢
        obtain ⟨hsetup, hnotTallied, hlen, hpubkeys, hcount⟩ := hcore
        refine ⟨hsetup, ?_, hlen, hpubkeys, hcount⟩
        intro hnewSlot
        exact hnotTallied (Nat.lt_trans hslot hnewSlot)
      ·
        intro hmsg horder hnumNew
        exact hcond hmsg horder (fun hold => hnumNew (Nat.lt_trans hold hslot))
    · intro chain ctx setup result _ hinit _
      dsimp [P]
      refine ⟨rfl, ?_⟩
      unfold BoardroomVotingStrongPost
      constructor
      ·
        unfold BoardroomVotingCorePost
        have hstate := init_state_eq params chain ctx setup hinit
        have htime := (init_is_some params chain ctx setup).mpr
          ⟨result, hinit⟩
        rw [hstate]
        refine ⟨htime, ?_, ?_, ?_, ?_⟩
        · intro _; rfl
        · simp [AddressMap.empty, FMap.size_empty]
        · rfl
        · have hge := BoardroomVotingProtocolCorrect.order_ge_two
            (params := params)
          norm_num
          omega
      · exact init_conditional_post params pks parties chain ctx setup hinit
    · intro height slot fin_height caddr dep_info cstate balance out_act
        out_acts inc_calls prev_out_txs tx ih _ _ _ _
      dsimp [P] at ih
      exact False.elim (by cases ih.1)
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts _ _ ih hreceive _
      dsimp [P] at ih ⊢
      obtain ⟨hout, hstrong⟩ := ih
      unfold BoardroomVotingStrongPost at hstrong
      obtain ⟨hcore, hcond⟩ := hstrong
      have hacts := receive_new_acts_correct params hreceive
      refine ⟨?_, ?_⟩
      · simp [hacts, hout]
      · unfold BoardroomVotingStrongPost
        exact
          ⟨receive_preserves_core_post hcore hreceive,
            receive_preserves_conditional_post hcore hcond hreceive⟩
    · intro chain ctx dep_info prev_state msg head prev_out_queue
        prev_inc_calls prev_out_txs new_state new_acts _ _ ih _ _ _
      dsimp [P] at ih
      exact False.elim (by cases ih.1)
    · intro height slot fin_height caddr dep_info cstate balance out_queue
        inc_calls out_txs out_queue' ih hperm _
      dsimp [P] at ih ⊢
      rcases ih with ⟨hqueue, hstrong⟩
      rw [hqueue] at hperm
      exact ⟨hperm.nil_eq.symm, hstrong⟩
  obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, _hout, hstrong⟩ :=
    contract_induction
      (contract params)
      (fun _ oldSlot _ _ newSlot _ => oldSlot < newSlot)
      (fun _ _ => True)
      (fun _ _ _ _ _ => True)
      P hcases bstate caddr trace hdeployed
  exact ⟨cstate, dep, inc_calls, hdep, hstate, hinc, hstrong⟩

theorem boardroom_voting_correct
    (params : Params) [BoardroomVotingProtocolCorrect params]
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (parties : Base.Address → SecretVoterInfo) (pks : List A)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract (contract params))) :
    ∃ (cstate : @State Base)
      (depinfo : @DeploymentInfo Base (@Setup Base))
      (inc_calls : List (@ContractCallInfo Base Msg)),
      deployment_info (@Setup Base) trace caddr = some depinfo ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      incoming_calls Msg trace caddr = some inc_calls ∧
      (MsgAssumption params pks parties inc_calls →
        SignupOrderAssumption pks parties inc_calls →
        (cstate.setup.finish_registration_by < bstate.current_slot →
          pks.length = (signups inc_calls).length) →
        ((has_tallied inc_calls = false → cstate.tally = none) ∧
          (has_tallied inc_calls = true →
            cstate.tally =
              some
                (sumnat
                  (fun party => if (parties party).svi_sv then 1 else 0)
                  ((signups inc_calls).map Prod.fst))))) := by
  obtain ⟨cstate, depinfo, inc_calls, hdep, hstate, hinc, hstrong⟩ :=
    boardroom_voting_correct_strong params bstate caddr trace parties pks
      hdeployed
  refine ⟨cstate, depinfo, inc_calls, hdep, hstate, hinc, ?_⟩
  intro hmsg horder hnum
  unfold BoardroomVotingStrongPost at hstrong
  obtain ⟨_hcore, hcond⟩ := hstrong
  have hpost := hcond hmsg horder hnum
  exact hpost.2.2.2

end ConCert.Examples.BoardroomVoting
