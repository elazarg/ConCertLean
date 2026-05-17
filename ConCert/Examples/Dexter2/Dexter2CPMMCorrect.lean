/- Port of the entrypoint-level lemmas from
examples/dexter2/Dexter2CPMMCorrect.v. -/

import ConCert.Examples.Dexter2.Dexter2CPMM

namespace ConCert.Examples.Dexter2.CPMM.Correct

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

omit Base in
theorem div_eq {n m p : Nat}
    (h : checked_div n m = .Ok p) :
    n / m = p ∧ m ≠ 0 := by
  unfold checked_div at h
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at h
    cases h
  · rw [if_neg hm] at h
    cases h
    constructor
    · rfl
    · intro hz
      subst hz
      simp at hm

omit Base in
theorem div_zero {n m : Nat} {e : Error}
    (h : checked_div n m = .Err e) :
    m = 0 := by
  unfold checked_div at h
  by_cases hm : (m == 0) = true
  · exact Nat.eq_of_beq_eq_true (by simpa using hm)
  · rw [if_neg hm] at h
    cases h

omit Base in
theorem ceildiv_eq {n m p : Nat}
    (h : ceildiv n m = .Ok p) :
    ceildiv_ n m = p ∧ m ≠ 0 := by
  unfold ceildiv at h
  unfold ceildiv_
  by_cases hmod : (n % m == 0) = true
  · rw [if_pos hmod] at h
    rw [if_pos hmod]
    exact div_eq h
  · rw [if_neg hmod] at h
    rw [if_neg hmod]
    cases hdiv : checked_div n m with
    | Err e =>
        rw [hdiv] at h
        simp at h
    | Ok q =>
        rw [hdiv] at h
        cases h
        have hq := div_eq hdiv
        exact ⟨by rw [hq.1], hq.2⟩

omit Base in
theorem ceildiv_zero {n m : Nat} {e : Error}
    (h : ceildiv n m = .Err e) :
    m = 0 := by
  unfold ceildiv at h
  by_cases hmod : (n % m == 0) = true
  · rw [if_pos hmod] at h
    exact div_zero h
  · rw [if_neg hmod] at h
    cases hdiv : checked_div n m with
    | Err err =>
        exact div_zero hdiv
    | Ok q =>
        rw [hdiv] at h
        cases h

omit Base in
theorem sub_eq {n m p : Nat}
    (h : checked_sub n m = .Ok p) :
    n - m = p ∧ m ≤ n := by
  unfold checked_sub at h
  by_cases hlt : n < m
  · simp [hlt] at h
  · simp [hlt] at h
    cases h
    exact ⟨rfl, le_of_not_gt hlt⟩

omit Base in
theorem sub_fail {n m : Nat} {e : Error}
    (h : checked_sub n m = .Err e) :
    n < m := by
  unfold checked_sub at h
  by_cases hlt : n < m
  · exact hlt
  · simp [hlt] at h

omit Base in
theorem checked_div_ok_of_ne_zero {n m : Nat} (h : m ≠ 0) :
    checked_div n m = .Ok (n / m) := by
  unfold checked_div
  have hm : (m == 0) = false := by simp [h]
  rw [if_neg]
  intro ht
  rw [ht] at hm
  cases hm

omit Base in
theorem ceildiv_ok_of_ne_zero {n m : Nat} (h : m ≠ 0) :
    ceildiv n m = .Ok (ceildiv_ n m) := by
  unfold ceildiv ceildiv_
  by_cases hmod : (n % m == 0) = true
  · rw [if_pos hmod, if_pos hmod]
    exact checked_div_ok_of_ne_zero h
  · rw [if_neg hmod, if_neg hmod]
    rw [checked_div_ok_of_ne_zero h]

omit Base in
theorem checked_sub_ok_of_le {n m : Nat} (h : m ≤ n) :
    checked_sub n m = .Ok (n - m) := by
  unfold checked_sub
  rw [if_neg (not_lt.mpr h)]

theorem mint_or_burn_ok_of_ne_null
    (null_address : Base.Address) (state : @State Base)
    (target : Base.Address) (quantity : Int)
    (hneq : state.lqtAddress ≠ null_address) :
    mint_or_burn null_address state target quantity =
      .Ok
        (call_liquidity_token state.lqtAddress 0
          (.msg_mint_or_burn { target := target, quantity := quantity })) := by
  unfold mint_or_burn
  have haddr :
      Base.address_eqb state.lqtAddress null_address = false :=
    Address.address_eq_ne _ _ hneq
  simp [haddr]

theorem mint_or_burn_ok_shape
    (null_address : Base.Address) {state : @State Base}
    {target : Base.Address} {quantity : Int} {act : @ActionBody Base}
    (h : mint_or_burn null_address state target quantity = .Ok act) :
    state.lqtAddress ≠ null_address ∧
      act =
        call_liquidity_token state.lqtAddress 0
          (.msg_mint_or_burn { target := target, quantity := quantity }) := by
  unfold mint_or_burn at h
  by_cases haddr : Base.address_eqb state.lqtAddress null_address = true
  · rw [if_pos haddr] at h
    cases h
  · rw [if_neg haddr] at h
    cases h
    constructor
    · intro heq
      exact haddr ((Base.address_eqb_spec _ _).mpr heq)
    · rfl

theorem xtz_transfer_ok_of_not_contract
    {to_ : Base.Address} {amount : Nat}
    (h : Base.address_is_contract to_ = false) :
    xtz_transfer to_ amount = .Ok (.act_transfer to_ (N_to_amount amount)) := by
  unfold xtz_transfer
  simp [h]

theorem xtz_transfer_ok_shape
    {to_ : Base.Address} {amount : Nat} {act : @ActionBody Base}
    (h : xtz_transfer to_ amount = .Ok act) :
    Base.address_is_contract to_ = false ∧
      act = .act_transfer to_ (N_to_amount amount) := by
  unfold xtz_transfer at h
  by_cases hcontract : Base.address_is_contract to_ = true
  · rw [if_pos hcontract] at h
    cases h
  · rw [if_neg hcontract] at h
    cases h
    constructor
    · cases haddr : Base.address_is_contract to_ <;>
        simp [haddr] at hcontract ⊢
    · rfl

omit Base in
private theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) :
    b = false := by
  cases b <;> simp at h ⊢

theorem default_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state none =
      .Ok (new_state, new_acts)) :
    { prev_state with
      xtzPool := prev_state.xtzPool + amount_to_N ctx.ctx_amount } =
      new_state := by
  unfold receive default_ at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    cases h
    rfl

theorem default_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state none =
      .Ok (new_state, new_acts)) :
    new_state.xtzPool = prev_state.xtzPool + amount_to_N ctx.ctx_amount := by
  have hstate :=
    default_state_eq (Base := Base) null_address set_delegate_call h
  rw [← hstate]

theorem default_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state none =
      .Ok (new_state, new_acts)) :
    new_acts = [] := by
  unfold receive default_ at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    cases h
    rfl

theorem default_entrypoint_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    prev_state.selfIsUpdatingTokenPool = false ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state none =
          .Ok (new_state, new_acts) := by
  constructor
  · intro hself
    refine ⟨{ prev_state with
      xtzPool := prev_state.xtzPool + amount_to_N ctx.ctx_amount }, [], ?_⟩
    simp [receive, default_, hself]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive default_ at h
    by_cases hself : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself] at h
      cases h
    · exact bool_false_of_not_true hself

theorem set_manager_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_manager : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetManager new_manager))) =
        .Ok (new_state, new_acts)) :
    { prev_state with manager := new_manager } = new_state := by
  unfold receive set_manager at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hmanager :
          Base.address_eqb ctx.ctx_from prev_state.manager = false
      · rw [if_pos hmanager] at h
        cases h
      · rw [if_neg hmanager] at h
        cases h
        rfl

theorem set_manager_manager_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_manager : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetManager new_manager))) =
        .Ok (new_state, new_acts)) :
    new_state.manager = new_manager := by
  have hstate :=
    set_manager_state_eq (Base := Base) null_address set_delegate_call h
  rw [← hstate]

theorem set_manager_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_manager : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetManager new_manager))) =
        .Ok (new_state, new_acts)) :
    new_acts = [] := by
  unfold receive set_manager at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hmanager :
          Base.address_eqb ctx.ctx_from prev_state.manager = false
      · rw [if_pos hmanager] at h
        cases h
      · rw [if_neg hmanager] at h
        cases h
        rfl

theorem set_manager_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (new_manager : Base.Address) :
    (ctx.ctx_amount ≤ 0 ∧
        prev_state.selfIsUpdatingTokenPool = false ∧
        ctx.ctx_from = prev_state.manager) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.SetManager new_manager))) =
          .Ok (new_state, new_acts) := by
  constructor
  · rintro ⟨hamount, hself, hmanager⟩
    refine ⟨{ prev_state with manager := new_manager }, [], ?_⟩
    have hnonzero : non_zero_amount ctx.ctx_amount = false := by
      simp [non_zero_amount, not_lt.mpr hamount]
    have hmanager_eqb :
        Base.address_eqb ctx.ctx_from prev_state.manager = true :=
      (Base.address_eqb_spec _ _).mpr hmanager
    simp [receive, set_manager, hself, hnonzero, hmanager_eqb]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive set_manager at h
    simp at h
    by_cases hself_true : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself_true] at h
      cases h
    · rw [if_neg hself_true] at h
      by_cases hamount_true : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount_true] at h
        cases h
      · rw [if_neg hamount_true] at h
        by_cases hmanager_false :
            Base.address_eqb ctx.ctx_from prev_state.manager = false
        · rw [if_pos hmanager_false] at h
          cases h
        · refine ⟨?_, bool_false_of_not_true hself_true, ?_⟩
          · have hnonzero_false :
                non_zero_amount ctx.ctx_amount = false :=
              bool_false_of_not_true hamount_true
            simp [non_zero_amount] at hnonzero_false
            exact hnonzero_false
          · have hmanager_true :
                Base.address_eqb ctx.ctx_from prev_state.manager = true := by
              cases haddr : Base.address_eqb ctx.ctx_from prev_state.manager <;>
                simp [haddr] at hmanager_false ⊢
            exact (Base.address_eqb_spec _ _).mp hmanager_true

theorem set_baker_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @SetBakerParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetBaker param))) = .Ok (new_state, new_acts)) :
    { prev_state with freezeBaker := param.freezeBaker_ } = new_state := by
  unfold receive set_baker at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hmanager :
          Base.address_eqb ctx.ctx_from prev_state.manager = false
      · rw [if_pos hmanager] at h
        cases h
      · rw [if_neg hmanager] at h
        by_cases hfreeze : prev_state.freezeBaker = true
        · rw [if_pos hfreeze] at h
          cases h
        · rw [if_neg hfreeze] at h
          cases h
          rfl

theorem set_baker_freeze_baker_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @SetBakerParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetBaker param))) = .Ok (new_state, new_acts)) :
    new_state.freezeBaker = param.freezeBaker_ := by
  have hstate :=
    set_baker_state_eq (Base := Base) null_address set_delegate_call h
  rw [← hstate]

theorem set_baker_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @SetBakerParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetBaker param))) = .Ok (new_state, new_acts)) :
    new_acts = set_delegate_call param.baker := by
  unfold receive set_baker at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hmanager :
          Base.address_eqb ctx.ctx_from prev_state.manager = false
      · rw [if_pos hmanager] at h
        cases h
      · rw [if_neg hmanager] at h
        by_cases hfreeze : prev_state.freezeBaker = true
        · rw [if_pos hfreeze] at h
          cases h
        · rw [if_neg hfreeze] at h
          cases h
          rfl

theorem set_baker_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @SetBakerParam Base) :
    (ctx.ctx_amount ≤ 0 ∧
        prev_state.selfIsUpdatingTokenPool = false ∧
        ctx.ctx_from = prev_state.manager ∧
        prev_state.freezeBaker = false) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.SetBaker param))) =
          .Ok (new_state, new_acts) := by
  constructor
  · rintro ⟨hamount, hself, hmanager, hfreeze⟩
    refine ⟨{ prev_state with freezeBaker := param.freezeBaker_ },
      set_delegate_call param.baker, ?_⟩
    have hnonzero : non_zero_amount ctx.ctx_amount = false := by
      simp [non_zero_amount, not_lt.mpr hamount]
    have hmanager_eqb :
        Base.address_eqb ctx.ctx_from prev_state.manager = true :=
      (Base.address_eqb_spec _ _).mpr hmanager
    simp [receive, set_baker, hself, hnonzero, hmanager_eqb, hfreeze]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive set_baker at h
    simp at h
    by_cases hself_true : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself_true] at h
      cases h
    · rw [if_neg hself_true] at h
      by_cases hamount_true : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount_true] at h
        cases h
      · rw [if_neg hamount_true] at h
        by_cases hmanager_false :
            Base.address_eqb ctx.ctx_from prev_state.manager = false
        · rw [if_pos hmanager_false] at h
          cases h
        · rw [if_neg hmanager_false] at h
          by_cases hfreeze_true : prev_state.freezeBaker = true
          · rw [if_pos hfreeze_true] at h
            cases h
          · refine
              ⟨?_, bool_false_of_not_true hself_true, ?_,
                bool_false_of_not_true hfreeze_true⟩
            · have hnonzero_false :
                  non_zero_amount ctx.ctx_amount = false :=
                bool_false_of_not_true hamount_true
              simp [non_zero_amount] at hnonzero_false
              exact hnonzero_false
            · have hmanager_true :
                  Base.address_eqb ctx.ctx_from prev_state.manager = true := by
                cases haddr : Base.address_eqb ctx.ctx_from prev_state.manager <;>
                  simp [haddr] at hmanager_false ⊢
              exact (Base.address_eqb_spec _ _).mp hmanager_true

theorem set_lqt_address_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_lqt_address : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetLqtAddress new_lqt_address))) =
        .Ok (new_state, new_acts)) :
    { prev_state with lqtAddress := new_lqt_address } = new_state := by
  unfold receive set_lqt_address at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hmanager :
          Base.address_eqb ctx.ctx_from prev_state.manager = false
      · rw [if_pos hmanager] at h
        cases h
      · rw [if_neg hmanager] at h
        by_cases hlqt :
            Base.address_eqb prev_state.lqtAddress null_address = false
        · rw [if_pos hlqt] at h
          cases h
        · rw [if_neg hlqt] at h
          cases h
          rfl

theorem set_lqt_address_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_lqt_address : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetLqtAddress new_lqt_address))) =
        .Ok (new_state, new_acts)) :
    new_state.lqtAddress = new_lqt_address := by
  have hstate :=
    set_lqt_address_state_eq (Base := Base) null_address set_delegate_call h
  rw [← hstate]

theorem set_lqt_address_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_lqt_address : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.SetLqtAddress new_lqt_address))) =
        .Ok (new_state, new_acts)) :
    new_acts = [] := by
  unfold receive set_lqt_address at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hmanager :
          Base.address_eqb ctx.ctx_from prev_state.manager = false
      · rw [if_pos hmanager] at h
        cases h
      · rw [if_neg hmanager] at h
        by_cases hlqt :
            Base.address_eqb prev_state.lqtAddress null_address = false
        · rw [if_pos hlqt] at h
          cases h
        · rw [if_neg hlqt] at h
          cases h
          rfl

theorem set_lqt_address_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base)
    (new_lqt_address : Base.Address) :
    (ctx.ctx_amount ≤ 0 ∧
        prev_state.selfIsUpdatingTokenPool = false ∧
        ctx.ctx_from = prev_state.manager ∧
        prev_state.lqtAddress = null_address) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.SetLqtAddress new_lqt_address))) =
          .Ok (new_state, new_acts) := by
  constructor
  · rintro ⟨hamount, hself, hmanager, hlqt⟩
    refine ⟨{ prev_state with lqtAddress := new_lqt_address }, [], ?_⟩
    have hnonzero : non_zero_amount ctx.ctx_amount = false := by
      simp [non_zero_amount, not_lt.mpr hamount]
    have hmanager_eqb :
        Base.address_eqb ctx.ctx_from prev_state.manager = true :=
      (Base.address_eqb_spec _ _).mpr hmanager
    have hlqt_eqb :
        Base.address_eqb prev_state.lqtAddress null_address = true :=
      (Base.address_eqb_spec _ _).mpr hlqt
    simp [receive, set_lqt_address, hself, hnonzero, hmanager_eqb,
      hlqt_eqb]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive set_lqt_address at h
    simp at h
    by_cases hself_true : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself_true] at h
      cases h
    · rw [if_neg hself_true] at h
      by_cases hamount_true : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount_true] at h
        cases h
      · rw [if_neg hamount_true] at h
        by_cases hmanager_false :
            Base.address_eqb ctx.ctx_from prev_state.manager = false
        · rw [if_pos hmanager_false] at h
          cases h
        · rw [if_neg hmanager_false] at h
          by_cases hlqt_false :
              Base.address_eqb prev_state.lqtAddress null_address = false
          · rw [if_pos hlqt_false] at h
            cases h
          · refine
              ⟨?_, bool_false_of_not_true hself_true, ?_, ?_⟩
            · have hnonzero_false :
                  non_zero_amount ctx.ctx_amount = false :=
                bool_false_of_not_true hamount_true
              simp [non_zero_amount] at hnonzero_false
              exact hnonzero_false
            · have hmanager_true :
                  Base.address_eqb ctx.ctx_from prev_state.manager = true := by
                cases haddr : Base.address_eqb ctx.ctx_from prev_state.manager <;>
                  simp [haddr] at hmanager_false ⊢
              exact (Base.address_eqb_spec _ _).mp hmanager_true
            · have hlqt_true :
                  Base.address_eqb prev_state.lqtAddress null_address = true := by
                cases haddr : Base.address_eqb prev_state.lqtAddress null_address <;>
                  simp [haddr] at hlqt_false ⊢
              exact (Base.address_eqb_spec _ _).mp hlqt_true

theorem update_token_pool_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg .UpdateTokenPool)) = .Ok (new_state, new_acts)) :
    { prev_state with selfIsUpdatingTokenPool := true } = new_state := by
  unfold receive update_token_pool at h
  simp at h
  by_cases horigin : Base.address_eqb ctx.ctx_from ctx.ctx_origin = false
  · rw [if_pos horigin] at h
    cases h
  · rw [if_neg horigin] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hself : prev_state.selfIsUpdatingTokenPool = true
      · rw [if_pos hself] at h
        cases h
      · rw [if_neg hself] at h
        cases h
        rfl

theorem update_token_pool_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg .UpdateTokenPool)) = .Ok (new_state, new_acts)) :
    new_state.selfIsUpdatingTokenPool = true := by
  have hstate :=
    update_token_pool_state_eq (Base := Base) null_address set_delegate_call h
  rw [← hstate]

theorem update_token_pool_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    (ctx.ctx_amount ≤ 0 ∧
        prev_state.selfIsUpdatingTokenPool = false ∧
        ctx.ctx_from = ctx.ctx_origin) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg .UpdateTokenPool)) = .Ok (new_state, new_acts) := by
  constructor
  · rintro ⟨hamount, hself, horigin⟩
    refine ⟨{ prev_state with selfIsUpdatingTokenPool := true },
      [call_to_token prev_state.tokenAddress 0
        (.msg_balance_of
          { bal_requests :=
              [{ owner := ctx.ctx_contract_address,
                 bal_req_token_id := prev_state.tokenId }],
            bal_callback :=
              { blob := none, return_addr := ctx.ctx_contract_address } })],
      ?_⟩
    have hnonzero : non_zero_amount ctx.ctx_amount = false := by
      simp [non_zero_amount, not_lt.mpr hamount]
    have horigin_eqb : Base.address_eqb ctx.ctx_from ctx.ctx_origin = true :=
      (Base.address_eqb_spec _ _).mpr horigin
    simp [receive, update_token_pool, hself, hnonzero, horigin_eqb]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive update_token_pool at h
    simp at h
    by_cases horigin_false :
        Base.address_eqb ctx.ctx_from ctx.ctx_origin = false
    · rw [if_pos horigin_false] at h
      cases h
    · rw [if_neg horigin_false] at h
      by_cases hamount_true : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount_true] at h
        cases h
      · rw [if_neg hamount_true] at h
        by_cases hself_true : prev_state.selfIsUpdatingTokenPool = true
        · rw [if_pos hself_true] at h
          cases h
        · refine ⟨?_, bool_false_of_not_true hself_true, ?_⟩
          · have hnonzero_false :
                non_zero_amount ctx.ctx_amount = false :=
              bool_false_of_not_true hamount_true
            simp [non_zero_amount] at hnonzero_false
            exact hnonzero_false
          · have horigin_true :
                Base.address_eqb ctx.ctx_from ctx.ctx_origin = true := by
              cases haddr : Base.address_eqb ctx.ctx_from ctx.ctx_origin <;>
                simp [haddr] at horigin_false ⊢
            exact (Base.address_eqb_spec _ _).mp horigin_true

theorem update_token_pool_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg .UpdateTokenPool)) = .Ok (new_state, new_acts)) :
    new_acts =
      [call_to_token prev_state.tokenAddress 0
        (.msg_balance_of
          { bal_requests :=
              [{ owner := ctx.ctx_contract_address,
                 bal_req_token_id := prev_state.tokenId }],
            bal_callback :=
              { blob := none, return_addr := ctx.ctx_contract_address } })] := by
  unfold receive update_token_pool at h
  simp at h
  by_cases horigin : Base.address_eqb ctx.ctx_from ctx.ctx_origin = false
  · rw [if_pos horigin] at h
    cases h
  · rw [if_neg horigin] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hself : prev_state.selfIsUpdatingTokenPool = true
      · rw [if_pos hself] at h
        cases h
      · rw [if_neg hself] at h
        cases h
        rfl

theorem update_token_pool_internal_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {responses : UpdateTokenPoolInternal}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.receive_balance_of_param responses)) =
        .Ok (new_state, new_acts)) :
    { prev_state with
      selfIsUpdatingTokenPool := false,
      tokenPool :=
        match responses with
        | [] => 0
        | response :: _ => response.balance } = new_state := by
  unfold receive update_token_pool_internal at h
  simp at h
  by_cases hbad :
      prev_state.selfIsUpdatingTokenPool = false ∨
        Base.address_eqb ctx.ctx_from prev_state.tokenAddress = false
  · rw [if_pos hbad] at h
    cases h
  · rw [if_neg hbad] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      cases responses with
      | nil =>
          simp at h
      | cons response rest =>
          simp at h
          rcases h with ⟨hstate, _⟩
          simpa using hstate

theorem update_token_pool_internal_update_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {responses : UpdateTokenPoolInternal}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.receive_balance_of_param responses)) =
        .Ok (new_state, new_acts)) :
    new_state.selfIsUpdatingTokenPool = false := by
  have hstate :=
    update_token_pool_internal_state_eq
      (Base := Base) null_address set_delegate_call h
  rw [← hstate]

theorem update_token_pool_internal_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {responses : UpdateTokenPoolInternal}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.receive_balance_of_param responses)) =
        .Ok (new_state, new_acts)) :
    new_acts = [] := by
  unfold receive update_token_pool_internal at h
  simp at h
  by_cases hbad :
      prev_state.selfIsUpdatingTokenPool = false ∨
        Base.address_eqb ctx.ctx_from prev_state.tokenAddress = false
  · rw [if_pos hbad] at h
    cases h
  · rw [if_neg hbad] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      cases responses with
      | nil =>
          simp at h
      | cons response rest =>
          simp at h
          rcases h with ⟨_, hacts⟩
          exact hacts

theorem update_token_pool_internal_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base)
    (responses : UpdateTokenPoolInternal) :
    (ctx.ctx_amount ≤ 0 ∧
        prev_state.selfIsUpdatingTokenPool = true ∧
        ctx.ctx_from = prev_state.tokenAddress ∧
        responses ≠ []) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.receive_balance_of_param responses)) =
          .Ok (new_state, new_acts) := by
  constructor
  · rintro ⟨hamount, hself, hsender, hresponses⟩
    cases responses with
    | nil =>
        exact False.elim (hresponses rfl)
    | cons response rest =>
        refine ⟨{ prev_state with
          tokenPool := response.balance,
          selfIsUpdatingTokenPool := false }, [], ?_⟩
        have hnonzero : non_zero_amount ctx.ctx_amount = false := by
          simp [non_zero_amount, not_lt.mpr hamount]
        have hsender_eqb :
            Base.address_eqb ctx.ctx_from prev_state.tokenAddress = true :=
          (Base.address_eqb_spec _ _).mpr hsender
        simp [receive, update_token_pool_internal, hself, hsender_eqb,
          hnonzero]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive update_token_pool_internal at h
    simp at h
    by_cases hbad :
        prev_state.selfIsUpdatingTokenPool = false ∨
          Base.address_eqb ctx.ctx_from prev_state.tokenAddress = false
    · rw [if_pos hbad] at h
      cases h
    · rw [if_neg hbad] at h
      by_cases hamount_true : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount_true] at h
        cases h
      · rw [if_neg hamount_true] at h
        cases responses with
        | nil =>
            simp at h
        | cons response rest =>
            refine ⟨?_, ?_, ?_, by simp⟩
            · have hnonzero_false :
                  non_zero_amount ctx.ctx_amount = false :=
                bool_false_of_not_true hamount_true
              simp [non_zero_amount] at hnonzero_false
              exact hnonzero_false
            · have hself_not_false :
                  ¬ prev_state.selfIsUpdatingTokenPool = false := by
                intro hfalse
                exact hbad (Or.inl hfalse)
              cases hself : prev_state.selfIsUpdatingTokenPool <;>
                simp [hself] at hself_not_false ⊢
            · have hsender_not_false :
                  ¬ Base.address_eqb ctx.ctx_from
                      prev_state.tokenAddress = false := by
                intro hfalse
                exact hbad (Or.inr hfalse)
              have hsender_true :
                  Base.address_eqb ctx.ctx_from
                    prev_state.tokenAddress = true := by
                cases haddr :
                    Base.address_eqb ctx.ctx_from prev_state.tokenAddress <;>
                  simp [haddr] at hsender_not_false ⊢
              exact (Base.address_eqb_spec _ _).mp hsender_true

theorem add_liquidity_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @AddLiquidityParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.AddLiquidity param))) =
        .Ok (new_state, new_acts)) :
    let lqt_minted :=
      amount_to_N ctx.ctx_amount * prev_state.lqtTotal / prev_state.xtzPool
    let tokens_deposited :=
      ceildiv_
        (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
        prev_state.xtzPool
    { prev_state with
      lqtTotal := prev_state.lqtTotal + lqt_minted,
      tokenPool := prev_state.tokenPool + tokens_deposited,
      xtzPool := prev_state.xtzPool + amount_to_N ctx.ctx_amount } =
      new_state := by
  unfold receive add_liquidity at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.add_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      cases hdiv :
          checked_div
            (amount_to_N ctx.ctx_amount * prev_state.lqtTotal)
            prev_state.xtzPool with
      | Err e =>
          rw [hdiv] at h
          cases h
      | Ok lqt_minted =>
          rw [hdiv] at h
          simp at h
          cases hceil :
              ceildiv
                (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
                prev_state.xtzPool with
          | Err e =>
              rw [hceil] at h
              cases h
          | Ok tokens_deposited =>
              rw [hceil] at h
              simp at h
              by_cases hmax : param.maxTokensDeposited < tokens_deposited
              · rw [if_pos hmax] at h
                cases h
              · rw [if_neg hmax] at h
                by_cases hmin : lqt_minted < param.minLqtMinted
                · rw [if_pos hmin] at h
                  cases h
                · rw [if_neg hmin] at h
                  cases hmint :
                      mint_or_burn null_address prev_state param.owner
                        (Int.ofNat lqt_minted) with
                  | Err e =>
                      have hmint' :
                          mint_or_burn null_address prev_state param.owner
                            (↑lqt_minted : Int) = .Err e := by
                        simpa using hmint
                      rw [hmint'] at h
                      cases h
                  | Ok op_lqt =>
                      have hmint' :
                          mint_or_burn null_address prev_state param.owner
                            (↑lqt_minted : Int) = .Ok op_lqt := by
                        simpa using hmint
                      rw [hmint'] at h
                      rcases h with ⟨hstate, _⟩
                      have hdiv_eq := (div_eq hdiv).1
                      have hceil_eq := (ceildiv_eq hceil).1
                      simp [hdiv_eq, hceil_eq]

theorem add_liquidity_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @AddLiquidityParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.AddLiquidity param))) =
        .Ok (new_state, new_acts)) :
    let lqt_minted :=
      amount_to_N ctx.ctx_amount * prev_state.lqtTotal / prev_state.xtzPool
    let tokens_deposited :=
      ceildiv_
        (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
        prev_state.xtzPool
    new_state.lqtTotal = prev_state.lqtTotal + lqt_minted ∧
      new_state.tokenPool = prev_state.tokenPool + tokens_deposited ∧
      new_state.xtzPool =
        prev_state.xtzPool + amount_to_N ctx.ctx_amount := by
  rw [← add_liquidity_state_eq
    (Base := Base) null_address set_delegate_call h]
  simp

theorem add_liquidity_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @AddLiquidityParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.AddLiquidity param))) =
        .Ok (new_state, new_acts)) :
    let lqt_minted :=
      amount_to_N ctx.ctx_amount * prev_state.lqtTotal / prev_state.xtzPool
    let tokens_deposited :=
      ceildiv_
        (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
        prev_state.xtzPool
    new_acts =
      [ token_transfer prev_state ctx.ctx_from ctx.ctx_contract_address
          tokens_deposited,
        call_liquidity_token prev_state.lqtAddress 0
          (.msg_mint_or_burn
            { target := param.owner, quantity := Int.ofNat lqt_minted }) ] := by
  unfold receive add_liquidity at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.add_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      cases hdiv :
          checked_div
            (amount_to_N ctx.ctx_amount * prev_state.lqtTotal)
            prev_state.xtzPool with
      | Err e =>
          rw [hdiv] at h
          cases h
      | Ok lqt_minted =>
          rw [hdiv] at h
          simp at h
          cases hceil :
              ceildiv
                (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
                prev_state.xtzPool with
          | Err e =>
              rw [hceil] at h
              cases h
          | Ok tokens_deposited =>
              rw [hceil] at h
              simp at h
              by_cases hmax : param.maxTokensDeposited < tokens_deposited
              · rw [if_pos hmax] at h
                cases h
              · rw [if_neg hmax] at h
                by_cases hmin : lqt_minted < param.minLqtMinted
                · rw [if_pos hmin] at h
                  cases h
                · rw [if_neg hmin] at h
                  cases hmint :
                      mint_or_burn null_address prev_state param.owner
                        (Int.ofNat lqt_minted) with
                  | Err e =>
                      have hmint' :
                          mint_or_burn null_address prev_state param.owner
                            (↑lqt_minted : Int) = .Err e := by
                        simpa using hmint
                      rw [hmint'] at h
                      cases h
                  | Ok op_lqt =>
                      have hmint' :
                          mint_or_burn null_address prev_state param.owner
                            (↑lqt_minted : Int) = .Ok op_lqt := by
                        simpa using hmint
                      rw [hmint'] at h
                      rcases h with ⟨_, hacts⟩
                      have hop :
                          op_lqt =
                            call_liquidity_token prev_state.lqtAddress 0
                              (.msg_mint_or_burn
                                { target := param.owner,
                                  quantity := Int.ofNat lqt_minted }) := by
                        unfold mint_or_burn at hmint
                        by_cases hlqt :
                            Base.address_eqb prev_state.lqtAddress
                              null_address = true
                        · rw [if_pos hlqt] at hmint
                          cases hmint
                        · rw [if_neg hlqt] at hmint
                          cases hmint
                          rfl
                      have hdiv_eq := (div_eq hdiv).1
                      have hceil_eq := (ceildiv_eq hceil).1
                      simp [hop, hdiv_eq, hceil_eq]

theorem add_liquidity_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @AddLiquidityParam Base) :
    let lqt_minted :=
      amount_to_N ctx.ctx_amount * prev_state.lqtTotal / prev_state.xtzPool
    let tokens_deposited :=
      ceildiv_
        (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
        prev_state.xtzPool
    (prev_state.selfIsUpdatingTokenPool = false ∧
        chain.current_slot < param.add_deadline ∧
        tokens_deposited ≤ param.maxTokensDeposited ∧
        param.minLqtMinted ≤ lqt_minted ∧
        prev_state.xtzPool ≠ 0 ∧
        prev_state.lqtAddress ≠ null_address) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.AddLiquidity param))) =
          .Ok (new_state, new_acts) := by
  dsimp
  constructor
  · rintro ⟨hself, hdeadline, hmax, hmin, hxtz, hlqt⟩
    let lqt_minted :=
      amount_to_N ctx.ctx_amount * prev_state.lqtTotal / prev_state.xtzPool
    let tokens_deposited :=
      ceildiv_
        (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
        prev_state.xtzPool
    let op_lqt :=
      call_liquidity_token prev_state.lqtAddress 0
        (.msg_mint_or_burn
          { target := param.owner, quantity := Int.ofNat lqt_minted })
    let new_state :=
      { prev_state with
        lqtTotal := prev_state.lqtTotal + lqt_minted,
        tokenPool := prev_state.tokenPool + tokens_deposited,
        xtzPool := prev_state.xtzPool + amount_to_N ctx.ctx_amount }
    refine ⟨new_state,
      [ token_transfer prev_state ctx.ctx_from ctx.ctx_contract_address
          tokens_deposited,
        op_lqt ], ?_⟩
    have hdeadline_not : ¬ param.add_deadline ≤ chain.current_slot :=
      Nat.not_le_of_gt hdeadline
    have hdiv :
        checked_div
          (amount_to_N ctx.ctx_amount * prev_state.lqtTotal)
          prev_state.xtzPool =
          .Ok lqt_minted := by
      dsimp [lqt_minted]
      exact checked_div_ok_of_ne_zero hxtz
    have hceil :
        ceildiv
          (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
          prev_state.xtzPool =
          .Ok tokens_deposited := by
      dsimp [tokens_deposited]
      exact ceildiv_ok_of_ne_zero hxtz
    have hmax_not : ¬ param.maxTokensDeposited < tokens_deposited :=
      not_lt.mpr hmax
    have hmin_not : ¬ lqt_minted < param.minLqtMinted :=
      not_lt.mpr hmin
    have hmint :
        mint_or_burn null_address prev_state param.owner
          (Int.ofNat lqt_minted) = .Ok op_lqt := by
      dsimp [op_lqt]
      exact mint_or_burn_ok_of_ne_null null_address prev_state
        param.owner (Int.ofNat lqt_minted) hlqt
    unfold receive add_liquidity
    simp [hself]
    rw [if_neg hdeadline_not, hdiv, hceil]
    simp
    rw [if_neg hmax_not, if_neg hmin_not]
    have hmint' :
        mint_or_burn null_address prev_state param.owner
          (↑lqt_minted : Int) = .Ok op_lqt := by
      simpa using hmint
    rw [hmint']
    simp [new_state, hself]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive add_liquidity at h
    simp at h
    by_cases hself : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself] at h
      cases h
    · rw [if_neg hself] at h
      by_cases hdeadline : param.add_deadline ≤ chain.current_slot
      · rw [if_pos hdeadline] at h
        cases h
      · rw [if_neg hdeadline] at h
        cases hdiv :
            checked_div
              (amount_to_N ctx.ctx_amount * prev_state.lqtTotal)
              prev_state.xtzPool with
        | Err e =>
            rw [hdiv] at h
            cases h
        | Ok lqt_minted =>
            rw [hdiv] at h
            simp at h
            cases hceil :
                ceildiv
                  (amount_to_N ctx.ctx_amount * prev_state.tokenPool)
                  prev_state.xtzPool with
            | Err e =>
                rw [hceil] at h
                cases h
            | Ok tokens_deposited =>
                rw [hceil] at h
                simp at h
                by_cases hmax : param.maxTokensDeposited < tokens_deposited
                · rw [if_pos hmax] at h
                  cases h
                · rw [if_neg hmax] at h
                  by_cases hmin : lqt_minted < param.minLqtMinted
                  · rw [if_pos hmin] at h
                    cases h
                  · rw [if_neg hmin] at h
                    cases hmint :
                        mint_or_burn null_address prev_state param.owner
                          (Int.ofNat lqt_minted) with
                    | Err e =>
                        have hmint' :
                            mint_or_burn null_address prev_state param.owner
                              (↑lqt_minted : Int) = .Err e := by
                          simpa using hmint
                        rw [hmint'] at h
                        cases h
                    | Ok op_lqt =>
                        have hmint' :
                            mint_or_burn null_address prev_state param.owner
                              (↑lqt_minted : Int) = .Ok op_lqt := by
                          simpa using hmint
                        rw [hmint'] at h
                        have hdiv_info := div_eq hdiv
                        have hceil_info := ceildiv_eq hceil
                        have hmint_info :=
                          mint_or_burn_ok_shape
                            (Base := Base) null_address hmint
                        refine
                          ⟨bool_false_of_not_true hself,
                            Nat.lt_of_not_ge hdeadline, ?_, ?_,
                            hdiv_info.2, hmint_info.1⟩
                        · have hle : tokens_deposited ≤
                              param.maxTokensDeposited := le_of_not_gt hmax
                          simpa [hceil_info.1] using hle
                        · have hle : param.minLqtMinted ≤ lqt_minted :=
                            le_of_not_gt hmin
                          simpa [hdiv_info.1] using hle

theorem xtz_to_token_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @XtzToTokenParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.XtzToToken param))) =
        .Ok (new_state, new_acts)) :
    let tokens_bought :=
      (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool) /
        (prev_state.xtzPool * 1000 + amount_to_N ctx.ctx_amount * 997)
    { prev_state with
      tokenPool := prev_state.tokenPool - tokens_bought,
      xtzPool := prev_state.xtzPool + amount_to_N ctx.ctx_amount } =
      new_state := by
  unfold receive xtz_to_token at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.xtt_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      cases hdiv :
          checked_div
            (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool)
            (prev_state.xtzPool * 1000 +
              amount_to_N ctx.ctx_amount * 997) with
      | Err e =>
          rw [hdiv] at h
          cases h
      | Ok tokens_bought =>
          rw [hdiv] at h
          simp at h
          by_cases hmin : tokens_bought < param.minTokensBought
          · rw [if_pos hmin] at h
            cases h
          · rw [if_neg hmin] at h
            cases hsub :
                checked_sub prev_state.tokenPool tokens_bought with
            | Err e =>
                rw [hsub] at h
                cases h
            | Ok new_tokenPool =>
                rw [hsub] at h
                rcases h with ⟨hstate, _⟩
                have hdiv_eq := (div_eq hdiv).1
                have hsub_eq := (sub_eq hsub).1
                simp [hdiv_eq, hsub_eq]

theorem xtz_to_token_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @XtzToTokenParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.XtzToToken param))) =
        .Ok (new_state, new_acts)) :
    let tokens_bought :=
      (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool) /
        (prev_state.xtzPool * 1000 + amount_to_N ctx.ctx_amount * 997)
    new_state.tokenPool = prev_state.tokenPool - tokens_bought ∧
      new_state.xtzPool =
        prev_state.xtzPool + amount_to_N ctx.ctx_amount := by
  rw [← xtz_to_token_state_eq
    (Base := Base) null_address set_delegate_call h]
  simp

theorem xtz_to_token_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @XtzToTokenParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.XtzToToken param))) =
        .Ok (new_state, new_acts)) :
    let tokens_bought :=
      (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool) /
        (prev_state.xtzPool * 1000 + amount_to_N ctx.ctx_amount * 997)
    new_acts =
      [ token_transfer prev_state ctx.ctx_contract_address
          param.tokens_to tokens_bought ] := by
  unfold receive xtz_to_token at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.xtt_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      cases hdiv :
          checked_div
            (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool)
            (prev_state.xtzPool * 1000 +
              amount_to_N ctx.ctx_amount * 997) with
      | Err e =>
          rw [hdiv] at h
          cases h
      | Ok tokens_bought =>
          rw [hdiv] at h
          simp at h
          by_cases hmin : tokens_bought < param.minTokensBought
          · rw [if_pos hmin] at h
            cases h
          · rw [if_neg hmin] at h
            cases hsub :
                checked_sub prev_state.tokenPool tokens_bought with
            | Err e =>
                rw [hsub] at h
                cases h
            | Ok new_tokenPool =>
                rw [hsub] at h
                rcases h with ⟨_, hacts⟩
                have hdiv_eq := (div_eq hdiv).1
                simp [hdiv_eq]

theorem xtz_to_token_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @XtzToTokenParam Base) :
    let tokens_bought :=
      (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool) /
        (prev_state.xtzPool * 1000 + amount_to_N ctx.ctx_amount * 997)
    (prev_state.selfIsUpdatingTokenPool = false ∧
        chain.current_slot < param.xtt_deadline ∧
        (prev_state.xtzPool ≠ 0 ∨ 0 < ctx.ctx_amount) ∧
        param.minTokensBought ≤ tokens_bought ∧
        tokens_bought ≤ prev_state.tokenPool) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.XtzToToken param))) =
          .Ok (new_state, new_acts) := by
  dsimp
  constructor
  · rintro ⟨hself, hdeadline, hdenom_src, hmin, hbalance⟩
    let paid := amount_to_N ctx.ctx_amount
    let denom := prev_state.xtzPool * 1000 + paid * 997
    let tokens_bought :=
      paid * 997 * prev_state.tokenPool / denom
    let new_state :=
      { prev_state with
        tokenPool := prev_state.tokenPool - tokens_bought,
        xtzPool := prev_state.xtzPool + paid }
    refine ⟨new_state,
      [token_transfer prev_state ctx.ctx_contract_address
        param.tokens_to tokens_bought], ?_⟩
    have hdeadline_not : ¬ param.xtt_deadline ≤ chain.current_slot :=
      Nat.not_le_of_gt hdeadline
    have hdenom_pos : 0 < denom := by
      rcases hdenom_src with hpool | hpaid
      · dsimp [denom, paid]
        exact Nat.add_pos_left
          (Nat.mul_pos (Nat.pos_of_ne_zero hpool) (by decide)) _
      · have hpaid_pos : 0 < paid := by
          dsimp [paid, amount_to_N]
          rw [Int.lt_toNat]
          exact hpaid
        dsimp [denom]
        exact Nat.add_pos_right _
          (Nat.mul_pos hpaid_pos (by decide))
    have hdiv :
        checked_div (paid * 997 * prev_state.tokenPool) denom =
          .Ok tokens_bought := by
      dsimp [tokens_bought]
      exact checked_div_ok_of_ne_zero (Nat.ne_of_gt hdenom_pos)
    have hmin_not : ¬ tokens_bought < param.minTokensBought :=
      not_lt.mpr hmin
    have hsub :
        checked_sub prev_state.tokenPool tokens_bought =
          .Ok (prev_state.tokenPool - tokens_bought) :=
      checked_sub_ok_of_le hbalance
    unfold receive xtz_to_token
    simp [hself]
    rw [if_neg hdeadline_not]
    rw [hdiv]
    simp
    rw [if_neg hmin_not, hsub]
    simp [new_state, paid, tokens_bought, denom, hself]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive xtz_to_token at h
    simp at h
    by_cases hself : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself] at h
      cases h
    · rw [if_neg hself] at h
      by_cases hdeadline : param.xtt_deadline ≤ chain.current_slot
      · rw [if_pos hdeadline] at h
        cases h
      · rw [if_neg hdeadline] at h
        cases hdiv :
            checked_div
              (amount_to_N ctx.ctx_amount * 997 * prev_state.tokenPool)
              (prev_state.xtzPool * 1000 +
                amount_to_N ctx.ctx_amount * 997) with
        | Err e =>
            rw [hdiv] at h
            cases h
        | Ok tokens_bought =>
            rw [hdiv] at h
            simp at h
            by_cases hmin : tokens_bought < param.minTokensBought
            · rw [if_pos hmin] at h
              cases h
            · rw [if_neg hmin] at h
              cases hsub :
                  checked_sub prev_state.tokenPool tokens_bought with
              | Err e =>
                  rw [hsub] at h
                  cases h
              | Ok new_tokenPool =>
                  have hdiv_info := div_eq hdiv
                  have hsub_info := sub_eq hsub
                  refine
                    ⟨bool_false_of_not_true hself,
                      Nat.lt_of_not_ge hdeadline, ?_, ?_, ?_⟩
                  · by_cases hpool : prev_state.xtzPool = 0
                    · right
                      have hpaid_ne :
                          amount_to_N ctx.ctx_amount ≠ 0 := by
                        intro hpaid
                        apply hdiv_info.2
                        simp [hpool, hpaid]
                      unfold amount_to_N at hpaid_ne
                      have hpaid_pos :
                          0 < ctx.ctx_amount.toNat :=
                        Nat.pos_of_ne_zero hpaid_ne
                      exact Int.lt_toNat.mp hpaid_pos
                    · exact Or.inl hpool
                  · have hle : param.minTokensBought ≤ tokens_bought :=
                      le_of_not_gt hmin
                    simpa [hdiv_info.1] using hle
                  · have hle : tokens_bought ≤ prev_state.tokenPool :=
                      hsub_info.2
                    simpa [hdiv_info.1] using hle

theorem token_to_xtz_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TokenToXtzParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.TokenToXtz param))) =
        .Ok (new_state, new_acts)) :
    let xtz_bought :=
      (param.tokensSold * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold * 997)
    { prev_state with
      tokenPool := prev_state.tokenPool + param.tokensSold,
      xtzPool := prev_state.xtzPool - xtz_bought } =
      new_state := by
  unfold receive token_to_xtz at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.ttx_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      by_cases hamount : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount] at h
        cases h
      · rw [if_neg hamount] at h
        cases hdiv :
            checked_div
              (param.tokensSold * 997 * prev_state.xtzPool)
              (prev_state.tokenPool * 1000 +
                param.tokensSold * 997) with
        | Err e =>
            rw [hdiv] at h
            cases h
        | Ok xtz_bought =>
            rw [hdiv] at h
            simp at h
            by_cases hmin : xtz_bought < param.minXtzBought
            · rw [if_pos hmin] at h
              cases h
            · rw [if_neg hmin] at h
              cases hsub : checked_sub prev_state.xtzPool xtz_bought with
              | Err e =>
                  rw [hsub] at h
                  cases h
              | Ok new_xtzPool =>
                  rw [hsub] at h
                  cases hxtz : xtz_transfer param.xtz_to xtz_bought with
                  | Err e =>
                      rw [hxtz] at h
                      cases h
                  | Ok op_tez =>
                      rw [hxtz] at h
                      rcases h with ⟨hstate, _⟩
                      have hdiv_eq := (div_eq hdiv).1
                      have hsub_eq := (sub_eq hsub).1
                      simp [hdiv_eq, hsub_eq]

theorem token_to_xtz_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TokenToXtzParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.TokenToXtz param))) =
        .Ok (new_state, new_acts)) :
    let xtz_bought :=
      (param.tokensSold * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold * 997)
    new_state.tokenPool = prev_state.tokenPool + param.tokensSold ∧
      new_state.xtzPool = prev_state.xtzPool - xtz_bought := by
  rw [← token_to_xtz_state_eq
    (Base := Base) null_address set_delegate_call h]
  simp

theorem token_to_xtz_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TokenToXtzParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.TokenToXtz param))) =
        .Ok (new_state, new_acts)) :
    let xtz_bought :=
      (param.tokensSold * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold * 997)
    new_acts =
      [ token_transfer prev_state ctx.ctx_from ctx.ctx_contract_address
          param.tokensSold,
        .act_transfer param.xtz_to (N_to_amount xtz_bought) ] := by
  unfold receive token_to_xtz at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.ttx_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      by_cases hamount : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount] at h
        cases h
      · rw [if_neg hamount] at h
        cases hdiv :
            checked_div
              (param.tokensSold * 997 * prev_state.xtzPool)
              (prev_state.tokenPool * 1000 +
                param.tokensSold * 997) with
        | Err e =>
            rw [hdiv] at h
            cases h
        | Ok xtz_bought =>
            rw [hdiv] at h
            simp at h
            by_cases hmin : xtz_bought < param.minXtzBought
            · rw [if_pos hmin] at h
              cases h
            · rw [if_neg hmin] at h
              cases hsub : checked_sub prev_state.xtzPool xtz_bought with
              | Err e =>
                  rw [hsub] at h
                  cases h
              | Ok new_xtzPool =>
                  rw [hsub] at h
                  cases hxtz : xtz_transfer param.xtz_to xtz_bought with
                  | Err e =>
                      rw [hxtz] at h
                      cases h
                  | Ok op_tez =>
                      rw [hxtz] at h
                      rcases h with ⟨_, hacts⟩
                      have hdiv_eq := (div_eq hdiv).1
                      have hxtz_shape := xtz_transfer_ok_shape hxtz
                      simp [hdiv_eq, hxtz_shape.2]

theorem token_to_xtz_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @TokenToXtzParam Base) :
    let xtz_bought :=
      (param.tokensSold * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold * 997)
    (prev_state.selfIsUpdatingTokenPool = false ∧
        chain.current_slot < param.ttx_deadline ∧
        non_zero_amount ctx.ctx_amount = false ∧
        (prev_state.tokenPool ≠ 0 ∨ param.tokensSold ≠ 0) ∧
        param.minXtzBought ≤ xtz_bought ∧
        xtz_bought ≤ prev_state.xtzPool ∧
        Base.address_is_contract param.xtz_to = false) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.TokenToXtz param))) =
          .Ok (new_state, new_acts) := by
  dsimp
  constructor
  · rintro ⟨hself, hdeadline, hamount, hdenom_src, hmin,
      hbalance, hcontract⟩
    let denom := prev_state.tokenPool * 1000 + param.tokensSold * 997
    let xtz_bought :=
      param.tokensSold * 997 * prev_state.xtzPool / denom
    let new_state :=
      { prev_state with
        tokenPool := prev_state.tokenPool + param.tokensSold,
        xtzPool := prev_state.xtzPool - xtz_bought }
    refine ⟨new_state,
      [ token_transfer prev_state ctx.ctx_from ctx.ctx_contract_address
          param.tokensSold,
        .act_transfer param.xtz_to (N_to_amount xtz_bought) ], ?_⟩
    have hdeadline_not : ¬ param.ttx_deadline ≤ chain.current_slot :=
      Nat.not_le_of_gt hdeadline
    have hdenom_pos : 0 < denom := by
      rcases hdenom_src with hpool | hsold
      · dsimp [denom]
        exact Nat.add_pos_left
          (Nat.mul_pos (Nat.pos_of_ne_zero hpool) (by decide)) _
      · dsimp [denom]
        exact Nat.add_pos_right _
          (Nat.mul_pos (Nat.pos_of_ne_zero hsold) (by decide))
    have hdiv :
        checked_div
          (param.tokensSold * 997 * prev_state.xtzPool) denom =
          .Ok xtz_bought := by
      dsimp [xtz_bought]
      exact checked_div_ok_of_ne_zero (Nat.ne_of_gt hdenom_pos)
    have hmin_not : ¬ xtz_bought < param.minXtzBought :=
      not_lt.mpr hmin
    have hsub :
        checked_sub prev_state.xtzPool xtz_bought =
          .Ok (prev_state.xtzPool - xtz_bought) :=
      checked_sub_ok_of_le hbalance
    have hxtz :
        xtz_transfer param.xtz_to xtz_bought =
          .Ok (.act_transfer param.xtz_to (N_to_amount xtz_bought)) :=
      xtz_transfer_ok_of_not_contract hcontract
    unfold receive token_to_xtz
    simp [hself]
    rw [if_neg hdeadline_not, hamount, hdiv]
    simp
    rw [if_neg hmin_not, hsub]
    simp
    rw [hxtz]
    simp [new_state, denom, xtz_bought, hself]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive token_to_xtz at h
    simp at h
    by_cases hself : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself] at h
      cases h
    · rw [if_neg hself] at h
      by_cases hdeadline : param.ttx_deadline ≤ chain.current_slot
      · rw [if_pos hdeadline] at h
        cases h
      · rw [if_neg hdeadline] at h
        by_cases hamount : non_zero_amount ctx.ctx_amount = true
        · rw [if_pos hamount] at h
          cases h
        · rw [if_neg hamount] at h
          cases hdiv :
              checked_div
                (param.tokensSold * 997 * prev_state.xtzPool)
                (prev_state.tokenPool * 1000 +
                  param.tokensSold * 997) with
          | Err e =>
              rw [hdiv] at h
              cases h
          | Ok xtz_bought =>
              rw [hdiv] at h
              simp at h
              by_cases hmin : xtz_bought < param.minXtzBought
              · rw [if_pos hmin] at h
                cases h
              · rw [if_neg hmin] at h
                cases hsub :
                    checked_sub prev_state.xtzPool xtz_bought with
                | Err e =>
                    rw [hsub] at h
                    cases h
                | Ok new_xtzPool =>
                    rw [hsub] at h
                    cases hxtz : xtz_transfer param.xtz_to xtz_bought with
                    | Err e =>
                        rw [hxtz] at h
                        cases h
                    | Ok op_tez =>
                        have hdiv_info := div_eq hdiv
                        have hsub_info := sub_eq hsub
                        have hxtz_info := xtz_transfer_ok_shape hxtz
                        refine
                          ⟨bool_false_of_not_true hself,
                            Nat.lt_of_not_ge hdeadline,
                            bool_false_of_not_true hamount, ?_, ?_, ?_,
                            hxtz_info.1⟩
                        · by_cases hpool : prev_state.tokenPool = 0
                          · right
                            intro hsold
                            apply hdiv_info.2
                            simp [hpool, hsold]
                          · exact Or.inl hpool
                        · have hle : param.minXtzBought ≤ xtz_bought :=
                            le_of_not_gt hmin
                          simpa [hdiv_info.1] using hle
                        · have hle : xtz_bought ≤ prev_state.xtzPool :=
                            hsub_info.2
                          simpa [hdiv_info.1] using hle

theorem token_to_token_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TokenToTokenParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.TokenToToken param))) =
        .Ok (new_state, new_acts)) :
    let xtz_bought :=
      (param.tokensSold_ * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold_ * 997)
    { prev_state with
      tokenPool := prev_state.tokenPool + param.tokensSold_,
      xtzPool := prev_state.xtzPool - xtz_bought } =
      new_state := by
  unfold receive token_to_token at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hdeadline : param.ttt_deadline ≤ chain.current_slot
      · rw [if_pos hdeadline] at h
        cases h
      · rw [if_neg hdeadline] at h
        cases hdiv :
            checked_div
              (param.tokensSold_ * 997 * prev_state.xtzPool)
              (prev_state.tokenPool * 1000 +
                param.tokensSold_ * 997) with
        | Err e =>
            rw [hdiv] at h
            cases h
        | Ok xtz_bought =>
            rw [hdiv] at h
            simp at h
            cases hsub : checked_sub prev_state.xtzPool xtz_bought with
            | Err e =>
                rw [hsub] at h
                cases h
            | Ok new_xtzPool =>
                rw [hsub] at h
                rcases h with ⟨hstate, _⟩
                have hdiv_eq := (div_eq hdiv).1
                have hsub_eq := (sub_eq hsub).1
                simp [hdiv_eq, hsub_eq]

theorem token_to_token_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TokenToTokenParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.TokenToToken param))) =
        .Ok (new_state, new_acts)) :
    let xtz_bought :=
      (param.tokensSold_ * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold_ * 997)
    new_state.tokenPool = prev_state.tokenPool + param.tokensSold_ ∧
      new_state.xtzPool = prev_state.xtzPool - xtz_bought := by
  rw [← token_to_token_state_eq
    (Base := Base) null_address set_delegate_call h]
  simp

theorem token_to_token_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TokenToTokenParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.TokenToToken param))) =
        .Ok (new_state, new_acts)) :
    let xtz_bought :=
      (param.tokensSold_ * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold_ * 997)
    new_acts =
      [ token_transfer prev_state ctx.ctx_from ctx.ctx_contract_address
          param.tokensSold_,
        call_to_other_token param.outputDexterContract xtz_bought
          (.other_msg
            (.XtzToToken
              { tokens_to := param.to_,
                minTokensBought := param.minTokensBought_,
                xtt_deadline := param.ttt_deadline })) ] := by
  unfold receive token_to_token at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hamount : non_zero_amount ctx.ctx_amount = true
    · rw [if_pos hamount] at h
      cases h
    · rw [if_neg hamount] at h
      by_cases hdeadline : param.ttt_deadline ≤ chain.current_slot
      · rw [if_pos hdeadline] at h
        cases h
      · rw [if_neg hdeadline] at h
        cases hdiv :
            checked_div
              (param.tokensSold_ * 997 * prev_state.xtzPool)
              (prev_state.tokenPool * 1000 +
                param.tokensSold_ * 997) with
        | Err e =>
            rw [hdiv] at h
            cases h
        | Ok xtz_bought =>
            rw [hdiv] at h
            simp at h
            cases hsub : checked_sub prev_state.xtzPool xtz_bought with
            | Err e =>
                rw [hsub] at h
                cases h
            | Ok new_xtzPool =>
                rw [hsub] at h
                rcases h with ⟨_, hacts⟩
                have hdiv_eq := (div_eq hdiv).1
                simp [hdiv_eq]

theorem token_to_token_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @TokenToTokenParam Base) :
    let xtz_bought :=
      (param.tokensSold_ * 997 * prev_state.xtzPool) /
        (prev_state.tokenPool * 1000 + param.tokensSold_ * 997)
    (prev_state.selfIsUpdatingTokenPool = false ∧
        non_zero_amount ctx.ctx_amount = false ∧
        chain.current_slot < param.ttt_deadline ∧
        (prev_state.tokenPool ≠ 0 ∨ param.tokensSold_ ≠ 0) ∧
        xtz_bought ≤ prev_state.xtzPool) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.TokenToToken param))) =
          .Ok (new_state, new_acts) := by
  dsimp
  constructor
  · rintro ⟨hself, hamount, hdeadline, hdenom_src, hbalance⟩
    let denom := prev_state.tokenPool * 1000 + param.tokensSold_ * 997
    let xtz_bought :=
      param.tokensSold_ * 997 * prev_state.xtzPool / denom
    let new_state :=
      { prev_state with
        tokenPool := prev_state.tokenPool + param.tokensSold_,
        xtzPool := prev_state.xtzPool - xtz_bought }
    refine ⟨new_state,
      [ token_transfer prev_state ctx.ctx_from ctx.ctx_contract_address
          param.tokensSold_,
        call_to_other_token param.outputDexterContract xtz_bought
          (.other_msg
            (.XtzToToken
              { tokens_to := param.to_,
                minTokensBought := param.minTokensBought_,
                xtt_deadline := param.ttt_deadline })) ], ?_⟩
    have hdeadline_not : ¬ param.ttt_deadline ≤ chain.current_slot :=
      Nat.not_le_of_gt hdeadline
    have hdenom_pos : 0 < denom := by
      rcases hdenom_src with hpool | hsold
      · dsimp [denom]
        exact Nat.add_pos_left
          (Nat.mul_pos (Nat.pos_of_ne_zero hpool) (by decide)) _
      · dsimp [denom]
        exact Nat.add_pos_right _
          (Nat.mul_pos (Nat.pos_of_ne_zero hsold) (by decide))
    have hdiv :
        checked_div
          (param.tokensSold_ * 997 * prev_state.xtzPool) denom =
          .Ok xtz_bought := by
      dsimp [xtz_bought]
      exact checked_div_ok_of_ne_zero (Nat.ne_of_gt hdenom_pos)
    have hsub :
        checked_sub prev_state.xtzPool xtz_bought =
          .Ok (prev_state.xtzPool - xtz_bought) :=
      checked_sub_ok_of_le hbalance
    unfold receive token_to_token
    simp [hself]
    rw [hamount, if_neg hdeadline_not, hdiv]
    simp
    rw [hsub]
    simp [new_state, denom, xtz_bought, hself]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive token_to_token at h
    simp at h
    by_cases hself : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself] at h
      cases h
    · rw [if_neg hself] at h
      by_cases hamount : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount] at h
        cases h
      · rw [if_neg hamount] at h
        by_cases hdeadline : param.ttt_deadline ≤ chain.current_slot
        · rw [if_pos hdeadline] at h
          cases h
        · rw [if_neg hdeadline] at h
          cases hdiv :
              checked_div
                (param.tokensSold_ * 997 * prev_state.xtzPool)
                (prev_state.tokenPool * 1000 +
                  param.tokensSold_ * 997) with
          | Err e =>
              rw [hdiv] at h
              cases h
          | Ok xtz_bought =>
              rw [hdiv] at h
              simp at h
              cases hsub : checked_sub prev_state.xtzPool xtz_bought with
              | Err e =>
                  rw [hsub] at h
                  cases h
              | Ok new_xtzPool =>
                  have hdiv_info := div_eq hdiv
                  have hsub_info := sub_eq hsub
                  refine
                    ⟨bool_false_of_not_true hself,
                      bool_false_of_not_true hamount,
                      Nat.lt_of_not_ge hdeadline, ?_, ?_⟩
                  · by_cases hpool : prev_state.tokenPool = 0
                    · right
                      intro hsold
                      apply hdiv_info.2
                      simp [hpool, hsold]
                    · exact Or.inl hpool
                  · have hle : xtz_bought ≤ prev_state.xtzPool :=
                      hsub_info.2
                    simpa [hdiv_info.1] using hle

theorem remove_liquidity_state_eq
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @RemoveLiquidityParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.RemoveLiquidity param))) =
        .Ok (new_state, new_acts)) :
    let xtz_withdrawn :=
      param.lqtBurned * prev_state.xtzPool / prev_state.lqtTotal
    let tokens_withdrawn :=
      param.lqtBurned * prev_state.tokenPool / prev_state.lqtTotal
    { prev_state with
      lqtTotal := prev_state.lqtTotal - param.lqtBurned,
      tokenPool := prev_state.tokenPool - tokens_withdrawn,
      xtzPool := prev_state.xtzPool - xtz_withdrawn } =
      new_state := by
  unfold receive remove_liquidity at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.remove_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      by_cases hamount : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount] at h
        cases h
      · rw [if_neg hamount] at h
        cases hdiv_xtz :
            checked_div (param.lqtBurned * prev_state.xtzPool)
              prev_state.lqtTotal with
        | Err e =>
            rw [hdiv_xtz] at h
            cases h
        | Ok xtz_withdrawn =>
            rw [hdiv_xtz] at h
            simp at h
            cases hdiv_tok :
                checked_div (param.lqtBurned * prev_state.tokenPool)
                  prev_state.lqtTotal with
            | Err e =>
                rw [hdiv_tok] at h
                cases h
            | Ok tokens_withdrawn =>
                rw [hdiv_tok] at h
                simp at h
                by_cases hmin_xtz :
                    xtz_withdrawn < param.minXtzWithdrawn
                · rw [if_pos hmin_xtz] at h
                  cases h
                · rw [if_neg hmin_xtz] at h
                  by_cases hmin_tok :
                      tokens_withdrawn < param.minTokensWithdrawn
                  · rw [if_pos hmin_tok] at h
                    cases h
                  · rw [if_neg hmin_tok] at h
                    cases hsub_lqt :
                        checked_sub prev_state.lqtTotal
                          param.lqtBurned with
                    | Err e =>
                        rw [hsub_lqt] at h
                        cases h
                    | Ok new_lqtPool =>
                        rw [hsub_lqt] at h
                        simp at h
                        cases hsub_tok :
                            checked_sub prev_state.tokenPool
                              tokens_withdrawn with
                        | Err e =>
                            rw [hsub_tok] at h
                            cases h
                        | Ok new_tokenPool =>
                            rw [hsub_tok] at h
                            simp at h
                            cases hsub_xtz :
                                checked_sub prev_state.xtzPool
                                  xtz_withdrawn with
                            | Err e =>
                                rw [hsub_xtz] at h
                                cases h
                            | Ok new_xtzPool =>
                                rw [hsub_xtz] at h
                                simp at h
                                cases hmint :
                                    mint_or_burn null_address prev_state
                                      ctx.ctx_from
                                      (-(Int.ofNat param.lqtBurned)) with
                                | Err e =>
                                    have hmint' :
                                        mint_or_burn null_address prev_state
                                          ctx.ctx_from
                                          (-(↑param.lqtBurned : Int)) =
                                            .Err e := hmint
                                    rw [hmint'] at h
                                    cases h
                                | Ok op_lqt =>
                                    have hmint' :
                                        mint_or_burn null_address prev_state
                                          ctx.ctx_from
                                          (-(↑param.lqtBurned : Int)) =
                                            .Ok op_lqt := hmint
                                    rw [hmint'] at h
                                    cases hxtz :
                                        xtz_transfer param.liquidity_to
                                          xtz_withdrawn with
                                    | Err e =>
                                        rw [hxtz] at h
                                        cases h
                                    | Ok op_xtz =>
                                        rw [hxtz] at h
                                        rcases h with ⟨hstate, _⟩
                                        have hdiv_xtz_eq :=
                                          (div_eq hdiv_xtz).1
                                        have hdiv_tok_eq :=
                                          (div_eq hdiv_tok).1
                                        have hsub_lqt_eq :=
                                          (sub_eq hsub_lqt).1
                                        have hsub_tok_eq :=
                                          (sub_eq hsub_tok).1
                                        have hsub_xtz_eq :=
                                          (sub_eq hsub_xtz).1
                                        simp [hdiv_xtz_eq, hdiv_tok_eq,
                                          hsub_lqt_eq, hsub_tok_eq,
                                          hsub_xtz_eq]

theorem remove_liquidity_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @RemoveLiquidityParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.RemoveLiquidity param))) =
        .Ok (new_state, new_acts)) :
    let xtz_withdrawn :=
      param.lqtBurned * prev_state.xtzPool / prev_state.lqtTotal
    let tokens_withdrawn :=
      param.lqtBurned * prev_state.tokenPool / prev_state.lqtTotal
    new_state.lqtTotal = prev_state.lqtTotal - param.lqtBurned ∧
      new_state.tokenPool = prev_state.tokenPool - tokens_withdrawn ∧
      new_state.xtzPool = prev_state.xtzPool - xtz_withdrawn := by
  rw [← remove_liquidity_state_eq
    (Base := Base) null_address set_delegate_call h]
  simp

theorem remove_liquidity_new_acts_correct
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @RemoveLiquidityParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive null_address set_delegate_call chain ctx prev_state
      (some (.other_msg (.RemoveLiquidity param))) =
        .Ok (new_state, new_acts)) :
    let xtz_withdrawn :=
      param.lqtBurned * prev_state.xtzPool / prev_state.lqtTotal
    let tokens_withdrawn :=
      param.lqtBurned * prev_state.tokenPool / prev_state.lqtTotal
    new_acts =
      [ call_liquidity_token prev_state.lqtAddress 0
          (.msg_mint_or_burn
            { target := ctx.ctx_from,
              quantity := -(↑param.lqtBurned : Int) }),
        token_transfer prev_state ctx.ctx_contract_address
          param.liquidity_to tokens_withdrawn,
        .act_transfer param.liquidity_to (N_to_amount xtz_withdrawn) ] := by
  unfold receive remove_liquidity at h
  simp at h
  by_cases hself : prev_state.selfIsUpdatingTokenPool = true
  · rw [if_pos hself] at h
    cases h
  · rw [if_neg hself] at h
    by_cases hdeadline : param.remove_deadline ≤ chain.current_slot
    · rw [if_pos hdeadline] at h
      cases h
    · rw [if_neg hdeadline] at h
      by_cases hamount : non_zero_amount ctx.ctx_amount = true
      · rw [if_pos hamount] at h
        cases h
      · rw [if_neg hamount] at h
        cases hdiv_xtz :
            checked_div (param.lqtBurned * prev_state.xtzPool)
              prev_state.lqtTotal with
        | Err e =>
            rw [hdiv_xtz] at h
            cases h
        | Ok xtz_withdrawn =>
            rw [hdiv_xtz] at h
            simp at h
            cases hdiv_tok :
                checked_div (param.lqtBurned * prev_state.tokenPool)
                  prev_state.lqtTotal with
            | Err e =>
                rw [hdiv_tok] at h
                cases h
            | Ok tokens_withdrawn =>
                rw [hdiv_tok] at h
                simp at h
                by_cases hmin_xtz :
                    xtz_withdrawn < param.minXtzWithdrawn
                · rw [if_pos hmin_xtz] at h
                  cases h
                · rw [if_neg hmin_xtz] at h
                  by_cases hmin_tok :
                      tokens_withdrawn < param.minTokensWithdrawn
                  · rw [if_pos hmin_tok] at h
                    cases h
                  · rw [if_neg hmin_tok] at h
                    cases hsub_lqt :
                        checked_sub prev_state.lqtTotal
                          param.lqtBurned with
                    | Err e =>
                        rw [hsub_lqt] at h
                        cases h
                    | Ok new_lqtPool =>
                        rw [hsub_lqt] at h
                        simp at h
                        cases hsub_tok :
                            checked_sub prev_state.tokenPool
                              tokens_withdrawn with
                        | Err e =>
                            rw [hsub_tok] at h
                            cases h
                        | Ok new_tokenPool =>
                            rw [hsub_tok] at h
                            simp at h
                            cases hsub_xtz :
                                checked_sub prev_state.xtzPool
                                  xtz_withdrawn with
                            | Err e =>
                                rw [hsub_xtz] at h
                                cases h
                            | Ok new_xtzPool =>
                                rw [hsub_xtz] at h
                                simp at h
                                cases hmint :
                                    mint_or_burn null_address prev_state
                                      ctx.ctx_from
                                      (-(Int.ofNat param.lqtBurned)) with
                                | Err e =>
                                    have hmint' :
                                        mint_or_burn null_address prev_state
                                          ctx.ctx_from
                                          (-(↑param.lqtBurned : Int)) =
                                            .Err e := hmint
                                    rw [hmint'] at h
                                    cases h
                                | Ok op_lqt =>
                                    have hmint' :
                                        mint_or_burn null_address prev_state
                                          ctx.ctx_from
                                          (-(↑param.lqtBurned : Int)) =
                                            .Ok op_lqt := hmint
                                    rw [hmint'] at h
                                    cases hxtz :
                                        xtz_transfer param.liquidity_to
                                          xtz_withdrawn with
                                    | Err e =>
                                        rw [hxtz] at h
                                        cases h
                                    | Ok op_xtz =>
                                        rw [hxtz] at h
                                        rcases h with ⟨_, hacts⟩
                                        have hdiv_xtz_eq :=
                                          (div_eq hdiv_xtz).1
                                        have hdiv_tok_eq :=
                                          (div_eq hdiv_tok).1
                                        have hmint_shape :=
                                          mint_or_burn_ok_shape
                                            (Base := Base) null_address hmint
                                        have hxtz_shape :=
                                          xtz_transfer_ok_shape hxtz
                                        simp [hdiv_xtz_eq, hdiv_tok_eq,
                                          hmint_shape.2, hxtz_shape.2]

theorem remove_liquidity_is_some
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base)
    (param : @RemoveLiquidityParam Base) :
    let xtz_withdrawn :=
      param.lqtBurned * prev_state.xtzPool / prev_state.lqtTotal
    let tokens_withdrawn :=
      param.lqtBurned * prev_state.tokenPool / prev_state.lqtTotal
    (prev_state.selfIsUpdatingTokenPool = false ∧
        chain.current_slot < param.remove_deadline ∧
        non_zero_amount ctx.ctx_amount = false ∧
        prev_state.lqtTotal ≠ 0 ∧
        param.minXtzWithdrawn ≤ xtz_withdrawn ∧
        param.minTokensWithdrawn ≤ tokens_withdrawn ∧
        param.lqtBurned ≤ prev_state.lqtTotal ∧
        tokens_withdrawn ≤ prev_state.tokenPool ∧
        xtz_withdrawn ≤ prev_state.xtzPool ∧
        prev_state.lqtAddress ≠ null_address ∧
        Base.address_is_contract param.liquidity_to = false) ↔
      ∃ new_state new_acts,
        receive null_address set_delegate_call chain ctx prev_state
          (some (.other_msg (.RemoveLiquidity param))) =
          .Ok (new_state, new_acts) := by
  dsimp
  constructor
  · rintro ⟨hself, hdeadline, hamount, htotal, hmin_xtz,
      hmin_tok, hlqt_burned, htok_pool, hxtz_pool, hlqt_addr,
      hcontract⟩
    let xtz_withdrawn :=
      param.lqtBurned * prev_state.xtzPool / prev_state.lqtTotal
    let tokens_withdrawn :=
      param.lqtBurned * prev_state.tokenPool / prev_state.lqtTotal
    let op_lqt :=
      call_liquidity_token prev_state.lqtAddress 0
        (.msg_mint_or_burn
          { target := ctx.ctx_from,
            quantity := -(↑param.lqtBurned : Int) })
    let new_state :=
      { prev_state with
        lqtTotal := prev_state.lqtTotal - param.lqtBurned,
        tokenPool := prev_state.tokenPool - tokens_withdrawn,
        xtzPool := prev_state.xtzPool - xtz_withdrawn }
    refine ⟨new_state,
      [ op_lqt,
        token_transfer prev_state ctx.ctx_contract_address
          param.liquidity_to tokens_withdrawn,
        .act_transfer param.liquidity_to (N_to_amount xtz_withdrawn) ],
      ?_⟩
    have hdeadline_not :
        ¬ param.remove_deadline ≤ chain.current_slot :=
      Nat.not_le_of_gt hdeadline
    have hdiv_xtz :
        checked_div (param.lqtBurned * prev_state.xtzPool)
          prev_state.lqtTotal = .Ok xtz_withdrawn := by
      dsimp [xtz_withdrawn]
      exact checked_div_ok_of_ne_zero htotal
    have hdiv_tok :
        checked_div (param.lqtBurned * prev_state.tokenPool)
          prev_state.lqtTotal = .Ok tokens_withdrawn := by
      dsimp [tokens_withdrawn]
      exact checked_div_ok_of_ne_zero htotal
    have hmin_xtz_not :
        ¬ xtz_withdrawn < param.minXtzWithdrawn :=
      not_lt.mpr hmin_xtz
    have hmin_tok_not :
        ¬ tokens_withdrawn < param.minTokensWithdrawn :=
      not_lt.mpr hmin_tok
    have hsub_lqt :
        checked_sub prev_state.lqtTotal param.lqtBurned =
          .Ok (prev_state.lqtTotal - param.lqtBurned) :=
      checked_sub_ok_of_le hlqt_burned
    have hsub_tok :
        checked_sub prev_state.tokenPool tokens_withdrawn =
          .Ok (prev_state.tokenPool - tokens_withdrawn) :=
      checked_sub_ok_of_le htok_pool
    have hsub_xtz :
        checked_sub prev_state.xtzPool xtz_withdrawn =
          .Ok (prev_state.xtzPool - xtz_withdrawn) :=
      checked_sub_ok_of_le hxtz_pool
    have hmint :
        mint_or_burn null_address prev_state ctx.ctx_from
          (-(↑param.lqtBurned : Int)) = .Ok op_lqt := by
      dsimp [op_lqt]
      exact mint_or_burn_ok_of_ne_null null_address prev_state
        ctx.ctx_from (-(↑param.lqtBurned : Int)) hlqt_addr
    have hxtz :
        xtz_transfer param.liquidity_to xtz_withdrawn =
          .Ok
            (.act_transfer param.liquidity_to
              (N_to_amount xtz_withdrawn)) :=
      xtz_transfer_ok_of_not_contract hcontract
    unfold receive remove_liquidity
    simp [hself]
    rw [if_neg hdeadline_not, hamount, hdiv_xtz]
    simp
    rw [hdiv_tok]
    simp
    rw [if_neg hmin_xtz_not, if_neg hmin_tok_not, hsub_lqt]
    simp
    rw [hsub_tok]
    simp
    rw [hsub_xtz]
    simp
    rw [hmint, hxtz]
    simp [new_state, op_lqt, xtz_withdrawn, tokens_withdrawn, hself]
  · rintro ⟨new_state, new_acts, h⟩
    unfold receive remove_liquidity at h
    simp at h
    by_cases hself : prev_state.selfIsUpdatingTokenPool = true
    · rw [if_pos hself] at h
      cases h
    · rw [if_neg hself] at h
      by_cases hdeadline : param.remove_deadline ≤ chain.current_slot
      · rw [if_pos hdeadline] at h
        cases h
      · rw [if_neg hdeadline] at h
        by_cases hamount : non_zero_amount ctx.ctx_amount = true
        · rw [if_pos hamount] at h
          cases h
        · rw [if_neg hamount] at h
          cases hdiv_xtz :
              checked_div (param.lqtBurned * prev_state.xtzPool)
                prev_state.lqtTotal with
          | Err e =>
              rw [hdiv_xtz] at h
              cases h
          | Ok xtz_withdrawn =>
              rw [hdiv_xtz] at h
              simp at h
              cases hdiv_tok :
                  checked_div (param.lqtBurned * prev_state.tokenPool)
                    prev_state.lqtTotal with
              | Err e =>
                  rw [hdiv_tok] at h
                  cases h
              | Ok tokens_withdrawn =>
                  rw [hdiv_tok] at h
                  simp at h
                  by_cases hmin_xtz :
                      xtz_withdrawn < param.minXtzWithdrawn
                  · rw [if_pos hmin_xtz] at h
                    cases h
                  · rw [if_neg hmin_xtz] at h
                    by_cases hmin_tok :
                        tokens_withdrawn < param.minTokensWithdrawn
                    · rw [if_pos hmin_tok] at h
                      cases h
                    · rw [if_neg hmin_tok] at h
                      cases hsub_lqt :
                          checked_sub prev_state.lqtTotal
                            param.lqtBurned with
                      | Err e =>
                          rw [hsub_lqt] at h
                          cases h
                      | Ok new_lqtPool =>
                          rw [hsub_lqt] at h
                          simp at h
                          cases hsub_tok :
                              checked_sub prev_state.tokenPool
                                tokens_withdrawn with
                          | Err e =>
                              rw [hsub_tok] at h
                              cases h
                          | Ok new_tokenPool =>
                              rw [hsub_tok] at h
                              simp at h
                              cases hsub_xtz :
                                  checked_sub prev_state.xtzPool
                                    xtz_withdrawn with
                              | Err e =>
                                  rw [hsub_xtz] at h
                                  cases h
                              | Ok new_xtzPool =>
                                  rw [hsub_xtz] at h
                                  simp at h
                                  cases hmint :
                                      mint_or_burn null_address prev_state
                                        ctx.ctx_from
                                        (-(Int.ofNat param.lqtBurned)) with
                                  | Err e =>
                                      have hmint' :
                                          mint_or_burn null_address prev_state
                                            ctx.ctx_from
                                            (-(↑param.lqtBurned : Int)) =
                                              .Err e := hmint
                                      rw [hmint'] at h
                                      cases h
                                  | Ok op_lqt =>
                                      have hmint' :
                                          mint_or_burn null_address prev_state
                                            ctx.ctx_from
                                            (-(↑param.lqtBurned : Int)) =
                                              .Ok op_lqt := hmint
                                      rw [hmint'] at h
                                      cases hxtz :
                                          xtz_transfer param.liquidity_to
                                            xtz_withdrawn with
                                      | Err e =>
                                          rw [hxtz] at h
                                          cases h
                                      | Ok op_xtz =>
                                          have hdiv_xtz_info :=
                                            div_eq hdiv_xtz
                                          have hdiv_tok_info :=
                                            div_eq hdiv_tok
                                          have hsub_lqt_info :=
                                            sub_eq hsub_lqt
                                          have hsub_tok_info :=
                                            sub_eq hsub_tok
                                          have hsub_xtz_info :=
                                            sub_eq hsub_xtz
                                          have hmint_info :=
                                            mint_or_burn_ok_shape
                                              (Base := Base) null_address hmint
                                          have hxtz_info :=
                                            xtz_transfer_ok_shape hxtz
                                          refine
                                            ⟨bool_false_of_not_true hself,
                                              Nat.lt_of_not_ge hdeadline,
                                              bool_false_of_not_true hamount,
                                              hdiv_xtz_info.2, ?_, ?_,
                                              hsub_lqt_info.2, ?_, ?_,
                                              hmint_info.1, hxtz_info.1⟩
                                          · have hle :
                                                param.minXtzWithdrawn ≤
                                                  xtz_withdrawn :=
                                              le_of_not_gt hmin_xtz
                                            simpa [hdiv_xtz_info.1] using hle
                                          · have hle :
                                                param.minTokensWithdrawn ≤
                                                  tokens_withdrawn :=
                                              le_of_not_gt hmin_tok
                                            simpa [hdiv_tok_info.1] using hle
                                          · have hle :
                                                tokens_withdrawn ≤
                                                  prev_state.tokenPool :=
                                              hsub_tok_info.2
                                            simpa [hdiv_tok_info.1] using hle
                                          · have hle :
                                                xtz_withdrawn ≤
                                                  prev_state.xtzPool :=
                                              hsub_xtz_info.2
                                            simpa [hdiv_xtz_info.1] using hle

theorem init_state_eq
    (null_address : Base.Address) (chain : Chain)
    (ctx : @ContractCallContext Base) (setup : @Setup Base)
    {state : @State Base}
    (h : init null_address chain ctx setup = .Ok state) :
    state =
      { tokenPool := 0,
        xtzPool := 0,
        lqtTotal := setup.lqtTotal_,
        selfIsUpdatingTokenPool := false,
        freezeBaker := false,
        manager := setup.manager_,
        tokenAddress := setup.tokenAddress_,
        tokenId := setup.tokenId_,
        lqtAddress := null_address } := by
  unfold init at h
  cases h
  rfl

theorem init_correct
    (null_address : Base.Address) (chain : Chain)
    (ctx : @ContractCallContext Base) (setup : @Setup Base)
    {state : @State Base}
    (h : init null_address chain ctx setup = .Ok state) :
    state.tokenPool = 0 ∧
      state.xtzPool = 0 ∧
      state.lqtTotal = setup.lqtTotal_ ∧
      state.selfIsUpdatingTokenPool = false ∧
      state.freezeBaker = false ∧
      state.manager = setup.manager_ ∧
      state.tokenAddress = setup.tokenAddress_ ∧
      state.lqtAddress = null_address ∧
      state.tokenId = setup.tokenId_ := by
  rw [init_state_eq (Base := Base) null_address chain ctx setup h]
  simp

theorem init_is_some
    (null_address : Base.Address) (chain : Chain)
    (ctx : @ContractCallContext Base) (setup : @Setup Base) :
    ∃ state, init null_address chain ctx setup = .Ok state := by
  let state : @State Base :=
    { tokenPool := 0,
      xtzPool := 0,
      lqtTotal := setup.lqtTotal_,
      selfIsUpdatingTokenPool := false,
      freezeBaker := false,
      manager := setup.manager_,
      tokenAddress := setup.tokenAddress_,
      tokenId := setup.tokenId_,
      lqtAddress := null_address }
  exact ⟨state, rfl⟩

end ConCert.Examples.Dexter2.CPMM.Correct
