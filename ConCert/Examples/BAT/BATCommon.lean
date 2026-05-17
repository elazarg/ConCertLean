/- Proof-support definitions and lemmas from examples/bat/BATCommon.v. -/

import ConCert.Examples.BAT.BAT
import ConCert.Execution.BlockchainTheories
import Mathlib.Tactic.Linarith

namespace ConCert.Examples.BAT

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.Containers
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

def finalize_act (cstate : @State Base) (caddr : Base.Address) : @Action Base :=
  { act_origin := cstate.fundDeposit,
    act_from := cstate.fundDeposit,
    act_body := .act_call caddr 0 (serialize (Msg.finalize : @Msg Base)) }

def deploy_act (setup : @Setup Base)
    (contract : @Contract Base (@Setup Base) (@Msg Base) (@State Base) Error _ _ _ _)
    (from_ : Base.Address) : @Action Base :=
  { act_origin := from_,
    act_from := from_,
    act_body := create_deployment 0 contract setup }

omit Base in
theorem Nat_mod_le (n m : Nat) : n % m ≤ n :=
  Nat.mod_le n m

omit Base in
theorem Nat_sub_add_mod (n m p : Nat) :
    n ≤ p → p - n + n % m ≤ p := by
  intro hn
  calc
    p - n + n % m ≤ p - n + n := by
      exact Nat.add_le_add_left (Nat.mod_le n m) (p - n)
    _ = p := Nat.sub_add_cancel hn

omit Base in
theorem Nat_div_mod (n m : Nat) :
    n / m * m = n - n % m := by
  have h := Nat.div_add_mod n m
  rw [Nat.mul_comm] at h
  exact Nat.eq_sub_of_add_eq h

omit Base in
theorem Nat_add_le (n m p : Nat) :
    n ≤ m → n ≤ p + m := by
  intro h
  omega

omit Base in
theorem Nat_le_add_distr (n m p : Nat) :
    n + m ≤ p → n ≤ p := by
  intro h
  omega

omit Base in
theorem Nat_le_sub (n m p : Nat) :
    p ≤ m → n ≤ m - p → n + p ≤ m := by
  intro hp hn
  omega

omit Base in
theorem Nat_div_mul_le (n m : Nat) :
    n / m * m ≤ n :=
  Nat.div_mul_le_self n m

omit Base in
theorem Nat_sub_mod_le (n m : Nat) :
    n - n % m ≤ n := by
  omega

omit Base in
theorem Nat_le_div_mul (n m : Nat) :
    m ≠ 0 → n - m ≤ n / m * m := by
  intro hm
  rw [Nat_div_mod]
  have hmod : n % m < m := Nat.mod_lt n (Nat.pos_of_ne_zero hm)
  omega

omit Base in
private theorem nat_le_sum_of_mem :
    ∀ {xs : List Nat} {x : Nat}, x ∈ xs → x ≤ xs.sum
  | [], _, h => by cases h
  | y :: ys, x, h => by
      simp only [List.mem_cons] at h
      simp only [List.sum_cons]
      rcases h with rfl | hmem
      · omega
      · have ih := nat_le_sum_of_mem (xs := ys) hmem
        omega

theorem balance_le_sum_balances (addr : Base.Address) (state : @State Base) :
    with_default 0 (FMap.find addr (balances state)) ≤
      ConCert.Examples.EIP20.EIP20Token.sum_balances state.token_state := by
  cases hfind : FMap.find addr (balances state) with
  | none =>
      exact Nat.zero_le _
  | some bal =>
      have hmem_pair :
          (addr, bal) ∈ FMap.elements (balances state) :=
        (FMap.In_elements addr bal (balances state)).mpr hfind
      have hmem :
          bal ∈ (FMap.elements (balances state)).map
              (fun p : Base.Address × TokenValue => p.2) := by
        exact List.mem_map.mpr ⟨(addr, bal), hmem_pair, rfl⟩
      simpa [with_default, ConCert.Examples.EIP20.EIP20Token.sum_balances] using
        nat_le_sum_of_mem hmem

def total_balance (bstate : @ChainState Base) (accounts : List Base.Address) :
    Amount :=
  (accounts.map (fun acc => bstate.env_account_balances acc)).sum

theorem total_balance_positive
    (bstate : @ChainState Base) (accounts : List Base.Address) :
    reachable bstate → 0 ≤ total_balance bstate accounts := by
  intro hreach
  unfold total_balance
  induction accounts with
  | nil =>
      simp
  | cons acc accounts ih =>
      simp only [List.map_cons, List.sum_cons]
      have hacc : 0 ≤ bstate.env_account_balances acc :=
        account_balance_nonnegative bstate acc hreach
      have htail := ih
      linarith

theorem total_balance_eq
    (env1 env2 : @ChainState Base) (accounts : List Base.Address)
    (h : ∀ a, a ∈ accounts →
      env1.env_account_balances a = env2.env_account_balances a) :
    total_balance env1 accounts = total_balance env2 accounts := by
  unfold total_balance
  induction accounts with
  | nil =>
      simp
  | cons acc accounts ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := h acc List.mem_cons_self
      have htail :
          ∀ a, a ∈ accounts →
            env1.env_account_balances a = env2.env_account_balances a := by
        intro a ha
        exact h a (List.mem_cons_of_mem _ ha)
      rw [hhead, ih htail]

theorem total_balance_le
    (env1 env2 : @ChainState Base) (accounts : List Base.Address)
    (h : ∀ a, a ∈ accounts →
      env1.env_account_balances a ≤ env2.env_account_balances a) :
    total_balance env1 accounts ≤ total_balance env2 accounts := by
  unfold total_balance
  induction accounts with
  | nil =>
      simp
  | cons acc accounts ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := h acc List.mem_cons_self
      have htail :
          ∀ a, a ∈ accounts →
            env1.env_account_balances a ≤ env2.env_account_balances a := by
        intro a ha
        exact h a (List.mem_cons_of_mem _ ha)
      have hih := ih htail
      linarith

def pending_usage (bstate : @ChainState Base) (account : Base.Address) : Amount :=
  min
    ((bstate.chain_state_queue.map fun act =>
      if Base.address_eqb act.act_from account then max 0 (act_amount act) else 0).sum)
    (bstate.env_account_balances account)

def spendable_balance (bstate : @ChainState Base)
    (accounts : List Base.Address) : Amount :=
  (accounts.map fun acc =>
    bstate.env_account_balances acc - pending_usage bstate acc).sum

theorem spendable_eq_total_balance
    (bstate : @ChainState Base) (accounts : List Base.Address) :
    reachable bstate →
    bstate.chain_state_queue = [] →
    spendable_balance bstate accounts = total_balance bstate accounts := by
  intro hreach hqueue
  unfold spendable_balance total_balance pending_usage
  rw [hqueue]
  simp only [List.map_nil, List.sum_nil]
  induction accounts with
  | nil =>
      simp
  | cons acc accounts ih =>
      simp only [List.map_cons, List.sum_cons]
      have hnonneg : 0 ≤ bstate.env_account_balances acc :=
        account_balance_nonnegative bstate acc hreach
      rw [min_eq_left hnonneg]
      simp [ih]

theorem spendable_balance_positive
    (bstate : @ChainState Base) (accounts : List Base.Address) :
    0 ≤ spendable_balance bstate accounts := by
  unfold spendable_balance pending_usage
  induction accounts with
  | nil =>
      simp
  | cons acc accounts ih =>
      simp only [List.map_cons, List.sum_cons]
      have hterm :
          0 ≤ bstate.env_account_balances acc -
            min
              ((bstate.chain_state_queue.map fun act =>
                if Base.address_eqb act.act_from acc then max 0 (act_amount act) else 0).sum)
              (bstate.env_account_balances acc) := by
        exact sub_nonneg.mpr (min_le_right _ _)
      linarith

def create_token_acts
    (env : @Environment Base) (caddr : Base.Address)
    (accounts : List Base.Address) (tokens_left exchange_rate : Nat) :
    List (@Action Base) :=
  let create_tokens_act (sender : Base.Address) (amount : Amount) : @Action Base :=
    { act_origin := sender,
      act_from := sender,
      act_body := .act_call caddr amount (serialize (Msg.create_tokens : @Msg Base)) }
  match accounts with
  | [] => []
  | acc :: accounts' =>
      if 0 < tokens_left then
        let amount' := 1 + tokens_left / exchange_rate
        let amount := min amount' (Int.toNat (env.env_account_balances acc))
        create_tokens_act acc (Int.ofNat amount) ::
          create_token_acts env caddr accounts'
            (tokens_left - amount * exchange_rate) exchange_rate
      else
        create_token_acts env caddr accounts' tokens_left exchange_rate

theorem create_token_acts_cons
    (caddr : Base.Address) (env : @Environment Base) (acc : Base.Address)
    (accounts : List Base.Address) (tokens_left exchange_rate : Nat) :
    let amount' := 1 + tokens_left / exchange_rate
    let amount := min amount' (Int.toNat (env.env_account_balances acc))
    let act : @Action Base :=
      { act_origin := acc,
        act_from := acc,
        act_body := .act_call caddr (Int.ofNat amount)
          (serialize (Msg.create_tokens : @Msg Base)) }
    0 < tokens_left →
      create_token_acts env caddr (acc :: accounts) tokens_left exchange_rate =
        act ::
          create_token_acts env caddr accounts
            (tokens_left - amount * exchange_rate) exchange_rate := by
  intro amount' amount act htokens
  simp [create_token_acts, htokens, amount', amount, act]

theorem create_token_acts_eq
    (caddr : Base.Address) (env1 env2 : @Environment Base)
    (accounts : List Base.Address) (tokens_left exchange_rate : Nat) :
    (∀ a, a ∈ accounts →
      env1.env_account_balances a = env2.env_account_balances a) →
    create_token_acts env1 caddr accounts tokens_left exchange_rate =
      create_token_acts env2 caddr accounts tokens_left exchange_rate := by
  intro h
  revert tokens_left
  induction accounts with
  | nil =>
      intro tokens_left
      simp [create_token_acts]
  | cons acc accounts ih =>
      intro tokens_left
      have hhead := h acc List.mem_cons_self
      have htail :
          ∀ a, a ∈ accounts →
            env1.env_account_balances a = env2.env_account_balances a := by
        intro a ha
        exact h a (List.mem_cons_of_mem _ ha)
      by_cases htokens : 0 < tokens_left
      · simp [create_token_acts, htokens, hhead, ih htail]
      · simp [create_token_acts, htokens, ih htail]

theorem create_token_acts_is_account
    (caddr : Base.Address) (env : @Environment Base)
    (accounts : List Base.Address) (tokens_left exchange_rate : Nat) :
    accounts.Forall (fun acc : Base.Address => Base.address_is_contract acc = false) →
    ∀ act : @Action Base,
      act ∈ create_token_acts env caddr accounts tokens_left exchange_rate →
      act_is_from_account act := by
  intro hforall
  induction accounts generalizing tokens_left with
  | nil =>
      intro act hmem
      simp [create_token_acts] at hmem
  | cons acc accounts ih =>
      intro act hmem
      simp only [List.forall_cons] at hforall
      by_cases htokens : 0 < tokens_left
      · simp [create_token_acts, htokens] at hmem
        rcases hmem with hact | htail
        · subst hact
          exact hforall.1
        · exact ih _ hforall.2 act htail
      · simp [create_token_acts, htokens] at hmem
        exact ih _ hforall.2 act hmem

theorem create_token_acts_origin_correct
    (accounts : List Base.Address) (env : @Environment Base)
    (caddr : Base.Address) (tokens_left exchange_rate : Nat) :
    (create_token_acts env caddr accounts tokens_left exchange_rate).Forall
      act_origin_is_eq_from := by
  revert tokens_left
  induction accounts with
  | nil =>
      intro tokens_left
      simp [create_token_acts]
  | cons acc accounts ih =>
      intro tokens_left
      by_cases htokens : 0 < tokens_left
      · simp [create_token_acts, htokens, ih, act_origin_is_eq_from,
          Address.address_eq_refl]
      · simp [create_token_acts, htokens, ih]

end ConCert.Examples.BAT
