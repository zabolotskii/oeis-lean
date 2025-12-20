/-
This file was edited by Aristotle. (And by me, Andrei Z.: see README.md.)

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c1809653-bb2c-48ca-946b-64a334c60dc0

The following was proved by Aristotle:

- theorem signs : ∀ n : ℕ, (Odd n → a n ≥ 0) ∧ (Even n → a n ≤ 0)
-/

-- https://oeis.org/A281487


import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.NumberTheory.Divisors

set_option linter.style.longLine false


def a : ℕ → ℤ := Nat.strongRec fun n a =>
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => - ∑ d ∈ (n+1).divisors.attach, a d (by
            linarith [Nat.divisor_le d.property])

set_option linter.hashCommand false
#guard a 18 = -14

noncomputable section AristotleLemmas

/-
If d divides 2k but not k, then d must be even.
unused
lemma divisors_double_diff_subset_even {k : ℕ} (hk : k ≠ 0) : ∀ d ∈ (2 * k).divisors, d ∉ k.divisors → Even d := by
  aesop;
  rw [ Nat.even_iff ] ; rw [ Nat.dvd_mul ] at a ; aesop;
  have := Nat.le_of_dvd ( by positivity ) left; interval_cases w <;> aesop;
-/

/-
Simplification rules for the sequence a(n).
-/
lemma a_simp : (a 0 = 0 ∧ a 1 = 1) ∧ ∀ n, a (n + 2) = - ∑ d ∈ (n + 1).divisors, a d := by
  unfold a
  constructor
  · unfold Nat.strongRec; trivial
  intro
  rw [ Nat.strongRec , ← Finset.sum_attach ]

/-
If the sign properties hold for m < 2k-1, then a(k) <= a(2k-1) for odd k.
-/
lemma a_odd_le_double_pred (k : ℕ) (hk : Odd k) (H : ∀ m < 2 * k - 1, (Odd m → a m ≥ 0) ∧ (Even m → a m ≤ 0)) : a k ≤ a (2 * k - 1) := by
  rcases k with ( _ | _ | k )
  · simp [parity_simps]
  · simp [parity_simps]
  simp_all only [parity_simps, Nat.mul_succ, Nat.add_one_sub_one];
  -- By definition of $a$, we can write
  have h_ak1 : a (k + 2) = -∑ d ∈ Nat.divisors (k + 1), a d := a_simp.2 _
  have h_a2k3 : a (2 * k + 3) = -∑ d ∈ Nat.divisors (2 * k + 2), a d := a_simp.2 _
  -- We can split the sum $\sum_{d \mid 2(k+1)} a(d)$ into two parts: $\sum_{d \mid k+1} a(d)$ and $\sum_{d \mid 2(k+1), d \not\mid k+1} a(d)$.
  have h_split : ∑ d ∈ Nat.divisors (2 * k + 2), a d = ∑ d ∈ Nat.divisors (k + 1), a d + ∑ d ∈ (Nat.divisors (2 * k + 2)).filter (fun d => d ∉ Nat.divisors (k + 1)), a d := by
    rw [ ← Finset.sum_union ];
    · congr with x
      norm_num [parity_simps]
      apply Iff.intro <;> intro h
      · rw [and_iff_right h]
        exact em _
      · rcases h with h | h
        · exact h.trans ⟨ 2, by ring ⟩
        · omega
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_filter.mp hx₂ |>.2 hx₁;
  -- Since $d$ divides $2(k+1)$ but not $k+1$, $d$ must be even.
  have h_even : ∀ d ∈ (Nat.divisors (2 * k + 2)).filter (fun d => d ∉ Nat.divisors (k + 1)), Even d := by
    intro d hd; contrapose! hd
    norm_num
    intro a
    exact Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime d 2 from by aesop ) a
  -- Since $d$ is even, by $H$, we have $a(d) \leq 0$.
  have h_even_le_zero : ∀ d ∈ (Nat.divisors (2 * k + 2)).filter (fun d => d ∉ Nat.divisors (k + 1)), a d ≤ 0 := by
    exact fun d hd => H d ( by linarith [ Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.dvd_of_mem_divisors ( Finset.filter_subset _ _ hd ) ) ] ) |>.2 ( h_even d hd );
  linarith [ show ∑ d ∈ Finset.filter ( fun d => d ∉ Nat.divisors ( k + 1 ) ) ( Nat.divisors ( 2 * k + 2 ) ), a d ≤ 0 from Finset.sum_nonpos h_even_le_zero ]

/-
For odd k, a(k) + a(2k) <= 0, assuming sign properties for smaller m.
-/
lemma a_odd_add_double_le_zero (k : ℕ) (hk : Odd k) (H : ∀ m < 2 * k, (Odd m → a m ≥ 0) ∧ (Even m → a m ≤ 0)) : a k + a (2 * k) ≤ 0 := by
  -- First, let's use the recurrence relation for `a(2k)` in terms of `a(2k-1)` and the sum of `a(d)` for `d` dividing `2k-1`.
  have h_recurrence : a (2 * k) = - a (2 * k - 1) - ∑ d ∈ (2 * k - 1).divisors.erase (2 * k - 1), a d := by
    rcases k with ( _ | k ) <;> simp [ Nat.mul_succ, a_simp ];
    ring;
  -- By the sign properties for $m < 2k-1$, we have $a(k) \leq a(2k-1)$.
  have h_odd : a k ≤ a (2 * k - 1) := by
    apply_rules [ a_odd_le_double_pred ];
    exact fun m mn => H m <| lt_of_lt_of_le mn <| Nat.pred_le _;
  -- By the sign properties for $m < 2k-1$, we have $a(d) \geq 0$ for all $d$ dividing $2k-1$.
  have h_divisors_pos : ∀ d ∈ (2 * k - 1).divisors.erase (2 * k - 1), 0 ≤ a d := by
    rcases k with ( _ | _ | k )
    · simp [parity_simps]
    · simp [parity_simps]
    norm_num [parity_simps, Nat.mul_succ] at *
    exact fun d h1 h2 => H d ( by linarith [ Nat.le_of_dvd ( Nat.succ_pos _ ) h2, Nat.lt_of_le_of_ne ( Nat.le_of_dvd ( Nat.succ_pos _ ) h2 ) h1 ] ) |>.1 ( by simpa [ parity_simps ] using h2.even );
  linarith [ Finset.sum_nonneg h_divisors_pos ]

/-
Definition of the odd part of a natural number and its basic properties.
-/
def oddPart (n : ℕ) : ℕ := n / 2 ^ (n.factorization 2)

lemma oddPart_spec (n : ℕ) (h : n ≠ 0) : Odd (oddPart n) ∧ oddPart n * 2 ^ (n.factorization 2) = n := by
  constructor
  · rw [ Nat.odd_iff ];
    exact Nat.mod_two_ne_zero.mp fun con => absurd ( Nat.dvd_of_mod_eq_zero con ) ( by exact Nat.not_dvd_ordCompl ( by norm_num ) ( by aesop ) );
  · exact Nat.div_mul_cancel ( Nat.ordProj_dvd _ _ )

/-
The sum of a(d) for divisors d of 2k with a fixed odd part t is non-positive.
-/
lemma sum_geometric_progression_le_zero (t : ℕ) (ht : Odd t) (k : ℕ) (htk : t ∣ k) (H : ∀ m < 2 * k + 1, (Odd m → a m ≥ 0) ∧ (Even m → a m ≤ 0)) : ∑ d ∈ (2 * k).divisors.filter (fun x => oddPart x = t), a d ≤ 0 := by
  -- For $j \geq 2$, $2^j t$ is even and $2^j t \leq 2k < 2k+1$. So by `H`, $a(2^j t) \leq 0$.
  have h_even : ∑ d ∈ ((2 * k).divisors).filter (fun d => (oddPart d) = t) \ {t, 2 * t}, a d ≤ 0 := by
    refine Finset.sum_nonpos fun x hx => ?_
    norm_num [parity_simps] at hx
    obtain ⟨⟨⟨left, right_2⟩, right_1⟩, ⟨left_1, right⟩⟩ := hx
    subst right_1
    exact H x ( by linarith [ Nat.le_of_dvd ( by positivity ) left ] ) |>.2 ( by
      contrapose! left_1; unfold oddPart at *
      rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> simp_all [ ← even_iff_two_dvd, parity_simps ] )
  by_cases h : t ∈ Nat.divisors ( 2 * k ) <;> by_cases h' : 2 * t ∈ Nat.divisors ( 2 * k ) <;> norm_num [parity_simps] at *
  · -- Since $t$ and $2t$ are both in this set, we can split the sum as $a(t) + a(2t) + \sum_{d \in \{d \in (2k).divisors \mid oddPart d = t\} \setminus \{t, 2t\}} a(d)$.
    have h_split : ∑ d ∈ ((2 * k).divisors).filter (fun d => (oddPart d) = t), a d = a t + a (2 * t) + ∑ d ∈ ((2 * k).divisors).filter (fun d => (oddPart d) = t) \ {t, 2 * t}, a d := by
      rw [ ← Finset.sum_sdiff <| show { t, 2 * t } ⊆ { d ∈ ( 2 * k |> Nat.divisors ) | oddPart d = t } from ?_ ];
      · grind;
      · unfold oddPart
        norm_num [Finset.insert_subset_iff]
        constructor
        · rw [ Nat.factorization_eq_zero_of_not_dvd ( by simpa [ ← even_iff_two_dvd ] using ht ), pow_zero, Nat.div_one ]
          norm_num [h, h']
        · cases ht
          simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ]
    -- By `a_odd_add_double_le_zero`, we have $a(t) + a(2t) \leq 0$.
    have h_odd_add_double : a t + a (2 * t) ≤ 0 := by
      convert a_odd_add_double_le_zero t ht _;
      exact fun m mn => H m ( by linarith [ Nat.le_of_dvd ( Nat.pos_of_ne_zero h'.2 ) htk ] );
    linarith;
  · norm_num [h, h' <| mul_dvd_mul_left 2 htk]
  · norm_num [h', h <| dvd_of_mul_left_dvd h'.1]
  · cases k <;> norm_num at *
    exact False.elim <| h <| htk.mul_left 2

end AristotleLemmas

theorem signs : ∀ n : ℕ, (Odd n → a n ≥ 0) ∧ (Even n → a n ≤ 0) := by
  intro n
  by_cases n = 0
  · subst n
    simp [a_simp.1]
  by_cases n = 1
  · subst n
    simp [a_simp.1]
  have hn : n > 1 := by omega
    -- We apply `a_simp` to re-express `a (n + 1)` in terms of the sums of `a d` for divisors `d` of `n`.
    -- We can then apply the induction hypothesis `h` and the previous results `sum_geometric_progression_le_zero` and `a_odd_add_double_le_zero`, respectively.
  induction n using Nat.strongRecOn with | ind n ih =>
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩
  <;> norm_num [parity_simps] at *
  · -- Since $n$ is even, we have $a(2k) = -\sum_{d \mid (2k-1)} a(d)$.
    have h_even : a (2 * k) = -∑ d ∈ (2 * k - 1).divisors, a d := by
      rcases k with ( _ | _ | k ) <;> simp [ Nat.mul_succ, a_simp ]
    -- Since $2k-1$ is odd, all its divisors $d$ are odd.
    have h_odd_divisors : ∀ d ∈ (2 * k - 1).divisors, Odd d := by
      exact fun d hd => Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun contra => by have := Nat.dvd_trans ( Nat.dvd_of_mod_eq_zero contra ) ( Nat.dvd_of_mem_divisors hd ) ; omega ) ;
    -- By the induction hypothesis, we know that $a(d) \geq 0$ for all odd $d$.
    have h_ind_odd : ∀ d ∈ (2 * k - 1).divisors, 0 ≤ a d := by
      intro d hd; specialize ih d ( Nat.lt_of_le_of_lt ( Nat.le_of_dvd ( Nat.sub_pos_of_lt hn ) ( Nat.dvd_of_mem_divisors hd ) ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) )
      exact if h : 1 < d then (ih (by omega) (by omega) h).1 (by aesop) else by interval_cases d <;> norm_num [ a_simp ] ;
    exact h_even.symm ▸ neg_nonpos_of_nonneg ( Finset.sum_nonneg h_ind_odd );
  · -- By definition of $a$, we have $a(2k+1) = - \sum_{d \in (2k).divisors} a(d)$.
    have h_def : a (2 * k + 1) = - ∑ d ∈ Nat.divisors (2 * k), a d := by
      rcases k with ( _ | k ) <;> norm_num [ Nat.mul_succ, Nat.divisors_prime_pow, a_simp ]
      contradiction
    -- We group the divisors of $2k$ by their odd part.
    have h_group : ∑ d ∈ Nat.divisors (2 * k), a d = ∑ t ∈ Nat.divisors (2 * k) |>.filter Odd, ∑ d ∈ Nat.divisors (2 * k) |>.filter (fun d => oddPart d = t), a d := by
      rw [ ← Finset.sum_biUnion ];
      · congr with x
        norm_num
        intro hx hk
        have x_ne0 : x ≠ 0 := ne_zero_of_dvd_ne_zero ( by positivity ) hx
        have ops := oddPart_spec x x_ne0
        exact ⟨⟨dvd_trans (dvd_of_mul_right_eq _ ops.2) hx, hk⟩, ops.1⟩
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    -- For each odd divisor $t$ of $2k$, we apply `sum_geometric_progression_le_zero` with $k$ and $t$.
    have h_inner : ∀ t ∈ Nat.divisors (2 * k) |>.filter (fun t => Odd t), ∑ d ∈ Nat.divisors (2 * k) |>.filter (fun d => oddPart d = t), a d ≤ 0 := by
      intro t ht
      have ⟨td2k, odd_t⟩ := Finset.mem_filter.mp ht
      replace td2k := (Nat.mem_divisors.mp td2k).left
      have h_odd_div : t ∣ k := by
        refine Nat.Coprime.dvd_of_dvd_mul_left ?_ td2k
        simp [odd_t]
      have h_sign : ∀ m < 2 * k + 1, (Odd m → a m ≥ 0) ∧ (Even m → a m ≤ 0) := by
        intro m hm; rcases m with ( _ | _ | m ) <;> norm_num [a_simp.1]
        exact ih (m+2) hm (by omega) (by omega) (by omega)
      exact sum_geometric_progression_le_zero t odd_t k h_odd_div h_sign
    exact h_def.symm ▸ neg_nonneg_of_nonpos ( h_group.symm ▸ Finset.sum_nonpos h_inner );

/-
theorem monotonicity : ∀ n : ℕ,
  (n%4 = 0 → a (n+3) ≥ -a n) ∧
  (n%4 = 1 → a (n+1) ≤ -a n) ∧
  (n%4 = 2 → a (n+3) ≥ -a n) ∧
  (n%4 = 3 → a (n+1) ≤ -a n) := by
  sorry
-/
