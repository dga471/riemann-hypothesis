module

public import Lib.Analytic.ZeroSymmetry
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov

/-!
# Gauss sums of primitive characters and the Pólya–Vinogradov bound

The Gauss sum of a primitive Dirichlet character mod `q` has absolute value `√q`. For a
non-principal character mod `q`, every partial sum of its values is at most `2 √q (1 + log q)` in
absolute value.

* `New.norm_gaussSum_of_isPrimitive`: the modulus of the Gauss sum.
* `New.polya_vinogradov`: the Pólya–Vinogradov inequality.

## Relation to the literature

Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. It is
proved here for initial intervals only, with the explicit bound `2 √q (1 + log q)`, by reducing to
Tau Ceti's `DirichletCharacter.norm_sum_Icc_changeLevel_le`. Source: Pólya 1918, Vinogradov 1918;
Davenport, Multiplicative Number Theory; Montgomery–Vaughan Thm 9.18.
-/

@[expose] public section

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction NeZero Nat

namespace New

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gauss sum of a primitive Dirichlet character mod `q`, taken with the standard additive
character `x ↦ exp (2 π i x / q)` of `ZMod q`, has absolute value `√q`. -/
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  have h_prod := gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hχ (isPrimitive_stdAddChar q)
  have h_conj : gaussSum χ⁻¹ stdAddChar⁻¹ = star (gaussSum χ stdAddChar) := by
    rw [star_gaussSum_eq, AddChar.inv_mulShift, ← Units.coe_neg_one, gaussSum_mulShift_eq, inv_inv]
  have h_sq : ‖gaussSum χ stdAddChar‖ * ‖gaussSum χ stdAddChar‖ = q := by
    simpa [h_conj] using congrArg norm h_prod
  rw [← h_sq, Real.sqrt_mul_self (norm_nonneg _)]

/-- For every nonzero natural number `r`, `2 ^ ω(r) ≤ 2 √r`. -/
private lemma two_pow_cardDistinctFactors_le_two_mul_sqrt {r : ℕ} (hr : r ≠ 0) :
    (2 : ℝ) ^ (cardDistinctFactors r) ≤ 2 * √r := by
  -- Every prime `p ≥ 5` satisfies `4 ≤ p`, and for `{2, 3}` we have `4 ^ |S| ≤ 4 * ∏ S`,
  -- so `4 ^ ω(r) ≤ 4 * ∏_{p ∣ r} p ≤ 4 * r`.
  have h_nat : 4 ^ r.primeFactors.card ≤ 4 * r := by
    let S := r.primeFactors ∩ {2, 3}
    let T := r.primeFactors \ {2, 3}
    have h_union : T ∪ S = r.primeFactors := Finset.sdiff_union_inter _ _
    have h_disj : Disjoint T S := Finset.disjoint_sdiff_inter _ _
    have hS_all : ∀ s : Finset ℕ, s ⊆ {2, 3} → 4 ^ s.card ≤ 4 * ∏ p ∈ s, p := by decide
    have hS : 4 ^ S.card ≤ 4 * ∏ p ∈ S, p := hS_all S Finset.inter_subset_right
    have hT : 4 ^ T.card ≤ ∏ p ∈ T, p := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod fun p hp ↦ ?_
      rw [Finset.mem_sdiff, Nat.mem_primeFactors] at hp
      have h2 : p ≠ 2 := by aesop
      have h3 : p ≠ 3 := by aesop
      have hge := hp.1.1.two_le
      omega
    have h_prod_le : ∏ p ∈ r.primeFactors, p ≤ r :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hr) (Nat.prod_primeFactors_dvd r)
    calc 4 ^ r.primeFactors.card
        = 4 ^ T.card * 4 ^ S.card := by rw [← h_union, Finset.card_union_of_disjoint h_disj, pow_add]
      _ ≤ (∏ p ∈ T, p) * (4 * ∏ p ∈ S, p) := Nat.mul_le_mul hT hS
      _ = 4 * ∏ p ∈ r.primeFactors, p := by
          rw [mul_left_comm, ← Finset.prod_union h_disj, h_union]
      _ ≤ 4 * r := Nat.mul_le_mul_left 4 h_prod_le
  have h_omega : cardDistinctFactors r = r.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_length_dedup_primeFactorsList,
      ← List.card_toFinset]
    rfl
  have h_sq : ((2 : ℝ) ^ (cardDistinctFactors r)) ^ 2 ≤ (2 * √r) ^ 2 := by
    rw [h_omega, ← pow_mul, mul_comm, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
    exact_mod_cast h_nat
  exact le_of_sq_le_sq h_sq (by positivity)

/-- The **Pólya–Vinogradov inequality** for initial intervals: for a non-principal Dirichlet
character `χ` mod `q` one has `|∑_{1 ≤ v ≤ X} χ v| ≤ 2 √q (1 + log q)` for all `X`. -/
theorem polya_vinogradov (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + Real.log q) := by
  obtain ⟨M, hMq, ψ, _, hψ, h_ind⟩ := exists_isPrimitive_changeLevel_eq χ
  obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd hMq
  have hψ_ne : ψ ≠ 1 := fun h ↦ hχ (by rw [← h_ind, h, map_one])
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hM_le : (M : ℝ) ≤ q := mod_cast le_of_dvd (NeZero.pos q) hMq
  have hr0 : r ≠ 0 := right_ne_zero_of_mul (hr.symm.trans_ne (NeZero.ne q))
  have hr_eq : q / M = r := by rw [hr, Nat.mul_div_cancel_left r (NeZero.pos M)]
  have h_log_nonneg : 0 ≤ 1 + Real.log q := by
    have hq1 : (1 : ℝ) ≤ q := mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    linarith [Real.log_nonneg hq1]
  have h_pv : ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 ^ cardDistinctFactors r * (√M * (1 + Real.log M)) := by
    rw [← h_ind, ← hr_eq, ← Icc_succ_left_eq_Ioc]
    exact ψ.norm_sum_Icc_changeLevel_le hψ hψ_ne hMq X
  calc ‖∑ v ∈ Ioc 0 X, χ v‖
      ≤ 2 ^ cardDistinctFactors r * (√M * (1 + Real.log q)) := h_pv.trans (by gcongr)
    _ ≤ 2 * √r * (√M * (1 + Real.log q)) :=
        mul_le_mul_of_nonneg_right (two_pow_cardDistinctFactors_le_two_mul_sqrt hr0)
          (mul_nonneg (Real.sqrt_nonneg _) h_log_nonneg)
    _ = 2 * √q * (1 + Real.log q) := by
        rw [hr, Nat.cast_mul, Real.sqrt_mul hM_pos.le]
        ring

end New
