module

import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicCore
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformization
public import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialsAndBaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionBase
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenies
public import GroundTheory.GlobalFields.ComplexMultiplication.WeberFunction
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsValuation
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Endomorphisms
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyRamification
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.SupersingularPowField
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateCharpoly
public import GroundTheory.GlobalFields.Artin.OneDim
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
public import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Global

section
open WeierstrassCurve OnePoint ShortWeierstrass

variable {F : Type*} [Field F]

open scoped Classical in
noncomputable def automorphismOrder (W : WeierstrassCurve F) : ℕ := by
  classical
  exact if W.a₆ = 0 then 4 else if W.a₄ = 0 then 6 else 2

def automorphismScale (W : WeierstrassCurve F) :
    MulAction.stabilizer (VariableChange F) W →* Fˣ where
  toFun ξ := ξ.1.u
  map_one' := rfl
  map_mul' _ _ := rfl

def automorphismPoint {W : WeierstrassCurve F} (ξ : MulAction.stabilizer (VariableChange F) W) :
    W.toAffine.Point → W.toAffine.Point :=
  variableChangePoint ξ.1 (MulAction.mem_stabilizer_iff.mp ξ.2)

section CharZero

variable [CharZero F] {W : WeierstrassCurve F}

theorem automorphism_rst_eq_zero (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) : ξ.1.r = 0 ∧ ξ.1.s = 0 ∧ ξ.1.t = 0 :=
  variableChange_rst_eq_zero hW ((MulAction.mem_stabilizer_iff.mp ξ.2).symm ▸ hW)

theorem mem_range_automorphismScale (hW : IsShortForm W) (u : Fˣ) :
    u ∈ (automorphismScale W).range ↔
      (↑u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ ∧ (↑u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  constructor
  · rintro ⟨ξ, rfl⟩
    have hξ : ξ.1 • W = W := MulAction.mem_stabilizer_iff.mp ξ.2
    have hCW : IsShortForm (ξ.1 • W) := hξ.symm ▸ hW
    have h4 := variableChange_a₄_of_isShortForm hW hCW
    have h6 := variableChange_a₆_of_isShortForm hW hCW
    rw [hξ] at h4 h6
    exact ⟨h4.symm, h6.symm⟩
  · rintro ⟨h4, h6⟩
    have hC : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
      ext
      · simp [variableChange_a₁, hW.a₁_eq]
      · simp [variableChange_a₂, hW.a₂_eq, hW.a₁_eq]
      · simp [variableChange_a₃, hW.a₃_eq, hW.a₁_eq]
      · simpa [variableChange_a₄, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h4
      · simpa [variableChange_a₆, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h6
    exact ⟨⟨_, MulAction.mem_stabilizer_iff.mpr hC⟩, rfl⟩

variable [W.IsElliptic]

omit [CharZero F] in
theorem scale_conditions_iff (hW : IsShortForm W) (w : F) :
    (w⁻¹ ^ 4 * W.a₄ = W.a₄ ∧ w⁻¹ ^ 6 * W.a₆ = W.a₆) ↔ w ^ automorphismOrder W = 1 := by
  have key : ∀ (k : ℕ) (c : F), c ≠ 0 → (w⁻¹ ^ k * c = c ↔ w ^ k = 1) := by
    intro k c hc
    rw [inv_pow]
    constructor
    · intro h
      exact inv_eq_one.mp (mul_right_cancel₀ hc (h.trans (one_mul c).symm))
    · intro h
      rw [h, inv_one, one_mul]
  unfold automorphismOrder
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    simp only [h6, mul_zero, and_true, ite_true]
    exact key 4 _ h4
  by_cases h4 : W.a₄ = 0
  · simp only [h4, h6, mul_zero, true_and, ite_false, ite_true]
    exact key 6 _ h6
  · simp only [h4, h6, ite_false, key 4 _ h4, key 6 _ h6]
    constructor
    · rintro ⟨a, b⟩
      have : w ^ 6 = w ^ 4 * w ^ 2 := by ring
      rw [this, a, one_mul] at b
      exact b
    · intro h
      refine ⟨?_, ?_⟩
      · rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, h, one_pow]
      · rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, h, one_pow]

theorem weberFunction_automorphismPoint (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) (P : W.toAffine.Point) :
    weberFunction W (automorphismPoint ξ P) = weberFunction W P :=
  weberFunction_variableChangePoint ξ.1 _ hW hW P

end CharZero

section Fibres

variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]

omit [CharZero F] [W.IsElliptic] in
theorem IsShortForm.sq_eq (hW : IsShortForm W) {x y : F} (h : W.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  have := h.1
  rw [Affine.equation_iff] at this
  simpa [hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using this

theorem exists_scale_of_weberValue_eq [IsAlgClosed F] (hW : IsShortForm W) {x₁ x₂ : F}
    (hx : weberValue W x₁ = weberValue W x₂) :
    ∃ v : F, v ≠ 0 ∧ v ^ 4 * W.a₄ = W.a₄ ∧ v ^ 6 * W.a₆ = W.a₆ ∧ v ^ 2 * x₁ = x₂ := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    rw [weberValue_of_a₆_eq_zero h6, weberValue_of_a₆_eq_zero h6] at hx
    have hc : g₂ W ^ 2 / W.Δ ≠ 0 := by simp [g₂, h4, hΔ]
    have hsq : x₁ ^ 2 = x₂ ^ 2 := mul_left_cancel₀ hc hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩
    · obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : F)
      have hi4 : i ^ 4 = 1 := by linear_combination (1 - i * i) * hi
      refine ⟨i, ?_, by rw [hi4, one_mul], by rw [h6, mul_zero], ?_⟩
      · rintro rfl
        simp at hi
      · linear_combination (-x₁) * hi - h
  by_cases h4 : W.a₄ = 0
  · rw [weberValue_of_a₄_eq_zero h4 h6, weberValue_of_a₄_eq_zero h4 h6] at hx
    have hc : g₃ W / W.Δ ≠ 0 := by simp [g₃, h6, hΔ]
    have hcube : x₁ ^ 3 = x₂ ^ 3 := mul_left_cancel₀ hc hx
    by_cases hx1 : x₁ = 0
    · have hx2 : x₂ = 0 := by
        rw [hx1, zero_pow (by norm_num)] at hcube
        exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube.symm
      exact ⟨1, one_ne_zero, by simp, by simp, by simp [hx1, hx2]⟩
    · obtain ⟨w, hw⟩ : ∃ w, w = x₂ / x₁ := ⟨_, rfl⟩
      have hw3 : w ^ 3 = 1 := by
        rw [hw, div_pow, ← hcube, div_self (pow_ne_zero 3 hx1)]
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw3
      refine ⟨w ^ 2, pow_ne_zero 2 hw0, by simp [h4], ?_, ?_⟩
      · rw [show (w ^ 2) ^ 6 = (w ^ 3) ^ 4 by ring, hw3, one_pow, one_mul]
      · rw [show (w ^ 2) ^ 2 = w ^ 3 * w by ring, hw3, one_mul, hw, div_mul_cancel₀ _ hx1]
  · rw [weberValue_of_ne_zero h4 h6, weberValue_of_ne_zero h4 h6] at hx
    have hc : g₂ W * g₃ W / W.Δ ≠ 0 := by simp [g₂, g₃, h4, h6, hΔ]
    have h : x₁ = x₂ := mul_left_cancel₀ hc hx
    exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩

omit [W.IsElliptic] in
theorem exists_automorphismPoint_of_scale (hW : IsShortForm W) {v x₁ y₁ x₂ y₂ : F} (hv : v ≠ 0)
    (h4 : v ^ 4 * W.a₄ = W.a₄) (h6 : v ^ 6 * W.a₆ = W.a₆) (hx : v ^ 2 * x₁ = x₂)
    (hy : v ^ 3 * y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    ∃ ξ : MulAction.stabilizer (VariableChange F) W,
      automorphismPoint ξ (.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by
  obtain ⟨ξ, hξ⟩ := (mem_range_automorphismScale hW ((Units.mk0 v hv)⁻¹)).mpr
    ⟨by simpa using h4, by simpa using h6⟩
  refine ⟨ξ, ?_⟩
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  have hu : (↑ξ.1.u⁻¹ : F) = v := by
    have : ξ.1.u = (Units.mk0 v hv)⁻¹ := hξ
    rw [this, inv_inv, Units.val_mk0]
  simp only [automorphismPoint, variableChangePoint_some, hr, hs, ht, hu, sub_zero, zero_mul,
    Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

theorem weberFunction_eq_iff [IsAlgClosed F] (hW : IsShortForm W) (P Q : W.toAffine.Point) :
    weberFunction W P = weberFunction W Q ↔
      ∃ ξ : MulAction.stabilizer (VariableChange F) W, automorphismPoint ξ P = Q := by
  constructor
  · intro hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => exact ⟨1, rfl⟩
      | some x y h => simp [weberFunction] at hPQ
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp [weberFunction] at hPQ
      | some x₂ y₂ h₂ =>
        simp only [weberFunction_some] at hPQ
        have hx : weberValue W x₁ = weberValue W x₂ := Option.some_injective _ hPQ
        obtain ⟨v, hv, h4, h6, hx2⟩ := exists_scale_of_weberValue_eq hW hx
        have hy : y₂ ^ 2 = (v ^ 3 * y₁) ^ 2 := by
          rw [hW.sq_eq h₂, ← hx2]
          linear_combination (-(v ^ 6)) * hW.sq_eq h₁ - v ^ 2 * x₁ * h4 - h6
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
        · exact exists_automorphismPoint_of_scale hW hv h4 h6 hx2 hy.symm h₁ h₂
        · refine exists_automorphismPoint_of_scale (v := -v) hW (neg_ne_zero.mpr hv) ?_ ?_ ?_ ?_
            h₁ h₂
          · rw [show (-v) ^ 4 = v ^ 4 by ring, h4]
          · rw [show (-v) ^ 6 = v ^ 6 by ring, h6]
          · rw [show (-v) ^ 2 = v ^ 2 by ring, hx2]
          · rw [hy]
            ring
  · rintro ⟨ξ, rfl⟩
    exact (weberFunction_automorphismPoint hW ξ P).symm

end Fibres
end

section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
  GroundTheory.Arith.Abelian

universe u

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem exists_scale_of_degree_eq_one_of_isAlgClosed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α γ : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A ∧
      γ ^ 2 = α ^ 3 ∧ γ ^ 2 * A.a₄ = B.a₄ * α ∧ γ ^ 2 * A.a₆ = B.a₆ := by
  obtain ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, c3, c2, c1, c0, d1, d0⟩ :=
    exists_coeffs_of_degree_eq_one_of_isAlgClosed ψ h
  rw [hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, hB.a₁_eq, hB.a₂_eq, hB.a₃_eq] at *
  have hδ : δ = 0 := by
    have : (2 * γ) * δ = 0 := by linear_combination d1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  have hε : ε = 0 := by
    have : (2 * γ) * ε = 0 := by linear_combination d0
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hγ)
  subst hδ hε
  have hβ : β = 0 := by
    have : (3 * α ^ 2) * β = 0 := by linear_combination -c2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h3 (pow_ne_zero 2 hα))
  subst hβ
  refine ⟨α, γ, hα, hγ, by simpa using hx, by simpa using hy, c3, by linear_combination c1,
    by linear_combination c0⟩

end AlgClosed

section General

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]

omit [A.IsElliptic] in
theorem IsShortForm.baseChange {W : WeierstrassCurve F} (hW : IsShortForm W) (L : Type*) [Field L]
    [Algebra F L] : IsShortForm (W.baseChange L) :=
  ⟨by simp [WeierstrassCurve.baseChange, hW.a₁_eq], by simp [WeierstrassCurve.baseChange, hW.a₂_eq],
    by simp [WeierstrassCurve.baseChange, hW.a₃_eq]⟩

theorem exists_scale_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hA : IsShortForm A)
    (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A ∧
      ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A ∧
      B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ := by
  classical
  let Ω := AlgebraicClosure F
  have hd : (isogBaseChange (F' := Ω) ψ).degree = 1 := by rw [degree_isogBaseChange, h]
  have inj := (algebraMap F Ω).injective
  have h2' : (2 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h2
    rwa [map_ofNat] at this
  have h3' : (3 : Ω) ≠ 0 := by
    have := (_root_.map_ne_zero (algebraMap F Ω)).mpr h3
    rwa [map_ofNat] at this
  obtain ⟨α, γ, hα, hγ, hx, hy, hc, h4, h6⟩ := exists_scale_of_degree_eq_one_of_isAlgClosed h2' h3'
    (hA.baseChange Ω) (hB.baseChange Ω) _ hd
  rw [isogBaseChange_alt, ← bcEmb_genX] at hx
  rw [isogBaseChange_y, ← bcEmb_genY] at hy
  have hX0 : genX A ≠ 0 := fun h => transcendental_genX A (h ▸ isAlgebraic_zero)
  have hY0 : genY A ≠ 0 := genY_ne_zero A
  set K' := (A.baseChange Ω).toAffine.FunctionField
  have hXb : bcEmb (F' := Ω) A (genX A) ≠ 0 := (_root_.map_ne_zero _).mpr hX0
  have hYb : bcEmb (F' := Ω) A (genY A) ≠ 0 := (_root_.map_ne_zero _).mpr hY0
  have ex : bcEmb (F' := Ω) A (ψ.x / genX A) = algebraMap Ω K' α := by
    rw [map_div₀, hx, mul_div_cancel_right₀ _ hXb]
  have ey : bcEmb (F' := Ω) A (ψ.y / genY A) = algebraMap Ω K' γ := by
    rw [map_div₀, hy, mul_div_cancel_right₀ _ hYb]
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_bcEmb A ex
  obtain ⟨c, hc'⟩ := exists_algebraMap_eq_of_bcEmb A ey
  have key : ∀ (b : F) (f : A.toAffine.FunctionField) (β : Ω),
      algebraMap F A.toAffine.FunctionField b = f → bcEmb (F' := Ω) A f = algebraMap Ω K' β →
        algebraMap F Ω b = β := by
    intro b f β hb hf
    apply (algebraMap Ω K').injective
    rw [← hf, ← hb, AlgHom.commutes, IsScalarTower.algebraMap_apply F Ω K']
  have haα := key a _ α ha ex
  have hcγ := key c _ γ hc' ey
  have ha0 : a ≠ 0 := by rintro rfl; exact hα (by rw [← haα, map_zero])
  have hc0 : c ≠ 0 := by rintro rfl; exact hγ (by rw [← hcγ, map_zero])
  have hca : c ^ 2 = a ^ 3 := inj (by rw [map_pow, map_pow, haα, hcγ, hc])
  have h4' : c ^ 2 * A.a₄ = B.a₄ * a := inj (by
    rw [map_mul, map_mul, map_pow, haα, hcγ]; exact h4)
  have h6' : c ^ 2 * A.a₆ = B.a₆ := inj (by
    rw [map_mul, map_pow, hcγ]; exact h6)
  let v : Fˣ := Units.mk0 (c / a) (div_ne_zero hc0 ha0)
  have hv2 : (v : F) ^ 2 = a := by
    show (c / a) ^ 2 = a
    field_simp
    linear_combination hca
  have hv3 : (v : F) ^ 3 = c := by
    show (c / a) ^ 3 = c
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
    rw [div_pow, ← hca, div_eq_iff hc2]
    ring
  have hv0 : (v : F) ^ 2 ≠ 0 := pow_ne_zero 2 v.ne_zero
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [hv2, ha, div_mul_cancel₀ _ hX0]
  · rw [hv3, hc', div_mul_cancel₀ _ hY0]
  · apply mul_right_cancel₀ hv0
    rw [hv2, ← h4', ← hv3, ← hv2]
    ring
  · rw [← h6', ← hv3]
    ring

end General
end

section
open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

theorem pow_eq_one_of_scale {F : Type*} [Field F] {E : WeierstrassCurve F} [E.IsElliptic]
    (hE : IsShortForm E) {u : F} (h4 : E.a₄ = u ^ 4 * E.a₄) (h6 : E.a₆ = u ^ 6 * E.a₆) :
    u ^ automorphismOrder E = 1 ∧ u ^ 12 = 1 := by
  by_cases hu : u = 0
  · subst hu
    rcases hE.a₄_ne_zero_or_a₆_ne_zero with h | h
    · exact absurd (by simpa using h4) h
    · exact absurd (by simpa using h6) h
  have hn : u ^ automorphismOrder E = 1 := by
    have := (scale_conditions_iff hE u⁻¹).mp ⟨by rw [inv_inv]; exact h4.symm,
      by rw [inv_inv]; exact h6.symm⟩
    rwa [inv_pow, inv_eq_one] at this
  refine ⟨hn, ?_⟩
  unfold automorphismOrder at hn
  split_ifs at hn
  · rw [show 12 = 4 * 3 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 6 * 2 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 2 * 6 by rfl, pow_mul, hn, one_pow]

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

omit [IsAlgClosed F] [A.IsElliptic] [B.IsElliptic] in
theorem vcPoint_constPoint (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    vcPoint (C.baseChange A.toAffine.FunctionField) (Elliptic.baseChange_smul_eq C _ hC)
        (constPoint A R) = constMap B A.toAffine.FunctionField (vcPoint C hC R) := by
  cases R with
  | zero => rfl
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some A h
    rw [e, vcPoint_some, vcPoint_some]
    show Point.some _ _ _ = Point.some _ _ _
    rw [Point.some.injEq]
    exact ⟨(map_vcX C (algebraMap F _) x).symm, (map_vcY C (algebraMap F _) x y).symm⟩

theorem pointMap_eq_vcPoint (C : VariableChange F) (hC : C • A = B) (ψ : Isogeny A B)
    (hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A)) (R : A.toAffine.Point) :
    ψ.pointMap R = vcPoint C hC R := by
  apply Isogeny.pointMap_eq_of_map_translate
  rw [hψ, Elliptic.map_vcPoint C (translate A R) hC, map_translate_genericPoint, vcPoint_add,
    vcPoint_constPoint]

theorem pointMap_some_of_scale (hA : IsShortForm A) (hB : IsShortForm B) (u : Fˣ)
    (h4 : B.a₄ = (u : F) ^ 4 * A.a₄) (h6 : B.a₆ = (u : F) ^ 6 * A.a₆) (ψ : Isogeny A B)
    (hx : ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A)
    (hy : ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A)
    {x y : F} (h : A.toAffine.Nonsingular x y) :
    ∃ h' : B.toAffine.Nonsingular ((u : F) ^ 2 * x) ((u : F) ^ 3 * y),
      ψ.pointMap (.some x y h) = .some _ _ h' := by
  let C : VariableChange F := ⟨u⁻¹, 0, 0, 0⟩
  have hC : C • A = B := by
    ext
    · simp [C, variableChange_a₁, hA.a₁_eq, hB.a₁_eq]
    · simp [C, variableChange_a₂, hA.a₁_eq, hA.a₂_eq, hB.a₂_eq]
    · simp [C, variableChange_a₃, hA.a₁_eq, hA.a₃_eq, hB.a₃_eq]
    · simp [C, variableChange_a₄, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h4]
    · simp [C, variableChange_a₆, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h6]
  have hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A) := by
    rw [ψ.val_eq_some_x_y]
    simp only [GroundTheory.Arith.Abelian.genericPoint, vcPoint_some, Point.some.injEq]
    constructor
    · rw [hx]
      simp [C, vcX, VariableChange.baseChange, VariableChange.map]
    · rw [hy]
      simp [C, vcY, VariableChange.baseChange, VariableChange.map]
  have ex : vcX C x = (u : F) ^ 2 * x := by simp [C, vcX]
  have ey : vcY C x y = (u : F) ^ 3 * y := by simp [C, vcY]
  have hN : B.toAffine.Nonsingular (vcX C x) (vcY C x y) := hC ▸ (nonsingular_vc C A x y).2 h
  rw [ex, ey] at hN
  refine ⟨hN, ?_⟩
  rw [pointMap_eq_vcPoint C hC ψ hψ, vcPoint_some, Point.some.injEq]
  exact ⟨ex, ey⟩

end AlgClosed

section BaseChange

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [DecidableEq Ω]

theorem pointMap_isogBaseChange_some_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ ∧
      ∀ (x y : Ω) (hxy : (A.baseChange Ω).toAffine.Nonsingular x y),
        ∃ h' : (B.baseChange Ω).toAffine.Nonsingular
            (algebraMap F Ω (u : F) ^ 2 * x) (algebraMap F Ω (u : F) ^ 3 * y),
          (isogBaseChange (F' := Ω) ψ).pointMap (.some x y hxy) = .some _ _ h' := by
  obtain ⟨u, hx, hy, h4, h6⟩ := exists_scale_of_degree_eq_one h2 h3 hA hB ψ h
  refine ⟨u, h4, h6, fun x y hxy => ?_⟩
  let v : Ωˣ := Units.map (algebraMap F Ω) u
  have hv : (v : Ω) = algebraMap F Ω (u : F) := rfl
  have h4' : (B.baseChange Ω).a₄ = (v : Ω) ^ 4 * (A.baseChange Ω).a₄ := by
    show algebraMap F Ω B.a₄ = _ * algebraMap F Ω A.a₄
    rw [h4, hv, map_mul, map_pow]
  have h6' : (B.baseChange Ω).a₆ = (v : Ω) ^ 6 * (A.baseChange Ω).a₆ := by
    show algebraMap F Ω B.a₆ = _ * algebraMap F Ω A.a₆
    rw [h6, hv, map_mul, map_pow]
  have hx' : (isogBaseChange (F' := Ω) ψ).x =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 2) *
        genX (A.baseChange Ω) := by
    rw [isogBaseChange_alt, hx, map_mul, AlgHom.commutes, bcEmb_genX, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  have hy' : (isogBaseChange (F' := Ω) ψ).y =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 3) *
        genY (A.baseChange Ω) := by
    rw [isogBaseChange_y, hy, map_mul, AlgHom.commutes, bcEmb_genY, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  exact pointMap_some_of_scale (hA.baseChange Ω) (hB.baseChange Ω) v h4' h6' _ hx' hy' hxy

end BaseChange
end

section
namespace Elliptic
open Complex Filter Topology Set WeierstrassCurve GroundTheory.Arith.Abelian
open scoped PeriodPair

theorem vcPoint_mul_apply (C D : VariableChange ℂ) {W W' W'' : WeierstrassCurve ℂ}
    (hD : D • W = W') (hC : C • W' = W'') (P : W.toAffine.Point) :
    vcPoint (C * D) (by rw [mul_smul, hD, hC]) P = vcPoint C hC (vcPoint D hD P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [vcPoint_some, vcPoint_some, vcPoint_some, Affine.Point.some.injEq]
    simp only [vcX, vcY, VariableChange.mul_def, mul_inv, Units.val_mul]
    have h1 : (D.u : ℂ) ≠ 0 := Units.ne_zero _
    have h2 : (C.u : ℂ) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val]
    constructor
    · field_simp
      ring
    · field_simp
      ring

theorem vcPoint_inv_vcPoint (C : VariableChange ℂ) {W W' : WeierstrassCurve ℂ} (h : C • W = W')
    (P : W.toAffine.Point) :
    vcPoint C⁻¹ (by rw [← h, inv_smul_smul]) (vcPoint C h P) = P := by
  rw [← vcPoint_mul_apply]
  rcases P with _ | ⟨x, y, h'⟩
  · rfl
  · rw [vcPoint_some, Affine.Point.some.injEq]
    simp [vcX, vcY, VariableChange.one_def]

theorem vcPoint_congr {C C' : VariableChange ℂ} (e : C = C') {W W' : WeierstrassCurve ℂ}
    (h : C • W = W') (h' : C' • W = W') (P : W.toAffine.Point) : vcPoint C h P = vcPoint C' h' P := by
  subst e
  rfl

section Coordinates

variable {W : WeierstrassCurve ℂ}

def ptX : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x _ _ => x

def ptY : W.toAffine.Point → ℂ
  | .zero => 0
  | .some _ y _ => y

theorem exists_eq_some_ptX_ptY {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ h : W.toAffine.Nonsingular (ptX P) (ptY P), P = .some (ptX P) (ptY P) h := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨h, rfl⟩

end Coordinates

section Core

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

theorem IsAnalyticUniformization.analyticAt_ptX_ptY (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) :
    AnalyticAt ℂ (fun w ↦ ptX (g w)) z ∧ AnalyticAt ℂ (fun w ↦ ptY (g w)) z := by
  obtain ⟨X, Y, hX, hY, hev⟩ := hg.analyticAt_affine z (fun h ↦ hz ((hg.map_eq_zero_iff z).1 h))
  refine ⟨hX.congr ?_, hY.congr ?_⟩ <;> filter_upwards [hev] with w ⟨h, e⟩ <;> rw [e] <;> rfl

theorem IsAnalyticUniformization.exists_chart (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∈ L.lattice) :
    ∃ U V : ℂ → ℂ, AnalyticAt ℂ U z ∧ AnalyticAt ℂ V z ∧ U z = 0 ∧ V z = 0 ∧
      ∀ᶠ w in 𝓝[≠] z, V w ≠ 0 ∧ ptX (g w) = U w / V w ∧ ptY (g w) = 1 / V w := by
  obtain ⟨U, V, hU, hV, hev⟩ := hg.analyticAt_infinity z ((hg.map_eq_zero_iff z).2 hz)
  have h0 : U z = 0 ∧ V z = 0 := by
    rcases hev.self_of_nhds with ⟨_, hU0, hV0⟩ | ⟨_, _, e⟩
    · exact ⟨hU0, hV0⟩
    · exact absurd (e.symm.trans ((hg.map_eq_zero_iff z).2 hz)) (Affine.Point.some_ne_zero _)
  refine ⟨U, V, hU, hV, h0.1, h0.2, ?_⟩
  have hL : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with w hw hwz hwL
    exact hw ⟨hwL, hwz⟩
  filter_upwards [nhdsWithin_le_nhds hev, hL] with w hw hwL
  rcases hw with ⟨hg0, -, -⟩ | ⟨hV0, h, e⟩
  · exact absurd ((hg.map_eq_zero_iff w).1 hg0) hwL
  · rw [e]
    exact ⟨hV0, rfl, rfl⟩

theorem IsAnalyticUniformization.meromorphic_ptX (hg : IsAnalyticUniformization L.lattice g) :
    Meromorphic fun w ↦ ptX (g w) := fun z ↦ by
  by_cases hz : z ∈ L.lattice
  · obtain ⟨U, V, hU, hV, -, -, hev⟩ := hg.exists_chart hz
    exact (hU.meromorphicAt.div hV.meromorphicAt).congr (by
      filter_upwards [hev] with w hw
      exact hw.2.1.symm)
  · exact (hg.analyticAt_ptX_ptY hz).1.meromorphicAt

theorem IsAnalyticUniformization.meromorphic_ptY (hg : IsAnalyticUniformization L.lattice g) :
    Meromorphic fun w ↦ ptY (g w) := fun z ↦ by
  by_cases hz : z ∈ L.lattice
  · obtain ⟨U, V, hU, hV, -, -, hev⟩ := hg.exists_chart hz
    exact (analyticAt_const.meromorphicAt.div hV.meromorphicAt).congr (by
      filter_upwards [hev] with w hw
      exact hw.2.2.symm)
  · exact (hg.analyticAt_ptX_ptY hz).2.meromorphicAt

theorem IsAnalyticUniformization.map_add_mem (hg : IsAnalyticUniformization L.lattice g) (z : ℂ)
    {l : ℂ} (hl : l ∈ L.lattice) : g (z + l) = g z := by
  rw [map_add (f := _), (hg.map_eq_zero_iff l).2 hl, add_zero]

theorem IsAnalyticUniformization.equation_ptX_ptY (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) :
    ptY (g z) ^ 2 = ptX (g z) ^ 3 + (weierstrassCurve L').a₄ * ptX (g z) + (weierstrassCurve L').a₆ := by
  obtain ⟨h, -⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  have e := (Affine.equation_iff _ _).1 h.1
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, zero_mul, add_zero] at e
  rw [e]

end Core

section Omega

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

def omegaFun (g : ℂ →+ (weierstrassCurve L').toAffine.Point) (z : ℂ) : ℂ :=
  deriv (fun w ↦ ptX (g w)) z / (2 * ptY (g z))

theorem IsAnalyticUniformization.deriv_relation (hg : IsAnalyticUniformization L.lattice g) {z : ℂ}
    (hz : z ∉ L.lattice) : ∀ᶠ w in 𝓝 z, 2 * ptY (g w) * deriv (fun v ↦ ptY (g v)) w =
      (3 * ptX (g w) ^ 2 + (weierstrassCurve L').a₄) * deriv (fun v ↦ ptX (g v)) w := by
  have hO := L.isClosed_lattice.isOpen_compl
  filter_upwards [hO.mem_nhds hz] with w (hw : w ∉ L.lattice)
  obtain ⟨hX, hY⟩ := hg.analyticAt_ptX_ptY hw
  have e : (fun v ↦ ptX (g v) * ptX (g v) * ptX (g v) + (weierstrassCurve L').a₄ * ptX (g v) +
      (weierstrassCurve L').a₆) =ᶠ[𝓝 w] fun v ↦ ptY (g v) * ptY (g v) := by
    filter_upwards [hO.mem_nhds hw] with v (hv : v ∉ L.lattice)
    have := hg.equation_ptX_ptY hv
    linear_combination -this
  have hX' := hX.differentiableAt.hasDerivAt
  have hY' := hY.differentiableAt.hasDerivAt
  have h1 := hY'.mul hY'
  have h2 := (((hX'.mul hX').mul hX').add (hX'.const_mul (weierstrassCurve L').a₄)).add_const
    (weierstrassCurve L').a₆
  have := h1.unique (h2.congr_of_eventuallyEq e.symm)
  simp only [Pi.mul_apply] at this
  linear_combination this

theorem IsAnalyticUniformization.omegaFun_order_nonneg_of_notMem
    (hg : IsAnalyticUniformization L.lattice g) {z : ℂ} (hz : z ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (omegaFun g) z := by
  obtain ⟨hX, hY⟩ := hg.analyticAt_ptX_ptY hz
  by_cases hY0 : ptY (g z) = 0
  · obtain ⟨h, -⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
    have hD : 3 * ptX (g z) ^ 2 + (weierstrassCurve L').a₄ ≠ 0 := by
      have h' := ((Affine.nonsingular_iff' _ _).1 h).2
      simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, hY0, zero_mul,
        mul_zero, add_zero, zero_sub, ne_eq, neg_eq_zero, not_true_eq_false, or_false] at h'
      exact h'
    set T : ℂ → ℂ := fun w ↦ deriv (fun v ↦ ptY (g v)) w /
      (3 * ptX (g w) ^ 2 + (weierstrassCurve L').a₄)
    have hT : AnalyticAt ℂ T z := hY.deriv.div (by fun_prop) hD
    have hDev : ∀ᶠ w in 𝓝 z, 3 * ptX (g w) ^ 2 + (weierstrassCurve L').a₄ ≠ 0 :=
      ((continuousAt_const.mul (hX.continuousAt.pow 2)).add continuousAt_const).eventually_ne hD
    have key : omegaFun g =ᶠ[𝓝[≠] z] T := by
      rcases hY.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · have hd : ∀ᶠ w in 𝓝 z, deriv (fun v ↦ ptY (g v)) w = 0 := by
          filter_upwards [h0.eventually_nhds] with w hw
          have hw' : (fun v ↦ ptY (g v)) =ᶠ[𝓝 w] fun _ ↦ (0 : ℂ) := hw
          rw [hw'.deriv_eq]
          exact deriv_const w 0
        filter_upwards [nhdsWithin_le_nhds h0, nhdsWithin_le_nhds hd] with w hw hdw
        simp only [omegaFun, T, hw, hdw, mul_zero, div_zero, zero_div]
      · filter_upwards [hne, nhdsWithin_le_nhds (hg.deriv_relation hz), nhdsWithin_le_nhds hDev]
          with w hw hrel hDw
        simp only [omegaFun, T]
        rw [div_eq_div_iff (mul_ne_zero two_ne_zero hw) hDw]
        linear_combination -hrel
    rw [meromorphicOrderAt_congr key]
    exact hT.meromorphicOrderAt_nonneg
  · exact (hX.deriv.div (analyticAt_const.mul hY) (mul_ne_zero two_ne_zero hY0)).meromorphicOrderAt_nonneg

end Omega

section OmegaLattice

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

theorem IsAnalyticUniformization.omegaFun_order_nonneg_of_mem
    (hg : IsAnalyticUniformization L.lattice g) {z : ℂ} (hz : z ∈ L.lattice) :
    0 ≤ meromorphicOrderAt (omegaFun g) z := by
  obtain ⟨U, V, hU, hV, hU0, hV0, hev⟩ := hg.exists_chart hz
  set X : ℂ → ℂ := fun w ↦ ptX (g w) with hXdef
  set Y : ℂ → ℂ := fun w ↦ ptY (g w) with hYdef
  set a₄ := (weierstrassCurve L').a₄
  set a₆ := (weierstrassCurve L').a₆
  have hXm : MeromorphicAt X z := hg.meromorphic_ptX z
  have hYm : MeromorphicAt Y z := hg.meromorphic_ptY z

  have hVne : ∀ᶠ w in 𝓝[≠] z, V w ≠ 0 := hev.mono fun _ h ↦ h.1
  have oVtop : meromorphicOrderAt V z ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hV.meromorphicAt).2 hVne
  have oVpos : 0 < meromorphicOrderAt V z := by
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos hV.meromorphicAt]
    have := hV.continuousAt.tendsto
    rw [hV0] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 oVtop
  have kpos : 0 < k := by
    rw [← hk] at oVpos
    exact_mod_cast oVpos

  have oY : meromorphicOrderAt Y z = ((-k : ℤ) : WithTop ℤ) := by
    have e : Y =ᶠ[𝓝[≠] z] V⁻¹ := by
      filter_upwards [hev] with w hw
      rw [Pi.inv_apply, ← one_div]
      exact hw.2.2
    rw [meromorphicOrderAt_congr e, meromorphicOrderAt_inv, ← hk]
    norm_cast

  have hgne : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
    filter_upwards [hev] with w hw hwL
    have h0 := (hg.map_eq_zero_iff w).2 hwL
    have h1 : ptY (g w) = 0 := by rw [h0]; rfl
    rw [hw.2.2] at h1
    exact one_div_ne_zero hw.1 h1
  have heq : (fun w ↦ Y w ^ 2) =ᶠ[𝓝[≠] z] fun w ↦ X w ^ 3 + a₄ * X w + a₆ := by
    filter_upwards [hgne] with w hw
    exact hg.equation_ptX_ptY hw
  have oY2 : meromorphicOrderAt (fun w ↦ Y w ^ 2) z = ((-(2 * k) : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt (Y ^ 2) z = _
    have e2 : ((2 : ℕ) : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) := by norm_cast
    rw [meromorphicOrderAt_pow hYm, oY, e2, ← WithTop.coe_mul]
    congr 1
    ring

  have hXneg : meromorphicOrderAt X z < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨G, hG, hXG⟩ := hXm.meromorphicOrderAt_nonneg_iff.1 hcon
    have e2 : (fun w ↦ Y w ^ 2) =ᶠ[𝓝[≠] z] fun w ↦ G w ^ 3 + a₄ * G w + a₆ := by
      filter_upwards [heq, hXG] with w h1 h2
      rw [h1, h2]
    have h2 : 0 ≤ meromorphicOrderAt (fun w ↦ Y w ^ 2) z := by
      rw [meromorphicOrderAt_congr e2]
      exact (by fun_prop : AnalyticAt ℂ (fun w ↦ G w ^ 3 + a₄ * G w + a₆) z).meromorphicOrderAt_nonneg
    rw [oY2] at h2
    have : (0 : ℤ) ≤ -(2 * k) := by exact_mod_cast h2
    omega
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hXneg)
  have mneg : m < 0 := by
    rw [← hm] at hXneg
    exact_mod_cast hXneg

  have h1 : (m : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ a₄ * X w) z := by
    show (m : WithTop ℤ) ≤ meromorphicOrderAt ((fun _ ↦ a₄) * X) z
    rw [meromorphicOrderAt_mul (MeromorphicAt.const a₄ z) hXm, ← hm]
    have := (analyticAt_const (v := a₄) (x := z)).meromorphicOrderAt_nonneg
    calc (m : WithTop ℤ) = 0 + m := (zero_add _).symm
      _ ≤ _ := add_le_add this le_rfl
  have h2 : (m : WithTop ℤ) ≤ meromorphicOrderAt (fun _ ↦ a₆) z :=
    le_trans (by exact_mod_cast mneg.le) analyticAt_const.meromorphicOrderAt_nonneg
  have hH : MeromorphicAt (fun w ↦ a₄ * X w + a₆) z := by fun_prop
  have h3 : (m : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ a₄ * X w + a₆) z := by
    show (m : WithTop ℤ) ≤ meromorphicOrderAt ((fun w ↦ a₄ * X w) + fun _ ↦ a₆) z
    exact le_trans (le_min h1 h2) (meromorphicOrderAt_add (by fun_prop) (MeromorphicAt.const _ _))
  have oX3 : meromorphicOrderAt (fun w ↦ X w ^ 3) z = ((3 * m : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt (X ^ 3) z = _
    rw [meromorphicOrderAt_pow hXm, ← hm]
    norm_cast
  have oRHS : meromorphicOrderAt (fun w ↦ X w ^ 3 + a₄ * X w + a₆) z = ((3 * m : ℤ) : WithTop ℤ) := by
    have e : (fun w ↦ X w ^ 3 + a₄ * X w + a₆) = (fun w ↦ X w ^ 3) + fun w ↦ a₄ * X w + a₆ := by
      funext w; simp only [Pi.add_apply]; ring
    have hlt : meromorphicOrderAt (fun w ↦ X w ^ 3) z < meromorphicOrderAt (fun w ↦ a₄ * X w + a₆) z := by
      rw [oX3]
      exact lt_of_lt_of_le (by exact_mod_cast (by omega : 3 * m < m)) h3
    rw [e, meromorphicOrderAt_add_eq_left_of_lt hH hlt, oX3]
  have hkm : 3 * m = -(2 * k) := by
    have := (meromorphicOrderAt_congr heq).symm.trans oY2
    rw [oRHS] at this
    exact_mod_cast this

  have oX' : meromorphicOrderAt (deriv X) z = ((m - 1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast mneg.ne) hm.symm
  have o2Y : meromorphicOrderAt (fun w ↦ 2 * Y w) z = ((-k : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt ((fun _ ↦ (2 : ℂ)) * Y) z = _
    rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const two_ne_zero, oY]
  have e : omegaFun g = deriv X * (fun w ↦ 2 * Y w)⁻¹ := by
    funext w
    simp only [omegaFun, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rfl
  rw [e, meromorphicOrderAt_mul hXm.deriv (show MeromorphicAt (fun w ↦ 2 * Y w) z by fun_prop).inv,
    meromorphicOrderAt_inv, oX', o2Y]
  have : (0 : ℤ) ≤ m - 1 + k := by omega
  have e' : (((m - 1 : ℤ) : WithTop ℤ) + -((-k : ℤ) : WithTop ℤ)) = ((m - 1 + k : ℤ) : WithTop ℤ) := by
    norm_cast
    ring
  rw [e']
  exact_mod_cast this

end OmegaLattice

section Lift

variable {L L' : PeriodPair} {g : ℂ →+ (weierstrassCurve L').toAffine.Point}

theorem eq_of_eventuallyEq_codiscrete {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[codiscrete ℂ] f₂)
    (h₁ : ContinuousAt f₁ z) (h₂ : ContinuousAt f₂ z) : f₁ z = f₂ z := by
  have h' : ∀ᶠ w in 𝓝[≠] z, f₁ w = f₂ w := by
    have := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h) z (mem_univ z)
    rw [compl_univ, union_empty] at this
    exact this
  exact tendsto_nhds_unique ((h₁.tendsto.mono_left nhdsWithin_le_nhds).congr' h')
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)

theorem IsAnalyticUniformization.meromorphic_omegaFun (hg : IsAnalyticUniformization L.lattice g) :
    Meromorphic (omegaFun g) := fun z ↦
  ((hg.meromorphic_ptX z).deriv).div ((MeromorphicAt.const 2 z).mul (hg.meromorphic_ptY z))

theorem IsAnalyticUniformization.isPeriodic_omegaFun (hg : IsAnalyticUniformization L.lattice g) :
    IsPeriodic L (omegaFun g) := by
  intro z l hl
  have hX : (fun w ↦ ptX (g (w + l))) = fun w ↦ ptX (g w) := funext fun w ↦ by rw [hg.map_add_mem w hl]
  simp only [omegaFun, hg.map_add_mem z hl]
  congr 1
  rw [← deriv_comp_add_const, hX]

theorem IsAnalyticUniformization.exists_omegaFun_eq_const (hg : IsAnalyticUniformization L.lattice g) :
    ∃ α : ℂ, omegaFun g =ᶠ[codiscrete ℂ] fun _ ↦ α :=
  exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hg.meromorphic_omegaFun hg.isPeriodic_omegaFun
    fun z ↦ by
      by_cases hz : z ∈ L.lattice
      · exact hg.omegaFun_order_nonneg_of_mem hz
      · exact hg.omegaFun_order_nonneg_of_notMem hz

theorem IsAnalyticUniformization.ptY_eq_zero_of_two_mul_mem (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∈ L.lattice) : ptY (g z) = 0 := by
  obtain ⟨h, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  have h0 : g z + g z = 0 := by rw [← map_add (f := _), ← two_mul]; exact (hg.map_eq_zero_iff _).2 h2
  have hneg : g z = -g z := eq_neg_of_add_eq_zero_left h0
  rw [e, Affine.Point.neg_some, Affine.Point.some.injEq] at hneg
  have := hneg.2
  simp only [Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero] at this
  linear_combination this / 2

theorem IsAnalyticUniformization.two_mul_mem_of_ptY_eq_zero (hg : IsAnalyticUniformization L.lattice g)
    {z : ℂ} (hz : z ∉ L.lattice) (hY : ptY (g z) = 0) : 2 * z ∈ L.lattice := by
  obtain ⟨h, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  have hneg : -g z = g z := by
    rw [e, Affine.Point.neg_some, Affine.Point.some.injEq]
    refine ⟨rfl, ?_⟩
    simp only [Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero, hY, neg_zero]
  rw [← hg.map_eq_zero_iff, two_mul, map_add (f := _)]
  nth_rewrite 1 [← hneg]
  exact neg_add_cancel _

theorem IsAnalyticUniformization.eventually_ptY_ne_zero (hg : IsAnalyticUniformization L.lattice g) :
    ∀ᶠ z in codiscrete ℂ, ptY (g z) ≠ 0 := by
  filter_upwards [eventually_affine (eventually_notMem_lattice L) two_ne_zero 0] with z hz hY
  rw [add_zero] at hz
  have hz' : z ∉ L.lattice := fun h ↦ hz (by rw [two_mul]; exact add_mem h h)
  exact hz (hg.two_mul_mem_of_ptY_eq_zero hz' hY)

theorem IsAnalyticUniformization.eventually_equation (hg : IsAnalyticUniformization L.lattice g) :
    ∀ᶠ z in codiscrete ℂ, (weierstrassCurve L').toAffine.Equation (ptX (g z)) (ptY (g z)) := by
  filter_upwards [eventually_notMem_lattice L] with z hz
  obtain ⟨h, -⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
  exact h.1

theorem IsAnalyticUniformization.not_eventually_ptX_eq_const
    (hg : IsAnalyticUniformization L.lattice g) (c : ℂ) :
    ¬ (fun z ↦ ptX (g z)) =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  intro h
  have half : ∀ z, z ∉ L.lattice → 2 * z ∈ L.lattice → g z = g (L.ω₁ / 2) := by
    have key : ∀ z, z ∉ L.lattice → 2 * z ∈ L.lattice →
        ∃ hn, g z = .some c 0 hn := by
      intro z hz h2
      obtain ⟨hn, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
      have hx : ptX (g z) = c :=
        eq_of_eventuallyEq_codiscrete h (hg.analyticAt_ptX_ptY hz).1.continuousAt continuousAt_const
      have hy : ptY (g z) = 0 := hg.ptY_eq_zero_of_two_mul_mem hz h2
      rw [e]
      exact exists_point_some_eq hn hx.symm hy.symm |>.imp fun _ h ↦ h
    intro z hz h2
    obtain ⟨h₁, e₁⟩ := key z hz h2
    obtain ⟨h₂, e₂⟩ := key (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice (by
      rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)
    rw [e₁, e₂]
  have e := half (L.ω₂ / 2) L.ω₂_div_two_notMem_lattice (by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)
  have hmem : L.ω₂ / 2 - L.ω₁ / 2 ∈ L.lattice := by
    rw [← hg.map_eq_zero_iff, map_sub, e, sub_self]
  have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := -1 / 2) (β := 1 / 2)).1 (by
    convert hmem using 1
    push_cast
    ring)
  norm_num at this

theorem IsAnalyticUniformization.exists_mul_add (hg : IsAnalyticUniformization L.lattice g) :
    ∃ α c : ℂ, α ≠ 0 ∧
      (fun z ↦ ptX (g z)) =ᶠ[codiscrete ℂ] (fun z ↦ ℘[L'] (α * z + c)) ∧
      (fun z ↦ ptY (g z)) =ᶠ[codiscrete ℂ] (fun z ↦ ℘'[L'] (α * z + c) / 2) := by
  obtain ⟨α, hα⟩ := hg.exists_omegaFun_eq_const
  set X : ℂ → ℂ := fun z ↦ ptX (g z) with hXdef
  set Y : ℂ → ℂ := fun z ↦ ptY (g z) with hYdef
  have hXm : Meromorphic X := hg.meromorphic_ptX
  have hYm : Meromorphic Y := hg.meromorphic_ptY
  have hPn : ((weierstrassCurve L').baseChange MeroField).toAffine.Nonsingular (germ X) (germ Y) :=
    Affine.equation_iff_nonsingular.1 (equation_germ hXm hYm hg.eventually_equation)
  have hYne : germ Y ≠ 0 := by
    intro h
    rw [germ_eq_zero_iff hYm] at h
    obtain ⟨z, h1, h2⟩ := nonempty_of_mem_codiscrete (h.and hg.eventually_ptY_ne_zero)
    exact h2 h1
  have h2ne : (2 : MeroField) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ MeroField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  have h2Y : (2 : MeroField) * germ Y ≠ 0 := mul_ne_zero h2ne hYne
  have hderiv : germ (deriv X) = 2 * germ Y * algebraMap ℂ MeroField α := by
    have e : deriv X =ᶠ[codiscrete ℂ] fun z ↦ 2 * Y z * α := by
      filter_upwards [hα, hg.eventually_ptY_ne_zero] with z h1 h2
      simp only [omegaFun] at h1
      rw [div_eq_iff (mul_ne_zero two_ne_zero h2)] at h1
      rw [h1]
      ring
    have hm : Meromorphic fun z ↦ 2 * Y z * α := fun z ↦ by fun_prop
    rw [(germ_eq_germ_iff hXm.deriv hm).2 e,
      show (fun z ↦ 2 * Y z * α) = ((fun _ ↦ (2 : ℂ)) * Y) * fun _ ↦ α from rfl,
      germ_mul ((Meromorphic.const 2).mul hYm) (Meromorphic.const α),
      germ_mul (Meromorphic.const 2) hYm, germ_const, germ_const, map_ofNat]
  have hω : omegaDeriv (omegaAt (weierstrassCurve L') (.some _ _ hPn)) = algebraMap ℂ MeroField α := by
    obtain ⟨s₁, -⟩ := omegaAt_some_spec (weierstrassCurve L') hPn
    have e := congrArg omegaDeriv s₁
    rw [LinearMap.map_smul, omegaDeriv_D, germDeriv_germ hXm] at e
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      weierstrassCurve_a₁, weierstrassCurve_a₃, map_zero, zero_mul, add_zero, smul_eq_mul] at e
    rw [hderiv] at e
    exact mul_left_cancel₀ h2Y e
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hderiv
    rw [← germDeriv_germ hXm] at hderiv
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero hderiv
    rw [← germ_const, germ_eq_germ_iff hXm (Meromorphic.const c)] at hc
    exact hg.not_eventually_ptX_eq_const c hc
  have hD : omegaDeriv (omegaAt (weierstrassCurve L')
      ((.some _ _ hPn : ((weierstrassCurve L').baseChange MeroField).toAffine.Point) -
        affinePoint L' α 0 hα0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L') ((.some _ _ hPn : ((weierstrassCurve L').baseChange
        MeroField).toAffine.Point) - affinePoint L' α 0 hα0) =
        omegaAt (weierstrassCurve L') (.some _ _ hPn) - omegaAt (weierstrassCurve L') (affinePoint L' α 0 hα0) :=
      map_sub (omegaHom (weierstrassCurve L')) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L') R
  have hP : (.some _ _ hPn : ((weierstrassCurve L').baseChange MeroField).toAffine.Point) =
      affinePoint L' α (0 + c) hα0 := by
    rw [← affinePoint_add_constMap, ← hR]
    abel
  rw [zero_add] at hP
  simp only [affinePoint, Affine.Point.some.injEq] at hP
  refine ⟨α, c, hα0, ?_, ?_⟩
  · exact (germ_eq_germ_iff hXm (meromorphic_weierstrassP_affine L' α c)).1 hP.1
  · exact (germ_eq_germ_iff hYm (meromorphic_derivWeierstrassP_half_affine L' α c)).1 hP.2

end Lift

section Classification

theorem exists_mul_of_isAnalyticUniformization {L L' : PeriodPair}
    {g : ℂ →+ (weierstrassCurve L').toAffine.Point} (hg : IsAnalyticUniformization L.lattice g) :
    ∃ α : ℂ, α ≠ 0 ∧ (∀ z, z ∈ L.lattice ↔ α * z ∈ L'.lattice) ∧ ∀ z, g z = toPoint L' (α * z) := by
  obtain ⟨α, c, hα, hX, hY⟩ := hg.exists_mul_add
  have good : ∀ z, z ∉ L.lattice → α * z + c ∉ L'.lattice → g z = toPoint L' (α * z + c) := by
    intro z hz hz'
    obtain ⟨hn, e⟩ := exists_eq_some_ptX_ptY (fun h0 ↦ hz ((hg.map_eq_zero_iff z).1 h0))
    obtain ⟨hXa, hYa⟩ := hg.analyticAt_ptX_ptY hz
    have haff : ContinuousAt (fun w ↦ α * w + c) z := by fun_prop
    have hx : ptX (g z) = ℘[L'] (α * z + c) := eq_of_eventuallyEq_codiscrete hX hXa.continuousAt
      ((L'.analyticOnNhd_weierstrassP _ hz').continuousAt.comp_of_eq haff rfl)
    have hy : ptY (g z) = ℘'[L'] (α * z + c) / 2 := eq_of_eventuallyEq_codiscrete hY hYa.continuousAt
      (((L'.analyticOnNhd_derivWeierstrassP _ hz').continuousAt.comp_of_eq haff rfl).div_const 2)
    rw [e, toPoint_of_notMem hz']
    exact point_some_congr hx hy
  have hG : ∀ᶠ w in codiscrete ℂ, w ∉ L.lattice ∧ α * w + c ∉ L'.lattice :=
    (eventually_notMem_lattice L).and (eventually_affine (eventually_notMem_lattice L') hα c)
  have all : ∀ z, g z = toPoint L' (α * z + 2 * c) := by
    intro z
    obtain ⟨w, ⟨hw1, hw2⟩, hw3, hw4⟩ :=
      nonempty_of_mem_codiscrete (hG.and (eventually_affine hG (neg_ne_zero.2 one_ne_zero) z))
    have e : z = w + (-1 * w + z) := by ring
    rw [e, map_add (f := _), good w hw1 hw2, good _ hw3 hw4, ← toPoint_add]
    congr 1
    ring
  obtain ⟨w, hw1, hw2⟩ := nonempty_of_mem_codiscrete hG
  have hc : c ∈ L'.lattice := by
    have e := (good w hw1 hw2).symm.trans (all w)
    have := torusToPoint_injective (L := L') (a₁ := Torus.mk L' _) (a₂ := Torus.mk L' _) e
    rw [Torus.mk_eq_mk_iff] at this
    convert neg_mem this using 1
    ring
  have all' : ∀ z, g z = toPoint L' (α * z) := fun z ↦ by
    rw [all z, toPoint_add_mem (by rw [two_mul]; exact add_mem hc hc)]
  refine ⟨α, hα, fun z ↦ ?_, all'⟩
  rw [← hg.map_eq_zero_iff, all', toPoint_eq_zero_iff]

variable {E : WeierstrassCurve ℂ} [E.IsElliptic] {L : PeriodPair}

theorem exists_vcPoint_of_isAnalyticUniformization {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization L.lattice f) :
    ∃ (C : VariableChange ℂ) (h : C • weierstrassCurve L = E), ∀ z, f z = vcPoint C h (toPoint L z) := by
  obtain ⟨L', C', hC'⟩ := exists_variableChange_eq_weierstrassCurve E
  have hg := hf.vcPoint C' hC'
  obtain ⟨α, hα, hker, hgz⟩ := exists_mul_of_isAnalyticUniformization hg
  have hlat : (L'.lattice : Set ℂ) = (α * ·) '' L.lattice := by
    ext y
    constructor
    · intro hy
      refine ⟨α⁻¹ * y, (hker _).2 (by rw [mul_inv_cancel_left₀ hα]; exact hy), ?_⟩
      show α * (α⁻¹ * y) = y
      rw [mul_inv_cancel_left₀ hα]
    · rintro ⟨z, hz, rfl⟩
      exact (hker z).1 hz
  have hinv : C'⁻¹ • weierstrassCurve L' = E := by rw [← hC', inv_smul_smul]
  refine ⟨C'⁻¹ * scaleVC hα, by rw [mul_smul, scaleVC_smul hα hlat, hinv], fun z ↦ ?_⟩
  rw [vcPoint_mul_apply (C'⁻¹) (scaleVC hα) (scaleVC_smul hα hlat) hinv,
    vcPoint_scaleVC_toPoint hα hlat, ← hgz z]
  show f z = vcPoint C'⁻¹ hinv (vcPoint C' hC' (f z))
  exact (vcPoint_inv_vcPoint C' hC' (f z)).symm

theorem exists_mul_eq_of_isAnalyticUniformization {f₁ f₂ : ℂ →+ E.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂) :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ z, z ∈ L.lattice ↔ c * z ∈ L.lattice) ∧ ∀ z, f₂ z = f₁ (c * z) := by
  obtain ⟨C, hC, hf₁C⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  have hinv : C⁻¹ • E = weierstrassCurve L := by rw [← hC, inv_smul_smul]
  have hg := hf₂.vcPoint C⁻¹ hinv
  obtain ⟨c, hc, hker, hgz⟩ := exists_mul_of_isAnalyticUniformization hg
  refine ⟨c, hc, hker, fun z ↦ ?_⟩
  have e := hgz z
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply] at e
  rw [hf₁C, ← e]
  have := vcPoint_inv_vcPoint C⁻¹ hinv (f₂ z)
  rw [vcPoint_congr (inv_inv C) _ hC] at this
  exact this.symm

end Classification
end Elliptic
end

section
open WeierstrassCurve GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point)

universe u

section FFMap

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')

theorem ffMap_surjective (hσ : Function.Surjective σ) (E : WeierstrassCurve F) :
    Function.Surjective (ffMap σ E) := by
  let R : IntermediateField F' (E.map σ).toAffine.FunctionField :=
    { (ffMap σ E).fieldRange with
      algebraMap_mem' := fun c => by
        obtain ⟨a, rfl⟩ := hσ c
        exact ⟨algebraMap F _ a, ffMap_algebraMap σ E a⟩ }
  have hR : R = ⊤ := by
    rw [eq_top_iff, ← adjoin_genX_genY (W := E.map σ), IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact ⟨genX E, ffMap_genX σ E⟩
    · exact ⟨genY E, ffMap_genY σ E⟩
  intro z
  have hz : z ∈ R := hR ▸ IntermediateField.mem_top
  exact hz

end FFMap

section BcPt

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F'] (E E' : WeierstrassCurve F)

def bcPtMap : (E'.baseChange E.toAffine.FunctionField).toAffine.Point →+
    ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := E') (bcEmb (F' := F') E)

end BcPt

section HomMap

variable {F F' : Type u} [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F]
  [DecidableEq F'] (σ : F →+* F') {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

def homPtMap : (E'.baseChange E.toAffine.FunctionField).toAffine.Point →+
    ((E'.map σ).baseChange (E.map σ).toAffine.FunctionField).toAffine.Point :=
  letI := σ.toAlgebra
  bcPtMap (F' := F') E E'

omit [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F] [DecidableEq F'] in
theorem homPtMap_isogeny (φ : Isogeny E E') : homPtMap σ φ.1 = (φ.map σ).1 := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  exact (isogBaseChange_val (F' := F') φ).symm

omit [IsAlgClosed F'] [DecidableEq F'] in
theorem homPtMap_mem (Q : isogHom E E') : homPtMap σ Q.1 ∈ isogHom (E.map σ) (E'.map σ) := by
  by_cases hQ : Q = 0
  · rw [hQ, ZeroMemClass.coe_zero, map_zero]
    exact zero_mem _
  · rw [← isogOfHom_val Q hQ, homPtMap_isogeny]
    exact ((isogOfHom Q hQ).map σ).toHom.2

def homMap : isogHom E E' →+ isogHom (E.map σ) (E'.map σ) where
  toFun Q := ⟨homPtMap σ Q.1, homPtMap_mem σ Q⟩
  map_zero' := Subtype.ext (map_zero (homPtMap σ))
  map_add' Q₁ Q₂ := Subtype.ext (map_add (homPtMap σ) Q₁.1 Q₂.1)

theorem homMap_toHom (φ : Isogeny E E') : homMap σ φ.toHom = (φ.map σ).toHom :=
  Subtype.ext rfl

theorem homConst_toHom (φ : Isogeny E E') : homConst E E' φ.toHom = invConst φ := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, algebraMap_invConst]
  rfl

omit [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F] [DecidableEq F'] in
theorem invConst_map (φ : Isogeny E E') : invConst (φ.map σ) = σ (invConst φ) := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  exact invConst_isogBaseChange (F' := F') φ

theorem homConst_homMap (Q : isogHom E E') :
    homConst (E.map σ) (E'.map σ) (homMap σ Q) = σ (homConst E E' Q) := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero, map_zero, map_zero, map_zero]
  · rw [← isogOfHom_toHom Q hQ, homMap_toHom, homConst_toHom, homConst_toHom, invConst_map]

theorem homMap_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homMap σ (homComp R Q) = homComp (homMap σ R) (homMap σ Q) := by
  by_cases hQ : Q = 0
  · simp only [hQ, homComp_zero_right, map_zero]
  by_cases hR : R = 0
  · simp only [hR, homComp_zero_left, map_zero]
  rw [← isogOfHom_toHom Q hQ, ← isogOfHom_toHom R hR, Isogeny.homComp_toHom, homMap_toHom,
    homMap_toHom, homMap_toHom, Isogeny.homComp_toHom, Isogeny.map_comp]

theorem homMap_one : homMap σ (1 : isogEnd E) = 1 := by
  rw [isogEnd_one_eq_mulIsogeny, homMap_toHom, Isogeny.map_mulIsogeny, ← isogEnd_one_eq_mulIsogeny]

def endMap : isogEnd E →+* isogEnd (E.map σ) where
  toFun := homMap σ
  map_one' := homMap_one σ
  map_mul' f g := homMap_homComp σ f g
  map_zero' := map_zero _
  map_add' := map_add _

theorem homMap_injective : Function.Injective (homMap σ : isogHom E E' → _) := by
  rw [injective_iff_map_eq_zero]
  intro Q hQ
  by_contra h
  rw [← isogOfHom_toHom Q h, homMap_toHom] at hQ
  exact Isogeny.toHom_ne_zero _ hQ

theorem homMap_surjective (hσ : Function.Surjective σ) :
    Function.Surjective (homMap σ : isogHom E E' → _) := by
  intro P
  by_cases hP : P = 0
  · exact ⟨0, by rw [hP, map_zero]⟩
  set ψ := isogOfHom P hP
  obtain ⟨x, hx⟩ := ffMap_surjective σ hσ E ψ.x
  obtain ⟨y, hy⟩ := ffMap_surjective σ hσ E ψ.y
  refine ⟨(Isogeny.ofMap σ ψ x y hx hy).toHom, ?_⟩
  rw [homMap_toHom, Isogeny.map_ofMap, isogOfHom_toHom]

def endMapEquiv (σ : F ≃+* F') : isogEnd E ≃+* isogEnd (E.map (σ : F →+* F')) :=
  RingEquiv.ofBijective (endMap (σ : F →+* F'))
    ⟨homMap_injective (σ : F →+* F'), homMap_surjective (σ : F →+* F') σ.surjective⟩

end HomMap

section ConstSet

open Elliptic

variable {F F' : Type u} [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F]
  [DecidableEq F']

variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic] in
def homConstSet : AddSubgroup F := (homConst E E').range

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem mem_homConstSet {c : F} :
    c ∈ homConstSet E E' ↔ ∃ Q : isogHom E E', homConst E E' Q = c :=
  AddMonoidHom.mem_range

theorem homConstSet_map (σ : F ≃+* F') :
    (homConstSet (E.map (σ : F →+* F')) (E'.map (σ : F →+* F')) : Set F') =
      σ '' homConstSet E E' := by
  ext z
  simp only [SetLike.mem_coe, mem_homConstSet, Set.mem_image]
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, rfl⟩ := homMap_surjective (E := E) (E' := E') (σ : F →+* F') σ.surjective P
    exact ⟨homConst E E' Q, ⟨Q, rfl⟩, (homConst_homMap (σ : F →+* F') Q).symm⟩
  · rintro ⟨c, ⟨Q, rfl⟩, rfl⟩
    exact ⟨homMap (σ : F →+* F') Q, homConst_homMap (σ : F →+* F') Q⟩

theorem homConst_vcHom_mul_inv (C : VariableChange F) (h : C • E = E') :
    homConst E' E (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) * homConst E E' (vcHom C h) = 1 := by
  rw [← homConst_homComp, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homConst_homId]

theorem homConstSet_le_mul {E₁ E₁' : WeierstrassCurve F} [E₁.IsElliptic] [E₁'.IsElliptic]
    (Q : isogHom E₁ E) (R : isogHom E' E₁') {z : F} (hz : z ∈ homConstSet E E') :
    homConst E' E₁' R * z * homConst E₁ E Q ∈ homConstSet E₁ E₁' := by
  obtain ⟨P, rfl⟩ := mem_homConstSet.1 hz
  exact mem_homConstSet.2
    ⟨homComp R (homComp P Q), by rw [homConst_homComp, homConst_homComp, mul_assoc]⟩

theorem homConstSet_vc {E₁ E₁' : WeierstrassCurve F} [E₁.IsElliptic] [E₁'.IsElliptic]
    (C C' : VariableChange F) (h : C • E = E₁) (h' : C' • E' = E₁') :
    ∃ c : F, c ≠ 0 ∧ (homConstSet E₁ E₁' : Set F) = (c * ·) '' homConstSet E E' := by
  set Q := vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)
  set R := vcHom C' h'
  set Q' := vcHom C h
  set R' := vcHom C'⁻¹ (inv_smul_eq_of_smul_eq C' h')
  have e1 : homConst E₁ E Q * homConst E E₁ Q' = 1 := homConst_vcHom_mul_inv C h
  have e2 : homConst E₁' E' R' * homConst E' E₁' R = 1 := homConst_vcHom_mul_inv C' h'
  set c := homConst E' E₁' R * homConst E₁ E Q
  have hc : c * (homConst E₁' E' R' * homConst E E₁ Q') = 1 := by
    linear_combination (homConst E₁' E' R' * homConst E' E₁' R) * e1 + e2
  refine ⟨c, left_ne_zero_of_mul_eq_one hc, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst E₁' E' R' * z * homConst E E₁ Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination z * hc
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end ConstSet

section Lattice

open Elliptic

theorem homConstSet_weierstrassCurve (L₁ L₂ : PeriodPair) :
    homConstSet (weierstrassCurve L₁) (weierstrassCurve L₂) = latticeHom L₁ L₂ := by
  ext z
  rw [mem_homConstSet]
  constructor
  · rintro ⟨Q, rfl⟩
    exact homConst_mem_latticeHom Q
  · intro hz
    exact ⟨latticeToHom ⟨z, hz⟩, homConst_latticeToHom ⟨z, hz⟩⟩

end Lattice
end

section
namespace Elliptic
open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem CMCurve.toEll_eq_of_curve_eq {E E' : CMCurve K} (h : E.curve = E'.curve) :
    E.toEll = E'.toEll :=
  (CMCurve.toEll_eq_iff E E').2 ⟨1, by rw [one_smul, h]⟩

def CMCurve.map (σ : ℂ ≃+* ℂ) (E : CMCurve K) : CMCurve K where
  curve := E.curve.map (σ : ℂ →+* ℂ)
  endIso := ⟨(endMapEquiv σ).symm.trans E.endIso.some⟩

omit [NumberField K] in
theorem CMCurve.map_curve (σ : ℂ ≃+* ℂ) (E : CMCurve K) :
    (E.map σ).curve = E.curve.map (σ : ℂ →+* ℂ) :=
  rfl

def ELL.map (σ : ℂ ≃+* ℂ) : ELL K → ELL K :=
  Quotient.lift (fun E : CMCurve K ↦ (E.map σ).toEll) fun E E' h ↦ by
    obtain ⟨C, hC⟩ := h
    rw [CMCurve.toEll_eq_iff]
    exact ⟨C.map (σ : ℂ →+* ℂ), by
      rw [CMCurve.map_curve, CMCurve.map_curve, map_variableChange, hC]⟩

theorem ELL.map_toEll (σ : ℂ ≃+* ℂ) (E : CMCurve K) : ELL.map σ E.toEll = (E.map σ).toEll :=
  rfl

theorem ELL.map_one (x : ELL K) : ELL.map 1 x = x := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  rw [ELL.map_toEll]
  apply CMCurve.toEll_eq_of_curve_eq
  rw [CMCurve.map_curve]
  exact WeierstrassCurve.map_id E.curve

theorem ELL.map_mul (σ τ : ℂ ≃+* ℂ) (x : ELL K) : ELL.map (σ * τ) x = ELL.map σ (ELL.map τ x) := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  rw [ELL.map_toEll, ELL.map_toEll, ELL.map_toEll]
  apply CMCurve.toEll_eq_of_curve_eq
  rw [CMCurve.map_curve, CMCurve.map_curve, CMCurve.map_curve, WeierstrassCurve.map_map]
  rfl

theorem j_congr {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

def ELL.j : ELL K → ℂ :=
  Quotient.lift (fun E : CMCurve K ↦ E.curve.j) fun E E' h ↦ by
    obtain ⟨C, hC⟩ := h
    show E.curve.j = E'.curve.j
    rw [← variableChange_j E.curve C]
    exact j_congr hC

omit [NumberField K] in
theorem ELL.j_toEll (E : CMCurve K) : ELL.j E.toEll = E.curve.j :=
  rfl

theorem ELL.j_injective : Function.Injective (ELL.j (K := K)) := by
  intro x y h
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨E', rfl⟩ := ELL.exists_eq y
  rw [ELL.j_toEll, ELL.j_toEll] at h
  exact (CMCurve.toEll_eq_iff E E').2 (exists_variableChange_of_j_eq E.curve E'.curve h)

theorem ELL.j_map (σ : ℂ ≃+* ℂ) (x : ELL K) : ELL.j (ELL.map σ x) = σ (ELL.j x) := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  rw [ELL.map_toEll, ELL.j_toEll, ELL.j_toEll]
  exact map_j E.curve (σ : ℂ →+* ℂ)

section Quadratic

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]
include hK

theorem ELL.finite_range_conj (x : ELL K) :
    (Set.range fun σ : ℂ ≃+* ℂ ↦ σ (ELL.j x)).Finite := by
  have := finite_ell hK
  refine (Set.finite_range (ELL.j (K := K))).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨ELL.map σ x, ELL.j_map σ x⟩

theorem ELL.isAlgebraic_j (x : ELL K) : IsAlgebraic ℚ (ELL.j x) :=
  Complex.isAlgebraic_of_finite_conjugates (ELL.finite_range_conj hK x)

end Quadratic
end Elliptic
end

section
namespace Elliptic
open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

theorem image_mul_image_mul (c d : ℂ) (S : Set ℂ) :
    (c * ·) '' ((d * ·) '' S) = ((c * d) * ·) '' S := by
  rw [Set.image_image]
  congr 1
  funext x
  ring

theorem eq_image_mul_inv {c : ℂ} (hc : c ≠ 0) {A B : Set ℂ} (h : B = (c * ·) '' A) :
    A = (c⁻¹ * ·) '' B := by
  rw [h, image_mul_image_mul, inv_mul_cancel₀ hc]
  simp only [one_mul, Set.image_id']

theorem image_ringEquiv_image_mul (σ : ℂ ≃+* ℂ) (c : ℂ) (S : Set ℂ) :
    σ '' ((c * ·) '' S) = (σ c * ·) '' (σ '' S) := by
  rw [Set.image_image, Set.image_image]
  simp only [map_mul]

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem image_idealLattice (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    σ '' (idealLattice σ₀ I : Set ℂ) = idealLattice σ₀ I := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hσ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ₀ x, ⟨x, hx, rfl⟩, hσ x⟩

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]
include hK

theorem latticeHom_eq_idealLattice (L L' : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ₀)
    (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : L'.lattice = idealLattice σ₀ ↑𝔟 * L.lattice) :
    (latticeHom L L' : Set ℂ) = idealLattice σ₀ ↑𝔟 := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ₀ hK L hL
  have hI' := idealLattice_mul_homothetic σ₀ (I : FractionalIdeal (𝓞 K)⁰ K) ↑𝔟 hI
  rw [← h] at hI'
  have hmem' : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I), c * σ₀ x = z := by
    intro z
    rw [← SetLike.mem_coe, hI']
    simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ₀ x, ⟨x, hx, rfl⟩, rfl⟩
  have hmemL : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), c * σ₀ x ∈ L.lattice := by
    intro x hx
    rw [← SetLike.mem_coe, hI]
    exact ⟨σ₀ x, (mem_idealLattice σ₀).2 ⟨x, hx, rfl⟩, rfl⟩
  ext α
  simp only [SetLike.mem_coe, mem_latticeHom]
  constructor
  · intro hα
    have hI0 : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact I.ne_zero
    obtain ⟨i₀, hi₀, hi₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨k₀, -, hk₀⟩ := (hmem' _).1 (hα _ (hmemL i₀ hi₀))
    have hσi₀ : σ₀ i₀ ≠ 0 := (map_ne_zero σ₀).2 hi₀0
    have hy : σ₀ (k₀ / i₀) = α := by
      rw [map_div₀, div_eq_iff hσi₀]
      exact mul_left_cancel₀ hc (by rw [hk₀]; ring)
    set y := k₀ / i₀
    have hyI : ∀ i ∈ (I : FractionalIdeal (𝓞 K)⁰ K), y * i ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      intro i hi
      obtain ⟨k, hk, hke⟩ := (hmem' _).1 (hα _ (hmemL i hi))
      have : σ₀ k = σ₀ (y * i) := by
        rw [map_mul, hy]
        exact mul_left_cancel₀ hc (by rw [hke]; ring)
      rwa [← σ₀.injective this]
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (I : FractionalIdeal (𝓞 K)⁰ K) ≤
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).1 ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r (hyI b hb)
    have hle' := mul_le_mul_left hle ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one,
      mul_one] at hle'
    exact (mem_idealLattice σ₀).2
      ⟨y, hle' (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y), hy⟩
  · intro hα l hl
    rw [h]
    exact Submodule.mul_mem_mul hα hl

theorem homConstSet_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧
      (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset⟩ := homConstSet_vc C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset⟩

theorem smul_toEll_of_homConstSet {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℂ}
    (hc : c ≠ 0)
    (h : (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll := by
  obtain ⟨b, hb, -⟩ := existsUnique_smul_eq σ₀ hK E.toEll E'.toEll
  obtain ⟨J, rfl⟩ := classGroup_mk_surjective hK b
  obtain ⟨d, hd, h'⟩ := homConstSet_of_smul σ₀ hK hb
  have e : (idealLattice σ₀ ↑J⁻¹ : Set ℂ) = ((d⁻¹ * c) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [eq_image_mul_inv hd h', h, image_mul_image_mul]
  have hcls := (classGroup_mk_eq_iff σ₀ hK 𝔞⁻¹ J⁻¹).2 ⟨d⁻¹ * c, mul_ne_zero (inv_ne_zero hd) hc, e⟩
  rw [map_inv, map_inv, inv_inj] at hcls
  rw [hcls]
  exact hb

theorem ELL.map_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (a : ClassGroup (𝓞 K))
    (x : ELL K) :
    ELL.map σ ((ellMulAction σ₀ hK).smul a x) = (ellMulAction σ₀ hK).smul a (ELL.map σ x) := by
  obtain ⟨𝔞, rfl⟩ := classGroup_mk_surjective hK a
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨E', hE'⟩ := ELL.exists_eq ((ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll)
  rw [← hE', ELL.map_toEll, ELL.map_toEll]
  obtain ⟨c, hc, h⟩ := homConstSet_of_smul σ₀ hK hE'.symm
  refine (smul_toEll_of_homConstSet σ₀ hK (c := σ c) ((map_ne_zero σ).2 hc) ?_).symm
  calc (homConstSet (E.map σ).curve (E'.map σ).curve : Set ℂ)
      = σ '' homConstSet E.curve E'.curve := homConstSet_map (E := E.curve) (E' := E'.curve) σ
    _ = σ '' ((c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) := by rw [h]
    _ = (σ c * ·) '' (σ '' idealLattice σ₀ ↑𝔞⁻¹) := image_ringEquiv_image_mul σ c _
    _ = (σ c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by rw [image_idealLattice σ₀ σ hσ]

theorem ellMulAction_one_smul (x : ELL K) : (ellMulAction σ₀ hK).smul 1 x = x := by
  rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply]

theorem ellMulAction_mul_smul (a b : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ₀ hK).smul (a * b) x =
      (ellMulAction σ₀ hK).smul a ((ellMulAction σ₀ hK).smul b x) := by
  rw [ellMulAction_smul, ellMulAction_smul, ellMulAction_smul, Equiv.symm_apply_apply, mul_assoc]

def galClass (σ : ℂ ≃+* ℂ) : ClassGroup (𝓞 K) :=
  (ellEquiv σ₀ hK).symm (ELL.map σ (ellEquiv σ₀ hK 1))

theorem ELL.map_eq_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    ELL.map σ x = (ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x := by
  have hx : x = (ellMulAction σ₀ hK).smul ((ellEquiv σ₀ hK).symm x) (ellEquiv σ₀ hK 1) := by
    rw [ellMulAction_smul, Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]
  rw [hx, ELL.map_smul σ₀ hK σ hσ]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]
  exact congrArg (ellEquiv σ₀ hK) (mul_comm _ _)

theorem apply_j_eq_j_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x) := by
  rw [← ELL.j_map, ELL.map_eq_galClass_smul σ₀ hK σ hσ]

theorem galClass_one : galClass σ₀ hK 1 = 1 := by
  rw [galClass, ELL.map_one, Equiv.symm_apply_apply]

theorem galClass_mul (σ τ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (hτ : ∀ k : K, τ (σ₀ k) = σ₀ k) :
    galClass σ₀ hK (σ * τ) = galClass σ₀ hK σ * galClass σ₀ hK τ := by
  rw [galClass, ELL.map_mul, ELL.map_eq_galClass_smul σ₀ hK τ hτ,
    ELL.map_eq_galClass_smul σ₀ hK σ hσ, ← ellMulAction_mul_smul]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]

theorem galClass_eq_one_iff (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    galClass σ₀ hK σ = 1 ↔ σ (ELL.j x) = ELL.j x := by
  rw [apply_j_eq_j_galClass_smul σ₀ hK σ hσ]
  constructor
  · intro h
    rw [h, ellMulAction_one_smul]
  · intro h
    exact (ell_smul_eq_self_iff σ₀ hK _ x).1 (ELL.j_injective h)
end Elliptic
end

section
namespace Elliptic
open NumberField Module WeierstrassCurve IntermediateField
open scoped nonZeroDivisors

section Extend

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem exists_algEquiv_extend_adjoin {α : ℂ} (hα : IsAlgebraic K α) (φ : K⟮α⟯ →ₐ[K] ℂ) :
    ∃ σ : ℂ ≃ₐ[K] ℂ, ∀ z : K⟮α⟯, σ z = φ z := by
  have hint := hα.isIntegral
  have hroot : Polynomial.aeval (φ (AdjoinSimple.gen K α)) (minpoly K α) = 0 := by
    rw [Polynomial.aeval_algHom_apply, aeval_gen_minpoly, map_zero]
  have heq : minpoly K α = minpoly K (φ (AdjoinSimple.gen K α)) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq hα heq
  refine ⟨σ, fun z ↦ ?_⟩
  have e : (σ.toAlgHom.comp (K⟮α⟯).val) = φ := by
    apply adjoin_algHom_ext
    rintro x rfl
    exact hσ
  exact DFunLike.congr_fun e z

end Extend

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]
include hK

def galClassHom : (ℂ ≃ₐ[K] ℂ) →* ClassGroup (𝓞 K) where
  toFun σ := galClass (algebraMap K ℂ) hK σ.toRingEquiv
  map_one' := galClass_one (algebraMap K ℂ) hK
  map_mul' σ τ := galClass_mul (algebraMap K ℂ) hK σ.toRingEquiv τ.toRingEquiv
    (fun k ↦ σ.commutes k) (fun k ↦ τ.commutes k)

theorem galClassHom_apply_j (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassHom hK σ) x) :=
  apply_j_eq_j_galClass_smul (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem galClassHom_eq_one_iff (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    galClassHom hK σ = 1 ↔ σ (ELL.j x) = ELL.j x :=
  galClass_eq_one_iff (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem ELL.isAlgebraic_j_over (x : ELL K) : IsAlgebraic K (ELL.j x) := by
  have : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact IsAlgebraic.extendScalars (algebraMap ℚ K).injective (ELL.isAlgebraic_j hK x)

theorem ELL.j_mem_adjoin (x y : ELL K) : ELL.j y ∈ K⟮ELL.j x⟯ := by
  have key : ∀ ρ : ℂ ≃ₐ[K⟮ELL.j x⟯] ℂ, ρ (ELL.j y) = ELL.j y := by
    intro ρ
    have h1 : (ρ.restrictScalars K) (ELL.j x) = ELL.j x :=
      ρ.commutes (AdjoinSimple.gen K (ELL.j x))
    rw [← galClassHom_eq_one_iff hK] at h1
    have h2 := galClassHom_apply_j hK (ρ.restrictScalars K) y
    rw [h1, ellMulAction_one_smul] at h2
    exact h2
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.1
    ((mem_bot_iff_forall_algEquiv_apply_eq (F := K⟮ELL.j x⟯)).2 key)
  rw [← hw]
  exact w.2

section Field

variable (M : IntermediateField K ℂ) (hM : ∀ y : ELL K, ELL.j y ∈ M)
include hM

omit [NumberField K] hK [_root_.NumberField.IsTotallyComplex K] in
theorem adjoin_j_le (x : ELL K) : K⟮ELL.j x⟯ ≤ M :=
  adjoin_simple_le_iff.2 (hM x)

def extendOf (τ : M ≃ₐ[K] M) : ℂ ≃ₐ[K] ℂ :=
  (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK (ellEquiv (algebraMap K ℂ) hK 1))
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM _))))).choose

def galClassOfFun (τ : M ≃ₐ[K] M) : ClassGroup (𝓞 K) :=
  galClassHom hK (extendOf hK M hM τ)

theorem galClassOfFun_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOfFun hK M hM τ) y) := by
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  have hy : ELL.j y ∈ K⟮ELL.j x₀⟯ := ELL.j_mem_adjoin hK x₀ y
  have spec := (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK x₀)
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM x₀))))).choose_spec ⟨_, hy⟩
  rw [galClassOfFun, ← galClassHom_apply_j]
  exact spec.symm

theorem galClassOfFun_unique (τ : M ≃ₐ[K] M) (a : ClassGroup (𝓞 K)) (y : ELL K)
    (h : (τ ⟨ELL.j y, hM y⟩ : ℂ) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul a y)) :
    galClassOfFun hK M hM τ = a := by
  rw [galClassOfFun_apply_j hK M hM] at h
  exact (existsUnique_smul_eq (algebraMap K ℂ) hK y _).unique (ELL.j_injective h) rfl

def galClassOf : (M ≃ₐ[K] M) →* ClassGroup (𝓞 K) where
  toFun := galClassOfFun hK M hM
  map_one' := by
    apply galClassOfFun_unique hK M hM 1 1 (ellEquiv (algebraMap K ℂ) hK 1)
    rw [ellMulAction_one_smul]
    rfl
  map_mul' τ₁ τ₂ := by
    set y := ellEquiv (algebraMap K ℂ) hK 1
    apply galClassOfFun_unique hK M hM _ _ y
    have h2 : τ₂ ⟨ELL.j y, hM y⟩ = ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul
        (galClassOfFun hK M hM τ₂) y), hM _⟩ :=
      Subtype.ext (galClassOfFun_apply_j hK M hM τ₂ y)
    rw [ellMulAction_mul_smul, ← galClassOfFun_apply_j hK M hM τ₁, ← h2]
    rfl

theorem galClassOf_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK M hM τ) y) :=
  galClassOfFun_apply_j hK M hM τ y

end Field
end Elliptic
end

section
namespace Elliptic
noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

universe u

section VC

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E₁.IsElliptic]
  [E₁'.IsElliptic]

theorem homConstSet_vc_pair (C C' : VariableChange F) (h : C • E = E₁) (h' : C' • E' = E₁') :
    ∃ c : F, c ≠ 0 ∧ (homConstSet E₁ E₁' : Set F) = (c * ·) '' homConstSet E E' ∧
      (homConstSet E₁' E₁ : Set F) = (c⁻¹ * ·) '' homConstSet E' E := by
  set Q := vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)
  set R := vcHom C' h'
  set Q' := vcHom C h
  set R' := vcHom C'⁻¹ (inv_smul_eq_of_smul_eq C' h')
  have e1 : homConst E₁ E Q * homConst E E₁ Q' = 1 := homConst_vcHom_mul_inv C h
  have e2 : homConst E₁' E' R' * homConst E' E₁' R = 1 := homConst_vcHom_mul_inv C' h'
  set c := homConst E' E₁' R * homConst E₁ E Q
  have hc : c * (homConst E₁' E' R' * homConst E E₁ Q') = 1 := by
    linear_combination (homConst E₁' E' R' * homConst E' E₁' R) * e1 + e2
  have hcinv : c⁻¹ = homConst E E₁ Q' * homConst E₁' E' R' := by
    rw [inv_eq_of_mul_eq_one_right hc, mul_comm]
  refine ⟨c, left_ne_zero_of_mul_eq_one hc, ?_, ?_⟩
  · ext z
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hz
      refine ⟨homConst E₁' E' R' * z * homConst E E₁ Q', homConstSet_le_mul Q' R' hz, ?_⟩
      linear_combination z * hc
    · rintro ⟨w, hw, rfl⟩
      have := homConstSet_le_mul Q R hw
      convert this using 1
      ring
  · ext z
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hz
      refine ⟨homConst E₁ E Q * z * homConst E' E₁' R, homConstSet_le_mul R Q hz, ?_⟩
      rw [hcinv]
      linear_combination z * hc
    · rintro ⟨w, hw, rfl⟩
      have := homConstSet_le_mul R' Q' hw
      convert this using 1
      rw [hcinv]
      ring

end VC

section Invariant

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem invConst_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    invConst (ψ.comp φ) = invConst ψ * invConst φ := by
  rw [← homConst_toHom, ← Isogeny.homComp_toHom, homConst_homComp, homConst_toHom, homConst_toHom]

theorem invConst_mem_homConstSet (φ : Isogeny E E') : invConst φ ∈ homConstSet E E' :=
  mem_homConstSet.2 ⟨φ.toHom, homConst_toHom φ⟩

theorem invConst_dualOver_mul (φ : Isogeny E E') :
    invConst (dualOver φ) * invConst φ = φ.degree := by
  rw [← invConst_comp, dualOver_comp, invConst_mulIsogeny]
  push_cast
  rfl

variable [CharZero F]

theorem invConst_ne_zero (φ : Isogeny E E') : invConst φ ≠ 0 := by
  intro h
  have := invConst_dualOver_mul φ
  rw [h, mul_zero] at this
  exact (Nat.cast_ne_zero.2 φ.degree_pos.ne') this.symm

end Invariant

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem idealLattice_one_mul_lattice (L : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ₀) :
    idealLattice σ₀ 1 * L.lattice = L.lattice := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm l hl
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hm
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    have ha : σ₀ (algebraMap (𝓞 K) K a) ∈ periodLatticeEnd L := hL ▸ (mem_cmRing σ₀).2 ⟨a, rfl⟩
    exact ha l hl
  · intro l hl
    have h1 : (1 : ℂ) ∈ idealLattice σ₀ 1 :=
      (mem_idealLattice σ₀).2 ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one σ₀⟩
    simpa using Submodule.mul_mem_mul h1 hl

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]

theorem homConstSet_pair_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧ (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ ∧
      (homConstSet E'.curve E.curve : Set ℂ) = (c⁻¹ * ·) '' idealLattice σ₀ ↑𝔞 := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset, hset'⟩ := homConstSet_vc_pair C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  have hLL : L.lattice = idealLattice σ₀ ↑𝔞 * L'.lattice := by
    rw [hL'lat, ← mul_assoc, ← idealLattice_mul, Units.mul_inv, idealLattice_one_mul_lattice σ₀ L hL]
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L' L hL' 𝔞 hLL] at hset'
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset, eq_image_mul_inv (inv_ne_zero hd) hset'⟩

include hK in
theorem homConstSet_symm {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : ℂ} (hb : b ≠ 0)
    (hset : (homConstSet E.curve E'.curve : Set ℂ) = (b * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (homConstSet E'.curve E.curve : Set ℂ) = (b⁻¹ * ·) '' idealLattice σ₀ ↑𝔞 := by
  obtain ⟨c, hc, h1, h2⟩ :=
    homConstSet_pair_of_smul σ₀ hK (smul_toEll_of_homConstSet σ₀ hK hb hset)

  have e : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = ((c⁻¹ * b) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← image_mul_image_mul, ← hset, h1, image_mul_image_mul, inv_mul_cancel₀ hc]
    simp

  have e' := idealLattice_mul_homothetic σ₀ (↑𝔞⁻¹) (↑𝔞 * ↑𝔞) e
  have hmul : (↑𝔞 * ↑𝔞 * ↑𝔞⁻¹ : FractionalIdeal (𝓞 K)⁰ K) = ↑𝔞 := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [← idealLattice_mul, hmul] at e'
  rw [h2]
  calc (c⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ)
      = (c⁻¹ * ·) '' (((c⁻¹ * b)⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ)) := by
        rw [← eq_image_mul_inv (mul_ne_zero (inv_ne_zero hc) hb) e']
    _ = (b⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ) := by
        rw [image_mul_image_mul]
        congr 2
        field_simp

end Lattice

section Prime

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def primeUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)

theorem primeUnit_val : ((primeUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
    v.asIdeal :=
  rfl

theorem primeUnit_inv_val :
    (((primeUnit v)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, primeUnit_val]

theorem classGroup_mk_primeUnit :
    ClassGroup.mk K (primeUnit v) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  rw [← ClassGroup.mk_mk0 K]
  rfl

theorem absNorm_dvd_of_natCast_mem (hv : (Ideal.absNorm v.asIdeal).Prime) {n : ℕ}
    (hn : (n : 𝓞 K) ∈ v.asIdeal) : Ideal.absNorm v.asIdeal ∣ n := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hn)
  rw [Ideal.absNorm_span_natCast] at h
  exact hv.dvd_of_dvd_pow h

theorem inv_absNorm_notMem_inv (hK : finrank ℚ K = 2) (hv : (Ideal.absNorm v.asIdeal).Prime) :
    ((Ideal.absNorm v.asIdeal : K))⁻¹ ∉ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  set p := Ideal.absNorm v.asIdeal with hpdef
  intro hmem
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hv.ne_zero
  have hle : v.asIdeal ≤ Ideal.span {(p : 𝓞 K)} := by
    intro y hy
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)).1 hmem
      (algebraMap (𝓞 K) K y) (FractionalIdeal.mem_coeIdeal_of_mem _ hy)
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [Ideal.mem_span_singleton']
    refine ⟨z, IsFractionRing.injective (𝓞 K) K ?_⟩
    rw [map_mul, hz, map_natCast]
    field_simp
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK]
  rw [hnorm] at hdvd
  have := Nat.le_of_dvd hv.pos hdvd
  have h2 := hv.two_le
  nlinarith

end Prime

section Degree

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

include hK in
theorem degree_eq_absNorm {E E' : CMCurve K} (v : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm v.asIdeal).Prime) (φ : Isogeny E.curve E'.curve)
    (hφ : (homConstSet E.curve E'.curve : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    φ.degree = Ideal.absNorm v.asIdeal := by
  classical
  set p := Ideal.absNorm v.asIdeal with hpdef
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hv.ne_zero
  have hφu : (homConstSet E.curve E'.curve : Set ℂ) =
      (c * ·) '' idealLattice σ₀ ↑(primeUnit v)⁻¹ := by
    rw [primeUnit_inv_val]; exact hφ
  have hsym := homConstSet_symm σ₀ hK hc hφu
  rw [primeUnit_val] at hsym

  have hpmem : (p : ℂ) ∈ idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    have hx : ((p : K)) ∈ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      have := FractionalIdeal.mem_coeIdeal_of_mem (S := (𝓞 K)⁰) (P := K) (Ideal.absNorm_mem v.asIdeal)
      simpa using this
    simpa using map_mem_idealLattice σ₀ hx
  have hν : c⁻¹ * p ∈ homConstSet E'.curve E.curve := by
    have h' : c⁻¹ * (p : ℂ) ∈ (homConstSet E'.curve E.curve : Set ℂ) := by
      rw [hsym]; exact ⟨p, hpmem, rfl⟩
    exact h'
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hν
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact mul_ne_zero (inv_ne_zero hc) hp0 hQ.symm
  set ν := isogOfHom Q hQ0 with hνdef
  have hνc : invConst ν = c⁻¹ * p := by rw [← homConst_toHom, isogOfHom_toHom, hQ]

  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hv.ne_zero
  have hcomp : ν.comp φ = mulIsogeny E.curve p hpz := by
    have h1 : endConst E.curve (ν.comp φ).toHom = endConst E.curve (mulIsogeny E.curve p hpz).toHom := by
      rw [endConst_apply, endConst_apply, homConst_toHom, homConst_toHom, invConst_comp, hνc,
        invConst_mulIsogeny]
      field_simp
      push_cast
      ring
    have h2 := congrArg Subtype.val (endConst_injective h1)
    exact Subtype.ext h2
  have hdeg1 : ν.degree * φ.degree = p ^ 2 := by
    rw [← Isogeny.degree_comp, hcomp, degree_mulIsogeny]
    simp

  have hdvd : p ∣ φ.degree := by
    have hd : invConst (dualOver φ) ∈ (homConstSet E'.curve E.curve : Set ℂ) :=
      invConst_mem_homConstSet _
    rw [hsym] at hd
    obtain ⟨z, hz, hz'⟩ := hd
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hz
    have e := invConst_dualOver_mul φ
    rw [← hcdef, ← hz'] at e
    simp only at e
    have hx' : σ₀ x = σ₀ (φ.degree : K) := by
      rw [map_natCast, ← e]
      field_simp
    have hxK : x = φ.degree := σ₀.injective hx'
    rw [hxK] at hx
    obtain ⟨y, hy, hy'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    have : y = (φ.degree : 𝓞 K) := IsFractionRing.injective (𝓞 K) K (by rw [hy', map_natCast])
    rw [this] at hy
    exact absNorm_dvd_of_natCast_mem v hv hy
  obtain ⟨k, hk, hkdeg⟩ := (Nat.dvd_prime_pow hv).1 (Dvd.intro_left _ hdeg1)
  interval_cases k
  · rw [hkdeg, pow_zero] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hv.two_le; omega)
  · rw [hkdeg, pow_one]
  · exfalso
    have hν1 : ν.degree = 1 := by
      rw [hkdeg] at hdeg1
      have hp2 : 0 < p ^ 2 := pow_pos hv.pos 2
      nlinarith
    have e := invConst_dualOver_mul ν
    rw [hν1, hνc, Nat.cast_one] at e
    have hd : invConst (dualOver ν) ∈ (homConstSet E.curve E'.curve : Set ℂ) :=
      invConst_mem_homConstSet _
    rw [hφ] at hd
    obtain ⟨z, hz, hz'⟩ := hd
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hz
    rw [← hz'] at e
    simp only at e
    have e2 : σ₀ x * p = 1 := by
      rw [← e]
      field_simp
    have hx' : σ₀ x = σ₀ ((p : K))⁻¹ := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left e2
    rw [σ₀.injective hx'] at hx
    exact inv_absNorm_notMem_inv v hK hv hx

include hK in
theorem exists_isogeny_homConstSet_eq {E E' : CMCurve K} (v : HeightOneSpectrum (𝓞 K))
    (h : (ellMulAction σ₀ hK).smul
      (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) E.toEll = E'.toEll) :
    ∃ φ : Isogeny E.curve E'.curve, (homConstSet E.curve E'.curve : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  classical
  rw [← classGroup_mk_primeUnit] at h
  obtain ⟨c, hc, hset⟩ := homConstSet_of_smul σ₀ hK h
  rw [primeUnit_inv_val] at hset
  have h1 : (1 : ℂ) ∈ idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    simpa using map_mem_idealLattice σ₀ (FractionalIdeal.one_mem_inv_coe_ideal v.ne_bot)
  have hcmem : c ∈ homConstSet E.curve E'.curve := by
    have h' : c ∈ (homConstSet E.curve E'.curve : Set ℂ) := by
      rw [hset]; exact ⟨1, h1, mul_one c⟩
    exact h'
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hcmem
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact hc hQ.symm
  refine ⟨isogOfHom Q hQ0, ?_⟩
  rw [← homConst_toHom, isogOfHom_toHom, hQ]
  exact hset

end Degree

end
end Elliptic
end

section
open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField Polynomial

section Descent

variable {L : Type} [Field L] [CharZero L] [Algebra L ℂ] {W W' : WeierstrassCurve L} [W.IsElliptic]
  [W'.IsElliptic]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_map_eq_of_forall_conj_eq
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) (h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ) :
    ∃ φ : Isogeny W W', φ.map (algebraMap L ℂ) = ψ := by
  classical
  have hxfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.x = ψ.x := fun g ↦ by rw [← Isogeny.conj_alt_bis, h g]
  have hyfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.y = ψ.y := fun g ↦ by rw [← Isogeny.conj_y, h g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (W.baseChange ℂ) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (W.baseChange ℂ) r₂ = a at hr₂
  change ratEmb (W.baseChange ℂ) r₃ = b at hr₃
  have hab_fix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g a = a ∧ galFF W g b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add (f := _), map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX W _ ha) (galFF_mem_adjoin_genX W _ hb)
      ha hb e
  have hlift : ∀ s : RatFunc ℂ, (∀ g : ℂ ≃ₐ[L] ℂ,
      galFF W g (ratEmb (W.baseChange ℂ) s) = ratEmb (W.baseChange ℂ) s) →
      (∃ p : L[X], p.map (algebraMap L ℂ) = s.num) ∧
        ∃ q : L[X], q.map (algebraMap L ℂ) = s.denom := by
    intro s hs
    have hc : ∀ c ∈ s.num.coeffs ∪ s.denom.coeffs, c ∈ Set.range (algebraMap L ℂ) := by
      intro c hc
      have hbot : c ∈ (⊥ : IntermediateField L ℂ) := by
        refine (mem_bot_iff_forall_algEquiv_apply_eq (F := L)).2 fun g ↦ ?_
        obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb W g (hs g)
        rcases Finset.mem_union.mp hc with hc | hc
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (fun p : ℂ[X] ↦ p.coeff n) h1
          simpa using this
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (fun p : ℂ[X] ↦ p.coeff n) h2
          simpa using this
      exact IntermediateField.mem_bot.1 hbot
    constructor
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.num.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_left _ (coeff_mem_coeffs hn))
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.denom.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_right _ (coeff_mem_coeffs hn))
  obtain ⟨⟨n₁, hn₁⟩, ⟨d₁, hd₁⟩⟩ := hlift r (fun g ↦ by rw [hr]; exact hxfix g)
  obtain ⟨⟨n₂, hn₂⟩, ⟨d₂, hd₂⟩⟩ := hlift r₂ (fun g ↦ by rw [hr₂]; exact (hab_fix g).1)
  obtain ⟨⟨n₃, hn₃⟩, ⟨d₃, hd₃⟩⟩ := hlift r₃ (fun g ↦ by rw [hr₃]; exact (hab_fix g).2)
  set X₁ := genX W
  set x₁ : W.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : W.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY W
  have hrat : ∀ (s : RatFunc ℂ) (p q : L[X]), p.map (algebraMap L ℂ) = s.num →
      q.map (algebraMap L ℂ) = s.denom →
      ffMap (algebraMap L ℂ) W (aeval X₁ p / aeval X₁ q) = ratEmb (W.baseChange ℂ) s := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, ffMap_aeval, ffMap_aeval, ffMap_genX, hp, hq]
    rfl
  have hx₁ : ffMap (algebraMap L ℂ) W x₁ = ψ.x := by
    rw [← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap (algebraMap L ℂ) W y₁ = ψ.y := by
    rw [hab, map_add (f := _), map_mul, ← hr₂, ← hr₃, hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃,
      ffMap_genY]
    rfl
  exact ⟨Isogeny.ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁,
    Isogeny.map_ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁⟩

omit [CharZero L] [W.IsElliptic] [W'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_congr {F : Type} [Field F]
    {C D C' D' : WeierstrassCurve F} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    invConst (φ.congr hC hC') = invConst φ := by
  subst hC hC'
  rw [Isogeny.congr_rfl]

omit [CharZero L] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_conj (g : ℂ ≃ₐ[L] ℂ)
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) : invConst (ψ.conj g) = g (invConst ψ) := by
  rw [Isogeny.conj, Isogeny.mapOf, Isogeny.invConst_congr, invConst_map]
  rfl

end Descent
end

section
open IsLocalRing GroundTheory.Arith.Abelian

universe u

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (F : Type u) [Field F] [Algebra 𝒪 F] [IsFractionRing 𝒪 F] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic]

theorem invConst_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F)) {c : 𝒪}
    (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    invConst (reduceIsogeny F W W' φ) = 0 := by
  obtain ⟨c', h1, h2⟩ := exists_invConst_reduceIsogeny F W W' φ
  have e : c' = c := IsFractionRing.injective 𝒪 F (h1.trans hφ.symm)
  rw [← h2, e]
  exact (residue_eq_zero_iff c).2 hc

theorem isogenyPullback_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    isogenyPullback (reduceIsogeny F W W' φ) (invariantDifferential (W'.map (residue 𝒪))) = 0 := by
  rw [isogenyPullback_eq_invConst_smul, invConst_reduceIsogeny_eq_zero F φ hc hφ, zero_smul]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] [PerfectRing (ResidueField 𝒪) p]

theorem reduceIsogeny_eq_comp_frobeniusIsogeny (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    (hdeg : φ.degree = p) {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    ∃ ψ : Isogeny (frobeniusTwist (W.map (residue 𝒪)) p) (W'.map (residue 𝒪)),
      reduceIsogeny F W W' φ = ψ.comp (frobeniusIsogeny (W.map (residue 𝒪)) p) ∧
      ψ.degree = 1 ∧ Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero :=
  exists_isomorphism_of_degree_eq p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

theorem residue_j_eq_pow (φ : Isogeny (W.baseChange F) (W'.baseChange F)) (hdeg : φ.degree = p)
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    residue 𝒪 W'.j = residue 𝒪 W.j ^ p := by
  rw [← j_map_residue, ← j_map_residue]
  exact j_eq_pow_of_isogenyPullback_eq_zero p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])
end

section
namespace Elliptic
noncomputable section

open NumberField IsDedekindDomain IsLocalRing Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Residue

variable {L : Type*} [Field L] [NumberField L] (𝔓 : HeightOneSpectrum (𝓞 L))

instance finite_residueField_localizationAt : Finite (ResidueField (localizationAt L 𝔓)) :=
  Finite.of_equiv _
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔓.asIdeal (localizationAt L 𝔓)).toEquiv

theorem algebraMap_mem_maximalIdeal_localizationAt_iff (a : 𝓞 L) :
    algebraMap (𝓞 L) (localizationAt L 𝔓) a ∈ maximalIdeal (localizationAt L 𝔓) ↔ a ∈ 𝔓.asIdeal :=
  IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a

theorem charP_residueField_localizationAt {p : ℕ} (hp : p.Prime) (hmem : (p : 𝓞 L) ∈ 𝔓.asIdeal) :
    CharP (ResidueField (localizationAt L 𝔓)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 p).2 hmem
  rw [map_natCast] at h
  rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
  exact h

variable {K : Type*} [Field K] [Algebra K L]

theorem residue_smul_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    (a : 𝓞 L) :
    IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ (σ • a)) =
      IsLocalRing.residue (localizationAt L 𝔓) (algebraMap (𝓞 L) _ a) ^
        Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff, ← map_pow, ← map_sub,
    algebraMap_mem_maximalIdeal_localizationAt_iff]
  exact hσ a

omit [NumberField L] in
theorem smul_notMem_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {s : 𝓞 L} (hs : s ∉ 𝔓.asIdeal) : σ • s ∉ 𝔓.asIdeal := by
  intro h
  apply hs
  have h' : s ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) ∈ 𝔓.asIdeal := by
    have := 𝔓.asIdeal.sub_mem h (hσ s)
    simpa using this
  exact 𝔓.isPrime.mem_of_pow_mem _ h'

theorem residue_apply_of_isArithFrobAt {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal)
    {x : L} (hx : x ∈ localizationAt L 𝔓) :
    ∃ h : σ x ∈ localizationAt L 𝔓, IsLocalRing.residue (localizationAt L 𝔓) ⟨σ x, h⟩ =
      IsLocalRing.residue (localizationAt L 𝔓) ⟨x, hx⟩ ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  set q := Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K))
  obtain ⟨a, s, hs, hxs⟩ := mem_localizationAt_iff.1 hx
  have hs0 : (algebraMap (𝓞 L) L s) ≠ 0 := by
    intro h0
    apply hs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσs := smul_notMem_of_isArithFrobAt 𝔓 hσ hs
  have hσs0 : (algebraMap (𝓞 L) L (σ • s)) ≠ 0 := by
    intro h0
    apply hσs
    rw [(IsFractionRing.injective (𝓞 L) L) (h0.trans (map_zero _).symm)]
    exact 𝔓.asIdeal.zero_mem
  have hσx : σ x = algebraMap (𝓞 L) L (σ • a) * (algebraMap (𝓞 L) L (σ • s))⁻¹ := by
    rw [hxs, map_mul, map_inv₀]
    rfl
  have hmem : σ x ∈ localizationAt L 𝔓 := mem_localizationAt_iff.2 ⟨σ • a, σ • s, hσs, hσx⟩
  refine ⟨hmem, ?_⟩
  set R := localizationAt L 𝔓
  set A := algebraMap (𝓞 L) R
  have e1 : (⟨x, hx⟩ : R) * A s = A a := by
    apply Subtype.ext
    change x * algebraMap (𝓞 L) L s = algebraMap (𝓞 L) L a
    rw [hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have e2 : (⟨σ x, hmem⟩ : R) * A (σ • s) = A (σ • a) := by
    apply Subtype.ext
    change σ x * algebraMap (𝓞 L) L (σ • s) = algebraMap (𝓞 L) L (σ • a)
    rw [hσx, mul_assoc, inv_mul_cancel₀ hσs0, mul_one]
  have hres : IsLocalRing.residue R (A (σ • s)) ≠ 0 := by
    rw [Ne, residue_eq_zero_iff, algebraMap_mem_maximalIdeal_localizationAt_iff]
    exact hσs
  have r1 := congrArg (IsLocalRing.residue R) e1
  have r2 := congrArg (IsLocalRing.residue R) e2
  rw [map_mul] at r1 r2
  rw [residue_smul_of_isArithFrobAt 𝔓 hσ, residue_smul_of_isArithFrobAt 𝔓 hσ, ← r1, mul_pow] at r2
  exact mul_right_cancel₀ (by rwa [residue_smul_of_isArithFrobAt 𝔓 hσ] at hres) r2

end Residue

section DegreeOne

theorem intCast_surjective_ringOfIntegers_rat :
    Function.Surjective (Int.castRingHom (𝓞 ℚ)) := by
  intro z
  refine ⟨Rat.ringOfIntegersEquiv z, Rat.ringOfIntegersEquiv.injective ?_⟩
  simp

theorem absNorm_prime_of_ringOfIntegers_rat (𝔮 : Ideal (𝓞 ℚ)) (h0 : 𝔮 ≠ ⊥) [𝔮.IsMaximal] :
    (Ideal.absNorm 𝔮).Prime := by
  let _ : Field (𝓞 ℚ ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hfin : Finite (𝓞 ℚ ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h0
  set p := ringChar (𝓞 ℚ ⧸ 𝔮)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 ℚ ⧸ 𝔮) p).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 ℚ ⧸ 𝔮) p)
  have : Fact p.Prime := ⟨hp⟩
  let f : ZMod p →+* 𝓞 ℚ ⧸ 𝔮 := ZMod.castHom (dvd_refl p) _
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := intCast_surjective_ringOfIntegers_rat z
    exact ⟨n, by simp [f]⟩
  have hbij : Function.Bijective f := ⟨f.injective, hsurj⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_congr (Equiv.ofBijective f hbij),
    Nat.card_zmod]
  exact hp

theorem absNorm_prime_of_mem_degreeOnePrimes {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ degreeOnePrimes ℚ K) :
    (Ideal.absNorm v.asIdeal).Prime := by
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under (𝓞 ℚ)) v.asIdeal
  have hv' : v.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := hv
  rw [hv', pow_one] at h
  rw [← h]
  have hne : v.asIdeal.under (𝓞 ℚ) ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_under_eq_bot hb)
  have : (v.asIdeal.under (𝓞 ℚ)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  exact absNorm_prime_of_ringOfIntegers_rat _ hne

end DegreeOne

section LatticeForm

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

include hK in
theorem exists_unit_of_homConstSet_eq (L L' : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ₀)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hL' : L'.lattice = idealLattice σ₀ ↑𝔞⁻¹ * L.lattice)
    (φ : Isogeny (weierstrassCurve L) (weierstrassCurve L'))
    (hφ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    ∃ u : (𝓞 K)ˣ, invConst φ = σ₀ (algebraMap (𝓞 K) K u) ∧
      ∀ z : ℂ, homPt φ.toHom (toPoint L z) = toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z) := by
  classical
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hM : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← hφ, homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL']
  have hM' := eq_image_mul_inv hc hM
  have hP : (idealPeriodPair σ₀ hK 𝔞⁻¹).lattice = idealLattice σ₀ ↑𝔞⁻¹ :=
    lattice_idealPeriodPair σ₀ hK _
  have hPend : periodLatticeEnd (idealPeriodPair σ₀ hK 𝔞⁻¹) = cmRingOfEmbedding σ₀ := latticeEnd_idealPeriodPair σ₀ hK _
  have mult : ∀ d : ℂ, (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = (d * ·) '' idealLattice σ₀ ↑𝔞⁻¹ →
      d ∈ cmRingOfEmbedding σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    have h' : d * l ∈ (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) := by
      rw [hd]
      exact ⟨l, hl, rfl⟩
    exact h'
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c hM)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ hM')
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc])
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm, fun z ↦ ?_⟩
  rw [← latticeToHom_homConst φ.toHom, homPt_latticeToHom]
  congr 1
  change homConst _ _ φ.toHom * z = _
  rw [homConst_toHom, ← hcdef, ← ha]

end LatticeForm

section Main

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [NumberField L] in
theorem algebraMap_mem_of_liesOver {𝔭 : HeightOneSpectrum (𝓞 K)} {𝔓 : HeightOneSpectrum (𝓞 L)}
    [h : 𝔓.asIdeal.LiesOver 𝔭.asIdeal] {a : 𝓞 K} (ha : a ∈ 𝔭.asIdeal) :
    algebraMap (𝓞 K) (𝓞 L) a ∈ 𝔓.asIdeal := by
  rw [h.over] at ha
  exact ha

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [NumberField L] in
theorem isogBaseChange_eq_map {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (φ : Isogeny A A') : isogBaseChange (F' := ℂ) φ = φ.map (algebraMap L ℂ) :=
  Isogeny.ext_xy
    (by rw [isogBaseChange_alt, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_x _ φ).symm)
    (by rw [isogBaseChange_y, ← ffMap_algebraMap_eq_bcEmb]; exact (Isogeny.map_y _ φ).symm)

omit [NumberField L] in
include hK in
theorem exists_isogBaseChange_eq_of_isogeny {A A' : WeierstrassCurve L} [A.IsElliptic]
    [A'.IsElliptic] (hA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)) (φ : Isogeny A A')
    (ψ : Isogeny (A.baseChange ℂ) (A'.baseChange ℂ)) :
    ∃ φ' : Isogeny A A', isogBaseChange φ' = ψ := by
  classical
  suffices h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ by
    obtain ⟨φ', hφ'⟩ := ψ.exists_map_eq_of_forall_conj_eq h
    exact ⟨φ', (isogBaseChange_eq_map φ').trans hφ'⟩
  intro g
  set D := dualOver (isogBaseChange (F' := ℂ) φ)
  obtain ⟨Λ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve (A.baseChange ℂ)
  have hΛ : _root_.periodLatticeEnd Λ = cmRingOfEmbedding (algebraMap K ℂ) :=
    latticeEnd_eq_cmRing_of_ringEquiv (algebraMap K ℂ) hK Λ
      ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hA.some))
  have hmem : endConst (A.baseChange ℂ) (D.comp ψ).toHom ∈ cmRingOfEmbedding (algebraMap K ℂ) := by
    rw [← hΛ, ← range_endConst hC]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := (mem_cmRing (algebraMap K ℂ)).1 hmem
  rw [endConst_apply, homConst_toHom, invConst_comp] at ha
  have hD := invConst_dualOver_mul (isogBaseChange (F' := ℂ) φ)
  rw [invConst_isogBaseChange, degree_isogBaseChange] at hD
  change invConst D * _ = _ at hD
  have hD0 : invConst D ≠ 0 := invConst_ne_zero D
  have hc0 : algebraMap L ℂ (invConst φ) ≠ 0 := by
    rw [← invConst_isogBaseChange]
    exact invConst_ne_zero _
  have hψ : invConst ψ = algebraMap L ℂ (algebraMap K L (algebraMap (𝓞 K) K a) * invConst φ /
      φ.degree) := by
    have hdeg0 : (φ.degree : ℂ) ≠ 0 := Nat.cast_ne_zero.2 φ.degree_pos.ne'
    rw [map_div₀, map_mul, map_natCast, ← IsScalarTower.algebraMap_apply, ha, ← hD]
    field_simp
  have hc : invConst (ψ.conj g) = invConst ψ := by
    rw [Isogeny.invConst_conj, hψ]
    exact g.commutes _
  have hQ : (ψ.conj g).toHom - ψ.toHom = 0 := by
    by_contra hne
    have h0 := invConst_ne_zero (isogOfHom _ hne)
    rw [← homConst_toHom, isogOfHom_toHom, map_sub, homConst_toHom, homConst_toHom, hc,
      sub_self] at h0
    exact h0 rfl
  have hQ' : (ψ.conj g).toHom = ψ.toHom := sub_eq_zero.1 hQ
  have h2 := congrArg Subtype.val hQ'
  exact Isogeny.ext' h2

include hK in
theorem exists_mem_maximalIdeal_invConst (𝔭 : HeightOneSpectrum (𝓞 K))
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    ∃ c ∈ maximalIdeal (localizationAt L 𝔓), algebraMap (localizationAt L 𝔓) L c = invConst φ := by
  classical
  set c := invConst φ with hcdef
  have hc0 : algebraMap L ℂ c ≠ 0 := by
    rw [hcdef, ← invConst_isogBaseChange]
    exact invConst_ne_zero _

  have step1 : ∀ β ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      c * algebraMap K L β ∈ localizationAt L 𝔓 := by
    intro β hβ
    by_cases hβ0 : β = 0
    · rw [hβ0, map_zero, mul_zero]
      exact zero_mem _
    have hmem : algebraMap L ℂ c * algebraMap K ℂ β ∈
        homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) := by
      have h' : algebraMap L ℂ c * algebraMap K ℂ β ∈ (homConstSet ((W.baseChange L).baseChange ℂ)
          ((W'.baseChange L).baseChange ℂ) : Set ℂ) := by
        rw [hφ]
        exact ⟨_, map_mem_idealLattice _ hβ, rfl⟩
      exact h'
    obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hmem
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      rw [map_zero] at hQ
      exact mul_ne_zero hc0 ((map_ne_zero _).2 hβ0) hQ.symm
    obtain ⟨ν, hν⟩ := exists_isogBaseChange_eq_of_isogeny hK hEW φ (isogOfHom Q hQ0)
    have e : algebraMap L ℂ (invConst ν) = algebraMap L ℂ (c * algebraMap K L β) := by
      rw [← invConst_isogBaseChange, hν, ← homConst_toHom, isogOfHom_toHom, hQ, map_mul,
        ← IsScalarTower.algebraMap_apply]
    have e' := (algebraMap L ℂ).injective e
    obtain ⟨d, hd, -⟩ := exists_invConst_reduceIsogeny L W W' ν
    rw [← e', ← hd]
    exact d.2

  have h1 : (1 : K) ∈ (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 𝔭.ne_bot)]
    exact FractionalIdeal.one_mem_one _
  have key := FractionalIdeal.mul_induction_on
    (C := fun z : K ↦ ∃ m ∈ maximalIdeal (localizationAt L 𝔓),
      algebraMap (localizationAt L 𝔓) L m = c * algebraMap K L z) h1
    (fun i hi j hj ↦ by
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
      refine ⟨⟨c * algebraMap K L i, step1 i hi⟩ * algebraMap (𝓞 L) (localizationAt L 𝔓)
        (algebraMap (𝓞 K) (𝓞 L) a), Ideal.mul_mem_left _ _
          ((algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2
            (algebraMap_mem_of_liesOver ha)), ?_⟩
      change c * algebraMap K L i * algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L, map_mul,
        mul_assoc])
    (fun x y ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩ ↦
      ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [(algebraMap (localizationAt L 𝔓) L).map_add, e₁, e₂, (algebraMap K L).map_add, mul_add]⟩)
  obtain ⟨m, hm, e⟩ := key
  exact ⟨m, hm, by rw [e, map_one, mul_one]⟩

include hK in
theorem reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hEW : Nonempty (isogEnd ((W.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (hEW' : Nonempty (isogEnd ((W'.baseChange L).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny (W.baseChange L) (W'.baseChange L))
    (hφ : (homConstSet ((W.baseChange L).baseChange ℂ) ((W'.baseChange L).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' φ = ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  obtain ⟨c, hc, hcφ⟩ := exists_mem_maximalIdeal_invConst hK 𝔭 𝔓 hEW φ hφ
  have hdeg : φ.degree = Ideal.absNorm 𝔭.asIdeal := by
    have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, hEW⟩) (E' := ⟨_, hEW'⟩) 𝔭 hv
      (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ)
    rwa [degree_isogBaseChange] at h
  have hp : p = Ideal.absNorm 𝔭.asIdeal := by
    have hmem : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 L) ∈ 𝔓.asIdeal := by
      have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
      rwa [map_natCast] at this
    have h0 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ResidueField (localizationAt L 𝔓)) = 0 := by
      have h := (algebraMap_mem_maximalIdeal_localizationAt_iff 𝔓 _).2 hmem
      rw [map_natCast] at h
      rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), residue_eq_zero_iff]
      exact h
    have hdvd := (CharP.cast_eq_zero_iff (ResidueField (localizationAt L 𝔓)) p _).1 h0
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) hv).1 hdvd
  have hdeg' : φ.degree = p := hdeg.trans hp.symm
  obtain ⟨ψ, h1, h2, -, h4, h5⟩ := reduceIsogeny_eq_comp_frobeniusIsogeny L p φ hdeg' hc hcφ
  exact ⟨hp, hdeg', ⟨ψ, h1, h2, h4, h5⟩, residue_j_eq_pow L p φ hdeg' hc hcφ⟩

include hK in
theorem reduceIsogeny_congr_eq_comp_frobeniusIsogeny (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] {A A' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic]
    (hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K))
    (hEA' : Nonempty (isogEnd (A'.baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny A A')
    (hφ : (homConstSet (A.baseChange ℂ) (A'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {W W' : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic] [W'.IsElliptic]
    (hW : W.map (algebraMap (localizationAt L 𝔓) L) = A)
    (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) = A')
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p] :
    p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
      (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
          (W'.map (IsLocalRing.residue _)),
        reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
          ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
        ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
        ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
      IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  subst hW hW'
  erw [Isogeny.congr_rfl]
  exact reduceIsogeny_eq_comp_frobeniusIsogeny_of_homConstSet hK 𝔭 hv 𝔓 hEA hEA' φ hφ p

end Main

section Global

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

abbrev primeClass (𝔭 : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [NumberField L] in
theorem ELL.j_eq_algebraMap_j {A : WeierstrassCurve L} [A.IsElliptic] {x : ELL K}
    {h : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K)}
    (hx : (⟨A.baseChange ℂ, h⟩ : CMCurve K).toEll = x) : ELL.j x = algebraMap L ℂ A.j := by
  rw [← hx, ELL.j_toEll]
  exact WeierstrassCurve.map_j _ _

omit [NumberField L] in
include hK in
theorem exists_isogeny_primeClass_smul
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y)))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (x : ELL K) :
    ∃ φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧
      ((Ideal.absNorm 𝔭.asIdeal).Prime → φ.degree = Ideal.absNorm 𝔭.asIdeal) := by
  classical
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x
  obtain ⟨h₀, hx⟩ := hE x
  obtain ⟨h₁, hy⟩ := hE y
  obtain ⟨ψ, hψ⟩ := exists_isogeny_homConstSet_eq (algebraMap K ℂ) hK
    (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 (by rw [hx, hy])
  obtain ⟨φ, hφ⟩ := exists_isogBaseChange_eq_of_isogeny hK h₀ (hiso x y).some ψ
  have hφ' : (homConstSet ((E x).baseChange ℂ) ((E y).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← invConst_isogBaseChange, hφ]
    exact hψ
  refine ⟨φ, hφ', fun hv ↦ ?_⟩
  have h := degree_eq_absNorm (algebraMap K ℂ) hK (E := ⟨_, h₀⟩) (E' := ⟨_, h₁⟩) 𝔭 hv
    (isogBaseChange φ) (by rw [invConst_isogBaseChange]; exact hφ')
  rwa [degree_isogBaseChange] at h

include hK in
theorem frobenius_at_primes_of_degree_one (hL : ∀ x : ELL K, ELL.j x ∈ L)
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y))) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite ∧ ∀ 𝔭 ∉ S, 𝔭 ∈ degreeOnePrimes ℚ K →
      ∀ (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal],
        (∃ (W : ELL K → WeierstrassCurve (localizationAt L 𝔓)) (_ : ∀ x, (W x).IsElliptic),
          (∀ x, (W x).map (algebraMap (localizationAt L 𝔓) L) = E x) ∧
          Pairwise fun x y ↦ IsLocalRing.residue _ (W x).j ≠ IsLocalRing.residue _ (W y).j) ∧
        (∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ 𝔓.asIdeal →
          galClassOf hK L hL σ = primeClass 𝔭 ∧
          ∀ x : ELL K, σ ⟨ELL.j x, hL x⟩ =
            ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x), hL _⟩) ∧
        ∀ (x : ELL K)
          (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
          (homConstSet ((E x).baseChange ℂ)
              ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) :
                Set ℂ) =
            (algebraMap L ℂ (invConst φ) * ·) ''
              idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
          ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
            (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
            (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
              E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
            (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
            p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
              (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
                  (W'.map (IsLocalRing.residue _)),
                reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
                  ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
                ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
                ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
              IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
  classical
  have : Finite (ELL K) := finite_ell hK
  have hj : ∀ x, ELL.j x = algebraMap L ℂ (E x).j := fun x ↦ by
    obtain ⟨h, hx⟩ := hE x
    exact ELL.j_eq_algebraMap_j hx
  have hEj : Pairwise fun x y ↦ (E x).j ≠ (E y).j := fun x y hxy e ↦
    hxy (ELL.j_injective (by rw [hj, hj, e]))
  obtain ⟨T, hT, hTgood⟩ :=
    exists_finite_forall_liesOver (K := K) (eventually_goodReduction E hEj)
  refine ⟨T, hT, fun 𝔭 h𝔭T h𝔭1 𝔓 _ ↦ ?_⟩
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  obtain ⟨W, hWell, hWmap, hWj, hWres⟩ := hTgood 𝔭 h𝔭T 𝔓 inferInstance
  have partB : ∀ (x : ELL K)
      (φ : Isogeny (E x) (E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))),
      (homConstSet ((E x).baseChange ℂ)
          ((E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)).baseChange ℂ) : Set ℂ) =
        (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ →
      ∀ (W W' : WeierstrassCurve (localizationAt L 𝔓)) [W.IsElliptic] [W'.IsElliptic]
        (hW : W.map (algebraMap (localizationAt L 𝔓) L) = E x)
        (hW' : W'.map (algebraMap (localizationAt L 𝔓) L) =
          E ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x))
        (p : ℕ) [Fact p.Prime] [CharP (ResidueField (localizationAt L 𝔓)) p],
        p = Ideal.absNorm 𝔭.asIdeal ∧ φ.degree = p ∧
          (∃ ψ : Isogeny (frobeniusTwist (W.map (IsLocalRing.residue _)) p)
              (W'.map (IsLocalRing.residue _)),
            reduceIsogeny L W W' (φ.congr hW.symm hW'.symm) =
              ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue _)) p) ∧
            ψ.degree = 1 ∧ (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
            ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero) ∧
          IsLocalRing.residue _ W'.j = IsLocalRing.residue _ W.j ^ p := by
    intro x φ hφ W W' _ _ hW hW' q _ _
    obtain ⟨h₁, -⟩ := hE x
    obtain ⟨h₂, -⟩ := hE ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x)
    exact reduceIsogeny_congr_eq_comp_frobeniusIsogeny hK 𝔭 hv 𝔓 h₁ h₂ φ hφ hW hW' q
  refine ⟨⟨W, hWell, hWmap, hWres⟩, fun σ hσ ↦ ?_, partB⟩

  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have : Fact p.Prime := ⟨hv⟩
  have : CharP (ResidueField (localizationAt L 𝔓)) p := by
    refine charP_residueField_localizationAt 𝔓 hv ?_
    have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
    rwa [map_natCast] at this
  set x₀ : ELL K := classToEll (algebraMap K ℂ) hK 1
  set y := (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀
  set z := (ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK L hL σ) x₀
  obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK E hE hiso 𝔭 x₀
  obtain ⟨-, -, -, hjy⟩ := partB x₀ φ hφ (W x₀) (W y) (hWmap x₀) (hWmap y) p
  have hjmem : (E x₀).j ∈ localizationAt L 𝔓 := by
    rw [← hWj x₀]
    exact (W x₀).j.2
  obtain ⟨hσmem, hσres⟩ := residue_apply_of_isArithFrobAt 𝔓 hσ hjmem
  have hq : Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) = p := by
    rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), hpdef, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  have hσj : σ (E x₀).j = (E z).j := by
    have h := galClassOf_apply_j hK L hL σ x₀
    have e1 : (⟨ELL.j x₀, hL x₀⟩ : L) = (E x₀).j := Subtype.ext (hj x₀)
    rw [e1] at h
    apply Subtype.ext
    rw [h, hj z]
    rfl
  have key : IsLocalRing.residue _ (W z).j = IsLocalRing.residue _ (W y).j := by
    have ez : (W z).j = ⟨σ (E x₀).j, hσmem⟩ := Subtype.ext (by
      show ((W z).j : L) = σ (E x₀).j
      rw [hσj, ← hWj z]
      rfl)
    have ex : (W x₀).j = ⟨(E x₀).j, hjmem⟩ := Subtype.ext (by
      show ((W x₀).j : L) = (E x₀).j
      rw [← hWj x₀]
      rfl)
    rw [ez, hσres, hq, hjy, ex]
  have hzy : z = y := by
    by_contra hne
    exact hWres hne key
  have hcls : galClassOf hK L hL σ = primeClass 𝔭 := by
    obtain ⟨a, -, huniq⟩ := existsUnique_smul_eq (algebraMap K ℂ) hK x₀ y
    exact (huniq _ hzy).trans (huniq _ rfl).symm
  refine ⟨hcls, fun x ↦ Subtype.ext ?_⟩
  rw [galClassOf_apply_j, hcls]

end Global

end
end Elliptic
end

section
namespace Elliptic
noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField Polynomial
open scoped nonZeroDivisors

section Galois

theorem exists_isGalois_le {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω]
    [Algebra F Ω] (M : IntermediateField F Ω) [FiniteDimensional F M] :
    ∃ L : IntermediateField F Ω, M ≤ L ∧ FiniteDimensional F L ∧ IsGalois F L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F M
  have hM : M = F⟮(α : Ω)⟯ := by
    rw [← lift_adjoin_simple F M α, hα, lift_top (K := M)]
  have hint : IsIntegral F (α : Ω) := (Algebra.IsIntegral.isIntegral α).map M.val
  have hsplit : ((minpoly F (α : Ω)).map (algebraMap F Ω)).Splits := IsAlgClosed.splits _
  have := adjoin_rootSet_isSplittingField hsplit
  refine ⟨adjoin F ((minpoly F (α : Ω)).rootSet Ω), ?_,
    IsSplittingField.finiteDimensional _ (minpoly F (α : Ω)),
    IsGalois.of_separable_splitting_field (minpoly.irreducible hint).separable⟩
  exact hM.le.trans (adjoin_simple_le_iff.2
    (subset_adjoin F _ (mem_rootSet.2 ⟨minpoly.ne_zero hint, minpoly.aeval F _⟩)))

end Galois

section Models

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

omit [Algebra K ℂ] in
theorem exists_cmCurve_toEll_of_j_eq (x : ELL K) (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (hW : W.j = ELL.j x) :
    ∃ h : Nonempty (isogEnd W ≃+* 𝓞 K), (⟨W, h⟩ : CMCurve K).toEll = x := by
  classical
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq E.curve W (by rw [hW, ELL.j_toEll])
  refine ⟨⟨(vcEndEquiv C hC).symm.trans E.endIso.some⟩, ?_⟩
  exact (CMCurve.toEll_eq_iff _ _).2 ⟨C⁻¹, inv_smul_eq_of_smul_eq C hC⟩

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]

include hK in
theorem nonempty_isogeny_of_cmCurve (A B : CMCurve K) : Nonempty (Isogeny A.curve B.curve) := by
  classical
  obtain ⟨a, ha, -⟩ := existsUnique_smul_eq (algebraMap K ℂ) hK A.toEll B.toEll
  obtain ⟨I, rfl⟩ := classGroup_mk_surjective hK a
  obtain ⟨c, hc, hset⟩ := homConstSet_of_smul (algebraMap K ℂ) hK ha
  have hI : (((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≠ ⊥ := by
    rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    exact Units.ne_zero _
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hmem : c * algebraMap K ℂ t ∈ (homConstSet A.curve B.curve : Set ℂ) := by
    rw [hset]
    exact ⟨_, map_mem_idealLattice _ ht, rfl⟩
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hmem
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact mul_ne_zero hc ((_root_.map_ne_zero _).2 ht0) hQ.symm
  exact ⟨isogOfHom Q hQ0⟩

include hK in
theorem exists_models_isogenous_of (M J : IntermediateField K ℂ) [FiniteDimensional K M]
    [FiniteDimensional K J] (E₀ : ELL K → WeierstrassCurve J) [∀ y, (E₀ y).IsElliptic]
    (hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y) :
    ∃ L : IntermediateField K ℂ, M ≤ L ∧ FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ hJL : J ≤ L,
        (∀ x, ∃ h : Nonempty (isogEnd (((E₀ x).map (inclusion hJL).toRingHom).baseChange ℂ) ≃+* 𝓞 K),
          (⟨((E₀ x).map (inclusion hJL).toRingHom).baseChange ℂ, h⟩ : CMCurve K).toEll = x) ∧
        ∀ x y, Nonempty (Isogeny ((E₀ x).map (inclusion hJL).toRingHom)
          ((E₀ y).map (inclusion hJL).toRingHom)) := by
  classical
  haveI := finite_ell hK
  haveI : NumberField J := NumberField.of_module_finite K J
  have hE₀ : ∀ y, ∃ h : Nonempty (isogEnd ((E₀ y).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E₀ y).baseChange ℂ, h⟩ : CMCurve K).toEll = y := fun y ↦
    exists_cmCurve_toEll_of_j_eq y _ (by
      show ((E₀ y).map (algebraMap J ℂ)).j = _
      rw [map_j, hE₀j])
  have hF : ∀ p : ELL K × ELL K, ∃ F₁ : IntermediateField J ℂ, NumberField F₁ ∧
      Nonempty (Isogeny ((E₀ p.1).baseChange F₁) ((E₀ p.2).baseChange F₁)) := by
    rintro ⟨y, z⟩
    obtain ⟨hy, -⟩ := hE₀ y
    obtain ⟨hz, -⟩ := hE₀ z
    obtain ⟨ψ⟩ := nonempty_isogeny_of_cmCurve hK ⟨_, hy⟩ ⟨_, hz⟩
    obtain ⟨F₁, hF₁, φ, -⟩ := Isogeny.exists_numberField_mapOf_eq ψ
    exact ⟨F₁, hF₁, ⟨φ⟩⟩
  choose F hFnum hFiso using hF
  have hFfin : ∀ p, FiniteDimensional K ((F p).restrictScalars K) := fun p ↦ by
    haveI := hFnum p
    haveI : FiniteDimensional ℚ ((F p).restrictScalars K) := (inferInstance : FiniteDimensional ℚ (F p))
    exact Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)
  set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K
  haveI : FiniteDimensional K M' := by
    haveI := hFfin
    infer_instance
  obtain ⟨L, hM'L, hLfin, hLgal⟩ := exists_isGalois_le M'
  have hJL : J ≤ L := le_trans (le_trans le_sup_right le_sup_left) hM'L
  have hFL : ∀ p, (F p).restrictScalars K ≤ L := fun p ↦
    le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L
  set ι : J →+* L := (inclusion hJL).toRingHom
  refine ⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, hJL,
    fun y ↦ ?_, fun y z ↦ ?_⟩
  · refine exists_cmCurve_toEll_of_j_eq y _ ?_
    show (((E₀ y).map ι).map (algebraMap L ℂ)).j = _
    rw [map_j, map_j]
    exact hE₀j y
  · obtain ⟨φ⟩ := hFiso (y, z)
    let κ : F (y, z) →+* L := (inclusion (hFL (y, z))).toRingHom
    have hκ : κ.comp (algebraMap J (F (y, z))) = ι := by
      ext a
      rfl
    have e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = (E₀ w).map ι := fun w ↦ by
      show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _
      rw [WeierstrassCurve.map_map, hκ]
    exact ⟨(φ.map κ).congr (e y) (e z)⟩

include hK in
theorem exists_models_isogenous (M : IntermediateField K ℂ) [FiniteDimensional K M] :
    ∃ L : IntermediateField K ℂ, M ≤ L ∧ FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ _ : ∀ x : ELL K, ELL.j x ∈ L, ∃ (E : ELL K → WeierstrassCurve L) (_ : ∀ x, (E x).IsElliptic),
        (∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
          (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x) ∧
        ∀ x y, Nonempty (Isogeny (E x) (E y)) := by
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯
  have hJ : ∀ y, ELL.j y ∈ J := fun y ↦ ELL.j_mem_adjoin hK x₀ y
  haveI : FiniteDimensional K J :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  obtain ⟨L, hML, hLfin, hLgal, hJL, hcm, hiso⟩ :=
    exists_models_isogenous_of hK M J (fun y ↦ ofJ (⟨ELL.j y, hJ y⟩ : J))
      (fun y ↦ by simp only [ofJ_j]; rfl)
  exact ⟨L, hML, hLfin, hLgal, fun y ↦ hJL (hJ y), fun y ↦ (ofJ (⟨ELL.j y, hJ y⟩ : J)).map (inclusion hJL).toRingHom,
    fun _ ↦ inferInstance, hcm, hiso⟩

end Models

end
end Elliptic
end

section
open IsDedekindDomain NumberField
open scoped Pointwise

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in
theorem algebraMap_restrictNormalHom_smul (σ : Gal(L/K)) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x) =
      σ • algebraMap (𝓞 F) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap F L ((σ.restrictNormal F) (x : F)) = σ (algebraMap F L (x : F))
  exact AlgEquiv.restrictNormal_commutes σ F x

theorem IsArithFrobAt.restrictNormalHom {φ : Gal(L/K)} {Q : Ideal (𝓞 L)}
    (h : IsArithFrobAt (𝓞 K) φ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom F φ) (Q.under (𝓞 F)) := by
  intro x
  rw [Ideal.under_under]
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F φ • x -
    x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) ∈ Q
  rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact h _
end

section
namespace Elliptic
noncomputable section

open NumberField IsDedekindDomain Module IntermediateField WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {H L : IntermediateField K Ω}
  (h : H ≤ L)

def galRestrict [Normal K H] : (L ≃ₐ[K] L) →* (H ≃ₐ[K] H) :=
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  AlgEquiv.restrictNormalHom H

theorem galRestrict_apply [Normal K H] (σ : L ≃ₐ[K] L) (z : H) :
    ((galRestrict h σ z : H) : Ω) = (σ (inclusion h z) : Ω) := by
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ H z)

theorem galRestrict_surjective [Normal K H] [Normal K L] :
    Function.Surjective (galRestrict h) := by
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := H) (E := L)

theorem mem_fixingSubgroup_restrict_iff [Normal K H] (σ : L ≃ₐ[K] L) :
    σ ∈ (restrict h).fixingSubgroup ↔ galRestrict h σ = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ
    ext z
    rw [galRestrict_apply, hσ _ ((mem_restrict h _).2 z.2)]
    rfl
  · intro hσ a ha
    have e := galRestrict_apply h σ ⟨a.1, (mem_restrict h a).1 ha⟩
    rw [hσ] at e
    exact Subtype.ext e.symm

end Restrict

section Frobenius

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem exists_isArithFrobAt_galRestrict {H L : IntermediateField K ℂ} [NumberField H]
    [NumberField L] [IsGalois K H] [IsGalois K L] (h : H ≤ L) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    ∃ w' : HeightOneSpectrum (𝓞 H), w'.asIdeal.LiesOver v.asIdeal ∧
      IsArithFrobAt (𝓞 K) (galRestrict h σ) w'.asIdeal := by
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨HeightOneSpectrum.under (𝓞 H) w, ?_, ?_⟩
  · have : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 H) w).asIdeal :=
      ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩
    exact Ideal.LiesOver.tower_bot w.asIdeal _ v.asIdeal
  · rw [HeightOneSpectrum.under_asIdeal]
    exact IsArithFrobAt.restrictNormalHom (F := H) hσ

theorem galRestrict_eq_of_isArithFrobAt {L : IntermediateField K ℂ} [NumberField L] [IsGalois K L]
    (hHL : hilbertClassField K ℂ ≤ L) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    galRestrict hHL σ = hilbertClassFieldArtinEquiv K ℂ (primeClass v) := by
  obtain ⟨w', hw', h1⟩ := exists_isArithFrobAt_galRestrict hHL v w σ hσ
  rw [hilbertClassFieldArtinEquiv_mk0 K ℂ v w']
  have hram : w'.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (isUnramifiedIn_iff_ramificationIdx K (hilbertClassField K ℂ) v).1
      ((isUnramifiedEverywhere_hilbertClassField K ℂ).1 v) w' hw'
  have hI : w'.asIdeal.inertia (hilbertClassField K ℂ ≃ₐ[K] hilbertClassField K ℂ) = ⊥ := by
    rw [← Subgroup.card_eq_one, natCard_inertia v w', hram]
  exact IsArithFrobAt.eq_of_inertia_eq_bot hI h1 (IsArithFrobAt.arithFrobAt _ _ _)

end Frobenius

section Main

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

include hK in
theorem galClassOf_eq_artin (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hHL : hilbertClassField K ℂ ≤ L) (hL : ∀ x : ELL K, ELL.j x ∈ L)
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y))) (τ : L ≃ₐ[K] L) :
    galClassOf hK L hL τ = (hilbertClassFieldArtinEquiv K ℂ).symm (galRestrict hHL τ) := by
  classical
  haveI : NumberField L := NumberField.of_module_finite K L
  set β : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K) :=
    (hilbertClassFieldArtinEquiv K ℂ).symm.toMonoidHom.comp (galRestrict hHL)
  change galClassOf hK L hL τ = β τ
  obtain ⟨S, hS, hfrob⟩ := frobenius_at_primes_of_degree_one hK hL E hE hiso
  have key : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∈ degreeOnePrimes ℚ K →
      ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        galClassOf hK L hL (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal) =
          β (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal) := by
    intro v hvS hv1 w hw
    have hσ := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal
    rw [((hfrob v hvS hv1 w).2.1 _ hσ).1]
    change _ = (hilbertClassFieldArtinEquiv K ℂ).symm (galRestrict hHL _)
    rw [galRestrict_eq_of_isArithFrobAt hHL v w _ hσ, MulEquiv.symm_apply_apply]
  set C : Set (L ≃ₐ[K] L) := {ρ | IsConj τ ρ}
  have hC : ∀ σ ∈ C, ∀ ρ : L ≃ₐ[K] L, ρ * σ * ρ⁻¹ ∈ C := fun σ hσ ρ ↦
    IsConj.trans hσ (isConj_iff.2 ⟨ρ, rfl⟩)
  have hdens := hasDirichletDensity_setOf_arithFrobAt_mem C hC
  rw [← hasDirichletDensity_inter_degreeOnePrimes_iff ℚ] at hdens
  haveI : Nonempty C := ⟨⟨τ, IsConj.refl τ⟩⟩
  have hpos : (0 : ℝ) < Nat.card C / Nat.card (L ≃ₐ[K] L) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨hvA, hv1⟩, hvS⟩ :
      (({v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
          arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal ∈ C} ∩ degreeOnePrimes ℚ K) \ S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hne
    have h0 := hasDirichletDensity_zero_of_finite (hS.subset hne)
    have := hdens.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq
    linarith
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  obtain ⟨c, hc⟩ := isConj_iff.1 (hvA w hw).2
  have e := key v hvS hv1 w hw
  rw [← hc] at e
  have conj : ∀ f : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K), f (c * τ * c⁻¹) = f τ := fun f ↦ by
    rw [map_mul, map_mul, map_inv, mul_comm (f c), mul_inv_cancel_right]
  rwa [conj, conj] at e

end Main

end
end Elliptic
end

section
namespace Elliptic
noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

section VC

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem homPt_vcHom (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    homPt (vcHom C hC) R = vcPoint C hC R := by
  have h0 : vcHom C hC ≠ 0 := fun h ↦ vcPt_ne_zero C hC (congrArg Subtype.val h)
  rw [homPt, dite_eq_right h0, Isogeny.pointHom_apply]
  exact pointMap_eq_vcPoint C hC _ (isogOfHom_val _ h0) R

variable {A' B' : WeierstrassCurve F} [A'.IsElliptic] [B'.IsElliptic]

theorem homConstSet_conj (V : VariableChange F) (hV : V • A = B) (V' : VariableChange F)
    (hV' : V' • A' = B') :
    (homConstSet A A' : Set F) =
      ((homConst B' A' (vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')) *
        homConst A B (vcHom V hV)) * ·) '' homConstSet B B' := by
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set Q' := vcHom V⁻¹ (inv_smul_eq_of_smul_eq V hV)
  set R' := vcHom V' hV'
  have e1 : homConst B A Q' * homConst A B Q = 1 := homConst_vcHom_mul_inv V hV
  have e2 : homConst B' A' R * homConst A' B' R' = 1 := homConst_vcHom_mul_inv V' hV'
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst A' B' R' * z * homConst B A Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination (homConst A B Q * homConst B A Q' * z) * e2 + z * e1
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end VC

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

theorem latticeEnd_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    periodLatticeEnd L = periodLatticeEnd L' := by
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔ (∀ l ∈ L'.lattice, α * l ∈ L'.lattice)
  rw [h]

include hK in
theorem latticeEnd_eq_cmRing_of_lattice_eq {L : PeriodPair} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : L.lattice = idealLattice σ₀ 𝔞) : periodLatticeEnd L = cmRingOfEmbedding σ₀ := by
  exact (latticeEnd_eq_of_lattice_eq (L' := idealPeriodPair σ₀ hK 𝔞)
    (h.trans (lattice_idealPeriodPair σ₀ hK 𝔞).symm)).trans
    (latticeEnd_idealPeriodPair σ₀ hK 𝔞)

include hK in
theorem exists_unit_of_forall_mem_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℂ}
    (hc : ∀ z, z ∈ idealLattice σ₀ J ↔ c * z ∈ idealLattice σ₀ J) :
    ∃ ε : (𝓞 K)ˣ, c = σ₀ (algebraMap (𝓞 K) K ε) := by
  have hP := lattice_idealPeriodPair σ₀ hK J
  have hPend : periodLatticeEnd (idealPeriodPair σ₀ hK J) = cmRingOfEmbedding σ₀ :=
    latticeEnd_idealPeriodPair σ₀ hK J
  have hne : ∃ z, z ∉ idealLattice σ₀ J := by
    by_contra h
    push Not at h
    have h1 : (Real.sqrt 2 : ℂ) * (idealPeriodPair σ₀ hK J).ω₁ ∉ (idealPeriodPair σ₀ hK J).lattice :=
      sqrt_two_mul_notMem _
    rw [hP] at h1
    exact h1 (h _)
  obtain ⟨z₀, hz₀⟩ := hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hz₀ ((hc z₀).2 (by rw [zero_mul]; exact zero_mem _))
  have mult : ∀ d : ℂ, (∀ l ∈ idealLattice σ₀ J, d * l ∈ idealLattice σ₀ J) → d ∈ cmRingOfEmbedding σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    exact hd l hl
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c fun l hl ↦ (hc l).1 hl)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ fun l hl ↦ (hc _).2 (by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; exact hl))
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc0])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

include hK in
theorem exists_unit_pointMap_vcPoint (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair)
    (hL : L.lattice = idealLattice σ₀ 𝔞) (hL' : L'.lattice = idealLattice σ₀ ↑(𝔟 * 𝔞))
    {A A' : WeierstrassCurve ℂ} [A.IsElliptic] [A'.IsElliptic]
    (V : VariableChange ℂ) (hV : V • weierstrassCurve L = A)
    (V' : VariableChange ℂ) (hV' : V' • weierstrassCurve L' = A') (φ : Isogeny A A')
    (hφ : (homConstSet A A' : Set ℂ) = (invConst φ * ·) '' idealLattice σ₀ 𝔟) :
    ∃ u : (𝓞 K)ˣ, ∀ z : ℂ, φ.pointMap (vcPoint V hV (toPoint L z)) =
      vcPoint V' hV' (toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z)) := by
  classical
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set c := homConst A' (weierstrassCurve L') R * homConst (weierstrassCurve L) A Q
  have hset := homConstSet_conj V hV V' hV'

  set Φ := homComp R (homComp φ.toHom Q)
  have hΦ : homConst _ _ Φ = c * invConst φ := by
    rw [homConst_homComp, homConst_homComp, homConst_toHom]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    have e := homConst_vcHom_mul_inv V' hV'
    have e' := homConst_vcHom_mul_inv V hV
    simp only [c, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_mul] at e; exact zero_ne_one e
    · rw [h0, mul_zero] at e'; exact zero_ne_one e'
  have hΦ0 : Φ ≠ 0 := by
    intro h
    have := congrArg (homConst _ _) h
    rw [hΦ, map_zero] at this
    exact mul_ne_zero hc0 (invConst_ne_zero φ) this
  set ψ := isogOfHom Φ hΦ0
  have hψc : invConst ψ = c * invConst φ := by
    rw [← homConst_toHom, isogOfHom_toHom, hΦ]
  have hLend := latticeEnd_eq_cmRing_of_lattice_eq σ₀ hK hL
  have hL'' : L'.lattice = idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ * L.lattice := by
    rw [hL', inv_inv, hL, Units.val_mul, idealLattice_mul]
  have hψ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst ψ * ·) '' idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ := by
    rw [inv_inv, hset, hφ, Set.image_image, hψc]
    congr 1
    funext x
    ring
  obtain ⟨u, -, hu⟩ := exists_unit_of_homConstSet_eq σ₀ hK L L' hLend 𝔟⁻¹ hL'' ψ hψ
  refine ⟨u, fun z ↦ ?_⟩
  have h1 := hu z
  rw [isogOfHom_toHom, TateCharpoly.homPt_homComp, TateCharpoly.homPt_homComp, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, homPt_vcHom, homPt_vcHom, homPt_toHom, Isogeny.pointHom_apply] at h1
  have h2 := congrArg (vcPoint V' hV') h1
  rwa [vcPoint_vcPoint_of_eq_inv V'⁻¹ V' (inv_inv V').symm] at h2

end Lattice

end
end Elliptic
end

end GroundTheory.Global
