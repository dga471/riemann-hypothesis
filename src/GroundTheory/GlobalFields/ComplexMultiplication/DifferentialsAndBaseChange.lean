module

public import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsPic
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsValuation
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogenyExists
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobenius
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobeniusSep
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyRamification
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.SupersingularPowField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilFixedField
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilGaloisFunctionField
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.KaehlerPlace
public import GroundTheory.FunctionField.PlaceDefs
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section
noncomputable section
namespace GroundTheory.Global

section
open WeierstrassCurve

variable {F : Type*} [Field F]

section VariableChangePoint

theorem nonsingular_variableChange (C : VariableChange F) (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (↑C.u⁻¹ ^ 2 * (x - C.r))
      (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hd⟩ := h
  rw [Affine.equation_iff'] at he ⊢
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  set v : F := ↑C.u⁻¹
  refine ⟨?_, ?_⟩
  · linear_combination v ^ 6 * he
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hY : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have : v ^ 3 * (2 * y + W.a₁ * x + W.a₃) = 0 := by linear_combination h2
      simpa [hv] using this
    have hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 := by
      have : v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 0 := by
        linear_combination h1 - v ^ 4 * C.s * hY
      simpa [hv] using this
    rcases hd with hd | hd
    · exact hd hX
    · exact hd hY

def variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F} (hC : C • W = W') :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
      (by subst hC; exact nonsingular_variableChange C W h)

theorem variableChangePoint_some (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint C hC (.some x y h) =
      .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        (by subst hC; exact nonsingular_variableChange C W h) := rfl

end VariableChangePoint
end

section
open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff nonsingular_iff')

universe u v

section Identities

variable {R : Type*} [CommRing R]

private theorem chord_identities {a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ x₃ y₃ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (e₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (e₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hx : x₃ = l ^ 2 + a₁ * l - a₂ - x₁ - x₂)
    (hy : y₃ = -(l * (x₃ - x₁) + y₁) - a₁ * x₃ - a₃) :
    ((2 * l + a₁) * ((3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) - l * (2 * y₁ + a₁ * x₁ + a₃)) -
        (x₁ - x₂) * (2 * y₁ + a₁ * x₁ + a₃)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃) ∧
    (-(2 * l + a₁) * ((3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) - l * (2 * y₂ + a₁ * x₂ + a₃)) -
        (x₁ - x₂) * (2 * y₂ + a₁ * x₂ + a₃)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃) ∧
    (-(x₃ - x₁) * ((3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) - l * (2 * y₁ + a₁ * x₁ + a₃)) -
        (l + a₁) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃) + l * (x₁ - x₂) * (2 * y₁ + a₁ * x₁ + a₃) -
        (x₁ - x₂) * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃) ∧
    ((x₃ - x₁) * ((3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) - l * (2 * y₂ + a₁ * x₂ + a₃)) -
        (l + a₁) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃) := by
  subst hy
  subst hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a₁^2*x₂ - a₁*a₃ + a₁*l*x₁ - 3*a₁*l*x₂ - a₁*y₁ - a₁*y₂ - 2*a₃*l + 2*l^2*x₁ -
      2*l^2*x₂ - 2*l*y₁ - 2*l*y₂) * hl + (-a₁ - 2*l) * e₁ + (a₁ + 2*l) * e₂
  · linear_combination (a₁^2*x₁ + a₁*a₃ + 3*a₁*l*x₁ - a₁*l*x₂ + a₁*y₁ + a₁*y₂ + 2*a₃*l + 2*l^2*x₁ -
      2*l^2*x₂ + 2*l*y₁ + 2*l*y₂ - 2*x₁^2 + 4*x₁*x₂ - 2*x₂^2) * hl + (a₁ + 2*l) * e₁ +
      (-a₁ - 2*l) * e₂
  · linear_combination (a₁^2*l*x₂ - a₁*a₂*x₂ + a₁*a₃*l - a₁*l^2*x₁ + 2*a₁*l^2*x₂ + a₁*l*y₁ +
      a₁*l*y₂ - 3*a₁*x₂^2 - a₂*a₃ + a₂*l*x₁ - a₂*l*x₂ - a₂*y₁ - a₂*y₂ + a₃*l^2 - 3*a₃*x₂ - l^3*x₁ +
      l^3*x₂ + l^2*y₁ + l^2*y₂ + 3*l*x₁*x₂ - 3*l*x₂^2 - 3*x₂*y₁ - 3*x₂*y₂) * hl +
      (a₁*l - a₂ + l^2 - 3*x₂) * e₁ + (-a₁*l + a₂ - l^2 + 3*x₂) * e₂
  · linear_combination (-a₁^2*l*x₁ + a₁*a₂*x₁ - a₁*a₃*l - 2*a₁*l^2*x₁ + a₁*l^2*x₂ - a₁*l*y₁ -
      a₁*l*y₂ + 2*a₁*x₁^2 + 2*a₁*x₁*x₂ - a₁*x₂^2 + a₂*a₃ + a₂*l*x₁ - a₂*l*x₂ + a₂*y₁ + a₂*y₂ -
      a₃*l^2 + 3*a₃*x₁ - l^3*x₁ + l^3*x₂ - l^2*y₁ - l^2*y₂ + l*x₁^2 + l*x₁*x₂ - 2*l*x₂^2 +
      3*x₁*y₁ + 3*x₁*y₂) * hl + (-a₁*l + a₂ - l^2 + 3*x₁) * e₁ + (a₁*l - a₂ + l^2 - 3*x₁) * e₂

private theorem tangent_identities {a₁ a₂ a₃ a₄ x₁ y₁ x₃ y₃ l : R}
    (hl : l * (2 * y₁ + a₁ * x₁ + a₃) = 3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁)
    (hx : x₃ = l ^ 2 + a₁ * l - a₂ - x₁ - x₁)
    (hy : y₃ = -(l * (x₃ - x₁) + y₁) - a₁ * x₃ - a₃) :
    (2 * l + a₁) * ((6 * x₁ + 2 * a₂) * (2 * y₁ + a₁ * x₁ + a₃) -
        a₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) -
        l * (2 * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) + a₁ * (2 * y₁ + a₁ * x₁ + a₃))) -
        2 * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₁ + a₁ * x₁ + a₃) =
      2 * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₃ + a₁ * x₃ + a₃) ∧
    -(x₃ - x₁) * ((6 * x₁ + 2 * a₂) * (2 * y₁ + a₁ * x₁ + a₃) -
        a₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) -
        l * (2 * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) + a₁ * (2 * y₁ + a₁ * x₁ + a₃))) -
        (l + a₁) * (2 * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₃ + a₁ * x₃ + a₃)) +
        l * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₁ + a₁ * x₁ + a₃) -
        (2 * y₁ + a₁ * x₁ + a₃) * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) =
      2 * (2 * y₁ + a₁ * x₁ + a₃) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃) := by
  subst hy
  subst hx
  refine ⟨?_, ?_⟩
  · linear_combination (a₁^2 + 4*a₁*l + 4*l^2) * hl
  · linear_combination (-a₁^2*l + a₁*a₂ - 3*a₁*l^2 + 6*a₁*x₁ + 2*a₂*l + 3*a₃ - 2*l^3 + 6*l*x₁ +
      6*y₁) * hl

end Identities

section AtPoint

variable {F : Type u} [Field F] (E : WeierstrassCurve F) {L : Type v} [Field L] [Algebra F L]

open Classical in
noncomputable def omegaAt : (E.baseChange L).toAffine.Point → Ω[L⁄F]
  | .zero => 0
  | .some x y _ =>
    if 2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃ ≠ 0 then
      (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃)⁻¹ • D F L x
    else
      (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y)⁻¹ • D F L y

@[simp]
theorem omegaAt_zero : omegaAt E (0 : (E.baseChange L).toAffine.Point) = 0 := rfl

theorem D_coeff (c : F) : D F L (algebraMap F L c) = 0 := (D F L).map_algebraMap c

theorem D_equation {x y : L} (h : (E.baseChange L).toAffine.Equation x y) :
    (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃) • D F L y =
      (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y) • D F L x := by
  have e := congrArg (D F L) ((equation_iff _ _).mp h)
  have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have h2 : D F L (E.baseChange L).a₂ = 0 := D_coeff E.a₂
  have h3 : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
  have h4 : D F L (E.baseChange L).a₄ = 0 := D_coeff E.a₄
  have h6 : D F L (E.baseChange L).a₆ = 0 := D_coeff E.a₆
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, h1, h2, h3, h4, h6, smul_zero,
    add_zero] at e
  linear_combination (norm := module) e

theorem omegaAt_some_spec {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃) • omegaAt E (.some x y h) =
        D F L x ∧
      (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y) • omegaAt E (.some x y h) = D F L y := by
  have rel := D_equation E h.1
  have hns := ((nonsingular_iff' _ _).mp h).2
  set a := 2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃ with ha
  set b := 3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
    (E.baseChange L).a₁ * y with hb
  have hb' : (E.baseChange L).a₁ * y - (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x +
      (E.baseChange L).a₄) = -b := by rw [hb]; ring
  rw [hb', neg_ne_zero] at hns
  by_cases hu : a ≠ 0
  · have e : omegaAt E (.some x y h) = a⁻¹ • D F L x := by
      simp only [omegaAt, ← ha, ite_eq_left hu]
    rw [e, smul_smul, mul_inv_cancel₀ hu, one_smul, smul_smul, mul_comm, ← smul_smul, ← rel,
      smul_smul, inv_mul_cancel₀ hu, one_smul]
    exact ⟨rfl, rfl⟩
  · have e : omegaAt E (.some x y h) = b⁻¹ • D F L y := by
      simp only [omegaAt, ← ha, ← hb, ite_eq_right hu]
    rw [not_not] at hu
    have hb0 : b ≠ 0 := hns.resolve_right (fun h' => h' hu)
    have hx : D F L x = 0 := by
      have := rel
      rw [hu, zero_smul] at this
      exact (smul_eq_zero.mp this.symm).resolve_left hb0
    rw [e, hu, zero_smul, hx, smul_smul, mul_inv_cancel₀ hb0, one_smul]
    exact ⟨rfl, rfl⟩

theorem omegaAt_some_eq {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) {η : Ω[L⁄F]}
    (h₁ : (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃) • η = D F L x)
    (h₂ : (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y) • η = D F L y) :
    omegaAt E (.some x y h) = η := by
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec E h
  have hns := ((nonsingular_iff' _ _).mp h).2
  rcases hns with hp | hu
  · have hp' : 3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y ≠ 0 := by
      intro h0; apply hp; linear_combination -h0
    exact smul_right_injective _ hp' (s₂.trans h₂.symm)
  · exact smul_right_injective _ hu (s₁.trans h₁.symm)

end AtPoint

section Add

variable {F : Type u} [Field F] (E : WeierstrassCurve F) {L : Type v} [Field L] [Algebra F L]

theorem D_two : D F L (2 : L) = 0 := by simpa using (D F L).map_natCast 2

theorem D_three : D F L (3 : L) = 0 := by simpa using (D F L).map_natCast 3

theorem D_addX (x₁ x₂ l : L) :
    D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) =
      (2 * l + (E.baseChange L).a₁) • D F L l - D F L x₁ - D F L x₂ := by
  have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have h2 : D F L (E.baseChange L).a₂ = 0 := D_coeff E.a₂
  simp only [WeierstrassCurve.Affine.addX, map_sub, map_add (f := _), Derivation.leibniz,
    Derivation.leibniz_pow, h1, h2, smul_zero, add_zero]
  module

theorem D_addY (x₁ x₂ y₁ l : L) :
    D F L ((E.baseChange L).toAffine.addY x₁ x₂ y₁ l) =
      -(l • (D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) - D F L x₁) +
        ((E.baseChange L).toAffine.addX x₁ x₂ l - x₁) • D F L l) - D F L y₁ -
        (E.baseChange L).a₁ • D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) := by
  have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have h3 : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, map_sub, map_add, map_neg, Derivation.leibniz, h1, h3,
    smul_zero, add_zero, sub_zero]
  module

variable [DecidableEq L]

theorem omegaAt_neg (P : (E.baseChange L).toAffine.Point) : omegaAt E (-P) = -omegaAt E P := by
  rcases P with _ | ⟨x, y, h⟩
  · show omegaAt E (-0) = -omegaAt E 0
    simp
  · obtain ⟨s, t⟩ := omegaAt_some_spec E h
    have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
    have h3 : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
    rw [Point.neg_some]
    refine omegaAt_some_eq E _ ?_ ?_
    · rw [← s]
      simp only [WeierstrassCurve.Affine.negY]
      module
    · simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, Derivation.leibniz, h1, h3,
        smul_zero, add_zero, sub_zero, ← s, ← t]
      module

theorem omegaAt_add (P Q : (E.baseChange L).toAffine.Point) :
    omegaAt E (P + Q) = omegaAt E P + omegaAt E Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show omegaAt E (0 + 0) = omegaAt E 0 + omegaAt E 0
    simp
  · show omegaAt E (0 + _) = omegaAt E 0 + _
    simp
  · show omegaAt E (_ + 0) = _ + omegaAt E 0
    simp
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E.baseChange L).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, omegaAt_zero]
    obtain ⟨rfl, rfl⟩ := hxy
    have e : (Point.some x₁ ((E.baseChange L).toAffine.negY x₁ y₂) h₁ :
        (E.baseChange L).toAffine.Point) = -Point.some x₁ y₂ h₂ := rfl
    rw [e, omegaAt_neg, neg_add_cancel]
  rw [Point.add_some hxy]
  obtain ⟨s₁, t₁⟩ := omegaAt_some_spec E h₁
  obtain ⟨s₂, t₂⟩ := omegaAt_some_spec E h₂
  have e₁ := (equation_iff _ _).mp h₁.1
  have e₂ := (equation_iff _ _).mp h₂.1
  have ha₁ : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have ha₂ : D F L (E.baseChange L).a₂ = 0 := D_coeff E.a₂
  have ha₃ : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
  have ha₄ : D F L (E.baseChange L).a₄ = 0 := D_coeff E.a₄
  set l := (E.baseChange L).toAffine.slope x₁ x₂ y₁ y₂ with hl_def
  set ω₁ := omegaAt E (Point.some x₁ y₁ h₁)
  set ω₂ := omegaAt E (Point.some x₂ y₂ h₂)
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (E.baseChange L).toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    obtain rfl := hx
    obtain rfl := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy
    have hω : ω₂ = ω₁ := rfl
    have hu : y₁ - (E.baseChange L).toAffine.negY x₁ y₁ =
        2 * y₁ + (E.baseChange L).a₁ * x₁ + (E.baseChange L).a₃ := by
      simp only [WeierstrassCurve.Affine.negY]; ring
    have hu0 : 2 * y₁ + (E.baseChange L).a₁ * x₁ + (E.baseChange L).a₃ ≠ 0 := by
      rw [← hu]; exact sub_ne_zero.mpr hy
    have hl : l * (2 * y₁ + (E.baseChange L).a₁ * x₁ + (E.baseChange L).a₃) =
        3 * x₁ ^ 2 + 2 * (E.baseChange L).a₂ * x₁ + (E.baseChange L).a₄ -
          (E.baseChange L).a₁ * y₁ := by
      rw [hl_def, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hu, div_mul_cancel₀ _ hu0]
    have hDl := congrArg (D F L) hl
    simp only [Derivation.leibniz, map_add (f := _), map_sub, Derivation.leibniz_pow, ha₁, ha₂, ha₃, ha₄,
      D_two, D_three, smul_zero, add_zero] at hDl
    rw [← s₁, ← t₁] at hDl
    obtain ⟨iE, iF⟩ := tangent_identities (x₃ := (E.baseChange L).toAffine.addX x₁ x₁ l)
      (y₃ := (E.baseChange L).toAffine.addY x₁ x₁ y₁ l) hl rfl rfl
    have hX : (2 * (E.baseChange L).toAffine.addY x₁ x₁ y₁ l +
        (E.baseChange L).a₁ * (E.baseChange L).toAffine.addX x₁ x₁ l + (E.baseChange L).a₃) •
          (ω₁ + ω₂) = D F L ((E.baseChange L).toAffine.addX x₁ x₁ l) := by
      rw [hω]
      refine smul_right_injective _ hu0 ?_
      beta_reduce
      rw [D_addX, ← s₁]
      linear_combination (norm := module) (-(2 * l + (E.baseChange L).a₁)) • hDl - iE • ω₁
    refine omegaAt_some_eq E _ hX ?_
    refine smul_right_injective _ hu0 ?_
    beta_reduce
    rw [D_addY, ← hX, hω, ← s₁, ← t₁]
    linear_combination (norm := module)
      ((E.baseChange L).toAffine.addX x₁ x₁ l - x₁) • hDl - iF • ω₁
  · have hs : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hl : l * (x₁ - x₂) = y₁ - y₂ := by
      rw [hl_def, WeierstrassCurve.Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hs]
    have hDl := congrArg (D F L) hl
    simp only [Derivation.leibniz, map_sub] at hDl
    rw [← s₁, ← s₂, ← t₁, ← t₂] at hDl
    obtain ⟨iA, iB, iC, iD⟩ := chord_identities (x₃ := (E.baseChange L).toAffine.addX x₁ x₂ l)
      (y₃ := (E.baseChange L).toAffine.addY x₁ x₂ y₁ l) hl e₁ e₂ rfl rfl
    have hX : (2 * (E.baseChange L).toAffine.addY x₁ x₂ y₁ l +
        (E.baseChange L).a₁ * (E.baseChange L).toAffine.addX x₁ x₂ l + (E.baseChange L).a₃) •
          (ω₁ + ω₂) = D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) := by
      refine smul_right_injective _ (mul_ne_zero hs hs) ?_
      beta_reduce
      rw [D_addX, ← s₁, ← s₂]
      linear_combination (norm := module)
        (-((x₁ - x₂) * (2 * l + (E.baseChange L).a₁))) • hDl - iA • ω₁ - iB • ω₂
    refine omegaAt_some_eq E _ hX ?_
    refine smul_right_injective _ (mul_ne_zero hs hs) ?_
    beta_reduce
    rw [D_addY, ← hX, ← s₁, ← t₁]
    linear_combination (norm := module)
      ((x₁ - x₂) * ((E.baseChange L).toAffine.addX x₁ x₂ l - x₁)) • hDl - iC • ω₁ - iD • ω₂

noncomputable def omegaHom : (E.baseChange L).toAffine.Point →+ Ω[L⁄F] :=
  AddMonoidHom.mk' (omegaAt E) (omegaAt_add E)

end Add

section Push

variable {F : Type u} [Field F] {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L']

noncomputable def kpush (σ : L →ₐ[F] L') : Ω[L⁄F] →+ Ω[L'⁄F] :=
  letI : Algebra L L' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  (KaehlerDifferential.map F F L L').toAddMonoidHom

theorem kpush_D (σ : L →ₐ[F] L') (a : L) : kpush σ (D F L a) = D F L' (σ a) := by
  let _ : Algebra L L' := σ.toRingHom.toAlgebra
  have _ : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  exact KaehlerDifferential.map_D F F L L' a

theorem kpush_smul (σ : L →ₐ[F] L') (a : L) (η : Ω[L⁄F]) :
    kpush σ (a • η) = σ a • kpush σ η := by
  let _ : Algebra L L' := σ.toRingHom.toAlgebra
  have _ : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  show KaehlerDifferential.map F F L L' (a • η) = _
  rw [LinearMap.map_smul]
  exact (algebraMap_smul L' a _).symm

variable (E : WeierstrassCurve F) [DecidableEq L] [DecidableEq L']

theorem kpush_omegaAt (σ : L →ₐ[F] L') (P : (E.baseChange L).toAffine.Point) :
    kpush σ (omegaAt E P) = omegaAt E (Point.map σ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show kpush σ (omegaAt E 0) = omegaAt E (Point.map σ 0)
    rw [map_zero, omegaAt_zero, omegaAt_zero, map_zero]
  · rw [Point.map_some]
    obtain ⟨s, t⟩ := omegaAt_some_spec E h
    have c1 : (E.baseChange L').a₁ = σ (E.baseChange L).a₁ := (σ.commutes E.a₁).symm
    have c2 : (E.baseChange L').a₂ = σ (E.baseChange L).a₂ := (σ.commutes E.a₂).symm
    have c3 : (E.baseChange L').a₃ = σ (E.baseChange L).a₃ := (σ.commutes E.a₃).symm
    have c4 : (E.baseChange L').a₄ = σ (E.baseChange L).a₄ := (σ.commutes E.a₄).symm
    refine (omegaAt_some_eq E _ ?_ ?_).symm
    · rw [c1, c3, ← kpush_D, ← s, kpush_smul]
      simp only [map_add (f := _), map_mul, map_ofNat]
    · rw [c1, c2, c4, ← kpush_D, ← t, kpush_smul]
      simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat]

end Push

section Invariant

variable {F : Type u} [Field F] (E : WeierstrassCurve F)

instance isFunctionField_functionField :
    GroundTheory.FunctionField.IsFunctionField F E.toAffine.FunctionField :=
  ⟨⟨genX E, transcendental_genX E, Module.finite_of_finrank_pos (by
    rw [finrank_adjoin_genX E]; norm_num)⟩⟩

variable [E.IsElliptic]

theorem genDen_ne_zero :
    2 * genY E + algebraMap F E.toAffine.FunctionField E.a₁ * genX E +
      algebraMap F E.toAffine.FunctionField E.a₃ ≠ 0 := by
  intro h0
  apply Ψ₂Sq_ne_zero E
  rw [← aeval_genX_eq_zero_iff]
  have e := (equation_iff _ _).mp (equation_gen E)
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, map_add, map_mul, map_pow, aeval_C, aeval_X, map_ofNat]
  linear_combination (2 * genY E + algebraMap F E.toAffine.FunctionField E.a₁ * genX E +
      algebraMap F E.toAffine.FunctionField E.a₃) * h0 - 4 * e

noncomputable def invariantDifferential : Ω[E.toAffine.FunctionField⁄F] :=
  omegaAt E (genericPoint E)

theorem invariantDifferential_eq :
    invariantDifferential E = (2 * genY E + algebraMap F E.toAffine.FunctionField E.a₁ * genX E +
      algebraMap F E.toAffine.FunctionField E.a₃)⁻¹ • D F E.toAffine.FunctionField (genX E) := by
  have h := genDen_ne_zero E
  simp only [invariantDifferential, GroundTheory.Arith.Abelian.genericPoint, omegaAt]
  exact ite_eq_left h

instance isSeparable_adjoin_genX :
    Algebra.IsSeparable F⟮genX E⟯ E.toAffine.FunctionField := by
  set F' := F⟮genX E⟯
  have sepX : IsSeparable F' (genX E) := by
    have : genX E = algebraMap F' E.toAffine.FunctionField
        ⟨genX E, IntermediateField.mem_adjoin_simple_self F _⟩ := rfl
    rw [this]
    exact isSeparable_algebraMap _
  have hAdj : F'⟮genX E⟯ = IntermediateField.extendScalars (le_refl F') := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.extendScalars_restrictScalars,
      Set.pair_eq_singleton]
  have : Algebra.IsSeparable F' F'⟮genX E⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F' E.toAffine.FunctionField).mpr sepX
  have hY : IsSeparable F'⟮genX E⟯ (genY E) := by
    rw [hAdj]; exact isSeparable_genY E _ le_rfl
  have sepY : IsSeparable F' (genY E) := IsSeparable.of_algebra_isSeparable_of_isSeparable F' hY
  have := IntermediateField.isSeparable_adjoin_pair_of_isSeparable F' E.toAffine.FunctionField
    sepX sepY
  have hz : ∀ z : E.toAffine.FunctionField, z ∈ F'⟮genX E, genY E⟯ := by
    intro z
    have htop : (⊤ : IntermediateField F E.toAffine.FunctionField) ≤
        (F'⟮genX E, genY E⟯).restrictScalars F := by
      rw [← adjoin_genX_genY E, IntermediateField.restrictScalars_adjoin]
      exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
    exact htop trivial
  exact ⟨fun z => IntermediateField.isSeparable_of_mem_isSeparable F' E.toAffine.FunctionField (hz z)⟩

theorem D_genX_ne_zero : D F E.toAffine.FunctionField (genX E) ≠ 0 :=
  GroundTheory.Arith.SchemeCoh.D_ne_zero_of_isSeparable (genX E)

theorem invariantDifferential_ne_zero : invariantDifferential E ≠ 0 := by
  rw [invariantDifferential_eq]
  exact smul_ne_zero (inv_ne_zero (genDen_ne_zero E)) (D_genX_ne_zero E)

theorem span_invariantDifferential :
    Submodule.span E.toAffine.FunctionField {invariantDifferential E} = ⊤ := by
  rw [invariantDifferential_eq, Submodule.span_singleton_smul_eq
    (IsUnit.mk0 _ (inv_ne_zero (genDen_ne_zero E)))]
  exact GroundTheory.Arith.SchemeCoh.span_D_eq_top (genX E)

end Invariant

section Pullback

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

noncomputable def isogenyPullback (φ : Isogeny E E') :
    Ω[E'.toAffine.FunctionField⁄F] →+ Ω[E.toAffine.FunctionField⁄F] :=
  kpush φ.comap

omit [E.IsElliptic] [E'.IsElliptic] in
theorem isogenyPullback_D (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    isogenyPullback φ (D F _ f) = D F _ (φ.comap f) :=
  kpush_D _ _

omit [E.IsElliptic] [E'.IsElliptic] in
theorem isogenyPullback_smul (φ : Isogeny E E') (f : E'.toAffine.FunctionField)
    (η : Ω[E'.toAffine.FunctionField⁄F]) :
    isogenyPullback φ (f • η) = φ.comap f • isogenyPullback φ η :=
  kpush_smul _ _ _

theorem isogenyPullback_invariantDifferential (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = omegaAt E' φ.1 := by
  rw [isogenyPullback, invariantDifferential, kpush_omegaAt, φ.map_comap_genericPoint]

end Pullback

section Coefficient

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem mem_span_invariantDifferential (η : Ω[E.toAffine.FunctionField⁄F]) :
    η ∈ Submodule.span E.toAffine.FunctionField {invariantDifferential E} := by
  rw [span_invariantDifferential E]; trivial

noncomputable def invCoeff (η : Ω[E.toAffine.FunctionField⁄F]) : E.toAffine.FunctionField :=
  (Submodule.mem_span_singleton.mp (mem_span_invariantDifferential E η)).choose

theorem invCoeff_smul (η : Ω[E.toAffine.FunctionField⁄F]) :
    invCoeff E η • invariantDifferential E = η :=
  (Submodule.mem_span_singleton.mp (mem_span_invariantDifferential E η)).choose_spec

theorem invCoeff_eq {η : Ω[E.toAffine.FunctionField⁄F]} {c : E.toAffine.FunctionField}
    (h : c • invariantDifferential E = η) : invCoeff E η = c :=
  smul_left_injective _ (invariantDifferential_ne_zero E) ((invCoeff_smul E η).trans h.symm)

theorem invCoeff_add (η₁ η₂ : Ω[E.toAffine.FunctionField⁄F]) :
    invCoeff E (η₁ + η₂) = invCoeff E η₁ + invCoeff E η₂ :=
  invCoeff_eq E (by rw [add_smul, invCoeff_smul, invCoeff_smul])

theorem invCoeff_zero : invCoeff E 0 = 0 :=
  invCoeff_eq E (zero_smul _ _)

theorem invCoeff_invariantDifferential : invCoeff E (invariantDifferential E) = 1 :=
  invCoeff_eq E (one_smul _ _)

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]

variable (E E') in
noncomputable def homCoeff : isogHom E E' →+ E.toAffine.FunctionField where
  toFun Q := invCoeff E (omegaAt E' Q.1)
  map_zero' := by
    show invCoeff E (omegaAt E' 0) = 0
    rw [omegaAt_zero, invCoeff_zero]
  map_add' Q₁ Q₂ := by
    show invCoeff E (omegaAt E' (Q₁.1 + Q₂.1)) = _
    rw [omegaAt_add, invCoeff_add]

omit [E'.IsElliptic] in
theorem homCoeff_smul (Q : isogHom E E') : homCoeff E E' Q • invariantDifferential E = omegaAt E' Q.1 :=
  invCoeff_smul E _

noncomputable def isogCoeff (φ : Isogeny E E') : E.toAffine.FunctionField :=
  homCoeff E E' ⟨φ.1, φ.respectsAdd⟩

theorem isogenyPullback_invariantDifferential_eq_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = isogCoeff φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential, isogCoeff, homCoeff_smul]

variable (E) in
noncomputable def homIdentity : isogHom E E := ⟨genericPoint E, respectsAdd_genericPoint⟩

variable (E) in
theorem homCoeff_zsmul_homIdentity (n : ℤ) : homCoeff E E (n • homIdentity E) = n := by
  rw [map_zsmul]
  show n • invCoeff E (invariantDifferential E) = _
  rw [invCoeff_invariantDifferential, zsmul_one]

variable (E) in
theorem isogCoeff_mulIsogeny (n : ℤ) (hn : n ≠ 0) : isogCoeff (mulIsogeny E n hn) = n :=
  homCoeff_zsmul_homIdentity E n

end Coefficient
end

section
open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F']

section Emb

variable (E : WeierstrassCurve F) [E.IsElliptic]

omit [E.IsElliptic] in
theorem transcendental_genX_baseChange : Transcendental F (genX (E.baseChange F')) :=
  Transcendental.restrictScalars (algebraMap F F').injective (transcendental_genX _)

noncomputable def bcEmb :
    E.toAffine.FunctionField →ₐ[F] (E.baseChange F').toAffine.FunctionField :=
  liftPoint E (L := (E.baseChange F').toAffine.FunctionField) (u := genX (E.baseChange F'))
    (v := genY (E.baseChange F')) (equation_gen (E.baseChange F'))
    (transcendental_genX_baseChange E)

omit [E.IsElliptic] in
theorem bcEmb_genX : bcEmb (F' := F') E (genX E) = genX (E.baseChange F') :=
  liftPoint_genX _ _ _

omit [E.IsElliptic] in
theorem bcEmb_genY : bcEmb (F' := F') E (genY E) = genY (E.baseChange F') :=
  liftPoint_genY _ _ _

theorem map_bcEmb_genericPoint [DecidableEq F'] :
    Point.map (bcEmb (F' := F') E) (genericPoint E) =
      (genericPoint (E.baseChange F') :
        (E.baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) :=
  map_liftPoint_genericPoint E _ _

omit [E.IsElliptic] in
theorem transcendental_bcEmb {z : E.toAffine.FunctionField} (hz : Transcendental F z) :
    Transcendental F' (bcEmb (F' := F') E z) := by
  set K' := (E.baseChange F').toAffine.FunctionField
  set ι := bcEmb (F' := F') E
  intro halg
  have : FiniteDimensional F⟮z⟯ E.toAffine.FunctionField :=
    finiteDimensional_adjoin_of_transcendental E hz
  set A : IntermediateField F' K' := F'⟮ι z⟯
  have hA : Algebra.IsAlgebraic F' A := isAlgebraic_adjoin_simple halg.isIntegral
  have hmem : ∀ w ∈ F⟮z⟯, ι w ∈ A := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact mem_adjoin_simple_self F' _
    | algebraMap x =>
      rw [ι.commutes, IsScalarTower.algebraMap_apply F F' K']
      exact A.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let g : F⟮z⟯ →+* A :=
    { toFun := fun w => ⟨ι w, hmem w w.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hint : IsIntegral F⟮z⟯ (genX E) := Algebra.IsIntegral.isIntegral _
  set p := minpoly F⟮z⟯ (genX E)
  have hq : aeval (genX (E.baseChange F')) (p.map g) = 0 := by
    have e : (algebraMap A K').comp g = ι.toRingHom.comp (algebraMap F⟮z⟯ E.toAffine.FunctionField) := by
      ext w; rfl
    rw [aeval_def, eval₂_map, e, ← bcEmb_genX]
    have h2 := hom_eval₂ p (algebraMap F⟮z⟯ E.toAffine.FunctionField) ι.toRingHom (genX E)
    rw [← aeval_def, minpoly.aeval, map_zero] at h2
    exact h2.symm
  have hX : IsAlgebraic A (genX (E.baseChange F')) :=
    ⟨p.map g, (minpoly.monic hint).map g |>.ne_zero, hq⟩
  exact transcendental_genX (E.baseChange F') (hX.restrictScalars F')

end Emb

section Isog

variable [DecidableEq F'] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

noncomputable def bcPoint (φ : Isogeny E E') :
    ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := E') (bcEmb (F' := F') E) φ.1

omit [DecidableEq F'] [E.IsElliptic] [E'.IsElliptic] in
theorem map_restrictScalars_eq {L : Type u} [Field L] [Algebra F' L] [DecidableEq L]
    (g : (E.baseChange F').toAffine.FunctionField →ₐ[F'] L)
    (X : (E'.baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) :
    letI : Algebra F L := ((algebraMap F' L).comp (algebraMap F F')).toAlgebra
    haveI : IsScalarTower F F' L := IsScalarTower.of_algebraMap_eq' rfl
    Point.map (W' := E') (g.restrictScalars F) X =
      Point.map (W' := E'.baseChange F') g
        (X : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) := by
  cases X <;> rfl

omit [DecidableEq F'] in
theorem isIsogeny_bcPoint (φ : Isogeny E E') :
    IsIsogeny (E.baseChange F') (E'.baseChange F') (bcPoint φ) := by
  rw [isIsogeny_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨x, y, h, he, hx⟩, -⟩ := φ.2
    show IsGenPt (E'.baseChange F') (Point.map (W' := E') (bcEmb (F' := F') E) φ.1)
    rw [he]
    exact transcendental_bcEmb E hx
  · rw [respectsAdd_iff]
    intro L _ _ _ P₁ P₂ h₁ h₂ h₃
    let _ : Algebra F L := ((algebraMap F' L).comp (algebraMap F F')).toAlgebra
    have _ : IsScalarTower F F' L := IsScalarTower.of_algebraMap_eq' rfl
    have res : ∀ P : ((E.baseChange F').baseChange L).toAffine.Point,
        IsGenPt (E.baseChange F') P → IsGenPt E (P : (E.baseChange L).toAffine.Point) := by
      intro P hP
      cases P with
      | zero => exact hP.elim
      | some x y h => exact Transcendental.restrictScalars (algebraMap F F').injective hP
    have key : ∀ (P : ((E.baseChange F').baseChange L).toAffine.Point)
        (hP : IsGenPt (E.baseChange F') P),
        Point.map (genEval (E.baseChange F') P hP) (bcPoint φ) =
          φ.app (P : (E.baseChange L).toAffine.Point) (res P hP) := by
      intro P hP
      have hg : ((genEval (E.baseChange F') P hP).restrictScalars F).comp (bcEmb (F' := F') E) =
          genEval E (P : (E.baseChange L).toAffine.Point) (res P hP) := by
        refine eq_genEval E _ ?_ _
        cases P with
        | zero => exact hP.elim
        | some u v hv =>
          simp only [GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
          congr 1
          · show genEval (E.baseChange F') _ hP (bcEmb (F' := F') E (genX E)) = u
            rw [bcEmb_genX]; exact genEval_genX (E.baseChange F') _ hP
          · show genEval (E.baseChange F') _ hP (bcEmb (F' := F') E (genY E)) = v
            rw [bcEmb_genY]; exact genEval_genY (E.baseChange F') _ hP
      unfold Isogeny.app
      rw [← hg, ← Point.map_map, map_restrictScalars_eq]
      rfl
    rw [key _ h₃, key _ h₁, key _ h₂]
    exact φ.app_add (res _ h₁) (res _ h₂) (res _ h₃)

noncomputable def isogBaseChange (φ : Isogeny E E') : Isogeny (E.baseChange F') (E'.baseChange F') :=
  ⟨bcPoint φ, isIsogeny_bcPoint φ⟩

theorem isogBaseChange_val (φ : Isogeny E E') :
    (isogBaseChange (F' := F') φ).1 = Point.map (W' := E') (bcEmb (F' := F') E) φ.1 := rfl

end Isog

section Diff

variable (E : WeierstrassCurve F) [E.IsElliptic]

noncomputable def bcDiff :
    Ω[E.toAffine.FunctionField⁄F] →+ Ω[(E.baseChange F').toAffine.FunctionField⁄F'] :=
  letI : Algebra E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    (bcEmb (F' := F') E).toRingHom.toAlgebra
  haveI : IsScalarTower F E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun a => ((bcEmb (F' := F') E).commutes a).symm
  (KaehlerDifferential.map F F' E.toAffine.FunctionField
    (E.baseChange F').toAffine.FunctionField).toAddMonoidHom

omit [E.IsElliptic] in
theorem bcDiff_D (a : E.toAffine.FunctionField) :
    bcDiff (F' := F') E (D F _ a) = D F' _ (bcEmb (F' := F') E a) := by
  let _ : Algebra E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    (bcEmb (F' := F') E).toRingHom.toAlgebra
  have _ : IsScalarTower F E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun a => ((bcEmb (F' := F') E).commutes a).symm
  exact KaehlerDifferential.map_D F F' _ _ a

omit [E.IsElliptic] in
theorem bcDiff_smul (a : E.toAffine.FunctionField) (η : Ω[E.toAffine.FunctionField⁄F]) :
    bcDiff (F' := F') E (a • η) = bcEmb (F' := F') E a • bcDiff E η := by
  let _ : Algebra E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    (bcEmb (F' := F') E).toRingHom.toAlgebra
  have _ : IsScalarTower F E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun a => ((bcEmb (F' := F') E).commutes a).symm
  show KaehlerDifferential.map F F' _ _ (a • η) = _
  rw [LinearMap.map_smul]
  exact (algebraMap_smul (E.baseChange F').toAffine.FunctionField a _).symm

variable [DecidableEq F'] {E} {E' : WeierstrassCurve F}

omit [E.IsElliptic] [DecidableEq F'] in
theorem bcDiff_omegaAt (P : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) :
    bcDiff (F' := F') E (omegaAt E' P) =
      omegaAt (E'.baseChange F') (Point.map (W' := E') (bcEmb (F' := F') E) P :
        ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) := by
  rcases P with _ | ⟨x, y, h⟩
  · show bcDiff E (omegaAt E' 0) = omegaAt (E'.baseChange F') 0
    rw [omegaAt_zero, omegaAt_zero, map_zero]
  · obtain ⟨s, t⟩ := omegaAt_some_spec E' h
    have c1 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₁ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₁ := ((bcEmb (F' := F') E).commutes E'.a₁).symm
    have c2 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₂ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₂ := ((bcEmb (F' := F') E).commutes E'.a₂).symm
    have c3 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₃ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₃ := ((bcEmb (F' := F') E).commutes E'.a₃).symm
    have c4 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₄ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₄ := ((bcEmb (F' := F') E).commutes E'.a₄).symm
    refine (omegaAt_some_eq (E'.baseChange F') _ ?_ ?_).symm
    · rw [c1, c3, ← bcDiff_D, ← s, bcDiff_smul]
      simp only [map_add (f := _), map_mul, map_ofNat]
    · rw [c1, c2, c4, ← bcDiff_D, ← t, bcDiff_smul]
      simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat]

variable (E) in
theorem bcDiff_invariantDifferential :
    bcDiff (F' := F') E (invariantDifferential E) = invariantDifferential (E.baseChange F') := by
  rw [invariantDifferential, bcDiff_omegaAt, map_bcEmb_genericPoint]
  rfl

variable [E'.IsElliptic]

theorem bcDiff_isogenyPullback (φ : Isogeny E E') :
    bcDiff (F' := F') E (isogenyPullback φ (invariantDifferential E')) =
      isogenyPullback (isogBaseChange (F' := F') φ) (invariantDifferential (E'.baseChange F')) := by
  rw [isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential, bcDiff_omegaAt]
  rfl

theorem isogCoeff_isogBaseChange (φ : Isogeny E E') :
    isogCoeff (isogBaseChange (F' := F') φ) = bcEmb (F' := F') E (isogCoeff φ) := by
  refine invCoeff_eq (E.baseChange F') ?_
  rw [← bcDiff_invariantDifferential, ← bcDiff_smul, ← isogenyPullback_invariantDifferential_eq_smul,
    bcDiff_isogenyPullback, isogenyPullback_invariantDifferential]

end Diff
end

section
open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in
theorem D_comap_mem_span (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    D F E.toAffine.FunctionField (φ.comap f) ∈
      Submodule.span E.toAffine.FunctionField {isogenyPullback φ (invariantDifferential E')} := by
  rw [← isogenyPullback_D, ← invCoeff_smul E' (D F _ f), isogenyPullback_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem span_isogenyPullback_eq_top (φ : Isogeny E E') (hφ : φ.IsSeparable) :
    Submodule.span E.toAffine.FunctionField {isogenyPullback φ (invariantDifferential E')} = ⊤ := by
  set M := φ.comap.fieldRange
  set K := E.toAffine.FunctionField
  have : Algebra.IsSeparable M K := hφ
  have : Algebra.FormallyUnramified M K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map F M K ω).mp (Subsingleton.elim _ _)
  induction z with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span M (Set.range (D F M)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      obtain ⟨f, hf⟩ := e.2
      change D F K (e : K) ∈ _
      rw [← hf]
      exact D_comap_mem_span φ f
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h

theorem isogenyPullback_ne_zero_of_isSeparable (φ : Isogeny E E') (hφ : φ.IsSeparable) :
    isogenyPullback φ (invariantDifferential E') ≠ 0 := by
  intro h0
  have htop := span_isogenyPullback_eq_top φ hφ
  rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have hmem : invariantDifferential E ∈ (⊥ : Submodule E.toAffine.FunctionField _) := by
    rw [htop]; trivial
  exact invariantDifferential_ne_zero E ((Submodule.mem_bot _).mp hmem)

theorem isSeparable_of_isogenyPullback_ne_zero (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') ≠ 0) : φ.IsSeparable := by
  set M := φ.comap.fieldRange
  set K := E.toAffine.FunctionField
  have hc : isogCoeff φ ≠ 0 := by
    intro h; apply hφ; rw [isogenyPullback_invariantDifferential_eq_smul, h, zero_smul]
  have htop : Submodule.span K {isogenyPullback φ (invariantDifferential E')} = ⊤ := by
    rw [isogenyPullback_invariantDifferential_eq_smul,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]
    exact span_invariantDifferential E
  have hx : φ.comap (genX E') ∈ M := ⟨genX E', rfl⟩
  have hzero : KaehlerDifferential.map F M K K (isogenyPullback φ (invariantDifferential E')) = 0 := by
    rw [invariantDifferential_eq, isogenyPullback_smul, isogenyPullback_D, map_smul, map_D]
    have : D M K (algebraMap K K (φ.comap (genX E'))) = D M K (algebraMap M K ⟨_, hx⟩) := rfl
    rw [this, Derivation.map_algebraMap, smul_zero]
  have hsub : Subsingleton Ω[K⁄M] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective F M K ω'
    have hω : ω ∈ Submodule.span K {isogenyPullback φ (invariantDifferential E')} := by
      rw [htop]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    rw [map_smul, hzero, smul_zero]
  have : Algebra.FormallyUnramified M K := ⟨hsub⟩
  have : FiniteDimensional M K := φ.finiteDimensional
  have : Algebra.EssFiniteType M K := inferInstance
  exact Algebra.FormallyUnramified.isSeparable M K

theorem isSeparable_iff_isogenyPullback_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogenyPullback φ (invariantDifferential E') ≠ 0 :=
  ⟨isogenyPullback_ne_zero_of_isSeparable φ, isSeparable_of_isogenyPullback_ne_zero φ⟩

theorem isSeparable_iff_isogCoeff_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogCoeff φ ≠ 0 := by
  rw [isSeparable_iff_isogenyPullback_ne_zero, isogenyPullback_invariantDifferential_eq_smul]
  exact ⟨fun h h0 => h (by rw [h0, zero_smul]),
    fun h h0 => h ((smul_eq_zero.mp h0).resolve_right (invariantDifferential_ne_zero E))⟩
end

section
open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

variable {F : Type u} [Field F]

section Const

variable [DecidableEq F] (E : WeierstrassCurve F) {L : Type*} [Field L] [Algebra F L] [DecidableEq L]

theorem omegaAt_constMap (R : E.toAffine.Point) : omegaAt E (constMap E L R) = 0 := by
  rcases R with _ | ⟨x, y, h⟩
  · exact omegaAt_zero E
  · refine omegaAt_some_eq E _ ?_ ?_ <;> rw [smul_zero] <;> exact (D_coeff _).symm

end Const

section Points

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem infinite_points [IsAlgClosed F] : Infinite E.toAffine.Point := by
  have key : ∀ x : F, ∃ y : F, E.toAffine.Equation x y := by
    intro x
    set q : F[X] := X ^ 2 + C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
    have hq : q.degree = 2 := by simp only [q]; compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; decide)
    refine ⟨y, ?_⟩
    rw [equation_iff]
    simp only [q, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
    linear_combination hy
  choose y hy using key
  refine Infinite.of_injective
    (fun x => (Point.some x (y x) (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (hy x)) :
      E.toAffine.Point)) ?_
  intro a b h
  simp only [Point.some.injEq] at h
  exact h.1

end Points

section AlgClosed

variable [IsAlgClosed F] [DecidableEq F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem translate_isogCoeff (φ : Isogeny E E') (R : E.toAffine.Point) :
    translate E R (isogCoeff φ) = isogCoeff φ := by
  have h1 := isogenyPullback_invariantDifferential_eq_smul φ
  rw [isogenyPullback_invariantDifferential] at h1
  have h2 := congrArg (kpush (translate E R)) h1
  rw [kpush_omegaAt, Isogeny.map_translate, omegaAt_add, omegaAt_constMap, add_zero, h1,
    kpush_smul, invariantDifferential, kpush_omegaAt, map_translate_genericPoint, omegaAt_add] at h2
  have h3 : omegaAt E (constPoint E R) = 0 := omegaAt_constMap E R
  rw [h3, add_zero] at h2
  exact (smul_left_injective _ (invariantDifferential_ne_zero E) h2).symm

theorem exists_isogCoeff_eq_algebraMap (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  set K := E.toAffine.FunctionField
  set c := isogCoeff φ
  by_contra hne
  have hc : Transcendental F c := fun halg => hne (exists_algebraMap_eq_of_isAlgebraic' halg)
  have : FiniteDimensional F⟮c⟯ K := finiteDimensional_adjoin_of_transcendental E hc
  have hfix : ∀ R : E.toAffine.Point, ∀ z ∈ F⟮c⟯, translate E R z = z := by
    intro R z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact translate_isogCoeff φ R
    | algebraMap x => exact (translate E R).commutes x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  let T : E.toAffine.Point → (K →ₐ[F⟮c⟯] K) := fun R =>
    { (translate E R).toRingHom with
      commutes' := fun r => hfix R r r.2 }
  have hT : Function.Injective T := by
    intro R S h
    exact translate_inj E (AlgHom.ext fun f => DFunLike.congr_fun h f)
  have hfin : Finite E.toAffine.Point := Finite.of_injective T hT
  exact (not_finite_iff_infinite.mpr (infinite_points E)) hfin

noncomputable def isogConst (φ : Isogeny E E') : F :=
  (exists_isogCoeff_eq_algebraMap φ).choose

theorem algebraMap_isogConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (isogConst φ) = isogCoeff φ :=
  (exists_isogCoeff_eq_algebraMap φ).choose_spec

theorem isSeparable_iff_isogConst_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogConst φ ≠ 0 := by
  rw [isSeparable_iff_isogCoeff_ne_zero, ← algebraMap_isogConst, ne_eq, ne_eq,
    map_eq_zero_iff _ (algebraMap F E.toAffine.FunctionField).injective]

theorem exists_homCoeff_eq_algebraMap (Q : isogHom E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = homCoeff E E' Q := by
  by_cases hQ : Q = 0
  · exact ⟨0, by rw [hQ, map_zero, map_zero]⟩
  · exact exists_isogCoeff_eq_algebraMap (isogOfHom Q hQ)

variable (E E') in
noncomputable def homConst : isogHom E E' →+ F where
  toFun Q := (exists_homCoeff_eq_algebraMap Q).choose
  map_zero' := (algebraMap F E.toAffine.FunctionField).injective (by
    rw [(exists_homCoeff_eq_algebraMap (0 : isogHom E E')).choose_spec, map_zero, map_zero])
  map_add' Q₁ Q₂ := (algebraMap F E.toAffine.FunctionField).injective (by
    rw [(exists_homCoeff_eq_algebraMap (Q₁ + Q₂)).choose_spec, map_add (f := _), map_add (f := _),
      (exists_homCoeff_eq_algebraMap Q₁).choose_spec, (exists_homCoeff_eq_algebraMap Q₂).choose_spec])

theorem algebraMap_homConst (Q : isogHom E E') :
    algebraMap F E.toAffine.FunctionField (homConst E E' Q) = homCoeff E E' Q :=
  (exists_homCoeff_eq_algebraMap Q).choose_spec

theorem omegaAt_eq_homConst_smul (Q : isogHom E E') :
    omegaAt E' Q.1 = homConst E E' Q • invariantDifferential E := by
  rw [← homCoeff_smul, ← algebraMap_homConst, algebraMap_smul]

end AlgClosed
end

section
open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section Descent

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem exists_eq_add_mul_genY (c : E.toAffine.FunctionField) :
    ∃ r s : E.toAffine.FunctionField, r ∈ F⟮genX E⟯ ∧ s ∈ F⟮genX E⟯ ∧ c = r + s * genY E := by
  set F₁ := F⟮genX E⟯
  have hfin : FiniteDimensional F₁ E.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_genX E]; norm_num)
  have hint : IsIntegral F₁ (genY E) := Algebra.IsIntegral.isIntegral _
  have htop : F₁⟮genY E⟯ = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY E
  have hdeg : (minpoly F₁ (genY E)).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top',
      finrank_adjoin_genX E]
  have hc : c ∈ (F₁⟮genY E⟯).toSubalgebra := by rw [htop]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨p, rfl⟩ := hc
  have hm1 : minpoly F₁ (genY E) ≠ 1 := fun h => by rw [h, natDegree_one] at hdeg; omega
  have hq : (p %ₘ minpoly F₁ (genY E)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p (minpoly.monic hint) hm1
    omega
  have hval : aeval (genY E) p = aeval (genY E) (p %ₘ minpoly F₁ (genY E)) :=
    (aeval_modByMonic_eq_self_of_root (minpoly.aeval F₁ (genY E))).symm
  obtain ⟨q, hqdef⟩ : ∃ q, q = p %ₘ minpoly F₁ (genY E) := ⟨_, rfl⟩
  rw [← hqdef] at hq hval
  refine ⟨(q.coeff 0 : E.toAffine.FunctionField), (q.coeff 1 : E.toAffine.FunctionField),
    (q.coeff 0).2, (q.coeff 1).2, ?_⟩
  change aeval (genY E) p = _
  rw [hval, eq_X_add_C_of_natDegree_le_one hq]
  simp only [map_add (f := _), map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul_X, coeff_C]
  simp
  ring

variable {F' : Type u} [Field F'] [Algebra F F']

theorem exists_algebraMap_eq_of_bcEmb {c : E.toAffine.FunctionField} {a : F'}
    (h : bcEmb (F' := F') E c = algebraMap F' (E.baseChange F').toAffine.FunctionField a) :
    ∃ a₀ : F, algebraMap F E.toAffine.FunctionField a₀ = c := by
  set K' := (E.baseChange F').toAffine.FunctionField
  have hinj : Function.Injective (bcEmb (F' := F') E) := (bcEmb (F' := F') E).toRingHom.injective
  have hmap : ∀ w ∈ F⟮genX E⟯, bcEmb (F' := F') E w ∈ F'⟮genX (E.baseChange F')⟯ :=
    fun _ hw => (IntermediateField.adjoin_le_iff
      (T := ((F'⟮genX (E.baseChange F')⟯).restrictScalars F).comap (bcEmb (F' := F') E))).2
      (Set.singleton_subset_iff.2 <| by
        simpa [bcEmb_genX] using mem_adjoin_simple_self F' _) hw
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add (f := _), map_mul, bcEmb_genY] at h
  have hs0 : bcEmb (F' := F') E s = 0 := by
    by_contra hne
    apply genY_not_mem (E.baseChange F')
    have e : genY (E.baseChange F') =
        (algebraMap F' K' a - bcEmb (F' := F') E r) / bcEmb (F' := F') E s := by
      rw [eq_div_iff hne]; linear_combination h
    rw [e]
    exact div_mem (sub_mem (IntermediateField.algebraMap_mem _ a) (hmap r hr)) (hmap s hs)
  have hs00 : s = 0 := hinj (by rw [hs0, map_zero])
  rw [hs0, zero_mul, add_zero] at h
  rw [hs00, zero_mul, add_zero]
  obtain ⟨p, q, rfl⟩ := (mem_adjoin_simple_iff F r).mp hr
  by_cases hq0 : aeval (genX E) q = 0
  · exact ⟨0, by rw [hq0, div_zero, map_zero]⟩
  have hq : q ≠ 0 := fun h0 => hq0 (by rw [h0, map_zero])
  have hq0' : aeval (genX (E.baseChange F')) q ≠ 0 := by
    rw [← bcEmb_genX, aeval_algHom_apply]
    exact fun h0 => hq0 (hinj (by rw [h0, map_zero]))
  rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, bcEmb_genX, div_eq_iff hq0'] at h
  have key : aeval (genX (E.baseChange F'))
      (p.map (algebraMap F F') - C a * q.map (algebraMap F F')) = 0 := by
    rw [map_sub, map_mul, aeval_C, aeval_map_algebraMap, aeval_map_algebraMap]
    linear_combination h
  rw [aeval_genX_eq_zero_iff] at key
  have hcoeff : ∀ j, algebraMap F F' (p.coeff j) = a * algebraMap F F' (q.coeff j) := by
    intro j
    have := congrArg (fun (f : F'[X]) => f.coeff j) key
    simp only [coeff_sub, coeff_map, coeff_C_mul, coeff_zero] at this
    linear_combination this
  have hqi : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, a₀ = p.coeff q.natDegree / q.coeff q.natDegree := ⟨_, rfl⟩
  have ha : a = algebraMap F F' a₀ := by
    rw [ha₀, map_div₀, hcoeff, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr hqi)]
  have hp : p = C a₀ * q := by
    ext j
    apply (algebraMap F F').injective
    rw [coeff_C_mul, map_mul, hcoeff j, ← ha]
  refine ⟨a₀, ?_⟩
  rw [hp, map_mul, aeval_C, mul_div_cancel_right₀ _ hq0]

end Descent

section Constant

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem exists_algebraMap_eq_isogCoeff (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  classical
  obtain ⟨b, hb⟩ := exists_isogCoeff_eq_algebraMap
    (isogBaseChange (F' := AlgebraicClosure F) φ)
  rw [isogCoeff_isogBaseChange] at hb
  exact exists_algebraMap_eq_of_bcEmb E hb.symm

noncomputable def invConst (φ : Isogeny E E') : F :=
  (exists_algebraMap_eq_isogCoeff φ).choose

theorem algebraMap_invConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (invConst φ) = isogCoeff φ :=
  (exists_algebraMap_eq_isogCoeff φ).choose_spec

theorem isogenyPullback_eq_invConst_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = invConst φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_invConst, algebraMap_smul]

variable (E) in
theorem invConst_mulIsogeny (n : ℤ) (hn : n ≠ 0) : invConst (mulIsogeny E n hn) = n :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_mulIsogeny, map_intCast])

theorem invConst_isogBaseChange {F' : Type u} [Field F'] [Algebra F F'] [DecidableEq F']
    (φ : Isogeny E E') :
    invConst (isogBaseChange (F' := F') φ) = algebraMap F F' (invConst φ) :=
  (algebraMap F' (E.baseChange F').toAffine.FunctionField).injective (by
    rw [algebraMap_invConst, isogCoeff_isogBaseChange, ← algebraMap_invConst, AlgHom.commutes,
      IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField])

end Constant
end

section
open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section FF

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F') (E : WeierstrassCurve F)

noncomputable def ffMap : E.toAffine.FunctionField →+* (E.map σ).toAffine.FunctionField :=
  letI := σ.toAlgebra
  (bcEmb (F' := F') E).toRingHom

theorem ffMap_genX : ffMap σ E (genX E) = genX (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genX (F' := F') E

theorem ffMap_genY : ffMap σ E (genY E) = genY (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genY (F' := F') E

theorem ffMap_algebraMap (a : F) :
    ffMap σ E (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F' (E.map σ).toAffine.FunctionField (σ a) := by
  let _ := σ.toAlgebra
  exact (bcEmb (F' := F') E).commutes a

theorem ringHom_ext_functionField {W : WeierstrassCurve F} {L : Type*} [Field L]
    {f g : W.toAffine.FunctionField →+* L}
    (hc : ∀ a : F, f (algebraMap F _ a) = g (algebraMap F _ a)) (hx : f (genX W) = g (genX W))
    (hy : f (genY W) = g (genY W)) : f = g := by
  let _ : Algebra F L := (f.comp (algebraMap F W.toAffine.FunctionField)).toAlgebra
  let f' : W.toAffine.FunctionField →ₐ[F] L := { f with commutes' := fun a => rfl }
  let g' : W.toAffine.FunctionField →ₐ[F] L := { g with commutes' := fun a => (hc a).symm }
  have e : f' = g' := algHom_ext_gen W hx hy
  ext z
  exact DFunLike.congr_fun e z

noncomputable def ffCongr {C D : WeierstrassCurve F'} (h : C = D) :
    C.toAffine.FunctionField ≃+* D.toAffine.FunctionField := by
  subst h; exact RingEquiv.refl _

theorem ffCongr_genX {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genX C) = genX D := by
  subst h; rfl

theorem ffCongr_genY {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genY C) = genY D := by
  subst h; rfl

theorem ffCongr_algebraMap {C D : WeierstrassCurve F'} (h : C = D) (a : F') :
    ffCongr h (algebraMap F' C.toAffine.FunctionField a) = algebraMap F' D.toAffine.FunctionField a := by
  subst h; rfl

end FF

section Map

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

omit [E.IsElliptic] [E'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.val_eq (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  rcases φ with ⟨Q, ⟨x, y, h, rfl, hx⟩, hr⟩
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.ext_xy {φ ψ : Isogeny E E'} (hx : φ.x = ψ.x) (hy : φ.y = ψ.y) : φ = ψ := by
  apply Isogeny.ext'
  rw [φ.val_eq, ψ.val_eq]
  simp only [Point.some.injEq]
  exact ⟨hx, hy⟩

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.map (φ : Isogeny E E') : Isogeny (E.map σ) (E'.map σ) :=
  letI := σ.toAlgebra
  letI := Classical.decEq F'
  isogBaseChange (F' := F') φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_x (φ : Isogeny E E') : (φ.map σ).x = ffMap σ E φ.x := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show xOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_y (φ : Isogeny E E') : (φ.map σ).y = ffMap σ E φ.y := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show yOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comap_map (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    (φ.map σ).comap (ffMap σ E' f) = ffMap σ E (φ.comap f) := by
  have e : (φ.map σ).comap.toRingHom.comp (ffMap σ E') = (ffMap σ E).comp φ.comap.toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_algebraMap,
        AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        Isogeny.comap_genX, Isogeny.map_x]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        Isogeny.comap_genY, Isogeny.map_y]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_alt (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).x = φ.comap ψ.x := by
  rw [Isogeny.x, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_y (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).y = φ.comap ψ.y := by
  rw [Isogeny.y, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).map σ = (ψ.map σ).comp (φ.map σ) := by
  apply Isogeny.ext_xy
  · rw [Isogeny.map_x, Isogeny.comp_alt, Isogeny.comp_alt, Isogeny.map_x, Isogeny.comap_map]
  · rw [Isogeny.map_y, Isogeny.comp_y, Isogeny.comp_y, Isogeny.map_y, Isogeny.comap_map]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).map σ = mulIsogeny (E.map σ) n hn := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := F') E) (n • genericPoint E) =
    n • genericPoint (E.baseChange F')
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

end Map

section Congr

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {C D C' D' C'' D'' : WeierstrassCurve F'} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
  [D'.IsElliptic] [C''.IsElliptic] [D''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : Isogeny D D' := by
  subst hC hC'; exact φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_alt (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').x = ffCongr hC φ.x := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_y (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').y = ffCongr hC φ.y := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_rfl (φ : Isogeny C C') : φ.congr rfl rfl = φ :=
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.degree_congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : (φ.congr hC hC').degree = φ.degree := by
  subst hC hC'; rfl

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : Isogeny D D' :=
  (φ.map σ).congr hE hE'

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_alt (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').x = ffCongr hE (ffMap σ E φ.x) := by
  rw [Isogeny.mapOf, Isogeny.congr_alt, Isogeny.map_x]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_y (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').y = ffCongr hE (ffMap σ E φ.y) := by
  rw [Isogeny.mapOf, Isogeny.congr_y, Isogeny.map_y]

end Congr
end

section
open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section Compositum

variable {k M : Type u} [Field k] [Field M] (σ : k →+* M) (L : Type u) [Field L] [Algebra k L]

theorem exists_free_compositum :
    ∃ (L' : Type u) (_ : Field L') (ι : L →+* L') (j : M →+* L'),
      ι.comp (algebraMap k L) = j.comp σ ∧
        ∀ u : L, Transcendental k u → Transcendental j.fieldRange (ι u) := by
  classical
  letI : Algebra k M := σ.toAlgebra
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k M
  let A := MvPolynomial B L
  let L₁ := FractionRing A
  let L' := AlgebraicClosure L₁
  let toL' : A →ₐ[k] L' := IsScalarTower.toAlgHom k A L'
  have htoL' : Function.Injective toL' := by
    have h1 : Function.Injective (algebraMap A L₁) := IsFractionRing.injective A L₁
    have h2 : Function.Injective (algebraMap L₁ L') := (algebraMap L₁ L').injective
    have : (toL' : A → L') = algebraMap L₁ L' ∘ algebraMap A L₁ := by
      ext a
      simp [toL', IsScalarTower.algebraMap_apply A L₁ L']
    rw [this]
    exact h2.comp h1

  let R := Algebra.adjoin k (Set.range ((↑) : B → M))
  let e := hB.1.aevalEquiv
  let x : B → L' := fun b => toL' (MvPolynomial.X b)
  let f₀ : R →ₐ[k] L' :=
    toL'.comp ((MvPolynomial.mapAlgHom (Algebra.ofId k L)).comp e.symm.toAlgHom)
  have hf₀inj : Function.Injective f₀ := by
    refine htoL'.comp ((MvPolynomial.map_injective _ (algebraMap k L).injective).comp ?_)
    exact e.symm.injective
  have hf₀x : ∀ p : MvPolynomial B k, f₀ (e p) = MvPolynomial.aeval x p := by
    intro p
    have : toL'.comp (MvPolynomial.mapAlgHom (Algebra.ofId k L)) = MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro b
      rw [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X, MvPolynomial.aeval_X]
    show toL' (MvPolynomial.mapAlgHom (Algebra.ofId k L) (e.symm (e p))) = _
    rw [e.symm_apply_apply]
    exact DFunLike.congr_fun this p
  letI : Algebra R L' := f₀.toRingHom.toAlgebra
  haveI : IsScalarTower k R L' := IsScalarTower.of_algebraMap_eq (fun a => (f₀.commutes a).symm)
  haveI : Module.IsTorsionFree R L' := Module.isTorsionFree_iff_algebraMap_injective.mpr hf₀inj
  haveI : Algebra.IsAlgebraic R M := hB.isAlgebraic
  let j₀ : M →ₐ[R] L' := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let j : M →ₐ[k] L' := j₀.restrictScalars k
  let ι : L →ₐ[k] L' := IsScalarTower.toAlgHom k L L'
  refine ⟨L', inferInstance, ι.toRingHom, j.toRingHom, ?_, fun u hu => ?_⟩
  · ext a
    exact (ι.commutes a).trans (j.commutes a).symm

  have hjR : ∀ r : R, j (r : M) = f₀ r := fun r => j₀.commutes r
  have hjb : ∀ b : B, j (b : M) = x b := by
    intro b
    have hr : (b : M) = ((e (MvPolynomial.X b) : R) : M) := by
      rw [show ((e (MvPolynomial.X b) : R) : M) = MvPolynomial.aeval ((↑) : B → M) (MvPolynomial.X b)
        from hB.1.algebraMap_aevalEquiv _, MvPolynomial.aeval_X]
    rw [hr, hjR, hf₀x, MvPolynomial.aeval_X]
  have hind : AlgebraicIndependent k (Sum.elim (fun _ : Unit => ι u) x) := by
    have h1 := AlgebraicIndependent.sumElim_comp (R := k) (S := L) (A := A)
      (x := fun _ : Unit => u) (algebraicIndependent_unique_type_iff.mpr hu)
      (MvPolynomial.algebraicIndependent_X B L)
    have h2 := h1.map' htoL'
    refine (algebraicIndependent_equiv' (Equiv.sumComm Unit B) ?_).mpr h2
    funext z
    rcases z with _ | b
    · simp [ι, toL', IsScalarTower.algebraMap_apply L A L']
    · rfl
  obtain ⟨-, hu'⟩ := AlgebraicIndependent.sumElim_iff.mp hind
  have htr : Transcendental (Algebra.adjoin k (Set.range x)) (ι u) :=
    algebraicIndependent_unique_type_iff.mp hu'
  intro halg
  set R' := Algebra.adjoin k (Set.range x)
  set K₁ := j.toRingHom.fieldRange
  have hR'K : R'.toSubring ≤ K₁.toSubring := by
    show (Algebra.adjoin k (Set.range x) : Set L') ⊆ K₁
    have hle : Algebra.adjoin k (Set.range x) ≤ j.range :=
      Algebra.adjoin_le (by rintro _ ⟨b, rfl⟩; exact ⟨b, hjb b⟩)
    intro z hz
    obtain ⟨m, hm⟩ := hle hz
    exact ⟨m, hm⟩
  letI : Algebra R' K₁ := (Subring.inclusion hR'K).toAlgebra
  haveI : IsScalarTower R' K₁ L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmem : ∀ r : R, f₀ r ∈ R' := by
    intro r
    obtain ⟨p, rfl⟩ := e.surjective r
    rw [hf₀x]
    show MvPolynomial.aeval x p ∈ Algebra.adjoin k (Set.range x)
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨p, rfl⟩
  let f : R →+* R' := f₀.toRingHom.codRestrict R' hmem
  let g : M →+* K₁ := j.toRingHom.rangeRestrictField
  have hf : Function.Injective f := RingHom.injective_codRestrict.mpr hf₀inj
  have hcomp : (algebraMap R' K₁).comp f = g.comp (algebraMap R M) := by
    ext r
    exact (hjR r).symm
  haveI : Algebra.IsAlgebraic R' K₁ := by
    refine ⟨fun z => ?_⟩
    obtain ⟨m, hm⟩ := z.2
    have hz : g m = z := Subtype.ext hm
    rw [← hz]
    exact (Algebra.IsAlgebraic.isAlgebraic m).ringHom_of_comp_eq f g hf hcomp
  exact htr (halg.restrictScalars R')

end Compositum

section Descent

theorem point_some_congr {K : Type*} [Field K] {W : WeierstrassCurve K} {x y x' y' : K}
    {h : W.toAffine.Nonsingular x y} {h' : W.toAffine.Nonsingular x' y'} (hx : x = x')
    (hy : y = y') : (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx hy
  rfl

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem respectsAdd_of_map (ψ : Isogeny (E.map σ) (E'.map σ))
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : Q ≠ 0)
    (hx : ffMap σ E (xOf _ Q) = ψ.x) (hy : ffMap σ E (yOf _ Q) = ψ.y) : RespectsAdd E E' Q := by
  classical
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  obtain ⟨L', _, ι, j, hcomm, htr⟩ := exists_free_compositum σ L
  letI : Algebra F' L' := j.toAlgebra
  letI : Algebra F L' := ((algebraMap F' L').comp σ).toAlgebra
  let ιA : L →ₐ[F] L' := { ι with commutes' := fun a => DFunLike.congr_fun hcomm a }
  let pm : (E.baseChange L).toAffine.Point →+ ((E.map σ).baseChange L').toAffine.Point :=
    Point.map (W' := E) ιA
  have hgen : ∀ P : (E.baseChange L).toAffine.Point, IsGenPt E P →
      IsGenPt (E.map σ) (pm P) := by
    intro P hP
    cases P with
    | zero => exact hP.elim
    | some u v h =>
      show Transcendental F' (ι u)
      intro halg
      exact htr u hP (halg.ringHom_of_comp_eq j.rangeRestrictField (RingHom.id L')
        j.rangeRestrictField.injective rfl)
  have happ : ∀ {X Y : ((E.map σ).baseChange L').toAffine.Point} (h : X = Y)
      (hX : IsGenPt (E.map σ) X) (hY : IsGenPt (E.map σ) Y), ψ.app X hX = ψ.app Y hY := by
    intro X Y h hX hY
    subst h
    rfl
  let pm' : (E'.baseChange L').toAffine.Point →+ ((E'.map σ).baseChange L').toAffine.Point :=
    AddMonoidHom.id _
  have key : ∀ (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P),
      pm' (Point.map ιA (Point.map (genEval E P hP) Q)) = ψ.app (pm P) (hgen P hP) := by
    intro P hP
    rw [Point.map_map, ← genEval_map]
    have hg : (genEval E (Point.map ιA P) (isGenPt_map E ιA hP)).toRingHom =
        (genEval (E.map σ) (pm P) (hgen P hP)).toRingHom.comp (ffMap σ E) := by
      apply ringHom_ext_functionField
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply, ffMap_algebraMap,
          AlgHom.commutes]
        rfl
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply, ffMap_genX,
          genEval_genX]
        rfl
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply, ffMap_genY,
          genEval_genY]
        rfl
    rw [Isogeny.app, ψ.val_eq]
    cases Q with
    | zero => exact absurd rfl hQ
    | some a b hab =>
      have hx' : ffMap σ E a = ψ.x := hx
      have hy' : ffMap σ E b = ψ.y := hy
      have ea : genEval E (Point.map ιA P) (isGenPt_map E ιA hP) a =
          genEval (E.map σ) (pm P) (hgen P hP) ψ.x := by
        rw [← hx']; exact DFunLike.congr_fun hg a
      have eb : genEval E (Point.map ιA P) (isGenPt_map E ιA hP) b =
          genEval (E.map σ) (pm P) (hgen P hP) ψ.y := by
        rw [← hy']; exact DFunLike.congr_fun hg b
      rw [Point.map_some]
      show (Point.some _ _ _ : ((E'.map σ).baseChange L').toAffine.Point) = Point.some _ _ _
      exact point_some_congr ea eb
  have hpm' : Function.Injective pm' := fun _ _ h => h
  apply Point.map_injective (W' := E') ιA
  apply hpm'
  rw [map_add (f := _), map_add (f := _), key _ h₃, key _ h₁, key _ h₂]
  have h₃' : IsGenPt (E.map σ) (pm P₁ + pm P₂) := by
    rw [← map_add (f := _)]; exact hgen _ h₃
  rw [← ψ.app_add (hgen P₁ h₁) (hgen P₂ h₂) h₃']
  exact happ (map_add _ _ _) _ _

omit [E.IsElliptic] in
theorem transcendental_of_ffMap {z : E.toAffine.FunctionField}
    (h : Transcendental F' (ffMap σ E z)) : Transcendental F z := by
  intro halg
  refine h (halg.ringHom_of_comp_eq σ (ffMap σ E) σ.injective ?_)
  ext a
  exact (ffMap_algebraMap σ E a).symm

omit [E.IsElliptic] [E'.IsElliptic] in
theorem baseChange_map_ffMap :
    (E'.baseChange E.toAffine.FunctionField).map (ffMap σ E) =
      (E'.map σ).baseChange (E.map σ).toAffine.FunctionField := by
  have hc : (ffMap σ E).comp (algebraMap F E.toAffine.FunctionField) =
      (algebraMap F' (E.map σ).toAffine.FunctionField).comp σ := RingHom.ext (ffMap_algebraMap σ E)
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    WeierstrassCurve.map_map, hc]

omit [E.IsElliptic] [E'.IsElliptic] in
theorem nonsingular_of_ffMap {x y : E.toAffine.FunctionField}
    (h : ((E'.map σ).baseChange (E.map σ).toAffine.FunctionField).toAffine.Nonsingular
      (ffMap σ E x) (ffMap σ E y)) :
    (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y := by
  have h' : ((E'.baseChange E.toAffine.FunctionField).map (ffMap σ E)).toAffine.Nonsingular
      (ffMap σ E x) (ffMap σ E y) := by
    rw [baseChange_map_ffMap]; exact h
  exact (WeierstrassCurve.Affine.map_nonsingular (W := (E'.baseChange _).toAffine)
    (ffMap σ E).injective x y).mp h'

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.ofMap (ψ : Isogeny (E.map σ) (E'.map σ))
    (x y : E.toAffine.FunctionField) (hx : ffMap σ E x = ψ.x) (hy : ffMap σ E y = ψ.y) :
    Isogeny E E' :=
  ⟨.some x y (nonsingular_of_ffMap σ (hx ▸ hy ▸ ψ.nonsingular)),
    (isIsogeny_iff _).mpr ⟨transcendental_of_ffMap σ (hx ▸ ψ.transcendental_alt),
      respectsAdd_of_map σ ψ (by simp) hx hy⟩⟩

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_ofMap (ψ : Isogeny (E.map σ) (E'.map σ))
    (x y : E.toAffine.FunctionField) (hx : ffMap σ E x = ψ.x) (hy : ffMap σ E y = ψ.y) :
    (Isogeny.ofMap σ ψ x y hx hy).map σ = ψ :=
  Isogeny.ext_xy (by rw [Isogeny.map_x]; exact hx) (by rw [Isogeny.map_y]; exact hy)

end Descent

section Bridge

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F'] (E : WeierstrassCurve F)
  [E.IsElliptic]

theorem ffMap_algebraMap_eq_bcEmb (f : E.toAffine.FunctionField) :
    ffMap (algebraMap F F') E f = bcEmb (F' := F') E f := by
  have e : ffMap (algebraMap F F') E = (bcEmb (F' := F') E).toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      rw [ffMap_algebraMap]
      show _ = bcEmb (F' := F') E (algebraMap F _ a)
      rw [AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField a).symm
    · rw [ffMap_genX]; exact (bcEmb_genX E).symm
    · rw [ffMap_genY]; exact (bcEmb_genY E).symm
  exact DFunLike.congr_fun e f

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic] [DecidableEq F']

theorem isogBaseChange_alt (φ : Isogeny E E') :
    (isogBaseChange (F' := F') φ).x = bcEmb (F' := F') E φ.x := by
  show xOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem isogBaseChange_y (φ : Isogeny E E') :
    (isogBaseChange (F' := F') φ).y = bcEmb (F' := F') E φ.y := by
  show yOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

end Bridge
end

section
open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)
open scoped Polynomial.Bivariate

universe u

section Neg

variable {F : Type u} [Field F] (E : WeierstrassCurve F)

theorem xOf_neg {K : Type*} [Field K] {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xOf W (-P) = xOf W P := GroundTheory.Arith.Abelian.xOf_neg W P

theorem xOf_map {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L] [DecidableEq K]
    [DecidableEq L] (f : K →ₐ[F] L) (P : (E.baseChange K).toAffine.Point) :
    xOf _ (Point.map f P) = f (xOf _ P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

end Neg

section Even

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_neg_genericPoint : IsGenPt E (-genericPoint E) :=
  isGenPt_neg (show IsGenPt E (genericPoint E) from transcendental_genX E)

variable (E) in
noncomputable def negFF : E.toAffine.FunctionField →ₐ[F] E.toAffine.FunctionField :=
  genEval E (-genericPoint E) isGenPt_neg_genericPoint

theorem negFF_genX : negFF E (genX E) = genX E := by
  rw [negFF, genEval_genX, xOf_neg]
  rfl

theorem negFF_genY :
    negFF E (genY E) = -genY E - algebraMap F _ E.a₁ * genX E - algebraMap F _ E.a₃ := by
  rw [negFF, genEval_genY]
  rfl

theorem negFF_of_mem {w : E.toAffine.FunctionField} (hw : w ∈ F⟮genX E⟯) : negFF E w = w := by
  induction hw using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx, negFF_genX]
  | algebraMap x => exact AlgHom.commutes _ x
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem mem_adjoin_genX_of_negFF {c : E.toAffine.FunctionField} (h : negFF E c = c) :
    c ∈ F⟮genX E⟯ := by
  obtain ⟨r, s, hr, hs, rfl⟩ := exists_eq_add_mul_genY E c
  rw [map_add (f := _), map_mul, negFF_of_mem hr, negFF_of_mem hs, negFF_genY] at h
  have hs0 : s = 0 := by
    have : s * ((2 : E.toAffine.FunctionField) * genY E + algebraMap F _ E.a₁ * genX E +
        algebraMap F _ E.a₃) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_right (_root_.GroundTheory.Global.genDen_ne_zero E)
  rw [hs0, zero_mul, add_zero]
  exact hr

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.negFF_alt (φ : Isogeny E E') : negFF E φ.x = φ.x := by
  have hG : IsGenPt E (genericPoint E) := transcendental_genX E
  have e := map_genEval_neg φ.respectsAdd hG
  have e2 : Point.map (genEval E (genericPoint E) hG) φ.1 = φ.1 := φ.app_genericPoint hG
  rw [e2] at e
  have := congrArg (xOf _) e
  rw [xOf_neg, xOf_map] at this
  exact this

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.x_mem_adjoin_genX (φ : Isogeny E E') :
    φ.x ∈ F⟮genX E⟯ :=
  mem_adjoin_genX_of_negFF φ.negFF_alt

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_ratEmb_eq_x (φ : Isogeny E E') :
    ∃ r : RatFunc F, ratEmb E r = φ.x := by
  have h := φ.x_mem_adjoin_genX
  rw [← fieldRange_ratEmb] at h
  exact h

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.degree_eq_max_natDegree (φ : Isogeny E E')
    {r : RatFunc F} (hr : ratEmb E r = φ.x) :
    φ.degree = max r.num.natDegree r.denom.natDegree := by
  set α := φ.comap
  set E1 : IntermediateField F E.toAffine.FunctionField := F⟮genX E⟯
  set M := α.fieldRange
  set E0 : IntermediateField F E.toAffine.FunctionField := F⟮φ.x⟯
  have hxE1 : φ.x ∈ E1 := φ.x_mem_adjoin_genX
  have hxM : φ.x ∈ M := ⟨genX E', φ.comap_genX⟩
  have h01 : E0 ≤ E1 := adjoin_simple_le_iff.mpr hxE1
  have h0M : E0 ≤ M := adjoin_simple_le_iff.mpr hxM
  have e1 : relfinrank E1 ⊤ = 2 := by rw [relfinrank_top_right, finrank_adjoin_genX]
  have e2 : relfinrank E0 M = 2 := by
    have hE0 : E0 = (F⟮genX E'⟯).map α := by
      rw [adjoin_map, Set.image_singleton, φ.comap_genX]
    have hM : M = (⊤ : IntermediateField F _).map α := (map_top_eq_fieldRange α).symm
    rw [hE0, hM, relfinrank_map_map, relfinrank_top_right, finrank_adjoin_genX]
  have e3 : relfinrank E0 E1 = max r.num.natDegree r.denom.natDegree := by
    have hE0 : E0 = (F⟮r⟯).map (ratEmb E) := by
      rw [adjoin_map, Set.image_singleton, hr]
    have hE1 : E1 = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E) := by
      rw [map_top_eq_fieldRange, fieldRange_ratEmb]
    rw [hE0, hE1, relfinrank_map_map, relfinrank_top_right, RatFunc.finrank_eq_max_natDegree]
  have t1 := relfinrank_mul_relfinrank h01 (le_top : E1 ≤ ⊤)
  have t2 := relfinrank_mul_relfinrank h0M (le_top : M ≤ ⊤)
  rw [e1, e3] at t1
  rw [e2, ← t1] at t2
  have hdeg : φ.degree = relfinrank M ⊤ := by rw [Isogeny.degree, relfinrank_top_right]
  rw [hdeg]
  omega

end Even

section RatFunc

variable {F : Type u} [Field F]

theorem num_denom_div_of_isCoprime {p q : F[X]} (hq : q.Monic) (h : IsCoprime p q) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).num = p ∧
      (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).denom = q := by
  set r := algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q
  have hq0 : q ≠ 0 := hq.ne_zero
  have hinj := RatFunc.algebraMap_injective F
  have hcross : r.num * q = p * r.denom := by
    have e : algebraMap F[X] (RatFunc F) r.num / algebraMap F[X] (RatFunc F) r.denom =
        algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q := RatFunc.num_div_denom r
    rw [div_eq_div_iff ((map_ne_zero_iff _ hinj).mpr r.denom_ne_zero)
      ((map_ne_zero_iff _ hinj).mpr hq0), ← map_mul, ← map_mul] at e
    exact hinj e
  have hd1 : q ∣ r.denom :=
    h.symm.dvd_of_dvd_mul_left ⟨r.num, by linear_combination -hcross⟩
  have hd2 : r.denom ∣ q :=
    r.isCoprime_num_denom.symm.dvd_of_dvd_mul_left ⟨p, by linear_combination hcross⟩
  have hden : r.denom = q :=
    Polynomial.eq_of_monic_of_associated r.monic_denom hq (associated_of_dvd_dvd hd2 hd1)
  refine ⟨?_, hden⟩
  rw [hden] at hcross
  exact mul_right_cancel₀ hq0 hcross

end RatFunc

section Degree

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in
theorem ffMap_aeval (p : F[X]) (z : E.toAffine.FunctionField) :
    ffMap σ E (aeval z p) = aeval (ffMap σ E z) (p.map σ) := by
  rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  simp [ffMap_algebraMap]

end Degree
end

section
open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section Conj

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

variable (E) in
theorem baseChange_map_algEquiv (g : Ω ≃ₐ[F] Ω) :
    (E.baseChange Ω).map (g : Ω →+* Ω) = E.baseChange Ω :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) E (g : Ω →ₐ[F] Ω)

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.conj (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    Isogeny (E.baseChange Ω) (E'.baseChange Ω) :=
  ψ.mapOf (g : Ω →+* Ω) (baseChange_map_algEquiv E g) (baseChange_map_algEquiv E' g)

variable (E) in
theorem ffCongr_ffMap_eq_galFF (g : Ω ≃ₐ[F] Ω) (f : (E.baseChange Ω).toAffine.FunctionField) :
    ffCongr (baseChange_map_algEquiv E g) (ffMap (g : Ω →+* Ω) (E.baseChange Ω) f) =
      galFF E g f := by
  have e : (ffCongr (baseChange_map_algEquiv E g)).toRingHom.comp
      (ffMap (g : Ω →+* Ω) (E.baseChange Ω)) = (galFF E g).toRingHom := by
    apply ringHom_ext_functionField
    · intro c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        ffMap_algebraMap, ffCongr_algebraMap, galFF_algebraMap]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        ffCongr_genX, galFF_genX]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        ffCongr_genY, galFF_genY]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_alt_bis (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : (ψ.conj g).x = galFF E g ψ.x := by
  rw [Isogeny.conj, Isogeny.mapOf_alt, ffCongr_ffMap_eq_galFF]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_y (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : (ψ.conj g).y = galFF E g ψ.y := by
  rw [Isogeny.conj, Isogeny.mapOf_y, ffCongr_ffMap_eq_galFF]

variable (E E') in
theorem map_galFF_curve' (g : Ω ≃ₐ[F] Ω) :
    ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).map
      (galFF E g : _ →+* _) =
      (E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField := by
  have e : ∀ a : F, galFF E g (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField
      (algebraMap F Ω a)) = algebraMap Ω _ (algebraMap F Ω a) := fun a => by
    rw [galFF_algebraMap, AlgEquiv.commutes]
  ext <;> exact e _

variable (E E') in
noncomputable def galPt (g : Ω ≃ₐ[F] Ω) :
    ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point →+
      ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point :=
  autPoint _ (galFF E g) (map_galFF_curve' E E' g)

theorem galPt_val (g : Ω ≃ₐ[F] Ω) (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    galPt E E' g ψ.1 = (ψ.conj g).1 := by
  rw [ψ.val_eq, galPt, autPoint_some, (ψ.conj g).val_eq]
  exact point_some_congr (ψ.conj_alt_bis g).symm (ψ.conj_y g).symm

theorem galPt_constMap [DecidableEq Ω] (g : Ω ≃ₐ[F] Ω) (c : (E'.baseChange Ω).toAffine.Point) :
    galPt E E' g (constMap (E'.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField c) =
      constMap (E'.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField
        (galPointsHom F Ω E' g c) := by
  cases c with
  | zero => rfl
  | some x y h =>
    show autPoint _ _ _ (Point.some _ _ _) = Point.some _ _ _
    rw [autPoint_some]
    exact point_some_congr (galFF_algebraMap E g x) (galFF_algebraMap E g y)

theorem galPt_map_translate [IsAlgClosed Ω] [DecidableEq Ω] (g : Ω ≃ₐ[F] Ω)
    (R : (E.baseChange Ω).toAffine.Point)
    (Q : ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) :
    galPt E E' g (Point.map (translate (E.baseChange Ω) R) Q) =
      Point.map (translate (E.baseChange Ω) (galPointsHom F Ω E g R)) (galPt E E' g Q) := by
  cases Q with
  | zero => rfl
  | some a b h =>
    rw [Point.map_some, galPt, autPoint_some, autPoint_some, Point.map_some]
    exact point_some_congr (galFF_translate E g R a) (galFF_translate E g R b)

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.pointMap_conj [IsAlgClosed Ω] [DecidableEq Ω]
    (g : Ω ≃ₐ[F] Ω) (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω))
    (R : (E.baseChange Ω).toAffine.Point) :
    (ψ.conj g).pointMap (galPointsHom F Ω E g R) = galPointsHom F Ω E' g (ψ.pointMap R) := by
  apply Isogeny.pointMap_eq_of_map_translate
  have h := congrArg (galPt E E' g) (ψ.map_translate R)
  rw [galPt_map_translate, map_add (f := _), galPt_val, galPt_constMap] at h
  exact h

end Conj

section Torsion

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isAlgebraic_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (hR : n • (Point.some x y h : (E.baseChange Ω).toAffine.Point) = 0) :
    IsAlgebraic F x ∧ IsAlgebraic F y := by
  have hx : IsAlgebraic F x := by
    rcases (zsmul_eq_zero_iff_ΨSq (E.baseChange Ω) n _).mp hR with h0 | ⟨x', y', h', he, hev⟩
    · exact absurd h0 (Point.some_ne_zero h)
    · have hxx : x = x' := (Point.some.inj he).1
      refine ⟨E.ΨSq n, ΨSq_ne_zero_of_ne_zero E hn, ?_⟩
      rw [hxx, ← eval_map_algebraMap, ← WeierstrassCurve.map_ΨSq]
      exact hev
  refine ⟨hx, ?_⟩
  have hxi : IsIntegral F x := hx.isIntegral
  set A := integralClosure F Ω
  have hb : _root_.IsIntegral F (algebraMap F Ω E.a₁ * x + algebraMap F Ω E.a₃) :=
    (isIntegral_algebraMap.mul hxi).add isIntegral_algebraMap
  have hc : _root_.IsIntegral F (x ^ 3 + algebraMap F Ω E.a₂ * x ^ 2 + algebraMap F Ω E.a₄ * x +
      algebraMap F Ω E.a₆) :=
    (((hxi.pow 3).add (isIntegral_algebraMap.mul (hxi.pow 2))).add
      (isIntegral_algebraMap.mul hxi)).add isIntegral_algebraMap
  let b : A := ⟨_, hb⟩
  let c : A := ⟨_, hc⟩
  let q : A[X] := X ^ 2 + C b * X - C c
  have hmon : q.Monic := by
    simp only [q]
    monicity!
  have heq : aeval y q = 0 := by
    have e := (equation_iff _ _).mp h.1
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    simp only [q, map_sub, map_add (f := _), map_mul, map_pow, aeval_X, aeval_C]
    show y ^ 2 + (algebraMap F Ω E.a₁ * x + algebraMap F Ω E.a₃) * y -
      (x ^ 3 + algebraMap F Ω E.a₂ * x ^ 2 + algebraMap F Ω E.a₄ * x + algebraMap F Ω E.a₆) = 0
    linear_combination e
  exact (isIntegral_trans (R := F) (A := A) y ⟨q, hmon, heq⟩).isAlgebraic

theorem galPointsHom_eq_self_of_zsmul_eq_zero (g : Ω ≃ₐ[F] Ω)
    (hg : ∀ z : Ω, IsAlgebraic F z → g z = z) {n : ℤ} (hn : n ≠ 0)
    {R : (E.baseChange Ω).toAffine.Point} (hR : n • R = 0) : galPointsHom F Ω E g R = R := by
  cases R with
  | zero => exact map_zero _
  | some x y h =>
    obtain ⟨hx, hy⟩ := isAlgebraic_of_zsmul_eq_zero hn h hR
    exact galPointsHom_some_eq_self F Ω E h (hg x hx) (hg y hy)

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_eq_self [IsAlgClosed Ω] (g : Ω ≃ₐ[F] Ω)
    (hg : ∀ z : Ω, IsAlgebraic F z → g z = z)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : ψ.conj g = ψ := by
  have hfix : ∀ {n : ℤ}, n ≠ 0 → ∀ R : (E.baseChange Ω).toAffine.Point, n • R = 0 →
      (ψ.conj g).pointMap R = ψ.pointMap R := by
    intro n hn R hR
    have h1 := ψ.pointMap_conj g R
    rw [galPointsHom_eq_self_of_zsmul_eq_zero g hg hn hR] at h1
    rw [h1]
    apply galPointsHom_eq_self_of_zsmul_eq_zero g hg hn
    rw [← Isogeny.pointHom_apply, ← map_zsmul, hR, map_zero]
  set χ := (ψ.conj g).1 - ψ.1 with hχ
  have hmem : χ ∈ isogHom (E.baseChange Ω) (E'.baseChange Ω) :=
    (isogHom _ _).sub_mem (ψ.conj g).respectsAdd ψ.respectsAdd
  by_contra hne
  have hχ0 : (⟨χ, hmem⟩ : isogHom (E.baseChange Ω) (E'.baseChange Ω)) ≠ 0 := by
    intro h0
    apply hne
    apply Isogeny.ext'
    have h0' := congrArg Subtype.val h0
    exact sub_eq_zero.mp h0'
  set φχ := isogOfHom ⟨χ, hmem⟩ hχ0
  have hker : ∀ {n : ℤ}, n ≠ 0 → ∀ R, n • R = 0 → R ∈ φχ.pointHom.ker := by
    intro n hn R hR
    rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]
    apply Isogeny.pointMap_eq_of_map_translate
    rw [isogOfHom_val, map_zero, add_zero]
    show Point.map _ ((ψ.conj g).1 - ψ.1) = (ψ.conj g).1 - ψ.1
    rw [map_sub, Isogeny.map_translate, Isogeny.map_translate, hfix hn R hR]
    abel
  obtain ⟨ℓ, hℓ2, hℓ⟩ : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (ℓ : Ω) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : Ω) = 0
    · refine ⟨3, by norm_num, ?_⟩
      have e : ((3 : ℕ) : Ω) = ((2 : ℕ) : Ω) + 1 := by push_cast; ring
      rw [e, h2, zero_add]
      exact one_ne_zero
    · exact ⟨2, le_refl 2, h2⟩
  set d := φχ.degree
  set n : ℤ := (ℓ : ℤ) ^ (d + 1) with hn
  have hnΩ : (n : Ω) ≠ 0 := by
    rw [hn]
    push_cast
    exact pow_ne_zero _ hℓ
  have hn0 : n ≠ 0 := fun h => hnΩ (by rw [h, Int.cast_zero])
  have hcard := card_zsmul_eq_zero (E.baseChange Ω) hnΩ
  have hle : Nat.card {P : (E.baseChange Ω).toAffine.Point // n • P = 0} ≤
      Nat.card φχ.pointHom.ker :=
    Nat.card_le_card_of_injective (fun P => ⟨P.1, hker hn0 P.1 P.2⟩)
      (by intro a b h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
  have hkd := φχ.card_ker_le_degree
  have hnat : n.natAbs = ℓ ^ (d + 1) := by
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast]
  rw [hcard, hnat] at hle
  have h2 : d < 2 ^ (d + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h3 : 2 ^ (d + 1) ≤ ℓ ^ (d + 1) := Nat.pow_le_pow_left hℓ2 _
  have h4 : ℓ ^ (d + 1) ≤ (ℓ ^ (d + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

end Torsion
end

section
open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section SlopeTestRemainingChoices

theorem map_aeval_of_comp {A B K K' : Type*} [CommRing A] [CommRing B] [CommRing K]
    [CommRing K'] [Algebra A K] [Algebra B K'] (f : K →+* K') (τ : A →+* B)
    (h : ∀ a, f (algebraMap A K a) = algebraMap B K' (τ a)) (p : A[X]) (z : K) :
    f (aeval z p) = aeval (f z) (p.map τ) := by
  rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  exact h a

theorem eq_of_add_mul_genY_eq {K : Type*} [Field K] {W : WeierstrassCurve K}
    {a b a' b' : W.toAffine.FunctionField} (ha : a ∈ K⟮genX W⟯) (hb : b ∈ K⟮genX W⟯)
    (ha' : a' ∈ K⟮genX W⟯) (hb' : b' ∈ K⟮genX W⟯)
    (h : a + b * genY W = a' + b' * genY W) : a = a' ∧ b = b' := by
  by_cases hbb : b = b'
  · subst hbb
    exact ⟨add_right_cancel h, rfl⟩
  · exfalso
    apply genY_not_mem W
    have hne : b - b' ≠ 0 := sub_ne_zero.mpr hbb
    have e : genY W = (a' - a) / (b - b') := by
      rw [eq_div_iff hne]
      linear_combination h
    rw [e]
    exact div_mem (sub_mem ha' ha) (sub_mem hb hb')

theorem ffCongr_aeval {K : Type u} [Field K] {C D : WeierstrassCurve K} (h : C = D) (p : K[X]) :
    ffCongr h (aeval (genX C) p) = aeval (genX D) p := by
  subst h
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_congr {K : Type u} [Field K]
    {C D C' D' : WeierstrassCurve K} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').congr hC.symm hC'.symm = φ := by
  subst hC hC'
  rfl

end SlopeTestRemainingChoices

section Galois

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (E : WeierstrassCurve F)

theorem galFF_aeval (g : Ω ≃ₐ[F] Ω) (p : Polynomial Ω) :
    galFF E g (aeval (genX (E.baseChange Ω)) p) =
      aeval (genX (E.baseChange Ω)) (p.map (g : Ω →+* Ω)) := by
  have := map_aeval_of_comp (galFF E g).toRingHom (g : Ω →+* Ω)
    (fun c => galFF_algebraMap E g c) p (genX (E.baseChange Ω))
  simpa [galFF_genX] using this

theorem galFF_ratEmb (g : Ω ≃ₐ[F] Ω) (r : RatFunc Ω) :
    galFF E g (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω)
      (algebraMap _ _ (r.num.map (g : Ω →+* Ω)) / algebraMap _ _ (r.denom.map (g : Ω →+* Ω))) := by
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [ratEmb_div, ratEmb_div, map_div₀, galFF_aeval, galFF_aeval]

theorem map_eq_of_galFF_ratEmb (g : Ω ≃ₐ[F] Ω) {r : RatFunc Ω}
    (h : galFF E g (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω) r) :
    r.num.map (g : Ω →+* Ω) = r.num ∧ r.denom.map (g : Ω →+* Ω) = r.denom := by
  rw [galFF_ratEmb] at h
  have h2 := ratEmb_injective (E.baseChange Ω) h
  have hcop : IsCoprime (r.num.map (g : Ω →+* Ω)) (r.denom.map (g : Ω →+* Ω)) := by
    simpa using r.isCoprime_num_denom.map (mapRingHom (g : Ω →+* Ω))
  obtain ⟨h1, h1'⟩ := num_denom_div_of_isCoprime (r.monic_denom.map (g : Ω →+* Ω)) hcop
  rw [h2] at h1 h1'
  exact ⟨h1.symm, h1'.symm⟩

theorem galFF_mem_adjoin_genX (g : Ω ≃ₐ[F] Ω) {a : (E.baseChange Ω).toAffine.FunctionField}
    (ha : a ∈ Ω⟮genX (E.baseChange Ω)⟯) : galFF E g a ∈ Ω⟮genX (E.baseChange Ω)⟯ := by
  rw [← fieldRange_ratEmb] at ha ⊢
  obtain ⟨r, rfl⟩ := ha
  exact ⟨_, (galFF_ratEmb E g r).symm⟩

end Galois

section Descent

variable {F Ω : Type u} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [IsAlgClosed Ω] in
theorem map_toAlgHom_baseChange (F₁ : IntermediateField F Ω) (W : WeierstrassCurve F) :
    (W.baseChange F₁).map (algebraMap F₁ Ω) = W.baseChange Ω :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) W (IsScalarTower.toAlgHom F F₁ Ω)

theorem isAlgebraic_of_forall_algEquiv {c : Ω}
    (h : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, g c = c) : IsAlgebraic F c := by
  haveI : IsAlgClosed (algebraicClosure F Ω) := IsAlgClosure.isAlgClosed F
  have hc := (mem_bot_iff_forall_algEquiv_apply_eq (F := algebraicClosure F Ω)).mpr h
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hc
  exact mem_algebraicClosure_iff.mp a.2

theorem isAlgebraic_coeffs [DecidableEq Ω] {r : RatFunc Ω}
    (h : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω,
      galFF E (g.restrictScalars F) (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω) r) :
    ∀ c ∈ r.num.coeffs ∪ r.denom.coeffs, IsAlgebraic F c := by
  intro c hc
  apply isAlgebraic_of_forall_algEquiv
  intro g
  obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb E (g.restrictScalars F) (h g)
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    have := congrArg (fun p : Polynomial Ω => p.coeff n) h1
    simpa using this
  · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    have := congrArg (fun p : Polynomial Ω => p.coeff n) h2
    simpa using this

omit [IsAlgClosed Ω] in
theorem exists_map_eq_of_coeffs {S : Finset Ω} {p : Polynomial Ω} (hp : p.coeffs ⊆ S) :
    ∃ p₁ : Polynomial (IntermediateField.adjoin F (S : Set Ω)),
      p₁.map (algebraMap (IntermediateField.adjoin F (S : Set Ω)) Ω) = p := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  by_cases hn : p.coeff n = 0
  · exact ⟨0, by rw [hn, map_zero]⟩
  · exact ⟨⟨p.coeff n, IntermediateField.subset_adjoin F _ (hp (coeff_mem_coeffs hn))⟩, rfl⟩

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_finiteDimensional_mapOf_eq
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧
      ∃ (φ : Isogeny (E.baseChange F₁) (E'.baseChange F₁))
        (h : (E.baseChange F₁).map (algebraMap F₁ Ω) = E.baseChange Ω)
        (h' : (E'.baseChange F₁).map (algebraMap F₁ Ω) = E'.baseChange Ω),
        φ.mapOf (algebraMap F₁ Ω) h h' = ψ := by
  classical
  have hfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, ψ.conj (g.restrictScalars F) = ψ :=
    fun g => ψ.conj_eq_self _ (fun z hz => g.commutes ⟨z, mem_algebraicClosure_iff.mpr hz⟩)
  have hxfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.x = ψ.x :=
    fun g => by rw [← Isogeny.conj_alt_bis, hfix g]
  have hyfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.y = ψ.y :=
    fun g => by rw [← Isogeny.conj_y, hfix g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (E.baseChange Ω) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (E.baseChange Ω) r₂ = a at hr₂
  change ratEmb (E.baseChange Ω) r₃ = b at hr₃
  have hab_fix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω,
      galFF E (g.restrictScalars F) a = a ∧ galFF E (g.restrictScalars F) b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add (f := _), map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX E _ ha) (galFF_mem_adjoin_genX E _ hb)
      ha hb e
  have h1 := isAlgebraic_coeffs (E := E) (r := r) (fun g => by rw [hr]; exact hxfix g)
  have h2 := isAlgebraic_coeffs (E := E) (r := r₂) (fun g => by rw [hr₂]; exact (hab_fix g).1)
  have h3 := isAlgebraic_coeffs (E := E) (r := r₃) (fun g => by rw [hr₃]; exact (hab_fix g).2)
  set S : Finset Ω := (r.num.coeffs ∪ r.denom.coeffs) ∪ (r₂.num.coeffs ∪ r₂.denom.coeffs) ∪
    (r₃.num.coeffs ∪ r₃.denom.coeffs) with hS
  have hSalg : ∀ c ∈ (S : Set Ω), _root_.IsIntegral F c := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact (h1 c hc).isIntegral
      · exact (h2 c hc).isIntegral
    · exact (h3 c hc).isIntegral
  set F₁ := IntermediateField.adjoin F (S : Set Ω)
  haveI : FiniteDimensional F F₁ := IntermediateField.finiteDimensional_adjoin hSalg
  obtain ⟨n₁, hn₁⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₁, hd₁⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r.denom)
    (fun c hc => by simp [hS, hc])
  obtain ⟨n₂, hn₂⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₂, hd₂⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.denom)
    (fun c hc => by simp [hS, hc])
  obtain ⟨n₃, hn₃⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₃, hd₃⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.denom)
    (fun c hc => by simp [hS, hc])
  set σ₁ := algebraMap F₁ Ω
  set C₁ := E.baseChange F₁
  have h := map_toAlgHom_baseChange F₁ E
  have h' := map_toAlgHom_baseChange F₁ E'
  set ψ₁ := ψ.congr h.symm h'.symm
  set X₁ := genX C₁
  set x₁ : C₁.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : C₁.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY C₁
  have hrat : ∀ (s : RatFunc Ω) (p q : Polynomial F₁), p.map σ₁ = s.num → q.map σ₁ = s.denom →
      ffMap σ₁ C₁ (aeval X₁ p / aeval X₁ q) = ffCongr h.symm (ratEmb (E.baseChange Ω) s) := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, map_div₀, ffCongr_aeval, ffCongr_aeval, ffMap_aeval, ffMap_aeval,
      ffMap_genX, hp, hq]
  have hx₁ : ffMap σ₁ C₁ x₁ = ψ₁.x := by
    rw [Isogeny.congr_alt, ← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap σ₁ C₁ y₁ = ψ₁.y := by
    rw [Isogeny.congr_y, hab, map_add (f := _), map_mul, ← hr₂, ← hr₃, map_add (f := _), map_mul,
      hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃, ffMap_genY, ffCongr_genY]
  refine ⟨F₁, inferInstance, Isogeny.ofMap σ₁ ψ₁ x₁ y₁ hx₁ hy₁, h, h', ?_⟩
  rw [Isogeny.mapOf, Isogeny.map_ofMap]
  exact Isogeny.congr_congr h.symm h'.symm ψ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_numberField_mapOf_eq [NumberField F]
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    ∃ F₁ : IntermediateField F Ω, NumberField F₁ ∧
      ∃ (φ : Isogeny (E.baseChange F₁) (E'.baseChange F₁))
        (h : (E.baseChange F₁).map (algebraMap F₁ Ω) = E.baseChange Ω)
        (h' : (E'.baseChange F₁).map (algebraMap F₁ Ω) = E'.baseChange Ω),
        φ.mapOf (algebraMap F₁ Ω) h h' = ψ := by
  obtain ⟨F₁, hfin, rest⟩ := ψ.exists_finiteDimensional_mapOf_eq
  exact ⟨F₁, NumberField.of_module_finite F F₁, rest⟩

end Descent

section OverF

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [DecidableEq Ω] in
theorem galFF_bcEmb (g : Ω ≃ₐ[F] Ω) (f : E.toAffine.FunctionField) :
    galFF E g (bcEmb (F' := Ω) E f) = bcEmb (F' := Ω) E f := by
  have e : (galFF E g).toRingHom.comp (bcEmb (F' := Ω) E).toRingHom =
      (bcEmb (F' := Ω) E).toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, AlgHom.commutes]
      exact galFF_algebraMap_base E g a
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, bcEmb_genX]
      exact galFF_genX E g
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, bcEmb_genY]
      exact galFF_genY E g
  exact DFunLike.congr_fun e f

theorem conj_isogBaseChange (g : Ω ≃ₐ[F] Ω) (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).conj g = isogBaseChange (F' := Ω) φ :=
  Isogeny.ext_xy (by rw [Isogeny.conj_alt_bis, isogBaseChange_alt, galFF_bcEmb])
    (by rw [Isogeny.conj_y, isogBaseChange_y, galFF_bcEmb])

theorem pointMap_isogBaseChange_galPointsHom [IsAlgClosed Ω] (g : Ω ≃ₐ[F] Ω) (φ : Isogeny E E')
    (R : (E.baseChange Ω).toAffine.Point) :
    (isogBaseChange (F' := Ω) φ).pointMap (galPointsHom F Ω E g R) =
      galPointsHom F Ω E' g ((isogBaseChange (F' := Ω) φ).pointMap R) := by
  have := (isogBaseChange (F' := Ω) φ).pointMap_conj g R
  rwa [conj_isogBaseChange] at this

theorem exists_pointMap_isogBaseChange_eq [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E')
    (P : E.toAffine.Point) :
    ∃ P' : E'.toAffine.Point,
      (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P) = constMap E' Ω P' := by
  set Q := (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P)
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, galPointsHom F Ω E' g Q = Q := by
    intro g
    rw [← pointMap_isogBaseChange_galPointsHom]
    congr 1
    exact map_constMap E (g : Ω →ₐ[F] Ω) P
  cases hQ : Q with
  | zero => exact ⟨0, (map_zero (constMap E' Ω)).symm⟩
  | some u v h =>
    rw [hQ] at hfix
    have key : ∀ g : Ω ≃ₐ[F] Ω, g u = u ∧ g v = v := by
      intro g
      have := hfix g
      obtain ⟨h', e⟩ := galPointsHom_some F Ω E' g h
      rw [e] at this
      exact ⟨(Point.some.inj this).1, (Point.some.inj this).2⟩
    have hu : u ∈ (⊥ : IntermediateField F Ω) :=
      mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).1
    have hv : v ∈ (⊥ : IntermediateField F Ω) :=
      mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).2
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hu
    obtain ⟨b, rfl⟩ := IntermediateField.mem_bot.mp hv
    have hab : E'.toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F Ω) (algebraMap F Ω).injective a b).mp h
    exact ⟨.some a b hab, rfl⟩

variable (Ω) in
noncomputable def pointHomOver [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E') :
    E.toAffine.Point →+ E'.toAffine.Point :=
  AddMonoidHom.mk' (fun P => (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose)
    (fun P₁ P₂ => by
      apply constMap_injective E' Ω
      have e₃ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ (P₁ + P₂)).choose_spec
      have e₁ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P₁).choose_spec
      have e₂ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P₂).choose_spec
      rw [map_add (constMap E' Ω), ← e₃, ← e₁, ← e₂, map_add (constMap E Ω),
        Isogeny.pointMap_add])

theorem constMap_pointHomOver [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E')
    (P : E.toAffine.Point) :
    constMap E' Ω (pointHomOver Ω φ P) =
      (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P) :=
  (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose_spec.symm

end OverF
end

section
open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff CoordinateRing)
open scoped Polynomial.Bivariate

universe u

section Coord

theorem eq_zero_of_aeval_genX_add_mul_genY {K : Type*} [Field K] (V : WeierstrassCurve K)
    {P Q : K[X]} (h : aeval (genX V) P + aeval (genX V) Q * genY V = 0) : P = 0 ∧ Q = 0 := by
  apply CoordinateRing.smul_basis_eq_zero (W' := V.toAffine)
  apply IsFractionRing.injective V.toAffine.CoordinateRing V.toAffine.FunctionField
  rw [map_zero, ← h, map_add (f := _), Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    genX_eq, aeval_algebraMap_apply, aeval_algebraMap_apply, aeval_X_left_apply,
    aeval_X_left_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

end Coord

section LinearDisjoint

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (W : WeierstrassCurve F)

theorem bcEmb_algebraMap_smul_basis (p q : F[X]) :
    bcEmb (F' := Ω) W (algebraMap W.toAffine.CoordinateRing _
      (p • 1 + q • CoordinateRing.mk W.toAffine Y)) =
      aeval (genX (W.baseChange Ω)) (p.map (algebraMap F Ω)) +
        aeval (genX (W.baseChange Ω)) (q.map (algebraMap F Ω)) * genY (W.baseChange Ω) := by
  have e : ∀ t : F[X], algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap F[X] W.toAffine.CoordinateRing t) = aeval (genX W) t := by
    intro t
    rw [← IsScalarTower.algebraMap_apply, genX_eq, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [map_add (f := _), Algebra.smul_def, Algebra.smul_def, mul_one, map_add (f := _), map_mul, e, e,
    show algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine Y) = genY W from rfl, map_mul, ← aeval_algHom_apply,
    ← aeval_algHom_apply, bcEmb_genX, bcEmb_genY, aeval_map_algebraMap, aeval_map_algebraMap]

theorem coordinateRing_eq_zero_of_sum {ι : Type*} (s : Finset ι) {ω : ι → Ω}
    (hω : LinearIndependent F ω) (r : ι → W.toAffine.CoordinateRing)
    (h : ∑ i ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r i)) * algebraMap Ω _ (ω i) = 0) :
    ∀ i ∈ s, r i = 0 := by
  choose p q hpq using fun i => CoordinateRing.exists_smul_basis_eq (r i)
  have e : ∀ i, bcEmb (F' := Ω) W (algebraMap _ _ (r i)) * algebraMap Ω _ (ω i) =
      aeval (genX (W.baseChange Ω)) (C (ω i) * (p i).map (algebraMap F Ω)) +
        aeval (genX (W.baseChange Ω)) (C (ω i) * (q i).map (algebraMap F Ω)) *
          genY (W.baseChange Ω) := by
    intro i
    rw [← hpq i, bcEmb_algebraMap_smul_basis]
    simp only [map_mul, aeval_C]
    ring

  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum] at h
  obtain ⟨hP, hQ⟩ := eq_zero_of_aeval_genX_add_mul_genY _ h
  have hcoef : ∀ (t : ι → F[X]), ∑ i ∈ s, C (ω i) * (t i).map (algebraMap F Ω) = 0 →
      ∀ i ∈ s, t i = 0 := by
    intro t ht i hi
    ext n
    have hn := congrArg (fun p : Polynomial Ω => p.coeff n) ht
    simp only [finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at hn
    have hn' : ∑ j ∈ s, (t j).coeff n • ω j = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    rw [coeff_zero]
    exact linearIndependent_iff'.mp hω s (fun j => (t j).coeff n) hn' i hi
  intro i hi
  rw [← hpq i, hcoef p hP i hi, hcoef q hQ i hi, zero_smul, zero_smul, add_zero]

theorem linearDisjoint_bcEmb : (bcEmb (F' := Ω) W).fieldRange.LinearDisjoint Ω := by
  classical
  apply LinearDisjoint.of_basis_right' (Module.Basis.ofVectorSpace F Ω)
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose α hα using fun j => AlgHom.mem_fieldRange.mp (g j).2
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors W.toAffine.CoordinateRing) s α
  choose! r hr using hc
  have hc0 : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (c : _) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  have hsum : ∑ j ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r j)) *
      algebraMap Ω _ (Module.Basis.ofVectorSpace F Ω j) = 0 := by
    have : ∀ j ∈ s, bcEmb (F' := Ω) W (algebraMap _ _ (r j)) *
        algebraMap Ω _ (Module.Basis.ofVectorSpace F Ω j) =
        bcEmb (F' := Ω) W (algebraMap W.toAffine.CoordinateRing _ c) *
          (g j • (algebraMap Ω _ ∘ Module.Basis.ofVectorSpace F Ω) j) := by
      intro j hj
      rw [hr j hj, Algebra.smul_def, map_mul, Function.comp_apply, Algebra.smul_def,
        mul_assoc]
      congr 2
      exact hα j
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hg, mul_zero]
  have h0 := coordinateRing_eq_zero_of_sum W s (Module.Basis.ofVectorSpace F Ω).linearIndependent r hsum i hi
  have : α i = 0 := by
    have := hr i hi
    rw [h0, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc0
  exact Subtype.ext (by rw [← hα i, this, map_zero]; rfl)

end LinearDisjoint

section Sup

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (W : WeierstrassCurve F)

theorem sup_bcEmb_eq_top :
    (bcEmb (F' := Ω) W).fieldRange ⊔
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ IntermediateField.adjoin Ω {genX (W.baseChange Ω), genY (W.baseChange Ω)} := by
    rw [adjoin_genX_genY]; trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact (le_sup_left : (bcEmb (F' := Ω) W).fieldRange ≤ _) ⟨genX W, bcEmb_genX W⟩
    · exact (le_sup_left : (bcEmb (F' := Ω) W).fieldRange ≤ _) ⟨genY W, bcEmb_genY W⟩
  | algebraMap x =>
    exact (le_sup_right : (IsScalarTower.toAlgHom F Ω _).fieldRange ≤ _) ⟨x, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | inv x _ hx => exact inv_mem hx
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem sup_toSubalgebra_bcEmb_eq_top [Algebra.IsAlgebraic F Ω] :
    (bcEmb (F' := Ω) W).fieldRange.toSubalgebra ⊔
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra =
        ⊤ := by
  have : Algebra.IsAlgebraic F
      (IsScalarTower.toAlgHom F Ω (W.baseChange Ω).toAffine.FunctionField).fieldRange :=
    ⟨fun ⟨x, hx⟩ => by
      obtain ⟨ω, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      exact isAlgebraic_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic ω).algHom _)⟩
  rw [← sup_toSubalgebra_of_isAlgebraic_right, sup_bcEmb_eq_top, top_toSubalgebra]

end Sup

section Descent

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem comap_isogBaseChange_bcEmb (φ : Isogeny E E') (g : E'.toAffine.FunctionField) :
    (isogBaseChange (F' := Ω) φ).comap (bcEmb (F' := Ω) E' g) = bcEmb (F' := Ω) E (φ.comap g) := by
  classical
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  have hx : (isogBaseChange (F' := Ω) φ).x = bcEmb (F' := Ω) E φ.x := by
    change xOf _ (isogBaseChange (F' := Ω) φ).1 = _
    rw [isogBaseChange_val, he, Point.map_some, Isogeny.x, he]
    rfl
  have hy : (isogBaseChange (F' := Ω) φ).y = bcEmb (F' := Ω) E φ.y := by
    change yOf _ (isogBaseChange (F' := Ω) φ).1 = _
    rw [isogBaseChange_val, he, Point.map_some, Isogeny.y, he]
    rfl
  have : ((isogBaseChange (F' := Ω) φ).comap.restrictScalars F).comp (bcEmb (F' := Ω) E') =
      (bcEmb (F' := Ω) E).comp φ.comap := by
    apply algHom_ext_gen E'
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, bcEmb_genX, Isogeny.comap_genX, hx]
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, bcEmb_genY, Isogeny.comap_genY, hy]
  exact DFunLike.congr_fun this g

theorem mem_fieldRange_comap_of_bcEmb [Algebra.IsAlgebraic F Ω] (φ : Isogeny E E')
    {f : E.toAffine.FunctionField}
    (hf : bcEmb (F' := Ω) E f ∈ (isogBaseChange (F' := Ω) φ).comap.fieldRange) :
    f ∈ φ.comap.fieldRange := by
  classical
  set ι := bcEmb (F' := Ω) E
  set ψ := isogBaseChange (F' := Ω) φ
  set Ω₁ := (IsScalarTower.toAlgHom F Ω (E.baseChange Ω).toAffine.FunctionField).fieldRange
  have H : ι.fieldRange.LinearDisjoint Ω₁ :=
    linearDisjoint_iff'.2 (by rw [AlgHom.fieldRange_toSubalgebra]; exact linearDisjoint_bcEmb E)
  set b := Module.Basis.ofVectorSpace F Ω₁
  set bb := H.basisOfBasisRight (sup_toSubalgebra_bcEmb_eq_top E) b
  have hrepr : ∀ (x : Ω₁) (i : Module.Basis.ofVectorSpaceIndex F Ω₁),
      ((bb.repr (x : (E.baseChange Ω).toAffine.FunctionField) i : ι.fieldRange) :
        (E.baseChange Ω).toAffine.FunctionField) = algebraMap F _ (b.repr x i) :=
    fun x i => H.algebraMap_basisOfBasisRight_repr_apply _ b x i
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : b.repr 1 = 0 := Finsupp.ext hcon
    exact one_ne_zero (b.repr.injective (h1.trans (map_zero _).symm))
  set N₁ := (ι.comp φ.comap).fieldRange
  set c : (E.baseChange Ω).toAffine.FunctionField →ₗ[ι.fieldRange] ι.fieldRange := bb.coord i
  have hc : ∀ (a : ι.fieldRange) (z : (E.baseChange Ω).toAffine.FunctionField),
      ((c ((a : (E.baseChange Ω).toAffine.FunctionField) * z) : ι.fieldRange) :
        (E.baseChange Ω).toAffine.FunctionField) = a * (c z : (E.baseChange Ω).toAffine.FunctionField) := by
    intro a z
    change ((c (a • z) : ι.fieldRange) : (E.baseChange Ω).toAffine.FunctionField) = _
    rw [map_smul, smul_eq_mul, IntermediateField.coe_mul]
  have hcΩ : ∀ ω : Ω, ((c (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω) : ι.fieldRange) :
      (E.baseChange Ω).toAffine.FunctionField) ∈ N₁ := by
    intro ω
    have := hrepr ⟨algebraMap Ω _ ω, ⟨ω, rfl⟩⟩ i
    change ((c (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω) : ι.fieldRange) :
      (E.baseChange Ω).toAffine.FunctionField) = _ at this
    rw [this]
    exact IntermediateField.algebraMap_mem N₁ _

  set T : (E'.baseChange Ω).toAffine.FunctionField →ₗ[F] (E.baseChange Ω).toAffine.FunctionField :=
    (ι.fieldRange.val.toLinearMap.comp (c.restrictScalars F)).comp
      (ψ.comap.restrictScalars F).toLinearMap
  have hT : ∀ z, T z = ((c (ψ.comap z) : ι.fieldRange) : (E.baseChange Ω).toAffine.FunctionField) :=
    fun z => rfl
  have hle : Subalgebra.toSubmodule (bcEmb (F' := Ω) E').fieldRange.toSubalgebra *
      Subalgebra.toSubmodule
        (IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra ≤
      (Subalgebra.toSubmodule N₁.toSubalgebra).comap T := by
    rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hm
    obtain ⟨ω, rfl⟩ := AlgHom.mem_fieldRange.mp hn
    rw [Submodule.mem_comap, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    have e1 : ψ.comap (bcEmb (F' := Ω) E' a *
        IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField ω) =
        ι (φ.comap a) * algebraMap Ω (E.baseChange Ω).toAffine.FunctionField ω := by
      rw [map_mul, comap_isogBaseChange_bcEmb, IsScalarTower.coe_toAlgHom', AlgHom.commutes]
    rw [hT, e1, hc ⟨ι (φ.comap a), ⟨φ.comap a, rfl⟩⟩]
    exact mul_mem ⟨a, rfl⟩ (hcΩ ω)
  obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp hf
  have hzT : T z ∈ N₁ := by
    have h3 : z ∈ Subalgebra.toSubmodule (bcEmb (F' := Ω) E').fieldRange.toSubalgebra *
        Subalgebra.toSubmodule
          (IsScalarTower.toAlgHom F Ω (E'.baseChange Ω).toAffine.FunctionField).fieldRange.toSubalgebra := by
      rw [Subalgebra.mul_toSubmodule, sup_toSubalgebra_bcEmb_eq_top]
      trivial
    have h4 := hle h3
    rwa [Submodule.mem_comap, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at h4
  have e2 : T z = ι f * algebraMap F _ (b.repr 1 i) := by
    have h1 := hc ⟨ι f, ⟨f, rfl⟩⟩ 1
    rw [mul_one] at h1
    rw [hT, hz, h1]
    congr 1
    exact hrepr 1 i
  have hmem : ι f ∈ N₁ := by
    have := mul_mem hzT (IntermediateField.algebraMap_mem N₁ (b.repr 1 i)⁻¹)
    rwa [e2, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one] at this
  obtain ⟨g, hg⟩ := AlgHom.mem_fieldRange.mp hmem
  exact ⟨g, ι.injective hg⟩

end Descent
end

section
open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section BaseChange

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem x_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).x = bcEmb (F' := Ω) E φ.x := by
  classical
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  change xOf _ (isogBaseChange (F' := Ω) φ).1 = _
  rw [isogBaseChange_val, he, Point.map_some, Isogeny.x, he]
  rfl

theorem y_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).y = bcEmb (F' := Ω) E φ.y := by
  classical
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  change yOf _ (isogBaseChange (F' := Ω) φ).1 = _
  rw [isogBaseChange_val, he, Point.map_some, Isogeny.y, he]
  rfl

theorem isogBaseChange_injective :
    Function.Injective (isogBaseChange (F' := Ω) : Isogeny E E' → _) := by
  intro φ ψ h
  apply Isogeny.ext_xy
  · have e := congrArg Isogeny.x h
    rw [x_isogBaseChange, x_isogBaseChange] at e
    exact (bcEmb (F' := Ω) E).injective e
  · have e := congrArg Isogeny.y h
    rw [y_isogBaseChange, y_isogBaseChange] at e
    exact (bcEmb (F' := Ω) E).injective e

theorem isogBaseChange_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    isogBaseChange (F' := Ω) (ψ.comp φ) =
      (isogBaseChange (F' := Ω) ψ).comp (isogBaseChange (F' := Ω) φ) := by
  apply Isogeny.ext_xy
  · rw [x_isogBaseChange, Isogeny.comp_alt, Isogeny.comp_alt, x_isogBaseChange,
      comap_isogBaseChange_bcEmb]
  · rw [y_isogBaseChange, Isogeny.comp_y, Isogeny.comp_y, y_isogBaseChange,
      comap_isogBaseChange_bcEmb]

theorem isogBaseChange_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    isogBaseChange (F' := Ω) (mulIsogeny E n hn) = mulIsogeny (E.baseChange Ω) n hn := by
  classical
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := Ω) E) (n • genericPoint E) =
    n • genericPoint (E.baseChange Ω)
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

theorem degree_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).degree = φ.degree := by
  obtain ⟨r, hr⟩ := φ.exists_ratEmb_eq_x
  have hcop : IsCoprime (r.num.map (algebraMap F Ω)) (r.denom.map (algebraMap F Ω)) := by
    simpa using r.isCoprime_num_denom.map (mapRingHom (algebraMap F Ω))
  obtain ⟨h1, h2⟩ := num_denom_div_of_isCoprime (r.monic_denom.map (algebraMap F Ω)) hcop
  have hb : ∀ p : F[X], bcEmb (F' := Ω) E (aeval (genX E) p) =
      aeval (genX (E.baseChange Ω)) (p.map (algebraMap F Ω)) := by
    intro p
    rw [← aeval_algHom_apply, bcEmb_genX, aeval_map_algebraMap]
  have hx : ratEmb (E.baseChange Ω) (algebraMap _ _ (r.num.map (algebraMap F Ω)) /
      algebraMap _ _ (r.denom.map (algebraMap F Ω))) = (isogBaseChange (F' := Ω) φ).x := by
    rw [x_isogBaseChange, ← hr, ratEmb_div]
    conv_rhs => rw [← RatFunc.num_div_denom r]
    rw [ratEmb_div, map_div₀, hb, hb]
  rw [φ.degree_eq_max_natDegree hr, (isogBaseChange (F' := Ω) φ).degree_eq_max_natDegree hx, h1, h2,
    natDegree_map_eq_of_injective (algebraMap F Ω).injective,
    natDegree_map_eq_of_injective (algebraMap F Ω).injective]

end BaseChange

section Dual

variable {F : Type u} [Field F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

theorem isogeny_degree_ne_zero (φ : Isogeny E E') : (φ.degree : ℤ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (_root_.GroundTheory.Arith.Abelian.Isogeny.degree_pos φ).ne'

theorem mulIsogeny_eq_dual_comp_isogBaseChange [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    mulIsogeny (E.baseChange (AlgebraicClosure F)) φ.degree (isogeny_degree_ne_zero φ) =
      (isogBaseChange (F' := AlgebraicClosure F) φ).dual.comp (isogBaseChange φ) := by
  rw [Isogeny.dual_comp]
  exact mulIsogeny_congr (by rw [degree_isogBaseChange]) _ _

theorem mulIsogeny_comap_mem_fieldRange (φ : Isogeny E E') (f : E.toAffine.FunctionField) :
    (mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap f ∈ φ.comap.fieldRange := by
  classical
  apply mem_fieldRange_comap_of_bcEmb (Ω := AlgebraicClosure F) φ
  rw [← comap_isogBaseChange_bcEmb, isogBaseChange_mulIsogeny,
    mulIsogeny_eq_dual_comp_isogBaseChange, Isogeny.comap_comp, AlgHom.comp_apply]
  exact ⟨_, rfl⟩

noncomputable def dualComapOver (φ : Isogeny E E') :
    E.toAffine.FunctionField →ₐ[F] E'.toAffine.FunctionField :=
  φ.comap.equivFieldRange.symm.toAlgHom.comp
    ((mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (mulIsogeny_comap_mem_fieldRange φ))

theorem comap_dualComapOver (φ : Isogeny E E') (f : E.toAffine.FunctionField) :
    φ.comap (dualComapOver φ f) = (mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap f := by
  have := φ.comap.equivFieldRange.apply_symm_apply
    ((mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (mulIsogeny_comap_mem_fieldRange φ) f)
  exact congrArg Subtype.val this

noncomputable def dualPtOver (φ : Isogeny E E') : (E.baseChange E'.toAffine.FunctionField).toAffine.Point :=
  Point.map (dualComapOver φ) (genericPoint E)

theorem isGenPt_dualPtOver (φ : Isogeny E E') : IsGenPt E (dualPtOver φ) :=
  isGenPt_map_genericPoint E _

theorem map_bcEmb_dualPtOver [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') (dualPtOver φ) :
      ((E.baseChange (AlgebraicClosure F)).baseChange
        (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
      (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1 := by
  have hD : (bcEmb (F' := AlgebraicClosure F) E').comp (dualComapOver φ) =
      ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap.restrictScalars F).comp
        (bcEmb (F' := AlgebraicClosure F) E) := by
    apply AlgHom.ext
    intro f
    have key : (isogBaseChange (F' := AlgebraicClosure F) φ).comap
        (bcEmb (F' := AlgebraicClosure F) E' (dualComapOver φ f)) =
        (isogBaseChange (F' := AlgebraicClosure F) φ).comap
          ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap
            (bcEmb (F' := AlgebraicClosure F) E f)) := by
      rw [comap_isogBaseChange_bcEmb, comap_dualComapOver, ← comap_isogBaseChange_bcEmb,
        isogBaseChange_mulIsogeny, mulIsogeny_eq_dual_comp_isogBaseChange, Isogeny.comap_comp,
        AlgHom.comp_apply]
    exact (isogBaseChange (F' := AlgebraicClosure F) φ).comap.injective key
  have hcast : ∀ X : (E.baseChange (E.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point,
      Point.map (W' := E)
          ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap.restrictScalars F) X =
        Point.map (W' := E.baseChange (AlgebraicClosure F))
          (isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap X := by
    intro X
    cases X <;> rfl
  rw [dualPtOver, Point.map_map, hD, ← Point.map_map, hcast, map_bcEmb_genericPoint,
    Isogeny.map_comap_genericPoint]

end Dual
end

section
open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section DualOver

variable {F : Type u} [Field F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

theorem respectsAdd_dualPtOver (φ : Isogeny E E') : RespectsAdd E' E (dualPtOver φ) := by
  classical
  have hQ := isGenPt_dualPtOver φ
  have hxy : ∀ Q : (E.baseChange E'.toAffine.FunctionField).toAffine.Point, IsGenPt E Q →
      xOf _ (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') Q :
        ((E.baseChange (AlgebraicClosure F)).baseChange
          (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
        bcEmb (F' := AlgebraicClosure F) E' (xOf _ Q) ∧
      yOf _ (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') Q :
        ((E.baseChange (AlgebraicClosure F)).baseChange
          (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
        bcEmb (F' := AlgebraicClosure F) E' (yOf _ Q) := by
    intro Q hQ
    cases Q with
    | zero => exact hQ.elim
    | some x y h => exact ⟨rfl, rfl⟩
  refine respectsAdd_of_map (algebraMap F (AlgebraicClosure F))
    (isogBaseChange (F' := AlgebraicClosure F) φ).dual (isGenPt_ne_zero E hQ) ?_ ?_
  · rw [ffMap_algebraMap_eq_bcEmb]
    show _ = xOf _ (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1
    rw [← map_bcEmb_dualPtOver]
    exact ((hxy _ hQ).1).symm
  · rw [ffMap_algebraMap_eq_bcEmb]
    show _ = yOf _ (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1
    rw [← map_bcEmb_dualPtOver]
    exact ((hxy _ hQ).2).symm

noncomputable def dualOver (φ : Isogeny E E') : Isogeny E' E :=
  ⟨dualPtOver φ, (isIsogeny_iff _).mpr ⟨isGenPt_dualPtOver φ, respectsAdd_dualPtOver φ⟩⟩

theorem isogBaseChange_dualOver [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    isogBaseChange (F' := AlgebraicClosure F) (dualOver φ) = (isogBaseChange φ).dual :=
  Subtype.ext (map_bcEmb_dualPtOver φ)

theorem dualOver_comp (φ : Isogeny E E') :
    (dualOver φ).comp φ = mulIsogeny E φ.degree (isogeny_degree_ne_zero φ) := by
  classical
  apply isogBaseChange_injective (Ω := AlgebraicClosure F)
  rw [isogBaseChange_comp, isogBaseChange_dualOver, isogBaseChange_mulIsogeny,
    mulIsogeny_eq_dual_comp_isogBaseChange]

theorem comp_dualOver (φ : Isogeny E E') :
    φ.comp (dualOver φ) = mulIsogeny E' φ.degree (isogeny_degree_ne_zero φ) := by
  classical
  apply isogBaseChange_injective (Ω := AlgebraicClosure F)
  rw [isogBaseChange_comp, isogBaseChange_dualOver, isogBaseChange_mulIsogeny, Isogeny.comp_dual]
  exact mulIsogeny_congr (by rw [degree_isogBaseChange]) _ _

theorem degree_dualOver (φ : Isogeny E E') : (dualOver φ).degree = φ.degree := by
  classical
  rw [← degree_isogBaseChange (Ω := AlgebraicClosure F), isogBaseChange_dualOver,
    Isogeny.degree_dual, degree_isogBaseChange]

end DualOver
end

section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

section Twist

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusTwist : WeierstrassCurve F := E.map (frobenius F p)

instance [E.IsElliptic] : (frobeniusTwist E p).IsElliptic := by
  unfold frobeniusTwist; infer_instance

theorem j_frobeniusTwist [E.IsElliptic] : (frobeniusTwist E p).j = E.j ^ p := by
  show (E.map (frobenius F p)).j = _
  rw [map_j, frobenius_def]

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem baseChange_frobeniusTwist :
    (frobeniusTwist E p).baseChange L = (E.baseChange L).map (frobenius L p) := by
  show (E.map (frobenius F p)).map (algebraMap F L) = (E.map (algebraMap F L)).map (frobenius L p)
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [frobenius_def]

theorem nonsingular_pow {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) := by
  rw [baseChange_frobeniusTwist]
  have := ((E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y).mpr h
  simpa only [frobenius_def] using this

theorem nonsingular_pow_iff {x y : L} :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) ↔
      (E.baseChange L).toAffine.Nonsingular x y := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y
  simpa only [frobenius_def] using this

theorem negY_pow (x y : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.negY (x ^ p) (y ^ p) =
      (E.baseChange L).toAffine.negY x y ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_negY (frobenius L p) x y
  simpa only [frobenius_def] using this

theorem addX_pow (x₁ x₂ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addX (x₁ ^ p) (x₂ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addX x₁ x₂ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addX (frobenius L p) x₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem addY_pow (x₁ x₂ y₁ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addY (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addY x₁ x₂ y₁ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addY (frobenius L p) x₁ y₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem slope_pow [DecidableEq L] (x₁ x₂ y₁ y₂ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.slope (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
      (E.baseChange L).toAffine.slope x₁ x₂ y₁ y₂ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_slope (frobenius L p) x₁ x₂ y₁ y₂
  simpa only [frobenius_def] using this

end Twist

section PointMap

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusPoint (L : Type*) [Field L] [Algebra F L] [CharP L p] :
    (E.baseChange L).toAffine.Point → ((frobeniusTwist E p).baseChange L).toAffine.Point
  | .zero => 0
  | .some x y h => .some (x ^ p) (y ^ p) (nonsingular_pow E p h)

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem frobeniusPoint_some {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    frobeniusPoint E p L (.some x y h) = .some (x ^ p) (y ^ p) (nonsingular_pow E p h) := rfl

theorem frobeniusPoint_add [DecidableEq L] (P Q : (E.baseChange L).toAffine.Point) :
    frobeniusPoint E p L (P + Q) = frobeniusPoint E p L P + frobeniusPoint E p L Q := by
  have hinj : Function.Injective fun z : L => z ^ p := by
    intro a b hab
    exact frobenius_inj L p (by simpa only [frobenius_def] using hab)
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · show frobeniusPoint E p L (0 + Q) = 0 + frobeniusPoint E p L Q
    rw [zero_add, zero_add]
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · show frobeniusPoint E p L (Point.some x₁ y₁ h₁ + 0) = frobeniusPoint E p L (Point.some x₁ y₁ h₁) + 0
    rw [add_zero, add_zero]
  rw [frobeniusPoint_some, frobeniusPoint_some]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E.baseChange L).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, Point.add_of_Y_eq (congrArg (· ^ p) hxy.1)
      (by rw [negY_pow, hxy.2])]
    rfl
  · have hxy' : ¬(x₁ ^ p = x₂ ^ p ∧
        y₁ ^ p = ((frobeniusTwist E p).baseChange L).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
      rintro ⟨hx, hy⟩
      rw [negY_pow] at hy
      exact hxy ⟨hinj hx, hinj hy⟩
    rw [Point.add_some hxy, Point.add_some hxy', frobeniusPoint_some, Point.some.injEq,
      slope_pow, addX_pow, addY_pow]
    exact ⟨rfl, rfl⟩

theorem isGenPt_frobeniusPoint_iff (P : (E.baseChange L).toAffine.Point) :
    IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L P) ↔ IsGenPt E P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · exact Iff.rfl
  · rw [frobeniusPoint_some, isGenPt_some, isGenPt_some]
    exact ⟨fun ht hx => ht (hx.pow p), fun ht => ht.pow hp.out.pos⟩

end PointMap

section FrobeniusIsogeny

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime]
  [CharP F p]

omit [E.IsElliptic] in
theorem map_frobeniusPoint {L L' : Type*} [Field L] [Algebra F L] [CharP L p] [Field L']
    [Algebra F L'] [CharP L' p] [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L')
    (P : (E.baseChange L).toAffine.Point) :
    Point.map σ (frobeniusPoint E p L P) = frobeniusPoint E p L' (Point.map σ P) := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [frobeniusPoint_some, Point.map_some, map_pow]

noncomputable def frobeniusGenPt :
    ((frobeniusTwist E p).baseChange E.toAffine.FunctionField).toAffine.Point :=
  frobeniusPoint E p _ (genericPoint E)

theorem map_genEval_frobeniusGenPt {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    Point.map (genEval E P hP) (frobeniusGenPt E p) = frobeniusPoint E p L P := by
  classical
  rw [frobeniusGenPt, map_frobeniusPoint, map_genEval_genericPoint]

theorem isGenPt_frobeniusGenPt : IsGenPt (frobeniusTwist E p) (frobeniusGenPt E p) :=
  (isGenPt_frobeniusPoint_iff E p _).mpr (transcendental_genX E)

theorem respectsAdd_frobeniusGenPt : RespectsAdd E (frobeniusTwist E p) (frobeniusGenPt E p) := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  rw [map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt,
    frobeniusPoint_add]

noncomputable def frobeniusIsogeny : Isogeny E (frobeniusTwist E p) :=
  ⟨frobeniusGenPt E p, (isIsogeny_iff _).mpr
    ⟨isGenPt_frobeniusGenPt E p, respectsAdd_frobeniusGenPt E p⟩⟩

theorem frobeniusIsogeny_app {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    (frobeniusIsogeny E p).app P hP = frobeniusPoint E p L P :=
  map_genEval_frobeniusGenPt E p P hP

theorem comap_frobeniusIsogeny_genX :
    (frobeniusIsogeny E p).comap (genX (frobeniusTwist E p)) = genX E ^ p :=
  (frobeniusIsogeny E p).comap_genX

theorem comap_frobeniusIsogeny_genY :
    (frobeniusIsogeny E p).comap (genY (frobeniusTwist E p)) = genY E ^ p :=
  (frobeniusIsogeny E p).comap_genY

theorem fieldRange_comap_frobeniusIsogeny :
    (frobeniusIsogeny E p).comap.fieldRange = powField E p := by
  rw [← map_top_eq_fieldRange, ← adjoin_genX_genY (frobeniusTwist E p), adjoin_map, powField]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, comap_frobeniusIsogeny_genX,
    comap_frobeniusIsogeny_genY]

theorem degree_frobeniusIsogeny [PerfectRing F p] : (frobeniusIsogeny E p).degree = p := by
  have h := congrArg (fun M : IntermediateField F E.toAffine.FunctionField =>
    Module.finrank M E.toAffine.FunctionField) (fieldRange_comap_frobeniusIsogeny E p)
  rw [Isogeny.degree]
  exact h.trans (finrank_powField E p)

end FrobeniusIsogeny
end

section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (p : ℕ)
  [hp : Fact p.Prime] [CharP F p]

omit [E.IsElliptic] in
theorem exists_frobeniusPoint_eq {L : Type*} [Field L] [Algebra F L] [CharP L p] [PerfectRing L p]
    (P : ((frobeniusTwist E p).baseChange L).toAffine.Point) :
    ∃ R : (E.baseChange L).toAffine.Point, frobeniusPoint E p L R = P := by
  have hroot : ∀ z : L, ∃ w : L, w ^ p = z := fun z =>
    ⟨(frobeniusEquiv L p).symm z, by rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]⟩
  rcases P with (_ | ⟨u, v, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨u', rfl⟩ := hroot u
    obtain ⟨v', rfl⟩ := hroot v
    exact ⟨.some u' v' ((nonsingular_pow_iff E p).mp h), rfl⟩

variable [PerfectRing F p]

theorem fieldRange_le_powField_of_not_isSeparable (φ : Isogeny E E') (hφ : ¬ φ.IsSeparable) :
    φ.comap.fieldRange ≤ powField E p := by
  have := φ.finiteDimensional
  apply le_powField_of_finSepDegree_lt E p
  exact lt_of_le_of_ne (Field.finSepDegree_le_finrank _ _)
    fun h => hφ ((Field.finSepDegree_eq_finrank_iff _ _).mp h)

theorem exists_comp_frobeniusIsogeny_eq (φ : Isogeny E E') (hφ : ¬ φ.IsSeparable) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', ψ.comp (frobeniusIsogeny E p) = φ := by
  classical
  have hle := fieldRange_le_powField_of_not_isSeparable p φ hφ
  rw [← fieldRange_comap_frobeniusIsogeny E p] at hle
  obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.mp (hle (AlgHom.mem_fieldRange.mpr ⟨genX E', φ.comap_genX⟩))
  obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hle (AlgHom.mem_fieldRange.mpr ⟨genY E', φ.comap_genY⟩))
  have hns : (E'.baseChange (frobeniusTwist E p).toAffine.FunctionField).toAffine.Nonsingular a b :=
    (E'.toAffine.baseChange_nonsingular (frobeniusIsogeny E p).comap.toRingHom.injective a b).mp (by
      rw [ha, hb]
      exact φ.nonsingular)
  have ht : Transcendental F a := fun h => φ.transcendental_alt (by rw [← ha]; exact h.algHom (frobeniusIsogeny E p).comap)
  set Q : (E'.baseChange (frobeniusTwist E p).toAffine.FunctionField).toAffine.Point :=
    .some a b hns with hQdef
  have hQ : Point.map (frobeniusIsogeny E p).comap Q = φ.1 := by
    rw [φ.val_eq_some_x_y, hQdef, Point.map_some]
    simp only [Point.some.injEq]
    exact ⟨ha, hb⟩

  have key : ∀ {L : Type u} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
      (R : (E.baseChange L).toAffine.Point) (hR : IsGenPt E R)
      (h' : IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L R)),
      Point.map (genEval _ (frobeniusPoint E p L R) h') Q = φ.app R hR := by
    intro L _ _ _ _ R hR h'
    rw [genEval_congr _ (frobeniusIsogeny_app E p R hR).symm h'
      ((frobeniusIsogeny E p).isGenPt_app R hR), Isogeny.genEval_app, ← Point.map_map, hQ]
    rfl
  have hresp : RespectsAdd (frobeniusTwist E p) E' Q := by
    rw [respectsAdd_iff]
    intro L _ _ _ P₁ P₂ h₁ h₂ h₃
    have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
    have : CharP (AlgebraicClosure L) p :=
      charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure L)).injective p
    let σ : L →ₐ[F] AlgebraicClosure L := IsScalarTower.toAlgHom F L (AlgebraicClosure L)
    obtain ⟨R₁, e₁⟩ := exists_frobeniusPoint_eq (E := E) p (Point.map σ P₁)
    obtain ⟨R₂, e₂⟩ := exists_frobeniusPoint_eq (E := E) p (Point.map σ P₂)
    have e₃ : frobeniusPoint E p _ (R₁ + R₂) = Point.map σ (P₁ + P₂) := by
      rw [frobeniusPoint_add, e₁, e₂, map_add (f := _)]
    have gen : ∀ {R P} (hP : IsGenPt (frobeniusTwist E p) P)
        (e : frobeniusPoint E p (AlgebraicClosure L) R = Point.map σ P), IsGenPt E R :=
      fun hP e => (isGenPt_frobeniusPoint_iff E p _).mp (e ▸ isGenPt_map _ σ hP)
    have step : ∀ (P : ((frobeniusTwist E p).baseChange L).toAffine.Point)
        (hP : IsGenPt (frobeniusTwist E p) P) (R : (E.baseChange (AlgebraicClosure L)).toAffine.Point)
        (e : frobeniusPoint E p _ R = Point.map σ P),
        Point.map σ (Point.map (genEval _ P hP) Q) = φ.app R (gen hP e) := by
      intro P hP R e
      rw [Point.map_map, ← genEval_map, genEval_congr _ e.symm _
        ((isGenPt_frobeniusPoint_iff E p R).mpr (gen hP e))]
      exact key R _ _
    apply Point.map_injective (W' := E') σ
    rw [map_add (f := _), step _ h₁ R₁ e₁, step _ h₂ R₂ e₂, step _ h₃ _ e₃]
    exact φ.app_add (gen h₁ e₁) (gen h₂ e₂) (gen h₃ e₃)
  refine ⟨⟨Q, (isIsogeny_iff _).mpr ⟨ht, hresp⟩⟩, Isogeny.ext' ?_⟩
  exact (Isogeny.comp_val _ _).trans hQ

theorem exists_eq_comp_frobeniusIsogeny (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', φ = ψ.comp (frobeniusIsogeny E p) ∧
      φ.degree = ψ.degree * p ∧ ψ.degree = φ.degree / p := by
  obtain ⟨ψ, hψ⟩ := exists_comp_frobeniusIsogeny_eq p φ
    fun h => (isSeparable_iff_isogenyPullback_ne_zero φ).mp h hφ
  have hd : φ.degree = ψ.degree * p := by
    rw [← hψ, Isogeny.degree_comp, degree_frobeniusIsogeny]
  exact ⟨ψ, hψ.symm, hd, by rw [hd, Nat.mul_div_cancel _ hp.out.pos]⟩

omit [E.IsElliptic] [CharP F p] [PerfectRing F p] hp in
theorem Isogeny.comap_bijective_of_degree_eq_one {E₁ E₂ : WeierstrassCurve F} [E₁.IsElliptic]
    [E₂.IsElliptic] (ψ : Isogeny E₁ E₂) (h : ψ.degree = 1) : Function.Bijective ψ.comap := by
  refine ⟨ψ.comap.toRingHom.injective, fun z => ?_⟩
  have htop : (⊤ : IntermediateField F E₁.toAffine.FunctionField) ≤ ψ.comap.fieldRange := by
    rw [← relfinrank_eq_one_iff, relfinrank_top_right]
    exact h
  exact AlgHom.mem_fieldRange.mp (htop trivial)

theorem exists_isomorphism_of_degree_eq (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) (hdeg : φ.degree = p) :
    ∃ ψ : Isogeny (frobeniusTwist E p) E', φ = ψ.comp (frobeniusIsogeny E p) ∧ ψ.degree = 1 ∧
      Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny (frobeniusTwist E p) 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny E' 1 one_ne_zero := by
  obtain ⟨ψ, hψ, hd, -⟩ := exists_eq_comp_frobeniusIsogeny p φ hφ
  have h1 : ψ.degree = 1 := by
    rw [hdeg] at hd
    exact (Nat.mul_eq_right hp.out.ne_zero).mp hd.symm
  refine ⟨ψ, hψ, h1, Isogeny.comap_bijective_of_degree_eq_one ψ h1, ?_, ?_⟩
  · rw [dualOver_comp]
    congr 1
    simp [h1]
  · rw [comp_dualOver]
    congr 1
    simp [h1]
end

section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero IntermediateField GroundTheory.Arith.Abelian

universe u

section Basis

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem eq_zero_of_algebraMap_add_mul_genY {P Q : F[X]}
    (h : algebraMap F[X] W.toAffine.FunctionField P +
      algebraMap F[X] W.toAffine.FunctionField Q * genY W = 0) : P = 0 ∧ Q = 0 := by
  rw [← algebraMap_smul_basis] at h
  have h' := (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField)
    (h.trans (map_zero _).symm)
  exact smul_basis_eq_zero h'

theorem eq_of_equation_genX_genY {W' : WeierstrassCurve F}
    (h : (W'.baseChange W.toAffine.FunctionField).toAffine.Equation (genX W) (genY W)) :
    W' = W := by
  have eW := genY_sq_add W
  have eW' := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eW'
  set P : F[X] := -(C (W.a₂ - W'.a₂) * X ^ 2 + C (W.a₄ - W'.a₄) * X + C (W.a₆ - W'.a₆)) with hP
  set Q : F[X] := C (W.a₁ - W'.a₁) * X + C (W.a₃ - W'.a₃) with hQ
  have key : algebraMap F[X] W.toAffine.FunctionField P +
      algebraMap F[X] W.toAffine.FunctionField Q * genY W = 0 := by
    simp only [hP, hQ, map_add (f := _), map_mul, map_neg, map_pow, algebraMap_C_functionField, ← genX_eq,
      map_sub]
    linear_combination eW - eW'
  obtain ⟨hP0, hQ0⟩ := eq_zero_of_algebraMap_add_mul_genY W key
  have c2 := congrArg (AddMonoidAlgebra.coeff · 2) hP0
  have c1 := congrArg (AddMonoidAlgebra.coeff · 1) hP0
  have c0 := congrArg (AddMonoidAlgebra.coeff · 0) hP0
  have d1 := congrArg (AddMonoidAlgebra.coeff · 1) hQ0
  have d0 := congrArg (AddMonoidAlgebra.coeff · 0) hQ0
  simp [hP, hQ, coeff_X, coeff_C, coeff_X_pow, -map_sub] at c2 c1 c0 d1 d0
  ext
  · linear_combination -d1
  · linear_combination c2
  · linear_combination -d0
  · linear_combination c1
  · linear_combination c0

end Basis

section Poles

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {W : WeierstrassCurve F}
  [W.IsElliptic]

omit [DecidableEq F] in
theorem valuationPoint_genY_le_one {P : W.toAffine.Point} (hP : P ≠ 0) :
    valuationPoint W P (genY W) ≤ 1 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    show (heightOneOfNonsingular h).valuation _ (algebraMap _ _ _) ≤ 1
    exact HeightOneSpectrum.valuation_le_one _ _

theorem exists_algebraMap_eq_of_valuationPoint_le_one {f : W.toAffine.FunctionField}
    (h : ∀ P : W.toAffine.Point, P ≠ 0 → valuationPoint W P f ≤ 1) :
    ∃ p q : F[X], algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X) = f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one W.toAffine.FunctionField f
    fun v => by rw [← valuationPoint_pointOfIdeal]; exact h _ (pointOfIdeal_ne_zero W v)
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  exact ⟨p, q, rfl⟩

theorem exists_eq_linear_of_valuation {f : W.toAffine.FunctionField}
    (h : ∀ P : W.toAffine.Point, P ≠ 0 → valuationPoint W P f ≤ 1)
    (h0 : valuationInfty W f = exp 2) :
    ∃ α β : F, α ≠ 0 ∧ f = algebraMap F W.toAffine.FunctionField α * genX W +
      algebraMap F W.toAffine.FunctionField β := by
  obtain ⟨p, q, rfl⟩ := exists_algebraMap_eq_of_valuationPoint_le_one h
  have ha : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    intro h'
    rw [h', map_zero, map_zero] at h0
    exact exp_ne_zero h0.symm
  rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha, exp_inj] at h0
  by_cases hq : q = 0
  · subst hq
    rw [natDegree_norm_smul_basis_of_q_eq_zero] at h0
    have hp1 : p.natDegree = 1 := by omega
    obtain ⟨c₁, c₀, rfl⟩ : ∃ c₁ c₀ : F, p = C c₁ * X + C c₀ :=
      ⟨_, _, eq_X_add_C_of_natDegree_le_one hp1.le⟩
    refine ⟨c₁, c₀, ?_, ?_⟩
    · rintro rfl
      simp at hp1
    · rw [algebraMap_smul_basis, map_zero, zero_mul, add_zero]
      simp only [map_add (f := _), map_mul, algebraMap_C_functionField, ← genX_eq]
  · exfalso
    by_cases hp : p = 0
    · subst hp
      rw [natDegree_norm_smul_basis_of_p_eq_zero hq] at h0
      omega
    · rw [natDegree_norm_smul_basis_of_ne_zero hp hq] at h0
      have := le_max_right (2 * p.natDegree) (2 * q.natDegree + 3)
      omega

theorem exists_eq_genY_form_of_valuation {g : W.toAffine.FunctionField}
    (h : ∀ P : W.toAffine.Point, P ≠ 0 → valuationPoint W P g ≤ 1)
    (h0 : valuationInfty W g = exp 3) :
    ∃ γ δ ε : F, γ ≠ 0 ∧ g = algebraMap F W.toAffine.FunctionField γ * genY W +
      algebraMap F W.toAffine.FunctionField δ * genX W + algebraMap F W.toAffine.FunctionField ε := by
  obtain ⟨p, q, rfl⟩ := exists_algebraMap_eq_of_valuationPoint_le_one h
  have ha : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    intro h'
    rw [h', map_zero, map_zero] at h0
    exact exp_ne_zero h0.symm
  rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha, exp_inj] at h0
  by_cases hq : q = 0
  · subst hq
    rw [natDegree_norm_smul_basis_of_q_eq_zero] at h0
    omega
  have hdeg : q.natDegree = 0 ∧ p.natDegree ≤ 1 := by
    by_cases hp : p = 0
    · subst hp
      rw [natDegree_norm_smul_basis_of_p_eq_zero hq] at h0
      exact ⟨by omega, by simp⟩
    · rw [natDegree_norm_smul_basis_of_ne_zero hp hq] at h0
      have h1 := le_max_left (2 * p.natDegree) (2 * q.natDegree + 3)
      have h2 := le_max_right (2 * p.natDegree) (2 * q.natDegree + 3)
      omega
  obtain ⟨c, rfl⟩ : ∃ c : F, q = C c := ⟨_, eq_C_of_natDegree_eq_zero hdeg.1⟩
  obtain ⟨c₁, c₀, rfl⟩ : ∃ c₁ c₀ : F, p = C c₁ * X + C c₀ :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one hdeg.2⟩
  refine ⟨c, c₁, c₀, ?_, ?_⟩
  · rintro rfl
    exact hq (map_zero C)
  · rw [algebraMap_smul_basis]
    simp only [map_add (f := _), map_mul, algebraMap_C_functionField, ← genX_eq]
    ring

end Poles

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem exists_coeffs_of_degree_eq_one_of_isAlgClosed (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ α β γ δ ε : F, α ≠ 0 ∧ γ ≠ 0 ∧
      ψ.x = algebraMap F A.toAffine.FunctionField α * genX A +
        algebraMap F A.toAffine.FunctionField β ∧
      ψ.y = algebraMap F A.toAffine.FunctionField γ * genY A +
        algebraMap F A.toAffine.FunctionField δ * genX A +
        algebraMap F A.toAffine.FunctionField ε ∧
      γ ^ 2 = α ^ 3 ∧
      γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2 = 0 ∧
      γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
        2 * B.a₂ * α * β - B.a₄ * α = 0 ∧
      γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β -
        B.a₆ = 0 ∧
      2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁ = 0 ∧
      2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃ = 0 := by
  have hmul := ψ.ramIdx_mul_card_ker
  rw [h] at hmul
  have hram : ψ.ramIdx = 1 := (mul_eq_one.mp hmul).1
  have hbot : ψ.pointHom.ker = ⊥ := AddSubgroup.card_eq_one.mp (mul_eq_one.mp hmul).2
  have hne : ∀ R : A.toAffine.Point, R ≠ 0 → ψ.pointMap R ≠ 0 := by
    intro R hR h0
    have hR' : R ∈ ψ.pointHom.ker := by
      rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]; exact h0
    rw [hbot, AddSubgroup.mem_bot] at hR'
    exact hR hR'
  have hval : ∀ (R : A.toAffine.Point) (f : B.toAffine.FunctionField),
      valuationPoint A R (ψ.comap f) = valuationPoint B (ψ.pointMap R) f := by
    intro R f
    rw [ψ.valuationPoint_comap, hram, pow_one]
  have h0 : ψ.pointMap 0 = 0 := map_zero ψ.pointHom
  have hinf : ∀ f : B.toAffine.FunctionField, valuationInfty A (ψ.comap f) = valuationInfty B f := by
    intro f
    rw [← valuationPoint_zero_eq, hval, h0, valuationPoint_zero_eq]
  obtain ⟨α, β, hα, hf⟩ := exists_eq_linear_of_valuation (W := A) (f := ψ.comap (genX B))
    (fun R hR => by rw [hval]; exact valuationPoint_genX_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genX B])
  obtain ⟨γ, δ, ε, hγ, hg⟩ := exists_eq_genY_form_of_valuation (W := A) (g := ψ.comap (genY B))
    (fun R hR => by rw [hval]; exact valuationPoint_genY_le_one (hne R hR))
    (by rw [hinf, valuationInfty_genY B])
  set ι := algebraMap F A.toAffine.FunctionField with hι
  have hx : ψ.x = ι α * genX A + ι β := by rw [← ψ.comap_genX]; exact hf
  have hy : ψ.y = ι γ * genY A + ι δ * genX A + ι ε := by rw [← ψ.comap_genY]; exact hg
  have hN := ψ.nonsingular
  have eB := (equation_iff _ _).mp hN.1
  rw [hx, hy] at eB
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at eB
  have eA := genY_sq_add A
  set P : F[X] := C (γ ^ 2 - α ^ 3) * X ^ 3 +
    C (γ ^ 2 * A.a₂ + δ ^ 2 + B.a₁ * α * δ - 3 * α ^ 2 * β - B.a₂ * α ^ 2) * X ^ 2 +
    C (γ ^ 2 * A.a₄ + 2 * δ * ε + B.a₁ * (α * ε + β * δ) + B.a₃ * δ - 3 * α * β ^ 2 -
      2 * B.a₂ * α * β - B.a₄ * α) * X +
    C (γ ^ 2 * A.a₆ + ε ^ 2 + B.a₁ * β * ε + B.a₃ * ε - β ^ 3 - B.a₂ * β ^ 2 - B.a₄ * β - B.a₆)
    with hP
  set Q : F[X] := C (2 * γ * δ + B.a₁ * γ * α - γ ^ 2 * A.a₁) * X +
    C (2 * γ * ε + B.a₁ * γ * β + B.a₃ * γ - γ ^ 2 * A.a₃) with hQ
  have key : algebraMap F[X] A.toAffine.FunctionField P +
      algebraMap F[X] A.toAffine.FunctionField Q * genY A = 0 := by
    simp only [hP, hQ, map_add (f := _), map_mul, map_pow, algebraMap_C_functionField, ← genX_eq, map_sub,
      map_ofNat]
    linear_combination eB - ι γ ^ 2 * eA
  obtain ⟨hP0, hQ0⟩ := eq_zero_of_algebraMap_add_mul_genY A key
  have c3 := congrArg (AddMonoidAlgebra.coeff · 3) hP0
  have c2 := congrArg (AddMonoidAlgebra.coeff · 2) hP0
  have c1 := congrArg (AddMonoidAlgebra.coeff · 1) hP0
  have c0 := congrArg (AddMonoidAlgebra.coeff · 0) hP0
  have d1 := congrArg (AddMonoidAlgebra.coeff · 1) hQ0
  have d0 := congrArg (AddMonoidAlgebra.coeff · 0) hQ0
  simp only [hP, hQ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c3 c2 c1 c0 d1 d0
  norm_num at c3 c2 c1 c0 d1 d0
  refine ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, by linear_combination c3, by linear_combination c2,
    by linear_combination c1, by linear_combination c0, by linear_combination d1,
    by linear_combination d0⟩

theorem exists_variableChange_of_degree_eq_one_of_isAlgClosed (ψ : Isogeny A B)
    (h : ψ.degree = 1) : ∃ C : VariableChange F, C • B = A := by
  obtain ⟨α, β, γ, δ, ε, hα, hγ, hx, hy, hc3, -, -, -, -, -⟩ :=
    exists_coeffs_of_degree_eq_one_of_isAlgClosed ψ h
  set ι := algebraMap F A.toAffine.FunctionField with hι
  have hN := ψ.nonsingular
  have hu2 : (α / γ) ^ 2 * α = 1 := by
    field_simp
    linear_combination -hc3
  have hu3 : (α / γ) ^ 3 * γ = 1 := by
    field_simp
    linear_combination -hc3
  have hδ : ι (δ / α) * ι α = ι δ := by rw [← map_mul, div_mul_cancel₀ δ hα]
  have hu2' : ι (α / γ) ^ 2 * ι α = 1 := by rw [← map_pow, ← map_mul, hu2, map_one]
  have hu3' : ι (α / γ) ^ 3 * ι γ = 1 := by rw [← map_pow, ← map_mul, hu3, map_one]
  let Cv : VariableChange F := ⟨Units.mk0 (γ / α) (div_ne_zero hγ hα), β, δ / α, ε⟩
  refine ⟨Cv, eq_of_equation_genX_genY A ?_⟩
  have hV := (nonsingular_variableChange (Cv.map ι) (B.baseChange A.toAffine.FunctionField) hN).1
  have hcurve : (Cv.map ι) • (B.baseChange A.toAffine.FunctionField) =
      (Cv • B).baseChange A.toAffine.FunctionField :=
    map_variableChange B Cv ι
  rw [hcurve] at hV
  have hX : (↑(Cv.map ι).u⁻¹ : A.toAffine.FunctionField) ^ 2 * (ψ.x - (Cv.map ι).r) = genX A := by
    show ι ((γ / α)⁻¹) ^ 2 * (ψ.x - ι β) = genX A
    rw [hx, inv_div]
    linear_combination genX A * hu2'
  have hY : (↑(Cv.map ι).u⁻¹ : A.toAffine.FunctionField) ^ 3 *
      (ψ.y - (Cv.map ι).s * (ψ.x - (Cv.map ι).r) - (Cv.map ι).t) = genY A := by
    show ι ((γ / α)⁻¹) ^ 3 * (ψ.y - ι (δ / α) * (ψ.x - ι β) - ι ε) = genY A
    rw [hx, hy, inv_div]
    linear_combination genY A * hu3' - ι (α / γ) ^ 3 * genX A * hδ
  rw [hX, hY] at hV
  exact hV

end AlgClosed

section General

variable {F : Type u} [Field F]

theorem j_eq_of_variableChange_eq {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
    (C : VariableChange F) (h : C • W = W') : W'.j = W.j := by
  subst h
  exact variableChange_j _ _

theorem j_eq_of_degree_eq_one {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
    (ψ : Isogeny A B) (h : ψ.degree = 1) : B.j = A.j := by
  classical
  have hd : (isogBaseChange (F' := AlgebraicClosure F) ψ).degree = 1 := by
    rw [degree_isogBaseChange, h]
  obtain ⟨C, hC⟩ := exists_variableChange_of_degree_eq_one_of_isAlgClosed _ hd
  have hj : (A.baseChange (AlgebraicClosure F)).j = (B.baseChange (AlgebraicClosure F)).j :=
    j_eq_of_variableChange_eq C hC
  have eA : (A.baseChange (AlgebraicClosure F)).j = algebraMap F (AlgebraicClosure F) A.j :=
    map_j _ _
  have eB : (B.baseChange (AlgebraicClosure F)).j = algebraMap F (AlgebraicClosure F) B.j :=
    map_j _ _
  rw [eA, eB] at hj
  exact ((algebraMap F (AlgebraicClosure F)).injective hj).symm

theorem j_eq_pow_of_isogenyPullback_eq_zero {E E' : WeierstrassCurve F} [E.IsElliptic]
    [E'.IsElliptic] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') = 0) (hdeg : φ.degree = p) :
    E'.j = E.j ^ p := by
  obtain ⟨ψ, -, h1, -⟩ := exists_isomorphism_of_degree_eq p φ hφ hdeg
  rw [j_eq_of_degree_eq_one ψ h1, j_frobeniusTwist]

end General
end

end GroundTheory.Global
