module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
public import GroundTheory.AutomorphicForms.GL2.GJFEBlock
public import GroundTheory.AutomorphicForms.GL2.GJLocalFECoeff
public import GroundTheory.AutomorphicForms.GL2.GJLocalFEGamma
import GroundTheory.AutomorphicForms.GL2.GJZetaCore
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.SmoothRepSchur
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxBlock
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MeasureTheory Polynomial GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel


namespace UpperTheory.V.Z.Gam

theorem ldBlock_of (hL : LdLaurent) (hM : LdMean) (hT : LdTate) : LdBlock := by
  intro F _ _ _ _ _ _ m _ _ _ μ _ H _ _ _ _ _ _ _ W _ _ σ hσ hirr α hα0 hα hsupp ψ hψ hψ1 γ hFE
  have hShape := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.gxBlock_of hL hM hT
    F m μ H W σ hσ hirr α hα0 hα hsupp ψ hψ hψ1 γ hFE
  obtain ⟨c, j, hc, hγ⟩ := hShape
  by_cases h : m = 1 ∧ ∀ g ∈ integralGL F m, σ (g, 1) = 1
  · refine ⟨1 - C α * X, c, j, by simp, ?_, hc, by simpa only [ite_eq_left h] using hγ⟩
    rw [ite_eq_left h, show (1 - C α * X : ℂ[X]) = C (-α) * X + C 1 by simp; ring]
    exact natDegree_linear (neg_ne_zero.2 hα0)
  · exact ⟨1, c, j, by simp, by simp [h], hc, by simpa only [ite_eq_right h] using hγ⟩

end UpperTheory.V.Z.Gam
