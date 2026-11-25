module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibility
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValuesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegralStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.DatumVec\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector\nimport Formalism.LocalToGlobal.IndefiniteReal.LinksDefs\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.conj_principalFractional_integral_idempotentSum : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IdemIntegral.conj_mem_intAf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.DatumVec\npublic import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs\npublic import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.selfDual_vector_pairs_integral_frame_columns : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PairIntegral.pair_mem_intAf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.OneMapT\npublic import Formalism.LocalToGlobal.IndefiniteReal.FWTie\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesFieldStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeightsStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValuesStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegralStatement\npublic import Formalism.LocalToGlobal.ProjectiveLattices.ThClass\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement\npublic import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.FreeModule.IdealQuotient\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace GlobalTheory.PinnedData

variable {D : D7}

theorem adForms_ext {Gr Γ : Type} [Group Gr] [Group Γ] (ι : Γ →* Gr) {Wc : Type} [NormedAddCommGroup Wc]
    [InnerProductSpace ℂ Wc] (ρ : Γ →* Module.End ℂ Wc) {J J' : Subgroup Gr} (χ : J →* ℂˣ) (hle : J' ≤ J) {I : Type}
    {y : I → Gr} (hy : Bridge.IsReps ι J' y) {f f' : Gr → Wc} (h1 : f ∈ Bridge.AdForms ι ρ J χ)
    (h2 : f' ∈ Bridge.AdForms ι ρ J χ) (h : ∀ k, f (y k) = f' (y k)) : f = f' := by
  funext g
  obtain ⟨k, ⟨γ, u, rfl⟩, -⟩ := hy g
  have m1 := h1 γ (y k) ⟨u, hle u.2⟩
  have m2 := h2 γ (y k) ⟨u, hle u.2⟩
  rw [h k] at m1
  exact m1.trans m2.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)



theorem exists_thAd {F : Face D A} (hR : R.Char F) (t : T0) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) {Cl : Type} (h : Cl → GA D (Vc D i)) {J' : Subgroup (Bridge.Gf (Vc D i))}
    (hle : J' ≤ levJ R i t) (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)))
    (v₀ : (R.MW i (sg0 D A)).Vec) : ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.models.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_ext _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y)) (hrange.le (LinearMap.mem_range_self _ y'))
      fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dite_eq_left hx]
  rw [huniq _ _ _ hx.choose_spec hy]

alias latEmb_iotaW := _root_.GlobalTheory.LevelAction.latEmb_iotaW



end GlobalTheory.PinnedData
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField =====
