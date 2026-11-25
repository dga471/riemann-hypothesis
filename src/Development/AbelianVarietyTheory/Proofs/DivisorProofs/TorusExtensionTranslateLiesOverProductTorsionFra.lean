module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullMulValue
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny, Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkToAkULevelField, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.Mum GlobalTheory.UT GlobalTheory.ZH

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\n\n"}
namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

theorem qkToAkU_level_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN p q x hy hg hx
  obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
  obtain rfl := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk p x x₀ hx
    ((indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1 (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl))
  exact (indAtTransl_any hL R I hI D A G hG U F (hN ▸ Nat.mul_pos hk hn |> fun _ => N)
    (hN ▸ Nat.mul_pos hk hn) q x).1 (h₀ n N hn hN q hy hg)

end GlobalTheory.DvrAnyChar
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkToAkULevelField =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkToAkULevelField", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherianStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny\nimport Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem\n\n"}
namespace GlobalTheory.Poinc.Tors.AnyField
open GlobalTheory.TorsionAnyChar

theorem qkToAkU_level_field : LL → FieldUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ k n N hk hn hN p q x hy hg hx
  have hf : (algebraMap F (AlgebraicClosure F)).comp (algebraMap (FractionRing R) F) = algebraMap _ _ :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  obtain ⟨p', hp⟩ := qkExtExists R D.toPre F (AlgebraicClosure F) (algebraMap F _) (fun r => DFunLike.congr_fun hf r) k p
  obtain ⟨q', hq⟩ := qkExtExists R D.toPre F (AlgebraicClosure F) (algebraMap F _) (fun r => DFunLike.congr_fun hf r) N q
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U (hN ▸ Nat.mul_pos hk hn) hq x).2
    (DvrAnyChar.qkToAkU_level_any hL R I hI D A G hG U _ k n N hk hn hN p' q' _ (by rw [hq.1, hp.1, hy])
      (((TorusExt.eq_gtExt_iff _ hf _ _).2 hq.2).trans
        (((TorusExt.eq_gtExt_iff _ hf _ _).2 hp.2).trans (congrArg (TorusExt.gtExt D.toPre _ hf) hg).symm).symm)
      ((TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hk hp x).1 hx))

theorem exists_sumI_smul {R : Type} [CommRing R] {I : Ideal R} [IsAdicComplete I R] {E Ix : Type} [AddCommGroup E]
    [Module R E] {x : Ix → E} {s : E} (h : SumI I x s) (a : Ix → R) : ∃ s', SumI I (fun i => a i • x i) s' := by
  classical
  obtain ⟨N, hN, hs, hx, hS⟩ := h
  choose S hS using hS
  have h1 : ∀ n (T T' : Finset Ix), S n ⊆ T → T ⊆ T' → ∑ i ∈ T', a i • x i - ∑ i ∈ T, a i • x i ∈ I ^ n • N :=
    fun n T T' h h' => by
      rw [← Finset.sum_sdiff h', add_sub_cancel_right]
      exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (by
        have := sub_mem (hS n (S n) le_rfl) (hS n (insert i (S n)) (Finset.subset_insert _ _))
        rwa [Finset.sum_insert (fun hi' => (Finset.mem_sdiff.1 hi).2 (h hi')),
          sub_sub_sub_cancel_left, add_sub_cancel_right] at this)
  have : Module.Finite R N := Module.Finite.iff_fg.2 hN
  let T : ℕ → Finset Ix := fun n => (Finset.range (n + 1)).biUnion S
  have hT : ∀ n, S n ⊆ T n := fun n => Finset.subset_biUnion_of_mem S (Finset.self_mem_range_succ n)
  let f : ℕ → N := fun n => ⟨∑ i ∈ T n, a i • x i, Submodule.sum_mem _ fun i _ => N.smul_mem _ (hx i)⟩
  obtain ⟨l, hl⟩ := (T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I N).prec' f (fun {m n} h => by
    rw [SModEq.sub_mem, Submodule.mem_smul_top_iff, ← neg_mem_iff]
    simpa [f] using h1 m _ _ (hT m) (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (by lia))))
  refine ⟨l, N, hN, l.2, fun i => N.smul_mem _ (hx i), fun n => ⟨T n, fun T' h => ?_⟩⟩
  have e := hl n
  rw [SModEq.sub_mem, Submodule.mem_smul_top_iff] at e
  have := add_mem (h1 n _ _ (hT n) h) e
  rw [← neg_mem_iff]
  convert this using 1; simp [f]

theorem exists_sumF_twist {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) {Ix : Type}
    {x : Ix → FractionRing R} {s : FractionRing R} (h : SumF I (FractionRing R) x s) {n : ℕ} (hn : 1 ≤ n)
    (a : Ix → FractionRing R) (ha : ∀ i, a i ^ n = 1) : ∃ s', SumF I (FractionRing R) (fun i => a i * x i) s' := by
  obtain ⟨-, -, hc, hI⟩ := hI
  have : ∀ i, ∃ b : R, algebraMap R (FractionRing R) b = a i := fun i =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow hn (by rw [ha]; exact isIntegral_one))
  choose b hb using this
  let : Module R (FractionRing R) := Module.compHom _ (algebraMap R (FractionRing R))
  obtain ⟨s', hs'⟩ := exists_sumI_smul h b
  exact ⟨s', by simp only [← hb]; exact hs'⟩

end GlobalTheory.Poinc.Tors.AnyField
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkToAkULevelField =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkToAkULevelField\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullMulValue\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms\nimport Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus\npublic import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull\nimport Development.AbelianVarietyTheory.Definitions.Divisors.FromBase\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny\n\n"}
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open ReciprocityTheory.AnForm.R GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Tors.Translate
open GlobalTheory.UT.CoefBasic GlobalTheory.AdicSum GlobalTheory.Poinc.Tors.AnyField GlobalTheory.Poinc.Tors.ValPair

section Pull
open GlobalTheory.UT.PullMul

theorem pull_mul_all {S : Scheme.{0}} (P : PolAV S) (T : Over S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (n k k' : ℕ)
    (hk : k' = k * n ^ 2)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) (hN : IsNormMul P.A P.L ρ n α₀) (ψ : T ⊗ P.A ⟶ T ⊗ P.A) (m : T ⊗ P.A ⟶ P.A)
    (hm : ψ ≫ snd _ _ = m) (hψ : ψ ≫ fst _ _ = fst _ _) (hmn : m = snd _ _ ≫ (𝟙 P.A ^ n)) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, m.left] ![(k' : ℤ), -(k : ℤ)]), α.IsGen ∧
      LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T ((k' : ℤ) - k)) ∧
      ∀ (t : LB.Sec (LPow P.A P.L (k : ℤ) T)) (c : ∀ z : T.left, T.left.presheaf.stalk z),
        (∀ z J, Good P.L z J → VVRank.sv P.A t (ptSecT P.A 1).left z J =
          c z * (val (rigT P.A P.L ρ T (k : ℤ)) (𝟙 _) z J).val) →
        ∃ t' : LB.Sec (LPow P.A P.L (k' : ℤ) T), IsTwistPull P.A P.L ψ m hm k' k α t t' ∧
          ∀ x : T ⟶ P.A, x ^ n = 1 → ∀ z J, Good P.L z J → VVRank.sv P.A t' (ptSecT P.A x).left z J =
            c z * (val (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α₀ x.left) (rigT P.A P.L ρ T 1)) (𝟙 _) z J).val ^ k := by
  have em : (snd T P.A).left ≫ (mulA P.A n).left = m.left := by rw [hmn, Over.comp_left]
  obtain ⟨α, hα, hv⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, m.left]) (ε' := ![(k' : ℤ), -(k : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, em, hk,
        Nat.cast_mul, Nat.cast_pow]
      congr 2; ring)
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L _ _ α₀ (snd T P.A).left) k)
    (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα₀ _) k)
  have hv' : ∀ (y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      val α (ptSecT P.A y).left z J = val α₀ y.left z J ^ k := fun y z J hJ => by
    rw [hv _ _ z J hJ, val_powGen, val_pull hJ, ← Over.comp_left, ptSecT, lift_snd]
  refine ⟨α, hα, corr_of_val P.isLB fun z J hJ => ?_, fun t c ht => ?_⟩
  · have a := val_corr hJ hN T.hom
    rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow] at a
    rw [val_pull hJ, Category.id_comp, hv' 1 z J hJ, one_left, val_rigT ρ T _ _ z hJ, Category.id_comp]
    refine (congrArg (· ^ k) a).trans ?_
    change (rv ρ T.hom z J ^ ((n : ℤ) ^ 2) * (rv ρ T.hom z J)⁻¹) ^ k = rv ρ T.hom z J ^ _
    rw [← zpow_sub_one, ← zpow_natCast, ← zpow_mul, hk]; congr 1; push_cast; ring
  · obtain ⟨t', ht'⟩ := VVRank.exists_isTwistPull P.A (ψ := ψ) (hm := hm) P.isLB hα t
    refine ⟨t', ht', fun x hxn z J hJ => ?_⟩
    have e₁ : ptSecT P.A x ≫ ψ = ptSecT P.A 1 := by
      ext1
      · rw [Category.assoc, hψ, ptSecT, ptSecT, lift_fst, lift_fst]
      · rw [Category.assoc, hm, hmn, ptSecT, ptSecT, lift_snd_assoc, lift_snd, MonObj.comp_pow, Category.comp_id, hxn]
    rw [VVRank.sv_of_isTwistPull P.A ht' _ z hJ, ← Over.comp_left, e₁, ht z J hJ, hv' x z J hJ,
      val_rigT ρ T _ _ z hJ, val_mul hJ, val_pull hJ, val_rigT ρ T _ _ z hJ, Category.id_comp, zpow_one,
      mul_left_comm, ← Units.val_mul, zpow_natCast, ← mul_pow, Units.val_pow_eq_pow_val]
    simp only [Category.id_comp]

end Pull

private lemma cst_mul_stalk {R : Type} [CommRing R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (z : (TFK (R := R) F).left) (a b : F) :
    (UT.cst (R := R) F z (a * b) : (TFK (R := R) F).left.presheaf.stalk z) =
      UT.cst (R := R) F z a * UT.cst (R := R) F z b := by
  rw [cst_eq, cst_eq, cst_eq, map_mul]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

section Field
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_act_value (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (x₁ x₂ : TFK (R := R) F ⟶ A.A)
    (hx : x₂ = x₁ * θ.pt) (e₁ : FrAt x₁) (he₁ : e₁.IsGen) (e₂ : FrAt x₂) (he₂ : e₂.IsGen) :
    ∃ u : F, u ≠ 0 ∧ ∀ (t t' : SecA A F N) (c : F), IsActOf A.A A.L (N : ℤ) θ t t' → ValAt t x₂ e₂ c →
      ValAt t' x₁ e₁ (u * c) := by
  have p₁ : ptSecT A.A x₁ ≫ translPt A.A θ.pt = x₂ := by
    rw [ptSecT, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, ← Hom.mul_def, hx, mul_comm]
  have p₂ : (ptSecT A.A x₁).left ≫ (translT A.A θ.pt).left = (ptSecT A.A x₂).left := by
    rw [← Over.comp_left, translT, comp_lift, p₁, ptSecT, lift_fst]; rfl
  have e₀ : (ptSecT A.A x₁).left ≫ (snd (TFK (R := R) F) A.A).left = x₁.left := by rw [← Over.comp_left, ptSecT, lift_snd]
  have e₃ : (ptSecT A.A x₁).left ≫ (translPt A.A θ.pt).left = x₂.left := by rw [← Over.comp_left, p₁]
  obtain ⟨u, hu, hv⟩ := TWM.exists_ratio (F := F) A.isLB
    (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ θ.φ (ptSecT A.A x₁).left) (powFrame A.A A.L x₂ e₂ N))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _) (EvalLevel.powFrame_isGen x₂ e₂ he₂ N))
    (powFrame A.A A.L x₁ e₁ N) (EvalLevel.powFrame_isGen x₁ e₁ he₁ N) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
      exact (congrArg₂ (fun a b => h a ^ (N : ℤ) * (h b ^ (N : ℤ))⁻¹ * h x₂.left ^ (N : ℤ)) e₀ e₃).trans
        (inv_mul_cancel_right _ _))
  refine ⟨u, hu, fun t t' c ha ht z J hJ => ?_⟩
  have a₁ := GlobalTheory.BoxTheta.act_val θ t t' ha (ptSecT A.A x₁).left z hJ
  rw [p₂] at a₁
  have a₀ := (val_pull (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
    (ε := ![(N : ℤ), -(N : ℤ)]) hJ θ.φ (ptSecT A.A x₁).left (𝟙 _)).trans
    (congrArg (fun r => val (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
      (ε := ![(N : ℤ), -(N : ℤ)]) θ.φ r z J) (Category.id_comp _))
  have a₂ := ((Units.val_mul _ _).symm.trans (congrArg Units.val ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₀ rfl)).symm)).trans (hv _ (𝟙 _) z J hJ)
  refine a₁.trans ((congrArg _ (ht z J hJ)).trans ?_)
  change _ = UT.cst (R := R) F z (u * c) * _
  rw [cst_mul_stalk]
  refine (mul_left_comm _ _ _).trans ((congrArg _ a₂).trans ?_)
  exact (_root_.mul_assoc _ _ _).symm.trans
    (congrArg₂ (fun a b : (TFK (R := R) F).left.presheaf.stalk z => a * b) (_root_.mul_comm _ _) rfl)

theorem value_at_level (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen)
    {g₁ g₂ : GtPtF D.toPre F} {w₁ : Frm D.toPre F 1 g₁.b} (hw₁ : w₁.IsGen) {x₁ x₂ : TFK (R := R) F ⟶ A.A} {e₁ : FrAt x₁}
    (he₁ : e₁.IsGen) (H : LiesOver U.toUnifPre w₀ g₁ w₁ x₁ e₁) {N : ℕ} (hN1 : 1 ≤ N) (q : QkPt D.toPre F N)
    (x : TFK (R := R) F ⟶ A.A) (hx : QkToAkU U.toUnifPre F N q x) (hadd : g₁.IsAdd q.g g₂) (hx₂ : x₂ = x₁ * x)
    (e : FrAt x₂) (he : e.IsGen) (w : Frm D.toPre F N g₂.b) (hw : w.IsGen) :
    ∃ κ : F, κ ≠ 0 ∧ ∀ (t : SecA A F N) s (c : F), U.ExpandsF F N w₀ t s → ValAt t x₂ e c →
      SumF I F (coef s g₂ w) (κ * c) := by
  have hL := GlobalTheory.firstFiveLaws
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  have : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hw₀
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := R) F) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := exists_act_value N θ x₁ x₂ hx₂ e₁ he₁ e he
  obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w₁ hw₁ N
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.TorsionAnyChar.coefPhi_field hL R _ hB D F N hN1 q w' hw' g₁ g₂ hadd W hW
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic R D.toPre F N g₂).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.TorsionAnyChar.expBijF_any hL R _ hB D A G hG U).1 F N hN1 w₀ hw₀).1 t'
  have h₂ := ((sumF_calculus R I hB F _ _ (fun _ => 0) _ 0).2.2 _ (fun β => β + q.y) (add_left_injective _)
    fun β hβ => absurd ⟨β - q.y, sub_add_cancel _ _⟩ hβ).2 (H N hN1 W hWv hW t' s' (u * c) hs' (hval t t' c ht' hc'))
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' W ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hW, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := sumF_smul hB d h₂
  simp only [Function.comp_apply, h₃, ← hdc] at h₄
  rwa [_root_.mul_assoc]

theorem isTorsFrame_of_liesOver [CharZero R] (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G)
    {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {n : ℕ} (hn : 1 ≤ n)
    {g₁ g₀ g₂ o : GtPtF D.toPre F} (ho : GtPtF.IsNsmul n g₁ o) {w₁ : Frm D.toPre F 1 g₁.b} (hw₁ : w₁.IsGen)
    {x₁ x₂ : TFK (R := R) F ⟶ A.A} {e₁ : FrAt x₁} (he₁ : IsTorsFrame A ρ n x₁ e₁)
    (H₁ : LiesOver U.toUnifPre w₀ g₁ w₁ x₁ e₁) {χ : Multiplicative D.toPre.X →* Fˣ} (hχ : χ ^ n = 1) (ht : IsTor χ g₀)
    (hadd : g₁.IsAdd g₀ g₂) {w₂ : Frm D.toPre F 1 g₂.b} (hw₂ : w₂.IsGen)
    (hww : ∀ z J, Good D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w₁ (𝟙 _) z J) (hx₂ : x₂ ^ n = 1) {e₂ : FrAt x₂}
    (he₂ : e₂.IsGen) (H₂ : LiesOver U.toUnifPre w₀ g₂ w₂ x₂ e₂) : IsTorsFrame A ρ n x₂ e₂ := by
  have hL := GlobalTheory.firstFiveLaws
  have hbij := (GlobalTheory.TorsionAnyChar.expBijF_any hL R _ hB D A G hG U).1 F
  obtain ⟨hx₁, -, α₀, hα₀, hN₀, hC⟩ := he₁
  refine ⟨hx₂, he₂, α₀, hα₀, hN₀, corr_of_val A.isLB ?_⟩
  have f₁ : x₂.left ≫ (mulA A.A n).left = (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx₂]; rfl
  obtain ⟨r, -, hr⟩ := TWM.exists_ratio (F := F) A.isLB
    (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ α₀ x₂.left) (rigT A.A A.L ρ (TFK (R := R) F) 1))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα₀ _) (EvalLevel.rigT_isGen hρ 1))
    (powFrame A.A A.L x₂ e₂ ((n : ℤ) ^ 2)) (EvalLevel.powFrame_isGen x₂ e₂ he₂ _) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_one]
      exact (congrArg₂ (fun a b => h a ^ ((n : ℤ) ^ 2) * (h b)⁻¹ * h ((TFK (R := R) F).hom ≫ eSec A.A))
        (Category.comp_id _) f₁).trans (inv_mul_cancel_right _ _))
  obtain ⟨u₀, hN⟩ := (sumF_origin hL R _ hB D A G hG U F).2.1 ρ hρ
  obtain ⟨E, eG, eA, -, eh, eAct⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R _ hB D A G hG U).1 n
  have hinj : Function.Injective E.h := fun a b h => by
    rw [eh, eh, ← natCast_zsmul, ← natCast_zsmul] at h
    exact smul_right_injective _ (by exact_mod_cast (by lia : n ≠ 0)) h
  have hAct : E.Act g₁ o := (eAct F _ _).2 ho
  have key : ∀ k : ℕ, 4 ≤ k → r ^ k = 1 := fun k hk => by
    have hpos : 1 ≤ k * n ^ 2 := Nat.mul_pos (by lia) (Nat.pow_pos hn)
    obtain ⟨⟨κ, hκ⟩, hpull⟩ := coef_twistPull hL R _ hB D A G hG U F E hinj (k * n ^ 2) k (by lia) hpos
      (by rw [eG]; exact exists_gen_mulPull_pow_unif R _ D A G U.toUnifPre n k _ rfl)
    obtain ⟨σ, c, hc, hσ⟩ := NonVan.exists_sec_ne_zero hL R A F k hk 1 (rigT A.A A.L ρ (TFK (R := R) F) 1)
      (EvalLevel.rigT_isGen hρ 1)
    rw [show powFrame A.A A.L (1 : TFK (R := R) F ⟶ A.A) (rigT A.A A.L ρ (TFK (R := R) F) 1) (k : ℤ) =
        rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ) from
      congrArg LB.Gen.mk (funext fun j => congrArg (· ^ (k : ℤ)) (zpow_one _))] at hσ
    obtain ⟨α, hα, hα', Hα⟩ := pull_mul_all A (TFK (R := R) F) ρ n k (k * n ^ 2) rfl α₀ hα₀ hN₀
      (lift (fst _ _) (snd _ _ ≫ E.aA)) (snd _ _ ≫ E.aA) (lift_snd _ _) (lift_fst _ _) (by rw [eA])
    obtain ⟨t, htw, htv⟩ := Hα σ (fun z => UT.cst (R := R) F z c) hσ
    obtain ⟨s, hs, -⟩ := (hbij k (by lia) u₀ hN.1).1 σ
    obtain ⟨s', hs', -⟩ := (hbij _ hpos w₀ hw₀).1 t
    obtain ⟨d, -, hd⟩ := exists_coef_ratio (F := F) U hw₀ hN.1 (k * n ^ 2)
    obtain ⟨s'', hs'', es⟩ := hd t s' hs'
    obtain ⟨W₁, hW₁, vW₁⟩ := TorsionValue.exists_frm_pow w₁ hw₁ (k * n ^ 2)
    obtain ⟨W₂, hW₂, vW₂⟩ := TorsionValue.exists_frm_pow w₂ hw₂ (k * n ^ 2)
    obtain ⟨w, hw, hwv⟩ := TorsionValue.exists_frm_kap hAct.1 W₁ hW₁ κ hκ.1
    obtain ⟨-, h₂⟩ := hpull u₀ ρ hN _ _ (lift_snd _ _) (lift_fst _ _) rfl α hα hα' σ t s s'' hs hs'' htw κ hκ g₁ o hAct
      W₁ w hW₁ hw hwv
    have pw : ∀ (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) z J,
        (val (powFrame A.A A.L x e ((n : ℤ) ^ 2)) (𝟙 _) z J).val ^ k =
          (val (powFrame A.A A.L x e ((k * n ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val := fun x e z J => by
      rw [PullMul.val_powFrame, PullMul.val_powFrame, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
      congr 2; push_cast; ring
    have S₁ := H₁ _ hpos W₁ vW₁ hW₁ t s' c hs' fun z J hJ =>
      (htv x₁ hx₁ z J hJ).trans (by rw [← val_corr hJ hC (𝟙 _), pw]; rfl)
    have S₂ := H₂ _ hpos W₂ vW₂ hW₂ t s' (c * r ^ k) hs' fun z J hJ => by
      refine (htv x₂ hx₂ z J hJ).trans ?_
      change _ = UT.cst (R := R) F z (c * r ^ k) * _
      rw [cst_mul_stalk, show UT.cst (R := R) F z (r ^ k) = UT.cst (R := R) F z r ^ k by rw [cst_eq, cst_eq, map_pow], ← pw]
      exact (congrArg (fun q : (TFK (R := R) F).left.presheaf.stalk z =>
        @id ((TFK (R := R) F).left.presheaf.stalk z) (UT.cst (R := R) F z c) * q ^ k) (hr _ (𝟙 _) z J hJ)).trans
        ((congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (UT.cst (R := R) F z c) * ·) (mul_pow _ _ _)).trans
          (_root_.mul_assoc _ _ _).symm)
    have e₃ : coef s' g₂ W₂ = coef s' g₁ W₁ := funext fun β => by
      rw [((coef_basic R D.toPre F _ g₁).2.2 W₁ hW₁).2.2.2 χ g₀ g₂ W₂ ht hadd
        (fun z J hJ => by rw [vW₁ z J hJ, vW₂ z J hJ, hww z J hJ])]
      by_cases hβ : β ∈ Set.range E.h
      · obtain ⟨b, rfl⟩ := hβ
        rw [eh, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hχ, MonoidHom.one_apply, Units.val_one, _root_.one_mul]
      · rw [es g₁ W₁ hW₁]; simp only [h₂ β hβ, mul_zero]
    rw [e₃] at S₂
    exact mul_left_cancel₀ hc (((sumF_calculus R I hB F _ _ (fun _ => 0) _ _).1 S₂ S₁).trans (_root_.mul_one c).symm)
  have r₁ : r = 1 := by have a := key 5 (by lia); rwa [pow_succ, key 4 le_rfl, _root_.one_mul] at a
  intro z J hJ
  refine Units.ext (Eq.symm ((hr _ (𝟙 _) z J hJ).trans ?_))
  have b : UT.cst (R := R) F z r = 1 := by rw [cst_eq, r₁, map_one]
  exact (congrArg (fun q : (Spec (CommRingCat.of F)).presheaf.stalk z => q * _) b).trans (_root_.one_mul _)

end Field

attribute [local instance] TorusExt.gtGroup in
theorem exists_liesOver (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G)
    {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {n : ℕ} (hn : 1 ≤ n)
    {g₁ g₂ : GtPtF D.toPre (FractionRing R)} {w₁ : Frm D.toPre (FractionRing R) 1 g₁.b} (hw₁ : w₁.IsGen)
    {x₁ x₂ x : TFK (R := R) (FractionRing R) ⟶ A.A} {e₁ : FrAt x₁} (he₁ : e₁.IsGen)
    (H₁ : LiesOver U.toUnifPre w₀ g₁ w₁ x₁ e₁) {χ : Multiplicative D.toPre.X →* (FractionRing R)ˣ} (hχ : χ ^ n = 1)
    (p : QkPt D.toPre (FractionRing R) n) (ht : IsTor χ p.g) (hx : QkToAkU U.toUnifPre (FractionRing R) n p x)
    (hadd : g₁.IsAdd p.g g₂) {w₂ : Frm D.toPre (FractionRing R) 1 g₂.b} (hw₂ : w₂.IsGen)
    (hww : ∀ z J, Good D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w₁ (𝟙 _) z J) (hx₂ : x₂ = x₁ * x) :
    ∃ e₂ : FrAt x₂, e₂.IsGen ∧ LiesOver U.toUnifPre w₀ g₂ w₂ x₂ e₂ := by
  have hL := GlobalTheory.firstFiveLaws
  have hbij := (GlobalTheory.TorsionAnyChar.expBijF_any hL R _ hB D A G hG U).1 (FractionRing R)
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := FractionRing R)
  obtain ⟨e, he⟩ : ∃ e : FrAt x₂, e.IsGen := exists_gen_pt A.isLB z₀ (fun y => pt_eq y z₀) _ _
  choose Ω hΩ hΩv using TorsionValue.exists_frm_pow w₂ hw₂
  have pf : ∀ (e : FrAt x₂) (k : ℤ) z J, val (powFrame A.A A.L x₂ e k) (𝟙 _) z J = val e (𝟙 _) z J ^ k :=
    fun _ _ _ _ => map_zpow _ _ _
  obtain ⟨l, hl, H⟩ := exists_degree_constant hB (fun k a c => ∃ (t : SecA A (FractionRing R) k)
      (s : Fam D.toPre (FractionRing R) k),
      U.ExpandsF (FractionRing R) k w₀ t s ∧ ValAt t x₂ e c ∧ a = coef s g₂ (Ω k)) n hn
    (by
      rintro k _ c hk ⟨t, s, hs, -, rfl⟩
      obtain ⟨W, hW, vW⟩ := TorsionValue.exists_frm_pow w₁ hw₁ k
      obtain ⟨c₁, hc₁⟩ := GlobalTheory.OneBasis.exists_valAt A (FractionRing R) hL.1 t x₁ he₁
      rw [funext (((coef_basic R D.toPre _ _ g₁).2.2 W hW).2.2.2 χ p.g g₂ (Ω k) ht hadd
        (fun z J hJ => by rw [vW z J hJ, hΩv k z J hJ, hww z J hJ]) s)]
      exact exists_sumF_twist hB (H₁ k hk W vW hW t s c₁ hs hc₁) hn _ fun β => by
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ, MonoidHom.one_apply, Units.val_one])
    (by
      rintro k k' _ _ c c' hk hk' ⟨t, s, hs, ht, rfl⟩ ⟨t', s', hs', ht', rfl⟩
      obtain ⟨t'', h''⟩ := TorsionValue.exists_secA_mul t t'
      obtain ⟨s'', hs'', -⟩ := (hbij (k + k') (by lia) w₀ hw₀).1 t''
      refine ⟨_, ⟨t'', s'', hs'', fun z J hJ => ?_, rfl⟩, fun α =>
        (GlobalTheory.TorsionAnyChar.prodConv_field hL R _ hB D A G hG U _ w₀ hw₀ k k' _ hk hk' rfl t t' t'' s s' s'' hs hs' hs''
          (fun z J hJ => h'' _ _ z J hJ) g₂ _ _ _ (hΩ k) (hΩ k') (hΩ _)
          (fun z J hJ => by rw [hΩv _ z J hJ, hΩv _ z J hJ, hΩv _ z J hJ, pow_add]) α)⟩
      change _ = UT.cst (R := R) (FractionRing R) z (c * c') * _
      rw [h'' _ _ z J hJ, ht z J hJ, ht' z J hJ, pf, pf, pf, cst_mul_stalk, Nat.cast_add, zpow_add, Units.val_mul]
      change (UT.cst (R := R) (FractionRing R) z c * _) * (UT.cst (R := R) (FractionRing R) z c' * _) = _
      ring)
    (fun k hk => by
      obtain ⟨t, c, hc, ht⟩ := NonVan.exists_sec_ne_zero hL R A _ k hk x₂ e he
      obtain ⟨s, hs, -⟩ := (hbij k (by lia) w₀ hw₀).1 t
      exact ⟨_, c, ⟨t, s, hs, ht, rfl⟩, hc⟩)
    (fun m hm => by
      let q : QkPt D.toPre (FractionRing R) (n * m) :=
        ⟨m • p.y, p.g, GlobalTheory.InducingAut.exists_qk_mul D.tau_bimult p m⟩
      obtain ⟨κ, hκ, Hκ⟩ := value_at_level hB hG U hw₀ hw₁ he₁ H₁ (Nat.mul_pos hn hm) q x
        (qkToAkU_level_field hL R _ hB D A G hG U _ n m _ hn hm rfl p q x rfl rfl hx) hadd hx₂ e he (Ω _) (hΩ _)
      refine ⟨κ, hκ, ?_⟩
      rintro _ c ⟨t, s, hs, ht, rfl⟩
      exact Hκ t s c hs ht)
  obtain ⟨e₂, he₂, ve⟩ := exists_scale (R := R) (φ := fun _ : Fin 1 => x₂.left) e he (inv_ne_zero hl)
  refine ⟨e₂, he₂, fun k hk w hwv hw t s c hs ht => ?_⟩
  have S := H k _ (c * l⁻¹ ^ k) hk ⟨t, s, hs, fun z J hJ => by
    refine (ht z J hJ).trans ?_
    rw [pf, pf, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, cst_eq, cst_eq, map_mul, map_pow]
    exact (congrArg (fun q => _ * q ^ k) (ve z J hJ)).trans
      ((congrArg (_ * ·) (mul_pow _ _ _)).trans (_root_.mul_assoc _ _ _).symm), rfl⟩
  rw [mul_left_comm, ← mul_pow, mul_inv_cancel₀ hl, one_pow, _root_.mul_one] at S
  rw [funext (coef_scale g₂ (w' := w) (hΩ k) (c := 1) (fun z J hJ => by
    rw [hwv z J hJ, hΩv k z J hJ, map_one, _root_.one_mul]) s)]
  simpa only [_root_.one_mul] using S

end GlobalTheory.Poinc.Tors.Translate
end
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFra =====
