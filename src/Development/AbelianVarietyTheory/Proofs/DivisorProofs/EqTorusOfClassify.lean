module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff

@[expose] public section

noncomputable section

section Helpers

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion
open GlobalTheory.FinitePartGeneric ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint

namespace GlobalTheory.ToricTorsionUnif

theorem exists_torsion_toG (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (U : Unif (maximalIdeal R) D A G) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq U.toUnifPre x₀ g₀ :=
  GlobalTheory.WholeBaseFinitePart.exists_torsion_toG_unif R hR.1 G D A U k hk

theorem generic (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp R))
    (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G) (hfin : IsFinite N.hom) (htors : x₀ ^ k = 1)
    (hform : FormalEq U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left) (hx : OverGen F N x)
    (q : QkPt D.toPre F k) (hq : q.y = 0) (hg : GtPt.IsPullF F x g₀ q.g) :
    ∃ a : TFK (R := R) F ⟶ A.A, a.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x ≫ x₀.left ∧
      QkToAkU U.toUnifPre F k q a := by
  have := hR.2
  exact GlobalTheory.WholeBaseFinitePart.generic_unif R hR.1 G hG D A U k hk N g₀ x₀ hfin htors hform F x hx q hq hg
end GlobalTheory.ToricTorsionUnif

end Helpers

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped CategoryTheory.Obj

theorem GlobalTheory.ToricTorsionUnif.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∃ s : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ G), (∀ (B : Type) [CommRing B] (a : R →+* B) τ h, s B a τ h ^ k = 1) ∧ (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (a' : R →+* B') (f : B →+* B') τ h τ' h', a' = f.comp a → (∀ χ, (τ' χ : B') = f (τ χ : B)) → (s B' a' τ' h').left = spMap f ≫ (s B a τ h).left) ∧ (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (a' : R →+* B') (f : B →+* B') (G₀ : Over (Sp B)) [GrpObj G₀] (φ : G₀.left ⟶ G.left) (h₀ : IsGrpPullback G₀ G (spMap a) φ) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp B) D.toPre.X), a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → (s B' a' τ h).left = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h₀).left ≫ φ) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g → QkToAkU U.toUnifPre F k q x → x.left ≫ genMap U = (s F a τ h).left := by
  intro R _ _ _ hR G _ _ hG D A U k hk
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ := GlobalTheory.ToricTorsionUnif.exists_torsion_toG R hR G D A U k hk
  let u : ∀ (B : Type) [CommRing B] (_ : Multiplicative D.toPre.X →* Bˣ),
      D.toPre.X →+ Additive Γ(Sp B, ⊤)ˣ := fun B _ τ =>
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : ∀ (B : Type) [CommRing B] (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → k • u B τ = 0 := fun B _ τ hτ =>
    AddMonoidHom.ext fun χ => Additive.toMul.injective (by
      have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
      simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
        map_one, AddMonoidHom.zero_apply, toMul_zero])
  choose gT hgT using fun (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ) =>
    GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := Over.mk (spMap a)) (u B τ)
  choose hT hhT hTu using fun (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ)
      (hτ : τ ^ k = 1) =>
    let ⟨_, h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k (u B τ) (hu B τ hτ) (T := Over.mk (spMap a))
      (g := gT B a τ) (hgT B a τ)
    hU _ _ ⟨_, h₁, h₂⟩
  refine ⟨fun B _ a τ hτ => hT B a τ hτ ≫ x₀,
    fun B _ a τ hτ => by show (hT B a τ hτ ≫ x₀) ^ k = 1; rw [← MonObj.comp_pow, htors, MonObj.comp_one],
    fun B B' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_,
    fun B B' _ _ a ha a' f G₀ _ φ h₀ τ hτ z ha' hz => ?_,
    fun F _ _ _ a τ hτ q x ha hq hqt hx => ?_⟩
  · subst ha
    let ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a) :=
      Over.homMk (spMap f) (GlobalTheory.ToricTorsionSec.spMap_comp a f).symm
    have hρ : GtPt.IsPull ρ.left (gT B a τ) (gT B' (f.comp a) τ') :=
      GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT B a τ) (hgT B' _ τ') fun χ =>
        (GlobalTheory.ToricTorsionSec.appTop_unitOn f _).trans (by congr 2; exact Units.ext (hτf _).symm)
    have e := hTu B' _ τ' hτ' (ρ ≫ hT B a τ hτ) (GlobalTheory.ToricTorsionSec.isPull_trans (hhT B a τ hτ) hρ)
    show (hT B' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT B a τ hτ ≫ x₀).left
    rw [← e]; rfl
  · subst ha'
    exact GlobalTheory.TorusTorsionPoint.eq_torus_of_classify_unif R G D A U N g₀ x₀ hform B B' a ha f G₀ φ h₀ τ z hz
      (gT B' _ τ) (hgT B' _ τ) (hT B' _ τ hτ) (hhT B' _ τ hτ)
  · subst ha
    have hx' : GlobalTheory.FlatTors.OverGen F N (hT F _ τ hτ).left :=
      (Over.w (hT F _ τ hτ)).trans (GlobalTheory.ToricTorsionSec.spMap_comp _ _)
    have hp := GlobalTheory.ToricTorsionSec.isPullF_trans (hhT F _ τ hτ)
      (GlobalTheory.ToricTorsionSec.isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)
    rw [Category.id_comp] at hp
    obtain ⟨a', ha', hq'⟩ := GlobalTheory.ToricTorsionUnif.generic R hR G hG D A U k hk N g₀ x₀ hfin htors hform F _ hx' q hq hp
    obtain rfl := GlobalTheory.TorsionImage.qkToAkU_unique GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 R
      (maximalIdeal R) hR.1 D A G hG U F k hk q x a' hx hq'
    show x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (hT F _ τ hτ ≫ x₀).left
    rw [ha', Over.comp_left]

end
