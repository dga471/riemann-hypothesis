module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelAmpleQProjNoeth

open GlobalTheory.RelAmpleQProj

theorem isQProjOver_of_relAmple_noeth : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0})
    (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L →
    IsQProjOver (A.hom ≫ s) := by
  rintro K _ _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProjNoeth
