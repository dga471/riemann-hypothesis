module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LN


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
theorem _root_.GlobalTheory.LN.pelSt_holds : _root_.GlobalTheory.LN.PelSt := by
  obtain ⟨hLaws, hTwist, hTheta, hTorsion, hRank⟩ := _root_.GlobalTheory.lawsAndExpansions
  exact _root_.GlobalTheory.PELOfUnif.main hLaws hTwist hTheta hTorsion hRank

end GlobalTheory.LN
