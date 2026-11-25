module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ComplexConjugate

namespace GlobalTheory

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB Y}

theorem CxPts.mem_ptsIn_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

end Points

end GlobalTheory
