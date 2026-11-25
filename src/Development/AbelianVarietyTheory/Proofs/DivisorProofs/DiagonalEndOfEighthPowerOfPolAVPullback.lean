module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullback

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isDiagEnd_pullback : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (ψ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P u ε → IsGrpPullback P'.A P.A f ψ →
    LBIso P'.L (P.L.pull ψ) → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A),
      IsDiagEnd F W P' (f ≫ u) ε' ∧ ∀ E, (ε' E).left ≫ ψ = ψ ≫ (ε E).left := by
  intro g n F W T T' P P' u f φ ε ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ hφ hL
  obtain ⟨c', hc'u, pr', hmon, huniv', hbun', hlift⟩ :=
    sharpOver_pullback_end g n _ (zetaAway n) F W T T' P P' u f φ c hc pr hpr huniv hbun hφ hL
  have hE : ∀ E, ∃ b' : P'.A ⟶ P'.A,
      (∀ a, b' ≫ pr' a = ((List.finRange 8).map fun b => pr' b ^ E a b).prod) ∧
      b'.left ≫ φ = φ ≫ (ε E).left := fun E => by
    obtain ⟨b', hb', hcomm⟩ := hlift (ε E) E fun a => by
      rw [hdiag E a, List.ofFn_eq_map]
    exact ⟨b', fun a => by rw [hb' a, List.ofFn_eq_map], hcomm⟩
  choose ε' hε' hcomm using hE
  exact ⟨ε', ⟨c', hc'u, pr', hmon, huniv', hbun', hε'⟩, hcomm⟩

end GlobalTheory.Poinc
