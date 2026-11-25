module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem nonempty_tq_pullback_comp {T S S' : Scheme.{0}} (r : T ⟶ S') (f : S' ⟶ S) {g : T ⟶ S} (h : g = r ≫ f)
    (G : Over S) [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ ((Over.pullback f).obj G) X) :
    Nonempty (TQ ((Over.pullback g).obj G) X) := by
  subst h
  obtain ⟨Q', -⟩ := exists_tq_baseChange _ _ _ X _ _ _
    ((isGrpPullback_of_iso (pullCompIso r f G)).comp (isGrpPullback_pullback _ r)) Q
  exact ⟨Q'⟩

theorem thick_zero_factor (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ r, thick V (IsLocalRing.maximalIdeal V) 0 = r ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (show IsLocalRing.maximalIdeal V ≤ IsLocalRing.maximalIdeal V ^ (0 + 1) by simp))), ?_⟩
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.UU
