module

import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConnOpen

theorem isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  apply CrystallineSemistableComparison.isOpen_connectedComponent_of_noetherianSpace

end GlobalTheory.ConnOpen

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
