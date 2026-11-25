module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem smooth_of_isPullback_of_surjective_of_flat :
    ∀ (X X' Y Y' : Scheme.{0}) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), IsPullback φ p p' π → Surjective π → Flat p' → LocallyOfFinitePresentation p' → Smooth p → Smooth p' := by
  intro X X' Y Y' π φ p p' h hπ hflat hlfp hsm

  refine Smooth.of_smooth_fiberToSpecResidueField p' fun y' => ?_

  obtain ⟨y, rfl⟩ := hπ.surj y'

  have hsq := (isPullback_fiberToSpecResidueField_of_isPullback h y).flip

  have hff : (π.residueFieldMap y).hom.FaithfullyFlat := by
    letI := (π.residueFieldMap y).hom.toAlgebra
    show Module.FaithfullyFlat _ _
    infer_instance
  obtain ⟨hF, hS⟩ := (flat_and_surjective_SpecMap_iff _).2 hff

  have hfib : Smooth (p.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd p (X.fromSpecResidueField y)))

  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ⟨⟨hS, hF⟩, inferInstance⟩ hfib

end GlobalTheory
