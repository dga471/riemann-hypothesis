module

public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialsAndBaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionBase
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Global

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Transport

theorem pointCongr_pointCongr {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (P : V₁.toAffine.Point) :
    pointCongr h₂ (pointCongr h₁ P) = pointCongr (h₁.trans h₂) P := by
  subst h₁; subst h₂; rfl

theorem pointMapRing_pointCongr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    pointMapRing f V₂ (pointCongr h P) =
      pointCongr (congrArg (fun V => V.map f) h) (pointMapRing f V₁ P) := by
  subst h; rfl

theorem pointMapRing_congr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    {f g : F →+* L} (h : f = g) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = pointCongr (by rw [h]) (pointMapRing g V P) := by
  subst h; rfl

theorem pointMapRing_pointMapRing {F L L' : Type*} [Field F] [Field L] [Field L'] [DecidableEq F]
    [DecidableEq L] [DecidableEq L'] (f : F →+* L) (g : L →+* L') (V : WeierstrassCurve F)
    (P : V.toAffine.Point) :
    pointMapRing g (V.map f) (pointMapRing f V P) = pointMapRing (g.comp f) V P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem map_eq_pointCongr_pointMapRing {R F₁ F₂ : Type*} [CommRing R] [Field F₁] [Field F₂]
    [Algebra R F₁] [Algebra R F₂] [DecidableEq F₁] [DecidableEq F₂] (V : WeierstrassCurve R)
    (σ : F₁ →ₐ[R] F₂) (P : (V.baseChange F₁).toAffine.Point) :
    Point.map σ P = pointCongr (by
        show V.map (σ.toRingHom.comp (algebraMap R F₁)) = V.map (algebraMap R F₂)
        exact congrArg V.map σ.comp_algebraMap) (pointMapRing σ.toRingHom (V.baseChange F₁) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (pointCongr _)).symm
  · rw [Point.map_some]
    obtain ⟨h', e⟩ := pointMapRing_some σ.toRingHom (V.baseChange F₁) h
    rw [e, pointCongr_some, Point.some.injEq]
    exact ⟨rfl, rfl⟩

theorem reducePoint_pointCongr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type*) [Field K] [Algebra 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
    {V₁ V₂ : WeierstrassCurve 𝒪} (h : V₁ = V₂) (P : (curveK K V₁).Point) :
    reducePoint K V₂ (pointCongr (congrArg (fun V => V.map (algebraMap 𝒪 K)) h) P) =
      pointCongr (congrArg (fun V => V.map (residue 𝒪)) h) (reducePoint K V₁ P) := by
  subst h; rfl

end Transport

section Eval

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  (M : Type*) [Field M] [Algebra Λ M] [IsFractionRing Λ M] [Algebra K M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [IsDomain Λ]
  [IsDiscreteValuationRing Λ] [IsLocalHom j] [IsFractionRing Λ M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)] in
theorem map_baseChange_eq_map_of
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c)) :
    (W'.baseChange K).baseChange M = (W'.map j).map (algebraMap Λ M) := by
  show W'.map ((algebraMap K M).comp (algebraMap 𝒪 K)) = W'.map ((algebraMap Λ M).comp j)
  congr 1
  exact RingHom.ext hjM

variable {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
  (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

theorem map_fieldEvalRed_eq :
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).map
      (fieldEvalRed W j hxy hx) = (W'.map j).map (residue Λ) := by
  show W'.map (((fieldEvalRed W j hxy hx).comp (algebraMap (ResidueField 𝒪) _)).comp
    (residue 𝒪)) = W'.map ((residue Λ).comp j)
  congr 1
  refine RingHom.ext fun c => ?_
  simp [fieldEvalRed_algebraMap, ResidueField.map_residue]

variable [W'.IsElliptic]

theorem reducePoint_genEval
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c))
    (hR : ((W.baseChange K).baseChange M).toAffine.Nonsingular (algebraMap Λ M x)
      (algebraMap Λ M y))
    (hRg : IsGenPt (W.baseChange K) (Point.some _ _ hR))
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reducePoint M (W'.map j) (pointCongr (map_baseChange_eq_map_of K W' j M hjM)
        (Point.map (genEval (W.baseChange K) _ hRg) Q)) =
      pointCongr (map_fieldEvalRed_eq W W' j hxy hx)
        (pointMapRing (fieldEvalRed W j hxy hx) _ (reduceFF K W W' Q)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  set σ := genEval (W.baseChange K) _ hRg
  have hσ : σ.toRingHom.comp (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
    apply comp_algebraMap_gaussLift
    · intro c
      show σ (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, σ.commutes, hjM]
    · exact genEval_genX _ _ hRg
    · exact genEval_genY _ _ hRg
  have c0 : (gaussCurve W W').map (gaussLift W j hxy hx) = W'.map j := by
    show W'.map ((gaussLift W j hxy hx).comp (algebraMap 𝒪 (gaussRing W))) = W'.map j
    exact congrArg W'.map (RingHom.ext (gaussLift_algebraMap_base W j hxy hx))
  set Q₀ := pointCongr (gaussCurve_map_functionField K W W').symm Q with hQ₀
  have hQ : Q = pointCongr (gaussCurve_map_functionField K W W') Q₀ := by
    rw [hQ₀, pointCongr_pointCongr]; rfl
  have key := reducePoint_pointMapRing (W.baseChange K).toAffine.FunctionField M hσ
    (gaussCurve W W') Q₀
  have lhs : pointCongr (map_baseChange_eq_map_of K W' j M hjM) (Point.map σ Q) =
      pointCongr (congrArg (fun V => V.map (algebraMap Λ M)) c0)
        (pointCongr (map_curveK_eq _ M hσ (gaussCurve W W')) (pointMapRing σ.toRingHom _ Q₀)) := by
    rw [map_eq_pointCongr_pointMapRing, hQ, pointMapRing_pointCongr, pointCongr_pointCongr,
      pointCongr_pointCongr, pointCongr_pointCongr]
  rw [lhs, reducePoint_pointCongr, key, pointMapRing_congr (residueField_map_gaussLift W j hxy hx),
    ← pointMapRing_pointMapRing]
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [pointMapRing_pointCongr]
  erw [pointCongr_pointCongr, pointCongr_pointCongr, pointCongr_pointCongr]
  · rfl
  · exact c0

end Eval
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

section Push

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def pushField : ResidueField (gaussRing (gaussCurve W W)) →+* univField (W.map (residue 𝒪)) :=
  (ffCongr (gaussCurve_map_residue W W)).toRingHom.comp
    ((ffMap (gaussResidue W) ((gaussCurve W W).map (residue (gaussRing W)))).comp
      (gaussResidue (gaussCurve W W)))

theorem pushField_residue_algebraMap (g : gaussRing W) :
    pushField W (residue _ (algebraMap (gaussRing W) (gaussRing (gaussCurve W W)) g)) =
      algebraMap (W.map (residue 𝒪)).toAffine.FunctionField _ (gaussResidue W (residue _ g)) := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_residue_algebraMap,
    ffMap_algebraMap]
  exact ffCongr_algebraMap _ _

theorem pushField_gaussX :
    pushField W (residue _ (gaussX (gaussCurve W W))) = genX _ := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_gaussX, ffMap_genX]
  exact ffCongr_genX _

theorem pushField_gaussY :
    pushField W (residue _ (gaussY (gaussCurve W W))) = genY _ := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_gaussY, ffMap_genY]
  exact ffCongr_genY _

end Push

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

abbrev liftField : Type _ :=
  ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.FunctionField

abbrev liftJ : 𝒪 →+* gaussRing (gaussCurve W W) :=
  (algebraMap (gaussRing W) (gaussRing (gaussCurve W W))).comp (algebraMap 𝒪 (gaussRing W))

theorem liftJ_algebraMap (c : 𝒪) :
    algebraMap K (liftField K W) (algebraMap 𝒪 K c) =
      algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (liftJ W c) := by
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (gaussRing W) (gaussRing (gaussCurve W W)) (liftField K W),
    IsScalarTower.algebraMap_apply (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (liftField K W),
    ← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField K W)]

theorem pushField_comp_residueField_map :
    (pushField W).comp (ResidueField.map (liftJ W)) =
      algebraMap (ResidueField 𝒪) (univField (W.map (residue 𝒪))) := by
  refine RingHom.ext fun c => ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [RingHom.comp_apply, ResidueField.map_residue, RingHom.comp_apply,
    pushField_residue_algebraMap, gaussResidue_residue_algebraMap,
    ← IsScalarTower.algebraMap_apply]

theorem pushCurve_eq (V : WeierstrassCurve 𝒪) :
    ((V.map (liftJ W)).map (residue _)).map (pushField W) =
      (V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪))) := by
  show V.map (((pushField W).comp (residue _)).comp (liftJ W)) =
    V.map ((algebraMap (ResidueField 𝒪) _).comp (residue 𝒪))
  have h : ((pushField W).comp (residue _)).comp (liftJ W) =
      (algebraMap (ResidueField 𝒪) (univField (W.map (residue 𝒪)))).comp (residue 𝒪) := by
    rw [← pushField_comp_residueField_map, RingHom.comp_assoc, RingHom.comp_assoc,
      ResidueField.map_comp_residue]
  rw [h]

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

def pushPt (V : WeierstrassCurve 𝒪) :
    ((V.map (liftJ W)).map (residue _)).toAffine.Point →+
      ((V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point :=
  (pointCongr (pushCurve_eq W V)).toAddMonoidHom.comp (pointMapRing (pushField W) _)

def redU (V : WeierstrassCurve 𝒪) [V.IsElliptic] :
    ((V.baseChange K).baseChange (liftField K W)).toAffine.Point →+
      ((V.map (liftJ W)).map (residue _)).toAffine.Point :=
  (reductionHom (liftField K W) (V.map (liftJ W))).comp
    (pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
      (liftJ_algebraMap K W))).toAddMonoidHom

theorem pushPt_redU_some (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    {x y : gaussRing (gaussCurve W W)}
    (h : ((V.baseChange K).baseChange (liftField K W)).toAffine.Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y)) :
    ∃ h' : ((V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Nonsingular
        (pushField W (residue _ x)) (pushField W (residue _ y)),
      pushPt W V (redU K W V (.some _ _ h)) = .some _ _ h' := by
  have h₁ : (curveK (liftField K W) (V.map (liftJ W))).Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y) := by
    show ((V.map (liftJ W)).map (algebraMap _ (liftField K W))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K V (liftJ W) (liftField K W) (liftJ_algebraMap K W)]
    exact h
  have n : (curveRed (V.map (liftJ W))).Nonsingular (residue _ x) (residue _ y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (equation_residue (V.map (liftJ W)) (equation_of_map (liftField K W) _ h₁.1))
  obtain ⟨h', e⟩ := pointMapRing_some (pushField W) ((V.map (liftJ W)).map (residue _)) n
  refine ⟨by rw [← pushCurve_eq W V]; exact h', ?_⟩
  have e₁ : pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
      (liftJ_algebraMap K W)) (Point.some _ _ h) = Point.some _ _ h₁ := pointCongr_some _ h
  have e₂ : redU K W V (.some _ _ h) = .some _ _ n := by
    show reducePoint (liftField K W) (V.map (liftJ W)) (pointCongr _ (.some _ _ h)) = _
    rw [e₁, reducePoint_some_integral _ _ h₁ n]
  rw [e₂]
  exact (congrArg (pointCongr (pushCurve_eq W V)) e).trans (pointCongr_some _ _)

instance isElliptic_baseChange_ring {R : Type*} [CommRing R] (V : WeierstrassCurve R) [V.IsElliptic]
    (A : Type*) [CommRing A] [Algebra R A] : (V.baseChange A).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

variable [W.IsElliptic]

def liftPt₁ : ((W.baseChange K).baseChange (liftField K W)).toAffine.Point :=
  Point.map (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField (liftField K W))
    (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))

theorem baseChange_liftField_eq :
    ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField).baseChange
      (liftField K W) = (W.baseChange K).baseChange (liftField K W) := by
  show W.map (((algebraMap (W.baseChange K).toAffine.FunctionField (liftField K W)).comp
      (algebraMap (gaussRing W) _)).comp (algebraMap 𝒪 (gaussRing W))) =
    W.map ((algebraMap K (liftField K W)).comp (algebraMap 𝒪 K))
  refine congrArg W.map (RingHom.ext fun c => ?_)
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField K W)]

def liftPt₂ : ((W.baseChange K).baseChange (liftField K W)).toAffine.Point :=
  pointCongr (baseChange_liftField_eq K W)
    (GroundTheory.Arith.Abelian.genericPoint
      ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField))

theorem exists_some_eq {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
    {a b a' b' : F} (h : V.toAffine.Nonsingular a b) (ha : a = a') (hb : b = b') :
    ∃ h', (Point.some a b h : V.toAffine.Point) = Point.some a' b' h' := by
  subst ha; subst hb; exact ⟨h, rfl⟩

theorem liftPt₁_eq : ∃ h, liftPt₁ K W = Point.some
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussX W)))
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussY W))) h := by
  have hx : algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussX W)) =
        algebraMap (W.baseChange K).toAffine.FunctionField _ (genX (W.baseChange K)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (gaussRing W)
      (W.baseChange K).toAffine.FunctionField (liftField K W), algebraMap_gaussX]
  have hy : algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussY W)) =
        algebraMap (W.baseChange K).toAffine.FunctionField _ (genY (W.baseChange K)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (gaussRing W)
      (W.baseChange K).toAffine.FunctionField (liftField K W), algebraMap_gaussY]
  rw [liftPt₁, GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
  exact exists_some_eq _ hx.symm hy.symm

theorem liftPt₂_eq : ∃ h, liftPt₂ K W = Point.some
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (gaussX (gaussCurve W W)))
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (gaussY (gaussCurve W W))) h := by
  rw [liftPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact exists_some_eq _
    (algebraMap_gaussX (gaussCurve W W) (W.baseChange K).toAffine.FunctionField).symm
    (algebraMap_gaussY (gaussCurve W W) (W.baseChange K).toAffine.FunctionField).symm

theorem pushPt_redU_liftPt₁ :
    pushPt W W (redU K W W (liftPt₁ K W)) = univPt₁ (W.map (residue 𝒪)) := by
  obtain ⟨h, e⟩ := liftPt₁_eq K W
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e, e', univPt₁, GroundTheory.Arith.Abelian.genericPoint, Point.map_some, Point.some.injEq]
  constructor
  · rw [pushField_residue_algebraMap, gaussResidue_gaussX]; rfl
  · rw [pushField_residue_algebraMap, gaussResidue_gaussY]; rfl

theorem pushPt_redU_liftPt₂ :
    pushPt W W (redU K W W (liftPt₂ K W)) = univPt₂ (W.map (residue 𝒪)) := by
  obtain ⟨h, e⟩ := liftPt₂_eq K W
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e, e', univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.some.injEq]
  exact ⟨pushField_gaussX W, pushField_gaussY W⟩

theorem isGenPt_liftPt₁ : IsGenPt (W.baseChange K) (liftPt₁ K W) :=
  isGenPt_map _ _ (transcendental_genX _)

theorem transOver_liftPt₂ :
    TransOver (W.baseChange K) (W.baseChange K).toAffine.FunctionField (liftPt₂ K W) := by
  rw [liftPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

theorem isGenPt_liftPt₂ : IsGenPt (W.baseChange K) (liftPt₂ K W) := (transOver_liftPt₂ K W).isGenPt

theorem isGenPt_liftPt₁₂ : IsGenPt (W.baseChange K) (liftPt₁ K W + liftPt₂ K W) :=
  ((transOver_liftPt₂ K W).add_left (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))).isGenPt

end Main
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

theorem redU_apply (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (P : ((V.baseChange K).baseChange (liftField K W)).toAffine.Point) :
    redU K W V P = reducePoint (liftField K W) (V.map (liftJ W))
      (pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
        (liftJ_algebraMap K W)) P) := by
  simp only [redU, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    reductionHom_apply]

theorem pushPt_apply (V : WeierstrassCurve 𝒪)
    (P : ((V.map (liftJ W)).map (residue (gaussRing (gaussCurve W W)))).toAffine.Point) :
    pushPt W V P = pointCongr (pushCurve_eq W V) (pointMapRing (pushField W) _ P) := by
  simp only [pushPt, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]

variable [W.IsElliptic]

theorem exists_integral_of_reducePoint_ne_zero {𝒪₀ : Type*} [CommRing 𝒪₀] [IsDomain 𝒪₀]
    [IsDiscreteValuationRing 𝒪₀] (K₀ : Type*) [Field K₀] [Algebra 𝒪₀ K₀] [IsFractionRing 𝒪₀ K₀]
    (V : WeierstrassCurve 𝒪₀) {P : (curveK K₀ V).Point} (hP : reducePoint K₀ V P ≠ 0) :
    ∃ (x y : 𝒪₀) (h : (curveK K₀ V).Nonsingular (algebraMap 𝒪₀ K₀ x) (algebraMap 𝒪₀ K₀ y)),
      P = Point.some _ _ h := by
  rcases point_cases K₀ V P with h0 | ⟨X₀, Y₀, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · exact absurd (by rw [h0, reducePoint_zero]) hP
  · exact absurd (reducePoint_some_notMem K₀ V h hX) hP
  · exact ⟨x, y, h, rfl⟩

theorem liftPt₁₂_eq : ∃ (x y : gaussRing (gaussCurve W W)) (h : _),
    liftPt₁ K W + liftPt₂ K W = Point.some (algebraMap _ (liftField K W) x)
      (algebraMap _ (liftField K W) y) h := by
  have hsum : pushPt W W (redU K W W (liftPt₁ K W + liftPt₂ K W)) =
      univPt₁ (W.map (residue 𝒪)) + univPt₂ (W.map (residue 𝒪)) := by
    rw [map_add (f := _), map_add (f := _), pushPt_redU_liftPt₁, pushPt_redU_liftPt₂]
  have hne : redU K W W (liftPt₁ K W + liftPt₂ K W) ≠ 0 := fun h0 =>
    isGenPt_ne_zero _ (isGenPt_univPt₁₂ (W.map (residue 𝒪))) (by rw [← hsum, h0, map_zero])
  rw [redU_apply] at hne
  obtain ⟨x, y, h, hP⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have hP' : liftPt₁ K W + liftPt₂ K W = pointCongr (map_baseChange_eq_map_of K W (liftJ W)
      (liftField K W) (liftJ_algebraMap K W)).symm (Point.some _ _ h) := by
    rw [← hP, pointCongr_pointCongr]; rfl
  rw [hP', pointCongr_some]
  exact ⟨x, y, _, rfl⟩

omit [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))] [W.IsElliptic] in
theorem pointCongr_pointCongr_eq {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (h₃ : V₁ = V₃)
    (P : V₁.toAffine.Point) : pointCongr h₂ (pointCongr h₁ P) = pointCongr h₃ P := by
  subst h₁; subst h₂; rfl

variable (W' : WeierstrassCurve 𝒪) [W'.IsElliptic]

theorem pushField_comp_fieldEvalRed {x y : gaussRing (gaussCurve W W)}
    (hxy : (W.map (liftJ W)).toAffine.Equation x y)
    (hx : Function.Injective (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x)))
    {R : ((W.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point}
    (hR : IsGenPt (W.map (residue 𝒪)) R) (hRx : xOf _ R = pushField W (residue _ x))
    (hRy : yOf _ R = pushField W (residue _ y)) :
    (pushField W).comp (fieldEvalRed W (liftJ W) hxy hx) =
      (genEval (W.map (residue 𝒪)) R hR).toRingHom := by
  apply ringHom_ext_functionField
  · intro c
    rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
      pushField_comp_residueField_map]
    exact ((genEval _ R hR).commutes c).symm
  · rw [RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      genEval_genX, hRx]
  · rw [RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      genEval_genY, hRy]

theorem pushPt_redU_genEval {x y : gaussRing (gaussCurve W W)}
    (h : ((W.baseChange K).baseChange (liftField K W)).toAffine.Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y))
    (hg : IsGenPt (W.baseChange K) (Point.some _ _ h))
    {R : ((W.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point}
    (hR : IsGenPt (W.map (residue 𝒪)) R)
    (hpush : pushPt W W (redU K W W (Point.some _ _ h)) = R)
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    pushPt W W' (redU K W W' (Point.map (genEval (W.baseChange K) _ hg) Q)) =
      Point.map (genEval (W.map (residue 𝒪)) R hR) (reduceFF K W W' Q) := by
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e'] at hpush
  subst hpush
  have hxy : (W.map (liftJ W)).toAffine.Equation x y := by
    have h₁ : ((W.map (liftJ W)).map (algebraMap _ (liftField K W))).toAffine.Equation
        (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y) := by
      rw [← map_baseChange_eq_map_of K W (liftJ W) (liftField K W) (liftJ_algebraMap K W)]
      exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W.map (liftJ W)).toAffine
      (IsFractionRing.injective _ (liftField K W)) x y).mp h₁
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (pushField W (residue _ x)) := hR
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (pushField W (residue _ x)) p =
        pushField W (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, pushField_comp_residueField_map]
    rw [key, hp, map_zero]
  have main := reducePoint_genEval (K := K) (W := W) (W' := W') (j := liftJ W)
    (M := liftField K W) (hxy := hxy) (hx := hx) (liftJ_algebraMap K W) h hg Q
  have hring := pushField_comp_fieldEvalRed W hxy hx hR rfl rfl
  rw [redU_apply, main, pushPt_apply, pointMapRing_pointCongr, pointCongr_pointCongr,
    pointMapRing_pointMapRing, pointMapRing_congr hring, map_eq_pointCongr_pointMapRing]
  exact pointCongr_pointCongr_eq _ _ _ _

theorem univAdd_reduceFF
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point)
    (hQ : RespectsAdd (W.baseChange K) (W'.baseChange K) Q) : UnivAdd (reduceFF K W W' Q) := by
  haveI : DecidableEq (ResidueField (gaussRing (gaussCurve W W))) := Classical.decEq _
  obtain ⟨h₁, e₁⟩ := liftPt₁_eq K W
  obtain ⟨h₂, e₂⟩ := liftPt₂_eq K W
  obtain ⟨x₃, y₃, h₃, e₃⟩ := liftPt₁₂_eq K W
  have g₁ : IsGenPt (W.baseChange K) (Point.some _ _ h₁) := by
    rw [← e₁]; exact isGenPt_liftPt₁ K W
  have g₂ : IsGenPt (W.baseChange K) (Point.some _ _ h₂) := by
    rw [← e₂]; exact isGenPt_liftPt₂ K W
  have g₃ : IsGenPt (W.baseChange K) (Point.some _ _ h₃) := by
    rw [← e₃]; exact isGenPt_liftPt₁₂ K W
  have hsum : pushPt W W (redU K W W (liftPt₁ K W + liftPt₂ K W)) =
      univPt₁ (W.map (residue 𝒪)) + univPt₂ (W.map (residue 𝒪)) := by
    rw [map_add (f := _), map_add (f := _), pushPt_redU_liftPt₁, pushPt_redU_liftPt₂]
  have k₁ := pushPt_redU_genEval K W W' h₁ g₁ (isGenPt_univPt₁ _)
    (by rw [← e₁]; exact pushPt_redU_liftPt₁ K W) Q
  have k₂ := pushPt_redU_genEval K W W' h₂ g₂ (isGenPt_univPt₂ _)
    (by rw [← e₂]; exact pushPt_redU_liftPt₂ K W) Q
  have k₃ := pushPt_redU_genEval K W W' h₃ g₃ (isGenPt_univPt₁₂ _)
    (by rw [← e₃]; exact hsum) Q
  have hs : Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h₃ := by
    rw [← e₁, ← e₂, e₃]
  have hadd := (respectsAdd_iff Q).mp hQ (liftField K W) _ _ g₁ g₂ (hs ▸ g₃)
  rw [genEval_congr _ hs _ g₃] at hadd
  have := congrArg (fun P => pushPt W W' (redU K W W' P)) hadd
  simp only [map_add (f := _)] at this
  rw [k₁, k₂, k₃] at this
  exact this

theorem respectsAdd_reduceFF
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point)
    (hQ : RespectsAdd (W.baseChange K) (W'.baseChange K) Q) :
    RespectsAdd (W.map (residue 𝒪)) (W'.map (residue 𝒪)) (reduceFF K W W' Q) :=
  respectsAdd_of_univAdd _ (univAdd_reduceFF K W W' Q hQ)

end Main
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

section Generic

variable [W.IsElliptic]

omit [W.IsElliptic] in
theorem reduceFF_some (V : WeierstrassCurve 𝒪) [V.IsElliptic] {x y : gaussRing W}
    (h : ((V.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y)) :
    ∃ h', reduceFF K W V (Point.some _ _ h) =
      Point.some (gaussResidue W (residue _ x)) (gaussResidue W (residue _ y)) h' := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have h₁ : (curveK (W.baseChange K).toAffine.FunctionField (gaussCurve W V)).Nonsingular
      (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y) := by
    show ((gaussCurve W V).map (algebraMap _ _)).toAffine.Nonsingular _ _
    rw [gaussCurve_map_functionField]; exact h
  have e₁ : pointCongr (gaussCurve_map_functionField K W V).symm (Point.some _ _ h) =
      Point.some _ _ h₁ := pointCongr_some _ h
  have n₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue (gaussCurve W V)
      (equation_of_map (W.baseChange K).toAffine.FunctionField (gaussCurve W V) h₁.1))
  obtain ⟨h₂, e₂⟩ := pointMapRing_some (gaussResidue W) ((gaussCurve W V).map (residue _)) n₁
  refine ⟨by rw [← gaussCurve_map_residue W V]; exact h₂, ?_⟩
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [e₁, reducePoint_some_integral _ _ h₁ n₁]
  erw [e₂]
  rw [pointCongr_some]

theorem reduceFF_genericPoint :
    reduceFF K W W (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) =
      GroundTheory.Arith.Abelian.genericPoint (W.map (residue 𝒪)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hx := algebraMap_gaussX W K
  have hy := algebraMap_gaussY W K
  obtain ⟨h₁, e₁⟩ : ∃ h₁ : (curveK (W.baseChange K).toAffine.FunctionField
      (gaussCurve W W)).Nonsingular (algebraMap (gaussRing W) _ (gaussX W))
        (algebraMap (gaussRing W) _ (gaussY W)),
      pointCongr (gaussCurve_map_functionField K W W).symm
        (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) = Point.some _ _ h₁ := by
    rw [GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
    exact exists_some_eq _ hx.symm hy.symm
  have n₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue (gaussCurve W W)
      (equation_of_map (W.baseChange K).toAffine.FunctionField (gaussCurve W W) h₁.1))
  obtain ⟨h₂, e₂⟩ := pointMapRing_some (gaussResidue W) ((gaussCurve W W).map (residue _)) n₁
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [e₁, reducePoint_some_integral _ _ h₁ n₁]
  erw [e₂]
  rw [pointCongr_some, GroundTheory.Arith.Abelian.genericPoint, Point.some.injEq, gaussResidue_gaussX,
    gaussResidue_gaussY]
  exact ⟨rfl, rfl⟩

theorem reduceFF_zsmul_genericPoint (n : ℤ) :
    reduceFF K W W (n • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) =
      n • GroundTheory.Arith.Abelian.genericPoint (W.map (residue 𝒪)) := by
  rw [map_zsmul, reduceFF_genericPoint]

end Generic

section Coordinates

variable {F : Type*} [Field F] [DecidableEq F]

theorem xOf_pointCongr {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    xOf V₂ (pointCongr h P) = xOf V₁ P := by
  subst h; rfl

theorem yOf_pointCongr {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    yOf V₂ (pointCongr h P) = yOf V₁ P := by
  subst h; rfl

theorem pointCongr_eq_zero_iff {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂)
    (P : V₁.toAffine.Point) : pointCongr h P = 0 ↔ P = 0 := by
  subst h; rfl

variable {L : Type*} [Field L] [DecidableEq L]

theorem xOf_pointMapRing (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    xOf (V.map f) (pointMapRing f V P) = f (xOf V P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : L) = f 0; rw [map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]; rfl

theorem yOf_pointMapRing (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    yOf (V.map f) (pointMapRing f V P) = f (yOf V P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : L) = f 0; rw [map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]; rfl

theorem pointMapRing_eq_zero_iff (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]
    exact ⟨fun h0 => absurd h0 (Point.some_ne_zero _), fun h0 => absurd h0 (Point.some_ne_zero _)⟩

theorem point_ext_xy {V : WeierstrassCurve F} {P Q : V.toAffine.Point} (h0 : P = 0 ↔ Q = 0)
    (hx : xOf V P = xOf V Q) (hy : yOf V P = yOf V Q) : P = Q := by
  rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩
  · rfl
  · exact absurd (h0.1 rfl) (Point.some_ne_zero _)
  · exact absurd (h0.2 rfl) (Point.some_ne_zero _)
  · rw [Point.some.injEq]; exact ⟨hx, hy⟩

end Coordinates

section Composition

omit [IsFractionRing 𝒪 K] in
theorem fieldEvalRed_congr {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    (j : 𝒪 →+* Λ) [IsLocalHom j] {x₁ y₁ x₂ y₂ : Λ} (hxy₁ : (W.map j).toAffine.Equation x₁ y₁)
    (hxy₂ : (W.map j).toAffine.Equation x₂ y₂)
    (hx₁ : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x₁)))
    (hx₂ : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x₂)))
    (ex : residue Λ x₁ = residue Λ x₂) (ey : residue Λ y₁ = residue Λ y₂) :
    fieldEvalRed W j hxy₁ hx₁ = fieldEvalRed W j hxy₂ hx₂ := by
  apply ringHom_ext_functionField
  · intro c; rw [fieldEvalRed_algebraMap, fieldEvalRed_algebraMap]
  · rw [fieldEvalRed_genX, fieldEvalRed_genX, ex]
  · rw [fieldEvalRed_genY, fieldEvalRed_genY, ey]

omit [IsFractionRing 𝒪 K] in
theorem gaussResidue_comp_residueField_map :
    (gaussResidue W).comp (ResidueField.map (algebraMap 𝒪 (gaussRing W))) =
      algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField := by
  refine RingHom.ext fun c => ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [RingHom.comp_apply, ResidueField.map_residue, gaussResidue_residue_algebraMap]

variable (W' W'' : WeierstrassCurve 𝒪) [W'.IsElliptic] [W''.IsElliptic]

theorem reduceFF_map_genEval
    {R : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hR : IsGenPt (W'.baseChange K) R) (hR' : IsGenPt (W'.map (residue 𝒪)) (reduceFF K W W' R))
    (Q : ((W''.baseChange K).baseChange (W'.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reduceFF K W W'' (Point.map (genEval (W'.baseChange K) R hR) Q) =
      Point.map (genEval (W'.map (residue 𝒪)) _ hR') (reduceFF K W' W'' Q) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have e := gaussCurve_map_functionField K W W'
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr e.symm R) ≠ 0 := by
    intro h0
    apply isGenPt_ne_zero _ hR'
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    erw [h0]
    rw [map_zero, map_zero]
  obtain ⟨x, y, h₀, hP⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have hRe : R = pointCongr e (Point.some _ _ h₀) := by
    rw [← hP, pointCongr_pointCongr]; rfl
  obtain ⟨h, hRs⟩ : ∃ h, R = Point.some (algebraMap (gaussRing W) _ x)
      (algebraMap (gaussRing W) _ y) h := by
    rw [hRe, pointCongr_some]; exact ⟨_, rfl⟩
  subst hRs
  obtain ⟨h', e'⟩ := reduceFF_some K W W' h
  have hR'' : IsGenPt (W'.map (residue 𝒪)) (Point.some _ _ h') := e' ▸ hR'
  rw [genEval_congr _ e' hR' hR'']
  set j := algebraMap 𝒪 (gaussRing W)
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (j c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map j).toAffine.Equation x y := by
    have h₁ : ((W'.map j).map (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' j _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map j).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  have hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue _ x)) := by
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := hR''
    refine Function.Injective.of_comp (f := gaussResidue W) ?_
    convert transcendental_iff_injective.mp hT using 1
    funext p
    rw [Function.comp_apply, aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂,
      gaussResidue_comp_residueField_map]
  have hring : (gaussResidue W).comp (fieldEvalRed W' j hxy hx) =
      (genEval (W'.map (residue 𝒪)) _ hR'').toRingHom := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((genEval _ _ hR'').commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        genEval_genX]
      rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        genEval_genY]
      rfl
  have main := reducePoint_genEval (K := K) (W := W') (W' := W'') (j := j)
    (M := (W.baseChange K).toAffine.FunctionField) (hxy := hxy) (hx := hx) hjM h hR Q
  have main' : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'')
      (pointCongr (gaussCurve_map_functionField K W W'').symm
        (Point.map (genEval (W'.baseChange K) _ hR) Q)) =
      pointCongr (map_fieldEvalRed_eq W' W'' j hxy hx)
        (pointMapRing (fieldEvalRed W' j hxy hx) _ (reduceFF K W' W'' Q)) := main
  have hL : reduceFF K W W'' (Point.map (genEval (W'.baseChange K) _ hR) Q) =
      pointCongr (gaussCurve_map_residue W W'') (pointMapRing (gaussResidue W) _
        (reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'')
          (pointCongr (gaussCurve_map_functionField K W W'').symm
            (Point.map (genEval (W'.baseChange K) _ hR) Q)))) := by
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rfl
  rw [hL, main']
  have hf := DFunLike.congr_fun hring
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
  apply point_ext_xy
  · rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, pointCongr_eq_zero_iff,
      pointMapRing_eq_zero_iff, map_eq_pointCongr_pointMapRing, pointCongr_eq_zero_iff,
      pointMapRing_eq_zero_iff]
  · rw [xOf_pointCongr, xOf_pointMapRing, xOf_pointCongr, xOf_pointMapRing, hf,
      map_eq_pointCongr_pointMapRing, xOf_pointCongr, xOf_pointMapRing]
    rfl
  · rw [yOf_pointCongr, yOf_pointMapRing, yOf_pointCongr, yOf_pointMapRing, hf,
      map_eq_pointCongr_pointMapRing, yOf_pointCongr, yOf_pointMapRing]
    rfl

end Composition
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section Setup

abbrev liftField₂ : Type _ :=
  ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField).toAffine.FunctionField

abbrev liftJ₂ : 𝒪 →+* gaussRing (gaussCurve W W') :=
  (algebraMap (gaussRing W) (gaussRing (gaussCurve W W'))).comp (algebraMap 𝒪 (gaussRing W))

theorem liftJ₂_algebraMap (c : 𝒪) :
    algebraMap K (liftField₂ K W W') (algebraMap 𝒪 K c) =
      algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (liftJ₂ W W' c) := by
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (gaussRing W) (gaussRing (gaussCurve W W')) (liftField₂ K W W'),
    IsScalarTower.algebraMap_apply (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W'),
    ← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField₂ K W W')]

theorem baseChange_liftField₂_eq :
    ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField).baseChange
      (liftField₂ K W W') = (W'.baseChange K).baseChange (liftField₂ K W W') := by
  rw [baseChange_baseChange]
  show W'.map (((algebraMap (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')).comp
      (algebraMap (gaussRing W) _)).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K (liftField₂ K W W')).comp (algebraMap 𝒪 K))
  refine congrArg W'.map (RingHom.ext fun c => ?_)
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField₂ K W W')]

variable [W'.IsElliptic]

def genPt₂ : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point :=
  pointCongr (baseChange_liftField₂_eq K W W')
    (GroundTheory.Arith.Abelian.genericPoint
      ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField))

theorem genPt₂_eq : ∃ h, genPt₂ K W W' = Point.some
    (algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (gaussX (gaussCurve W W')))
    (algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (gaussY (gaussCurve W W'))) h := by
  rw [genPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact exists_some_eq _
    (algebraMap_gaussX (gaussCurve W W') (W.baseChange K).toAffine.FunctionField).symm
    (algebraMap_gaussY (gaussCurve W W') (W.baseChange K).toAffine.FunctionField).symm

theorem transOver_genPt₂ :
    TransOver (W'.baseChange K) (W.baseChange K).toAffine.FunctionField (genPt₂ K W W') := by
  rw [genPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

end Setup

section Red

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W')))]

def red₂ (V : WeierstrassCurve 𝒪)
    (P : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    ((V.map (liftJ₂ W W')).map (residue (gaussRing (gaussCurve W W')))).toAffine.Point :=
  reducePoint (liftField₂ K W W') (V.map (liftJ₂ W W'))
    (pointCongr (map_baseChange_eq_map_of K V (liftJ₂ W W') (liftField₂ K W W')
      (liftJ₂_algebraMap K W W')) P)

theorem red₂_add (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (P Q : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    red₂ K W W' V (P + Q) = red₂ K W W' V P + red₂ K W W' V Q := by
  rw [red₂, red₂, red₂, map_add (f := _), reducePoint_add]

theorem red₂_zero (V : WeierstrassCurve 𝒪) : red₂ K W W' V 0 = 0 := by
  rw [red₂, map_zero, reducePoint_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem red₂_map_of_reduceFF_eq_zero
    {R : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hR : reduceFF K W W' R = 0) :
    red₂ K W W' W' (Point.map (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W')) R) = 0 := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have e := gaussCurve_map_functionField K W W'
  have h0 : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr e.symm R) = 0 := by
    have := hR
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      reductionHom_apply] at this
    rwa [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff] at this
  rcases point_cases (W.baseChange K).toAffine.FunctionField (gaussCurve W W') (pointCongr e.symm R)
    with hz | ⟨X₀, Y₀, h, hP, hX⟩ | ⟨x, y, h, hP⟩
  · rw [pointCongr_eq_zero_iff] at hz
    rw [hz, map_zero, red₂_zero]
  · have hRe : R = pointCongr e (Point.some _ _ h) := by
      rw [← hP, pointCongr_pointCongr]; rfl
    rw [pointCongr_some] at hRe
    subst hRe
    have hσ : (algebraMap (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')).comp
        (algebraMap (gaussRing W) _) = (algebraMap (gaussRing (gaussCurve W W'))
          (liftField₂ K W W')).comp (algebraMap (gaussRing W) _) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have hX' := map_notMem_range (W.baseChange K).toAffine.FunctionField (liftField₂ K W W') hσ hX
    rw [red₂, Point.map_some, pointCongr_some]
    exact reducePoint_some_notMem _ _ _ hX'
  · exfalso
    have n := nonsingular_residue_of_isElliptic _ _ h.1
    rw [hP, reducePoint_some_integral _ _ h n] at h0
    exact Point.some_ne_zero n h0

end Red
end

section
open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

theorem exists_algebraMap_eq_of_isAlgebraic_ff (E : WeierstrassCurve F) [E.IsElliptic]
    {u : E.toAffine.FunctionField} (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = u := by
  classical
  have hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F' := AlgebraicClosure F) E u) :=
    (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'
  exact exists_algebraMap_eq_of_bcEmb E hc.symm

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsGenPt E' Q := by
  classical
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · by_contra hx
    have hx' : IsAlgebraic F x := not_not.mp hx
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hx'
    have hy' : IsAlgebraic F y := by
      have := isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))
      exact mem_algebraicClosure_iff.1 this
    obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hy'
    have hc : (E'.baseChange F).toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField)
        (algebraMap F _).injective a b).mp h
    have hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) =
        Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc) := by
      rw [Point.map_some, Point.some.injEq]; exact ⟨rfl, rfl⟩
    have key := (respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E)
      (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)
    have hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E),
        Point.map σ (Point.some _ _ h) =
          Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc) := fun σ => by
      rw [hQc, Point.map_map]
      have e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E) :=
        AlgHom.ext fun z => by
          rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]
      rw [e]
    rw [hconst, hconst, hconst, left_eq_add] at key
    have := Point.map_injective (W' := E') (Algebra.ofId F (univField E))
      (key.trans (map_zero _).symm)
    exact Point.some_ne_zero hc this

theorem isIsogeny_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsIsogeny E E' Q :=
  (isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section E1

theorem injective_eval₂_residue_gaussX₂ :
    Function.Injective (eval₂RingHom (ResidueField.map (liftJ₂ W W'))
      (residue _ (gaussX (gaussCurve W W')))) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 := congrArg (gaussResidue (gaussCurve W W')) hp
  have hc : (gaussResidue (gaussCurve W W')).comp (ResidueField.map (liftJ₂ W W')) =
      (algebraMap (ResidueField (gaussRing W)) _).comp
        (ResidueField.map (algebraMap 𝒪 (gaussRing W))) := by
    rw [ResidueField.map_comp, ← RingHom.comp_assoc, gaussResidue_comp_residueField_map]
  rw [map_zero, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_gaussX, hc,
    ← Polynomial.eval₂_map, ← aeval_def] at h1
  have hmap : p.map (ResidueField.map (algebraMap 𝒪 (gaussRing W))) = 0 := by
    by_contra hne
    exact transcendental_genX ((gaussCurve W W').map (residue (gaussRing W))) ⟨_, hne, h1⟩
  exact (Polynomial.map_eq_zero_iff (ResidueField.map _).injective).1 hmap

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W')))] [W.IsElliptic] [W'.IsElliptic]

theorem red₂_def (V : WeierstrassCurve 𝒪)
    (P : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    red₂ K W W' V P = reducePoint (liftField₂ K W W') (V.map (liftJ₂ W W'))
      (pointCongr (map_baseChange_eq_map_of K V (liftJ₂ W W') (liftField₂ K W W')
        (liftJ₂_algebraMap K W W')) P) :=
  rfl

theorem red₂_genPt₂ : ∃ n, red₂ K W W' W' (genPt₂ K W W') = Point.some
    (residue _ (gaussX (gaussCurve W W'))) (residue _ (gaussY (gaussCurve W W'))) n := by
  obtain ⟨hT, eT⟩ := genPt₂_eq K W W'
  have h₁ : (curveK (liftField₂ K W W') (W'.map (liftJ₂ W W'))).Nonsingular
      (algebraMap _ (liftField₂ K W W') (gaussX (gaussCurve W W')))
      (algebraMap _ (liftField₂ K W W') (gaussY (gaussCurve W W'))) := by
    show ((W'.map (liftJ₂ W W')).map (algebraMap _ (liftField₂ K W W'))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') (liftJ₂_algebraMap K W W')]
    exact hT
  have n := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue _ (equation_of_map _ _ h₁.1))
  refine ⟨n, ?_⟩
  rw [red₂, eT, pointCongr_some]
  exact reducePoint_some_integral _ _ h₁ n

theorem red₂_genEval_eq_zero
    {ψ : ((W.baseChange K).baseChange (W'.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hψ : RespectsAdd (W'.baseChange K) (W.baseChange K) ψ)
    {P : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point}
    (hP : IsGenPt (W'.baseChange K) P) (hPT : IsGenPt (W'.baseChange K) (P + genPt₂ K W W'))
    (h0 : red₂ K W W' W' P = 0) :
    red₂ K W W' W (Point.map (genEval (W'.baseChange K) P hP) ψ) = 0 := by
  have hjM := liftJ₂_algebraMap K W W'
  have hTg : IsGenPt (W'.baseChange K) (genPt₂ K W W') := (transOver_genPt₂ K W W').isGenPt
  obtain ⟨nT, rT⟩ := red₂_genPt₂ K W W'
  obtain ⟨hT, eT⟩ := genPt₂_eq K W W'

  have rPT : red₂ K W W' W' (P + genPt₂ K W W') = red₂ K W W' W' (genPt₂ K W W') := by
    rw [red₂_add, h0, zero_add]
  have hne : reducePoint (liftField₂ K W W') (W'.map (liftJ₂ W W')) (pointCongr (map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') hjM)
      (P + genPt₂ K W W')) ≠ 0 := by
    rw [← red₂_def, rPT, rT]; exact Point.some_ne_zero _
  obtain ⟨x₃, y₃, h₃, e₃⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have n₃ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue _ (equation_of_map _ _ h₃.1))
  have rP3 : red₂ K W W' W' (P + genPt₂ K W W') = Point.some _ _ n₃ := by
    rw [red₂_def, e₃, reducePoint_some_integral _ _ h₃ n₃]
  rw [rPT, rT, Point.some.injEq] at rP3
  obtain ⟨ex, ey⟩ := rP3
  have hPT' : P + genPt₂ K W W' = pointCongr (map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') hjM).symm
      (Point.some _ _ h₃) := by
    rw [← e₃, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at hPT'
  obtain ⟨h₃', e₃'⟩ : ∃ h₃' : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Nonsingular
      (algebraMap _ (liftField₂ K W W') x₃) (algebraMap _ (liftField₂ K W W') y₃), P + genPt₂ K W W' = Point.some _ _ h₃' :=
    ⟨_, hPT'⟩

  have hxy₃ : (W'.map (liftJ₂ W W')).toAffine.Equation x₃ y₃ :=
    (WeierstrassCurve.Affine.map_equation (W'.map (liftJ₂ W W')).toAffine (IsFractionRing.injective _ (liftField₂ K W W'))
      x₃ y₃).mp h₃.1
  have hT₁ : (curveK (liftField₂ K W W') (W'.map (liftJ₂ W W'))).Nonsingular (algebraMap _ (liftField₂ K W W') (gaussX (gaussCurve W W')))
      (algebraMap _ (liftField₂ K W W') (gaussY (gaussCurve W W'))) := by
    show ((W'.map (liftJ₂ W W')).map (algebraMap _ (liftField₂ K W W'))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') hjM]; exact hT
  have hxyT : (W'.map (liftJ₂ W W')).toAffine.Equation (gaussX (gaussCurve W W')) (gaussY (gaussCurve W W')) :=
    (WeierstrassCurve.Affine.map_equation (W'.map (liftJ₂ W W')).toAffine (IsFractionRing.injective _ (liftField₂ K W W'))
      _ _).mp hT₁.1
  have hxT := injective_eval₂_residue_gaussX₂ W W'
  have hx₃ : Function.Injective (eval₂RingHom (ResidueField.map (liftJ₂ W W')) (residue _ x₃)) := by
    rw [← ex]; exact hxT
  have g₃ : IsGenPt (W'.baseChange K) (Point.some _ _ h₃') := e₃' ▸ hPT
  have gT : IsGenPt (W'.baseChange K) (Point.some _ _ hT) := eT ▸ hTg
  have m₃ := reducePoint_genEval (K := K) (W := W') (W' := W) (j := liftJ₂ W W') (M := liftField₂ K W W') (hxy := hxy₃)
    (hx := hx₃) hjM h₃' g₃ ψ
  have mT := reducePoint_genEval (K := K) (W := W') (W' := W) (j := liftJ₂ W W') (M := liftField₂ K W W') (hxy := hxyT)
    (hx := hxT) hjM hT gT ψ
  have hfe := fieldEvalRed_congr W' (liftJ₂ W W') hxy₃ hxyT hx₃ hxT ex.symm ey.symm

  have hadd := (respectsAdd_iff ψ).mp hψ (liftField₂ K W W') P (genPt₂ K W W') hP hTg hPT
  have hR : red₂ K W W' W (Point.map (genEval (W'.baseChange K) _ hPT) ψ) =
      red₂ K W W' W (Point.map (genEval (W'.baseChange K) _ hTg) ψ) := by
    rw [genEval_congr _ e₃' hPT g₃, genEval_congr _ eT hTg gT]
    rw [red₂_def, red₂_def, m₃, mT]
    apply point_ext_xy
    · rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, pointCongr_eq_zero_iff,
        pointMapRing_eq_zero_iff]
    · rw [xOf_pointCongr, xOf_pointMapRing, xOf_pointCongr, xOf_pointMapRing, hfe]
    · rw [yOf_pointCongr, yOf_pointMapRing, yOf_pointCongr, yOf_pointMapRing, hfe]
  rw [hadd, red₂_add] at hR
  exact add_eq_right.mp hR

end E1

section Isogeny

theorem reducePoint_some_ne_zero (V : WeierstrassCurve 𝒪) [V.IsElliptic] {X₀ Y₀ : K}
    (h : (curveK K V).Nonsingular X₀ Y₀) (hX : X₀ ∈ Set.range (algebraMap 𝒪 K)) :
    reducePoint K V (Point.some X₀ Y₀ h) ≠ 0 := by
  obtain ⟨x, rfl⟩ := hX
  obtain ⟨y, rfl⟩ := exists_y_of_equation K V h.1
  rw [reducePoint_some_integral K V h (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue V (equation_of_map K V h.1)))]
  exact Point.some_ne_zero _

variable [W.IsElliptic] [W'.IsElliptic]

theorem reduceFF_isogeny_ne_zero (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    reduceFF K W W' φ.1 ≠ 0 := by
  letI : DecidableEq (ResidueField (gaussRing (gaussCurve W W'))) := Classical.decEq _
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  letI : DecidableEq K := Classical.decEq K
  intro hφ
  have hP : IsGenPt (W'.baseChange K) (Point.map (IsScalarTower.toAlgHom K
      (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')) φ.1) :=
    isGenPt_map _ _ φ.isGenPt
  have hPT : IsGenPt (W'.baseChange K) (Point.map (IsScalarTower.toAlgHom K
      (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')) φ.1 + genPt₂ K W W') :=
    ((transOver_genPt₂ K W W').add_left φ.1).isGenPt
  have key := red₂_genEval_eq_zero K W W' (dualOver φ).respectsAdd hP hPT
    (red₂_map_of_reduceFF_eq_zero K W W' hφ)
  have hcomp := congrArg Subtype.val (dualOver_comp φ)
  rw [Isogeny.mulIsogeny_val] at hcomp
  have hc2 : Point.map (genEval (W'.baseChange K) φ.1 φ.isGenPt) (dualOver φ).1 =
      (φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K) := hcomp
  rw [genEval_map _ _ φ.isGenPt, ← Point.map_map, hc2] at key

  have hd : ((φ.degree : ℤ)) ≠ 0 := isogeny_degree_ne_zero φ
  have hne : reduceFF K W W ((φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))
      ≠ 0 := by
    rw [reduceFF_zsmul_genericPoint]
    exact zsmul_genericPoint_ne_zero _ hd
  have hne' : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W)
      (pointCongr (gaussCurve_map_functionField K W W).symm
        ((φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))) ≠ 0 := by
    intro h0
    apply hne
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]
    exact h0
  obtain ⟨a, b, h, e⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne'
  have e' : (φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K) =
      pointCongr (gaussCurve_map_functionField K W W) (Point.some _ _ h) := by
    rw [← e, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at e'
  rw [e'] at key
  have ha : ∀ g : gaussRing W, (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W')) (algebraMap (gaussRing W) _ g) =
        algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W')
          (algebraMap (gaussRing W) _ g) := fun g => by
    rw [IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  rw [Point.map_some, red₂_def, pointCongr_some] at key
  exact reducePoint_some_ne_zero _ _ _ ⟨_, (ha a).symm⟩ key

theorem isGenPt_reduceFF_isogeny (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    IsGenPt (W'.map (residue 𝒪)) (reduceFF K W W' φ.1) ∧
      RespectsAdd (W.map (residue 𝒪)) (W'.map (residue 𝒪)) (reduceFF K W W' φ.1) := by
  letI : DecidableEq (ResidueField (gaussRing (gaussCurve W W))) := Classical.decEq _
  have h := respectsAdd_reduceFF K W W' φ.1 φ.respectsAdd
  exact ⟨isGenPt_of_respectsAdd h (reduceFF_isogeny_ne_zero K W W' φ), h⟩

def reduceIsogeny (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    Isogeny (W.map (residue 𝒪)) (W'.map (residue 𝒪)) :=
  ⟨reduceFF K W W' φ.1, isIsogeny_of_respectsAdd (isGenPt_reduceFF_isogeny K W W' φ).2
    (reduceFF_isogeny_ne_zero K W W' φ)⟩

theorem reduceIsogeny_val (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    (reduceIsogeny K W W' φ).1 = reduceFF K W W' φ.1 :=
  rfl

theorem reduceIsogeny_comp (W'' : WeierstrassCurve 𝒪) [W''.IsElliptic]
    (ψ : Isogeny (W'.baseChange K) (W''.baseChange K))
    (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    reduceIsogeny K W W'' (ψ.comp φ) = (reduceIsogeny K W' W'' ψ).comp (reduceIsogeny K W W' φ) :=
  Subtype.ext (reduceFF_map_genEval K W W' W'' φ.isGenPt (isGenPt_reduceFF_isogeny K W W' φ).1 ψ.1)

theorem reduceIsogeny_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    reduceIsogeny K W W (mulIsogeny (W.baseChange K) n hn) = mulIsogeny (W.map (residue 𝒪)) n hn :=
  Subtype.ext (reduceFF_zsmul_genericPoint K W n)

end Isogeny
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section Translate

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem isGenPt_genericPoint_add_constMap (R : E.toAffine.Point) :
    IsGenPt E (genericPoint E + constMap E E.toAffine.FunctionField R) := by
  have hG : TransOver E F (genericPoint E) := transcendental_genX E
  have := hG.add_left (M := E.toAffine.FunctionField) R
  rw [add_comm]
  exact this.isGenPt

end Translate

section OverF

variable {F : Type u} [Field F] [DecidableEq F] {E E' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] (Ω : Type u) [Field Ω] [Algebra F Ω] [DecidableEq Ω]

omit [DecidableEq F] in
theorem isogBaseChange_app (φ : Isogeny E E')
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (hX : IsGenPt (E.baseChange Ω) X)
    (hX' : IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)) :
    (isogBaseChange (F' := Ω) φ).app X hX =
      φ.app (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) hX' := by
  have hg : ((genEval (E.baseChange Ω) X hX).restrictScalars F).comp (bcEmb (F' := Ω) E) =
      genEval E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
        hX' := by
    refine eq_genEval E _ ?_ _
    cases X with
    | zero => exact hX.elim
    | some u v hv =>
      simp only [GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
      congr 1
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genX E)) = u
        rw [bcEmb_genX]; exact genEval_genX (E.baseChange Ω) _ hX
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genY E)) = v
        rw [bcEmb_genY]; exact genEval_genY (E.baseChange Ω) _ hX
  unfold Isogeny.app
  rw [isogBaseChange_val, ← hg, ← Point.map_map]
  generalize Point.map (W' := E') (bcEmb (F' := Ω) E) φ.1 = Y
  cases Y <;> rfl

omit [DecidableEq F] [E.IsElliptic] [DecidableEq Ω] in
theorem isGenPt_of_isGenPt_baseChange
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (h : IsGenPt (E.baseChange Ω) X) :
    IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) := by
  cases X with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.restrictScalars (algebraMap F Ω).injective h

omit [E.IsElliptic] in
theorem constMap_constMap_baseChange (V : WeierstrassCurve F) (R : V.toAffine.Point) :
    (constMap (V.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField (constMap V Ω R) :
      (V.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) =
      constMap V (E.baseChange Ω).toAffine.FunctionField R := by
  cases R <;> rfl

theorem app_genericPoint_add_constMap [PerfectField F] [IsAlgClosed Ω] (φ : Isogeny E E')
    (R : E.toAffine.Point) :
    φ.app (genericPoint E + constMap E E.toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap E R) =
      φ.1 + constMap E' E.toAffine.FunctionField (pointHomOver Ω φ R) := by
  set K' := (E.baseChange Ω).toAffine.FunctionField
  set ι := bcEmb (F' := Ω) E
  set Rω := constMap E Ω R
  set φΩ := isogBaseChange (F' := Ω) φ
  have hGΩ : IsGenPt (E.baseChange Ω) (genericPoint (E.baseChange Ω)) :=
    transcendental_genX (E.baseChange Ω)
  have hX := isGenPt_genericPoint_add_constMap (E.baseChange Ω) Rω
  have h1 := φΩ.app_add_constMap hGΩ Rω hX
  rw [φΩ.app_genericPoint hGΩ, ← constMap_pointHomOver] at h1
  have app_eq : ∀ {P P' : (E.baseChange K').toAffine.Point} (h : P = P') (hP : IsGenPt E P)
      (hP' : IsGenPt E P'), φ.app P hP = φ.app P' hP' := by
    intro P P' h hP hP'; subst h; rfl
  have e1 : Point.map ι (genericPoint E + constMap E E.toAffine.FunctionField R) =
      ((genericPoint (E.baseChange Ω) + constMap (E.baseChange Ω) K' Rω :
        ((E.baseChange Ω).baseChange K').toAffine.Point) : (E.baseChange K').toAffine.Point) := by
    rw [map_add (f := _), map_bcEmb_genericPoint, map_constMap, ← constMap_constMap_baseChange Ω E R]
    rfl
  have hX' := isGenPt_of_isGenPt_baseChange Ω _ hX
  apply Point.map_injective (W' := E') ι
  rw [Isogeny.map_app]
  refine (app_eq e1 _ hX').trans ?_
  rw [← isogBaseChange_app Ω φ _ hX hX', h1, map_add (f := _), map_constMap,
    ← constMap_constMap_baseChange Ω (E := E) E' (pointHomOver Ω φ R)]
  rfl

end OverF

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem reduceFF_constMap (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (c : (V.baseChange K).toAffine.Point) :
    reduceFF K W V (constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField c) =
      constMap (V.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
        (reducePoint K V c) := by
  have hσ : (algebraMap K (W.baseChange K).toAffine.FunctionField).comp (algebraMap 𝒪 K) =
      (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp
        (algebraMap 𝒪 (gaussRing W)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  cases c with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | some X Y h =>
    by_cases hX : X ∈ Set.range (algebraMap 𝒪 K)
    · obtain ⟨x, rfl⟩ := hX
      obtain ⟨y, rfl⟩ := exists_y_of_equation K V h.1
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some _ _ h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField
            (algebraMap 𝒪 K x)) (algebraMap K (W.baseChange K).toAffine.FunctionField
              (algebraMap 𝒪 K y)) h₁ := ⟨_, rfl⟩
      have hx := RingHom.congr_fun hσ x
      have hy := RingHom.congr_fun hσ y
      simp only [RingHom.comp_apply] at hx hy
      obtain ⟨h₂, e₂⟩ := exists_some_eq h₁ hx hy
      obtain ⟨h₃, e₃⟩ := reduceFF_some K W V h₂
      rw [e₁, e₂, e₃]
      have e₄ := reducePoint_some_integral K V h
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (equation_residue V (equation_of_map K V h.1)))
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      show _ = Point.some _ _ _
      simp only [Point.some.injEq, gaussResidue_residue_algebraMap]
      exact ⟨rfl, rfl⟩
    · have hX' := map_notMem_range K (W.baseChange K).toAffine.FunctionField
        (f := algebraMap 𝒪 (gaussRing W)) hσ hX
      have e₄ := reducePoint_some_notMem K V h hX
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some X Y h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField X)
            (algebraMap K (W.baseChange K).toAffine.FunctionField Y) h₁ := ⟨_, rfl⟩
      rw [e₁, map_zero]
      simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        reductionHom_apply]
      rw [pointCongr_some, reducePoint_some_notMem _ (gaussCurve W V) _ hX', map_zero, map_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem reduceFF_genericPoint_add_constMap (R : (W.baseChange K).toAffine.Point) :
    reduceFF K W W (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R) =
      genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R) := by
  rw [map_add (f := _), reduceFF_genericPoint, reduceFF_constMap]

theorem reduceIsogeny_app_add_constMap (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) (S : (W'.baseChange K).toAffine.Point)
    (h : φ.app (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap _ R) =
      φ.1 + constMap (W'.baseChange K) (W.baseChange K).toAffine.FunctionField S) :
    (reduceIsogeny K W W' φ).app (genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R)) (isGenPt_genericPoint_add_constMap _ _) =
      (reduceIsogeny K W W' φ).1 + constMap (W'.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField (reducePoint K W' S) := by
  have hR' : IsGenPt (W.map (residue 𝒪)) (reduceFF K W W (genericPoint (W.baseChange K) +
      constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)) := by
    rw [reduceFF_genericPoint_add_constMap]
    exact isGenPt_genericPoint_add_constMap _ _
  have key := reduceFF_map_genEval K W W W' (isGenPt_genericPoint_add_constMap _ R) hR' φ.1
  have h2 := congrArg (reduceFF K W W') h
  rw [map_add (f := _), reduceFF_constMap] at h2
  rw [reduceIsogeny_val, ← h2]
  unfold Isogeny.app at key ⊢
  rw [key, reduceIsogeny_val, genEval_congr _ (reduceFF_genericPoint_add_constMap K W R) hR']

end Reduction

section PointsOverPerfect

universe v w

variable {𝒪 : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type v) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [PerfectField K] [PerfectField (ResidueField 𝒪)]
  (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
  (Ωk : Type w) [Field Ωk] [Algebra (ResidueField 𝒪) Ωk] [IsAlgClosed Ωk] [DecidableEq Ωk]

theorem reducePoint_pointHomOver (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) :
    reducePoint K W' (pointHomOver Ω φ R) =
      pointHomOver Ωk (reduceIsogeny K W W' φ) (reducePoint K W R) := by
  have h := reduceIsogeny_app_add_constMap K W W' φ R _ (app_genericPoint_add_constMap Ω φ R)
  rw [app_genericPoint_add_constMap Ωk (reduceIsogeny K W W' φ) (reducePoint K W R),
    add_right_inj] at h
  exact (constMap_injective _ _ h).symm

end PointsOverPerfect
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section SlopeTestRemainingChoices

theorem exists_gaussResidue_eq (z : (W.map (residue 𝒪)).toAffine.FunctionField) :
    ∃ b : gaussRing W, gaussResidue W (residue _ b) = z := by
  obtain ⟨a, s, hs, rfl⟩ :=
    IsFractionRing.div_surjective (A := (W.map (residue 𝒪)).toAffine.CoordinateRing) z
  obtain ⟨a', rfl⟩ := coordReduce_surjective W a
  obtain ⟨s', rfl⟩ := coordReduce_surjective W s
  have hs' : s' ∈ (gaussPrime W).primeCompl := fun h =>
    nonZeroDivisors.ne_zero hs (RingHom.mem_ker.1 h)
  refine ⟨IsLocalization.mk' (gaussRing W) a' ⟨s', hs'⟩, ?_⟩
  have hspec := IsLocalization.mk'_spec (gaussRing W) a' ⟨s', hs'⟩
  have := congrArg (fun b => gaussResidue W (residue _ b)) hspec
  simp only [map_mul, gaussResidue_residue] at this
  have hne : algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField (coordReduce W s') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hs)
  rw [eq_div_iff hne]
  exact this

end SlopeTestRemainingChoices

section Isog

variable [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))

theorem exists_isogeny_coords : ∃ (x y : gaussRing W)
    (h : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap _ _ x) (algebraMap _ _ y)), φ.1 = Point.some _ _ h := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr (gaussCurve_map_functionField K W W').symm φ.1) ≠ 0 := by
    intro h0
    apply reduceFF_isogeny_ne_zero K W W' φ
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]
    exact h0
  obtain ⟨x, y, h, e⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have e' : φ.1 = pointCongr (gaussCurve_map_functionField K W W') (Point.some _ _ h) := by
    rw [← e, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at e'
  exact ⟨x, y, _, e'⟩

theorem degree_reduceIsogeny_le : (reduceIsogeny K W W' φ).degree ≤ φ.degree := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) _ (algebraMap 𝒪 (gaussRing W) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation x y := by
    have h₁ : ((W'.map (algebraMap 𝒪 (gaussRing W))).map
        (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' (algebraMap 𝒪 (gaussRing W)) _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W)))
      (residue _ x)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := by
      have := (reduceIsogeny K W W' φ).isGenPt
      rw [hφ'] at this
      exact this
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (gaussResidue W (residue _ x)) p = gaussResidue W
        (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W))) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]
    rw [key, hp, map_zero]
  set g := gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx
  have hσ : (φ.comap : _ →+* _).comp (algebraMap (gaussRing W')
      (W'.baseChange K).toAffine.FunctionField) =
        (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp g := by
    apply comp_algebraMap_gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx K
    · intro c
      show φ.comap (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, φ.comap.commutes, hjM]
    · show φ.comap (genX _) = _
      rw [φ.comap_genX, Isogeny.x, hφ]; rfl
    · show φ.comap (genY _) = _
      rw [φ.comap_genY, Isogeny.y, hφ]; rfl
  have hring : (gaussResidue W).comp (fieldEvalRed W' (algebraMap 𝒪 (gaussRing W)) hxy hx) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _) := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((reduceIsogeny K W W' φ).comap.commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX]
      show _ = (reduceIsogeny K W W' φ).comap (genX _)
      rw [Isogeny.comap_genX, Isogeny.x, hφ']; rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY]
      show _ = (reduceIsogeny K W W' φ).comap (genY _)
      rw [Isogeny.comap_genY, Isogeny.y, hφ']; rfl
  have hres : (gaussResidue W).comp (ResidueField.map g) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _).comp (gaussResidue W') := by
    rw [residueField_map_gaussLift, ← RingHom.comp_assoc, hring]
  haveI := φ.finiteDimensional
  haveI := (reduceIsogeny K W W' φ).finiteDimensional
  haveI : Module.Free (reduceIsogeny K W W' φ).comap.fieldRange
      (W.map (residue 𝒪)).toAffine.FunctionField := Module.Free.of_divisionRing _ _
  set bb := Module.finBasis (reduceIsogeny K W W' φ).comap.fieldRange
    (W.map (residue 𝒪)).toAffine.FunctionField
  choose b hb using fun i => exists_gaussResidue_eq W (bb i)
  have hli : LinearIndependent φ.comap.fieldRange
      (fun i => algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (b i)) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc i₀
    by_contra hci
    choose f hf using fun i => AlgHom.mem_fieldRange.1 (c i).2
    obtain ⟨⟨s, hs⟩, hsf⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors (gaussRing W')) Finset.univ f
    choose a ha using fun i => hsf i (Finset.mem_univ i)

    have hrel : ∑ i, g (a i) * b i = 0 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField

      rw [map_sum, map_zero]
      have h1 := congrArg (fun z => φ.comap (algebraMap _ _ s) * z) hc
      simp only [mul_zero, Finset.mul_sum, Algebra.smul_def, IntermediateField.algebraMap_apply]
        at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← RingHom.comp_apply (algebraMap (gaussRing W) _) g, ← hσ, RingHom.comp_apply,
        ← mul_assoc]
      congr 1
      rw [← hf i, ← map_mul]
      show φ.comap (algebraMap _ _ (a i)) = φ.comap (algebraMap _ _ s * f i)
      rw [ha i, Algebra.smul_def]
    have hinj : ∀ z : gaussRing W', z ≠ 0 → g z ≠ 0 := fun z hz h0 => by
      have h2 : (φ.comap : (W'.baseChange K).toAffine.FunctionField →+*
          (W.baseChange K).toAffine.FunctionField) (algebraMap (gaussRing W')
          (W'.baseChange K).toAffine.FunctionField z) = 0 := by
        rw [← RingHom.comp_apply, hσ, RingHom.comp_apply, h0, map_zero]
      rw [map_eq_zero_iff _ (RingHom.injective _),
        map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h2
      exact hz h2
    have hai₀ : a i₀ ≠ 0 := by
      intro h0
      apply hci
      have := ha i₀
      rw [h0, map_zero, eq_comm, smul_eq_zero] at this
      rcases this with h1 | h1
      · exact (nonZeroDivisors.ne_zero hs h1).elim
      · exact Subtype.ext (by rw [← hf i₀, h1, map_zero]; rfl)
    obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => a i ≠ 0)
      (fun i => IsDiscreteValuationRing.addVal (gaussRing W') (a i)) ⟨i₀, by simp [hai₀]⟩
    have hai₁ : a i₁ ≠ 0 := (Finset.mem_filter.1 hi₁).2
    have hdvd : ∀ i, a i₁ ∣ a i := fun i => by
      by_cases hi : a i = 0
      · rw [hi]; exact dvd_zero _
      · exact (IsDiscreteValuationRing.addVal_le_iff_dvd).1
          (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩))
    choose a' ha' using hdvd
    have ha'₁ : a' i₁ = 1 := by
      have := ha' i₁
      exact (mul_eq_left₀ hai₁).1 this.symm
    have hrel' : ∑ i, g (a' i) * b i = 0 := by
      have : g (a i₁) * ∑ i, g (a' i) * b i = 0 := by
        rw [Finset.mul_sum, ← hrel]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ha' i, map_mul, mul_assoc]
      exact (mul_eq_zero.1 this).resolve_left (hinj _ hai₁)
    have hred' := congrArg (fun z => gaussResidue W (residue _ z)) hrel'

    simp only [map_sum, map_mul, map_zero, hb] at hred'
    have hcoef : ∀ i, gaussResidue W (residue _ (g (a' i))) =
        (reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))) := fun i => by
      rw [← ResidueField.map_residue, ← RingHom.comp_apply, hres]; rfl
    have hli' := bb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli'
    have h0 := hli' (fun i => ⟨(reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))),
      ⟨_, rfl⟩⟩) (by
        simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
        rw [← hred']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoef])
      i₁
    have h1 := congrArg Subtype.val h0
    simp only [ha'₁, map_one, ZeroMemClass.coe_zero] at h1
    exact one_ne_zero h1
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem degree_reduceIsogeny : (reduceIsogeny K W W' φ).degree = φ.degree := by
  have h1 := degree_reduceIsogeny_le K W W' φ
  have h2 := degree_reduceIsogeny_le K W' W (dualOver φ)
  rw [degree_dualOver] at h2
  have hc := reduceIsogeny_comp K W W' W (dualOver φ) φ
  rw [dualOver_comp, reduceIsogeny_mulIsogeny] at hc
  have hdeg := congrArg Isogeny.degree hc
  rw [degree_mulIsogeny, Isogeny.degree_comp, Int.natAbs_natCast] at hdeg
  have hpos := φ.degree_pos
  have hpos' := (reduceIsogeny K W W' φ).degree_pos
  apply le_antisymm h1
  by_contra! hlt
  have : (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree <
      φ.degree ^ 2 := sq φ.degree ▸ Nat.mul_lt_mul_of_le_of_lt h2 hlt hpos
  omega

end Isog
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped Polynomial.Bivariate

universe u

section Delta

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDeriv (f : E.toAffine.FunctionField) : E.toAffine.FunctionField :=
  invCoeff E (D F E.toAffine.FunctionField f)

theorem invCoeff_smul_mul (c : E.toAffine.FunctionField) (η : KaehlerDifferential F E.toAffine.FunctionField) :
    invCoeff E (c • η) = c * invCoeff E η :=
  invCoeff_eq E (by rw [mul_smul, invCoeff_smul])

theorem invDeriv_add (f g : E.toAffine.FunctionField) :
    invDeriv E (f + g) = invDeriv E f + invDeriv E g := by
  rw [invDeriv, map_add (f := _), invCoeff_add]; rfl

theorem invDeriv_mul (f g : E.toAffine.FunctionField) :
    invDeriv E (f * g) = f * invDeriv E g + g * invDeriv E f := by
  rw [invDeriv, Derivation.leibniz, invCoeff_add, invCoeff_smul_mul, invCoeff_smul_mul]; rfl

theorem invDeriv_algebraMap (c : F) : invDeriv E (algebraMap F _ c) = 0 := by
  rw [invDeriv, D_coeff, invCoeff_zero]

theorem invDeriv_genX : invDeriv E (genX E) = 2 * genY E +
    algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃ := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).1

theorem invDeriv_genY : invDeriv E (genY E) = 3 * genX E ^ 2 +
    2 * algebraMap F _ E.a₂ * genX E + algebraMap F _ E.a₄ - algebraMap F _ E.a₁ * genY E := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).2

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]

theorem isogCoeff_mul (φ : Isogeny E E') {x y : E.toAffine.FunctionField}
    {h : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y}
    (hφ : φ.1 = Point.some x y h) :
    isogCoeff φ * (2 * y + algebraMap F _ E'.a₁ * x + algebraMap F _ E'.a₃) = invDeriv E x := by
  have e := (omegaAt_some_spec E' h).1
  rw [← hφ, ← isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential_eq_smul,
    smul_smul] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at e
  rw [invDeriv, invCoeff_eq E e]
  ring

end Delta

section Dual

open TrivSqZeroExt

def dualMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun z := inl (f z.fst) + inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem dualMap_fst {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).fst = f z.fst := by simp [dualMap]

theorem dualMap_snd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).snd = f z.snd := by simp [dualMap]

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDerivHom : E.toAffine.FunctionField →+*
    TrivSqZeroExt E.toAffine.FunctionField E.toAffine.FunctionField where
  toFun f := inl f + inr (invDeriv E f)
  map_one' := by
    have h1 : invDeriv E 1 = 0 := by
      rw [← map_one (algebraMap F E.toAffine.FunctionField), invDeriv_algebraMap]
    ext <;> simp [h1]
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop, invDeriv_mul]
    ring
  map_zero' := by
    have h0 : invDeriv E 0 = 0 := by
      simpa using invDeriv_algebraMap E 0
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [invDeriv_add]

theorem invDerivHom_fst (f : E.toAffine.FunctionField) : (invDerivHom E f).fst = f := by
  simp [invDerivHom]

theorem invDerivHom_snd (f : E.toAffine.FunctionField) :
    (invDerivHom E f).snd = invDeriv E f := by
  simp [invDerivHom]

end Dual

section Gauss

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def gaussDX : gaussRing W :=
  2 * gaussY W + algebraMap 𝒪 _ W.a₁ * gaussX W + algebraMap 𝒪 _ W.a₃

def gaussDY : gaussRing W :=
  3 * gaussX W ^ 2 + 2 * algebraMap 𝒪 _ W.a₂ * gaussX W + algebraMap 𝒪 _ W.a₄ -
    algebraMap 𝒪 _ W.a₁ * gaussY W

theorem gauss_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation (gaussX W) (gaussY W) := by
  have h := equation_gen (W.baseChange K)
  rw [← algebraMap_gaussX W K, ← algebraMap_gaussY W K] at h
  have e : (W.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField =
      (W.map (algebraMap 𝒪 (gaussRing W))).map (algebraMap (gaussRing W) _) :=
    (gaussCurve_map_functionField K W W).symm
  rw [e] at h
  exact (WeierstrassCurve.Affine.map_equation (W.map (algebraMap 𝒪 (gaussRing W))).toAffine
    (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) _ _).mp h

theorem gauss_dual_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map ((inlHom (gaussRing W) (gaussRing W)).comp (algebraMap 𝒪 (gaussRing W)))).toAffine.Equation
      (inl (gaussX W) + inr (gaussDX W)) (inl (gaussY W) + inr (gaussDY W)) := by
  have e := (WeierstrassCurve.Affine.equation_iff _ _).1 (gauss_equation W K)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, RingHom.comp_apply, inlHom_apply]
  ext
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, add_zero]
    linear_combination e
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, snd_add, snd_mul, snd_pow, snd_inl,
      snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      nsmul_eq_mul, Nat.cast_ofNat, Nat.pred_eq_sub_one, zero_mul]
    simp only [gaussDX, gaussDY]
    norm_num
    ring

end Gauss

section GaussDeriv

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

def gaussDualA : W.toAffine.CoordinateRing →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  AdjoinRoot.lift (eval₂RingHom ((inlHom (gaussRing W) (gaussRing W)).comp
      (algebraMap 𝒪 (gaussRing W))) (inl (gaussX W) + inr (gaussDX W)))
    (inl (gaussY W) + inr (gaussDY W))
    (eval₂_polynomial_of_equation W _ (gauss_dual_equation W K))

theorem gaussDualA_algebraMap (c : 𝒪) :
    gaussDualA K W (algebraMap 𝒪 _ c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_X :
    gaussDualA K W (CoordinateRing.mk W (C X)) = inl (gaussX W) + inr (gaussDX W) := by
  rw [AdjoinRoot.mk_C, gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_Y :
    gaussDualA K W (CoordinateRing.mk W Y) = inl (gaussY W) + inr (gaussDY W) := by
  rw [AdjoinRoot.mk_X, gaussDualA, AdjoinRoot.lift_root]

theorem fst_gaussDualA (a : W.toAffine.CoordinateRing) :
    (gaussDualA K W a).fst = algebraMap _ (gaussRing W) a := by
  have : ((fstHom 𝒪 (gaussRing W) (gaussRing W)).toRingHom).comp (gaussDualA K W) =
      algebraMap _ (gaussRing W) := by
    apply coordinateRing_ringHom_ext
    · intro c
      simp [gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]
    · show (gaussDualA K W (CoordinateRing.mk W (C X))).fst = _
      rw [gaussDualA_X, fst_add, fst_inl, fst_inr, add_zero]; rfl
    · show (gaussDualA K W (CoordinateRing.mk W Y)).fst = _
      rw [gaussDualA_Y, fst_add, fst_inl, fst_inr, add_zero]; rfl
  exact congrArg (fun f => f a) this

def gaussDual : gaussRing W →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W) (g := gaussDualA K W)
    fun s => isUnit_iff_isUnit_fst.2 (by
      rw [fst_gaussDualA]; exact IsLocalization.map_units (gaussRing W) s)

theorem gaussDual_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussDual K W (algebraMap _ _ a) = gaussDualA K W a :=
  IsLocalization.lift_eq _ _

theorem gaussDual_algebraMap_base (c : 𝒪) :
    gaussDual K W (algebraMap 𝒪 (gaussRing W) c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussDual_algebraMap, gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]

def gaussDeriv (g : gaussRing W) : gaussRing W := (gaussDual K W g).snd

end GaussDeriv

section Compat

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic]

theorem algebraMap_gauss_const (c : 𝒪) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 _ c) =
      algebraMap K _ (algebraMap 𝒪 K c) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply 𝒪 K]

theorem algebraMap_gaussDeriv (g : gaussRing W) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussDeriv K W g) =
      invDeriv (W.baseChange K) (algebraMap (gaussRing W) _ g) := by
  have key : (dualMap (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField)).comp
      (gaussDual K W) = (invDerivHom (W.baseChange K)).comp (algebraMap (gaussRing W) _) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero, algebraMap_gauss_const,
          invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl, algebraMap_gaussX]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussX]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genX,
          gaussDX]
        simp only [map_add (f := _), map_mul, map_ofNat, algebraMap_gaussX, algebraMap_gaussY,
          algebraMap_gauss_const]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl, algebraMap_gaussY]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussY]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genY,
          gaussDY]
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, algebraMap_gaussX,
          algebraMap_gaussY, algebraMap_gauss_const]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

theorem gaussResidue_gaussDeriv (g : gaussRing W) :
    gaussResidue W (residue _ (gaussDeriv K W g)) =
      invDeriv (W.map (residue 𝒪)) (gaussResidue W (residue _ g)) := by
  have key : (dualMap ((gaussResidue W).comp (residue (gaussRing W)))).comp (gaussDual K W) =
      (invDerivHom (W.map (residue 𝒪))).comp ((gaussResidue W).comp (residue (gaussRing W))) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero,
          gaussResidue_residue_algebraMap, invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussX, invDeriv_genX, gaussDX]
        simp only [map_add (f := _), map_mul, map_ofNat, RingHom.comp_apply, gaussResidue_gaussX,
          gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussY, invDeriv_genY, gaussDY]
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, RingHom.comp_apply,
          gaussResidue_gaussX, gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

end Compat

section Isog

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))

theorem exists_invConst_reduceIsogeny :
    ∃ c : 𝒪, algebraMap 𝒪 K c = invConst φ ∧
      residue 𝒪 c = invConst (reduceIsogeny K W W' φ) := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  set u : gaussRing W := 2 * y + algebraMap 𝒪 _ W'.a₁ * x + algebraMap 𝒪 _ W'.a₃ with hu_def

  have hu_res : gaussResidue W (residue _ u) = 2 * gaussResidue W (residue _ y) +
      algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₁ * gaussResidue W (residue _ x) +
        algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₃ := by
    simp only [hu_def, map_add (f := _), map_mul, map_ofNat, gaussResidue_residue_algebraMap]
    rfl
  have hu_ne : gaussResidue W (residue _ u) ≠ 0 := by
    have hg := (reduceIsogeny K W W' φ).isGenPt
    rw [hφ'] at hg
    have hd := genDen_ne_zero (W'.map (residue 𝒪))
    intro h0
    apply hd
    apply (genEval (W'.map (residue 𝒪)) _ hg).toRingHom.injective
    rw [map_zero, ← h0, hu_res]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), map_mul, map_ofNat,
      AlgHom.commutes, genEval_genX, genEval_genY]
    rfl
  have hu : IsUnit u := by
    by_contra hnu
    exact hu_ne (by rw [(residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hnu), map_zero])

  have e1 : isogCoeff φ * algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u =
      algebraMap (gaussRing W) _ (gaussDeriv K W x) := by
    rw [algebraMap_gaussDeriv, ← isogCoeff_mul φ hφ]
    congr 1
    simp only [hu_def, map_add (f := _), map_mul, map_ofNat, algebraMap_gauss_const]
    rfl
  set v : gaussRing W := gaussDeriv K W x * ↑hu.unit⁻¹ with hv_def
  have hv : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField v = isogCoeff φ := by
    have hne : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hu.ne_zero
    rw [hv_def, map_mul, ← e1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

  have hint : invConst φ ∈ Set.range (algebraMap 𝒪 K) := by
    by_contra hX
    obtain ⟨t, ht, hte⟩ := exists_inv_mem_of_notMem_range K hX
    have hc0 : invConst φ ≠ 0 := fun h0 => hX ⟨0, by rw [map_zero, h0]⟩
    have h1 : v * algebraMap 𝒪 (gaussRing W) t = 1 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      rw [map_mul, hv, algebraMap_gauss_const, hte, ← algebraMap_invConst, map_inv₀,
        mul_inv_cancel₀ ((_root_.map_ne_zero _).2 hc0), map_one]
    have : IsUnit (algebraMap 𝒪 (gaussRing W) t) :=
      isUnit_iff_exists_inv.2 ⟨v, by rw [mul_comm]; exact h1⟩
    exact (mem_maximalIdeal _).1 ht ((isUnit_map_iff (algebraMap 𝒪 (gaussRing W)) t).1 this)
  obtain ⟨c, hc⟩ := hint
  refine ⟨c, hc, ?_⟩
  have hvc : algebraMap 𝒪 (gaussRing W) c = v := by
    apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
    rw [algebraMap_gauss_const, hc, algebraMap_invConst, hv]

  have e2 := isogCoeff_mul (reduceIsogeny K W W' φ) hφ'
  rw [← gaussResidue_gaussDeriv K W x] at e2
  have e2' : isogCoeff (reduceIsogeny K W W' φ) = gaussResidue W (residue _ v) := by
    have hres_u : gaussResidue W (residue _ u) * gaussResidue W (residue _ ↑hu.unit⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, IsUnit.mul_val_inv, map_one, map_one]
    rw [hv_def, map_mul, map_mul, ← e2, ← hu_res, mul_assoc, hres_u, mul_one]
  apply (algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField).injective
  rw [algebraMap_invConst, e2', ← hvc, gaussResidue_residue_algebraMap]

end Isog
end

end GroundTheory.Global
