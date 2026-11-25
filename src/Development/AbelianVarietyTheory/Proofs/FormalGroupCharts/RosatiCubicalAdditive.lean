module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosatiCube

open ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def IsNormGen (L : LB A.left) (f g : A ⟶ A) (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)

variable {L : LB A.left}

theorem IsNormGen.val_origin {f g : A ⟶ A} {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsNormGen L f g u)
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this

omit [IsCommMonObj A] in
theorem val_pull_pair {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (a b : T ⟶ A) :
    val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl

theorem pair_unique_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good L y J → val u (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J =
      val u' (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left y J)
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ A).left) {z : Z} {J} (hJ : Good L z J) : val u r z J = val u' r z J :=
  gen_unique' hL hF (A ⊗ A).hom _
    (Over.w (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)))
    sj hu hu' h Z r z J hJ

variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem ros_add_of_surj (sj : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.ros_add_of_surj c sj f g u hu h₀ hJ x x' y

theorem ros_sum_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) {f g f₁ g₁ f₂ g₂ : A ⟶ A}
    (hf : f = f₁ * f₂) (hg : g = g₁ * g₂) {u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsNormGen Lr.L f g u) (hu₁ : IsNormGen Lr.L f₁ g₁ u₁) (hu₂ : IsNormGen Lr.L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x w : T ⟶ A) :
    val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) =
      cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := by
  subst hf hg
  have ev : ∀ {T : Over S} {z : T.left} {J}, Good Lr.L z J → ∀ x w : T ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (fst A A) (snd A A)).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (snd A A ≫ g₁) (snd A A ≫ g₂))).left))
        (lift x w).left z J = val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) ∧
      val (LB.mulGen Lr.L _ _ _ _
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (lift (fst A A) (snd A A)).left)
          (LB.pullGen Lr.L _ _ u₂ (lift (fst A A) (snd A A)).left))) (lift x w).left z J =
        cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := fun hJ x w =>
    ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull_pair u _ hJ _ _) (val_cub c _ hJ _ _ _))).trans (by
      rw [lift_snd_assoc, lift_snd_assoc, lift_fst, lift_snd]),
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull_pair u₁ _ hJ _ _) (val_pull_pair u₂ _ hJ _ _))))).trans (by
      rw [lift_fst_assoc, lift_fst_assoc, lift_fst, lift_snd])⟩
  refine (ev hJ x w).1.symm.trans (Eq.trans (pair_unique_of_surj sj Lr.isLB (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ c.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _)
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₁.1 _) (pullGen_isGen _ _ _ _ hu₂.1 _)))
    (fun y I hI => ?_) _ hJ) (ev hJ x w).2)
  · refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := U) _ (prod_cub _ _ _ h)
      (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros _ _ _ _ h) (prod_ros _ _ _ _ h))).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := U) _ (prod_ros _ _ _ _ h) (prod_cub _ _ _ h)).symm)
    rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV c y I) := isCub_cubV c hI
    refine (ev hI 1 1).1.trans (Eq.trans ?_ (ev hI 1 1).2.symm)
    rw [hu.val_origin hI, hu₁.val_origin hI, hu₂.val_origin hI, C.face, C.face₃, _root_.mul_one, _root_.mul_one]

theorem rosati_cubical_additive : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, (u a).IsGen ∧ LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ (u a) (zero2 G)) (LB.oneGen Lr.L)) → ∀ (T : Over S) (z : T.left) (J), Good Lr.L z J → (∀ (a : O) (x x' y : T ⟶ G), val₂ (u a) z J (x * x') y * cubV c z J x x' (y ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) (x' ≫ act.act a) y * (val₂ (u a) z J x y * val₂ (u a) z J x' y)) ∧ (∀ (a : O) (x y y' : T ⟶ G), val₂ (u a) z J x (y * y') * cubV c z J x (y ≫ act.act (star a)) (y' ≫ act.act (star a)) = cubV c z J (x ≫ act.act a) y y' * (val₂ (u a) z J x y * val₂ (u a) z J x y')) ∧ (∀ (a b : O) (x y : T ⟶ G), val₂ (u (a + b)) z J x y * cubV c z J x (y ≫ act.act (star a)) (y ≫ act.act (star b)) = cubV c z J (x ≫ act.act a) (x ≫ act.act b) y * (val₂ (u a) z J x y * val₂ (u b) z J x y)) := by
  intro S G _ _ s₂ s₃ Lr c O _ _ act u hu T z J hJ
  refine ⟨fun a x x' y => ?_, fun a x y y' => ?_, fun a b x y => ?_⟩
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ x x' y).1
  · have := act.hom a
    have := act.hom (star a)
    exact (ros_add_of_surj c s₃ _ _ (u a) (hu a).1 (hu a).2 hJ y y' x).2
  · exact ros_sum_of_surj c s₂ (act.add a b) (by rw [star_add, act.add]) (hu (a + b)) (hu a) (hu b) hJ x y

end GlobalTheory.RosatiCube
