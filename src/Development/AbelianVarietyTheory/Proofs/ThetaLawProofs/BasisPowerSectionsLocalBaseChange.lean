module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

@[expose] public section

noncomputable section

namespace GlobalTheory.KeyBasis

section Universal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.SectionLimit

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_universal_basis (hS : SecBaseChangeSt) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ β : Fin (n ^ P.g) → H0 P.L n, ∀ (C : Type) [CommRing C] (q : Sp C ⟶ Sp R) (Y : Scheme.{0})
      (π : Y ⟶ P.A.left) (f : Y ⟶ Sp C), IsPullback f π q P.A.hom → ∀ s, ∃! c, Rep π f β s c :=
  exists_basis_pow hS R P n hn

end Universal

section Transfer

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SectionLimit

variable {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {C : Type} [CommRing C] {n N : ℕ}

theorem mem_wc {g : Y ⟶ X} {j : L.ι} {y : Y} (h : g y ∈ L.U j) :
    y ∈ LB.wchart L (fun _ : Fin 1 => g) (fun _ => j) := Set.mem_iInter.2 fun _ => h

theorem gs_cst (p : Y ⟶ Sp C) (W : Y.Opens) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ W) (a : C) :
    gs r z W (AbLaw.cst p W a) = cst (r ≫ p) z a :=
  (gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _)

theorem gs_comb (p : Y ⟶ Sp C) (W : Y.Opens) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ W) (c : Fin N → C)
    (a : Fin N → Γ(Y, W)) :
    gs r z W (∑ k, AbLaw.cst p W (c k) * a k) = ∑ k, cst (r ≫ p) z (c k) * gs r z W (a k) := by

  simp only [← gs_cst p W r z hz, gs_eq r z W hz, map_sum, map_mul]

theorem gs_congr {W : Y.Opens} (r : Z ⟶ Y) (z : Z) {a b : Γ(Y, W)} (h : a = b) : gs r z W a = gs r z W b := by rw [h]

theorem transfer (hL : L.IsLB) (hM : M.IsLB) (φ : Y ⟶ X) (p : Y ⟶ Sp C) (β : Fin N → Out.H0 L n)
    (b : Fin N → ∀ i, Γ(Y, M.U i)) (a : ∀ i, Γ(Y, M.U i))
    (u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : L.ι) (_ : M.ι), (Z.presheaf.stalk z)ˣ)
    (hb : ∀ k (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι) (i : M.ι), φ (r z) ∈ L.U j → r z ∈ M.U i →
      gs (r ≫ φ) z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) ((β k).f fun _ => j) =
        (u Z r z j i).val * gs r z (M.U i) (b k i))
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (n : ℤ))))
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι) (i : M.ι), φ (r z) ∈ L.U j → r z ∈ M.U i →
      gs r z (LB.wchart L (fun _ : Fin 1 => φ) (fun _ => j)) (s.f fun _ => j) =
        (u Z r z j i).val * gs r z (M.U i) (a i)) (c : Fin N → C) :
    Rep φ p β s c ↔ ∀ i, a i = ∑ k, AbLaw.cst p (M.U i) (c k) * b k i := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (i : M.ι), Good L z J → r z ∈ M.U i →
      (sval s r z J = ∑ k, cst (r ≫ p) z (c k) * sval (β k) (r ≫ φ) z J ↔
        gs r z (M.U i) (a i) = gs r z (M.U i) (∑ k, AbLaw.cst p (M.U i) (c k) * b k i)) := by
    intro Z r z J i hJ hi
    have hj : φ (r z) ∈ L.U (J (r ≫ φ)) := hJ (r ≫ φ)
    have e : ∀ k, sval (β k) (r ≫ φ) z J = (u Z r z (J (r ≫ φ)) i).val * gs r z (M.U i) (b k i) := fun k =>
      (sval_of (β k) _ z J (fun _ => J (r ≫ φ)) fun _ => by rw [Category.comp_id]).trans (hb k Z r z _ i hj hi)
    have e' : sval s r z J = (u Z r z (J (r ≫ φ)) i).val * gs r z (M.U i) (a i) := hs Z r z _ i hj hi
    rw [e', gs_comb p _ r z hi]
    simp only [e, mul_left_comm _ (u Z r z (J (r ≫ φ)) i).val, ← Finset.mul_sum]
    exact Units.mul_right_inj _
  constructor
  · intro h i
    refine fn_ext fun y hy => ?_
    choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
    exact (key Y (𝟙 Y) y J i hJ hy).1 (h Y (𝟙 Y) y J hJ)
  · intro h Z r z J hJ
    obtain ⟨i, hi⟩ := exists_chart hM (r z)
    exact (key Z r z J i hJ hi).2 (gs_congr r z (h i))

theorem pw_trans (s : LB.Sec (AbLaw.pw L (n : ℤ))) (r : Z ⟶ X) (z : Z) {j i : L.ι} (hj : r z ∈ L.U j) (hi : r z ∈ L.U i) :
    gs r z (L.U j) (s.f j) = (gm r z (L.U j ⊓ L.U i) (L.g j i) ^ (n : ℤ)).val * gs r z (L.U i) (s.f i) := by
  have hm : r z ∈ L.U j ⊓ L.U i := ⟨hj, hi⟩
  refine (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j i)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))

theorem exists_pw (β : Out.H0 L n) : ∃ b : LB.Sec (AbLaw.pw L (n : ℤ)),
    ∀ (Z : Scheme.{0}) (q : Z ⟶ X) (z : Z) (j : L.ι), q z ∈ L.U j →
      gs q z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) (β.f fun _ => j) = gs q z (L.U j) (b.f j) := by
  have le : ∀ j, L.U j ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := fun j y hy => mem_wc hy
  refine ⟨⟨fun j => resG X (le j) (β.f fun _ => j), fun j i => fn_ext fun y hy => ?_⟩,
    fun Z q z j hj => (gs_res q z (le j) hj _).symm⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.1 _)).trans
    ((sec_trans β (𝟙 X) y (le j hy.1) (le i hy.2)).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm))
  refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.2 _)).symm
  refine Eq.trans ?_ ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (map_zpow _ _ _))).symm
  refine congrArg Units.val ((Fin.prod_univ_one _).trans ?_)
  rw [Category.comp_id]
  rfl

theorem exists_powerSection_of_chartFunctions (a : LB.Sec (AbLaw.pw L (n : ℤ))) : ∃ s : Out.H0 L n,
    ∀ (Z : Scheme.{0}) (q : Z ⟶ X) (z : Z) (j : L.ι), q z ∈ L.U j →
      gs q z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) (s.f fun _ => j) = gs q z (L.U j) (a.f j) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => resG X (le j) (a.f (j 0)), fun j i => fn_ext fun y hy => ?_⟩,
    fun Z q z j hj => gs_res q z (le _) (mem_wc hj) _⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.1 _)).trans
    ((pw_trans a (𝟙 X) y (le j hy.1) (le i hy.2)).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm))
  refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.2 _)).symm
  refine Eq.trans ?_ ((gs_unit (𝟙 X) y _ hy _).trans
    (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j i hy.1 hy.2))).symm
  rw [Fin.prod_univ_one, Category.comp_id]

theorem exists_up (hL : L.IsLB) (hM : M.IsLB) {φ : Y ⟶ X} {w : LB.Iso M (L.pull φ)} (hw : w.IsGen)
    (a : LB.Sec (AbLaw.pw M (n : ℤ))) : ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (n : ℤ))),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι) (i : M.ι), φ (r z) ∈ L.U j → r z ∈ M.U i →
      gs r z (LB.wchart L (fun _ : Fin 1 => φ) (fun _ => j)) (s.f fun _ => j) =
        (gw w r z j i ^ n).val * gs r z (M.U i) (a.f i) := by
  have le : ∀ (i : M.ι) (j : Fin 1 → L.ι), M.U i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j ≤
      (L.pull φ).U (fun _ => j 0) ⊓ M.U i := fun i j y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 0), hy.1⟩
  let u : LB.Iso (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (n : ℤ))) (AbLaw.pw M (n : ℤ)) :=
    ⟨fun p => (res (le p.1 p.2) (w.s (fun _ => p.2 0, p.1)) ^ n)⁻¹⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : M.ι) (j : Fin 1 → L.ι),
      r z ∈ M.U i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j →
      gm r z (M.U i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j) (u.s (i, j)) = (gw w r z (j 0) i ^ n)⁻¹ :=
    fun Z r z i j h => (map_inv _ _).trans (congrArg (·⁻¹) ((map_pow _ _ _).trans
      (congrArg (· ^ n) (gm_res r z (le i j) h _))))
  have hu : u.IsGen := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    refine unit_ext fun y hy => ?_
    refine ((gm_res (𝟙 Y) y _ hy _).trans (hv _ _ y i j hy.1)).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ((gm_div _ _ (𝟙 Y) y (i, j) (i', j') hy).trans
      (congrArg₂ (fun s t => s * t⁻¹) (map_zpow _ (M.g i i') _) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1.2 hy.2.2)))
      ((gm_res (𝟙 Y) y _ hy _).trans (hv _ _ y i' j' hy.2))).trans ?_)
    rw [(isGen_iff w).1 hw Y (𝟙 Y) y (j 0) (j' 0) i i' (Set.mem_iInter.1 hy.1.2 0) (Set.mem_iInter.1 hy.2.2 0)
      hy.1.1 hy.2.1, Fin.prod_univ_one]
    simp only [zpow_natCast, mul_pow, mul_inv, inv_pow, inv_inv]
    exact congrArg (· * _) (mul_comm _ _)
  have hA := DVR.linComb_isLB L hL (fun _ : Fin 1 => φ) (fun _ => (n : ℤ))
  have hB : (AbLaw.pw M (n : ℤ)).IsLB := by
    refine ⟨hM.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ (n : ℤ)) (hM.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ (n : ℤ)) (hM.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  refine ⟨DVR.secOfIso a hu hA hB, fun Z r z j i hj hi => ?_⟩
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => j) ⊓ M.U i := ⟨mem_wc hj, hi⟩
  refine (gs_res r z inf_le_left hm _).symm.trans ((congrArg (gs r z _)
    (DVR.secOfIso_spec a hu hA hB (fun _ => j) i)).trans ((gs_mul r z _ hm _ _).trans
      (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  refine (gs_unit r z _ hm _).trans (congrArg Units.val ((map_inv _ _).trans ?_))
  exact (congrArg (·⁻¹) ((gm_res r z _ hm _).trans (hv Z r z i (fun _ => j) ⟨hi, mem_wc hj⟩))).trans (inv_inv _)

theorem via_val {φ : Y ⟶ X} {w : LB.Iso M (L.pull φ)} {a' : ∀ i, Γ(Y, M.U i)} {a : ∀ j, Γ(X, L.U j)}
    (h : KeyVia.Via w n a' a) (r : Z ⟶ Y) (z : Z) {j : L.ι} {i : M.ι} (hj : φ (r z) ∈ L.U j) (hi : r z ∈ M.U i) :
    gs (r ≫ φ) z (L.U j) (a j) = (gw w r z j i ^ n).val * gs r z (M.U i) (a' i) := by
  have hm : r z ∈ (L.pull φ).U (fun _ => j) ⊓ M.U i := ⟨mem_pull.2 hj, hi⟩
  have le : (L.pull φ).U (fun _ => j) ⊓ M.U i ≤ φ ⁻¹ᵁ L.U j := inf_le_left.trans (KeyVia.chart_le fun _ => j)
  refine (gs_appLE φ _ _ le r z hm _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) i le)).trans
    ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  let v : Γ(Y, (L.pull φ).U (fun _ => j) ⊓ M.U i)ˣ := w.s (fun _ => j, i)
  exact (congrArg (gs r z _) (Units.val_pow_eq_pow_val v n).symm).trans
    ((gs_unit r z _ hm _).trans (congrArg Units.val (map_pow _ _ _)))

end Transfer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem sum_comb {R T : Type} [CommRing R] [CommRing T] (g : R →+* T) {N N' : ℕ} (c : Fin N → R)
    (A : Matrix (Fin N) (Fin N') R) (v : Fin N' → T) :
    ∑ k, g (c k) * ∑ k', g (A k k') * v k' = ∑ k', g (Matrix.vecMul c A k') * v k' := by

  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem coords_comp {R : Type} [CommRing R] (x : KeyIn R) {l N N' : ℕ} {b : Fin N → RR x l} {b₀ : Fin N' → RR x l}
    {A : Matrix (Fin N) (Fin N') R} (hA : ∀ k, Coords x b₀ (A k) (b k).f) {c : Fin N → R}
    {f : ∀ i, Γ(x.P.A.left, x.P.L.U i)} (h : Coords x b c f) : Coords x b₀ (Matrix.vecMul c A) f := by
  intro i
  have e : ∀ k, (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i) = ∑ k', cst x.P.A.hom (x.P.L.U i) (A k k') *
      (show Γ(x.P.A.left, x.P.L.U i) from (b₀ k').f i) := fun k => hA k i
  refine ((h i).trans (Finset.sum_congr rfl fun k _ => congrArg (cst x.P.A.hom (x.P.L.U i) (c k) * ·) (e k))).trans ?_
  exact sum_comb _ c A _

theorem coords_single {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (k : Fin N) :
    Coords x b (Pi.single k 1) (b k).f := by
  intro i
  rw [Finset.sum_eq_single k (fun k' _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, map_one, _root_.one_mul]

theorem exists_good_basis (hS : Out.SecBaseChangeSt) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : KeyIn R) (l : ℕ) (hl : 1 ≤ l) : ∃ b : Fin (l ^ x.P.g) → RR x l, IsBasis x b ∧
      ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : KeyIn R') φ w (b' : Fin (l ^ x.P.g) → RR x' l),
        KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b k)) → IsBasis x' b' := by
  obtain ⟨β, hβ⟩ := exists_universal_basis hS R x.P l hl
  choose b hb using fun k => exists_pw (β k)
  refine ⟨b, fun a => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_powerSection_of_chartFunctions a
    have H := hβ R (𝟙 _) _ (𝟙 _) x.P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) s
    refine (existsUnique_congr fun c => ?_).1 H
    exact transfer x.P.isLB x.P.isLB (𝟙 _) x.P.A.hom β (fun k => (b k).f) a.f
      (fun Z r z j i => gm r z (x.P.L.U j ⊓ x.P.L.U i) (x.P.L.g j i) ^ (l : ℤ))
      (fun k Z r z j i hj hi => by
        rw [Category.comp_id]
        exact (hb k Z r z j hj).trans (pw_trans (b k) r z hj hi)) s
      (fun Z r z j i hj hi => (hs Z r z j hj).trans (pw_trans a r z hj hi)) c
  · rintro R' _ f x' φ w b' ⟨he, hg, F, ⟨hP, -⟩, hw, -⟩ hb' a
    obtain ⟨s, hs⟩ := exists_up x.P.isLB x'.P.isLB hw a
    have H := hβ R' (spMap f) _ φ x'.P.A.hom hP.flip s
    refine (existsUnique_congr fun c => ?_).1 H
    exact transfer x.P.isLB x'.P.isLB φ x'.P.A.hom β (fun k => (b' k).f) a.f
      (fun Z r z j i => gw w r z j i ^ l)
      (fun k Z r z j i hj hi => (hb k Z (r ≫ φ) z j hj).trans (via_val (w := w) (hb' k) r z hj hi)) s hs c

theorem main : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (l : ℕ), 1 ≤ l → (∃ b : Fin (l ^ x.P.g) → RR x l, IsBasis x b) ∧ ∀ b : Fin (l ^ x.P.g) → RR x l, IsBasis x b → ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : KeyIn R') φ w (b' : Fin (l ^ x.P.g) → RR x' l), KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b k)) → IsBasis x' b' := by
  intro hLaws R _ _ _ x l hl
  obtain ⟨b₀, h₀, H₀⟩ := exists_good_basis hLaws.secBaseChange R x l hl
  refine ⟨⟨b₀, h₀⟩, fun b hb R' _ f x' φ w b' hK hb' => ?_⟩
  obtain ⟨hex, -, hco⟩ := (KeyVia.main R R' x x' f).2 φ w hK
  choose b₀' hb₀' _ using fun k => hex l (b₀ k)
  have h₀' := H₀ R' f x' φ w b₀' hK hb₀'
  choose A hA _ using fun k => h₀ (b k)
  choose B hB _ using fun k => hb (b₀ k)
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    ext k k'
    have e := (hb (b k)).unique (coords_comp x (A := Matrix.of B) hB (hA k)) (coords_single x b k)
    refine Eq.trans ?_ ((congrFun e k').trans ?_)
    · rfl
    · rw [Matrix.one_apply, Pi.single_apply]
      simp only [eq_comm]
  have hA' : ∀ k, Coords x' b₀' (((Matrix.of A).map f) k) (b' k).f := fun k =>
    hco l _ b₀ b₀' (b k) (b' k) (A k) hb₀' (hb' k) (hA k)
  have hB' : ∀ k, Coords x' b' (((Matrix.of B).map f) k) (b₀' k).f := fun k =>
    hco l _ b b' (b₀ k) (b₀' k) (B k) hb' (hb₀' k) (hB k)
  have hAB' : (Matrix.of A).map f * (Matrix.of B).map f = 1 := by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero f) (map_one f)]
  intro s
  obtain ⟨c, hc, hu⟩ := h₀' s
  refine ⟨_, coords_comp x' hB' hc, fun d hd => ?_⟩
  rw [← hu _ (coords_comp x' hA' hd), Matrix.vecMul_vecMul, hAB', Matrix.vecMul_one]

end GlobalTheory.KeyBasis

end
