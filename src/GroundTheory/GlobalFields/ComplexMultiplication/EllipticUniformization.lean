module

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section
noncomputable section
namespace GroundTheory.Global
namespace Elliptic

section
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rectIntegral (f : ℂ → E) (z w : ℂ) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

def rectBoundary (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    {w.re} ×ℂ [[z.im, w.im]]

section Edges

variable {z w : ℂ}

lemma bottom_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + z.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]

lemma top_mem_rectBoundary {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + w.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]

lemma right_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]

lemma left_mem_rectBoundary {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (z.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]

lemma rectBoundary_subset : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  intro u hu
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff] at hu ⊢
  rcases hu with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact ⟨h1, h2 ▸ left_mem_uIcc⟩
  · exact ⟨h1, h2 ▸ right_mem_uIcc⟩
  · exact ⟨h1 ▸ left_mem_uIcc, h2⟩
  · exact ⟨h1 ▸ right_mem_uIcc, h2⟩

lemma notMem_rectBoundary_of_mem_Ioo {p : ℂ}
    (hre : p.re ∈ Ioo (min z.re w.re) (max z.re w.re))
    (him : p.im ∈ Ioo (min z.im w.im) (max z.im w.im)) : p ∉ rectBoundary z w := by
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff, not_or, not_and]
  have key : ∀ {a b t : ℝ}, t ∈ Ioo (min a b) (max a b) → t ≠ a ∧ t ≠ b := by
    intro a b t ht
    obtain ⟨h1, h2⟩ := ht
    rw [min_lt_iff] at h1
    rw [lt_max_iff] at h2
    constructor <;> rintro rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
  refine ⟨⟨⟨fun _ h ↦ (key him).1 h, fun _ h ↦ (key him).2 h⟩, fun h _ ↦ (key hre).1 h⟩,
    fun h _ ↦ (key hre).2 h⟩

variable {f g : ℂ → E}

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_bottom (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + z.im * I).continuousOn
    fun _ hx ↦ bottom_mem_rectBoundary hx).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_top (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + w.im * I).continuousOn
    fun _ hx ↦ top_mem_rectBoundary hx).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_right (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (w.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ right_mem_rectBoundary hy).intervalIntegrable

omit [NormedSpace ℂ E] in
lemma intervalIntegrable_left (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (z.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ left_mem_rectBoundary hy).intervalIntegrable

end Edges

section Linearity

variable {z w : ℂ} {f g : ℂ → E}

theorem rectIntegral_add (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u + g u) z w = rectIntegral f z w + rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_add (intervalIntegrable_bottom hf) (intervalIntegrable_bottom hg),
    integral_add (intervalIntegrable_top hf) (intervalIntegrable_top hg),
    integral_add (intervalIntegrable_right hf) (intervalIntegrable_right hg),
    integral_add (intervalIntegrable_left hf) (intervalIntegrable_left hg)]
  simp only [smul_add]
  abel

theorem rectIntegral_smul (c : ℂ) : rectIntegral (fun u ↦ c • f u) z w = c • rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_smul, smul_sub, smul_add]
  rw [smul_comm I c, smul_comm I c]

theorem rectIntegral_const_mul {f : ℂ → ℂ} (c : ℂ) :
    rectIntegral (fun u ↦ c * f u) z w = c * rectIntegral f z w :=
  rectIntegral_smul (f := f) c

theorem rectIntegral_zero : rectIntegral (fun _ ↦ (0 : E)) z w = 0 := by
  simp [rectIntegral]

theorem rectIntegral_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectBoundary z w)) :
    rectIntegral (fun u ↦ ∑ i ∈ s, f i u) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rectIntegral_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectIntegral_add (hf a (Finset.mem_insert_self a s))
      (continuousOn_finsetSum _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

theorem rectIntegral_congr (h : EqOn f g (rectBoundary z w)) :
    rectIntegral f z w = rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_congr (g := fun x : ℝ ↦ g (x + z.im * I))
      fun x hx ↦ h (bottom_mem_rectBoundary hx),
    integral_congr (g := fun x : ℝ ↦ g (x + w.im * I)) fun x hx ↦ h (top_mem_rectBoundary hx),
    integral_congr (g := fun y : ℝ ↦ g (w.re + y * I)) fun y hy ↦ h (right_mem_rectBoundary hy),
    integral_congr (g := fun y : ℝ ↦ g (z.re + y * I)) fun y hy ↦ h (left_mem_rectBoundary hy)]

end Linearity

section Derivative

variable {z w : ℂ}

theorem rectIntegral_eq_zero_of_hasDerivAt [CompleteSpace E] {F f : ℂ → E}
    (hF : ∀ u ∈ rectBoundary z w, HasDerivAt F (f u) u) (hf : ContinuousOn f (rectBoundary z w)) :
    rectIntegral f z w = 0 := by
  have hh : ∀ c : ℝ, ∀ x : ℝ, (x : ℂ) + c * I ∈ rectBoundary z w →
      HasDerivAt (fun x : ℝ ↦ F (x + c * I)) (f (x + c * I)) x := by
    intro c x hx
    have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ) + c * I) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp.add_const ((c : ℂ) * I)
    have h2 := (hF _ hx).scomp x h1
    rw [one_smul] at h2
    exact h2
  have hv : ∀ c : ℝ, ∀ y : ℝ, (c : ℂ) + y * I ∈ rectBoundary z w →
      HasDerivAt (fun y : ℝ ↦ F (c + y * I)) (I • f (c + y * I)) y := by
    intro c y hy
    have h1 : HasDerivAt (fun y : ℝ ↦ (c : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id' y).ofReal_comp.mul_const I).const_add (c : ℂ)
    exact (hF _ hy).scomp y h1
  have hb : ∫ x : ℝ in z.re..w.re, f (x + z.im * I) =
      F (w.re + z.im * I) - F (z.re + z.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (bottom_mem_rectBoundary hx))
      (intervalIntegrable_bottom hf)
  have ht : ∫ x : ℝ in z.re..w.re, f (x + w.im * I) =
      F (w.re + w.im * I) - F (z.re + w.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (top_mem_rectBoundary hx))
      (intervalIntegrable_top hf)
  have hr : I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I) =
      F (w.re + w.im * I) - F (w.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (right_mem_rectBoundary hy))
      ((intervalIntegrable_right hf).smul I)
  have hl : I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I) =
      F (z.re + w.im * I) - F (z.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (left_mem_rectBoundary hy))
      ((intervalIntegrable_left hf).smul I)
  rw [rectIntegral, hb, ht, hr, hl]
  abel

theorem rectIntegral_zpow_sub {p : ℂ} {n : ℤ} (hn : n ≠ -1) (hp : p ∉ rectBoundary z w) :
    rectIntegral (fun u ↦ (u - p) ^ n) z w = 0 := by
  have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hup : ∀ u ∈ rectBoundary z w, u - p ≠ 0 := fun u hu h ↦ hp (sub_eq_zero.1 h ▸ hu)
  refine rectIntegral_eq_zero_of_hasDerivAt (F := fun u ↦ (u - p) ^ (n + 1) / ((n : ℂ) + 1))
    (fun u hu ↦ ?_) ?_
  · have h1 : HasDerivAt (fun u : ℂ ↦ u - p) 1 u := (hasDerivAt_id u).sub_const p
    have h2 := ((hasDerivAt_zpow (n + 1) (u - p) (Or.inl (hup u hu))).comp u h1).div_const
      ((n : ℂ) + 1)
    refine h2.congr_deriv ?_
    rw [add_sub_cancel_right]
    push_cast
    field_simp
  · exact continuousOn_of_forall_continuousAt fun u hu ↦
      ((continuousAt_id.sub continuousAt_const).zpow₀ n (Or.inl (hup u hu)))

end Derivative

section Inverse

def invPrimitive (c x : ℝ) : ℂ :=
  ((Real.log (x ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) - I * ((Real.arctan (x / c) : ℝ) : ℂ)

lemma ofReal_add_mul_I_ne_zero {c : ℝ} (hc : c ≠ 0) (x : ℝ) : (x : ℂ) + c * I ≠ 0 := by
  intro h
  apply hc
  simpa using congrArg Complex.im h

lemma hasDerivAt_invPrimitive {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (invPrimitive c) ((x : ℂ) + c * I)⁻¹ x := by
  have hpos : 0 < x ^ 2 + c ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x ^ 2 + c ^ 2) / 2) (x / (x ^ 2 + c ^ 2)) x := by
    have := (((hasDerivAt_pow 2 x).add_const (c ^ 2)).log hpos.ne').div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 : HasDerivAt (fun x : ℝ ↦ Real.arctan (x / c)) (c / (x ^ 2 + c ^ 2)) x := by
    have := ((hasDerivAt_id' x).div_const c).arctan
    refine this.congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (invPrimitive c)
      (((x / (x ^ 2 + c ^ 2) : ℝ) : ℂ) - I * ((c / (x ^ 2 + c ^ 2) : ℝ) : ℂ)) x :=
    h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)
  refine h3.congr_deriv ?_
  apply Complex.ext
  · rw [Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_re]
    ring
  · rw [Complex.inv_im, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_im]
    ring

theorem integral_inv_ofReal_add_mul_I {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ x : ℝ in a..b, ((x : ℂ) + c * I)⁻¹ = invPrimitive c b - invPrimitive c a := by
  refine integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_invPrimitive hc x) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact (continuous_ofReal.add continuous_const).inv₀ (ofReal_add_mul_I_ne_zero hc)

lemma invPrimitive_rect_sum {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂) (hb₁ : b₁ < 0)
    (hb₂ : 0 < b₂) :
    (invPrimitive b₁ a₂ - invPrimitive b₁ a₁) - (invPrimitive b₂ a₂ - invPrimitive b₂ a₁) +
      (invPrimitive (-a₂) b₂ - invPrimitive (-a₂) b₁) -
      (invPrimitive (-a₁) b₂ - invPrimitive (-a₁) b₁) = 2 * π * I := by
  have hlog : ∀ s t : ℝ, Real.log (s ^ 2 + (-t) ^ 2) = Real.log (t ^ 2 + s ^ 2) := by
    intro s t; congr 1; ring
  have hat : ∀ s t : ℝ, Real.arctan (s / -t) = -Real.arctan (s / t) := by
    intro s t; rw [div_neg, Real.arctan_neg]
  have e1 : Real.arctan (b₂ / a₂) = π / 2 - Real.arctan (a₂ / b₂) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos ha₂ hb₂)]
  have e2 : Real.arctan (b₁ / a₂) = -(π / 2) - Real.arctan (a₂ / b₁) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_pos_of_neg ha₂ hb₁)]
  have e3 : Real.arctan (b₂ / a₁) = -(π / 2) - Real.arctan (a₁ / b₂) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha₁ hb₂)]
  have e4 : Real.arctan (b₁ / a₁) = π / 2 - Real.arctan (a₁ / b₁) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha₁ hb₁)]
  simp only [invPrimitive, hlog, hat, e1, e2, e3, e4]
  push_cast
  ring

theorem rectIntegral_sub_inv {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) : rectIntegral (fun u ↦ (u - p)⁻¹) z w = 2 * π * I := by
  have horiz : ∀ c : ℝ, c - p.im ≠ 0 → ∫ x : ℝ in z.re..w.re, ((x : ℂ) + c * I - p)⁻¹ =
      invPrimitive (c - p.im) (w.re - p.re) - invPrimitive (c - p.im) (z.re - p.re) := by
    intro c hc
    have e : ∀ x : ℝ, ((x : ℂ) + c * I - p) = ((x - p.re : ℝ) : ℂ) + ((c - p.im : ℝ) : ℂ) * I := by
      intro x; apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((c - p.im : ℝ) : ℂ) * I)⁻¹) p.re (a := z.re) (b := w.re)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  have vert : ∀ c : ℝ, -(c - p.re) ≠ 0 → I • ∫ y : ℝ in z.im..w.im, ((c : ℂ) + y * I - p)⁻¹ =
      invPrimitive (-(c - p.re)) (w.im - p.im) - invPrimitive (-(c - p.re)) (z.im - p.im) := by
    intro c hc
    rw [← intervalIntegral.integral_smul]
    have e : ∀ y : ℝ, I • ((c : ℂ) + y * I - p)⁻¹ =
        (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹ := by
      intro y
      have hX : (c : ℂ) + y * I - p = I * (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [smul_eq_mul, hX, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹) p.im (a := z.im) (b := w.im)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  unfold rectIntegral
  beta_reduce
  rw [horiz _ (by linarith), horiz _ (by linarith), vert _ (by linarith), vert _ (by linarith)]
  exact invPrimitive_rect_sum (by linarith) (by linarith) (by linarith) (by linarith)

end Inverse

section Cauchy

theorem rectIntegral_eq_zero_of_differentiable_on_off_countable [CompleteSpace E] (f : ℂ → E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    rectIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd

end Cauchy

section Periodic

theorem rectIntegral_eq_zero_of_periodic {g : ℂ → E} {τ : ℂ} (h1 : ∀ u, g (u + 1) = g u)
    (hτ : ∀ u, g (u + τ) = g u) (a : ℂ) : rectIntegral g a (a + 1 + τ.im * I) = 0 := by
  have hre : (a + 1 + τ.im * I).re = a.re + 1 := by simp
  have him : (a + 1 + τ.im * I).im = a.im + τ.im := by simp
  have hv : ∫ y : ℝ in a.im..a.im + τ.im, g (((a.re + 1 : ℝ) : ℂ) + y * I) =
      ∫ y : ℝ in a.im..a.im + τ.im, g ((a.re : ℂ) + y * I) := by
    congr 1
    ext y
    rw [← h1 ((a.re : ℂ) + y * I)]
    congr 1
    push_cast
    ring
  have hh : ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
      ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + a.im * I) := by
    have e : ∀ x : ℝ, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
        g (((x - τ.re : ℝ) : ℂ) + a.im * I) := by
      intro x
      rw [← hτ (((x - τ.re : ℝ) : ℂ) + a.im * I)]
      congr 1
      apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) τ.re
      (a := a.re) (b := a.re + 1)
    rw [this]
    have hper : Function.Periodic (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) 1 := by
      intro t
      beta_reduce
      rw [← h1 ((t : ℂ) + a.im * I)]
      congr 1
      push_cast
      ring
    rw [show a.re + 1 - τ.re = a.re - τ.re + 1 by ring]
    exact hper.intervalIntegral_add_eq (a.re - τ.re) a.re
  unfold rectIntegral
  rw [hre, him, hv, hh]
  abel

end Periodic
end

section
open Complex Filter Topology Set

def dslopeIter (p : ℂ) (k : ℕ) (g : ℂ → ℂ) : ℂ → ℂ :=
  (Function.swap dslope p)^[k] g

lemma dslopeIter_zero (p : ℂ) (g : ℂ → ℂ) : dslopeIter p 0 g = g := rfl

lemma dslopeIter_succ (p : ℂ) (k : ℕ) (g : ℂ → ℂ) :
    dslopeIter p (k + 1) g = dslopeIter p k (Function.swap dslope p g) :=
  Function.iterate_succ_apply _ _ _

lemma dslopeIter_succ' (p : ℂ) (k : ℕ) (g : ℂ → ℂ) :
    dslopeIter p (k + 1) g = Function.swap dslope p (dslopeIter p k g) :=
  Function.iterate_succ_apply' _ _ _

lemma eq_sum_add_dslopeIter (p : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    g z = ∑ j ∈ Finset.range k, (z - p) ^ j * dslopeIter p j g p +
      (z - p) ^ k * dslopeIter p k g z := by
  induction k with
  | zero => simp [dslopeIter_zero]
  | succ k ih =>
    rw [ih, Finset.sum_range_succ, dslopeIter_succ']
    have h := sub_smul_dslope (dslopeIter p k g) p z
    simp only [smul_eq_mul] at h
    show _ = _ + _ + (z - p) ^ (k + 1) * dslope (dslopeIter p k g) p z
    rw [pow_succ]
    linear_combination -((z - p) ^ k) * h

lemma analyticAt_dslopeIter {p : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p) (k : ℕ) :
    AnalyticAt ℂ (dslopeIter p k g) p := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [dslopeIter_succ']
    obtain ⟨q, hq⟩ := ih
    exact hq.has_fpower_series_dslope_fslope.analyticAt

lemma swap_dslope_sub_mul {p : ℂ} {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g p) :
    Function.swap dslope p (fun z ↦ (z - p) * g z) = g := by
  funext z
  show dslope (fun z ↦ (z - p) * g z) p z = g z
  rcases eq_or_ne z p with rfl | hz
  · rw [dslope_same]
    exact (((hasDerivAt_id z).sub_const z).mul hg.hasDerivAt).deriv.trans (by simp)
  · rw [dslope_of_ne _ hz, slope_def_field]
    have : z - p ≠ 0 := sub_ne_zero.2 hz
    simp only [sub_self, zero_mul, sub_zero]
    field_simp

lemma swap_dslope_const_mul (p a : ℂ) (g : ℂ → ℂ) :
    Function.swap dslope p (fun z ↦ a * g z) = fun z ↦ a * Function.swap dslope p g z := by
  funext z
  show dslope (fun z ↦ a * g z) p z = a * dslope g p z
  rcases eq_or_ne z p with rfl | hz
  · simp only [dslope_same]
    exact deriv_const_mul_field a
  · simp only [dslope_of_ne _ hz, slope_def_field]
    ring

lemma dslopeIter_const_mul (p a : ℂ) (g : ℂ → ℂ) (k : ℕ) :
    dslopeIter p k (fun z ↦ a * g z) = fun z ↦ a * dslopeIter p k g z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_const_mul, dslopeIter_succ']

lemma dslopeIter_congr {p : ℂ} {g₁ g₂ : ℂ → ℂ} (h : g₁ =ᶠ[𝓝 p] g₂) (k : ℕ) :
    dslopeIter p k g₁ =ᶠ[𝓝 p] dslopeIter p k g₂ := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [dslopeIter_succ', dslopeIter_succ']
    have hp : dslopeIter p k g₁ p = dslopeIter p k g₂ p := ih.eq_of_nhds
    filter_upwards [ih] with z hz
    show dslope (dslopeIter p k g₁) p z = dslope (dslopeIter p k g₂) p z
    rcases eq_or_ne z p with rfl | hzp
    · rw [dslope_same, dslope_same, ih.deriv_eq]
    · rw [dslope_of_ne _ hzp, dslope_of_ne _ hzp, slope_def_field, slope_def_field, hz, hp]

open Classical in
def meromorphicShift (f : ℂ → ℂ) (p : ℂ) : ℕ := by
  classical
  exact if h : MeromorphicAt f p then Nat.find h else 0

lemma analyticAt_pow_meromorphicShift_mul {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (fun z ↦ (z - p) ^ meromorphicShift f p * f z) p := by
  classical
  have := Nat.find_spec hf
  simp only [smul_eq_mul] at this
  unfold meromorphicShift
  rw [dite_eq_left hf]
  convert this

lemma meromorphicShift_le {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (h : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p) : meromorphicShift f p ≤ n := by
  classical
  have hf : MeromorphicAt f p := ⟨n, by simpa [smul_eq_mul] using h⟩
  unfold meromorphicShift
  rw [dite_eq_left hf]
  convert Nat.find_min' hf (by simpa [smul_eq_mul] using h)

lemma analyticAt_pow_mul_of_meromorphicShift_le {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    {n : ℕ} (hn : meromorphicShift f p ≤ n) : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p := by
  induction n, hn using Nat.le_induction with
  | base => exact analyticAt_pow_meromorphicShift_mul hf
  | succ n _ ih =>
    have e : (fun z ↦ (z - p) ^ (n + 1) * f z) = fun z ↦ (z - p) * ((z - p) ^ n * f z) := by
      funext z; ring
    rw [e]
    exact (analyticAt_id.sub analyticAt_const).mul ih

def laurentNumerator (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  fun z ↦ (z - p) ^ (meromorphicShift f p + 1) * f z

lemma analyticAt_laurentNumerator {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (laurentNumerator f p) p :=
  analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ _)

def laurentCoeff (f : ℂ → ℂ) (p : ℂ) (j : ℕ) : ℂ :=
  dslopeIter p j (laurentNumerator f p) p

def residue (f : ℂ → ℂ) (p : ℂ) : ℂ :=
  laurentCoeff f p (meromorphicShift f p)

def principalPart (f : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (meromorphicShift f p + 1),
    laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹

def regularPart (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  dslopeIter p (meromorphicShift f p + 1) (laurentNumerator f p)

lemma analyticAt_regularPart {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (regularPart f p) p :=
  analyticAt_dslopeIter (analyticAt_laurentNumerator hf) _

theorem eq_principalPart_add_regularPart (f : ℂ → ℂ) (p : ℂ) {z : ℂ} (hz : z ≠ p) :
    f z = principalPart f p z + regularPart f p z := by
  set n := meromorphicShift f p
  have h := eq_sum_add_dslopeIter p (laurentNumerator f p) (n + 1) z
  have hzp : z - p ≠ 0 := sub_ne_zero.2 hz
  have hpow : (z - p) ^ (n + 1) ≠ 0 := pow_ne_zero _ hzp
  apply mul_left_cancel₀ hpow
  have e1 : (z - p) ^ (n + 1) * f z = laurentNumerator f p z := rfl
  rw [e1, h, mul_add, principalPart, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n + 1 := by simp only [Finset.mem_range] at hj; omega
  have e2 : (z - p) ^ (n + 1) = (z - p) ^ (n + 1 - j) * (z - p) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  have hpj : (z - p) ^ (n + 1 - j) ≠ 0 := pow_ne_zero _ hzp
  rw [laurentCoeff, e2]
  field_simp
  rfl

theorem residue_eq_dslopeIter {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hn : AnalyticAt ℂ (fun z ↦ (z - p) ^ (n + 1) * f z) p) :
    residue f p = dslopeIter p n (fun z ↦ (z - p) ^ (n + 1) * f z) p := by
  have hf : MeromorphicAt f p := ⟨n + 1, by simpa [smul_eq_mul] using hn⟩
  set m := meromorphicShift f p with hm
  have step : ∀ j, m ≤ j + 1 →
      dslopeIter p (j + 1) (fun z ↦ (z - p) ^ (j + 1 + 1) * f z) p =
        dslopeIter p j (fun z ↦ (z - p) ^ (j + 1) * f z) p := by
    intro j hj
    have hd : DifferentiableAt ℂ (fun z ↦ (z - p) ^ (j + 1) * f z) p :=
      (analyticAt_pow_mul_of_meromorphicShift_le hf hj).differentiableAt
    rw [dslopeIter_succ]
    have e : (fun z ↦ (z - p) ^ (j + 1 + 1) * f z) =
        fun z ↦ (z - p) * ((z - p) ^ (j + 1) * f z) := by
      funext z; ring
    rw [e, swap_dslope_sub_mul hd]
  have up : ∀ j, m ≤ j →
      dslopeIter p j (fun z ↦ (z - p) ^ (j + 1) * f z) p = residue f p := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [step j (by omega), ih]
  have hmn : m ≤ n + 1 := meromorphicShift_le hn
  rcases Nat.lt_or_ge n m with h | h
  · rw [← step n (by omega), up (n + 1) (by omega)]
  · exact (up n h).symm

theorem residue_congr {f₁ f₂ : ℂ → ℂ} {p : ℂ} (hf₁ : MeromorphicAt f₁ p)
    (h : f₁ =ᶠ[𝓝[≠] p] f₂) : residue f₁ p = residue f₂ p := by
  set n := meromorphicShift f₁ p + 1
  have h₁ : AnalyticAt ℂ (fun z ↦ (z - p) ^ (n + 1) * f₁ z) p :=
    analyticAt_pow_mul_of_meromorphicShift_le hf₁ (by omega)
  have heq : (fun z ↦ (z - p) ^ (n + 1) * f₁ z) =ᶠ[𝓝 p] fun z ↦ (z - p) ^ (n + 1) * f₂ z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz
    rcases eq_or_ne z p with rfl | hzp
    · simp
    · rw [hz hzp]
  rw [residue_eq_dslopeIter h₁, residue_eq_dslopeIter (h₁.congr heq)]
  exact (dslopeIter_congr heq n).eq_of_nhds

theorem residue_eq_of_eventuallyEq {f u : ℂ → ℂ} {p c : ℂ} (hu : AnalyticAt ℂ u p)
    (h : f =ᶠ[𝓝[≠] p] fun z ↦ c * (z - p)⁻¹ + u z) : residue f p = c := by
  have hG : AnalyticAt ℂ (fun z ↦ c * (z - p) + (z - p) ^ 2 * u z) p := by fun_prop
  have heq : (fun z ↦ (z - p) ^ (1 + 1) * f z) =ᶠ[𝓝 p]
      fun z ↦ c * (z - p) + (z - p) ^ 2 * u z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz
    rcases eq_or_ne z p with rfl | hzp
    · simp
    · rw [hz hzp]
      have : z - p ≠ 0 := sub_ne_zero.2 hzp
      field_simp
  rw [residue_eq_dslopeIter (n := 1) (hG.congr heq.symm), dslopeIter_succ, dslopeIter_zero]
  show dslope _ p p = c
  rw [dslope_same, heq.deriv_eq]
  have hd := (((hasDerivAt_id p).sub_const p).const_mul c).add
    ((((hasDerivAt_id p).sub_const p).pow 2).mul hu.differentiableAt.hasDerivAt)
  exact hd.deriv.trans (by simp)

theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 :=
  residue_eq_of_eventuallyEq hf (Eventually.of_forall fun z ↦ by simp)

lemma swap_dslope_comp_mul {G : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0)
    (hG : DifferentiableAt ℂ G (c * w₀)) :
    Function.swap dslope w₀ (fun w ↦ G (c * w)) =
      fun w ↦ c * Function.swap dslope (c * w₀) G (c * w) := by
  funext w
  show dslope (fun w ↦ G (c * w)) w₀ w = c * dslope G (c * w₀) (c * w)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    have := hG.hasDerivAt.comp w ((hasDerivAt_id w).const_mul c)
    exact this.deriv.trans (by ring)
  · have hcw : c * w ≠ c * w₀ := fun h ↦ hw (mul_left_cancel₀ hc h)
    have h1 : w - w₀ ≠ 0 := sub_ne_zero.2 hw
    have h2 : c * w - c * w₀ ≠ 0 := sub_ne_zero.2 hcw
    rw [dslope_of_ne _ hw, dslope_of_ne _ hcw, slope_def_field, slope_def_field]
    rw [show c * w - c * w₀ = c * (w - w₀) by ring]
    field_simp

lemma dslopeIter_comp_mul {G : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hG : AnalyticAt ℂ G (c * w₀))
    (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (c * w)) = fun w ↦ c ^ k * dslopeIter (c * w₀) k G (c * w) := by
  induction k with
  | zero => funext w; simp [dslopeIter_zero]
  | succ k ih =>
    rw [dslopeIter_succ', ih]
    rw [swap_dslope_const_mul w₀ (c ^ k) (fun w ↦ dslopeIter (c * w₀) k G (c * w))]
    rw [swap_dslope_comp_mul hc ((analyticAt_dslopeIter hG k).differentiableAt)]
    funext w
    rw [dslopeIter_succ']
    ring

theorem residue_comp_mul {f : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hf : MeromorphicAt f (c * w₀)) :
    residue (fun w ↦ f (c * w)) w₀ = c⁻¹ * residue f (c * w₀) := by
  set n := meromorphicShift f (c * w₀)
  set G : ℂ → ℂ := fun z ↦ (z - c * w₀) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (c * w₀) := analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (c * w)) = fun w ↦ c⁻¹ ^ (n + 1) * G (c * w) := by
    funext w
    simp only [hGdef]
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  have hcomp : AnalyticAt ℂ (fun w ↦ G (c * w)) w₀ := by
    have : AnalyticAt ℂ (fun w ↦ c * w) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (c * w)) w₀ := by
    rw [e]
    exact analyticAt_const.mul hcomp
  rw [residue_eq_dslopeIter hana, e, dslopeIter_const_mul, dslopeIter_comp_mul hc hG]
  have : residue f (c * w₀) = dslopeIter (c * w₀) n G (c * w₀) := rfl
  rw [this, inv_pow, pow_succ]
  field_simp

theorem residue_logDeriv {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) {n : ℤ}
    (hn : meromorphicOrderAt f p = n) : residue (logDeriv f) p = n := by
  obtain ⟨g, hg, hgp, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  simp only [smul_eq_mul] at hfg
  have hu : AnalyticAt ℂ (fun z ↦ deriv g z / g z) p := hg.deriv.div hg hgp
  apply residue_eq_of_eventuallyEq hu
  have h2 : ∀ᶠ z in 𝓝[≠] p, f =ᶠ[𝓝 z] fun w ↦ (w - p) ^ n * g w := by
    have := eventually_eventually_nhdsWithin.2 hfg
    filter_upwards [this, self_mem_nhdsWithin] with z hz hzp
    rwa [nhdsWithin_eq_nhds.2 (isOpen_compl_singleton.mem_nhds hzp)] at hz
  have h3 : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgp)
  have h4 : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z := nhdsWithin_le_nhds hg.eventually_analyticAt
  filter_upwards [h2, h3, h4, self_mem_nhdsWithin] with z hz hgz hga hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  have h1 : HasDerivAt (fun w ↦ (w - p) ^ n) ((n : ℂ) * (z - p) ^ (n - 1) * 1) z := by
    have := (hasDerivAt_zpow n (z - p) (Or.inl hzp')).comp z ((hasDerivAt_id z).sub_const p)
    exact this
  have hd : HasDerivAt (fun w ↦ (w - p) ^ n * g w)
      ((n : ℂ) * (z - p) ^ (n - 1) * 1 * g z + (z - p) ^ n * deriv g z) z :=
    h1.mul hga.differentiableAt.hasDerivAt
  rw [logDeriv_apply, hz.deriv_eq, hz.eq_of_nhds, hd.deriv, zpow_sub_one₀ hzp']
  have hzn : (z - p) ^ n ≠ 0 := zpow_ne_zero n hzp'
  field_simp

theorem residue_ne_zero_of_meromorphicOrderAt_eq_neg_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (h : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) :
    residue f p ≠ 0 := by
  obtain ⟨g, hg, hgp, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
  simp only [smul_eq_mul] at hfg
  obtain ⟨q, hq⟩ := hg
  have hu : AnalyticAt ℂ (dslope g p) p := hq.has_fpower_series_dslope_fslope.analyticAt
  rw [residue_eq_of_eventuallyEq (c := g p) hu ?_]
  · exact hgp
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  have e := sub_smul_dslope g p z
  simp only [smul_eq_mul] at e
  rw [hz, zpow_neg_one]
  field_simp
  linear_combination -e
end

section
open Complex Filter Topology Set
open scoped Interval Real

lemma swap_dslope_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) :
    Function.swap dslope w₀ (fun w ↦ G (w + a)) =
      fun w ↦ Function.swap dslope (w₀ + a) G (w + a) := by
  funext w
  show dslope (fun w ↦ G (w + a)) w₀ w = dslope G (w₀ + a) (w + a)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    exact deriv_comp_add_const _ _ _
  · have hw' : w + a ≠ w₀ + a := fun h ↦ hw (add_right_cancel h)
    rw [dslope_of_ne _ hw, dslope_of_ne _ hw', slope_def_field, slope_def_field]
    congr 1
    ring

lemma dslopeIter_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (w + a)) = fun w ↦ dslopeIter (w₀ + a) k G (w + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_comp_add]
    funext w
    rw [dslopeIter_succ']

theorem residue_comp_add {f : ℂ → ℂ} {a w₀ : ℂ} (hf : MeromorphicAt f (w₀ + a)) :
    residue (fun w ↦ f (w + a)) w₀ = residue f (w₀ + a) := by
  set n := meromorphicShift f (w₀ + a)
  set G : ℂ → ℂ := fun z ↦ (z - (w₀ + a)) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (w₀ + a) :=
    analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) = fun w ↦ G (w + a) := by
    funext w
    simp only [hGdef]
    congr 2
    ring
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) w₀ := by
    rw [e]
    have : AnalyticAt ℂ (fun w ↦ w + a) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  rw [residue_eq_dslopeIter hana, e, dslopeIter_comp_add]
  rfl

theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (h : 0 ≤ meromorphicOrderAt f p) : residue f p = 0 := by
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    rw [residue_congr hf htop]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by rw [← hn] at h; exact_mod_cast h
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    simp only [smul_eq_mul] at hfg
    lift n to ℕ using hn0
    rw [residue_congr hf hfg]
    apply residue_eq_zero_of_analyticAt
    simp only [zpow_natCast]
    fun_prop

lemma analyticAt_principalPart (f : ℂ → ℂ) {p u : ℂ} (hu : u ≠ p) :
    AnalyticAt ℂ (principalPart f p) u := by
  have h : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ((z - p) ^ k)⁻¹) u := fun k ↦
    ((analyticAt_id.sub analyticAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hu))
  have : principalPart f p = fun z ↦ ∑ j ∈ Finset.range (meromorphicShift f p + 1),
      laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹ := rfl
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun j _ ↦ analyticAt_const.mul (h _)

theorem rectIntegral_principalPart (f : ℂ → ℂ) {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectIntegral (principalPart f p) z w = 2 * π * I * residue f p := by
  have hp : p ∉ rectBoundary z w := notMem_rectBoundary_of_mem_Ioo
    ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
    ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hne : ∀ u ∈ rectBoundary z w, u ≠ p := fun u hu h ↦ hp (h ▸ hu)
  have hc : ∀ k : ℕ, ContinuousOn (fun u ↦ ((u - p) ^ k)⁻¹) (rectBoundary z w) := fun k u hu ↦
    ((((continuous_id.sub continuous_const).pow k).continuousAt).inv₀
      (pow_ne_zero _ (sub_ne_zero.2 (hne u hu)))).continuousWithinAt
  set n := meromorphicShift f p
  have e : principalPart f p = fun u ↦ ∑ j ∈ Finset.range (n + 1),
      laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹ := rfl
  rw [e, rectIntegral_finset_sum (Finset.range (n + 1))
    (f := fun j u ↦ laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹)
    (fun j _ ↦ continuousOn_const.mul (hc _))]
  simp_rw [rectIntegral_const_mul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [Nat.add_sub_cancel_left]
    simp_rw [pow_one]
    rw [rectIntegral_sub_inv h1 h2 h3 h4]
    exact mul_comm _ _
  · intro j hj
    have hj' : j < n := Finset.mem_range.1 hj
    have e2 : (fun u ↦ ((u - p) ^ (n + 1 - j))⁻¹) = fun u ↦ (u - p) ^ (-((n + 1 - j : ℕ) : ℤ)) := by
      funext u
      rw [zpow_neg, zpow_natCast]
    rw [e2, rectIntegral_zpow_sub _ hp, mul_zero]
    omega

theorem rectIntegral_eq_sum_residue {f : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ)
    (hS : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    (hmero : ∀ p ∈ S, MeromorphicAt f p)
    (hana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ S → AnalyticAt ℂ f u) :
    rectIntegral f z w = 2 * π * I * ∑ p ∈ S, residue f p := by
  classical
  set F : ℂ → ℂ := fun u ↦ f u - ∑ q ∈ S, principalPart f q u with hF
  set E : ℂ → ℂ → ℂ := fun p u ↦ regularPart f p u - ∑ q ∈ S.erase p, principalPart f q u
    with hE
  set G : ℂ → ℂ := fun u ↦ if u ∈ S then E u u else F u with hG
  have hFE : ∀ p ∈ S, ∀ u, u ≠ p → F u = E p u := by
    intro p hp u hu
    simp only [hF, hE]
    rw [eq_principalPart_add_regularPart f p hu, ← Finset.add_sum_erase S _ hp]
    ring
  have hEana : ∀ p ∈ S, AnalyticAt ℂ (E p) p := by
    intro p hp
    exact (analyticAt_regularPart (hmero p hp)).sub
      (Finset.analyticAt_fun_sum _ fun q hq ↦
        analyticAt_principalPart f (Finset.ne_of_mem_erase hq).symm)
  have hGana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ G u := by
    intro u hu
    by_cases huS : u ∈ S
    · have hnhds : ((S.erase u : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 u :=
        (S.erase u).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine (hEana u huS).congr ?_
      filter_upwards [hnhds] with v hv
      simp only [hG]
      rcases eq_or_ne v u with rfl | hvu
      · simp [huS]
      · have hvS : v ∉ S := fun h ↦ hv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu, h⟩))
        rw [ite_eq_right hvS, hFE u huS v hvu]
    · have hnhds : ((S : Set ℂ))ᶜ ∈ 𝓝 u :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using huS)
      have hFana : AnalyticAt ℂ F u :=
        (hana u hu huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
          analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))
      refine hFana.congr ?_
      filter_upwards [hnhds] with v hv
      have hvS : v ∉ S := by simpa using hv
      simp only [hG, ite_eq_right hvS]
  have hSb : ∀ p ∈ S, p ∉ rectBoundary z w := fun p hp ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hS p hp
    exact notMem_rectBoundary_of_mem_Ioo
      ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
      ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hbK : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := rectBoundary_subset
  have hG0 : rectIntegral G z w = 0 := by
    apply rectIntegral_eq_zero_of_differentiable_on_off_countable G z w ∅ countable_empty
    · exact fun u hu ↦ (hGana u hu).continuousAt.continuousWithinAt
    · intro u hu
      apply (hGana u _).differentiableAt
      have h' := hu.1
      rw [mem_reProdIm] at h' ⊢
      exact ⟨Ioo_subset_Icc_self h'.1, Ioo_subset_Icc_self h'.2⟩
  have hGF : rectIntegral G z w = rectIntegral F z w := by
    apply rectIntegral_congr
    intro u hu
    have huS : u ∉ S := fun h ↦ hSb u h hu
    simp only [hG, ite_eq_right huS]
  have hPc : ∀ q ∈ S, ContinuousOn (principalPart f q) (rectBoundary z w) := fun q hq u hu ↦
    (analyticAt_principalPart f (fun (h : u = q) ↦ hSb q hq (h ▸ hu))).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (rectBoundary z w) := fun u hu ↦ by
    have huS : u ∉ S := fun h ↦ hSb u h hu
    exact ((hana u (hbK hu) huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
      analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))).continuousAt.continuousWithinAt
  have hsplit : rectIntegral f z w =
      rectIntegral F z w + ∑ q ∈ S, rectIntegral (principalPart f q) z w := by
    rw [← rectIntegral_finset_sum S hPc, ← rectIntegral_add hFc (continuousOn_finsetSum S hPc)]
    congr 1
    funext u
    rw [hF]
    ring
  rw [hsplit, ← hGF, hG0, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hS q hq
  exact rectIntegral_principalPart f h1 h2 h3 h4
end

section
open Complex Filter Topology Set

variable (L : PeriodPair)

abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup

abbrev Torus.mk (z : ℂ) : Torus L := QuotientAddGroup.mk z

lemma Torus.mk_eq_mk_iff {z w : ℂ} : Torus.mk L z = Torus.mk L w ↔ z - w ∈ L.lattice := by
  rw [Torus.mk, Torus.mk, QuotientAddGroup.eq_iff_sub_mem]
  rfl

lemma Torus.mk_surjective : Function.Surjective (Torus.mk L) :=
  QuotientAddGroup.mk_surjective

def IsPeriodic {E : Type*} (f : ℂ → E) : Prop :=
  ∀ z : ℂ, ∀ l ∈ L.lattice, f (z + l) = f z

def IsEllipticFunction (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ IsPeriodic L f

variable {L}

lemma IsPeriodic.sub {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : f (z - l) = f z := by
  simpa using (hf (z - l) l hl).symm

lemma IsPeriodic.comp_add {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ}
    (hl : l ∈ L.lattice) : (fun z ↦ f (z + l)) = f :=
  funext fun z ↦ hf z l hl

lemma IsPeriodic.eq_of_mk_eq {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {z w : ℂ}
    (h : Torus.mk L z = Torus.mk L w) : f z = f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  simpa using hf w (z - w) hzw

variable (L)

def fundamentalCompact : Set ℂ := closure (ZSpan.fundamentalDomain L.basis)

lemma isCompact_fundamentalCompact : IsCompact (fundamentalCompact L) :=
  (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure

lemma exists_sub_mem_fundamentalCompact (z : ℂ) :
    ∃ l ∈ L.lattice, z - l ∈ fundamentalCompact L := by
  refine ⟨ZSpan.floor L.basis z, ?_, subset_closure ?_⟩
  · rw [L.lattice_eq_span_range_basis]
    exact (ZSpan.floor L.basis z).2
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _

theorem isCompact_range_of_isPeriodic {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hc : Continuous f) (hf : IsPeriodic L f) : IsCompact (range f) :=
  IsZLattice.isCompact_range_of_periodic L.lattice f hc fun z w hw ↦ hf z w hw

theorem eq_of_differentiable_of_isPeriodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hd : Differentiable ℂ f) (hf : IsPeriodic L f) (z w : ℂ) : f z = f w :=
  hd.apply_eq_apply_of_bounded (isCompact_range_of_isPeriodic L hd.continuous hf).isBounded z w

variable {L}

lemma IsPeriodic.analyticAt_add_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    AnalyticAt ℂ f (z + l) ↔ AnalyticAt ℂ f z := by
  constructor
  · intro h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w + l) z := AnalyticAt.comp (g := f) h (by fun_prop)
    rwa [Function.comp_def, hf.comp_add hl] at this
  · intro h
    have h' : AnalyticAt ℂ f ((z + l) - l) := by simpa using h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w - l) (z + l) := AnalyticAt.comp (g := f) h' (by fun_prop)
    have e : (fun w ↦ f (w - l)) = f := funext fun w ↦ hf.sub w hl
    rwa [Function.comp_def, e] at this

lemma IsPeriodic.meromorphicOrderAt_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    meromorphicOrderAt f (z + l) = meromorphicOrderAt f z := by
  have := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := f) (x := z) (c := l)
  rw [hf.comp_add hl] at this
  exact this.symm

def singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Set ℂ :=
  {z | ¬ AnalyticAt ℂ f z}

theorem finite_inter_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ singularSet f).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin)
  exact h.subset fun z hz ↦ ⟨hz.1, hz.2⟩

variable (L)

theorem finite_image_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) (hp : IsPeriodic L f) :
    (Torus.mk L '' singularSet f).Finite := by
  refine ((finite_inter_singularSet hf (isCompact_fundamentalCompact L)).image
    (Torus.mk L)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨l, hl, hzl⟩ := exists_sub_mem_fundamentalCompact L z
  refine ⟨z - l, ⟨hzl, fun h ↦ hz ?_⟩, ?_⟩
  · have := (hp.analyticAt_add_iff hl (z - l)).2 h
    simpa using this
  · exact (Torus.mk_eq_mk_iff L).2 (by simpa using L.lattice.neg_mem hl)
end

section
open Complex Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E]

def limPunctured (f : ℂ → E) (z : ℂ) : E := limUnder (𝓝[≠] z) f

lemma limPunctured_eq_of_continuousAt {f : ℂ → E} {z : ℂ} (h : ContinuousAt f z) :
    limPunctured f z = f z :=
  (tendsto_nhdsWithin_of_tendsto_nhds h.tendsto).limUnder_eq

lemma tendsto_limPunctured [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) :
    Tendsto f (𝓝[≠] z) (𝓝 (limPunctured f z)) := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  rwa [limPunctured, hc.limUnder_eq]

lemma limPunctured_eventuallyEq_of_analyticAt [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {w : ℂ} (hw : AnalyticAt ℂ f w) :
    limPunctured f =ᶠ[𝓝 w] f := by
  filter_upwards [(isOpen_analyticAt ℂ f).mem_nhds hw] with u hu
  exact limPunctured_eq_of_continuousAt hu.continuousAt

variable [NormedSpace ℂ E]

lemma analyticAt_limPunctured [CompleteSpace E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) : AnalyticAt ℂ (limPunctured f) z := by
  have hev : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := hf.eventually_analyticAt
  have heq : limPunctured f =ᶠ[𝓝[≠] z] f :=
    hev.mono fun w hw ↦ (limPunctured_eventuallyEq_of_analyticAt hw).eq_of_nhds
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · exact hev.mono fun w hw ↦
      hw.differentiableAt.congr_of_eventuallyEq (limPunctured_eventuallyEq_of_analyticAt hw)
  · rw [← continuousWithinAt_compl_self]
    exact (tendsto_limPunctured hf ho).congr' heq.symm

variable {L : PeriodPair}

lemma IsPeriodic.limPunctured_add {f : ℂ → E} (hp : IsPeriodic L f) {z l : ℂ}
    (hl : l ∈ L.lattice) (hf : MeromorphicAt f z) (ho : 0 ≤ meromorphicOrderAt f z) :
    limPunctured f (z + l) = limPunctured f z := by
  have h1 : Tendsto (fun w ↦ w - l) (𝓝[≠] (z + l)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun w ↦ w - l) (𝓝 (z + l)) (𝓝 (z + l - l)) :=
        (continuous_id.sub continuous_const).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      simp only [mem_singleton_iff] at h ⊢
      rw [← h]; ring
  have h2 := (tendsto_limPunctured hf ho).comp h1
  have e : (f ∘ fun w ↦ w - l) = f := funext fun w ↦ hp.sub w hl
  rw [e] at h2
  exact h2.limUnder_eq

variable (L) in
theorem exists_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, ∀ z, AnalyticAt ℂ f z → f z = c := by
  have hd : Differentiable ℂ (limPunctured f) := fun z ↦
    (analyticAt_limPunctured (hf z) (ho z)).differentiableAt
  have hFp : IsPeriodic L (limPunctured f) := fun z l hl ↦
    hp.limPunctured_add hl (hf z) (ho z)
  refine ⟨limPunctured f 0, fun z hz ↦ ?_⟩
  rw [← limPunctured_eq_of_continuousAt hz.continuousAt]
  exact eq_of_differentiable_of_isPeriodic L hd hFp z 0

variable (L) in
theorem exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  obtain ⟨c, hc⟩ := exists_const_of_meromorphicOrderAt_nonneg L hf hp ho
  refine ⟨c, ?_⟩
  filter_upwards [(hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin] with z hz
  exact hc z hz
end

section
open Complex Filter Topology Set Polynomial
open scoped PeriodPair

variable {L : PeriodPair}

lemma meromorphicAt_eval {g : ℂ → ℂ} {x : ℂ} (hg : MeromorphicAt g x) (P : ℂ[X]) :
    MeromorphicAt (fun z ↦ P.eval (g z)) x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add]; fun_prop
  | monomial n a => simp only [eval_monomial]; fun_prop

lemma analyticAt_eval {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (P : ℂ[X]) :
    AnalyticAt ℂ (fun z ↦ P.eval (g z)) x := by
  simpa using hg.aeval_polynomial P

lemma isPeriodic_weierstrassP : IsPeriodic L ℘[L] := fun z l hl ↦
  L.weierstrassP_add_coe z ⟨l, hl⟩

lemma isPeriodic_derivWeierstrassP : IsPeriodic L ℘'[L] := fun z l hl ↦
  L.derivWeierstrassP_add_coe z ⟨l, hl⟩

lemma isEllipticFunction_weierstrassP : IsEllipticFunction L ℘[L] :=
  ⟨L.meromorphic_weierstrassP, isPeriodic_weierstrassP⟩

lemma weierstrassP_eq_zpow_mul {z : ℂ} (hz : z ≠ 0) :
    ℘[L] z = z ^ (-2 : ℤ) * (z ^ 2 * L.weierstrassPExcept 0 z + 1) := by
  have h := L.ite_eq_one_sub_sq_mul_weierstrassP 0 L.lattice.zero_mem z
  rw [ite_eq_right hz] at h
  have h' : z ^ 2 * ℘[L] z = z ^ 2 * L.weierstrassPExcept 0 z + 1 := by
    simpa using h
  have h2 : z ^ (-2 : ℤ) * z ^ 2 = 1 := by
    rw [zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero 2 hz)]
  rw [← h', ← mul_assoc, h2, one_mul]

lemma analyticAt_weierstrassP_laurent :
    AnalyticAt ℂ (fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1) 0 := by
  have := L.analyticAt_weierstrassPExcept 0
  fun_prop

lemma lt_meromorphicOrderAt_of_eventuallyEq {f w : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hw : AnalyticAt ℂ w x) (hw0 : w x = 0)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n * w z) :
    (n : WithTop ℤ) < meromorphicOrderAt f x := by
  have e : (fun z ↦ (z - x) ^ n * w z) = (fun z ↦ z - x) ^ n * w := rfl
  have hm : MeromorphicAt ((fun z ↦ z - x) ^ n) x :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt (x := x)).zpow n
  rw [meromorphicOrderAt_congr h, e, meromorphicOrderAt_mul hm hw.meromorphicAt,
    meromorphicOrderAt_zpow_id_sub_const]
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt w x := by
    rw [hw.meromorphicOrderAt_eq]
    have h1 : analyticOrderAt w x ≠ 0 := by
      rw [Ne, hw.analyticOrderAt_eq_zero]
      simpa using hw0
    cases h : analyticOrderAt w x with
    | top => simp
    | coe m =>
      rw [h] at h1
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by exact_mod_cast h1)
      simp only [ENat.map_natCast]
      exact_mod_cast this
  cases ho : meromorphicOrderAt w x with
  | top => simp
  | coe m =>
    rw [ho] at hpos
    have : (1 : ℤ) ≤ m := by exact_mod_cast hpos
    exact_mod_cast (by omega : n < n + m)

private lemma coe_add_one_le_of_lt {o : ℤ} {x : WithTop ℤ} (h : (o : WithTop ℤ) < x) :
    ((o + 1 : ℤ) : WithTop ℤ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe m =>
    have : o < m := by exact_mod_cast h
    exact_mod_cast (by omega : o + 1 ≤ m)

lemma even_of_meromorphicOrderAt_eq {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (he : ∀ z, f (-z) = f z) {n : ℤ} (hn : meromorphicOrderAt f 0 = n) : Even n := by
  obtain ⟨u, hu, hu0, e⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  have hneg : Tendsto (fun z : ℂ ↦ -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_neg.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have e' := hneg.eventually e
  have key : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (-1 : ℂ) ^ n * u (-z) = u z := by
    filter_upwards [e, e', self_mem_nhdsWithin] with z h1 h2 hz
    have hz' : z ≠ 0 := hz
    rw [he z, h1] at h2
    simp only [sub_zero, smul_eq_mul] at h2
    have h3 : z ^ n * u z = z ^ n * ((-1 : ℂ) ^ n * u (-z)) := by
      rw [h2, show -z = (-1 : ℂ) * z by ring, mul_zpow]
      ring
    exact (mul_left_cancel₀ (zpow_ne_zero n hz') h3).symm
  have hc : ContinuousAt (fun z ↦ (-1 : ℂ) ^ n * u (-z)) 0 := by
    have : ContinuousAt u (-0) := by simpa using hu.continuousAt
    exact continuousAt_const.mul (this.comp continuous_neg.continuousAt)
  have t1 : Tendsto u (𝓝[≠] 0) (𝓝 (u 0)) := hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 := (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' key
  have heq : (-1 : ℂ) ^ n * u (-0) = u 0 := tendsto_nhds_unique t2 t1
  rw [neg_zero] at heq
  rcases Int.even_or_odd n with h | h
  · exact h
  · exfalso
    rw [h.neg_one_zpow] at heq
    apply hu0
    linear_combination -heq / 2

lemma exists_eventuallyEq_const_of_analyticAt_off_lattice {g : ℂ → ℂ} (hg : Meromorphic g)
    (hp : IsPeriodic L g) (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (h0 : 0 ≤ meromorphicOrderAt g 0) : ∃ c : ℂ, g =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  refine exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg (L := L) hg hp fun z ↦ ?_
  by_cases hz : z ∈ L.lattice
  · have := hp.meromorphicOrderAt_add hz 0
    rw [zero_add] at this
    rwa [this]
  · exact (han z hz).meromorphicOrderAt_nonneg

theorem exists_polynomial_of_even_of_analyticAt_off_lattice (n : ℕ) {g : ℂ → ℂ}
    (hg : Meromorphic g) (hp : IsPeriodic L g) (he : ∀ z, g (-z) = g z)
    (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (hn : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g 0) :
    ∃ P : ℂ[X], g =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) := by
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  by_cases h0 : 0 ≤ meromorphicOrderAt g 0
  · obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_analyticAt_off_lattice hg hp han h0
    exact ⟨C c, by simpa using hc⟩
  push Not at h0
  obtain ⟨o, ho⟩ : ∃ o : ℤ, meromorphicOrderAt g 0 = o := by
    cases h : meromorphicOrderAt g 0 with
    | top => rw [h] at h0; exact absurd h0 (not_lt.2 le_top)
    | coe o => exact ⟨o, rfl⟩
  rw [ho] at h0 hn
  have ho0 : o < 0 := by exact_mod_cast h0
  have hno : -(n : ℤ) ≤ o := by exact_mod_cast hn
  obtain ⟨r, hr⟩ := even_of_meromorphicOrderAt_eq (hg 0) he ho
  obtain ⟨k, hk⟩ : ∃ k : ℕ, o = -2 * k := ⟨(-r).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨u, hu, hu0, hgu⟩ := (meromorphicOrderAt_eq_int_iff (hg 0)).1 ho
  have hv := analyticAt_weierstrassP_laurent (L := L)
  have hdiff : (fun z ↦ g z - u 0 * ℘[L] z ^ k) =ᶠ[𝓝[≠] 0] fun z ↦ (z - 0) ^ o *
      (u z - u 0 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) ^ k) := by
    filter_upwards [hgu, self_mem_nhdsWithin] with z h1 h2
    have h2' : z ≠ 0 := h2
    rw [h1, weierstrassP_eq_zpow_mul h2', mul_pow, ← zpow_natCast (z ^ (-2 : ℤ)), ← zpow_mul,
      hk, sub_zero, smul_eq_mul]
    ring
  have hlt := lt_meromorphicOrderAt_of_eventuallyEq
    (hu.sub (analyticAt_const.mul (hv.pow k))) (by simp) hdiff
  obtain ⟨P, hP⟩ := ih (2 * k - 1) (by omega) (g := fun z ↦ g z - u 0 * ℘[L] z ^ k)
    (fun z ↦ by have := hg z; have := L.meromorphic_weierstrassP z; fun_prop)
    (fun z l hl ↦ by simp only [hp z l hl, isPeriodic_weierstrassP z l hl])
    (fun z ↦ by simp only [he, L.weierstrassP_neg])
    (fun z hz ↦ by
      have := han z hz
      have := L.analyticOnNhd_weierstrassP z hz
      fun_prop)
    (by
      have e : ((-((2 * k - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) = ((o + 1 : ℤ) : WithTop ℤ) := by
        congr 1; omega
      rw [e]
      exact coe_add_one_le_of_lt hlt)
  refine ⟨P + C (u 0) * X ^ k, ?_⟩
  filter_upwards [hP] with z hz
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [← hz]
  ring

theorem exists_polynomial_mul_analyticAt_off_lattice {f : ℂ → ℂ} (hf : Meromorphic f)
    (hp : IsPeriodic L f) :
    ∃ Q : ℂ[X], Q ≠ 0 ∧ ∀ z ∉ L.lattice, AnalyticAt ℂ (fun w ↦ Q.eval (℘[L] w) * f w) z := by
  classical
  have hT := finite_image_singularSet L hf hp
  let rep : Torus L → ℂ := Function.surjInv (Torus.mk_surjective L)
  have hrep : ∀ t, Torus.mk L (rep t) = t := Function.surjInv_eq _
  let n : Torus L → ℕ := fun t ↦ (hf (rep t)).choose
  have hn : ∀ t, AnalyticAt ℂ (fun z ↦ (z - rep t) ^ n t • f z) (rep t) := fun t ↦
    (hf (rep t)).choose_spec
  let N := hT.toFinset.sup n
  refine ⟨∏ t ∈ hT.toFinset, (X - C (℘[L] (rep t))) ^ N, ?_, fun z hz ↦ ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun t _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have h℘ : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
  by_cases hfz : AnalyticAt ℂ f z
  · exact (analyticAt_eval h℘ _).mul hfz
  have ht : Torus.mk L z ∈ hT.toFinset := hT.mem_toFinset.2 ⟨z, hfz, rfl⟩
  have hza : z - rep (Torus.mk L z) ∈ L.lattice := (Torus.mk_eq_mk_iff L).1 (hrep _).symm
  have h℘a : ℘[L] (rep (Torus.mk L z)) = ℘[L] z :=
    isPeriodic_weierstrassP.eq_of_mk_eq (hrep _)
  have hφ : AnalyticAt ℂ (fun w ↦ ℘[L] w - ℘[L] z) z := h℘.sub analyticAt_const
  have hdφ : AnalyticAt ℂ (dslope (fun w ↦ ℘[L] w - ℘[L] z) z) z := by
    obtain ⟨p, hp'⟩ := hφ
    exact ⟨_, hp'.has_fpower_series_dslope_fslope⟩
  have hφeq : ∀ w, ℘[L] w - ℘[L] z = (w - z) * dslope (fun w ↦ ℘[L] w - ℘[L] z) z w := by
    intro w
    have := sub_smul_dslope_of_zero (f := fun w ↦ ℘[L] w - ℘[L] z) (sub_self _) w
    simp only [smul_eq_mul] at this
    exact this.symm
  have hnN : n (Torus.mk L z) ≤ N := Finset.le_sup ht
  have h1 : AnalyticAt ℂ (fun w ↦ (w - z) ^ n (Torus.mk L z) * f w) z := by
    set a := rep (Torus.mk L z)
    have hF : AnalyticAt ℂ (fun u ↦ (u - a) ^ n (Torus.mk L z) • f u) (z - (z - a)) := by
      rw [sub_sub_cancel]; exact hn _
    have := hF.comp (f := fun w ↦ w - (z - a)) (by fun_prop)
    refine this.congr (Eventually.of_forall fun w ↦ ?_)
    simp only [Function.comp_apply, smul_eq_mul]
    rw [show w - (z - a) - a = w - z by ring, hp.sub w hza]
  have hfN : AnalyticAt ℂ (fun w ↦ (w - z) ^ N * f w) z := by
    have e : (fun w ↦ (w - z) ^ N * f w) =
        fun w ↦ (w - z) ^ (N - n (Torus.mk L z)) * ((w - z) ^ n (Torus.mk L z) * f w) := by
      funext w; rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnN]
    rw [e]
    fun_prop
  generalize dslope (fun w ↦ ℘[L] w - ℘[L] z) z = D at hdφ hφeq
  refine (((hdφ.pow N).mul (analyticAt_eval h℘
    (∏ s ∈ hT.toFinset.erase (Torus.mk L z), (X - C (℘[L] (rep s))) ^ N))).mul hfN).congr
    (Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [← Finset.mul_prod_erase hT.toFinset (fun s ↦ (X - C (℘[L] (rep s))) ^ N) ht]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, h℘a]
  rw [hφeq w, mul_pow]
  ring

lemma eventually_nhdsNE_zero_eval_weierstrassP_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q.eval (℘[L] z) ≠ 0 := by
  have hcob : Tendsto ℘[L] (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
    apply tendsto_cobounded_of_meromorphicOrderAt_neg
    rw [L.order_weierstrassP 0 L.lattice.zero_mem]
    decide
  have hb : Bornology.IsBounded {w : ℂ | Q.IsRoot w} :=
    (Polynomial.finite_setOfPred_isRoot hQ).isBounded
  filter_upwards [hcob.eventually hb] with z hz
  exact hz

lemma eventually_codiscrete_ne_zero_of_nhdsNE {F : ℂ → ℂ} (hF : Meromorphic F)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z ≠ 0) : ∀ᶠ z in codiscrete ℂ, F z ≠ 0 := by
  have h0 : meromorphicOrderAt F 0 ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hF 0)).2 h
  have hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt F u ≠ ⊤ := fun u _ ↦
    (hF.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ 0) (mem_univ u) h0
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
    (hF.meromorphicOn (s := univ)) hall

lemma eventually_codiscrete_eval_weierstrassP_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in codiscrete ℂ, Q.eval (℘[L] z) ≠ 0 :=
  eventually_codiscrete_ne_zero_of_nhdsNE (fun z ↦ meromorphicAt_eval
    (L.meromorphic_weierstrassP z) Q) (eventually_nhdsNE_zero_eval_weierstrassP_ne_zero hQ)

lemma eventually_codiscrete_derivWeierstrassP_ne_zero :
    ∀ᶠ z in codiscrete ℂ, ℘'[L] z ≠ 0 := by
  apply eventually_codiscrete_ne_zero_of_nhdsNE L.meromorphic_derivWeierstrassP
  have hR : (C 4 * X ^ 3 - C L.g₂ * X - C L.g₃ : ℂ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℂ[X] ↦ p.coeff 3) h
    norm_num [coeff_X, coeff_C] at this
  filter_upwards [eventually_nhdsNE_zero_eval_weierstrassP_ne_zero hR,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz hzl hz0
  intro h
  have hzL : z ∉ L.lattice := fun hm ↦ hzl ⟨hm, hz0⟩
  have := L.derivWeierstrassP_sq z hzL
  rw [h] at this
  apply hz
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination -this

theorem exists_polynomial_div_of_even {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    (he : ∀ z, f (-z) = f z) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) / Q.eval (℘[L] z) := by
  obtain ⟨Q, hQ, hQa⟩ := exists_polynomial_mul_analyticAt_off_lattice hf.1 hf.2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun w ↦ Q.eval (℘[L] w) * f w) 0 := by
    cases h : meromorphicOrderAt (fun w ↦ Q.eval (℘[L] w) * f w) 0 with
    | top => exact ⟨0, le_top⟩
    | coe o => exact ⟨o.natAbs, by exact_mod_cast (by omega : -(o.natAbs : ℤ) ≤ o)⟩
  obtain ⟨P, hP⟩ := exists_polynomial_of_even_of_analyticAt_off_lattice n
    (g := fun w ↦ Q.eval (℘[L] w) * f w)
    (fun z ↦ by
      have := hf.1 z
      have := meromorphicAt_eval (L.meromorphic_weierstrassP z) Q
      fun_prop)
    (fun z l hl ↦ by simp only [hf.2 z l hl, isPeriodic_weierstrassP z l hl])
    (fun z ↦ by simp only [he, L.weierstrassP_neg]) hQa hn
  refine ⟨P, Q, hQ, ?_⟩
  filter_upwards [hP, eventually_codiscrete_eval_weierstrassP_ne_zero hQ] with z hz hQz
  rw [← hz, mul_div_cancel_left₀ _ hQz]

theorem exists_rational_weierstrassP {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∃ P Q R S : ℂ[X], Q ≠ 0 ∧ S ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z ↦
      P.eval (℘[L] z) / Q.eval (℘[L] z) + ℘'[L] z * (R.eval (℘[L] z) / S.eval (℘[L] z)) := by
  have hneg : Meromorphic fun z ↦ f (-z) := fun z ↦ by
    have : MeromorphicAt f (-z) := hf.1 (-z)
    exact this.comp_analyticAt (g := fun z ↦ -z) (by fun_prop)
  have hpneg : IsPeriodic L fun z ↦ f (-z) := fun z l hl ↦ by
    simp only [neg_add, ← sub_eq_add_neg]
    exact hf.2.sub (-z) hl
  obtain ⟨P, Q, hQ, h1⟩ := exists_polynomial_div_of_even (L := L)
    (f := fun z ↦ (f z + f (-z)) / 2)
    ⟨fun z ↦ ((hf.1 z).add (hneg z)).div analyticAt_const.meromorphicAt,
      fun z l hl ↦ by simp only [hf.2 z l hl, hpneg z l hl]⟩
    (fun z ↦ by simp only [neg_neg]; ring)
  obtain ⟨R, S, hS, h2⟩ := exists_polynomial_div_of_even (L := L)
    (f := fun z ↦ (f z - f (-z)) / 2 / ℘'[L] z)
    ⟨fun z ↦ (((hf.1 z).sub (hneg z)).div analyticAt_const.meromorphicAt).div
      (L.meromorphic_derivWeierstrassP z),
      fun z l hl ↦ by simp only [hf.2 z l hl, hpneg z l hl, isPeriodic_derivWeierstrassP z l hl]⟩
    (fun z ↦ by simp only [neg_neg, L.derivWeierstrassP_neg]; ring)
  refine ⟨P, Q, R, S, hQ, hS, ?_⟩
  filter_upwards [h1, h2, eventually_codiscrete_derivWeierstrassP_ne_zero (L := L)]
    with z e1 e2 e3
  rw [← e1, ← e2]
  field_simp
  ring
end

section
open Complex Filter Topology Set
open scoped Interval Real

variable {L : PeriodPair}

lemma IsPeriodic.residue_add {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f) {l : ℂ}
    (hl : l ∈ L.lattice) (z : ℂ) : residue f (z + l) = residue f z := by
  rw [← residue_comp_add (hf (z + l)), hp.comp_add hl]

lemma IsPeriodic.residue_eq_of_mk_eq {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f)
    {z w : ℂ} (h : Torus.mk L z = Torus.mk L w) : residue f z = residue f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  have := hp.residue_add hf hzw w
  rwa [add_sub_cancel] at this

variable (L) in
def torusResidue (L : PeriodPair) (f : ℂ → ℂ) (x : Torus L) : ℂ :=
  residue f x.out

lemma torusResidue_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusResidue L f (Torus.mk L z) = residue f z :=
  hf.2.residue_eq_of_mk_eq hf.1 (QuotientAddGroup.out_eq' (Torus.mk L z))

variable (L) in
lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by
  intro h
  have := LinearIndependent.pair_iff.mp L.indep 1 0 (by simp [h])
  simp at this

variable (L) in
lemma im_ω₂_div_ω₁_ne_zero : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro him
  have hc := ω₁_ne_zero L
  set τ := L.ω₂ / L.ω₁ with hτdef
  have hτ : ((τ.re : ℝ) : ℂ) = τ := Complex.ext (by simp) (by simp [him])
  have key := LinearIndependent.pair_iff.mp L.indep τ.re (-1) (by
    rw [Complex.real_smul, Complex.real_smul, hτ, hτdef]
    push_cast
    field_simp
    ring)
  norm_num at key

theorem finsum_torusResidue_eq_zero {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusResidue L f x = 0 := by
  classical
  obtain ⟨hmer, hper⟩ := hf
  have hω₁ : L.ω₁ ≠ 0 := ω₁_ne_zero L
  set c := L.ω₁ with hc_def
  have hc : c ≠ 0 := ω₁_ne_zero L
  have hcL : c ∈ L.lattice := L.ω₁_mem_lattice
  obtain ⟨τ, s, hs, hω₂, hτ⟩ : ∃ τ : ℂ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      L.ω₂ = (s : ℂ) * (c * τ) ∧ 0 < τ.im := by
    rcases lt_or_gt_of_ne (im_ω₂_div_ω₁_ne_zero L) with h | h
    · refine ⟨-(L.ω₂ / L.ω₁), -1, Or.inr rfl, ?_, by simpa using h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
    · refine ⟨L.ω₂ / L.ω₁, 1, Or.inl rfl, ?_, h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
  have hτL : c * τ ∈ L.lattice := by
    have h2 := L.ω₂_mem_lattice
    rcases hs with rfl | rfl
    · simpa [hω₂] using h2
    · simpa [hω₂] using L.lattice.neg_mem h2
  set h := τ.im with hh
  set g : ℂ → ℂ := fun w ↦ f (c * w) with hg_def
  have hg1 : ∀ u, g (u + 1) = g u := fun u ↦ by
    simp only [hg_def, mul_add, mul_one]
    exact hper _ _ hcL
  have hgτ : ∀ u, g (u + τ) = g u := fun u ↦ by
    simp only [hg_def, mul_add]
    exact hper _ _ hτL
  have hgmer : Meromorphic g := fun w ↦
    (hmer (c * w)).comp_analyticAt (g := fun w ↦ c * w) (by fun_prop)

  have hScount : (singularSet g).Countable := by
    have e : singularSet g = ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n ∩ singularSet g := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
        exact ⟨n, hn, hz⟩
      · rintro ⟨n, -, hz⟩
        exact hz
    rw [e]
    exact countable_iUnion fun n ↦
      (finite_inter_singularSet hgmer (isCompact_closedBall 0 (n : ℝ))).countable

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ ((fun s : ℂ ↦ s.re) '' singularSet g ∪
      (fun s : ℂ ↦ s.re - 1) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∈ ((fun s : ℂ ↦ s.im) '' singularSet g ∪
      (fun s : ℂ ↦ s.im - h) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  set a : ℂ := x₀ + y₀ * I with ha
  set b : ℂ := a + 1 + h * I with hb
  have ha_re : a.re = x₀ := by simp [ha]
  have ha_im : a.im = y₀ := by simp [ha]
  have hb_re : b.re = x₀ + 1 := by simp [hb, ha]
  have hb_im : b.im = y₀ + h := by simp [hb, ha]
  set K : Set ℂ := [[a.re, b.re]] ×ℂ [[a.im, b.im]] with hK_def
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hKmem : ∀ u : ℂ, u ∈ K ↔ u.re ∈ Icc x₀ (x₀ + 1) ∧ u.im ∈ Icc y₀ (y₀ + h) := by
    intro u
    rw [hK_def, mem_reProdIm, ha_re, hb_re, ha_im, hb_im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)]
  set T : Finset ℂ := (finite_inter_singularSet hgmer hK).toFinset with hT
  have hTmem : ∀ p, p ∈ T ↔ p ∈ K ∧ p ∈ singularSet g := by
    intro p
    simp [hT]

  have hTin : ∀ p ∈ T, x₀ < p.re ∧ p.re < x₀ + 1 ∧ y₀ < p.im ∧ p.im < y₀ + h := by
    intro p hp
    obtain ⟨hpK, hpS⟩ := (hTmem p).1 hp
    obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := (hKmem p).1 hpK
    have nr1 : p.re ≠ x₀ := fun e ↦ hx₀ (Or.inl ⟨p, hpS, e⟩)
    have nr2 : p.re ≠ x₀ + 1 := fun e ↦ hx₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    have ni1 : p.im ≠ y₀ := fun e ↦ hy₀ (Or.inl ⟨p, hpS, e⟩)
    have ni2 : p.im ≠ y₀ + h := fun e ↦ hy₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    exact ⟨lt_of_le_of_ne r1 (Ne.symm nr1), lt_of_le_of_ne r2 nr2,
      lt_of_le_of_ne i1 (Ne.symm ni1), lt_of_le_of_ne i2 ni2⟩

  have hsum0 : ∑ p ∈ T, residue g p = 0 := by
    have hres := rectIntegral_eq_sum_residue (f := g) (z := a) (w := b) T
      (fun p hp ↦ by
        obtain ⟨r1, r2, i1, i2⟩ := hTin p hp
        exact ⟨by rwa [ha_re], by rwa [hb_re], by rwa [ha_im], by rwa [hb_im]⟩)
      (fun p _ ↦ hgmer p)
      (fun u hu huT ↦ by
        by_contra hna
        exact huT ((hTmem u).2 ⟨hu, hna⟩))
    have hper0 : rectIntegral g a b = 0 := rectIntegral_eq_zero_of_periodic hg1 hgτ a
    rw [hper0] at hres
    have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    exact (mul_eq_zero.1 hres.symm).resolve_left h2pi

  set φ : ℂ → Torus L := fun p ↦ Torus.mk L (c * p) with hφ
  have hlat : ∀ m n : ℤ, (m : ℂ) * c + (n : ℂ) * (c * τ) ∈ L.lattice := fun m n ↦
    L.lattice.add_mem (by simpa [zsmul_eq_mul] using L.lattice.smul_mem m hcL)
      (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hτL)

  have hsupp : Function.support (torusResidue L f) ⊆ ↑(T.image φ) := by
    intro x hx
    set z := x.out with hz
    have hxz : Torus.mk L z = x := QuotientAddGroup.out_eq' x
    have hnz : residue f z ≠ 0 := hx
    have hfz : ¬ AnalyticAt ℂ f z := fun ha ↦ hnz (residue_eq_zero_of_analyticAt ha)
    set w := z / c with hw
    set n : ℤ := ⌊(w.im - y₀) / h⌋ with hn
    set p₁ : ℂ := w - n * τ with hp₁
    set m : ℤ := ⌊p₁.re - x₀⌋ with hm
    set p : ℂ := p₁ - m with hp
    have hp_re : p.re = p₁.re - m := by simp [hp]
    have hp_im : p.im = w.im - n * h := by simp [hp, hp₁, hh]
    have hn1 := Int.floor_le ((w.im - y₀) / h)
    have hn2 := Int.lt_floor_add_one ((w.im - y₀) / h)
    have hm1 := Int.floor_le (p₁.re - x₀)
    have hm2 := Int.lt_floor_add_one (p₁.re - x₀)
    rw [← hn] at hn1 hn2
    rw [← hm] at hm1 hm2
    rw [le_div_iff₀ hτ] at hn1
    rw [div_lt_iff₀ hτ] at hn2
    have hpK : p ∈ K := by
      rw [hKmem, hp_re, hp_im]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
    have hcp : z = c * p + ((m : ℂ) * c + (n : ℂ) * (c * τ)) := by
      simp only [hp, hp₁, hw]
      field_simp
      ring
    have hpS : p ∈ singularSet g := by
      intro hga
      apply hfz
      have h1 : AnalyticAt ℂ (fun z' ↦ g (c⁻¹ * z')) (c * p) := by
        have : AnalyticAt ℂ (fun z' ↦ c⁻¹ * z') (c * p) := by fun_prop
        exact hga.comp_of_eq this (by field_simp)
      have h2 : (fun z' ↦ g (c⁻¹ * z')) = f := by
        funext z'
        simp only [hg_def]
        congr 1
        field_simp
      rw [h2] at h1
      rw [hcp]
      exact (hper.analyticAt_add_iff (hlat m n) (c * p)).2 h1
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hTmem p).2 ⟨hpK, hpS⟩, ?_⟩)
    rw [← hxz, hφ]
    exact ((Torus.mk_eq_mk_iff L).2 (by rw [hcp]; simpa using hlat m n)).symm

  have hinj : Set.InjOn φ ↑T := by
    intro p hp q hq hpq
    obtain ⟨pr1, pr2, pi1, pi2⟩ := hTin p hp
    obtain ⟨qr1, qr2, qi1, qi2⟩ := hTin q hq
    have hdiff := (Torus.mk_eq_mk_iff L).1 hpq
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hdiff
    have hk : p - q = (m : ℂ) + ((n * s : ℤ) : ℂ) * τ := by
      have e : c * (p - q) = c * ((m : ℂ) + ((n * s : ℤ) : ℂ) * τ) := by
        rw [mul_sub, ← hmn, hω₂]
        push_cast
        ring
      exact mul_left_cancel₀ hc e
    set k : ℤ := n * s with hkdef
    have him := congrArg Complex.im hk
    have hre := congrArg Complex.re hk
    simp only [sub_im, add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add,
      sub_re, add_re, intCast_re, mul_re, intCast_im, zero_mul, sub_zero] at him hre
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) * h < h := by rw [hh]; linarith
      have h2 : -h < (k : ℝ) * h := by rw [hh]; linarith
      have h3 : (k : ℝ) < 1 := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h4 : (-1 : ℝ) < k := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h5 : k < 1 := by exact_mod_cast h3
      have h6 : -1 < k := by exact_mod_cast h4
      omega
    rw [hk0] at hre him
    simp only [Int.cast_zero, zero_mul, add_zero, sub_eq_zero] at hre him
    have hm0 : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith
      have h4 : (-1 : ℝ) < m := by linarith
      have h5 : m < 1 := by exact_mod_cast h3
      have h6 : -1 < m := by exact_mod_cast h4
      omega
    rw [hm0] at hre
    simp only [Int.cast_zero, sub_eq_zero] at hre
    exact Complex.ext hre him
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  have hterm : ∀ p ∈ T, torusResidue L f (φ p) = c * residue g p := by
    intro p _
    rw [hφ, torusResidue_mk ⟨hmer, hper⟩,
      show residue g p = c⁻¹ * residue f (c * p) from residue_comp_mul hc (hmer _)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum0, mul_zero]
end

section
open Complex Filter Topology Set
open scoped PeriodPair

variable {L : PeriodPair}

variable (L) in
def torusOrder (L : PeriodPair) (f : ℂ → ℂ) (x : Torus L) : ℤ :=
  (meromorphicOrderAt f x.out).untopD 0

lemma torusOrder_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusOrder L f (Torus.mk L z) = (meromorphicOrderAt f z).untopD 0 := by
  have h := (Torus.mk_eq_mk_iff L).1 (QuotientAddGroup.out_eq' (Torus.mk L z))
  have := hf.2.meromorphicOrderAt_add h z
  rw [add_sub_cancel] at this
  rw [torusOrder, this]

lemma isEllipticFunction_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    IsEllipticFunction L (logDeriv f) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ ?_⟩
  · have : logDeriv f = fun w ↦ deriv f w / f w := rfl
    rw [this]
    exact (hf.1 z).deriv.div (hf.1 z)
  · simp only [logDeriv_apply]
    rw [hf.2 z l hl]
    congr 1
    rw [← deriv_comp_add_const, hf.2.comp_add hl]

lemma residue_logDeriv_eq_untopD {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    residue (logDeriv f) z = (((meromorphicOrderAt f z).untopD 0 : ℤ) : ℂ) := by
  by_cases htop : meromorphicOrderAt f z = ⊤
  · rw [htop, WithTop.untopD_top, Int.cast_zero]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hmer : MeromorphicAt (logDeriv f) z := by
      have : logDeriv f = fun w ↦ deriv f w / f w := rfl
      rw [this]
      exact hf.deriv.div hf
    have h0 : logDeriv f =ᶠ[𝓝[≠] z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [htop] with w hw
      simp [logDeriv_apply, hw]
    rw [residue_congr hmer h0]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hn, WithTop.untopD_coe]
    exact residue_logDeriv hf hn.symm

lemma torusResidue_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (x : Torus L) :
    torusResidue L (logDeriv f) x = (torusOrder L f x : ℂ) :=
  residue_logDeriv_eq_untopD (hf.1 _)

lemma finite_support_torusResidue {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusResidue L f)).Finite := by
  refine (finite_image_singularSet L hf.1 hf.2).subset ?_
  intro x hx
  refine ⟨x.out, fun ha ↦ hx (residue_eq_zero_of_analyticAt ha), QuotientAddGroup.out_eq' x⟩

lemma finite_support_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusOrder L f)).Finite := by
  refine (finite_support_torusResidue (isEllipticFunction_logDeriv hf)).subset ?_
  intro x hx
  simp only [Function.mem_support, torusResidue_logDeriv hf] at hx ⊢
  exact_mod_cast hx

variable (L) in
def degree (L : PeriodPair) (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ x : Torus L, (-torusOrder L f x).toNat

lemma toNat_neg_untopD_sub_const {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (c : ℂ) :
    (-(meromorphicOrderAt (fun w ↦ f w - c) z).untopD 0).toNat =
      (-(meromorphicOrderAt f z).untopD 0).toNat := by
  have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
  have e : (fun w ↦ f w - c) = f + fun _ ↦ -c := by
    funext w; simp [sub_eq_add_neg]
  have hc0 : 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicOrderAt_nonneg
  rw [e]
  by_cases hneg : meromorphicOrderAt f z < 0
  · rw [meromorphicOrderAt_add_eq_left_of_lt hc (hneg.trans_le hc0)]
  · push Not at hneg
    have h1 : 0 ≤ meromorphicOrderAt (f + fun _ ↦ -c) z :=
      le_trans (le_min hneg hc0) (meromorphicOrderAt_add hf hc)
    have key : ∀ o : WithTop ℤ, 0 ≤ o → (-(o.untopD 0)).toNat = 0 := by
      intro o ho
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (0 : ℤ) ≤ n := by exact_mod_cast ho
        omega
    rw [key _ h1, key _ hneg]

lemma nonneg_of_toNat_neg_untopD_eq_zero {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 0) :
    0 ≤ o := by
  induction o with
  | top => exact le_top
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

lemma toNat_neg_untopD_eq_zero_of_nonneg {o : WithTop ℤ} (h : 0 ≤ o) :
    (-(o.untopD 0)).toNat = 0 := by
  induction o with
  | top => simp
  | coe n =>
    simp only [WithTop.untopD_coe]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    omega

lemma eq_neg_one_of_toNat_neg_untopD_eq_one {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 1) :
    o = ((-1 : ℤ) : WithTop ℤ) := by
  induction o with
  | top => simp at h
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    have : n = -1 := by omega
    rw [this]

lemma eventually_nhdsNE_of_eventually_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z)
    (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, p z := by
  rw [Filter.Eventually, codiscrete, mem_codiscreteWithin] at h
  have := disjoint_principal_right.1 (h x (mem_univ x))
  filter_upwards [this] with z hz
  by_contra hpz
  exact hz ⟨mem_univ z, hpz⟩

lemma finite_support_toNat_neg_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support fun x ↦ (-torusOrder L f x).toNat).Finite :=
  (finite_support_torusOrder hf).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega

lemma eq_zero_of_finsum_eq_zero_nat {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (h : ∑ᶠ x, u x = 0) (x : α) : u x = 0 := by
  classical
  by_contra hx
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp)] at h
  exact hx ((Finset.sum_eq_zero_iff.1 h) x (by simpa using hx))

theorem degree_ne_one {f : ℂ → ℂ} (hf : IsEllipticFunction L f) : degree L f ≠ 1 := by
  classical
  intro h1
  set u : Torus L → ℕ := fun x ↦ (-torusOrder L f x).toNat with hu
  have hfin : (Function.support u).Finite := finite_support_toNat_neg_torusOrder hf
  set s := hfin.toFinset with hs
  have hsum : ∑ x ∈ s, u x = 1 := by
    rw [← finsum_eq_sum_of_support_subset u (by simp [hs])]
    exact h1
  obtain ⟨x₀, hx₀s, hx₀⟩ : ∃ x₀ ∈ s, u x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact zero_ne_one hsum
  have hsplit := Finset.add_sum_erase s u hx₀s
  rw [hsum] at hsplit
  have hux₀ : u x₀ = 1 := by omega
  have hrest : ∀ x, x ≠ x₀ → u x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · have h0 : ∑ y ∈ s.erase x₀, u y = 0 := by omega
      exact Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_erase.2 ⟨hx, hxs⟩)
    · simpa [hs] using hxs
  have hres := finsum_torusResidue_eq_zero hf
  rw [finsum_eq_single _ x₀ (fun x hx ↦ ?_)] at hres
  · have hord := eq_neg_one_of_toNat_neg_untopD_eq_one hux₀
    exact residue_ne_zero_of_meromorphicOrderAt_eq_neg_one (hf.1 _) hord hres
  · exact residue_eq_zero_of_meromorphicOrderAt_nonneg (hf.1 _)
      (nonneg_of_toNat_neg_untopD_eq_zero (hrest x hx))
end

section
open Complex Filter Topology Set
open scoped PeriodPair

variable (L : PeriodPair)

def weierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

instance : (weierstrassCurve L).IsShortNF := ⟨rfl, rfl, rfl⟩

@[simp] lemma weierstrassCurve_a₁ : (weierstrassCurve L).a₁ = 0 := rfl
@[simp] lemma weierstrassCurve_a₂ : (weierstrassCurve L).a₂ = 0 := rfl
@[simp] lemma weierstrassCurve_a₃ : (weierstrassCurve L).a₃ = 0 := rfl
@[simp] lemma weierstrassCurve_a₄ : (weierstrassCurve L).a₄ = -(L.g₂ / 4) := rfl
@[simp] lemma weierstrassCurve_a₆ : (weierstrassCurve L).a₆ = -(L.g₃ / 4) := rfl

def discr : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

theorem weierstrassCurve_Δ : (weierstrassCurve L).Δ = discr L := by
  rw [WeierstrassCurve.Δ_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  ring

theorem weierstrassCurve_equation_iff (x Y : ℂ) :
    (weierstrassCurve L).toAffine.Equation x Y ↔
      (2 * Y) ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆]
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination h / 4

theorem equation_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (weierstrassCurve L).toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [weierstrassCurve_equation_iff, mul_div_cancel₀ _ two_ne_zero]
  exact L.derivWeierstrassP_sq z hz

variable {L}

lemma sum_le_finsum_of_finite {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (s : Finset α) : ∑ x ∈ s, u x ≤ ∑ᶠ x, u x := by
  classical
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset ∪ s) (fun x hx ↦ by simp [hx])]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_right

lemma isEllipticFunction_weierstrassP_sub (c : ℂ) :
    IsEllipticFunction L (fun z ↦ ℘[L] z - c) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [isPeriodic_weierstrassP z l hl]⟩
  have := L.meromorphic_weierstrassP z
  fun_prop

lemma meromorphicOrderAt_weierstrassP_sub_ne_top (c z : ℂ) :
    meromorphicOrderAt (fun w ↦ ℘[L] w - c) z ≠ ⊤ := by
  intro htop
  have h1 := meromorphicOrderAt_eq_top_iff.1 htop
  have h2 := eventually_nhdsNE_of_eventually_codiscrete
    (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) (Polynomial.X_sub_C_ne_zero c)) z
  obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hw2
  exact hw2 hw1

lemma le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) {n : ℕ}
    (h : ∀ i < n, iteratedDeriv i (fun w ↦ ℘[L] w - c) z = 0) :
    n ≤ (torusOrder (L := L) (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat := by
  have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
    (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hne := meromorphicOrderAt_weierstrassP_sub_ne_top (L := L) c z
  have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).2 h
  have hrep : Torus.mk L (Torus.mk L z).out = Torus.mk L z :=
    QuotientAddGroup.out_eq' (Torus.mk L z)
  have hperiod := (Torus.mk_eq_mk_iff L).1 hrep
  have horder := (isEllipticFunction_weierstrassP_sub c).2.meromorphicOrderAt_add hperiod z
  rw [add_sub_cancel] at horder
  rw [torusOrder, horder, ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hne
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt (fun w ↦ ℘[L] w - c) z :=
    ENat.ne_top_iff_exists.1 (fun h ↦ hne (by simp [h]))
  rw [← hm] at hle ⊢
  simp only [ENat.map_natCast, WithTop.untopD_coe, Int.toNat_natCast]
  exact_mod_cast hle

lemma one_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c) :
    1 ≤ (torusOrder (L := L) (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    obtain rfl : i = 0 := by omega
    simp [hc]

lemma two_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c)
    (h' : ℘'[L] z = 0) :
    2 ≤ (torusOrder (L := L) (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    interval_cases i
    · simp [hc]
    · rw [iteratedDeriv_one, deriv_sub_const, L.deriv_weierstrassP]
      exact h'

lemma finsum_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder (L := L) (fun w ↦ ℘[L] w - c) x).toNat = 2 := by
  let f : ℂ → ℂ := fun w ↦ ℘[L] w - c
  let order : Torus L → ℤ := torusOrder (L := L) f
  change ∑ᶠ x, (order x).toNat = 2
  have hf : IsEllipticFunction L f := isEllipticFunction_weierstrassP_sub c
  have hlog := isEllipticFunction_logDeriv hf
  have hres (x : Torus L) : torusResidue L (logDeriv f) x = (order x : ℂ) :=
    residue_logDeriv_eq_untopD (hf.1 x.out)
  have hfin : order.HasFiniteSupport :=
    (finite_support_torusResidue hlog).subset fun x hx ↦ by
      simp only [Function.mem_support, hres] at hx ⊢
      exact_mod_cast hx
  have hsum : ∑ᶠ x, order x = 0 := by
    have h := finsum_torusResidue_eq_zero hlog
    simp_rw [hres] at h
    have hc := (Int.castAddHom ℂ).map_finsum hfin
    simp only [Int.coe_castAddHom] at hc
    rw [← hc] at h
    exact_mod_cast h
  have hpos := hfin.fun_comp (g := Int.toNat) rfl
  have hneg := hfin.fun_comp (g := fun n ↦ (-n).toNat) rfl
  have hbalance :
      (∑ᶠ x, ((order x).toNat : ℤ)) - (∑ᶠ x, ((-order x).toNat : ℤ)) = 0 := by
    rw [← finsum_sub_distrib (hpos.fun_comp (g := fun n : ℕ ↦ (n : ℤ)) rfl)
      (hneg.fun_comp (g := fun n : ℕ ↦ (n : ℤ)) rfl)]
    simp only [Int.toNat_sub_toNat_neg, hsum]
  have hcounts : (∑ᶠ x, (order x).toNat) = ∑ᶠ x, (-order x).toNat := by
    have hcastPos := (Nat.castAddMonoidHom ℤ).map_finsum hpos
    have hcastNeg := (Nat.castAddMonoidHom ℤ).map_finsum hneg
    exact Int.ofNat_injective (hcastPos.trans ((sub_eq_zero.mp hbalance).trans hcastNeg.symm))
  have hpole (x : Torus L) :
      (-order x).toNat = (-(meromorphicOrderAt ℘[L] x.out).untopD 0).toNat :=
    toNat_neg_untopD_sub_const (L.meromorphic_weierstrassP x.out) c
  have hrep (x : Torus L) : x.out ∈ L.lattice ↔ x = 0 := by
    have hx : Torus.mk L x.out = x := QuotientAddGroup.out_eq' x
    have hzero : Torus.mk L 0 = (0 : Torus L) := QuotientAddGroup.mk_zero _
    rw [← sub_zero x.out, ← Torus.mk_eq_mk_iff L, hx, hzero]
  rw [hcounts, finsum_eq_single _ (0 : Torus L) ?_]
  · have horder : meromorphicOrderAt ℘[L] (0 : Torus L).out = ((-2 : ℤ) : WithTop ℤ) := by
      rw [L.order_weierstrassP _ ((hrep 0).2 rfl)]
      norm_num
    rw [hpole, horder, WithTop.untopD_coe]
    rfl
  · intro x hx
    rw [hpole]
    exact toNat_neg_untopD_eq_zero_of_nonneg
      (L.analyticOnNhd_weierstrassP x.out (fun h ↦ hx ((hrep x).1 h))).meromorphicOrderAt_nonneg

lemma finite_support_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    (Function.support fun x ↦ (torusOrder (L := L) (fun w ↦ ℘[L] w - c) x).toNat).Finite :=
  hasFiniteSupport_of_finsum_ne_zero (by rw [finsum_toNat_torusOrder_weierstrassP_sub]; decide)

lemma torus_mk_ne {z w : ℂ} (h : z - w ∉ L.lattice) : Torus.mk L z ≠ Torus.mk L w :=
  fun e ↦ h ((Torus.mk_eq_mk_iff L).1 e)

theorem derivWeierstrassP_eq_zero_of_two_mul_mem {w : ℂ} (h : 2 * w ∈ L.lattice) :
    ℘'[L] w = 0 := by
  have h1 : ℘'[L] (w - 2 * w) = ℘'[L] w := L.derivWeierstrassP_sub_coe w ⟨_, h⟩
  rw [show w - 2 * w = -w by ring, L.derivWeierstrassP_neg] at h1
  linear_combination -h1 / 2

theorem two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero {w : ℂ} (hw : w ∉ L.lattice) :
    2 * w ∈ L.lattice ↔ ℘'[L] w = 0 := by
  classical
  refine ⟨derivWeierstrassP_eq_zero_of_two_mul_mem, fun h' ↦ ?_⟩
  by_contra h2
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hne : Torus.mk L w ≠ Torus.mk L (-w) :=
    torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
  have hsum := sum_le_finsum_of_finite (finite_support_toNat_torusOrder_weierstrassP_sub (℘[L] w))
    {Torus.mk L w, Torus.mk L (-w)}
  rw [finsum_toNat_torusOrder_weierstrassP_sub, Finset.sum_pair hne] at hsum
  have o1 := two_le_toNat_torusOrder_weierstrassP_sub hw rfl h'
  have o2 := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
  omega

theorem sub_mem_or_add_mem_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) :
    z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hfin := finite_support_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have htot := finsum_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have oz := one_le_toNat_torusOrder_weierstrassP_sub hz h
  have hzw : Torus.mk L z ≠ Torus.mk L w := torus_mk_ne h1
  by_cases h2w : 2 * w ∈ L.lattice
  · have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w}
    rw [htot, Finset.sum_pair hzw] at hsum
    have ow := two_le_toNat_torusOrder_weierstrassP_sub hw rfl
      (derivWeierstrassP_eq_zero_of_two_mul_mem h2w)
    omega
  · have hzw' : Torus.mk L z ≠ Torus.mk L (-w) := torus_mk_ne (by rwa [sub_neg_eq_add])
    have hww' : Torus.mk L w ≠ Torus.mk L (-w) :=
      torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
    have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w, Torus.mk L (-w)}
    rw [htot, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hzw, hzw'⟩), Finset.sum_pair hww'] at hsum
    have ow := one_le_toNat_torusOrder_weierstrassP_sub hw rfl
    have ow' := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
    omega

lemma notMem_lattice_of_eq {x : ℂ} (α β : ℚ) (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬(α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  rw [hx]
  exact fun hm ↦ h (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice.1 hm)

lemma halfPeriod_facts :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₁ / 2) + ℘[L] (L.ω₂ / 2) + ℘[L] ((L.ω₁ + L.ω₂) / 2) = 0 ∧
      4 * (℘[L] (L.ω₁ / 2) ^ 2 + ℘[L] (L.ω₁ / 2) * ℘[L] (L.ω₂ / 2) + ℘[L] (L.ω₂ / 2) ^ 2) =
        L.g₂ ∧
      L.g₃ = 4 * ℘[L] (L.ω₁ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₁ / 2) := by
  set e1 := ℘[L] (L.ω₁ / 2)
  set e2 := ℘[L] (L.ω₂ / 2)
  set e3 := ℘[L] ((L.ω₁ + L.ω₂) / 2)
  have n1 : L.ω₁ / 2 ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have n2 : L.ω₂ / 2 ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice :=
    notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num)
  have root : ∀ u, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
    rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
    ring
  have f1 := root _ n1 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)
  have f2 := root _ n2 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)
  have f3 := root _ n3 (by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
  have d12 : e1 ≠ e2 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n2 h with h' | h'
    · exact notMem_lattice_of_eq (1 / 2) (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d13 : e1 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n3 h with h' | h'
    · exact notMem_lattice_of_eq 0 (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq 1 (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d23 : e2 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n2 n3 h with h' | h'
    · exact notMem_lattice_of_eq (-1 / 2) 0 (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) 1 (by push_cast; ring) (by norm_num) h'
  have s12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d12) (by linear_combination f1 - f2)
  have s13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d13) (by linear_combination f1 - f3)
  have hs : e1 + e2 + e3 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 d23) (by linear_combination (s12 - s13) / 4)
  exact ⟨d12, d13, d23, hs, s12, by linear_combination -f1⟩

variable (L)

theorem weierstrassP_halfPeriods_ne :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) :=
  let h := halfPeriod_facts (L := L)
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem discr_eq :
    discr L = 16 * ((℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2)) *
      (℘[L] (L.ω₁ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2)) *
      (℘[L] (L.ω₂ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2))) ^ 2 := by
  obtain ⟨-, -, -, hs, s12, hg3⟩ := halfPeriod_facts (L := L)
  rw [discr, hg3, ← s12, show ℘[L] ((L.ω₁ + L.ω₂) / 2) = -℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2) by
    linear_combination hs]
  ring

theorem discr_ne_zero : discr L ≠ 0 := by
  obtain ⟨d12, d13, d23⟩ := weierstrassP_halfPeriods_ne L
  rw [discr_eq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d12)
    (sub_ne_zero.2 d13)) (sub_ne_zero.2 d23)))

theorem weierstrassCurve_Δ_ne_zero : (weierstrassCurve L).Δ ≠ 0 := by
  rw [weierstrassCurve_Δ]
  exact discr_ne_zero L

instance : (weierstrassCurve L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (weierstrassCurve_Δ_ne_zero L)⟩

theorem weierstrassCurve_j : (weierstrassCurve L).j = 1728 * L.g₂ ^ 3 / discr L := by
  rw [WeierstrassCurve.j_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  have h := discr_ne_zero L
  rw [discr] at h
  have h1 : 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
    intro h0
    apply h
    linear_combination -16 * h0
  rw [div_eq_div_iff h1 h]
  ring
end

section
open Complex Filter Topology Set
open scoped PeriodPair

variable {L : PeriodPair}

lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by
  have hd : DifferentiableAt ℂ ℘[L] z := (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have := hd.hasDerivAt
  rwa [L.deriv_weierstrassP] at this

lemma hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (deriv ℘'[L] z) z :=
  (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt

theorem deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have key : ∀ u ∉ L.lattice,
      ℘'[L] u * (2 * deriv ℘'[L] u - (12 * ℘[L] u ^ 2 - L.g₂)) = 0 := by
    intro u hu
    have h1 : HasDerivAt (℘'[L] ^ 2) (2 * ℘'[L] u * deriv ℘'[L] u) u :=
      ((hasDerivAt_derivWeierstrassP hu).pow 2).congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃)
        ((12 * ℘[L] u ^ 2 - L.g₂) * ℘'[L] u) u := by
      have hp := hasDerivAt_weierstrassP hu
      exact ((((hp.pow 3).const_mul 4).sub (hp.const_mul L.g₂)).sub_const L.g₃).congr_deriv
        (by norm_num; ring)
    have heq : (℘'[L] ^ 2) =ᶠ[𝓝 u]
        (fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃) := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      exact L.derivWeierstrassP_sq v hv
    have := h1.unique (h2.congr_of_eventuallyEq heq)
    linear_combination this
  by_cases h0 : ℘'[L] z = 0
  · set D : ℂ → ℂ := fun u ↦ deriv ℘'[L] u - (6 * ℘[L] u ^ 2 - L.g₂ / 2) with hD
    have hDc : ContinuousAt D z := by
      have h1 := (L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt
      have h2 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
      exact h1.sub (((h2.pow 2).const_mul 6).sub continuousAt_const)
    have hev : ∀ᶠ u in 𝓝[≠] z, D u = 0 := by
      filter_upwards [eventually_nhdsNE_of_eventually_codiscrete
        (eventually_codiscrete_derivWeierstrassP_ne_zero (L := L)) z,
        nhdsWithin_le_nhds (hopen.mem_nhds hz)] with u hu1 hu2
      rcases mul_eq_zero.1 (key u hu2) with h | h
      · exact absurd h hu1
      · simp only [hD]
        linear_combination h / 2
    have hlim := tendsto_nhds_unique (hDc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun u hu ↦ hu.symm))
    simp only [hD] at hlim
    linear_combination hlim
  · rcases mul_eq_zero.1 (key z hz) with h | h
    · exact absurd h h0
    · linear_combination h / 2

theorem meromorphicOrderAt_nonneg_of_simple_pole {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    {p : ℂ} (hp : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p)
    (ho : ∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) (z : ℂ) :
    0 ≤ meromorphicOrderAt f z := by
  have hdeg : degree L f ≤ 1 := by
    rw [degree, finsum_eq_single _ (Torus.mk L p) (fun x hx ↦ ?_)]
    · rw [torusOrder_mk hf]
      generalize meromorphicOrderAt f p = o at hp
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (-1 : ℤ) ≤ n := by exact_mod_cast hp
        omega
    · obtain ⟨y, rfl⟩ := Torus.mk_surjective L x
      rw [torusOrder_mk hf]
      exact toNat_neg_untopD_eq_zero_of_nonneg
        (ho y fun h ↦ hx ((Torus.mk_eq_mk_iff L).2 h))
  have h0 : degree L f = 0 := by
    have := degree_ne_one hf
    omega
  have hall := eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0
    (Torus.mk L z)
  rw [torusOrder_mk hf] at hall
  exact nonneg_of_toNat_neg_untopD_eq_zero hall

lemma eq_of_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {x : ℂ} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (h : f =ᶠ[𝓝[≠] x] g) : f x = g x :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

variable (L) in
def chordSlope (L : PeriodPair) (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)

lemma chordSlope_comm (z w : ℂ) : chordSlope L z w = chordSlope L w z := by
  rw [chordSlope, chordSlope, ← neg_div_neg_eq, neg_sub, neg_sub]

variable (L) in
def addDefect (L : PeriodPair) (w z : ℂ) : ℂ :=
  ℘[L] (z + w) + ℘[L] z + ℘[L] w - chordSlope L z w ^ 2 / 4

lemma weierstrassP_eq_except_zero (z : ℂ) : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2 := by
  have := L.weierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  change ℘[L - (0 : ℂ)] z = ℘[L] z + (1 / (0 : ℂ) ^ 2 - 1 / (z - 0) ^ 2) at this
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, zero_sub,
    sub_zero] at this
  rw [this]
  ring

lemma derivWeierstrassP_eq_except_zero (z : ℂ) :
    ℘'[L] z = ℘'[L - (0 : ℂ)] z - 2 / z ^ 3 := by
  have := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  change ℘'[L - (0 : ℂ)] z = ℘'[L] z + 2 / (z - 0) ^ 3 at this
  simp only [sub_zero] at this
  rw [this]
  ring

lemma meromorphic_weierstrassP_comp_add (w : ℂ) : Meromorphic fun z ↦ ℘[L] (z + w) := fun x ↦
  (L.meromorphic_weierstrassP (x + w)).comp_analyticAt (g := fun z ↦ z + w) (by fun_prop)

lemma analyticAt_weierstrassP_comp_add {x w : ℂ} (h : x + w ∉ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] (z + w)) x :=
  (L.analyticOnNhd_weierstrassP (x + w) h).comp (g := ℘[L]) (f := fun z ↦ z + w) (by fun_prop)

lemma isEllipticFunction_addDefect (w : ℂ) : IsEllipticFunction L (addDefect L w) := by
  refine ⟨fun x ↦ ?_, fun z l hl ↦ ?_⟩
  · have h1 := meromorphic_weierstrassP_comp_add (L := L) w x
    have h2 := L.meromorphic_weierstrassP x
    have h3 := L.meromorphic_derivWeierstrassP x
    unfold addDefect chordSlope
    fun_prop
  · simp only [addDefect, chordSlope, add_right_comm z l w, isPeriodic_weierstrassP _ l hl,
      isPeriodic_derivWeierstrassP z l hl]

lemma analyticAt_addDefect {w z : ℂ} (hw : w ∉ L.lattice) (hz : z ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) : AnalyticAt ℂ (addDefect L w) z := by
  have hne : ℘[L] z - ℘[L] w ≠ 0 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq hz hw (sub_eq_zero.1 h) with h' | h'
    · exact hzw h'
    · exact hzw' h'
  have h1 := analyticAt_weierstrassP_comp_add hzw'
  have h2 := L.analyticOnNhd_weierstrassP z hz
  have h3 := L.analyticOnNhd_derivWeierstrassP z hz
  unfold addDefect chordSlope
  apply AnalyticAt.sub (by fun_prop)
  apply AnalyticAt.div _ analyticAt_const (by norm_num)
  apply AnalyticAt.pow
  exact AnalyticAt.div (by fun_prop) (by fun_prop) hne

lemma addDefect_algebra_zero (u p q x y z : ℂ) (hz : z ≠ 0) (hB : z ^ 2 * (p - x) + 1 ≠ 0) :
    u + (p + 1 / z ^ 2) + x - ((q - 2 / z ^ 3 - y) / (p + 1 / z ^ 2 - x)) ^ 2 / 4 =
      u + x + p + (8 * (p - x) + 4 * z ^ 2 * (p - x) ^ 2 - z ^ 4 * (q - y) ^ 2 + 4 * z * (q - y)) /
        (4 * (z ^ 2 * (p - x) + 1) ^ 2) := by
  have h1 : p + 1 / z ^ 2 - x = (z ^ 2 * (p - x) + 1) / z ^ 2 := by field_simp; ring
  have h2 : q - 2 / z ^ 3 - y = (z ^ 3 * (q - y) - 2) / z ^ 3 := by field_simp; ring
  rw [h1, h2]
  field_simp
  ring

lemma addDefect_algebra_neg (a b c n u z w : ℂ) (ht : z - -w ≠ 0) (hu : u ≠ 0) :
    (z - -w) * (a + 1 / (z + w) ^ 2 + b + c - (n / ((z - -w) * u)) ^ 2 / 4) =
      (z - -w) * a + (z - -w) * (b + c) + (4 * u ^ 2 - n ^ 2) / (z - -w) / (4 * u ^ 2) := by
  rw [sub_neg_eq_add] at ht ⊢
  field_simp
  ring

lemma analyticAt_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact hp.has_fpower_series_dslope_fslope.analyticAt

lemma exists_analyticAt_addDefect_zero {w : ℂ} (hw : w ∉ L.lattice) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 0 ∧ addDefect L w =ᶠ[𝓝[≠] 0] H := by
  have hP : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 := L.analyticAt_weierstrassPExcept 0
  have hP' : AnalyticAt ℂ ℘'[L - (0 : ℂ)] 0 := L.analyticAt_derivWeierstrassPExcept 0
  have hW : AnalyticAt ℂ (fun z ↦ ℘[L] (z + w)) 0 :=
    analyticAt_weierstrassP_comp_add (by simpa using hw)
  have hBf : AnalyticAt ℂ (fun z ↦ z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 1) 0 := by fun_prop
  have hBf0 : (fun z ↦ z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 1) 0 ≠ 0 := by simp
  refine ⟨fun z ↦ ℘[L] (z + w) + ℘[L] w + ℘[L - (0 : ℂ)] z +
      (8 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 4 * z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) ^ 2 -
        z ^ 4 * (℘'[L - (0 : ℂ)] z - ℘'[L] w) ^ 2 + 4 * z * (℘'[L - (0 : ℂ)] z - ℘'[L] w)) /
      (4 * (z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 1) ^ 2), ?_, ?_, ?_⟩
  · refine AnalyticAt.add (by fun_prop) (AnalyticAt.div (by fun_prop) (by fun_prop) ?_)
    simp
  · simp
    ring
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hBf.continuousAt.eventually_ne hBf0)] with z hz hBz
    have hz : z ≠ 0 := hz
    have e1 := weierstrassP_eq_except_zero (L := L) z
    have e2 := derivWeierstrassP_eq_except_zero (L := L) z
    simp only [addDefect, chordSlope]
    rw [e2, e1]
    exact addDefect_algebra_zero _ _ _ _ _ _ hz hBz

lemma exists_analyticAt_addDefect_self {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H w ∧ addDefect L w =ᶠ[𝓝[≠] w] H := by
  have hpw : AnalyticAt ℂ ℘[L] w := L.analyticOnNhd_weierstrassP w hw
  have hdw : AnalyticAt ℂ ℘'[L] w := L.analyticOnNhd_derivWeierstrassP w hw
  have h1 := analyticAt_dslope hpw
  have h2 := analyticAt_dslope hdw
  have hne : dslope ℘[L] w w ≠ 0 := by
    rw [dslope_same, L.deriv_weierstrassP]
    exact fun h ↦ h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  have hW := analyticAt_weierstrassP_comp_add (L := L) (x := w) (w := w) (by rwa [← two_mul])
  refine ⟨fun z ↦ ℘[L] (z + w) + ℘[L] z + ℘[L] w -
    (dslope ℘'[L] w z / dslope ℘[L] w z) ^ 2 / 4, ?_, ?_⟩
  · apply AnalyticAt.sub (by fun_prop)
    exact ((h2.div h1 hne).pow 2).div analyticAt_const (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [addDefect, chordSlope]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      div_div_div_cancel_right₀ (sub_ne_zero.2 hz)]

lemma neg_one_le_meromorphicOrderAt_addDefect_neg {w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (addDefect L w) (-w) := by
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hpw : AnalyticAt ℂ ℘[L] (-w) := L.analyticOnNhd_weierstrassP _ hw'
  have hdw : AnalyticAt ℂ ℘'[L] (-w) := L.analyticOnNhd_derivWeierstrassP _ hw'
  have hd0 : ℘'[L] w ≠ 0 := fun h ↦
    h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  set U := dslope ℘[L] (-w) with hU
  have hUa : AnalyticAt ℂ U (-w) := analyticAt_dslope hpw
  have hU0 : U (-w) = -℘'[L] w := by
    rw [hU, dslope_same, L.deriv_weierstrassP, L.derivWeierstrassP_neg]
  have hU0' : U (-w) ≠ 0 := by rw [hU0]; exact neg_ne_zero.2 hd0
  set M : ℂ → ℂ := fun z ↦ 4 * U z ^ 2 - (℘'[L] z - ℘'[L] w) ^ 2 with hM
  have hMa : AnalyticAt ℂ M (-w) := by simp only [hM]; fun_prop
  have hM0 : M (-w) = 0 := by simp only [hM, hU0, L.derivWeierstrassP_neg]; ring
  set M₁ := dslope M (-w) with hM₁
  have hM₁a : AnalyticAt ℂ M₁ (-w) := analyticAt_dslope hMa
  have hP0 : AnalyticAt ℂ (fun z ↦ ℘[L - (0 : ℂ)] (z + w)) (-w) := by
    have h : AnalyticAt ℂ ℘[L - (0 : ℂ)] (-w + w) := by
      rw [neg_add_cancel]
      exact L.analyticAt_weierstrassPExcept 0
    exact h.comp (g := ℘[L - (0 : ℂ)]) (f := fun z ↦ z + w) (by fun_prop)
  set H : ℂ → ℂ := fun z ↦ (z - -w) * ℘[L - (0 : ℂ)] (z + w) + (z - -w) * (℘[L] z + ℘[L] w) +
    M₁ z / (4 * U z ^ 2) with hH
  have hHa : AnalyticAt ℂ H (-w) := by
    simp only [hH]
    refine AnalyticAt.add (by fun_prop) (AnalyticAt.div hM₁a (by fun_prop) ?_)
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hU0')
  have hev : (fun z ↦ (z - -w) * addDefect L w z) =ᶠ[𝓝[≠] (-w)] H := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hUa.continuousAt.eventually_ne hU0')] with z hz hUz
    have ht : z - -w ≠ 0 := sub_ne_zero.2 hz
    have ht' : z + w ≠ 0 := by rwa [sub_neg_eq_add] at ht
    have eD : ℘[L] z - ℘[L] w = (z - -w) * U z := by
      have := sub_smul_dslope ℘[L] (-w) z
      rw [smul_eq_mul, L.weierstrassP_neg] at this
      rw [hU]
      exact this.symm
    have eM : M₁ z = (4 * U z ^ 2 - (℘'[L] z - ℘'[L] w) ^ 2) / (z - -w) := by
      have := sub_smul_dslope M (-w) z
      rw [smul_eq_mul, hM0, sub_zero] at this
      rw [eq_div_iff ht, mul_comm, hM₁, this]
    have e1 := weierstrassP_eq_except_zero (L := L) (z + w)
    simp only [addDefect, chordSlope, hH]
    rw [eD, eM, e1]
    exact addDefect_algebra_neg _ _ _ _ _ _ _ ht hUz
  have hord : 0 ≤ meromorphicOrderAt (fun z ↦ (z - -w) * addDefect L w z) (-w) := by
    rw [meromorphicOrderAt_congr hev]
    exact hHa.meromorphicOrderAt_nonneg
  rw [fun_meromorphicOrderAt_mul (by fun_prop) ((isEllipticFunction_addDefect w).1 _),
    meromorphicOrderAt_id_sub_const] at hord
  generalize meromorphicOrderAt (addDefect L w) (-w) = o at hord ⊢
  induction o with
  | top => exact le_top
  | coe n =>
    have : (0 : ℤ) ≤ 1 + n := by exact_mod_cast hord
    exact_mod_cast (by omega : (-1 : ℤ) ≤ n)

theorem weierstrassP_add_of_two_mul_notMem {z w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) (hz : z ∉ L.lattice) (hzw : z - w ∉ L.lattice)
    (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  have hE := isEllipticFunction_addDefect (L := L) w
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have ho : ∀ u, 0 ≤ meromorphicOrderAt (addDefect L w) u := by
    apply meromorphicOrderAt_nonneg_of_simple_pole hE
      (neg_one_le_meromorphicOrderAt_addDefect_neg hw h2w)
    intro u hu
    by_cases hu0 : u ∈ L.lattice
    · have := hE.2.meromorphicOrderAt_add hu0 0
      rw [zero_add] at this
      rw [this]
      obtain ⟨H, hH, -, hev⟩ := exists_analyticAt_addDefect_zero hw
      rw [meromorphicOrderAt_congr hev]
      exact hH.meromorphicOrderAt_nonneg
    by_cases hu1 : u - w ∈ L.lattice
    · have := hE.2.meromorphicOrderAt_add hu1 w
      rw [add_sub_cancel] at this
      rw [this]
      obtain ⟨H, hH, hev⟩ := exists_analyticAt_addDefect_self hw h2w
      rw [meromorphicOrderAt_congr hev]
      exact hH.meromorphicOrderAt_nonneg
    · exact (analyticAt_addDefect hw hu0 hu1
        (by rwa [sub_neg_eq_add] at hu)).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := exists_const_of_meromorphicOrderAt_nonneg L hE.1 hE.2 ho
  obtain ⟨H, hH, hH0, hev⟩ := exists_analyticAt_addDefect_zero (L := L) hw
  have hc0 : c = 0 := by
    have hgen : ∀ᶠ u in 𝓝[≠] (0 : ℂ), addDefect L w u = c := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
        nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
          (continuous_sub_right w)).mem_nhds (by simpa using hw')),
        nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
          (continuous_add_const w)).mem_nhds (by simpa using hw))] with u hu0 hu1 hu2 hu3
      exact hc u (analyticAt_addDefect hw (fun h ↦ hu1 ⟨h, hu0⟩) hu2 hu3)
    have := eq_of_eventuallyEq_nhdsNE hH.continuousAt continuousAt_const (hev.symm.trans hgen)
    rw [← this, hH0]
  have := hc z (analyticAt_addDefect hw hz hzw hzw')
  rw [hc0] at this
  simp only [addDefect] at this
  linear_combination this

lemma add_add_eq_zero_of_roots {g₂ g₃ x₁ x₂ x₃ : ℂ} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (f1 : 4 * x₁ ^ 3 - g₂ * x₁ - g₃ = 0) (f2 : 4 * x₂ ^ 3 - g₂ * x₂ - g₃ = 0)
    (f3 : 4 * x₃ ^ 3 - g₂ * x₃ - g₃ = 0) : x₁ + x₂ + x₃ = 0 := by
  have s12 : 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) = g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination f1 - f2)
  have s13 : 4 * (x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) = g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination f1 - f3)
  exact mul_left_cancel₀ (sub_ne_zero.2 h23) (by linear_combination (s12 - s13) / 4)

theorem weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  by_cases h2w : 2 * w ∈ L.lattice
  · by_cases h2z : 2 * z ∈ L.lattice
    · have d1 := derivWeierstrassP_eq_zero_of_two_mul_mem h2z
      have d2 := derivWeierstrassP_eq_zero_of_two_mul_mem h2w
      have root : ∀ u ∉ L.lattice, 2 * u ∈ L.lattice →
          4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
        rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
        ring
      have hne : ∀ {a b : ℂ}, a ∉ L.lattice → b ∉ L.lattice → a - b ∉ L.lattice →
          a + b ∉ L.lattice → ℘[L] a ≠ ℘[L] b := fun ha hb h1 h2 h ↦
        (sub_mem_or_add_mem_of_weierstrassP_eq ha hb h).elim h1 h2
      have nz : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
      have nw : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
      have a1 : z - (z + w) ∉ L.lattice := by rwa [show z - (z + w) = -w by ring]
      have a2 : z + (z + w) ∉ L.lattice := fun h ↦ hw (by
        have := sub_mem h h2z
        rwa [show z + (z + w) - 2 * z = w by ring] at this)
      have a3 : w - (z + w) ∉ L.lattice := by rwa [show w - (z + w) = -z by ring]
      have a4 : w + (z + w) ∉ L.lattice := fun h ↦ hz (by
        have := sub_mem h h2w
        rwa [show w + (z + w) - 2 * w = z by ring] at this)
      have hs := add_add_eq_zero_of_roots (hne hz hw hzw hzw') (hne hz hzw' a1 a2)
        (hne hw hzw' a3 a4) (root z hz h2z) (root w hw h2w)
        (root _ hzw' (by rw [mul_add]; exact add_mem h2z h2w))
      rw [chordSlope, d1, d2, sub_self, zero_div]
      linear_combination hs
    · have hwz : w - z ∉ L.lattice := fun h ↦ hzw (by simpa using neg_mem h)
      have := weierstrassP_add_of_two_mul_notMem hz h2z hw hwz (by rwa [add_comm])
      rw [add_comm, chordSlope_comm] at this
      linear_combination this
  · exact weierstrassP_add_of_two_mul_notMem hw h2w hz hzw hzw'

lemma derivAdd_algebra (x₁ x₂ y₁ y₂ g₂ g₃ : ℂ) (hD : x₁ - x₂ ≠ 0)
    (E₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (E₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ =
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) := by
  rw [← sub_eq_zero]
  have key : 2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ -
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) =
      (y₁ - y₂) / (4 * (x₁ - x₂) ^ 3) *
        ((y₂ ^ 2 - (4 * x₂ ^ 3 - g₂ * x₂ - g₃)) - (y₁ ^ 2 - (4 * x₁ ^ 3 - g₂ * x₁ - g₃))) := by
    field_simp
    ring
  rw [key, E₁, E₂]
  ring

theorem derivWeierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘'[L] (z + w) = -(chordSlope L z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have hopen : IsOpen {u : ℂ | u ∉ L.lattice ∧ u - w ∉ L.lattice ∧ u + w ∉ L.lattice} := by
    have h := L.isClosed_lattice.isOpen_compl
    exact h.inter ((h.preimage (continuous_sub_right w)).inter
      (h.preimage (continuous_add_const w)))
  have hne : ℘[L] z - ℘[L] w ≠ 0 := fun h ↦
    (sub_mem_or_add_mem_of_weierstrassP_eq hz hw (sub_eq_zero.1 h)).elim hzw hzw'
  have hL : HasDerivAt (fun u ↦ ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (hasDerivAt_weierstrassP hzw').comp_add_const z w
  have hp := hasDerivAt_weierstrassP hz
  have hd : HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
    rw [← deriv_derivWeierstrassP hz]
    exact hasDerivAt_derivWeierstrassP hz
  have hm : HasDerivAt (fun u ↦ chordSlope L u w)
      (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) - (℘'[L] z - ℘'[L] w) * ℘'[L] z) /
        (℘[L] z - ℘[L] w) ^ 2) z :=
    (hd.sub_const (℘'[L] w)).div (hp.sub_const (℘[L] w)) hne
  have hR : HasDerivAt (fun u ↦ chordSlope L u w ^ 2 / 4 - ℘[L] u - ℘[L] w)
      (2 * chordSlope L z w * (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) -
        (℘'[L] z - ℘'[L] w) * ℘'[L] z) / (℘[L] z - ℘[L] w) ^ 2) / 4 - ℘'[L] z) z :=
    ((((hm.pow 2).div_const 4).sub hp).sub_const (℘[L] w)).congr_deriv (by norm_num)
  have heq : (fun u ↦ ℘[L] (u + w)) =ᶠ[𝓝 z]
      (fun u ↦ chordSlope L u w ^ 2 / 4 - ℘[L] u - ℘[L] w) := by
    filter_upwards [hopen.mem_nhds ⟨hz, hzw, hzw'⟩] with u hu
    exact weierstrassP_add hu.1 hw hu.2.1 hu.2.2
  rw [hL.unique (hR.congr_of_eventuallyEq heq), weierstrassP_add hz hw hzw hzw']
  simp only [chordSlope]
  exact derivAdd_algebra _ _ _ _ _ _ hne (L.derivWeierstrassP_sq z hz) (L.derivWeierstrassP_sq w hw)

variable (L) in
def tangentSlope (L : PeriodPair) (w : ℂ) : ℂ := (6 * ℘[L] w ^ 2 - L.g₂ / 2) / ℘'[L] w

lemma exists_continuousAt_chordSlope {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ∃ s : ℂ → ℂ, ContinuousAt s w ∧ s w = tangentSlope L w ∧
      ∀ᶠ z in 𝓝[≠] w, z ∉ L.lattice ∧ z - w ∉ L.lattice ∧ z + w ∉ L.lattice ∧
        chordSlope L z w = s z := by
  have hpw : AnalyticAt ℂ ℘[L] w := L.analyticOnNhd_weierstrassP w hw
  have hdw : AnalyticAt ℂ ℘'[L] w := L.analyticOnNhd_derivWeierstrassP w hw
  have hne : dslope ℘[L] w w ≠ 0 := by
    rw [dslope_same, L.deriv_weierstrassP]
    exact fun h ↦ h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  refine ⟨fun z ↦ dslope ℘'[L] w z / dslope ℘[L] w z,
    ((analyticAt_dslope hdw).div (analyticAt_dslope hpw) hne).continuousAt, ?_, ?_⟩
  · simp only [dslope_same, L.deriv_weierstrassP, deriv_derivWeierstrassP hw, tangentSlope]
  · have h0 : (↑L.lattice \ {(0 : ℂ)})ᶜ ∈ 𝓝 (w - w) := by
      rw [sub_self]
      exact L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hw),
      nhdsWithin_le_nhds ((continuous_sub_right w).continuousAt.preimage_mem_nhds h0),
      nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
        (continuous_add_const w)).mem_nhds (show w + w ∉ L.lattice by rwa [← two_mul]))]
      with z hz h1 h2 h3
    have hz' : z - w ≠ 0 := sub_ne_zero.2 hz
    refine ⟨h1, fun h ↦ h2 ⟨h, hz'⟩, h3, ?_⟩
    simp only [chordSlope]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      div_div_div_cancel_right₀ hz']

theorem weierstrassP_two_mul {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘[L] (2 * w) = tangentSlope L w ^ 2 / 4 - 2 * ℘[L] w := by
  obtain ⟨s, hs, hsw, hev⟩ := exists_continuousAt_chordSlope hw h2w
  have hc : ContinuousAt (fun z ↦ ℘[L] (z + w)) w :=
    (analyticAt_weierstrassP_comp_add (show w + w ∉ L.lattice by rwa [← two_mul])).continuousAt
  have hg : ContinuousAt (fun z ↦ s z ^ 2 / 4 - ℘[L] z - ℘[L] w) w :=
    (((hs.pow 2).div_const 4).sub (L.analyticOnNhd_weierstrassP w hw).continuousAt).sub
      continuousAt_const
  have := eq_of_eventuallyEq_nhdsNE hc hg (hev.mono fun z ⟨h1, h2, h3, h4⟩ ↦ by
    simp only
    rw [weierstrassP_add h1 hw h2 h3, h4])
  simp only [hsw] at this
  rw [two_mul, this]
  ring

theorem derivWeierstrassP_two_mul {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘'[L] (2 * w) = -(tangentSlope L w * (℘[L] (2 * w) - ℘[L] w) + ℘'[L] w) := by
  obtain ⟨s, hs, hsw, hev⟩ := exists_continuousAt_chordSlope hw h2w
  have hww : w + w ∉ L.lattice := by rwa [← two_mul]
  have hc : ContinuousAt (fun z ↦ ℘'[L] (z + w)) w :=
    ((L.analyticOnNhd_derivWeierstrassP (w + w) hww).comp (g := ℘'[L]) (f := fun z ↦ z + w)
      (by fun_prop)).continuousAt
  have hc' : ContinuousAt (fun z ↦ ℘[L] (z + w)) w :=
    (analyticAt_weierstrassP_comp_add hww).continuousAt
  have hg : ContinuousAt (fun z ↦ -(s z * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z)) w :=
    ((hs.mul (hc'.sub (L.analyticOnNhd_weierstrassP w hw).continuousAt)).add
      (L.analyticOnNhd_derivWeierstrassP w hw).continuousAt).neg
  have := eq_of_eventuallyEq_nhdsNE hc hg (hev.mono fun z ⟨h1, h2, h3, h4⟩ ↦ by
    simp only
    rw [derivWeierstrassP_add h1 hw h2 h3, h4])
  simp only [hsw] at this
  rw [two_mul, this]
end

section
open Complex Filter Topology Set
open scoped PeriodPair

open WeierstrassCurve.Affine

variable {L : PeriodPair}

theorem exists_weierstrassP_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = c := by
  by_contra hcon
  push Not at hcon
  have h2 := finsum_toNat_torusOrder_weierstrassP_sub (L := L) c
  have h0 : ∀ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c)]
    by_cases hz : z ∈ L.lattice
    · have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
      have e : (fun w ↦ ℘[L] w - c) = ℘[L] + fun _ ↦ -c := by
        funext w
        simp [sub_eq_add_neg]
      have hlt : meromorphicOrderAt ℘[L] z < meromorphicOrderAt (fun _ : ℂ ↦ -c) z := by
        rw [L.order_weierstrassP z hz]
        exact lt_of_lt_of_le (by decide) analyticAt_const.meromorphicOrderAt_nonneg
      rw [e, meromorphicOrderAt_add_eq_left_of_lt hc hlt, L.order_weierstrassP z hz]
      rfl
    · have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
        (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
      have h0 : analyticOrderAt (fun w ↦ ℘[L] w - c) z = 0 :=
        ha.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (hcon z hz))
      rw [ha.meromorphicOrderAt_eq, h0]
      rfl
  simp [h0] at h2

variable (L) in
def toPoint (L : PeriodPair) (z : ℂ) : (weierstrassCurve L).toAffine.Point :=
  haveI := Classical.propDecidable (z ∈ L.lattice)
  if h : z ∈ L.lattice then 0 else
    .some (℘[L] z) (℘'[L] z / 2) (equation_iff_nonsingular.1 (equation_weierstrassP L h))

lemma toPoint_of_mem {z : ℂ} (h : z ∈ L.lattice) : toPoint L z = 0 := by
  rw [toPoint, dite_eq_left h]

lemma toPoint_of_notMem {z : ℂ} (h : z ∉ L.lattice) :
    toPoint L z = .some (℘[L] z) (℘'[L] z / 2)
      (equation_iff_nonsingular.1 (equation_weierstrassP L h)) := by
  rw [toPoint, dite_eq_right h]

lemma point_some_congr {x y x' y' : ℂ} {h : (weierstrassCurve L).toAffine.Nonsingular x y}
    {h' : (weierstrassCurve L).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl

@[simp]
lemma toPoint_zero : toPoint L 0 = 0 := toPoint_of_mem L.lattice.zero_mem

lemma toPoint_add_mem {z l : ℂ} (hl : l ∈ L.lattice) : toPoint L (z + l) = toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h hl)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hzl]
    exact point_some_congr (isPeriodic_weierstrassP z l hl)
      (by rw [isPeriodic_derivWeierstrassP z l hl])

lemma toPoint_eq_of_sub_mem {z w : ℂ} (h : z - w ∈ L.lattice) : toPoint L z = toPoint L w := by
  simpa using toPoint_add_mem (z := w) h

theorem toPoint_neg (z : ℂ) : toPoint L (-z) = -toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (neg_mem hz), neg_zero]
  · have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hz', Point.neg_some]
    refine point_some_congr (L.weierstrassP_neg z) ?_
    simp [negY, L.derivWeierstrassP_neg]
    ring

theorem toPoint_eq_zero_iff {z : ℂ} : toPoint L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h ↦ ?_, toPoint_of_mem⟩
  by_contra hz
  rw [toPoint_of_notMem hz] at h
  exact Point.some_ne_zero _ h

theorem toPoint_add (z w : ℂ) : toPoint L (z + w) = toPoint L z + toPoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, zero_add, add_comm, toPoint_add_mem hz]
  by_cases hw : w ∈ L.lattice
  · rw [toPoint_of_mem hw, add_zero, toPoint_add_mem hw]
  by_cases hzw' : z + w ∈ L.lattice
  · have : toPoint L w = toPoint L (-z) := toPoint_eq_of_sub_mem (by rwa [sub_neg_eq_add, add_comm])
    rw [toPoint_of_mem hzw', this, toPoint_neg, add_neg_cancel]
  by_cases hzw : z - w ∈ L.lattice
  ·
    have hwz : toPoint L w = toPoint L z := toPoint_eq_of_sub_mem (by simpa using neg_mem hzw)
    have h2 : toPoint L (z + w) = toPoint L (2 * z) :=
      toPoint_eq_of_sub_mem (by rw [show z + w - 2 * z = -(z - w) by ring]; exact neg_mem hzw)
    have h2z : 2 * z ∉ L.lattice := fun h ↦ hzw' (by
      rw [show z + w = 2 * z - (z - w) by ring]; exact sub_mem h hzw)
    have hd : ℘'[L] z ≠ 0 := fun h ↦ h2z ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hz).2 h)
    have hy : ℘'[L] z / 2 ≠ (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) := by
      simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero]
      intro h
      apply hd
      linear_combination h
    rw [h2, hwz, toPoint_of_notMem hz, toPoint_of_notMem h2z, Point.add_self_of_Y_ne hy]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2) =
        tangentSlope L z / 2 := by
      have hden : ℘'[L] z / 2 - (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) =
          ℘'[L] z := by
        simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
        ring
      rw [slope_of_Y_ne rfl hy, hden]
      simp only [tangentSlope, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₄]
      field_simp
      ring
    have hx : ℘[L] (2 * z) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] z)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2)) := by
      rw [hsl, weierstrassP_two_mul hz h2z]
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_two_mul hz h2z]
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring
  ·
    have hne : ℘[L] z ≠ ℘[L] w := fun h ↦
      (sub_mem_or_add_mem_of_weierstrassP_eq hz hw h).elim hzw hzw'
    rw [toPoint_of_notMem hz, toPoint_of_notMem hw, toPoint_of_notMem hzw',
      Point.add_of_X_ne hne]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        chordSlope L z w / 2 := by
      rw [slope_of_X_ne hne, chordSlope]
      ring
    have hx : ℘[L] (z + w) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] w)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) := by
      rw [hsl, weierstrassP_add hz hw hzw hzw']
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_add hz hw hzw hzw']
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring

theorem toPoint_surjective : Function.Surjective (toPoint L) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, toPoint_zero⟩
  obtain ⟨z, hz, hx⟩ := exists_weierstrassP_eq (L := L) x
  have hE := (weierstrassCurve_equation_iff L x y).1 h.1
  have hP := L.derivWeierstrassP_sq z hz
  rw [hx] at hP
  have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
  have hy : (y - ℘'[L] z / 2) * (y + ℘'[L] z / 2) = 0 := by linear_combination hE / 4 - hP / 4
  rcases mul_eq_zero.1 hy with h1 | h1
  · refine ⟨z, ?_⟩
    rw [toPoint_of_notMem hz]
    exact point_some_congr hx (by linear_combination -h1)
  · refine ⟨-z, ?_⟩
    rw [toPoint_of_notMem hz']
    exact point_some_congr (by rw [L.weierstrassP_neg, hx])
      (by rw [L.derivWeierstrassP_neg]; linear_combination -h1)

variable (L) in
def toPointHom (L : PeriodPair) : ℂ →+ (weierstrassCurve L).toAffine.Point where
  toFun := toPoint L
  map_zero' := toPoint_zero
  map_add' := toPoint_add

variable (L) in
def torusToPoint (L : PeriodPair) : Torus L →+ (weierstrassCurve L).toAffine.Point :=
  QuotientAddGroup.lift L.lattice.toAddSubgroup (toPointHom L) fun _ hl ↦ toPoint_of_mem hl

@[simp]
lemma torusToPoint_mk (z : ℂ) : torusToPoint L (Torus.mk L z) = toPoint L z := rfl

lemma torusToPoint_injective : Function.Injective (torusToPoint L) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
  rw [torusToPoint_mk, toPoint_eq_zero_iff] at hx
  exact (QuotientAddGroup.eq_zero_iff z).2 hx
end

end Elliptic
end GroundTheory.Global
