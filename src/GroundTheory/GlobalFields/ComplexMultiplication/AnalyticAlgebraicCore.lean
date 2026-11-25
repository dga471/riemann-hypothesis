module

public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialsAndBaseChange
public import GroundTheory.GlobalFields.ComplexMultiplication.EllipticUniformization
public import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionBase
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualWeil
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

@[expose] public section
noncomputable section
namespace GroundTheory.Global

section
namespace Elliptic
open _root_.Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular

theorem tendsto_E₄_atImInfty : Tendsto (fun τ : ℍ ↦ E₄ τ) atImInfty (𝓝 1) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (f := E₄) one_pos
    one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 E₄ 0 = 1 := by
    have := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    simpa [qExpansion_coeff] using this
  have hcomp : ∀ τ : ℍ, cuspFunction 1 E₄ (Function.Periodic.qParam 1 τ) = E₄ τ := fun τ ↦
    SlashInvariantFormClass.eq_cuspFunction E₄ τ one_mem_strictPeriods_SL one_ne_zero
  have := ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  rw [h0] at this
  exact this.congr hcomp

theorem tendsto_discriminant_atImInfty :
    Tendsto (fun τ : ℍ ↦ ModularForm.discriminant τ) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty

theorem eventually_le_norm_modularJ (R : ℝ) : ∀ᶠ τ in atImInfty, R ≤ ‖modularJ τ‖ := by
  have h1 : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) ≤ ‖E₄ τ‖ :=
    tendsto_E₄_atImInfty.norm.eventually (Ici_mem_nhds (by norm_num))
  have hc : (0 : ℝ) < 1 / (8 * (|R| + 1)) := by positivity
  have h2 : ∀ᶠ τ in atImInfty, ‖ModularForm.discriminant τ‖ < 1 / (8 * (|R| + 1)) :=
    tendsto_discriminant_atImInfty.norm.eventually (Iio_mem_nhds (by simpa using hc))
  filter_upwards [h1, h2] with τ h1 h2
  have hpos : 0 < ‖ModularForm.discriminant τ‖ :=
    norm_pos_iff.2 (ModularForm.discriminant_ne_zero τ)
  rw [modularJ, norm_div, norm_pow, le_div_iff₀ hpos]
  have hR : R ≤ |R| + 1 := by linarith [le_abs_self R]
  have h3 : (|R| + 1) * ‖ModularForm.discriminant τ‖ ≤ 1 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  have h4 : (1 / 2 : ℝ) ^ 3 ≤ ‖E₄ τ‖ ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  nlinarith

theorem exists_le_norm_modularJ (R : ℝ) : ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → R ≤ ‖modularJ τ‖ :=
  (atImInfty_mem _).1 (eventually_le_norm_modularJ R)

def modularJC (z : ℂ) : ℂ := modularJ (ofComplex z)

lemma modularJC_coe (τ : ℍ) : modularJC τ = modularJ τ := by
  rw [modularJC, ofComplex_apply]

lemma differentiableOn_modularJC : DifferentiableOn ℂ modularJC {z : ℂ | 0 < z.im} := by
  have h4 : DifferentiableOn ℂ ((fun τ : ℍ ↦ E₄ τ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo E₄)
  have hΔ : DifferentiableOn ℂ ((fun τ : ℍ ↦ ModularForm.discriminant τ) ∘ ofComplex)
      {z : ℂ | 0 < z.im} := by
    have := UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo CuspForm.discriminant)
    simpa [CuspForm.coe_discriminant] using this
  refine (h4.pow 3).div hΔ fun z _ ↦ ModularForm.discriminant_ne_zero _

lemma analyticOnNhd_modularJC : AnalyticOnNhd ℂ modularJC {z : ℂ | 0 < z.im} :=
  differentiableOn_modularJC.analyticOnNhd isOpen_upperHalfPlaneSet

lemma range_modularJ : range modularJ = modularJC '' {z : ℂ | 0 < z.im} := by
  ext w
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ, τ.im_pos, modularJC_coe τ⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ofComplex z, rfl⟩

lemma not_exists_modularJC_const : ¬ ∃ w, ∀ z ∈ {z : ℂ | 0 < z.im}, modularJC z = w := by
  rintro ⟨w, hw⟩
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  let τ : ℍ := ⟨(|A| + 1) * Complex.I, by simp; positivity⟩
  have hτ : A ≤ τ.im := by
    show A ≤ ((|A| + 1) * Complex.I).im
    simp
    linarith [le_abs_self A]
  have h1 := hA τ hτ
  rw [← modularJC_coe, hw _ τ.im_pos] at h1
  linarith

def fdBelow (A : ℝ) : Set ℂ :=
  {z | 1 ≤ normSq z ∧ |z.re| ≤ 1 / 2 ∧ 0 ≤ z.im ∧ z.im ≤ A}

lemma im_pos_of_mem_fdBelow {A : ℝ} {z : ℂ} (hz : z ∈ fdBelow A) : 0 < z.im := by
  obtain ⟨h1, h2, h3, -⟩ := hz
  rw [normSq_apply] at h1
  have hre : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.1 h2
    nlinarith
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [← h] at h1
    nlinarith

lemma isCompact_fdBelow (A : ℝ) : IsCompact (fdBelow A) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_normSq).inter
      ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |A|)).subset fun z hz ↦ ?_
    obtain ⟨-, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      _ ≤ 1 / 2 + |A| :=
        add_le_add h2 (by rw [abs_of_nonneg h3]; exact h4.trans (le_abs_self A))

lemma isOpen_range_modularJ : IsOpen (range modularJ) := by
  rw [range_modularJ]
  rcases analyticOnNhd_modularJC.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected with h | h
  · exact absurd h not_exists_modularJC_const
  · exact h _ subset_rfl isOpen_upperHalfPlaneSet

lemma isClosed_range_modularJ : IsClosed (range modularJ) := by
  refine closure_subset_iff_isClosed.1 fun w hw ↦ ?_
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  have hK : IsCompact (modularJC '' fdBelow A) :=
    (isCompact_fdBelow A).image_of_continuousOn
      (differentiableOn_modularJC.continuousOn.mono fun z hz ↦ im_pos_of_mem_fdBelow hz)
  have hsub : range modularJ ⊆ modularJC '' fdBelow A ∪ {y | ‖w‖ + 1 ≤ ‖y‖} := by
    rintro _ ⟨τ, rfl⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    rw [← modularJ_smul g τ]
    by_cases him : A ≤ (g • τ).im
    · exact Or.inr (hA _ him)
    · refine Or.inl ⟨(g • τ : ℍ), ⟨hg.1, hg.2, (g • τ).im_pos.le, ?_⟩, modularJC_coe _⟩
      exact (not_le.1 him).le
  have hclosed : IsClosed (modularJC '' fdBelow A ∪ {y : ℂ | ‖w‖ + 1 ≤ ‖y‖}) :=
    hK.isClosed.union (isClosed_le continuous_const continuous_norm)
  rcases closure_minimal hsub hclosed hw with h | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact ⟨ofComplex z, rfl⟩
  · have h' : ‖w‖ + 1 ≤ ‖w‖ := h
    linarith

theorem modularJ_surjective : Function.Surjective modularJ := by
  have h : range modularJ = univ :=
    IsClopen.eq_univ ⟨isClosed_range_modularJ, isOpen_range_modularJ⟩ (range_nonempty _)
  exact Set.range_eq_univ.1 h

theorem exists_variableChange_eq_weierstrassCurve_latticeOfTau (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ∃ τ : ℍ, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve (latticeOfTau τ) := by
  obtain ⟨τ, hτ⟩ := modularJ_surjective W.j
  refine ⟨τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [weierstrassCurve_latticeOfTau_j, hτ]

theorem exists_variableChange_eq_weierstrassCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve L := by
  obtain ⟨τ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve_latticeOfTau W
  exact ⟨latticeOfTau τ, C, hC⟩
end Elliptic
end

section
namespace Elliptic
open Filter Topology Set

theorem eventuallyEq_zero_codiscrete_iff {f : ℂ → ℂ} :
    f =ᶠ[codiscrete ℂ] 0 ↔ ∀ x, ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  change {z | f z = (0 : ℂ → ℂ) z} ∈ codiscreteWithin univ ↔ _
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp only [compl_univ, union_empty, mem_univ, true_implies, Pi.zero_apply]
  rfl

theorem eventuallyEq_zero_codiscrete_of_nhdsNE {f : ℂ → ℂ} (hf : Meromorphic f) {x : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] x, f z = 0) : f =ᶠ[codiscrete ℂ] 0 := by
  rw [eventuallyEq_zero_codiscrete_iff]
  intro u
  have hx : meromorphicOrderAt f x = ⊤ := meromorphicOrderAt_eq_top_iff.2 h
  by_contra hu
  have hu' : meromorphicOrderAt f u ≠ ⊤ := fun ht ↦ hu (meromorphicOrderAt_eq_top_iff.1 ht)
  exact (hf.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ u) (mem_univ x) hu' hx

theorem eventually_ne_zero_codiscrete {f : ℂ → ℂ} (hf : Meromorphic f)
    (h : ¬ f =ᶠ[codiscrete ℂ] 0) : ∀ᶠ z in codiscrete ℂ, f z ≠ 0 := by
  have hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ := fun u _ ht ↦
    h (eventuallyEq_zero_codiscrete_of_nhdsNE hf (meromorphicOrderAt_eq_top_iff.1 ht))
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
    (hf.meromorphicOn (s := univ)) hall

theorem nonempty_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) : S.Nonempty := by
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hS) 0 (mem_univ 0)
  rw [compl_univ, union_empty] at h
  exact Filter.nonempty_of_mem h

theorem isOpen_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) : IsOpen S :=
  (mem_codiscrete'.1 hS).1

theorem eventually_analyticAt {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∀ᶠ z in codiscrete ℂ, AnalyticAt ℂ f z :=
  (hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin

theorem deriv_eventuallyEq_codiscrete {f g : ℂ → ℂ} (h : f =ᶠ[codiscrete ℂ] g) :
    deriv f =ᶠ[codiscrete ℂ] deriv g := by
  have hS := isOpen_of_mem_codiscrete h
  filter_upwards [h] with z hz
  exact Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hS.mem_nhds hz) fun w hw ↦ hw)

def meroSubalgebra : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | Meromorphic f}
  mul_mem' hf hg := Meromorphic.mul hf hg
  add_mem' hf hg := Meromorphic.add hf hg
  algebraMap_mem' c := Meromorphic.const c

def meroNull : Ideal meroSubalgebra where
  carrier := {f | (f : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0}
  add_mem' {f g} hf hg := by
    change (fun z ↦ f.1 z + g.1 z) =ᶠ[codiscrete ℂ] 0
    filter_upwards [hf, hg] with z h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' := by
    change ((0 : meroSubalgebra) : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0
    exact Filter.EventuallyEq.rfl
  smul_mem' c f hf := by
    change (fun z ↦ c.1 z * f.1 z) =ᶠ[codiscrete ℂ] 0
    filter_upwards [hf] with z h
    simp only [Pi.zero_apply] at h ⊢
    rw [h, mul_zero]

theorem mem_meroNull {f : meroSubalgebra} : f ∈ meroNull ↔ (f : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0 :=
  Iff.rfl

instance meroNull_isMaximal : meroNull.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 ↦ ?_, fun J x hle hx hxJ ↦ ?_⟩
  · have h := (eventuallyEq_zero_codiscrete_iff.1 (mem_meroNull.1 h1)) 0
    obtain ⟨z, hz⟩ := h.exists
    exact one_ne_zero hz
  · have hf : Meromorphic (x : ℂ → ℂ) := x.2
    have hne := eventually_ne_zero_codiscrete hf hx
    let y : meroSubalgebra := ⟨(x : ℂ → ℂ)⁻¹, hf.inv⟩
    have hxy : x * y - 1 ∈ meroNull := by
      rw [mem_meroNull]
      change (fun z ↦ x.1 z * (x.1 z)⁻¹ - 1) =ᶠ[codiscrete ℂ] 0
      filter_upwards [hne] with z hz
      simp only [Pi.zero_apply]
      rw [mul_inv_cancel₀ hz, sub_self]
    have h1 : (1 : meroSubalgebra) = x * y - (x * y - 1) := by ring
    rw [h1]
    exact J.sub_mem (J.mul_mem_right y hxJ) (hle hxy)

abbrev MeroField : Type := meroSubalgebra ⧸ meroNull

noncomputable instance : Field MeroField := Ideal.Quotient.field _

noncomputable instance : DecidableEq MeroField := Classical.decEq _

open scoped Classical in
open Classical in
def germ (f : ℂ → ℂ) : MeroField :=
  if h : Meromorphic f then Ideal.Quotient.mk meroNull ⟨f, h⟩ else 0

theorem germ_of {f : ℂ → ℂ} (hf : Meromorphic f) : germ f = Ideal.Quotient.mk meroNull ⟨f, hf⟩ :=
  dite_eq_left hf

theorem germ_surjective (u : MeroField) : ∃ f : ℂ → ℂ, Meromorphic f ∧ germ f = u := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Ideal.Quotient.mk_surjective u
  exact ⟨f, hf, germ_of hf⟩

theorem germ_eq_germ_iff {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ f = germ g ↔ f =ᶠ[codiscrete ℂ] g := by
  rw [germ_of hf, germ_of hg, Ideal.Quotient.eq, mem_meroNull]
  change (f - g) =ᶠ[codiscrete ℂ] 0 ↔ _
  exact Filter.eventuallyEq_iff_sub.symm

theorem germ_congr {f g : ℂ → ℂ} (hf : Meromorphic f) (h : f =ᶠ[codiscrete ℂ] g) :
    germ f = germ g :=
  (germ_eq_germ_iff hf (hf.congr_codiscrete h)).2 h

theorem germ_eq_zero_iff {f : ℂ → ℂ} (hf : Meromorphic f) : germ f = 0 ↔ f =ᶠ[codiscrete ℂ] 0 := by
  rw [germ_of hf, Ideal.Quotient.eq_zero_iff_mem, mem_meroNull]

theorem germ_add {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f + g) = germ f + germ g := by
  rw [germ_of hf, germ_of hg, germ_of (hf.add hg), ← (Ideal.Quotient.mk meroNull).map_add]
  rfl

theorem germ_mul {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f * g) = germ f * germ g := by
  rw [germ_of hf, germ_of hg, germ_of (hf.mul hg), ← map_mul]
  rfl

theorem germ_neg {f : ℂ → ℂ} (hf : Meromorphic f) : germ (-f) = -germ f := by
  rw [germ_of hf, germ_of hf.neg, ← map_neg]
  rfl

theorem germ_sub {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f - g) = germ f - germ g := by
  rw [sub_eq_add_neg, germ_add hf hg.neg, germ_neg hg, ← sub_eq_add_neg]

theorem germ_const (c : ℂ) : germ (fun _ ↦ c) = algebraMap ℂ MeroField c := by
  rw [germ_of (Meromorphic.const c)]
  rfl

theorem germ_zero : germ (0 : ℂ → ℂ) = 0 := by
  have := germ_const 0
  rw [map_zero] at this
  exact this

theorem germ_one : germ (1 : ℂ → ℂ) = 1 := by
  have := germ_const 1
  rw [map_one] at this
  exact this

theorem germ_pow {f : ℂ → ℂ} (hf : Meromorphic f) (n : ℕ) : germ (f ^ n) = germ f ^ n := by
  rw [germ_of hf, germ_of (hf.pow (n := n)), ← map_pow]
  rfl

theorem germ_inv {f : ℂ → ℂ} (hf : Meromorphic f) : germ f⁻¹ = (germ f)⁻¹ := by
  by_cases h0 : f =ᶠ[codiscrete ℂ] 0
  · rw [(germ_eq_zero_iff hf).2 h0, inv_zero, germ_eq_zero_iff hf.inv]
    filter_upwards [h0] with z hz
    simp only [Pi.inv_apply, Pi.zero_apply] at hz ⊢
    rw [hz, inv_zero]
  · have hne := eventually_ne_zero_codiscrete hf h0
    have h1 : germ f * germ f⁻¹ = 1 := by
      rw [← germ_mul hf hf.inv, ← germ_one]
      apply germ_congr (hf.mul hf.inv)
      filter_upwards [hne] with z hz
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
      exact mul_inv_cancel₀ hz
    exact (eq_inv_of_mul_eq_one_right h1)

theorem germ_div {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f / g) = germ f / germ g := by
  rw [div_eq_mul_inv, germ_mul hf hg.inv, germ_inv hg, ← div_eq_mul_inv]

theorem comp_affine_eventuallyEq_zero {f : ℂ → ℂ} (h : f =ᶠ[codiscrete ℂ] 0) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : (fun z ↦ f (t * z + s)) =ᶠ[codiscrete ℂ] 0 := by
  rw [eventuallyEq_zero_codiscrete_iff] at h ⊢
  intro x
  have hc : Continuous fun z : ℂ ↦ t * z + s := by fun_prop
  have hmaps : MapsTo (fun z : ℂ ↦ t * z + s) {x}ᶜ {t * x + s}ᶜ := fun z hz hz' ↦ hz (by
    simp only [mem_singleton_iff, add_left_inj] at hz' ⊢
    exact mul_left_cancel₀ ht hz')
  exact (hc.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually (h _)

theorem meromorphic_comp_affine {f : ℂ → ℂ} (hf : Meromorphic f) (t s : ℂ) :
    Meromorphic fun z ↦ f (t * z + s) := fun x ↦
  (hf (t * x + s)).comp_analyticAt (g := fun z ↦ t * z + s) (by fun_prop)

def compAffineSub (t s : ℂ) : meroSubalgebra →ₐ[ℂ] meroSubalgebra where
  toFun f := ⟨fun z ↦ f.1 (t * z + s), meromorphic_comp_affine f.2 t s⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def affineComp (t s : ℂ) (ht : t ≠ 0) : MeroField →ₐ[ℂ] MeroField :=
  Ideal.Quotient.liftₐ meroNull ((Ideal.Quotient.mkₐ ℂ meroNull).comp (compAffineSub t s))
    fun f hf ↦ by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact comp_affine_eventuallyEq_zero hf ht s

theorem affineComp_germ (t s : ℂ) (ht : t ≠ 0) {f : ℂ → ℂ} (hf : Meromorphic f) :
    affineComp t s ht (germ f) = germ fun z ↦ f (t * z + s) := by
  rw [germ_of hf, germ_of (meromorphic_comp_affine hf t s)]
  rfl

def rep (u : MeroField) : ℂ → ℂ := (germ_surjective u).choose

theorem meromorphic_rep (u : MeroField) : Meromorphic (rep u) := (germ_surjective u).choose_spec.1

theorem germ_rep (u : MeroField) : germ (rep u) = u := (germ_surjective u).choose_spec.2

theorem rep_germ {f : ℂ → ℂ} (hf : Meromorphic f) : rep (germ f) =ᶠ[codiscrete ℂ] f :=
  (germ_eq_germ_iff (meromorphic_rep _) hf).1 (germ_rep _)

def derivFun (u : MeroField) : MeroField := germ (deriv (rep u))

theorem derivFun_germ {f : ℂ → ℂ} (hf : Meromorphic f) : derivFun (germ f) = germ (deriv f) :=
  germ_congr (meromorphic_rep _).deriv (deriv_eventuallyEq_codiscrete (rep_germ hf))

theorem derivFun_add (u v : MeroField) : derivFun (u + v) = derivFun u + derivFun v := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  obtain ⟨g, hg, rfl⟩ := germ_surjective v
  rw [← germ_add hf hg, derivFun_germ (hf.add hg), derivFun_germ hf, derivFun_germ hg,
    ← germ_add hf.deriv hg.deriv]
  apply germ_congr (hf.add hg).deriv
  filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2
  exact deriv_add h1.differentiableAt h2.differentiableAt

theorem derivFun_mul (u v : MeroField) :
    derivFun (u * v) = u * derivFun v + v * derivFun u := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  obtain ⟨g, hg, rfl⟩ := germ_surjective v
  rw [← germ_mul hf hg, derivFun_germ (hf.mul hg), derivFun_germ hf, derivFun_germ hg,
    ← germ_mul hf hg.deriv, ← germ_mul hg hf.deriv, ← germ_add (hf.mul hg.deriv) (hg.mul hf.deriv)]
  apply germ_congr (hf.mul hg).deriv
  filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2
  rw [deriv_mul h1.differentiableAt h2.differentiableAt]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

theorem derivFun_algebraMap (c : ℂ) : derivFun (algebraMap ℂ MeroField c) = 0 := by
  rw [← germ_const, derivFun_germ (Meromorphic.const c)]
  have : deriv (fun _ : ℂ ↦ c) = 0 := by
    funext z
    simp
  rw [this, germ_zero]

theorem derivFun_smul (c : ℂ) (u : MeroField) : derivFun (c • u) = c • derivFun u := by
  rw [Algebra.smul_def, derivFun_mul, derivFun_algebraMap, mul_zero, add_zero, Algebra.smul_def]

def germDeriv : Derivation ℂ MeroField MeroField :=
  Derivation.mk' { toFun := derivFun, map_add' := derivFun_add, map_smul' := derivFun_smul }
    fun u v ↦ by
      show derivFun (u * v) = u • derivFun v + v • derivFun u
      rw [derivFun_mul, smul_eq_mul, smul_eq_mul]

theorem germDeriv_germ {f : ℂ → ℂ} (hf : Meromorphic f) : germDeriv (germ f) = germ (deriv f) :=
  derivFun_germ hf

theorem exists_eq_algebraMap_of_germDeriv_eq_zero {u : MeroField} (hu : germDeriv u = 0) :
    ∃ c : ℂ, u = algebraMap ℂ MeroField c := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  rw [germDeriv_germ hf, germ_eq_zero_iff hf.deriv] at hu
  obtain ⟨x₀, hx₀⟩ := nonempty_of_mem_codiscrete (eventually_analyticAt hf)
  have hd : deriv f =ᶠ[𝓝 x₀] 0 := by
    have hne : ∀ᶠ z in 𝓝[≠] x₀, deriv f z = 0 := eventuallyEq_zero_codiscrete_iff.1 hu x₀
    have hcont : ContinuousAt (deriv f) x₀ := hx₀.deriv.continuousAt
    have h0 : deriv f x₀ = 0 := by
      have ht : Tendsto (deriv f) (𝓝[≠] x₀) (𝓝 (deriv f x₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hne' : deriv f =ᶠ[𝓝[≠] x₀] fun _ ↦ 0 := hne
      exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hne'.symm)
    rw [← nhdsNE_sup_pure x₀]
    exact ⟨hne, h0⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hx₀.eventually_analyticAt).and hd)
  have hconst : ∀ y ∈ Metric.ball x₀ ε, f x₀ = f y := fun y hy ↦
    (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball x₀ ε).isPreconnected
      (fun z hz ↦ (hball z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hball z hz).2) (Metric.mem_ball_self hε) hy
  refine ⟨f x₀, ?_⟩
  rw [← germ_const, germ_eq_germ_iff hf (Meromorphic.const _), Filter.eventuallyEq_iff_sub]
  apply eventuallyEq_zero_codiscrete_of_nhdsNE (hf.sub (Meromorphic.const _)) (x := x₀)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hε)] with z hz
  simp only [Pi.sub_apply]
  rw [← hconst z hz, sub_self]
end Elliptic
end

section
namespace Elliptic
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped PeriodPair

theorem mem_meroSubalgebra {f : ℂ → ℂ} : f ∈ meroSubalgebra ↔ Meromorphic f := Iff.rfl

def mero (f : ℂ → ℂ) (hf : Meromorphic f) : meroSubalgebra := ⟨f, mem_meroSubalgebra.2 hf⟩

@[simp] theorem coe_mero (f : ℂ → ℂ) (hf : Meromorphic f) : (mero f hf : ℂ → ℂ) = f := rfl

theorem mkₐ_eq_germ {f : ℂ → ℂ} (hf : Meromorphic f) :
    Ideal.Quotient.mkₐ ℂ meroNull (mero f hf) = germ f :=
  (germ_of hf).symm

theorem mkₐ_eq_zero_iff (a : meroSubalgebra) :
    Ideal.Quotient.mkₐ ℂ meroNull a = 0 ↔ (a : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0 := by
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem mkₐ_eq_mkₐ_iff (a b : meroSubalgebra) :
    Ideal.Quotient.mkₐ ℂ meroNull a = Ideal.Quotient.mkₐ ℂ meroNull b ↔
      (a : ℂ → ℂ) =ᶠ[codiscrete ℂ] b := by
  rw [← sub_eq_zero, ← map_sub, mkₐ_eq_zero_iff]
  exact (Filter.eventuallyEq_iff_sub (f := (a : ℂ → ℂ)) (g := b)).symm

theorem preimage_affine_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : (fun z ↦ t * z + s) ⁻¹' S ∈ codiscrete ℂ := by
  have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hS
  rw [codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x _
  have hc : Continuous fun z : ℂ ↦ t * z + s := by fun_prop
  have hmaps : MapsTo (fun z : ℂ ↦ t * z + s) {x}ᶜ {t * x + s}ᶜ := fun z hz hz' ↦ hz (by
    simp only [mem_singleton_iff, add_left_inj] at hz' ⊢
    exact mul_left_cancel₀ ht hz')
  have := (hc.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps) (h _ (mem_univ _))
  rw [compl_univ, union_empty] at this ⊢
  exact this

theorem eventually_affine {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : ∀ᶠ z in codiscrete ℂ, p (t * z + s) :=
  preimage_affine_mem_codiscrete h ht s

theorem eventually_notMem_lattice (L : PeriodPair) : ∀ᶠ z in codiscrete ℂ, z ∉ L.lattice := by
  filter_upwards [eventually_analyticAt L.meromorphic_weierstrassP] with z hz hzL
  have h := hz.meromorphicOrderAt_nonneg
  rw [L.order_weierstrassP z hzL] at h
  exact absurd h (by decide)

theorem meromorphic_eval_comp {f : ℂ → ℂ} (hf : Meromorphic f) (p : ℂ[X]) :
    Meromorphic fun z ↦ p.eval (f z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact fun x ↦ (hp x).add (hq x)
  | monomial n a =>
    simp only [eval_monomial]
    exact fun x ↦ (MeromorphicAt.const a x).mul ((hf x).pow n)

theorem germ_aeval {f : ℂ → ℂ} (hf : Meromorphic f) (p : ℂ[X]) :
    aeval (germ f) p = germ fun z ↦ p.eval (f z) := by
  have hp := meromorphic_eval_comp hf p
  rw [← mkₐ_eq_germ hf, ← mkₐ_eq_germ hp, Polynomial.aeval_algHom_apply]
  congr 1
  apply Subtype.ext
  rw [← Subalgebra.aeval_coe]
  funext z
  rw [Polynomial.aeval_fn_apply]
  simp [Polynomial.aeval_def, Polynomial.eval₂_id]

theorem ne_algebraMap_of_transcendental {u : MeroField} (hu : Transcendental ℂ u) (c : ℂ) :
    u ≠ algebraMap ℂ MeroField c := by
  rintro rfl
  exact hu (isAlgebraic_algebraMap c)

section Points

variable {W : WeierstrassCurve ℂ}

theorem equation_germ {x y : ℂ → ℂ} (hx : Meromorphic x) (hy : Meromorphic y)
    (h : ∀ᶠ z in codiscrete ℂ, W.toAffine.Equation (x z) (y z)) :
    (W.baseChange MeroField).toAffine.Equation (germ x) (germ y) := by
  set X : meroSubalgebra := mero x hx
  set Y : meroSubalgebra := mero y hy
  have key : Ideal.Quotient.mkₐ ℂ meroNull (Y ^ 2 + algebraMap ℂ _ W.a₁ * X * Y +
      algebraMap ℂ _ W.a₃ * Y - (X ^ 3 + algebraMap ℂ _ W.a₂ * X ^ 2 + algebraMap ℂ _ W.a₄ * X +
      algebraMap ℂ _ W.a₆)) = 0 := by
    rw [mkₐ_eq_zero_iff]
    filter_upwards [h] with z hz
    rw [equation_iff] at hz
    simp only [Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow,
      Subalgebra.coe_algebraMap, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, X, Y, coe_mero]
    linear_combination hz
  rw [← mkₐ_eq_germ hx, ← mkₐ_eq_germ hy, equation_iff]
  simp only [map_sub, map_add (f := _), map_mul, map_pow, AlgHom.commutes] at key
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  linear_combination key

theorem coords_of_add_some {x₁ y₁ x₂ y₂ x₃ y₃ : ℂ} {k₁ : W.toAffine.Nonsingular x₁ y₁}
    {k₂ : W.toAffine.Nonsingular x₂ y₂} {k₃ : W.toAffine.Nonsingular x₃ y₃} (hx : x₁ ≠ x₂)
    (h : Point.some x₁ y₁ k₁ + Point.some x₂ y₂ k₂ = Point.some x₃ y₃ k₃) :
    x₃ = W.toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂)) ∧
      y₃ = W.toAffine.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂)) := by
  rw [Point.add_some (fun h ↦ hx h.1), Point.some.injEq, slope_of_X_ne hx] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem add_some_germ {x₁ y₁ x₂ y₂ x₃ y₃ : ℂ → ℂ} (m₁ : Meromorphic x₁) (n₁ : Meromorphic y₁)
    (m₂ : Meromorphic x₂) (n₂ : Meromorphic y₂) (m₃ : Meromorphic x₃) (n₃ : Meromorphic y₃)
    {h₁ : (W.baseChange MeroField).toAffine.Nonsingular (germ x₁) (germ y₁)}
    {h₂ : (W.baseChange MeroField).toAffine.Nonsingular (germ x₂) (germ y₂)}
    {h₃ : (W.baseChange MeroField).toAffine.Nonsingular (germ x₃) (germ y₃)}
    (hx : germ x₁ ≠ germ x₂)
    (hpt : ∀ᶠ z in codiscrete ℂ, ∃ (k₁ : W.toAffine.Nonsingular (x₁ z) (y₁ z))
      (k₂ : W.toAffine.Nonsingular (x₂ z) (y₂ z)) (k₃ : W.toAffine.Nonsingular (x₃ z) (y₃ z)),
      Point.some _ _ k₁ + Point.some _ _ k₂ = Point.some _ _ k₃) :
    Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h₃ := by
  have hne : ∀ᶠ z in codiscrete ℂ, x₁ z - x₂ z ≠ 0 := by
    refine eventually_ne_zero_codiscrete (m₁.sub m₂) fun h ↦ hx ?_
    rw [germ_eq_germ_iff m₁ m₂, Filter.eventuallyEq_iff_sub]
    exact h
  set ℓ : ℂ → ℂ := fun z ↦ (y₁ z - y₂ z) / (x₁ z - x₂ z)
  have mℓ : Meromorphic ℓ := (n₁.sub n₂).div (m₁.sub m₂)
  have hℓ : germ ℓ = (germ y₁ - germ y₂) / (germ x₁ - germ x₂) := by
    rw [← germ_sub n₁ n₂, ← germ_sub m₁ m₂, ← germ_div (n₁.sub n₂) (m₁.sub m₂)]
    rfl
  have hxy : ¬(germ x₁ = germ x₂ ∧ germ y₁ = (W.baseChange MeroField).toAffine.negY (germ x₂) (germ y₂)) :=
    fun h ↦ hx h.1
  rw [Point.add_some hxy, Point.some.injEq, slope_of_X_ne hx, ← hℓ, ← mkₐ_eq_germ m₁,
    ← mkₐ_eq_germ m₂, ← mkₐ_eq_germ n₁, ← mkₐ_eq_germ mℓ, ← mkₐ_eq_germ m₃, ← mkₐ_eq_germ n₃]
  have e := baseChange_addX (W' := W) (Ideal.Quotient.mkₐ ℂ meroNull) (x₁ := mero x₁ m₁)
    (x₂ := mero x₂ m₂) (ℓ := mero ℓ mℓ)
  have e' := baseChange_addY (W' := W) (Ideal.Quotient.mkₐ ℂ meroNull) (x₁ := mero x₁ m₁)
    (x₂ := mero x₂ m₂) (y₁ := mero y₁ n₁) (ℓ := mero ℓ mℓ)
  rw [e, e', mkₐ_eq_mkₐ_iff, mkₐ_eq_mkₐ_iff]
  constructor
  · filter_upwards [hpt, hne] with z ⟨k₁, k₂, k₃, hz⟩ hz'
    obtain ⟨h1, -⟩ := coords_of_add_some (sub_ne_zero.1 hz') hz
    rw [coe_mero, h1]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ℓ, coe_mero]
  · filter_upwards [hpt, hne] with z ⟨k₁, k₂, k₃, hz⟩ hz'
    obtain ⟨-, h2⟩ := coords_of_add_some (sub_ne_zero.1 hz') hz
    rw [coe_mero, h2]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg,
      Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.neg_apply, Pi.pow_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ℓ, coe_mero]

end Points

section Lattice

variable (L : PeriodPair)

theorem meromorphic_weierstrassP_affine (t s : ℂ) : Meromorphic fun z ↦ ℘[L] (t * z + s) :=
  meromorphic_comp_affine L.meromorphic_weierstrassP t s

theorem meromorphic_derivWeierstrassP_half : Meromorphic fun z ↦ ℘'[L] z / 2 :=
  fun x ↦ (L.meromorphic_derivWeierstrassP x).div (MeromorphicAt.const 2 x)

theorem meromorphic_derivWeierstrassP_half_affine (t s : ℂ) :
    Meromorphic fun z ↦ ℘'[L] (t * z + s) / 2 :=
  meromorphic_comp_affine (meromorphic_derivWeierstrassP_half L) t s

theorem equation_affine (t s : ℂ) (ht : t ≠ 0) :
    ((weierstrassCurve L).baseChange MeroField).toAffine.Equation
      (germ fun z ↦ ℘[L] (t * z + s)) (germ fun z ↦ ℘'[L] (t * z + s) / 2) :=
  equation_germ (meromorphic_weierstrassP_affine L t s)
    (meromorphic_derivWeierstrassP_half_affine L t s) (by
      filter_upwards [eventually_affine (eventually_notMem_lattice L) ht s] with z hz
      exact equation_weierstrassP L hz)

theorem equation_base :
    ((weierstrassCurve L).baseChange MeroField).toAffine.Equation
      (germ ℘[L]) (germ fun z ↦ ℘'[L] z / 2) := by
  have h := equation_affine L 1 0 one_ne_zero
  simp only [one_mul, add_zero] at h
  exact h

def basePoint : ((weierstrassCurve L).baseChange MeroField).toAffine.Point :=
  .some _ _ (equation_iff_nonsingular.1 (equation_base L))

def affinePoint (t s : ℂ) (ht : t ≠ 0) : ((weierstrassCurve L).baseChange MeroField).toAffine.Point :=
  .some _ _ (equation_iff_nonsingular.1 (equation_affine L t s ht))

theorem map_affineComp_basePoint (t s : ℂ) (ht : t ≠ 0) :
    Point.map (affineComp t s ht) (basePoint L) = affinePoint L t s ht := by
  simp only [basePoint, affinePoint, Point.map_some, Point.some.injEq]
  exact ⟨affineComp_germ t s ht L.meromorphic_weierstrassP,
    affineComp_germ t s ht (meromorphic_derivWeierstrassP_half L)⟩

theorem map_affineComp_affinePoint (t s t' s' : ℂ) (ht : t ≠ 0) (ht' : t' ≠ 0) :
    Point.map (affineComp t' s' ht') (affinePoint L t s ht) =
      affinePoint L (t * t') (t * s' + s) (mul_ne_zero ht ht') := by
  simp only [affinePoint, Point.map_some, Point.some.injEq]
  rw [affineComp_germ t' s' ht' (meromorphic_weierstrassP_affine L t s),
    affineComp_germ t' s' ht' (meromorphic_derivWeierstrassP_half_affine L t s)]
  have e : ∀ z : ℂ, t * (t' * z + s') + s = t * t' * z + (t * s' + s) := fun z ↦ by ring
  simp only [e, and_self]

theorem transcendental_germ_weierstrassP : Transcendental ℂ (germ ℘[L]) := by
  rintro ⟨p, hp0, hp⟩
  rw [germ_aeval L.meromorphic_weierstrassP,
    germ_eq_zero_iff (meromorphic_eval_comp L.meromorphic_weierstrassP p)] at hp
  obtain ⟨z, h1, h2⟩ := nonempty_of_mem_codiscrete
    (hp.and (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) hp0))
  exact h2 (by simpa using h1)

theorem transcendental_germ_weierstrassP_affine (t s : ℂ) (ht : t ≠ 0) :
    Transcendental ℂ (germ fun z ↦ ℘[L] (t * z + s)) := by
  rw [← affineComp_germ t s ht L.meromorphic_weierstrassP]
  intro h
  exact transcendental_germ_weierstrassP L
    ((isAlgebraic_algHom_iff (affineComp t s ht) (affineComp t s ht).toRingHom.injective).1 h)

theorem affinePoint_add {t₁ s₁ t₂ s₂ : ℂ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₃ : t₁ + t₂ ≠ 0)
    (hx : (germ fun z ↦ ℘[L] (t₁ * z + s₁)) ≠ germ fun z ↦ ℘[L] (t₂ * z + s₂)) :
    affinePoint L t₁ s₁ h₁ + affinePoint L t₂ s₂ h₂ = affinePoint L (t₁ + t₂) (s₁ + s₂) h₃ := by
  apply add_some_germ (meromorphic_weierstrassP_affine L _ _)
    (meromorphic_derivWeierstrassP_half_affine L _ _) (meromorphic_weierstrassP_affine L _ _)
    (meromorphic_derivWeierstrassP_half_affine L _ _) (meromorphic_weierstrassP_affine L _ _)
    (meromorphic_derivWeierstrassP_half_affine L _ _) hx
  filter_upwards [eventually_affine (eventually_notMem_lattice L) h₁ s₁,
    eventually_affine (eventually_notMem_lattice L) h₂ s₂,
    eventually_affine (eventually_notMem_lattice L) h₃ (s₁ + s₂)] with z hz1 hz2 hz3
  have e : t₁ * z + s₁ + (t₂ * z + s₂) = (t₁ + t₂) * z + (s₁ + s₂) := by ring
  refine ⟨equation_iff_nonsingular.1 (equation_weierstrassP L hz1),
    equation_iff_nonsingular.1 (equation_weierstrassP L hz2),
    equation_iff_nonsingular.1 (equation_weierstrassP L hz3), ?_⟩
  have h := toPoint_add (L := L) (t₁ * z + s₁) (t₂ * z + s₂)
  rw [toPoint_of_notMem hz1, toPoint_of_notMem hz2, e, toPoint_of_notMem hz3] at h
  exact h.symm

theorem affinePoint_add_constMap (t s c : ℂ) (ht : t ≠ 0) :
    affinePoint L t s ht + constMap (weierstrassCurve L) MeroField (toPoint L c) =
      affinePoint L t (s + c) ht := by
  by_cases hc : c ∈ L.lattice
  · rw [toPoint_of_mem hc, map_zero, add_zero]
    simp only [affinePoint, Point.some.injEq]
    have e : ∀ z : ℂ, t * z + (s + c) = t * z + s + c := fun z ↦ by ring
    simp only [e, isPeriodic_weierstrassP _ c hc, isPeriodic_derivWeierstrassP _ c hc, and_self]
  · have hcp : constMap (weierstrassCurve L) MeroField (toPoint L c) =
        .some (germ fun _ ↦ ℘[L] c) (germ fun _ ↦ ℘'[L] c / 2)
          (equation_iff_nonsingular.1 (equation_germ (Meromorphic.const _) (Meromorphic.const _)
            (Eventually.of_forall fun _ ↦ equation_weierstrassP L hc))) := by
      rw [toPoint_of_notMem hc]
      show Point.some _ _ _ = Point.some _ _ _
      rw [Point.some.injEq]
      exact ⟨(germ_const _).symm, (germ_const _).symm⟩
    rw [hcp]
    apply add_some_germ (meromorphic_weierstrassP_affine L _ _)
      (meromorphic_derivWeierstrassP_half_affine L _ _) (Meromorphic.const _) (Meromorphic.const _)
      (meromorphic_weierstrassP_affine L _ _) (meromorphic_derivWeierstrassP_half_affine L _ _)
    · rw [germ_const]
      exact ne_algebraMap_of_transcendental (transcendental_germ_weierstrassP_affine L t s ht) _
    filter_upwards [eventually_affine (eventually_notMem_lattice L) ht s,
      eventually_affine (eventually_notMem_lattice L) ht (s + c)] with z hz1 hz3
    have e : t * z + s + c = t * z + (s + c) := by ring
    refine ⟨equation_iff_nonsingular.1 (equation_weierstrassP L hz1),
      equation_iff_nonsingular.1 (equation_weierstrassP L hc),
      equation_iff_nonsingular.1 (equation_weierstrassP L hz3), ?_⟩
    have h := toPoint_add (L := L) (t * z + s) c
    rw [toPoint_of_notMem hz1, toPoint_of_notMem hc, e, toPoint_of_notMem hz3] at h
    exact h.symm

def ellEval : (weierstrassCurve L).toAffine.FunctionField →ₐ[ℂ] MeroField :=
  liftPoint (weierstrassCurve L) (equation_base L) (transcendental_germ_weierstrassP L)

theorem ellEval_genX : ellEval L (genX (weierstrassCurve L)) = germ ℘[L] :=
  liftPoint_genX _ _ _

theorem ellEval_genY : ellEval L (genY (weierstrassCurve L)) = germ fun z ↦ ℘'[L] z / 2 :=
  liftPoint_genY _ _ _

theorem ellEval_injective : Function.Injective (ellEval L) := (ellEval L).toRingHom.injective

theorem map_ellEval_genericPoint :
    Point.map (ellEval L) (genericPoint (weierstrassCurve L)) = basePoint L :=
  map_liftPoint_genericPoint _ _ _

theorem isEllipticFunction_derivWeierstrassP_half : IsEllipticFunction L fun z ↦ ℘'[L] z / 2 :=
  ⟨meromorphic_derivWeierstrassP_half L, fun z l hl ↦ by
    simp only [isPeriodic_derivWeierstrassP z l hl]⟩

theorem exists_isEllipticFunction_ellEval_eq (a : (weierstrassCurve L).toAffine.FunctionField) :
    ∃ f, IsEllipticFunction L f ∧ ellEval L a = germ f := by
  let S : IntermediateField ℂ (weierstrassCurve L).toAffine.FunctionField :=
    { carrier := {a | ∃ f, IsEllipticFunction L f ∧ ellEval L a = germ f}
      mul_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        refine ⟨f * g, ⟨hf.1.mul hg.1, fun z l hl ↦ ?_⟩, ?_⟩
        · simp only [Pi.mul_apply, hf.2 z l hl, hg.2 z l hl]
        · rw [map_mul, ha, hb, germ_mul hf.1 hg.1]
      one_mem' := ⟨fun _ ↦ 1, ⟨Meromorphic.const 1, fun _ _ _ ↦ rfl⟩, by
        rw [map_one, germ_const, map_one]⟩
      add_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        refine ⟨f + g, ⟨hf.1.add hg.1, fun z l hl ↦ ?_⟩, ?_⟩
        · simp only [Pi.add_apply, hf.2 z l hl, hg.2 z l hl]
        · rw [map_add (f := _), ha, hb, germ_add hf.1 hg.1]
      zero_mem' := ⟨fun _ ↦ 0, ⟨Meromorphic.const 0, fun _ _ _ ↦ rfl⟩, by
        rw [map_zero, germ_const, map_zero]⟩
      algebraMap_mem' := fun c ↦ ⟨fun _ ↦ c, ⟨Meromorphic.const c, fun _ _ _ ↦ rfl⟩, by
        rw [AlgHom.commutes, germ_const]⟩
      inv_mem' := by
        rintro a ⟨f, hf, ha⟩
        refine ⟨f⁻¹, ⟨hf.1.inv, fun z l hl ↦ ?_⟩, ?_⟩
        · simp only [Pi.inv_apply, hf.2 z l hl]
        · rw [map_inv₀, ha, germ_inv hf.1] }
  have hX : genX (weierstrassCurve L) ∈ S :=
    ⟨℘[L], isEllipticFunction_weierstrassP (L := L), ellEval_genX L⟩
  have hY : genY (weierstrassCurve L) ∈ S :=
    ⟨_, isEllipticFunction_derivWeierstrassP_half L, ellEval_genY L⟩
  have hle : IntermediateField.adjoin ℂ {genX (weierstrassCurve L), genY (weierstrassCurve L)} ≤ S := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with rfl | rfl
    · exact hX
    · exact hY
  rw [adjoin_genX_genY] at hle
  exact hle IntermediateField.mem_top

theorem exists_ellEval_eq_germ {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∃ a, ellEval L a = germ f := by
  obtain ⟨P, Q, R, S, hQ, hS, heq⟩ := exists_rational_weierstrassP hf
  have m℘ := L.meromorphic_weierstrassP
  have md := L.meromorphic_derivWeierstrassP
  have mP := meromorphic_eval_comp m℘ P
  have mQ := meromorphic_eval_comp m℘ Q
  have mR := meromorphic_eval_comp m℘ R
  have mS := meromorphic_eval_comp m℘ S
  have h2 : (2 : MeroField) * germ (fun z ↦ ℘'[L] z / 2) = germ ℘'[L] := by
    rw [show (fun z ↦ ℘'[L] z / 2) = ℘'[L] / fun _ ↦ (2 : ℂ) from rfl,
      germ_div md (Meromorphic.const 2), germ_const, map_ofNat]
    have h2ne : (2 : MeroField) ≠ 0 := by
      rw [← map_ofNat (algebraMap ℂ MeroField) 2]
      exact (_root_.map_ne_zero _).2 two_ne_zero
    exact mul_div_cancel₀ _ h2ne
  refine ⟨aeval (genX (weierstrassCurve L)) P / aeval (genX (weierstrassCurve L)) Q +
    2 * genY (weierstrassCurve L) * (aeval (genX (weierstrassCurve L)) R /
      aeval (genX (weierstrassCurve L)) S), ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_div₀, map_div₀, map_ofNat, ← aeval_algHom_apply,
    ← aeval_algHom_apply, ← aeval_algHom_apply, ← aeval_algHom_apply, ellEval_genX, ellEval_genY,
    h2, germ_aeval m℘ P, germ_aeval m℘ Q, germ_aeval m℘ R, germ_aeval m℘ S, ← germ_div mP mQ,
    ← germ_div mR mS, ← germ_mul md (mR.div mS), ← germ_add (mP.div mQ) (md.mul (mR.div mS))]
  exact (germ_congr hf.1 heq).symm

end Lattice
end Elliptic
end

section
namespace Elliptic
open Filter Topology Set Polynomial
open scoped PeriodPair

theorem meromorphicAt_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

theorem germ_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i, Meromorphic (f i)) :
    germ (fun z ↦ ∑ i ∈ s, f i z) = ∑ i ∈ s, germ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [germ_const, map_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : Meromorphic fun z ↦ ∑ i ∈ s, f i z := fun x ↦
      meromorphicAt_fun_sum s fun i ↦ hf i x
    rw [← ih]
    exact germ_add (hf a) hs

theorem lt_meromorphicOrderAt_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) {c : ℤ}
    (hc : ∀ i ∈ s, (c : WithTop ℤ) < meromorphicOrderAt (f i) x) :
    (c : WithTop ℤ) < meromorphicOrderAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ ↦ rfl)]
    exact WithTop.coe_lt_top c
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := meromorphicAt_fun_sum s hf
    have h1 := hc a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    exact lt_of_lt_of_le (lt_min h1 h2) (meromorphicOrderAt_add (hf a) hs)

theorem exists_int_of_real_mul_mem (L : PeriodPair) {r : ℝ} (h : (r : ℂ) * L.ω₁ ∈ L.lattice) :
    ∃ a : ℤ, r = a := by
  obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
  have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - r) (n : ℝ) (by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_intCast]
    linear_combination e)
  exact ⟨m, (sub_eq_zero.1 this.1).symm⟩

theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.2 two_pos).ne'

theorem injective_mk_div_sqrt_two (L : PeriodPair) :
    Function.Injective fun m : ℕ ↦ Torus.mk L ((m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ)) := by
  intro m m' hm
  simp only at hm
  rw [Torus.mk_eq_mk_iff] at hm
  have e : (m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) - (m' : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) =
      ((((m : ℝ) - m') / Real.sqrt 2 : ℝ) : ℂ) * L.ω₁ := by
    push_cast
    ring
  rw [e] at hm
  obtain ⟨a, ha⟩ := exists_int_of_real_mul_mem L hm
  by_contra hne
  have hd : ((m : ℝ) - m') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  have ha0 : (a : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    exact hd ((div_eq_zero_iff.1 ha).resolve_right (Real.sqrt_pos.2 two_pos).ne')
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have hs : Real.sqrt 2 = ((m : ℝ) - m') / a := by
    rw [eq_div_iff ha0]
    rw [div_eq_iff hs2] at ha
    linear_combination (-1 : ℝ) * ha
  exact irrational_sqrt_two ⟨((m : ℚ) - m') / a, by push_cast; exact hs.symm⟩

theorem meromorphicOrderAt_weierstrassP_sqrt_two (L : PeriodPair) {z₀ : ℂ}
    (hz : (Real.sqrt 2 : ℂ) * z₀ + 0 ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) z₀ = -2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ := by fun_prop
  have hd : deriv (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ ≠ 0 := by
    have h1 := ((hasDerivAt_id' z₀).const_mul (Real.sqrt 2 : ℂ)).add_const 0
    rw [h1.deriv, mul_one]
    exact sqrt_two_ne_zero
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd
  rw [Function.comp_def] at this
  rw [this, L.order_weierstrassP _ hz]

theorem ellEval_indep (L : PeriodPair) (p : (weierstrassCurve L).toAffine.FunctionField[X])
    (hp : p ≠ 0) :
    (p.map (ellEval L).toRingHom).eval (germ fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) ≠ 0 := by
  set t : ℂ := (Real.sqrt 2 : ℂ)
  set h : ℂ → ℂ := fun z ↦ ℘[L] (t * z + 0)
  have mh : Meromorphic h := meromorphic_weierstrassP_affine L t 0
  choose f hf hfe using fun i ↦ exists_isEllipticFunction_ellEval_eq L (p.coeff i)
  set n := p.natDegree
  have mt : ∀ i, Meromorphic fun z ↦ f i z * h z ^ i := fun i x ↦
    ((hf i).1 x).mul ((mh x).pow i)
  have heval : (p.map (ellEval L).toRingHom).eval (germ h) =
      germ fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i := by
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective (ellEval_injective L),
      germ_sum _ mt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map, show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      germ_mul (hf i).1 (mh.pow (n := i)), germ_pow mh]
    congr 1
    exact hfe i
  intro h0
  rw [heval, germ_eq_zero_iff (fun x ↦ meromorphicAt_fun_sum _ fun i ↦ mt i x)] at h0

  have hfn : ¬ f n =ᶠ[codiscrete ℂ] 0 := by
    intro hz
    have h1 : ellEval L (p.coeff n) = 0 := by
      rw [hfe n, ← germ_zero]
      exact germ_congr (hf n).1 hz
    rw [map_eq_zero_iff _ (ellEval_injective L)] at h1
    exact hp (leadingCoeff_eq_zero.1 h1)

  set bad : Set ℂ := (⋃ i ∈ Finset.range (n + 1), singularSet (f i)) ∪ singularSet (f n)⁻¹
  have hbad : (Torus.mk L '' bad).Finite := by
    rw [image_union, image_iUnion₂]
    refine Finite.union (Finite.biUnion (Finset.finite_toSet _) fun i _ ↦
      finite_image_singularSet L (hf i).1 (hf i).2) ?_
    exact finite_image_singularSet L (hf n).1.inv fun z l hl ↦ by
      simp only [Pi.inv_apply, (hf n).2 z l hl]
  obtain ⟨m, hm⟩ := (hbad.preimage (injective_mk_div_sqrt_two L).injOn).infinite_compl.nonempty
  set z₀ : ℂ := (m : ℂ) * L.ω₁ / t
  have hz₀ : z₀ ∉ bad := fun hb ↦ hm ⟨z₀, hb, rfl⟩
  have hpole : t * z₀ + 0 ∈ L.lattice := by
    have : t * z₀ + 0 = (m : ℤ) • L.ω₁ := by
      simp only [z₀, t, add_zero, zsmul_eq_mul, Int.cast_natCast]
      field_simp [sqrt_two_ne_zero]
    rw [this]
    exact L.lattice.smul_mem (m : ℤ) L.ω₁_mem_lattice
  have han : ∀ i ∈ Finset.range (n + 1), AnalyticAt ℂ (f i) z₀ := fun i hi ↦ by
    by_contra hna
    exact hz₀ (Or.inl (mem_iUnion₂.2 ⟨i, hi, hna⟩))
  have haninv : AnalyticAt ℂ (f n)⁻¹ z₀ := by
    by_contra hna
    exact hz₀ (Or.inr hna)
  have hoh : meromorphicOrderAt h z₀ = -2 := meromorphicOrderAt_weierstrassP_sqrt_two L hpole
  have hon : meromorphicOrderAt (f n) z₀ = 0 := by
    have h1 := (han n (Finset.self_mem_range_succ n)).meromorphicOrderAt_nonneg
    have h2 := haninv.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_inv] at h2
    have hne : meromorphicOrderAt (f n) z₀ ≠ ⊤ := fun ht ↦
      hfn (eventuallyEq_zero_codiscrete_of_nhdsNE (hf n).1 (meromorphicOrderAt_eq_top_iff.1 ht))
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hk] at h1 h2 ⊢
    have : (0 : ℤ) ≤ k := by exact_mod_cast h1
    have : (0 : ℤ) ≤ -k := by exact_mod_cast h2
    have : k = 0 := by omega
    rw [this]
    rfl
  have hterm : ∀ i, meromorphicOrderAt (fun z ↦ f i z * h z ^ i) z₀ =
      meromorphicOrderAt (f i) z₀ + ((i * (-2) : ℤ) : WithTop ℤ) := fun i ↦ by
    rw [show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      meromorphicOrderAt_mul ((hf i).1 z₀) ((mh z₀).pow i), meromorphicOrderAt_pow (mh z₀), hoh]
    congr 1
  have htop : meromorphicOrderAt (fun z ↦ f n z * h z ^ n) z₀ = ((-2 * n : ℤ) : WithTop ℤ) := by
    rw [hterm, hon, zero_add]
    congr 1
    ring
  have hrest : ((-2 * n : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i) z₀ := by
    apply lt_meromorphicOrderAt_sum _ (fun i ↦ mt i z₀)
    intro i hi
    rw [hterm]
    have hi' : i < n := Finset.mem_range.1 hi
    have h0 := (han i (Finset.mem_range.2 (by omega))).meromorphicOrderAt_nonneg
    cases hc : meromorphicOrderAt (f i) z₀ with
    | top =>
      rw [top_add]
      exact WithTop.coe_lt_top _
    | coe k =>
      rw [hc] at h0
      have : (0 : ℤ) ≤ k := by exact_mod_cast h0
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      omega
  have hsum : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ =
      ((-2 * n : ℤ) : WithTop ℤ) := by
    have e : (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) =
        (fun z ↦ f n z * h z ^ n) + fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i := by
      funext z
      simp only [Finset.sum_range_succ, Pi.add_apply]
      ring
    rw [e, meromorphicOrderAt_add_eq_left_of_lt (meromorphicAt_fun_sum _ fun i ↦ mt i z₀)
      (htop ▸ hrest), htop]
  have hzero : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (eventuallyEq_zero_codiscrete_iff.1 h0 z₀)
  rw [hsum] at hzero
  exact WithTop.coe_ne_top hzero
end Elliptic
end

section
open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in
theorem exists_univField_algHom {M : Type*} [Field M] [Algebra F M] [DecidableEq M]
    (σ : E.toAffine.FunctionField →ₐ[F] M) {u v : M}
    (h : (E.baseChange M).toAffine.Nonsingular u v)
    (hu : ∀ p : E.toAffine.FunctionField[X], p ≠ 0 → (p.map σ.toRingHom).eval u ≠ 0) :
    ∃ τ : univField E →ₐ[F] M,
      τ.comp (IsScalarTower.toAlgHom F E.toAffine.FunctionField (univField E)) = σ ∧
        τ (genX (E.baseChange E.toAffine.FunctionField)) = u ∧
          τ (genY (E.baseChange E.toAffine.FunctionField)) = v := by
  let _ : Algebra E.toAffine.FunctionField M := σ.toRingHom.toAlgebra
  have hc : ∀ a : F, algebraMap E.toAffine.FunctionField M (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F M a := fun a ↦ σ.commutes a
  have hEq : ((E.baseChange E.toAffine.FunctionField).baseChange M).toAffine.Equation u v := by
    have e := (equation_iff _ _).1 h.1
    rw [equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e ⊢
    rw [hc, hc, hc, hc, hc]
    exact e
  have htr : Transcendental E.toAffine.FunctionField u := by
    rintro ⟨p, hp0, hp⟩
    apply hu p hp0
    rw [eval_map]
    exact hp
  let τ := liftPoint (E.baseChange E.toAffine.FunctionField) hEq htr
  have _ : IsScalarTower F E.toAffine.FunctionField M :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (σ.commutes c).symm
  refine ⟨τ.restrictScalars F, AlgHom.ext fun a ↦ ?_, ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom']
    exact τ.commutes a
  · rw [AlgHom.restrictScalars_apply]
    exact liftPoint_genX _ _ _
  · rw [AlgHom.restrictScalars_apply]
    exact liftPoint_genY _ _ _

theorem univAdd_of_pair (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {M : Type*} [Field M] [Algebra F M] [DecidableEq M] (σ : E.toAffine.FunctionField →ₐ[F] M)
    {u v : M} (h : (E.baseChange M).toAffine.Nonsingular u v)
    (hu : ∀ p : E.toAffine.FunctionField[X], p ≠ 0 → (p.map σ.toRingHom).eval u ≠ 0)
    (hA : IsGenPt E (Point.map σ (genericPoint E))) (hB : IsGenPt E (Point.some u v h))
    (hAB : IsGenPt E (Point.map σ (genericPoint E) + Point.some u v h))
    (hQ : Point.map (genEval E _ hAB) Q =
      Point.map (genEval E _ hA) Q + Point.map (genEval E _ hB) Q) : UnivAdd Q := by
  obtain ⟨τ, hτ, hu', hv'⟩ := exists_univField_algHom σ h hu
  have c₁ : Point.map τ (univPt₁ E) = Point.map σ (genericPoint E) := by
    rw [univPt₁, Point.map_map, hτ]
  have c₂ : Point.map τ (univPt₂ E) = Point.some u v h := by
    rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]
    exact ⟨hu', hv'⟩
  apply Point.map_injective τ
  rw [map_add (f := _), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E)),
    genEval_congr E (by rw [map_add (f := _), c₁, c₂]) _ hAB, genEval_congr E c₁ _ hA,
    genEval_congr E c₂ _ hB]
  exact hQ
end

section
namespace Elliptic
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

variable (L₁ L₂ : PeriodPair)

def latticeHom : AddSubgroup ℂ where
  carrier := {α | ∀ l ∈ L₁.lattice, α * l ∈ L₂.lattice}
  add_mem' {a b} ha hb l hl := by
    rw [add_mul]
    exact add_mem (ha l hl) (hb l hl)
  zero_mem' l _ := by
    rw [zero_mul]
    exact zero_mem _
  neg_mem' {a} ha l hl := by
    rw [neg_mul]
    exact neg_mem (ha l hl)

variable {L₁ L₂}

theorem mem_latticeHom {α : ℂ} : α ∈ latticeHom L₁ L₂ ↔ ∀ l ∈ L₁.lattice, α * l ∈ L₂.lattice :=
  Iff.rfl

theorem meromorphicOrderAt_weierstrassP_affine (L : PeriodPair) {t s z₀ : ℂ} (ht : t ≠ 0)
    (hz : t * z₀ + s ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] (t * z + s)) z₀ = -2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ t * z + s) z₀ := by fun_prop
  have hd : deriv (fun z : ℂ ↦ t * z + s) z₀ ≠ 0 := by
    have h1 := ((hasDerivAt_id' z₀).const_mul t).add_const s
    rw [h1.deriv, mul_one]
    exact ht
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd
  rw [Function.comp_def] at this
  rw [this, L.order_weierstrassP _ hz]

theorem germ_weierstrassP_ne (L : PeriodPair) {a b z₀ : ℂ} (ha : a ≠ 0)
    (h₁ : a * z₀ + 0 ∈ L.lattice) (h₂ : b * z₀ + 0 ∉ L.lattice) :
    (germ fun z ↦ ℘[L] (a * z + 0)) ≠ germ fun z ↦ ℘[L] (b * z + 0) := by
  intro h
  rw [germ_eq_germ_iff (meromorphic_weierstrassP_affine L a 0)
    (meromorphic_weierstrassP_affine L b 0)] at h
  have hne := (meromorphic_weierstrassP_affine L a 0 z₀).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
    (meromorphic_weierstrassP_affine L b 0 z₀) (mem_univ z₀) (by
      rw [accPt_iff_frequently_nhdsNE]
      exact Eventually.frequently (Eventually.of_forall fun _ ↦ mem_univ _)) h
  have h1 := meromorphicOrderAt_weierstrassP_affine L ha h₁
  rw [meromorphicOrderAt_congr hne] at h1
  have hf : AnalyticAt ℂ (fun z : ℂ ↦ b * z + 0) z₀ := by fun_prop
  have han : AnalyticAt ℂ (fun z ↦ ℘[L] (b * z + 0)) z₀ := by
    have h3 := AnalyticAt.comp (f := fun z : ℂ ↦ b * z + 0) (g := ℘[L])
      (L.analyticOnNhd_weierstrassP (b * z₀ + 0) h₂) hf
    exact h3
  have h0 := han.meromorphicOrderAt_nonneg
  rw [h1] at h0
  exact absurd h0 (by decide)

theorem sqrt_two_mul_notMem (L : PeriodPair) : (Real.sqrt 2 : ℂ) * L.ω₁ ∉ L.lattice := by
  intro h
  obtain ⟨a, ha⟩ := exists_int_of_real_mul_mem L h
  exact irrational_sqrt_two ⟨a, by push_cast; exact ha.symm⟩

theorem one_add_sqrt_two_ne_zero : (1 : ℂ) + Real.sqrt 2 ≠ 0 := by
  have : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  exact_mod_cast this.ne'

theorem affinePoint_congr (L : PeriodPair) {t t' s s' : ℂ} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (e₁ : t = t') (e₂ : s = s') : affinePoint L t s ht = affinePoint L t' s' ht' := by
  subst e₁ e₂
  rfl

theorem basePoint_eq (L : PeriodPair) : basePoint L = affinePoint L 1 0 one_ne_zero := by
  simp only [basePoint, affinePoint, one_mul, add_zero]

theorem isGenPt_affinePoint (L : PeriodPair) (t s : ℂ) (ht : t ≠ 0) :
    IsGenPt (weierstrassCurve L) (affinePoint L t s ht) :=
  transcendental_germ_weierstrassP_affine L t s ht

theorem genEval_affinePoint (L : PeriodPair) (s : ℂ) (hs : s ≠ 0)
    (h : IsGenPt (weierstrassCurve L) (affinePoint L s 0 hs)) :
    genEval (weierstrassCurve L) (affinePoint L s 0 hs) h = (affineComp s 0 hs).comp (ellEval L) := by
  refine (eq_genEval (weierstrassCurve L) _ ?_ h).symm
  rw [← Point.map_map, map_ellEval_genericPoint, map_affineComp_basePoint]

theorem isGenPt_of_map' {F : Type*} [Field F] {E : WeierstrassCurve F} {M N : Type*} [Field M]
    [Algebra F M] [DecidableEq M] [Field N] [Algebra F N] [DecidableEq N] (τ : M →ₐ[F] N)
    {A : (E.baseChange M).toAffine.Point} (h : IsGenPt E (Point.map τ A)) : IsGenPt E A := by
  cases A with
  | zero => exact h.elim
  | some x y k =>
    rw [Point.map_some, isGenPt_some] at h
    rw [isGenPt_some]
    exact fun halg ↦ h (halg.algHom τ)

theorem map_genEval_congr {F : Type*} [Field F] {E E' : WeierstrassCurve F} {M : Type*} [Field M]
    [Algebra F M] [DecidableEq M] (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {P P' : (E.baseChange M).toAffine.Point} (e : P = P') (h : IsGenPt E P) (h' : IsGenPt E P') :
    Point.map (genEval E P h) Q = Point.map (genEval E P' h') Q := by
  subst e
  rfl

theorem isEllipticFunction_weierstrassP_mul {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    IsEllipticFunction L₁ fun z ↦ ℘[L₂] (α * z + 0) := by
  refine ⟨meromorphic_weierstrassP_affine L₂ α 0, fun z l hl ↦ ?_⟩
  show ℘[L₂] (α * (z + l) + 0) = ℘[L₂] (α * z + 0)
  rw [show α * (z + l) + 0 = (α * z + 0) + α * l by ring]
  exact isPeriodic_weierstrassP _ _ (hα l hl)

theorem isEllipticFunction_derivWeierstrassP_mul_half {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    IsEllipticFunction L₁ fun z ↦ ℘'[L₂] (α * z + 0) / 2 := by
  refine ⟨meromorphic_derivWeierstrassP_half_affine L₂ α 0, fun z l hl ↦ ?_⟩
  show ℘'[L₂] (α * (z + l) + 0) / 2 = ℘'[L₂] (α * z + 0) / 2
  rw [show α * (z + l) + 0 = (α * z + 0) + α * l by ring]
  simp only [isPeriodic_derivWeierstrassP _ _ (hα l hl)]

def isogX {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) : (weierstrassCurve L₁).toAffine.FunctionField :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_weierstrassP_mul hα)).choose

def isogY {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) : (weierstrassCurve L₁).toAffine.FunctionField :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_derivWeierstrassP_mul_half hα)).choose

theorem ellEval_isogX {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    ellEval L₁ (isogX hα) = germ fun z ↦ ℘[L₂] (α * z + 0) :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_weierstrassP_mul hα)).choose_spec

theorem ellEval_isogY {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    ellEval L₁ (isogY hα) = germ fun z ↦ ℘'[L₂] (α * z + 0) / 2 :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_derivWeierstrassP_mul_half hα)).choose_spec

theorem nonsingular_isog {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    ((weierstrassCurve L₂).baseChange (weierstrassCurve L₁).toAffine.FunctionField).toAffine.Nonsingular
      (isogX hα) (isogY hα) := by
  rw [← (weierstrassCurve L₂).toAffine.baseChange_nonsingular (ellEval_injective L₁),
    ellEval_isogX, ellEval_isogY]
  exact equation_iff_nonsingular.1 (equation_affine L₂ α 0 h0)

def isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    ((weierstrassCurve L₂).baseChange (weierstrassCurve L₁).toAffine.FunctionField).toAffine.Point :=
  .some _ _ (nonsingular_isog hα h0)

theorem map_ellEval_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    Point.map (ellEval L₁) (isogPt hα h0) = affinePoint L₂ α 0 h0 := by
  simp only [isogPt, affinePoint, Point.map_some, Point.some.injEq]
  exact ⟨ellEval_isogX hα, ellEval_isogY hα⟩

theorem isGenPt_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    IsGenPt (weierstrassCurve L₂) (isogPt hα h0) := by
  apply isGenPt_of_map' (ellEval L₁)
  rw [map_ellEval_isogPt]
  exact isGenPt_affinePoint L₂ α 0 h0

theorem value_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) (s : ℂ) (hs : s ≠ 0)
    (h : IsGenPt (weierstrassCurve L₁) (affinePoint L₁ s 0 hs)) :
    Point.map (genEval (weierstrassCurve L₁) (affinePoint L₁ s 0 hs) h) (isogPt hα h0) =
      affinePoint L₂ (α * s) 0 (mul_ne_zero h0 hs) := by
  rw [genEval_affinePoint L₁ s hs h, ← Point.map_map, map_ellEval_isogPt,
    map_affineComp_affinePoint]
  exact affinePoint_congr L₂ _ _ rfl (by ring)

theorem respectsAdd_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    RespectsAdd (weierstrassCurve L₁) (weierstrassCurve L₂) (isogPt hα h0) := by
  set r : ℂ := (Real.sqrt 2 : ℂ)
  have hr : r ≠ 0 := sqrt_two_ne_zero
  have hA := isGenPt_map_genericPoint (weierstrassCurve L₁) (ellEval L₁)
  have eA : Point.map (ellEval L₁) (genericPoint (weierstrassCurve L₁)) =
      affinePoint L₁ 1 0 one_ne_zero := by
    rw [map_ellEval_genericPoint, basePoint_eq]
  have hx₁ : (germ fun z ↦ ℘[L₁] (1 * z + 0)) ≠ germ fun z ↦ ℘[L₁] (r * z + 0) :=
    germ_weierstrassP_ne L₁ one_ne_zero (z₀ := L₁.ω₁) (by simpa using L₁.ω₁_mem_lattice)
      (by simpa using sqrt_two_mul_notMem L₁)
  have eAB : affinePoint L₁ 1 0 one_ne_zero + affinePoint L₁ r 0 hr =
      affinePoint L₁ (1 + r) 0 one_add_sqrt_two_ne_zero := by
    rw [affinePoint_add L₁ one_ne_zero hr one_add_sqrt_two_ne_zero hx₁]
    exact affinePoint_congr L₁ _ _ rfl (by ring)
  apply respectsAdd_of_univAdd
  refine univAdd_of_pair (isogPt hα h0) (ellEval L₁)
    (equation_iff_nonsingular.1 (equation_affine L₁ r 0 hr)) (ellEval_indep L₁) hA
    (isGenPt_affinePoint L₁ r 0 hr) (by
      change IsGenPt _ (Point.map (ellEval L₁) (genericPoint _) + affinePoint L₁ r 0 hr)
      rw [eA, eAB]
      exact isGenPt_affinePoint L₁ _ 0 _) ?_
  have eS : Point.map (ellEval L₁) (genericPoint (weierstrassCurve L₁)) + affinePoint L₁ r 0 hr =
      affinePoint L₁ (1 + r) 0 one_add_sqrt_two_ne_zero := by
    rw [eA, eAB]
  have hx₂ : (germ fun z ↦ ℘[L₂] (α * 1 * z + 0)) ≠ germ fun z ↦ ℘[L₂] (α * r * z + 0) := by
    refine germ_weierstrassP_ne L₂ (mul_ne_zero h0 one_ne_zero) (z₀ := L₂.ω₁ / α) ?_ ?_
    · rw [show α * 1 * (L₂.ω₁ / α) + 0 = L₂.ω₁ by field_simp; ring]
      exact L₂.ω₁_mem_lattice
    · rw [show α * r * (L₂.ω₁ / α) + 0 = r * L₂.ω₁ by field_simp; ring]
      exact sqrt_two_mul_notMem L₂
  have key : affinePoint L₂ (α * (1 + r)) 0 (mul_ne_zero h0 one_add_sqrt_two_ne_zero) =
      affinePoint L₂ (α * 1) 0 (mul_ne_zero h0 one_ne_zero) +
        affinePoint L₂ (α * r) 0 (mul_ne_zero h0 hr) := by
    rw [affinePoint_add L₂ _ _ (by rw [← mul_add]; exact mul_ne_zero h0 one_add_sqrt_two_ne_zero)
      hx₂]
    exact affinePoint_congr L₂ _ _ (by ring) (by ring)
  have v1 := value_isogPt hα h0 1 one_ne_zero (isGenPt_affinePoint L₁ 1 0 one_ne_zero)
  have vr := value_isogPt hα h0 r hr (isGenPt_affinePoint L₁ r 0 hr)
  have vs := value_isogPt hα h0 (1 + r) one_add_sqrt_two_ne_zero
    (isGenPt_affinePoint L₁ _ 0 one_add_sqrt_two_ne_zero)
  refine (map_genEval_congr _ eS _ (isGenPt_affinePoint L₁ _ 0 one_add_sqrt_two_ne_zero)).trans ?_
  refine vs.trans (key.trans ?_)
  have vA := map_genEval_congr (isogPt hα h0) eA.symm
    (isGenPt_affinePoint L₁ 1 0 one_ne_zero) hA
  exact congrArg₂ (· + ·) (v1.symm.trans vA) vr.symm

def latticeIsog {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    Isogeny (weierstrassCurve L₁) (weierstrassCurve L₂) :=
  ⟨isogPt hα h0, (isIsogeny_iff _).2 ⟨isGenPt_isogPt hα h0, respectsAdd_isogPt hα h0⟩⟩

open Classical in
def latticeToHom (α : latticeHom L₁ L₂) : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂) :=
  if h : (α : ℂ) = 0 then 0 else (latticeIsog α.2 h).toHom

theorem latticeToHom_of_ne_zero (α : latticeHom L₁ L₂) (h : (α : ℂ) ≠ 0) :
    (latticeToHom α).1 = isogPt α.2 h := by
  rw [latticeToHom, dite_eq_right h]
  rfl

theorem latticeToHom_of_eq_zero (α : latticeHom L₁ L₂) (h : (α : ℂ) = 0) : latticeToHom α = 0 := by
  rw [latticeToHom, dite_eq_left h]

def omegaDeriv : KaehlerDifferential ℂ MeroField →ₗ[MeroField] MeroField := germDeriv.liftKaehlerDifferential

theorem omegaDeriv_D (u : MeroField) : omegaDeriv (D ℂ MeroField u) = germDeriv u :=
  germDeriv.liftKaehlerDifferential_comp_D u

theorem two_mul_germ_half {f : ℂ → ℂ} (hf : Meromorphic f) :
    (2 : MeroField) * germ (fun z ↦ f z / 2) = germ f := by
  rw [show (fun z ↦ f z / 2) = f / fun _ ↦ (2 : ℂ) from rfl, germ_div hf (Meromorphic.const 2),
    germ_const, map_ofNat]
  have h2ne : (2 : MeroField) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ MeroField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  exact mul_div_cancel₀ _ h2ne

theorem germ_derivWeierstrassP_half_ne_zero (L : PeriodPair) (t s : ℂ) (ht : t ≠ 0) :
    (germ fun z ↦ ℘'[L] (t * z + s) / 2) ≠ 0 := by
  intro h
  have e := (equation_iff _ _).1 (equation_affine L t s ht)
  rw [h] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆, map_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] at e
  apply transcendental_germ_weierstrassP_affine L t s ht
  refine ⟨X ^ 3 + C (-(L.g₂ / 4)) * X + C (-(L.g₃ / 4)), ?_, ?_⟩
  · apply_fun (fun p ↦ p.coeff 3)
    simp
  · simp only [map_add (f := _), map_pow, aeval_X, map_mul, aeval_C]
    linear_combination -e

theorem omegaDeriv_affinePoint (L : PeriodPair) (t s : ℂ) (ht : t ≠ 0) :
    omegaDeriv (omegaAt (weierstrassCurve L) (affinePoint L t s ht)) = algebraMap ℂ MeroField t := by
  obtain ⟨s₁, -⟩ := omegaAt_some_spec (weierstrassCurve L)
    (equation_iff_nonsingular.1 (equation_affine L t s ht))
  have e := congrArg omegaDeriv s₁
  rw [LinearMap.map_smul, omegaDeriv_D, germDeriv_germ (meromorphic_weierstrassP_affine L t s)] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    weierstrassCurve_a₁, weierstrassCurve_a₃, map_zero, zero_mul, add_zero, smul_eq_mul] at e
  have hd : deriv (fun z ↦ ℘[L] (t * z + s)) =ᶠ[codiscrete ℂ] fun z ↦ t * ℘'[L] (t * z + s) := by
    filter_upwards [eventually_affine (eventually_notMem_lattice L) ht s] with z hz
    have h1 := (hasDerivAt_weierstrassP hz).comp z (((hasDerivAt_id' z).const_mul t).add_const s)
    rw [mul_one] at h1
    rw [show (fun z ↦ ℘[L] (t * z + s)) = ℘[L] ∘ fun x ↦ t * x + s from rfl, h1.deriv, mul_comm]
  have md : Meromorphic fun z ↦ t * ℘'[L] (t * z + s) := fun x ↦
    (MeromorphicAt.const t x).mul (meromorphic_comp_affine L.meromorphic_derivWeierstrassP t s x)
  rw [germ_congr (meromorphic_weierstrassP_affine L t s).deriv hd,
    show (fun z ↦ t * ℘'[L] (t * z + s)) = (fun _ ↦ t) * fun z ↦ ℘'[L] (t * z + s) from rfl,
    germ_mul (Meromorphic.const t) (meromorphic_comp_affine L.meromorphic_derivWeierstrassP t s),
    germ_const, ← two_mul_germ_half (meromorphic_comp_affine L.meromorphic_derivWeierstrassP t s)] at e
  have hy := germ_derivWeierstrassP_half_ne_zero L t s ht
  have h2 : (2 : MeroField) * germ (fun z ↦ ℘'[L] (t * z + s) / 2) ≠ 0 := by
    refine mul_ne_zero ?_ hy
    rw [← map_ofNat (algebraMap ℂ MeroField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  apply mul_left_cancel₀ h2
  exact e.trans (mul_comm _ _)

theorem kpush_const_smul {K M : Type*} [Field K] [Algebra ℂ K] [Field M] [Algebra ℂ M]
    (σ : K →ₐ[ℂ] M) (c : ℂ) (η : KaehlerDifferential ℂ K) : kpush σ (c • η) = c • kpush σ η := by
  rw [← algebraMap_smul K c η, kpush_smul, AlgHom.commutes, algebraMap_smul]

theorem homConst_latticeToHom (α : latticeHom L₁ L₂) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) (latticeToHom α) = α := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, map_zero, h0]
  have e := omegaAt_eq_homConst_smul (latticeToHom α)
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, latticeToHom_of_ne_zero α h0, map_ellEval_isogPt, kpush_const_smul,
    invariantDifferential, kpush_omegaAt, map_ellEval_genericPoint, basePoint_eq] at e'
  have e'' := congrArg omegaDeriv e'
  rw [omegaDeriv_affinePoint, ← algebraMap_smul MeroField, LinearMap.map_smul,
    omegaDeriv_affinePoint, smul_eq_mul, map_one, mul_one] at e''
  exact ((algebraMap ℂ MeroField).injective e'').symm
end Elliptic
end

section
namespace Elliptic
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

variable {L₁ L₂ : PeriodPair}

theorem homConst_ne_zero {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)} (hQ : Q ≠ 0) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ≠ 0 := by
  set φ := isogOfHom Q hQ
  have hsep : φ.IsSeparable := by
    have := φ.finiteDimensional
    exact Algebra.IsSeparable.of_integral _ _
  have h1 := (isSeparable_iff_isogConst_ne_zero φ).1 hsep
  have h2 : isogConst φ = homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q := by
    apply (algebraMap ℂ (weierstrassCurve L₁).toAffine.FunctionField).injective
    rw [algebraMap_isogConst, algebraMap_homConst]
    rfl
  rwa [← h2]

theorem homConst_injective :
    Function.Injective (homConst (weierstrassCurve L₁) (weierstrassCurve L₂)) := by
  rw [injective_iff_map_eq_zero]
  intro Q h
  by_contra hQ
  exact homConst_ne_zero hQ h

theorem exists_eq_constMap_of_omegaDeriv {W : WeierstrassCurve ℂ}
    (P : (W.baseChange MeroField).toAffine.Point) (h : omegaDeriv (omegaAt W P) = 0) :
    ∃ R : W.toAffine.Point, P = constMap W MeroField R := by
  rcases P with _ | ⟨u, v, hP⟩
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec W hP
  have e₁ := congrArg omegaDeriv s₁
  have e₂ := congrArg omegaDeriv s₂
  rw [LinearMap.map_smul, h, smul_eq_mul, mul_zero, omegaDeriv_D, eq_comm] at e₁ e₂
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₁
  obtain ⟨d, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₂
  have hcd : W.toAffine.Nonsingular c d :=
    (W.toAffine.baseChange_nonsingular (f := Algebra.ofId ℂ MeroField)
      (algebraMap ℂ MeroField).injective c d).1 hP
  exact ⟨.some c d hcd, rfl⟩

theorem exists_map_ellEval_eq {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)}
    (hQ : Q ≠ 0) :
    ∃ c : ℂ, Point.map (ellEval L₁) Q.1 =
      affinePoint L₂ (homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q) c
        (homConst_ne_zero hQ) := by
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  have e := omegaAt_eq_homConst_smul Q
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, kpush_const_smul, invariantDifferential, kpush_omegaAt,
    map_ellEval_genericPoint, basePoint_eq] at e'
  have hω : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1)) =
      algebraMap ℂ MeroField α := by
    rw [e', ← algebraMap_smul MeroField, LinearMap.map_smul, omegaDeriv_affinePoint, smul_eq_mul,
      map_one, mul_one]
  have hD : omegaDeriv (omegaAt (weierstrassCurve L₂)
      (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0) =
        omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1) -
          omegaAt (weierstrassCurve L₂) (affinePoint L₂ α 0 h0) :=
      map_sub (omegaHom (weierstrassCurve L₂)) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L₂) R
  refine ⟨0 + c, ?_⟩
  rw [← affinePoint_add_constMap, ← hR]
  abel

theorem homConst_mem_latticeHom (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ∈ latticeHom L₁ L₂ := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero]
    exact zero_mem _
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  obtain ⟨c, hc⟩ := exists_map_ellEval_eq hQ
  have hg : IsGenPt (weierstrassCurve L₂) Q.1 := isGenPt_of_mem_isogHom Q.2 (fun h ↦ hQ (Subtype.ext h))
  obtain ⟨hne, hQs⟩ := eq_some_xOf_yOf _ (isGenPt_ne_zero _ hg)
  rw [hQs, Point.map_some, affinePoint, Point.some.injEq] at hc
  obtain ⟨f, hf, hfe⟩ := exists_isEllipticFunction_ellEval_eq L₁ (xOf _ Q.1)
  obtain ⟨g, hg', hge⟩ := exists_isEllipticFunction_ellEval_eq L₁ (yOf _ Q.1)
  rw [hfe, germ_eq_germ_iff hf.1 (meromorphic_weierstrassP_affine L₂ α c)] at hc
  rw [hge, germ_eq_germ_iff hg'.1 (meromorphic_derivWeierstrassP_half_affine L₂ α c)] at hc
  obtain ⟨hcx, hcy⟩ := hc
  intro l hl
  obtain ⟨z, h1, h2, h3, h4, h5, h6⟩ := nonempty_of_mem_codiscrete (hcx.and (hcy.and
    ((eventually_affine hcx one_ne_zero l).and ((eventually_affine hcy one_ne_zero l).and
    ((eventually_affine (eventually_notMem_lattice L₂) h0 c).and
    (eventually_affine (eventually_notMem_lattice L₂) h0 (α * l + c)))))))
  beta_reduce at h1 h2
  simp only [one_mul] at h3 h4
  rw [hf.2 z l hl] at h3
  rw [hg'.2 z l hl] at h4
  have e₁ : ℘[L₂] (α * z + (α * l + c)) = ℘[L₂] (α * z + c) := by
    rw [← h1, h3, show α * (z + l) + c = α * z + (α * l + c) by ring]
  have e₂ : ℘'[L₂] (α * z + (α * l + c)) = ℘'[L₂] (α * z + c) := by
    have := h2.symm.trans h4
    rw [show α * (z + l) + c = α * z + (α * l + c) by ring] at this
    linear_combination 2 * this.symm
  have hpt : toPoint L₂ (α * z + (α * l + c)) = toPoint L₂ (α * z + c) := by
    rw [toPoint_of_notMem h6, toPoint_of_notMem h5]
    exact point_some_congr e₁ (by rw [e₂])
  have := torusToPoint_injective (L := L₂) (a₁ := Torus.mk L₂ _) (a₂ := Torus.mk L₂ _) hpt
  rw [Torus.mk_eq_mk_iff] at this
  simpa using this

theorem latticeToHom_homConst (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    latticeToHom ⟨_, homConst_mem_latticeHom Q⟩ = Q :=
  homConst_injective (by rw [homConst_latticeToHom])

theorem latticeToHom_add (α β : latticeHom L₁ L₂) :
    latticeToHom (α + β) = latticeToHom α + latticeToHom β :=
  homConst_injective (by
    rw [map_add (f := _), homConst_latticeToHom, homConst_latticeToHom, homConst_latticeToHom]
    rfl)

theorem ellEval_comp_translate (L : PeriodPair) (z : ℂ) :
    (ellEval L).comp (translate (weierstrassCurve L) (toPoint L z)) =
      (affineComp 1 z one_ne_zero).comp (ellEval L) := by
  apply algHom_eq_of_map_genericPoint' (E := weierstrassCurve L)
  rw [← Point.map_map, map_translate_genericPoint, map_add (f := _), map_ellEval_genericPoint,
    show constPoint (weierstrassCurve L) (toPoint L z) =
      constMap (weierstrassCurve L) _ (toPoint L z) from rfl, map_constMap, basePoint_eq,
    affinePoint_add_constMap, ← Point.map_map, map_ellEval_genericPoint, basePoint_eq,
    map_affineComp_affinePoint]
  exact affinePoint_congr L _ _ (by ring) (by ring)

theorem homPt_latticeToHom (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeToHom α) (toPoint L₁ z) = toPoint L₂ (α * z) := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, homPt_zero, AddMonoidHom.zero_apply, h0, zero_mul,
      toPoint_zero]
  apply homPt_eq_of
  apply Point.map_injective (ellEval L₁)
  rw [Point.map_map, ellEval_comp_translate, ← Point.map_map, latticeToHom_of_ne_zero α h0,
    map_ellEval_isogPt, map_affineComp_affinePoint, map_add, map_ellEval_isogPt, map_constMap,
    affinePoint_add_constMap]
  exact affinePoint_congr L₂ _ _ (by ring) (by ring)

section End

variable {L : PeriodPair}

theorem latticeToHom_mul (α β : latticeHom L L) (h : (α : ℂ) * β ∈ latticeHom L L) :
    latticeToHom ⟨_, h⟩ = latticeToHom α * latticeToHom β := by
  by_cases hα : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α hα, zero_mul, latticeToHom_of_eq_zero _ (by simp [hα])]
  by_cases hβ : (β : ℂ) = 0
  · rw [latticeToHom_of_eq_zero β hβ, mul_zero, latticeToHom_of_eq_zero _ (by simp [hβ])]
  have hg : IsGenPt (weierstrassCurve L) (latticeToHom β).1 := by
    rw [latticeToHom_of_ne_zero β hβ]
    exact isGenPt_isogPt _ _
  apply Subtype.ext
  apply Point.map_injective (ellEval L)
  have e : Point.map (ellEval L) (latticeToHom β).1 = affinePoint L β 0 hβ := by
    rw [latticeToHom_of_ne_zero β hβ, map_ellEval_isogPt]
  rw [isogEnd_mul_def, homComp_of_isGenPt _ _ hg, Point.map_map, ← genEval_map _ (ellEval L) hg,
    genEval_congr _ e _ (isGenPt_affinePoint L β 0 hβ), genEval_affinePoint, ← Point.map_map,
    latticeToHom_of_ne_zero α hα, map_ellEval_isogPt, map_affineComp_affinePoint,
    latticeToHom_of_ne_zero _ (mul_ne_zero hα hβ), map_ellEval_isogPt]
  exact affinePoint_congr L _ _ rfl (by ring)

end End
end Elliptic
end

section
namespace Elliptic
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped PeriodPair

variable {L₁ L₂ : PeriodPair}

variable (L₁ L₂) in
def latticeHomEquiv : latticeHom L₁ L₂ ≃+ isogHom (weierstrassCurve L₁) (weierstrassCurve L₂) where
  toFun := latticeToHom
  invFun Q := ⟨_, homConst_mem_latticeHom Q⟩
  left_inv α := Subtype.ext (homConst_latticeToHom α)
  right_inv Q := latticeToHom_homConst Q
  map_add' := latticeToHom_add

variable (L : PeriodPair)

def latticeEnd : Subring ℂ where
  carrier := {α | ∀ l ∈ L.lattice, α * l ∈ L.lattice}
  add_mem' ha hb := (latticeHom L L).add_mem ha hb
  zero_mem' := (latticeHom L L).zero_mem
  neg_mem' ha := (latticeHom L L).neg_mem ha
  one_mem' l hl := by rwa [one_mul]
  mul_mem' {a b} ha hb l hl := by
    rw [mul_assoc]
    exact ha _ (hb l hl)

def latticeEndEquiv : latticeEnd L ≃+* isogEnd (weierstrassCurve L) where
  toFun α := latticeToHom ⟨α, α.2⟩
  invFun Q := ⟨homConst (weierstrassCurve L) (weierstrassCurve L) Q, homConst_mem_latticeHom Q⟩
  left_inv _ := Subtype.ext (homConst_latticeToHom _)
  right_inv Q := latticeToHom_homConst Q
  map_mul' α β := latticeToHom_mul ⟨α, α.2⟩ ⟨β, β.2⟩ (α * β).2
  map_add' α β := latticeToHom_add ⟨α, α.2⟩ ⟨β, β.2⟩

theorem homConst_latticeEndEquiv (α : latticeEnd L) :
    homConst (weierstrassCurve L) (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeToHom _

variable {L}
end Elliptic
end

end GroundTheory.Global
