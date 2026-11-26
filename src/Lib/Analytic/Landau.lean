module

public import Lib.Analytic.EntireLFunction
import TauCeti.Analysis.LaplaceTransform.Landau

/-!
# Landau's lemma

This part applies Landau's theorem for Laplace transforms (`TauCeti.Analysis.LaplaceTransform.Landau`)
to transforms satisfying `New.IsPolar`. Assume a one-sided bound on the error term `E`, and assume
that the residues `r x` at real `x > β` have non-negative real part. Then the part concludes that
there is no pole to the right of `β`. Together with `Lib.Analytic.EntireLFunction`, these are the
analytic tools for passing from a one-sided bound on an error term to the absence of zeros of
L-functions.

## Main definitions and results

* `New.IsPolar.landau`: let `β > 0`. If `E v ≤ A e^{(β-1)v}` for all large `v` and `re (r x) ≥ 0`
  for real `x > β`, then `r ρ = 0` for `re ρ > β`.

Notions from other files:
* `New.IsPolar` (from `Lib.Analytic.EntireLFunction`): `E` is measurable, `|E v| ≤ C e^v` for
  `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv` continues meromorphically with at most simple poles of
  residue `r ρ` in `re ρ > 0`.

## Relation to the literature

Known result: Landau's lemma on Dirichlet integrals of one sign. It is applied to transforms with
simple poles whose residues at real points have non-negative real part: no pole lies to the right
of the abscissa given by the one-sided bound. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Lemma 15.1 (Widder, The Laplace Transform, 1941, II Thm 5b).
-/

@[expose] public section

open Complex Set Filter MeasureTheory Metric Topology ComplexOrder AnalyticOnNhd Real

namespace New

variable {E : ℝ → ℝ}

/-- Let `E` satisfy `|E v| ≤ C e^v` for `v ≥ 0`, and let `β > 0`. If `E v ≤ A e^{(β-1)v}` for large
`v`, then `E(v) e^v ≤ K e^{βv}` for some `K` and all `v > 0`. -/
private lemma exists_mul_exp_le {C A β : ℝ} (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v)
    (hβ : 0 < β) (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v)) :
    ∃ K : ℝ, ∀ v : ℝ, 0 < v → E v * Real.exp v ≤ K * Real.exp (β * v) := by
  obtain ⟨Y, hY⟩ := hE_le.exists_forall_of_atTop
  refine ⟨max A (|C| * Y.exp ^ 2), fun v hv ↦ ?_⟩
  obtain hYv | hvY := le_total Y v
  · calc
      E v * v.exp ≤ (A * Real.exp ((β - 1) * v)) * v.exp := by grw [hY v hYv]
      _ = A * Real.exp (β * v) := by rw [mul_assoc, ← Real.exp_add, sub_one_mul, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · calc
      E v * v.exp ≤ |C| * v.exp * v.exp := by
        grw [le_abs_self (E v), hE_growth v hv.le, le_abs_self C]
      _ ≤ max A (|C| * Y.exp ^ 2) := by grw [mul_assoc, ← sq, hvY, ← le_max_right]
      _ ≤ _ := le_mul_of_one_le_right
        ((show 0 ≤ |C| * Y.exp ^ 2 by positivity).trans (le_max_right _ _))
        (Real.one_le_exp (by positivity))

/-- Identity theorem: two functions meromorphic on `re z > a` that agree far to the right agree
on a punctured neighbourhood of every point of the half-plane. -/
private lemma eventuallyEq_of_eq_far_right {f g : ℂ → ℂ} {a b : ℝ}
    (hf : MeromorphicOn f {z : ℂ | a < z.re}) (hg : MeromorphicOn g {z : ℂ | a < z.re})
    (hfg : ∀ z : ℂ, b < z.re → f z = g z) {ρ : ℂ} (hρ : a < ρ.re) :
    f =ᶠ[𝓝[≠] ρ] g := by
  obtain ⟨s₀, has₀, hbs₀⟩ : ∃ s₀ : ℝ, a < s₀ ∧ b < s₀ := by simpa using exists_gt (max a b)
  have order_s₀ : meromorphicOrderAt (f - g) s₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr <| eventually_nhdsWithin_of_eventually_nhds <|
      mem_of_superset ((isOpen_re_gt b).mem_nhds hbs₀) fun z hz ↦ sub_eq_zero.mpr (hfg z hz)
  exact eventuallyEq_iff_sub.mpr <| meromorphicOrderAt_eq_top_iff.mp <| by_contra fun hne ↦
    (hf.sub hg).meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt a).isPreconnected hρ has₀ hne order_s₀

/-- **No pole to the right of `β`**, by Landau's lemma and the sign of the residues at real points.
Suppose `IsPolar E r`: `|E v| ≤ C e^v` for `v ≥ 0` and the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` has a meromorphic continuation with at most simple poles of residue `r ρ`
in `re ρ > 0`. Let `β > 0`. If `E(v) ≤ A e^{(β-1)v}` for all large `v` and the residues at real points
right of `β` have real part `≥ 0`, then there is no pole in `re s > β`, that is, `r ρ = 0`. -/
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {A β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re) (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0 := by
  obtain ⟨hE, C, Φ, hΦ, hE_growth, Φ_eq, Φ_res⟩ := h
  obtain ⟨K, hK⟩ := exists_mul_exp_le hE_growth hβ hE_le
  let f (v : ℝ) : ℝ := K * Real.exp (β * v) - E v * Real.exp v
  have hf_nonneg : ∀ v : ℝ, 0 < v → 0 ≤ f v := fun v hv ↦ sub_nonneg.2 (hK v hv)
  let S : Set ℝ := {σ : ℝ | IntegrableOn (fun v : ℝ ↦ cexp (-(σ : ℂ) * v) • (f v : ℂ)) (Ioi 0)}
  let F (s : ℂ) : ℂ := ∫ v : ℝ in Ioi 0, cexp (-s * v) • (f v : ℂ)
  let Ψ (s : ℂ) : ℂ := K / (s - β) - Φ s
  have h_integrand (s : ℂ) (v : ℝ) :
      cexp (-s * v) • (f v : ℂ) = K * cexp ((β - s) * v) - E v * cexp ((1 - s) * v) := by
    simp only [f, smul_eq_mul, ofReal_sub, ofReal_mul, ofReal_exp, mul_sub, sub_mul, one_mul,
      Complex.exp_sub, neg_mul, Complex.exp_neg]
    ring
  have far_right (s : ℂ) (hs : β + 2 < s.re) :
      TauCeti.HasLaplace (fun v ↦ (f v : ℂ)) s (Ψ s) := by
    have hsβ : (β - s).re < 0 := by grind [sub_re, ofReal_re]
    have int_exp : IntegrableOn (fun v : ℝ ↦ K * cexp ((β - s) * v)) (Ioi 0) :=
      (integrableOn_exp_mul_complex_Ioi hsβ 0).const_mul K
    have int_E := integrableOn_laplace_of_abs_le hE hE_growth (s := s) (by linarith)
    refine TauCeti.HasLaplace.intro
      ((int_exp.sub int_E).congr (.of_forall fun v ↦ (h_integrand s v).symm)) ?_
    calc ∫ v : ℝ in Ioi 0, cexp (-s * v) • (f v : ℂ)
        = ∫ v : ℝ in Ioi 0, (K * cexp ((β - s) * v) - E v * cexp ((1 - s) * v)) :=
          setIntegral_congr_fun measurableSet_Ioi fun v _ ↦ h_integrand s v
      _ = Ψ s := by
          rw [integral_sub int_exp int_E, integral_const_mul, integral_exp_mul_complex_Ioi hsβ,
            ← neg_sub s, neg_div_neg_eq, ← Φ_eq s (by linarith)]
          simp [Ψ, div_eq_mul_inv]
  have Ψ_res (ρ : ℂ) (hρ : β < ρ.re) : Tendsto (fun z ↦ (z - ρ) * Ψ z) (𝓝[≠] ρ) (𝓝 (-r ρ)) := by
    have hK_cont : ContinuousAt (fun s : ℂ ↦ K / (s - β)) ρ := by
      fun_prop (disch := exact sub_ne_zero.2 fun h_eq ↦ by simp [h_eq] at hρ)
    simpa [Ψ, mul_sub] using (tendsto_sub_mul_of_continuousAt hK_cont).sub (Φ_res ρ (hβ.trans hρ))
  have bdd : BddAbove Sᶜ :=
    ⟨β + 2, fun x hx ↦ le_of_not_gt fun hlt ↦ hx (far_right x (by simpa)).integrable⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, IsLUB (insert β Sᶜ) a := Real.exists_isLUB (by simp) (bdd.insert β)
  have hL (s : ℂ) (hs : a < s.re) : TauCeti.HasLaplace (fun v ↦ (f v : ℂ)) s (F s) := by
    have h_mem : s.re ∈ S := of_not_not fun hxS ↦ hs.not_ge (ha.1 (mem_insert_of_mem β hxS))
    exact (h_mem.hasLaplace.integrableOn_of_re_le (by simp)).hasLaplace
  have hF_diff : DifferentiableOn ℂ F {s : ℂ | a < s.re} :=
    TauCeti.differentiableOn_of_hasLaplace_re_gt hL
  have F_analytic {z : ℂ} (hz : a < z.re) : AnalyticAt ℂ F z :=
    hF_diff.analyticAt ((isOpen_re_gt a).mem_nhds hz)
  have Ψ_eq {z : ℂ} (hz : a < z.re) : Ψ =ᶠ[𝓝[≠] z] F := eventuallyEq_of_eq_far_right (b := max a (β + 2))
    (fun w _ ↦ by fun_prop) (fun w hw ↦ (F_analytic hw).meromorphicAt)
    (fun w hw ↦ (far_right w (le_max_right _ _ |>.trans_lt hw)).unique
      (hL w (le_max_left _ _ |>.trans_lt hw))) hz
  obtain rfl | hβa : β = a ∨ β < a := (ha.1 (mem_insert β Sᶜ)).eq_or_lt
  · simpa using tendsto_nhds_unique ((Ψ_res ρ hρ).congr' (Ψ_eq hρ).mul_left)
      (tendsto_sub_mul_of_continuousAt (F_analytic hρ).continuousAt)
  · have hΨ_mer : MeromorphicAt Ψ a := by fun_prop
    have tendsto_real : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] a) (𝓝[≠] a) :=
      ((hasDerivAt_id' a).ofReal_comp.tendsto_nhdsNE one_ne_zero).mono_left (nhdsGT_le_nhdsNE a)
    have eq_near : ∀ᶠ x : ℝ in 𝓝[>] a, Ψ =ᶠ[𝓝 (x : ℂ)] F := by
      filter_upwards [tendsto_real.eventually hΨ_mer.eventually_analyticAt, self_mem_nhdsWithin]
        with x hΨx hx using (hΨx.frequently_eq_iff_eventually_eq (F_analytic (by simpa))).mp
          (Ψ_eq (by simpa)).frequently
    have h_nonneg : 0 ≤ -r a := by
      refine ge_of_tendsto ((Ψ_res a hβa).comp tendsto_real) ?_
      filter_upwards [eq_near, self_mem_nhdsWithin] with x hΨx (hx : a < x)
      have hFx : F x = (∫ v in Ioi (0 : ℝ), Real.exp (-x * v) * f v : ℝ) :=
        (setIntegral_congr_fun measurableSet_Ioi fun v _ ↦ by
          simp [smul_eq_mul, ofReal_exp]).trans integral_ofReal
      dsimp only [Function.comp_apply]
      rw [hΨx.self_of_nhds, hFx]
      have h_int_nonneg : 0 ≤ ∫ v in Ioi (0 : ℝ), Real.exp (-x * v) * f v :=
        setIntegral_nonneg measurableSet_Ioi fun v hv ↦
          mul_nonneg (Real.exp_nonneg _) (hf_nonneg v hv)
      rw [← ofReal_sub, ← ofReal_mul, ← ofReal_zero]
      exact Complex.real_le_real.mpr (mul_nonneg (sub_nonneg.2 hx.le) h_int_nonneg)
    have h_res_zero : -r a = 0 :=
      Complex.ext (le_antisymm (by simpa using hr a hβa) h_nonneg.1) h_nonneg.2.symm
    let G (z : ℂ) : ℂ := (z - a) * Ψ z
    obtain ⟨p, hp⟩ : AnalyticAt ℂ G a :=
      MeromorphicAt.analyticAt (by fun_prop)
        (by simpa [continuousAt_iff_punctured_nhds, G, h_res_zero] using Ψ_res a hβa)
    let g : ℂ → ℂ := dslope G a
    obtain ⟨δ, hδ, hg_an⟩ := hp.dslope_fslope.analyticAt.exists_ball_analyticOnNhd
    have hg_lap : ∀ z ∈ ball (a : ℂ) δ, a < z.re →
        TauCeti.HasLaplace (fun v ↦ (f v : ℂ)) z (g z) := by
      intro z hz hza
      have h_eq_on : EqOn g F (ball (a : ℂ) δ ∩ {w : ℂ | a < w.re}) := by
        have h_conn : IsPreconnected (ball (a : ℂ) δ ∩ {w : ℂ | a < w.re}) :=
          ((convex_ball (a : ℂ) δ).inter (convex_halfSpace_re_gt a)).isPreconnected
        obtain ⟨x, hΨx, hax, hxδ⟩ :=
          (eq_near.and (Ioo_mem_nhdsGT (by linarith : a < a + δ))).exists
        have hx_mem : (x : ℂ) ∈ ball (a : ℂ) δ ∩ {w : ℂ | a < w.re} := by
          refine ⟨?_, by simpa⟩
          rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.2 hax)]
          linarith
        have h_ev : g =ᶠ[𝓝 (x : ℂ)] F :=
          ((eqOn_dslope_sub_smul Ψ a).eventuallyEq_of_mem
            (isOpen_ne.mem_nhds (ofReal_injective.ne hax.ne'))).trans hΨx
        exact (hg_an.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
          (fun w hw ↦ F_analytic hw.2) h_conn hx_mem h_ev
      rw [h_eq_on ⟨hz, hza⟩]
      exact hL z hza
    have h_ext (σ : ℝ) (hσ : a - δ < σ) : σ ∈ S :=
      TauCeti.integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg (u₀ := 0)
        (ae_restrict_of_forall_mem measurableSet_Ioi hf_nonneg) hδ hg_an.differentiableOn hg_lap
        (by simpa)
    obtain ⟨σ, hσ, hσ_gt, -⟩ : ∃ σ ∈ insert β Sᶜ, max β (a - δ) < σ ∧ σ ≤ a :=
      ha.exists_between (max_lt hβa (sub_lt_self a hδ))
    obtain ⟨hβσ, hδσ⟩ : β < σ ∧ a - δ < σ := max_lt_iff.mp hσ_gt
    exact absurd (h_ext σ hδσ) (hσ.resolve_left hβσ.ne')

end New
