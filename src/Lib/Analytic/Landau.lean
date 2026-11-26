module

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import TauCeti.Analysis.LaplaceTransform.Meromorphic
public import Lib.Analytic.EntireLFunction

/-!
# Landau's lemma

This part applies Landau's theorem for Laplace transforms to transforms satisfying `New.IsPolar`.
Assume a one-sided bound on the error term `E`, and assume that the residues `r x` at real `x > β`
have non-negative real part. Then the part concludes that there is no pole to the right of `β`.
Together with `Lib.Analytic.EntireLFunction`, this is the analytic tool for passing from a
one-sided bound on an error term to the absence of zeros of L-functions.

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

open Complex Set Filter MeasureTheory Topology

namespace New

variable {E : ℝ → ℝ}

/-- **No pole to the right of `β`**, by Landau's theorem for Laplace transforms and the sign of the
residues at real points.
Suppose `IsPolar E r`: `|E v| ≤ C e^v` for `v ≥ 0` and the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` has a meromorphic continuation with at most simple poles of residue `r ρ`
in `re ρ > 0`. Let `β > 0`. If `E(v) ≤ A e^{(β-1)v}` for all large `v` and the residues at real points
right of `β` have real part `≥ 0`, then there is no pole in `re s > β`, that is, `r ρ = 0`. -/
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {A β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re) (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0 := by
  obtain ⟨hE, C, Φ, hΦ, hE_growth, Φ_eq, Φ_res⟩ := h
  obtain ⟨Y, hY⟩ := hE_le.exists_forall_of_atTop
  -- The Laplace transform of `E v * e ^ v` is `Φ` on `re s > 2`.
  have hL (s : ℂ) (hs : 2 < s.re) :
      TauCeti.HasLaplace (fun u ↦ ((E u * Real.exp u : ℝ) : ℂ)) s (Φ s) := by
    have h_eq (u : ℝ) : cexp (-s * u) • ((E u * Real.exp u : ℝ) : ℂ) = E u * cexp ((1 - s) * u) := by
      rw [show (1 - s) * u = u + -s * u by ring, Complex.exp_add]
      simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp]
      ring
    refine TauCeti.hasLaplace_iff.2 ⟨?_, ?_⟩
    · exact (integrableOn_laplace_of_abs_le hE hE_growth hs).congr_fun
        (fun u _ ↦ (h_eq u).symm) measurableSet_Ioi
    · simp_rw [h_eq]
      exact (Φ_eq s hs).symm
  have hg : ∀ᵐ u ∂volume.restrict (Ioi Y), E u * Real.exp u ≤ A * Real.exp (β * u) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ by
      calc E u * Real.exp u ≤ A * Real.exp ((β - 1) * u) * Real.exp u := by
            gcongr; exact hY u hu.le
        _ = A * Real.exp (β * u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  -- At a real pole `x ∈ (β, 2]`, the simple pole has trailing coefficient `r x`.
  have hsign (x : ℝ) (hx : x ∈ Ioc β 2) (hp : meromorphicOrderAt Φ (x : ℂ) < 0) :
      0 ≤ (meromorphicTrailingCoeffAt Φ (x : ℂ)).re := by
    have hx_re : 0 < (x : ℂ).re := by simpa using hβ.trans hx.1
    have hsub : MeromorphicAt (fun z : ℂ ↦ z - x) (x : ℂ) := by fun_prop
    -- The pole is simple: `(z - x) Φ z` has a limit, so its order is nonnegative.
    have h_ord : 0 ≤ meromorphicOrderAt ((fun z : ℂ ↦ z - x) * Φ) (x : ℂ) :=
      (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hsub.mul (hΦ x))).1 ⟨_, Φ_res x hx_re⟩
    rw [meromorphicOrderAt_mul hsub (hΦ x), meromorphicOrderAt_id_sub_const] at h_ord
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hp.ne_top
    rw [← hn] at hp h_ord
    have hn_eq : n = -1 := by
      norm_cast at hp h_ord
      omega
    have h_tendsto := (hΦ x).tendsto_nhds_meromorphicTrailingCoeffAt
    rw [← hn, hn_eq] at h_tendsto
    have h_lim : Tendsto (fun z : ℂ ↦ (z - x) * Φ z) (𝓝[≠] (x : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt Φ (x : ℂ))) := by
      simpa [Pi.mul_def] using h_tendsto
    rw [tendsto_nhds_unique h_lim (Φ_res x hx_re)]
    exact hr x hx.1
  obtain ⟨hn, -⟩ := TauCeti.hasLaplace_toMeromorphicNFOn_of_ae_le_exp hg (fun s _ ↦ hΦ s) hL hsign
  obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hΦ ρ)).2 (hn ρ hρ)
  have h_zero : Tendsto (fun z : ℂ ↦ z - ρ) (𝓝[≠] ρ) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa using tendsto_nhds_unique (Φ_res ρ (hβ.trans hρ)) (by simpa using h_zero.mul hc)

end New
