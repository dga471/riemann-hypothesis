module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionImageSup
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionImageSup
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartSup
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionSupBound
import Mathlib.Topology.Algebra.MvPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set Filter Topology

noncomputable section

namespace ResolutionImageSup

theorem analyticOnNhd_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} {V : Set E}
    {g : E → ι → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (fun w => g w i) V) (f : MvPolynomial ι ℂ) :
    AnalyticOnNhd ℂ (fun w => eval (g w) f) V :=
  BlockResolutionImageSup.analyticOnNhd_eval hg f

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem lift_ne_zero (d : HSMDatum D Ω κ) {x y : d.R.X} (hy : y ∈ d.R.U x) : d.R.lift x y ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := (d.R.mem x y hy).1 ()
  exact hi (by rw [h]; rfl)

theorem ptNorm_resPt_eq (d : HSMDatum D Ω κ) {n : ℕ} {f : MvPolynomial (Ix κ) ℂ} (hf : f.IsHomogeneous n)
    {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ptNorm d.m (RingHom.id ℂ) n f (resPt d y) = ptNorm d.m (RingHom.id ℂ) n f (d.R.lift x y) := by
  obtain ⟨c, hc, hcy⟩ := d.R.compat y x y ⟨d.R.mem_U y, hy⟩
  have h : resPt d y = c () • d.R.lift x y := by
    rw [resPt, hcy]
    rfl
  rw [h, ResolutionSupBound.ptNorm_smul d.m hf (hc ())]

end ResolutionImageSup

open ResolutionImageSup in
theorem ResolutionImageSup.proof (hC : ChartSupBound.Statement) : ResolutionImageSup.Statement := by
  intro D Ω _ _ κ _ d
  refine BlockResolutionImageSup.exists_sup_bound hC d.R d.dV d.vol d.m.ρ
    (fun x y hy => d.m.pos _ (lift_ne_zero d hy)) (fun x j => ?_)
    (fun y₀ => d.smooth.continuousOn.continuousAt (isOpen_ne.mem_nhds (lift_ne_zero d (d.R.mem_U y₀))))
    (P_hom := fun n f => f.IsHomogeneous n)
    (fun n f y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y))
    (fun hf _ _ hy => by rw [ptNorm_resPt_eq d hf hy]; simp [ptNorm])
    (fun n f => resolutionVolumeL2Complex d n f) (fun _ => rfl)
  have hL2 : ContDiffOn ℝ 2 (fun w => d.R.lift x ((d.R.A.chart j).symm w))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x) :=
    contDiffOn_pi.2 fun p => ((d.R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hρ : ContDiffOn ℝ 2 (fun w => d.m.ρ (d.R.lift x ((d.R.A.chart j).symm w)))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x) :=
    (d.smooth.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp hL2
      fun w hw => lift_ne_zero d hw.2
  exact contDiffOn_const.mul (hρ.log fun w hw => (d.m.pos _ (lift_ne_zero d hw.2)).ne')

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
