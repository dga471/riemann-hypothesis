module

public import GroundTheory.AutomorphicForms.ReductionMeasure
public import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Tactic.TypeStar

@[expose] public section

open MeasureTheory Measure Topology Filter Set IsDedekindDomain NumberField

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem isMulRightInvariant_finite (μ : Measure (AdelicGLn.FiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.FiniteAdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨fun g => ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [mul_one]
    exact Measure.map_id
  let _ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _
  have : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  set P := μi.prod μ
  have hP := (GJGlobal.isMulRightInvariant_prod_haar hn μi μ).map_mul_right_eq_self
  refine ⟨fun g => ?_⟩
  have hprod : P.map (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = μi.prod (μ.map (· * g)) := by
    have hf : (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = Prod.map id (· * g) := by
      funext p
      exact Prod.ext (mul_one p.1) rfl
    rw [hf, ← Measure.map_prod_map μi μ measurable_id (measurable_mul_const g), Measure.map_id]
  rw [hP] at hprod
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds (1 : AdelicGLn.InfiniteAdelicGL K n)
  have hA0 : μi A ≠ 0 := (measure_pos_of_mem_nhds μi hA).ne'
  have hAt : μi A ≠ ⊤ := hAc.measure_lt_top.ne
  refine Measure.ext fun B hB => ?_
  have h1 := congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod
  simp only [P, Measure.prod_prod] at h1
  exact ((ENNReal.mul_right_inj hA0 hAt).1 h1).symm

end

end Whittaker

end GroundTheory.Automorphic
