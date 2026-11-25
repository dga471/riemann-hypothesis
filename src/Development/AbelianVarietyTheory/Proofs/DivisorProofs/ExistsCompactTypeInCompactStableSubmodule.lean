module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Formalism.RealPlaceAnalysis.StatementKT
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace GlobalTheory.KTypeExists

open Formalism.REAL GlobalTheory.UnitaryDerived GlobalTheory.UnitaryHighestWeight

section Lie

variable {n : ℕ} {ε : Fin n → Bool}

theorem inK_smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) : inK ε ((t : ℂ) • X) := by
  refine ⟨?_, by rw [Matrix.smul_mul, Matrix.mul_smul, hX.2]⟩
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  show ((t : ℂ) • X)ᴴ * Jm ε + Jm ε * ((t : ℂ) • X) = 0
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← smul_add, h, smul_zero]

theorem exp_memK {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (kFacts n ε).2.2.2.1 _ (inK_smul hX t)

theorem entry_eq_zero {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) {a b : Fin n} (hab : ε a ≠ ε b) :
    X a b = 0 := by
  have h := congrFun (congrFun hX a) b
  simp only [Jm, mul_diagonal, diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at h hab
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h

theorem single_comm {a b : Fin n} (hab : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
  ext i j
  simp only [Jm, mul_diagonal, diagonal_mul, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [hab]
  · simp [h]

theorem conj_single {a b : Fin n} (hab : ε a = ε b) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = Matrix.single b a 1 := by
  rw [conjTranspose_single, star_one, ← single_comm hab.symm, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]

theorem cpart_inK {a b : Fin n} (hab : ε a = ε b) :
    inK ε (cpart1 ε (Matrix.single a b 1)) ∧ inK ε (cpart2 ε (Matrix.single a b 1)) := by
  obtain ⟨h1, h2, -⟩ := cpartMem n ε (Matrix.single a b 1)
  refine ⟨⟨h1, ?_⟩, h2, ?_⟩
  · rw [cpart1, conj_single hab, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      single_comm hab, single_comm hab.symm]
  · rw [cpart2, conj_single hab, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      single_comm hab, single_comm hab.symm]

theorem diag_inK (θ : Fin n → ℝ) : inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  have h : (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) * Jm ε =
      Jm ε * Matrix.diagonal fun a => (θ a : ℂ) * Complex.I := by
    simp only [Jm, diagonal_mul_diagonal, mul_comm]
  refine ⟨?_, h⟩
  show _ * _ + _ = 0
  rw [diag_skew, Matrix.neg_mul, h, neg_add_cancel]

end Lie

section Deriv

variable {n : ℕ} {ε : Fin n → Bool} {B : Type} [NormedRing B] [NormedAlgebra ℂ B]
  {F : Matrix (Fin n) (Fin n) ℂ → B}

theorem eabV_eabVK (hs : SmoothOnGV ε F) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → F (k * x) = F k * F x)
    {a b : Fin n} (hab : ε a = ε b) (c d : Fin n) :
    EabV ε a b (EabV ε c d F) 1 = EabV ε a b F 1 * EabV ε c d F 1 := by
  obtain ⟨h1, h2⟩ := cpart_inK hab
  have h := fun g hg => eabV_mul_of hs (hK g hg) c d
  show RdV _ _ 1 + Complex.I • RdV _ _ 1 = (RdV _ F 1 + Complex.I • RdV _ F 1) * _
  rw [rdV_one_of_eq_line hs h1.1 (fun t => h _ (exp_memK h1 t)),
    rdV_one_of_eq_line hs h2.1 (fun t => h _ (exp_memK h2 t)), add_mul, smul_mul_assoc]

theorem kRel_eabV (hs : SmoothOnGV ε F) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → F (k * x) = F k * F x) :
    KRel ε fun a b => EabV ε a b F 1 := by
  intro a b c d hab hcd
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have := eabGlV n ε B F a b c d 1 hs hone
  rwa [eabV_eabVK hs hK hab, eabV_eabVK hs hK hcd] at this

end Deriv

section Unit

variable {n : ℕ} {ε : Fin n → Bool} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}

theorem exists_derived (hs : SmoothOnGV ε π) (h1 : π 1 = 1)
    (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) (hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖) :
    ∃ E : Fin n → Fin n → Module.End ℂ W, KRel ε E ∧ KUnit ε E ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  refine ⟨fun a b => (EabV ε a b π 1).toLinearMap, ?_, ?_, ?_⟩
  · intro a b c d hab hcd
    have := congrArg ContinuousLinearMap.toLinearMap (kRel_eabV hs hK a b c d hab hcd)
    split_ifs at this ⊢ <;> exact this
  · intro a b hab x y
    obtain ⟨h1', h2'⟩ := cpart_inK hab
    have e1 : cpart1 ε (Matrix.single b a 1) = ((-1 : ℝ) : ℂ) • cpart1 ε (Matrix.single a b (1 : ℂ)) := by
      rw [cpart1, cpart1, conj_single hab, conj_single hab.symm, ← neg_sub, smul_neg]
      push_cast
      rw [neg_one_smul]
    have e2 : cpart2 ε (Matrix.single b a 1) = cpart2 ε (Matrix.single a b (1 : ℂ)) := by
      rw [cpart2, cpart2, conj_single hab, conj_single hab.symm, add_comm]
    have e3 := (rdLinV n _ _ π π _ _ (-1) 0 1 hs hs h1'.1 h1'.1 hone).2.1
    simp only [EabV, EcV, e1, e2, e3, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    have s1 := rdV_skew_line hs h1 h1'.1 (fun t => hiso _ (exp_memK h1' t)) x y
    have s2 := rdV_skew_line hs h1 h2'.1 (fun t => hiso _ (exp_memK h2' t)) x y
    rw [s1, s2]
    simp
  · intro Z hZ v
    have := hasDerivAt_apply hs hZ.1 v
    rw [rdV_eq_sum hs hZ.1] at this
    simpa using this

end Unit

section Weights

open Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}

theorem group_zeroK (h1 : π 1 = 1) (Z : Matrix (Fin n) (Fin n) ℂ) (v : W) :
    π (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  simp [h1]

theorem group_addK (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (s t : ℝ) (v : W) :
    π (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      π (NormedSpace.exp ((s : ℂ) • Z)) (π (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl Z).smul_left _).smul_right _), hK _ (exp_memK hZ s) _ (exp_indefinite_unitary_holds n ε Z hZ.1 t)]
  rfl

theorem isWtOn_of_isWeightK (h1 : π 1 = 1) (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x)
    (E : Fin n → Fin n → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin n → ℝ) (v : W) (hv : IsWeight E μ v) : IsWtOn (Kset ε) π μ v := by
  intro θ _
  have h := eigen (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)))
    (∑ a, ((θ a : ℂ) * Complex.I) • E a a) (group_zeroK h1 _) (group_addK hK (diag_inK θ))
    (fun w => by
      have := hE _ (diag_inK θ) w
      rw [UnitaryHighestWeight.sum_diag] at this
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using this)
    v (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) (by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv _, smul_smul, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring)
  simp only [exp_diag, one_mul] at h
  exact h

theorem isWeight_of_isWtOnK (E : Fin n → Fin n → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin n → ℝ) (v : W) (hv : IsWtOn (Kset ε) π μ v) : IsWeight E μ v := by
  intro a
  set θ : Fin n → ℝ := Pi.single a 1 with hθ
  have h1 := hE _ (diag_inK θ) v
  rw [UnitaryHighestWeight.sum_diag] at h1
  have h2 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) v) =
      fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v := by
    funext t
    have hm := exp_memK (diag_inK (ε := ε) θ) t
    rw [exp_diag] at hm ⊢
    rw [hv (fun b => t * θ b) hm]
    congr 2
    simp [hθ, Pi.single_apply]
    ring
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v) ((μ a * Complex.I) • v) 0 := by
    have h4 : HasDerivAt (fun t : ℝ => (μ a * Complex.I) * (t : ℂ)) (μ a * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (μ a * Complex.I)
    simpa using h4.cexp.smul_const v
  rw [h2] at h1
  have h5 := h1.unique h3
  have h6 : ∑ b, ((θ b : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp [hθ]
    · intro b _ hb
      simp [hθ, Pi.single_eq_of_ne hb]
    · simp
  rw [h6, mul_comm, ← smul_smul] at h5
  exact smul_right_injective W Complex.I_ne_zero h5

theorem stable_of_derivedK [FiniteDimensional ℂ W] (h1 : π 1 = 1)
    (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) (E : Fin n → Fin n → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, inK ε Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : KStable ε E S) : IsKStableOn ε π S := by
  intro g hg v hv
  obtain ⟨Y, hY, hg', -⟩ := compact_exponential_surjective n ε g hg
  have h := stable (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E a b)
    (group_zeroK h1 _) (group_addK hK hY)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hE _ hY w) S
    (fun w hw => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
      by_cases hab : ε a = ε b
      · exact S.smul_mem _ (hS a b hab w hw)
      · rw [entry_eq_zero hY.2 hab, zero_smul]
        exact S.zero_mem) v hv 1
  simpa [hg'] using h

theorem cdom_of_mem_kSpan (E : Fin n → Fin n → Module.End ℂ W) (Λ μ : Fin n → ℝ) (x v : W) (hr : KRel ε E)
    (hk : KUnit ε E) (hΛ : KHighest ε E Λ x) (hv : v ∈ kSpan ε E x) (hv0 : v ≠ 0) (hμ : IsWeight E μ v) :
    CDom ε μ Λ := by
  by_contra hne
  rw [compact_span_eq_lowering hr hΛ] at hv
  have key : ∀ z ∈ lowSpan ε E x, ⟪z, v⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      refine compact_weight_orthogonal W n _ E _ μ _ v hk (word_action_weight hr hΛ.1 w (fun q hq => (hw q hq).1)) hμ ?_
      intro heq
      exact hne (heq ▸ cdom_add_lowering_word _ Λ w hw)
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  exact hv0 (inner_self_eq_zero.mp (key v hv))

theorem exists_highest [FiniteDimensional ℂ W] [Nontrivial W] (hs : SmoothOnGV ε π) (h1 : π 1 = 1)
    (hK : ∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) (hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ W, IsKStableOn ε π S → S = ⊥ ∨ S = ⊤) :
    ∃ Λ : Fin n → ℝ, (∃ v, v ≠ 0 ∧ IsWtOn (Kset ε) π Λ v) ∧
      ∀ (μ : Fin n → ℝ) (v : W), v ≠ 0 → IsWtOn (Kset ε) π μ v → CDom ε μ Λ := by
  obtain ⟨E, hr, hk, hE⟩ := exists_derived hs h1 hK hiso
  obtain ⟨x, -, hx, Λ, hΛ⟩ := highestWeightExists_holds W n ε E ⊤ inferInstance hr hk (fun _ _ _ _ _ => trivial) top_ne_bot
  have hxm : x ∈ kSpan ε E x := Submodule.mem_sInf.2 fun S hS => hS.1
  have hst : KStable ε E (kSpan ε E x) := fun a b hab y hy =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b hab y (Submodule.mem_sInf.1 hy S hS)
  have htop : kSpan ε E x = ⊤ := by
    rcases hirr _ (stable_of_derivedK h1 hK E hE _ hst) with h | h
    · rw [h] at hxm
      exact absurd hxm hx
    · exact h
  exact ⟨Λ, ⟨x, hx, isWtOn_of_isWeightK h1 hK E hE Λ x hΛ.1⟩, fun μ v hv hw =>
    cdom_of_mem_kSpan E Λ μ x v hr hk hΛ (htop ▸ trivial) hv (isWeight_of_isWtOnK E hE μ v hw)⟩

end Weights

section Main

open Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_minimal (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStableOn ε σ S) (h0 : S ≠ ⊥) :
    ∃ S' : Submodule ℂ H, S' ≤ S ∧ S' ≠ ⊥ ∧ IsKStableOn ε σ S' ∧
      ∀ T : Submodule ℂ H, T ≤ S' → IsKStableOn ε σ T → T = ⊥ ∨ T = S' := by
  obtain ⟨S', ⟨hle, hne, hst⟩, hmin⟩ := (measure fun T : Submodule ℂ H => Module.finrank ℂ T).wf.has_min
    {T | T ≤ S ∧ T ≠ ⊥ ∧ IsKStableOn ε σ T} ⟨S, le_rfl, h0, hS⟩
  refine ⟨S', hle, hne, hst, fun T hT hTs => ?_⟩
  by_contra hcon
  push Not at hcon
  haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  exact hmin T ⟨hT.trans hle, hcon.1, hTs⟩ (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hT hcon.2))

theorem proj_comm (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hS : IsKStableOn ε σ S) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : H) :
    S.starProjection (σ k v) = σ k (S.starProjection v) := by
  have hk' : kᴴ ∈ Kset ε := by
    refine ⟨Unitary.star_mem hk.1, ?_⟩
    have := congrArg conjTranspose hk.2
    rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  have hkU : k ∈ UJset ε := (kFacts n ε).1 k hk
  have hkU' : kᴴ ∈ UJset ε := (kFacts n ε).1 _ hk'
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hS k hk _ (Submodule.starProjection_apply_mem S v)) fun w hw => ?_
  have hkk : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
  have hw' : w = σ k (σ kᴴ w) := by
    have := hσ.1.2 k hkU _ hkU'
    rw [hkk, hσ.1.1] at this
    exact DFunLike.congr_fun this w
  rw [← map_sub, hw']
  have := LinearIsometry.inner_map_map (𝕜 := ℂ) ⟨(σ k).toLinearMap, hσ.2.1 k hkU⟩ (v - S.starProjection v) (σ kᴴ w)
  exact this.trans (Submodule.starProjection_inner_eq_zero v _ (hS _ hk' w hw))

theorem exists_smooth_restrict (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hS : IsKStableOn ε σ S) :
    ∃ π : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S), SmoothOnGV ε π ∧ π 1 = 1 ∧
      (∀ k ∈ Kset ε, ∀ x, inUJ ε x → π (k * x) = π k * π x) ∧ ∀ k ∈ Kset ε, ∀ v : S, (π k v : H) = σ k v := by
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  let b : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun g => S.orthogonalProjection ∘L σ g ∘L S.subtypeL
  have hb : ∀ g (v : S), (b g v : H) = S.starProjection (σ g v) := fun g v => rfl
  have hbK : ∀ k ∈ Kset ε, ∀ v : S, (b k v : H) = σ k v := fun k hk v => by
    rw [hb, (Submodule.starProjection_eq_self_iff (K := S)).2 (hS k hk v v.2)]
  have hb1 : b 1 = 1 := by
    ext v
    rw [hb, hσ.1.1]
    exact (Submodule.starProjection_eq_self_iff (K := S)).2 v.2
  have hcont : ContinuousOn b {g | inUJ ε g} :=
    continuousOn_clm_apply.2 fun v => S.orthogonalProjection.continuous.comp_continuousOn (hσ.2.2 v)
  have hmul : ∀ k ∈ Kset ε, ∀ g, inUJ ε g → b (k * g) = b k * b g := fun k hk g hg => by
    ext v
    rw [ContinuousLinearMap.mul_apply, hbK k hk, hb, hb, hσ.1.2 k ((kFacts n ε).1 k hk) g hg,
      ContinuousLinearMap.comp_apply, proj_comm hσ S hS hk]
  obtain ⟨F, hF, hF1, hFK⟩ := exists_smooth_equivariant hb1 hcont
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have hFb : ∀ k ∈ Kset ε, F k = b k := fun k hk => by
    simpa [hF1] using hFK k ((kFacts n ε).1 k hk) (hmul k hk) 1 hone
  refine ⟨F, hF, hF1, fun k hk x hx => ?_, fun k hk v => ?_⟩
  · rw [hFb k hk]
    exact hFK k ((kFacts n ε).1 k hk) (hmul k hk) x hx
  · rw [hFb k hk, hbK k hk]

theorem exists_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.HolDict.Mt n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    IsKStableOn ε σ S → S ≠ ⊥ → ∃ (μ : Fin n → ℝ) (S' : Submodule ℂ H), S' ≤ S ∧ IsKTypeOf ε σ μ S' := by
  intro n ε H _ _ σ hσ S _ hS h0
  obtain ⟨S', hle, hne, hst, hmin⟩ := exists_minimal S hS h0
  haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  haveI : Nontrivial S' := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨π, hs, h1, hK, hπ⟩ := exists_smooth_restrict hσ S' hst
  have hiso : ∀ g ∈ Kset ε, ∀ v, ‖π g v‖ = ‖v‖ := fun g hg v => by
    rw [Submodule.coe_norm, hπ g hg, hσ.2.1 g ((kFacts n ε).1 g hg), Submodule.coe_norm]
  have hwt : ∀ (μ : Fin n → ℝ) (v : S'), IsWtOn (Kset ε) π μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := fun μ v =>
    forall₂_congr fun θ hθ => by rw [← hπ _ hθ, ← Submodule.coe_smul, Subtype.coe_inj]
  obtain ⟨Λ, ⟨x, hx, hxw⟩, hΛ⟩ := exists_highest hs h1 hK hiso fun T hT => by
    rcases hmin (T.map S'.subtype) (Submodule.map_subtype_le _ _) (by
      rintro g hg _ ⟨v, hv, rfl⟩
      exact ⟨π g v, hT g hg v hv, hπ g hg v⟩) with h | h
    · exact Or.inl (Submodule.map_injective_of_injective S'.injective_subtype (by rw [h, Submodule.map_bot]))
    · exact Or.inr (Submodule.map_injective_of_injective S'.injective_subtype
        (by rw [h, Submodule.map_top, Submodule.range_subtype]))
  refine ⟨Λ, S', hle, inferInstance, hst, hmin, ⟨x, x.2, fun h => hx (Subtype.ext h), (hwt Λ x).1 hxw⟩,
    fun μ v hv hv0 hw => hΛ μ ⟨v, hv⟩ (fun h => hv0 (congrArg Subtype.val h)) ((hwt μ ⟨v, hv⟩).2 hw)⟩

end Main

end GlobalTheory.KTypeExists
