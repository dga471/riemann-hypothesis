module

public import GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup SemiLocal WithZero Function Topology Filter

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus


instance : Dvd (Modulus K) :=
  ⟨fun 𝔪 𝔫 ↦ 𝔪.ideal ∣ 𝔫.ideal ∧ 𝔪.real ⊆ 𝔫.real⟩

omit [NumberField K] in
theorem dvd_iff {𝔪 𝔫 : Modulus K} : 𝔪 ∣ 𝔫 ↔ 𝔪.ideal ∣ 𝔫.ideal ∧ 𝔪.real ⊆ 𝔫.real :=
  Iff.rfl

omit [NumberField K] in
theorem dvd_refl' (𝔪 : Modulus K) : 𝔪 ∣ 𝔪 :=
  ⟨dvd_rfl, subset_rfl⟩

theorem ideal_dvd_ideal_iff {𝔪 𝔫 : Modulus K} :
    𝔪.ideal ∣ 𝔫.ideal ↔ ∀ v, 𝔪.exponent v ≤ 𝔫.exponent v := by
  have he (𝔞 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
      𝔞.exponent v = multiplicity v.asIdeal 𝔞.ideal := by
    simp [exponent, FiniteMultiplicity.of_prime_left v.prime 𝔞.ideal_ne_bot]
  simpa only [he, Ideal.finprod_heightOneSpectrum_pow_multiplicity 𝔪.ideal_ne_bot] using
    (finprod_asIdeal_pow_dvd_iff 𝔪.finite_support_exponent 𝔫.ideal_ne_bot)

end Modulus

theorem multiplicity_finprod_asIdeal_pow_eq {a : HeightOneSpectrum (𝓞 K) → ℕ}
    (ha : (support a).Finite) (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (∏ᶠ w, w.asIdeal ^ a w) = a v :=
  multiplicity_finprod_asIdeal_pow ha v

section Local

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

theorem isOpen_ker_localSymbol (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((localSymbol L v).ker : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  rw [ker_localSymbol L v w]
  exact LocalField.isOpen_range_normUnits _ _

theorem exists_unitsLevel_le_ker_localSymbol (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, unitsLevel v n ≤ (localSymbol L v).ker := by
  obtain ⟨n, -, hn⟩ := exists_unitsLevel_subset (K := K) v
    ((isOpen_ker_localSymbol L v).mem_nhds (localSymbol L v).ker.one_mem)
  exact ⟨n, hn⟩

def localConductorExponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  sInf {n : ℕ | unitsLevel v n ≤ (localSymbol L v).ker}

theorem unitsLevel_le_ker_localSymbol_iff (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} :
    unitsLevel v n ≤ (localSymbol L v).ker ↔ localConductorExponent L v ≤ n := by
  have hne : {n : ℕ | unitsLevel v n ≤ (localSymbol L v).ker}.Nonempty :=
    exists_unitsLevel_le_ker_localSymbol L v
  exact ⟨fun h ↦ Nat.sInf_le h,
    fun h ↦ (unitsLevel_antitone v h).trans (Nat.sInf_mem hne)⟩

theorem unitFiltrationUnits_zero_eq_unitsLevel_zero (v : HeightOneSpectrum (𝓞 K)) :
    LocalField.unitFiltrationUnits (v.adicCompletion K) 0 = unitsLevel v 0 := by
  ext x
  rw [mem_unitFiltrationUnits_zero_iff_valued, mem_unitsLevel]
  refine ⟨fun h ↦ ⟨h, ?_⟩, fun h ↦ h.1⟩
  rw [Nat.cast_zero, neg_zero, exp_zero]
  exact Valuation.map_sub_le _ h.le (by simp)

theorem localConductorExponent_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    localConductorExponent L v = 0 ↔ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [← Nat.le_zero, ← unitsLevel_le_ker_localSymbol_iff]
  constructor
  · intro h
    exact ramificationIdx_eq_one_of_units_le_ker_localSymbol v
      (by rw [unitFiltrationUnits_zero_eq_unitsLevel_zero]; exact h) w
  · intro he
    rw [unitsLevel_zero]
    exact units_le_ker_localSymbol L v ⟨w, inferInstance⟩ he

theorem finite_support_localConductorExponent :
    (support (localConductorExponent (K := K) L)).Finite := by
  have h := eventually_units_le_ker_localSymbol (K := K) L
  refine (Filter.eventually_cofinite.1 h).subset fun v hv ↦ ?_
  intro hu
  apply hv
  rw [← Nat.le_zero, ← unitsLevel_le_ker_localSymbol_iff, unitsLevel_zero]
  exact hu

end Local

end

end GroundTheory.Global
