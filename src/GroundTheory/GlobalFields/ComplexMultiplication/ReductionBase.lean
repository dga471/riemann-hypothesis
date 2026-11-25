module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FunctionFieldPoint
import GroundTheory.ArithmeticGeometry.AbelianVarieties.NormEDS
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.ReductionTorsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section
noncomputable section
namespace GroundTheory.Global

section
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem under_eq_of_liesOver {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 K) = v :=
  HeightOneSpectrum.ext h.over.symm

theorem exists_finite_forall_liesOver {p : HeightOneSpectrum (𝓞 L) → Prop}
    (hp : ∀ᶠ w in Filter.cofinite, p w) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v ∉ T, ∀ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal → p w := by
  refine ⟨(fun w => w.under (𝓞 K)) '' {w | ¬ p w}, (Filter.eventually_cofinite.mp hp).image _,
    fun v hv w hw => by_contra fun hn => hv ⟨w, hn, under_eq_of_liesOver hw⟩⟩
end

section
open NumberField IsDedekindDomain

variable (L : Type*) [Field L] [NumberField L]

def localizationAt (v : HeightOneSpectrum (𝓞 L)) : Subalgebra (𝓞 L) L :=
  Localization.subalgebra.ofField L v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors

variable {L}

instance (v : HeightOneSpectrum (𝓞 L)) : IsLocalization.AtPrime (localizationAt L v) v.asIdeal :=
  Localization.subalgebra.isLocalization_ofField _ _ _

instance (v : HeightOneSpectrum (𝓞 L)) : IsDiscreteValuationRing (localizationAt L v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _

theorem mem_localizationAt_iff {v : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ localizationAt L v ↔ ∃ a s : 𝓞 L, s ∉ v.asIdeal ∧
      x = algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L s)⁻¹ := by
  unfold localizationAt Localization.subalgebra.ofField
  rw [← SetLike.mem_coe, Subalgebra.coe_copy]
  simp only [Set.mem_ofPred_eq, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe, exists_prop]

theorem finite_setOf_mem_asIdeal {b : 𝓞 L} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 L) | b ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {b}) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv

theorem eventually_mem_localizationAt (x : L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x ∈ localizationAt L v := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  refine Filter.eventually_cofinite.mpr
    ((finite_setOf_mem_asIdeal (nonZeroDivisors.ne_zero hb)).subset fun v hv => ?_)
  by_contra h
  exact hv (mem_localizationAt_iff.mpr ⟨a, b, h, div_eq_mul_inv _ _⟩)

theorem eventually_isUnit_localizationAt {x : L} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ h : x ∈ localizationAt L v, IsUnit (⟨x, h⟩ : localizationAt L v) := by
  filter_upwards [eventually_mem_localizationAt x, eventually_mem_localizationAt x⁻¹] with v h h'
  exact ⟨h, (Submonoid.isUnit_iff_of_ne_zero hx).2 h'⟩
end

section
open NumberField IsDedekindDomain IsLocalRing

variable {L : Type*} [Field L] [NumberField L]

theorem eventually_exists_map_eq (E : WeierstrassCurve L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_mem_localizationAt E.a₁, eventually_mem_localizationAt E.a₂,
    eventually_mem_localizationAt E.a₃, eventually_mem_localizationAt E.a₄,
    eventually_mem_localizationAt E.a₆] with v h₁ h₂ h₃ h₄ h₆
  exact ⟨⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩, rfl⟩

theorem isElliptic_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L} [E.IsElliptic]
    {W : WeierstrassCurve (localizationAt L v)} (h : W.map (algebraMap (localizationAt L v) L) = E)
    (hΔ : E.Δ⁻¹ ∈ localizationAt L v) : W.IsElliptic := by
  have hW : algebraMap (localizationAt L v) L W.Δ = E.Δ := by
    rw [← WeierstrassCurve.map_Δ, h]
  rw [WeierstrassCurve.isElliptic_iff]
  refine isUnit_iff_exists_inv.mpr ⟨⟨E.Δ⁻¹, hΔ⟩, Subtype.ext ?_⟩
  change algebraMap (localizationAt L v) L W.Δ * E.Δ⁻¹ = 1
  rw [hW]
  exact mul_inv_cancel₀ E.isUnit_Δ.ne_zero

theorem eventually_exists_model (E : WeierstrassCurve L) [E.IsElliptic] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.IsElliptic ∧ W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_exists_map_eq E, eventually_mem_localizationAt E.Δ⁻¹] with v ⟨W, h⟩ hΔ
  exact ⟨W, isElliptic_of_map_eq h hΔ, h⟩

theorem algebraMap_j_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L}
    [E.IsElliptic] {W : WeierstrassCurve (localizationAt L v)} [W.IsElliptic]
    (h : W.map (algebraMap (localizationAt L v) L) = E) :
    algebraMap (localizationAt L v) L W.j = E.j := by
  subst h
  exact (W.map_j _).symm

theorem eventually_residue_j_ne {E E' : WeierstrassCurve L} [E.IsElliptic] [E'.IsElliptic]
    (hj : E.j ≠ E'.j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E →
          W'.map (algebraMap (localizationAt L v) L) = E' →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
  filter_upwards [eventually_isUnit_localizationAt (sub_ne_zero.mpr hj)] with v ⟨hmem, hu⟩
    W W' _ _ h h'
  have hsub : W.j - W'.j = ⟨E.j - E'.j, hmem⟩ :=
    Subtype.ext (congrArg₂ (· - ·) (algebraMap_j_of_map_eq h) (algebraMap_j_of_map_eq h'))
  intro heq
  refine (residue_ne_zero_iff_isUnit (W.j - W'.j)).mpr (hsub ▸ hu) ?_
  rw [map_sub, heq, sub_self]

theorem j_map_residue {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.map (residue R)).j = residue R W.j :=
  W.map_j _

theorem eventually_goodReduction {ι : Type*} [Finite ι] (E : ι → WeierstrassCurve L)
    [∀ i, (E i).IsElliptic] (hE : Pairwise fun i k => (E i).j ≠ (E k).j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ (W : ι → WeierstrassCurve (localizationAt L v)) (_ : ∀ i, (W i).IsElliptic),
        (∀ i, (W i).map (algebraMap (localizationAt L v) L) = E i) ∧
        (∀ i, algebraMap (localizationAt L v) L (W i).j = (E i).j) ∧
        Pairwise fun i k => residue (localizationAt L v) (W i).j ≠
          residue (localizationAt L v) (W k).j := by
  have hd : ∀ i k, ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, i ≠ k →
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E i →
          W'.map (algebraMap (localizationAt L v) L) = E k →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
    intro i k
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall fun _ h => (h hik).elim
    · exact (eventually_residue_j_ne (hE hik)).mono fun _ h _ => h
  filter_upwards [Filter.eventually_all.mpr fun i => eventually_exists_model (E i),
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hd i)] with v hm hdv
  choose W hWe hWm using hm
  exact ⟨W, hWe, hWm, fun i => algebraMap_j_of_map_eq (hWm i),
    fun i k hik => hdv i k hik (W i) (W k) (hWm i) (hWm k)⟩
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

abbrev coordReduce :
    W.toAffine.CoordinateRing →+* (W.map (residue 𝒪)).toAffine.CoordinateRing :=
  CoordinateRing.map W (residue 𝒪)

theorem coordReduce_surjective : Function.Surjective (coordReduce W) := by
  intro y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (mapRingHom (residue 𝒪))
    (Polynomial.map_surjective (residue 𝒪) residue_surjective) p
  exact ⟨CoordinateRing.mk W q, by rw [CoordinateRing.map_mk, ← hq]⟩

theorem coordReduce_algebraMap (a : 𝒪) :
    coordReduce W (algebraMap 𝒪 W.toAffine.CoordinateRing a) =
      algebraMap (ResidueField 𝒪) _ (residue 𝒪 a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul (A := 𝒪[X]) a (1 : W.toAffine.CoordinateRing), CoordinateRing.map_smul,
    map_one, ← algebraMap_smul (A := (ResidueField 𝒪)[X]) (residue 𝒪 a)]
  simp

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem smul_basis_mul (c : 𝒪) (p q : 𝒪[X]) :
    (C c * p) • (1 : W.toAffine.CoordinateRing) + (C c * q) • CoordinateRing.mk W Y =
      algebraMap 𝒪 W.toAffine.CoordinateRing c * (p • 1 + q • CoordinateRing.mk W Y) := by
  rw [mul_add, mul_smul, mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul,
    algebraMap_smul]
  simp only [Algebra.smul_def]

def gaussPrime : Ideal W.toAffine.CoordinateRing := RingHom.ker (coordReduce W)

instance : (gaussPrime W).IsPrime := RingHom.ker_isPrime _

theorem gaussPrime_eq {ϖ : 𝒪} (hϖ : Irreducible ϖ) :
    gaussPrime W = Ideal.span {algebraMap 𝒪 W.toAffine.CoordinateRing ϖ} := by
  have hm : RingHom.ker (residue 𝒪) = Ideal.span {ϖ} := by
    rw [ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  apply le_antisymm
  · intro y hy
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq y
    have hy' : coordReduce W (p • 1 + q • CoordinateRing.mk W Y) = 0 := hy
    simp_rw [map_add (f := _), CoordinateRing.map_smul, map_one, CoordinateRing.map_mk, Polynomial.map_X]
      at hy'
    obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero hy'
    have hker : ∀ r : 𝒪[X], r.map (residue 𝒪) = 0 → ∃ r' : 𝒪[X], r = C ϖ * r' := by
      intro r hr
      have : r ∈ RingHom.ker (mapRingHom (residue 𝒪)) := hr
      rw [Polynomial.ker_mapRingHom, hm, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton'] at this
      obtain ⟨r', hr'⟩ := this
      exact ⟨r', by rw [← hr', mul_comm]⟩
    obtain ⟨p', rfl⟩ := hker p hp
    obtain ⟨q', rfl⟩ := hker q hq
    rw [smul_basis_mul, mul_comm]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show coordReduce W _ = 0
    rw [coordReduce_algebraMap, (residue_eq_zero_iff _).2, map_zero]
    exact (mem_maximalIdeal _).2 hϖ.not_isUnit

abbrev gaussRing : Type _ := Localization.AtPrime (gaussPrime W)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem algebraMap_coordinateRing_injective :
    Function.Injective (algebraMap 𝒪 W.toAffine.CoordinateRing) :=
  FaithfulSMul.algebraMap_injective _ _

theorem algebraMap_gaussRing_injective :
    Function.Injective (algebraMap W.toAffine.CoordinateRing (gaussRing W)) :=
  IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (gaussPrime W))

instance : IsDiscreteValuationRing (gaussRing W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hmax : maximalIdeal (gaussRing W) = Ideal.span
      {(algebraMap W.toAffine.CoordinateRing (gaussRing W)
        (algebraMap 𝒪 W.toAffine.CoordinateRing ϖ))} := by
    have e := congrArg (Ideal.map (algebraMap W.toAffine.CoordinateRing (gaussRing W)))
      (gaussPrime_eq W hϖ)
    refine (Localization.AtPrime.map_eq_maximalIdeal (I := gaussPrime W)).symm.trans ?_
    rw [e, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (gaussRing W) := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (algebraMap_gaussRing_injective W)).2
      ((map_ne_zero_iff _ (algebraMap_coordinateRing_injective W)).2 hϖ.ne_zero)
  refine ((IsDiscreteValuationRing.TFAE (gaussRing W) hnf).out 1 5).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩

section Fraction

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem coordinateRing_map_algebraMap {S : Type*} [CommRing S] (f : 𝒪 →+* S) (a : 𝒪) :
    CoordinateRing.map W f (algebraMap 𝒪 W.toAffine.CoordinateRing a) =
      algebraMap S (W.map f).toAffine.CoordinateRing (f a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul (A := 𝒪[X]) a (1 : W.toAffine.CoordinateRing), CoordinateRing.map_smul,
    map_one, ← algebraMap_smul (A := S[X]) (f a)]
  simp

abbrev coordBase : W.toAffine.CoordinateRing →+* (W.baseChange K).toAffine.CoordinateRing :=
  CoordinateRing.map W (algebraMap 𝒪 K)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
theorem coordBase_algebraMap (a : 𝒪) :
    coordBase W K (algebraMap 𝒪 W.toAffine.CoordinateRing a) =
      algebraMap 𝒪 (W.baseChange K).toAffine.CoordinateRing a :=
  (coordinateRing_map_algebraMap W (algebraMap 𝒪 K) a).trans
    (IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.CoordinateRing a).symm

instance : Algebra W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField :=
  ((algebraMap (W.baseChange K).toAffine.CoordinateRing _).comp (coordBase W K)).toAlgebra

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
theorem algebraMap_coordinateRing_functionField (a : W.toAffine.CoordinateRing) :
    algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField a =
      algebraMap _ _ (coordBase W K a) :=
  rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem algebraMap_coordinateRing_functionField_injective :
    Function.Injective
      (algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField) := by
  intro a b h
  rw [algebraMap_coordinateRing_functionField, algebraMap_coordinateRing_functionField] at h
  exact CoordinateRing.map_injective (IsFractionRing.injective 𝒪 K)
    (IsFractionRing.injective (W.baseChange K).toAffine.CoordinateRing _ h)

theorem exists_map_eq_smul (α : (W.baseChange K).toAffine.CoordinateRing) :
    ∃ (c : 𝒪) (a : W.toAffine.CoordinateRing), c ≠ 0 ∧
      coordBase W K a = c • α := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq α
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors 𝒪) p
  obtain ⟨b', hb', hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors 𝒪) q
  refine ⟨b * b', (b' • IsLocalization.integerNormalization (nonZeroDivisors 𝒪) p) • 1 +
    (b • IsLocalization.integerNormalization (nonZeroDivisors 𝒪) q) • CoordinateRing.mk W Y,
    mul_ne_zero (nonZeroDivisors.ne_zero hb) (nonZeroDivisors.ne_zero hb'), ?_⟩
  change CoordinateRing.map W (algebraMap 𝒪 K) _ = _
  rw [map_add (f := _), CoordinateRing.map_smul, CoordinateRing.map_smul, map_one, CoordinateRing.map_mk,
    Polynomial.map_X, Polynomial.map_smul, Polynomial.map_smul, hbp, hbq, smul_add]
  simp only [algebraMap_smul, smul_assoc, smul_smul, mul_comm b b']
  rfl

instance : IsFractionRing W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField := by
  have hinj := algebraMap_coordinateRing_functionField_injective W K
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  · exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero y.2))
  · obtain ⟨α, β, hβ, rfl⟩ :=
      IsFractionRing.div_surjective (A := (W.baseChange K).toAffine.CoordinateRing) z
    obtain ⟨c₁, a₁, hc₁, ha₁⟩ := exists_map_eq_smul W K α
    obtain ⟨c₂, a₂, hc₂, ha₂⟩ := exists_map_eq_smul W K β
    have hβ0 : algebraMap _ (W.baseChange K).toAffine.FunctionField β ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hβ)
    have hc : ∀ c : 𝒪, c ≠ 0 → algebraMap 𝒪 (W.baseChange K).toAffine.FunctionField c ≠ 0 :=
      fun c hc => by
        rw [IsScalarTower.algebraMap_apply 𝒪 K]
        exact (map_ne_zero_iff _ (algebraMap K _).injective).2
          ((map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hc)
    have key : ∀ (c : 𝒪) (a : W.toAffine.CoordinateRing),
        algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField
          (algebraMap 𝒪 _ c * a) = algebraMap 𝒪 _ c *
            algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField a := by
      intro c a
      rw [map_mul, algebraMap_coordinateRing_functionField W K (algebraMap 𝒪 _ c),
        coordBase_algebraMap, ← IsScalarTower.algebraMap_apply]
    have hs : algebraMap 𝒪 W.toAffine.CoordinateRing c₁ * a₂ ∈ nonZeroDivisors _ := by
      refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
      have := congrArg (algebraMap W.toAffine.CoordinateRing
        (W.baseChange K).toAffine.FunctionField) h0
      rw [key, map_zero, algebraMap_coordinateRing_functionField, ha₂, Algebra.smul_def,
        map_mul, ← IsScalarTower.algebraMap_apply] at this
      exact mul_ne_zero (hc c₁ hc₁) (mul_ne_zero (hc c₂ hc₂) hβ0) this
    refine ⟨⟨algebraMap 𝒪 _ c₂ * a₁, ⟨_, hs⟩⟩, ?_⟩
    simp only
    rw [key, key, algebraMap_coordinateRing_functionField, algebraMap_coordinateRing_functionField,
      ha₁, ha₂, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    field_simp

theorem isUnit_algebraMap_primeCompl (y : (gaussPrime W).primeCompl) :
    IsUnit (algebraMap W.toAffine.CoordinateRing (W.baseChange K).toAffine.FunctionField y) :=
  IsLocalization.map_units (W.baseChange K).toAffine.FunctionField
    (⟨y.1, Ideal.primeCompl_le_nonZeroDivisors (gaussPrime W) y.2⟩ :
      nonZeroDivisors W.toAffine.CoordinateRing)

instance : Algebra (gaussRing W) (W.baseChange K).toAffine.FunctionField :=
  (IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W)
    (isUnit_algebraMap_primeCompl W K)).toAlgebra

instance : IsScalarTower W.toAffine.CoordinateRing (gaussRing W)
    (W.baseChange K).toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq _ a).symm

instance : IsFractionRing (gaussRing W) (W.baseChange K).toAffine.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (gaussPrime W).primeCompl _ _

instance : IsScalarTower 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
      ← IsScalarTower.algebraMap_apply, algebraMap_coordinateRing_functionField,
      coordBase_algebraMap, ← IsScalarTower.algebraMap_apply]

end Fraction

section Residue

def gaussResidue : ResidueField (gaussRing W) →+* (W.map (residue 𝒪)).toAffine.FunctionField :=
  IsFractionRing.lift (A := W.toAffine.CoordinateRing ⧸ gaussPrime W)
    (K := (gaussPrime W).ResidueField)
    (g := (algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField).comp
      (RingHom.kerLift (coordReduce W)))
    ((IsFractionRing.injective _ _).comp (RingHom.kerLift_injective _))

theorem gaussResidue_residue (a : W.toAffine.CoordinateRing) :
    gaussResidue W (residue (gaussRing W) (algebraMap _ (gaussRing W) a)) =
      algebraMap _ _ (coordReduce W a) := by
  have : residue (gaussRing W) (algebraMap _ (gaussRing W) a) =
      algebraMap (W.toAffine.CoordinateRing ⧸ gaussPrime W) (gaussPrime W).ResidueField
        (Ideal.Quotient.mk _ a) := by
    rw [Ideal.algebraMap_quotient_residueField_mk,
      IsScalarTower.algebraMap_apply _ (Localization.AtPrime (gaussPrime W))
        (gaussPrime W).ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rw [this, gaussResidue, IsFractionRing.lift_algebraMap]
  rfl

theorem gaussResidue_residue_algebraMap (c : 𝒪) :
    gaussResidue W (residue (gaussRing W) (algebraMap 𝒪 (gaussRing W) c)) =
      algebraMap (ResidueField 𝒪) _ (residue 𝒪 c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussResidue_residue, coordReduce_algebraMap, ← IsScalarTower.algebraMap_apply]

end Residue

section Generators

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def gaussX : gaussRing W := algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W (C X))

def gaussY : gaussRing W := algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W Y)

theorem algebraMap_gaussRing_functionField (a : W.toAffine.CoordinateRing) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (algebraMap W.toAffine.CoordinateRing _ a) =
        algebraMap (W.baseChange K).toAffine.CoordinateRing _ (coordBase W K a) := by
  rw [← IsScalarTower.algebraMap_apply, algebraMap_coordinateRing_functionField]

theorem algebraMap_gaussX :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussX W) =
      genX (W.baseChange K) := by
  rw [gaussX, algebraMap_gaussRing_functionField, genX]
  congr 1
  change CoordinateRing.map W (algebraMap 𝒪 K) _ = _
  rw [CoordinateRing.map_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]
  rfl

theorem algebraMap_gaussY :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussY W) =
      genY (W.baseChange K) := by
  rw [gaussY, algebraMap_gaussRing_functionField, genY]
  congr 1
  change CoordinateRing.map W (algebraMap 𝒪 K) _ = _
  rw [CoordinateRing.map_mk, Polynomial.map_X]
  rfl

theorem gaussResidue_gaussX :
    gaussResidue W (residue (gaussRing W) (gaussX W)) = genX (W.map (residue 𝒪)) := by
  rw [gaussX, gaussResidue_residue, genX]
  congr 1
  rw [CoordinateRing.map_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]

theorem gaussResidue_gaussY :
    gaussResidue W (residue (gaussRing W) (gaussY W)) = genY (W.map (residue 𝒪)) := by
  rw [gaussY, gaussResidue_residue, genY]
  congr 1
  rw [CoordinateRing.map_mk, Polynomial.map_X]

end Generators

instance : IsLocalHom (algebraMap 𝒪 (gaussRing W)) := by
  refine ⟨fun c hc => ?_⟩
  by_contra h
  have hm : algebraMap 𝒪 (gaussRing W) c ∈ maximalIdeal (gaussRing W) := by
    rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ (gaussPrime W)]
    show coordReduce W _ = 0
    rw [coordReduce_algebraMap, (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h), map_zero]
  exact (mem_maximalIdeal _).1 hm hc
end

section
open IsLocalRing GroundTheory.Arith.Abelian

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

theorem exists_zw_of_notMem_range {X₁ Y₁ : K} (h₁ : (curveK K W).Equation X₁ Y₁)
    (hX : X₁ ∉ Set.range ι) :
    ∃ z w v : 𝒪, z ∈ maximalIdeal 𝒪 ∧ z ≠ 0 ∧ w ∈ maximalIdeal 𝒪 ∧ w ≠ 0 ∧
      w = z ^ 3 * v ∧ IsUnit v ∧ ρ v = 1 ∧ ι z / ι w = X₁ ∧ -1 / ι w = Y₁ := by
  have hι := IsFractionRing.injective 𝒪 K
  obtain ⟨t, htm, ht⟩ := exists_inv_mem_of_notMem_range K hX
  have hX0 : X₁ ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
  have hT0 : ι t ≠ 0 := by rw [ht]; exact inv_ne_zero hX0
  have ht0 : t ≠ 0 := fun h => hT0 (by rw [h, map_zero])
  have hXt : X₁ * ι t = 1 := by rw [ht]; exact mul_inv_cancel₀ hX0
  obtain ⟨u, hu⟩ : ∃ u : 𝒪, u = 1 + W.a₂ * t + W.a₄ * t ^ 2 + W.a₆ * t ^ 3 := ⟨_, rfl⟩
  have huu : IsUnit u := isUnit_of_residue_ne_zero (by
    simp [hu, residue_eq_zero_of_mem htm])
  have hE := (WeierstrassCurve.Affine.equation_iff _ _).1 h₁
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hE

  have keyK : (Y₁ * ι t ^ 2) ^ 2 + ι W.a₁ * ι t * (Y₁ * ι t ^ 2) +
      ι W.a₃ * ι t ^ 2 * (Y₁ * ι t ^ 2) = ι t * ι u := by
    rw [hu]
    simp only [map_add (f := _), map_mul, map_one, map_pow]
    linear_combination (ι t) ^ 4 * hE - (ι W.a₁ * Y₁ * ι t ^ 3 - ι t * (1 + X₁ * ι t +
      X₁ ^ 2 * ι t ^ 2) - ι W.a₂ * ι t ^ 2 * (1 + X₁ * ι t) - ι W.a₄ * ι t ^ 3) * hXt

  obtain ⟨S, hS⟩ : Y₁ * ι t ^ 2 ∈ Set.range ι := by
    by_contra hSn
    obtain ⟨s', hs'm, hs'⟩ := exists_inv_mem_of_notMem_range K hSn
    have hS0 : Y₁ * ι t ^ 2 ≠ 0 := fun h => hSn ⟨0, by rw [h, map_zero]⟩
    have hinv : Y₁ * ι t ^ 2 * ι s' = 1 := by rw [hs']; exact mul_inv_cancel₀ hS0
    have e : ι (1 + W.a₁ * t * s' + W.a₃ * t ^ 2 * s') = ι (t * u * s' ^ 2) := by
      simp only [map_add (f := _), map_mul, map_one, map_pow]
      linear_combination (ι s') ^ 2 * keyK - (1 + Y₁ * ι t ^ 2 * ι s' + ι W.a₁ * ι t * ι s' +
        ι W.a₃ * ι t ^ 2 * ι s') * hinv
    have e' := congrArg ρ (hι e)
    simp only [map_add (f := _), map_mul, map_one, map_pow, residue_eq_zero_of_mem htm] at e'
    simp at e'
  have key : S ^ 2 + W.a₁ * t * S + W.a₃ * t ^ 2 * S = t * u := by
    apply hι
    simp only [map_add (f := _), map_mul, map_pow, hS]
    exact keyK
  have hSS : S * (S + W.a₁ * t + W.a₃ * t ^ 2) ∈ maximalIdeal 𝒪 := by
    rw [show S * (S + W.a₁ * t + W.a₃ * t ^ 2) = t * u by linear_combination key]
    exact Ideal.mul_mem_right _ _ htm
  have hB : S + W.a₁ * t + W.a₃ * t ^ 2 ∈ maximalIdeal 𝒪 := by
    have hat : W.a₁ * t + W.a₃ * t ^ 2 ∈ maximalIdeal 𝒪 :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ htm)
        (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_left _ _ htm))
    rcases (maximalIdeal.isMaximal 𝒪).isPrime.mem_or_mem hSS with h | h
    · rw [add_assoc]; exact Ideal.add_mem _ h hat
    · exact h
  obtain ⟨u', huu'⟩ : ∃ u' : 𝒪, u * u' = 1 := ⟨_, huu.mul_val_inv⟩
  obtain ⟨z, hz⟩ : ∃ z : 𝒪, z = -(S + W.a₁ * t + W.a₃ * t ^ 2) * u' := ⟨_, rfl⟩
  have htz : t = -S * z := by
    rw [hz]
    linear_combination (-u') * key - t * huu'
  have hz0 : z ≠ 0 := by rintro h; rw [h, mul_zero] at htz; exact ht0 htz
  have hS0 : S ≠ 0 := by rintro h; rw [h, neg_zero, zero_mul] at htz; exact ht0 htz
  have hzm : z ∈ maximalIdeal 𝒪 := by
    rw [hz]; exact Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 hB)
  obtain ⟨w, hw⟩ : ∃ w : 𝒪, w = t * z := ⟨_, rfl⟩
  have hwm : w ∈ maximalIdeal 𝒪 := hw ▸ Ideal.mul_mem_right _ _ htm
  have hw0 : w ≠ 0 := hw ▸ mul_ne_zero ht0 hz0
  obtain ⟨e, he⟩ : ∃ e : 𝒪, e = 1 - W.a₁ * z - W.a₂ * z ^ 2 - W.a₃ * w - W.a₄ * z * w -
      W.a₆ * w ^ 2 := ⟨_, rfl⟩
  have hwe : w * e = z ^ 3 := by
    have key' := key
    rw [hu, htz] at key'
    have : S * (w * e - z ^ 3) = 0 := by
      rw [he, hw, htz]
      linear_combination (-z ^ 2) * key'
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hS0)
  have hρe : ρ e = 1 := by
    simp [he, residue_eq_zero_of_mem hzm, residue_eq_zero_of_mem hwm]
  have heu : IsUnit e := isUnit_of_residue_ne_zero (by rw [hρe]; exact one_ne_zero)
  refine ⟨z, w, ↑heu.unit⁻¹, hzm, hz0, hwm, hw0, ?_, (heu.unit⁻¹).isUnit, ?_, ?_, ?_⟩
  · have h1 : e * ↑heu.unit⁻¹ = (1 : 𝒪) := heu.mul_val_inv
    linear_combination (↑heu.unit⁻¹ : 𝒪) * hwe - w * h1
  · have h1 : e * ↑heu.unit⁻¹ = (1 : 𝒪) := heu.mul_val_inv
    have := congrArg ρ h1
    rwa [map_mul, hρe, one_mul, map_one] at this
  · have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
    rw [hw, map_mul]
    field_simp
    linear_combination -hXt
  · have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
    have hSK := congrArg ι htz
    rw [map_mul, map_neg] at hSK
    rw [hw, map_mul]
    have hY : Y₁ = ι S / ι t ^ 2 := by rw [hS]; field_simp
    rw [hY]
    field_simp
    linear_combination (-1 : K) * hSK

theorem add_of_notMem_range' [DecidableEq K] [(W.map ι).IsElliptic]
    {X₁ Y₁ : K} (h₁ : (curveK K W).Nonsingular X₁ Y₁) (hX : X₁ ∉ Set.range ι) {x₂ y₂ : 𝒪}
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) :
    ∃ (x₃ y₃ : 𝒪) (h₃ : (curveK K W).Nonsingular (ι x₃) (ι y₃)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
        WeierstrassCurve.Affine.Point.some _ _ h₃ ∧ ρ x₃ = ρ x₂ ∧ ρ y₃ = ρ y₂ := by
  have hι := IsFractionRing.injective 𝒪 K
  obtain ⟨z', w, v, hzm, hz0, hwm, hw0', hwv, hvu, hρv', hX₁, hY₁⟩ :=
    exists_zw_of_notMem_range K W h₁.1 hX

  have heu : IsUnit (1 + y₂ * w) := isUnit_of_residue_ne_zero (by
    rw [map_add (f := _), map_one, map_mul, residue_eq_zero_of_mem hwm, mul_zero, add_zero]
    exact one_ne_zero)
  have hdu : IsUnit (1 - x₂ * z' ^ 2 * v) := isUnit_of_residue_ne_zero (by
    rw [map_sub, map_one, map_mul, map_mul, map_pow, residue_eq_zero_of_mem hzm]
    simp)
  set e := 1 + y₂ * w with he
  set d := 1 - x₂ * z' ^ 2 * v with hd
  set e' := (↑heu.unit⁻¹ : 𝒪) with he'
  set d' := (↑hdu.unit⁻¹ : 𝒪) with hd'
  have hee : e * e' = 1 := heu.mul_val_inv
  have hdd : d * d' = 1 := hdu.mul_val_inv
  set s := -(z' * d) * e' with hs
  set Fy := 2 * y₂ + W.a₁ * x₂ + W.a₃ with hFy
  set Fx := 3 * x₂ ^ 2 + 2 * W.a₂ * x₂ + W.a₄ - W.a₁ * y₂ with hFx
  set u₃ := (Fy - s * Fx) * z' * v * e * d' ^ 2 with hu₃
  set t₃ := -(Fy - s * Fx) * v * e ^ 2 * d' ^ 3 with ht₃

  have hw0 : ι w ≠ 0 := (map_ne_zero_iff _ hι).2 hw0'
  have hz0K : ι z' ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
  have hv0 : ι v ≠ 0 := (map_ne_zero_iff _ hι).2 hvu.ne_zero
  have he0 : ι e ≠ 0 := (map_ne_zero_iff _ hι).2 heu.ne_zero
  have hd0 : ι d ≠ 0 := (map_ne_zero_iff _ hι).2 hdu.ne_zero
  have heeK : ι e * ι e' = 1 := by rw [← map_mul, hee, map_one]
  have hddK : ι d * ι d' = 1 := by rw [← map_mul, hdd, map_one]
  have hwK : ι w = ι z' ^ 3 * ι v := by rw [hwv, map_mul, map_pow]
  have hX₂ : X₁ ≠ ι x₂ := fun h => hX ⟨x₂, h.symm⟩
  have hs0 : ι s ≠ 0 := by
    rw [hs, map_mul, map_neg, map_mul]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hz0K hd0)) (fun h => by
      rw [h, mul_zero] at heeK; exact zero_ne_one heeK)
  have hu₁ : X₁ - ι x₂ = ι (z' * d) / ι w := by
    rw [← hX₁, map_mul, hd, map_sub, map_one, map_mul, map_mul, map_pow, hwK]
    field_simp
  have hslope : (curveK K W).slope X₁ (ι x₂) Y₁ (ι y₂) = (ι s)⁻¹ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX₂, hu₁, ← hY₁]
    have hnum : -1 / ι w - ι y₂ = -ι e / ι w := by
      rw [he, map_add (f := _), map_one, map_mul]; field_simp; ring
    rw [hnum]
    refine eq_inv_of_mul_eq_one_left ?_
    simp only [hs, map_mul, map_neg]
    field_simp
    linear_combination heeK
  set ℓ := (ι s)⁻¹ with hℓ
  have hline : Y₁ = ι y₂ + ℓ * (X₁ - ι x₂) := by
    have := hslope
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX₂, div_eq_iff (sub_ne_zero.2 hX₂)] at this
    linear_combination this
  have hE₁ := h₁.1
  have hE₂ := h₂.1
  rw [WeierstrassCurve.Affine.equation_iff] at hE₁ hE₂
  rw [hline] at hE₁
  set B := ℓ ^ 2 + (curveK K W).a₁ * ℓ - 3 * ι x₂ - (curveK K W).a₂ with hB
  set C := ℓ * ι Fy - ι Fx with hC
  have hι2 : ι (2 : 𝒪) = 2 := map_ofNat _ 2
  have hι3 : ι (3 : 𝒪) = 3 := map_ofNat _ 3
  have hFyK : ι Fy = 2 * ι y₂ + (curveK K W).a₁ * ι x₂ + (curveK K W).a₃ := by
    rw [hFy]
    simp only [map_add (f := _), map_mul, hι2, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  have hFxK : ι Fx = 3 * ι x₂ ^ 2 + 2 * (curveK K W).a₂ * ι x₂ + (curveK K W).a₄ -
      (curveK K W).a₁ * ι y₂ := by
    rw [hFx]
    simp only [map_add (f := _), map_sub, map_mul, map_pow, hι2, hι3, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
  have R : (X₁ - ι x₂) * (-(X₁ - ι x₂) ^ 2 + B * (X₁ - ι x₂) + C) = 0 := by
    rw [hC, hFyK, hFxK, hB]
    linear_combination hE₁ - hE₂
  have R' := (mul_eq_zero.1 R).resolve_left (sub_ne_zero.2 hX₂)
  have he'K : ι e' = (ι e)⁻¹ := eq_inv_of_mul_eq_one_right heeK
  have hd'K : ι d' = (ι d)⁻¹ := eq_inv_of_mul_eq_one_right hddK
  have hsK : ι s = -(ι z' * ι d) * (ι e)⁻¹ := by rw [hs, map_mul, map_neg, map_mul, he'K]
  have E : C + (X₁ - ι x₂) * ι u₃ = 0 := by
    rw [hC, hℓ, hu₁, hu₃, hwK]
    simp only [map_mul, map_sub, map_pow, hd'K, hsK]
    rw [hsK] at hs0
    field_simp
    ring
  have hx₃ : (curveK K W).addX X₁ (ι x₂) ℓ = ι (x₂ + u₃) := by
    have h3 : (X₁ - ι x₂) * (B - (X₁ - ι x₂) - ι u₃) = 0 := by linear_combination R' - E
    have h4 := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hX₂))
    rw [WeierstrassCurve.Affine.addX, map_add (f := _)]
    rw [hB] at h4
    linear_combination h4
  have ht : ℓ * ι u₃ = ι t₃ := by
    rw [hℓ, hu₃, ht₃]
    simp only [map_mul, map_sub, map_pow, map_neg, hd'K, hsK]
    rw [hsK] at hs0
    field_simp
  have hy₃ : (curveK K W).addY X₁ (ι x₂) Y₁ ℓ =
      ι (-(y₂ + t₃) - W.a₁ * (x₂ + u₃) - W.a₃) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, hx₃,
      WeierstrassCurve.Affine.negY, hline]
    simp only [map_sub, map_neg, map_add (f := _), map_mul, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    rw [← ht]
    ring
  have h₃ := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun h => hX₂ h.1)
  rw [hslope, hx₃, hy₃] at h₃
  refine ⟨x₂ + u₃, -(y₂ + t₃) - W.a₁ * (x₂ + u₃) - W.a₃, h₃, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX₂, WeierstrassCurve.Affine.Point.some.injEq,
      hslope]
    exact ⟨hx₃, hy₃⟩
  · have hu₃m : u₃ ∈ maximalIdeal 𝒪 := by
      rw [hu₃]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ hzm)))
    rw [map_add (f := _), residue_eq_zero_of_mem hu₃m, add_zero]
  · have hu₃m : u₃ ∈ maximalIdeal 𝒪 := by
      rw [hu₃]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ hzm)))
    have hsm : s ∈ maximalIdeal 𝒪 := by
      rw [hs]; exact Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hzm))
    have hρe : ρ e = 1 := by
      rw [he, map_add (f := _), map_one, map_mul, residue_eq_zero_of_mem hwm, mul_zero, add_zero]
    have hρd : ρ d = 1 := by
      rw [hd, map_sub, map_one, map_mul, map_mul, map_pow, residue_eq_zero_of_mem hzm]
      simp
    have hρd' : ρ d' = 1 := by
      have := congrArg ρ hdd
      rwa [map_mul, hρd, one_mul, map_one] at this
    have hρv : ρ v = 1 := hρv'
    have hρt : ρ t₃ = -ρ Fy := by
      rw [ht₃]
      simp only [map_mul, map_neg, map_sub, map_pow, residue_eq_zero_of_mem hsm, hρv, hρe, hρd']
      ring
    rw [map_sub, map_sub, map_neg, map_add (f := _), hρt, hFy]
    have h2ρ : ρ (2 : 𝒪) = 2 := map_ofNat _ 2
    simp only [map_add (f := _), map_mul, h2ρ, residue_eq_zero_of_mem hu₃m, add_zero]
    ring

section Good

variable [W.IsElliptic]

theorem nonsingular_residue_of_isElliptic {x y : 𝒪} (h : (curveK K W).Equation (ι x) (ι y)) :
    (curveRed W).Nonsingular (ρ x) (ρ y) :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_residue W (equation_of_map K W h))

variable [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem reducePoint_add (P Q : (curveK K W).Point) :
    reducePoint K W (P + Q) = reducePoint K W P + reducePoint K W Q := by
  rcases point_cases K W P with rfl | ⟨X₁, Y₁, h₁, rfl, hX₁⟩ | ⟨x₁, y₁, h₁, rfl⟩
  · rw [zero_add, reducePoint_zero, zero_add]
  · rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]
    · rw [reducePoint_some_notMem K W h₁ hX₁, reducePoint_some_notMem K W h₂ hX₂, add_zero]
      rcases point_cases K W (WeierstrassCurve.Affine.Point.some _ _ h₁ +
          WeierstrassCurve.Affine.Point.some _ _ h₂) with h0 | ⟨X, Y, h, hS, hX⟩ | ⟨x, y, h, hS⟩
      · rw [h0, reducePoint_zero]
      · rw [hS, reducePoint_some_notMem K W h hX]
      · exfalso
        have hn : (curveK K W).Nonsingular X₂ ((curveK K W).negY X₂ Y₂) :=
          (WeierstrassCurve.Affine.nonsingular_neg _ _).2 h₂
        obtain ⟨x₃, y₃, h₃, e, -, -⟩ := add_of_notMem_range' K W hn hX₂ h
        have hneg : -(WeierstrassCurve.Affine.Point.some _ _ h₂) =
            WeierstrassCurve.Affine.Point.some _ _ hn := WeierstrassCurve.Affine.Point.neg_some h₂
        have e' : WeierstrassCurve.Affine.Point.some _ _ h₁ =
            WeierstrassCurve.Affine.Point.some _ _ h₃ := by
          rw [← e, ← hS, ← hneg]; abel
        rw [WeierstrassCurve.Affine.Point.some.injEq] at e'
        exact hX₁ ⟨x₃, e'.1.symm⟩
    · have n₂ := nonsingular_residue_of_isElliptic K W h₂.1
      obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₁ hX₁ h₂
      have n₃ : (curveRed W).Nonsingular (ρ x₃) (ρ y₃) := by rw [hx, hy]; exact n₂
      rw [e, reducePoint_some_integral K W h₃ n₃, reducePoint_some_notMem K W h₁ hX₁, zero_add,
        reducePoint_some_integral K W h₂ n₂, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
  · have n₁ := nonsingular_residue_of_isElliptic K W h₁.1
    rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]
    · obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₂ hX₂ h₁
      rw [add_comm] at e
      have n₃ : (curveRed W).Nonsingular (ρ x₃) (ρ y₃) := by rw [hx, hy]; exact n₁
      rw [e, reducePoint_some_integral K W h₃ n₃, reducePoint_some_notMem K W h₂ hX₂, add_zero,
        reducePoint_some_integral K W h₁ n₁, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    · have n₂ := nonsingular_residue_of_isElliptic K W h₂.1
      rw [reducePoint_some_integral K W h₁ n₁, reducePoint_some_integral K W h₂ n₂]
      by_cases hx : ρ x₁ = ρ x₂
      · by_cases hy : ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          rcases add_of_residue_neg K W h₁ h₂ n₁ n₂ hx hy with h0 | ⟨X, Y, h, hS, hX⟩
          · rw [h0, reducePoint_zero]
          · rw [hS, reducePoint_some_notMem K W h hX]
        · have hy' : ρ y₁ = ρ y₂ := by
            rcases WeierstrassCurve.Affine.Y_eq_of_X_eq n₁.1 n₂.1 hx with h | h
            · exact h
            · exact absurd h hy
          have hD : ρ (y₁ + y₂ + W.a₁ * x₁ + W.a₃) ≠ 0 := by
            intro h0; apply hy
            rw [map_add (f := _), map_add (f := _), map_add (f := _), map_mul] at h0
            simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₃, ← hx]
            linear_combination h0
          obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_eq K W h₁ h₂ n₁ n₂ hx hy' hD
          rw [e, e', reducePoint_some_integral K W h₃ n₃]
      · obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_X_ne K W h₁ h₂ n₁ n₂ hx
        rw [e, e', reducePoint_some_integral K W h₃ n₃]

def reductionHom : (curveK K W).Point →+ (curveRed W).Point where
  toFun := reducePoint K W
  map_zero' := reducePoint_zero K W
  map_add' := reducePoint_add K W

theorem reductionHom_apply (P : (curveK K W).Point) : reductionHom K W P = reducePoint K W P :=
  rfl

end Good
end

section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
include hxy in
theorem eval₂_polynomial_of_equation :
    W.toAffine.polynomial.eval₂ (eval₂RingHom j x) y = 0 := by
  have e := (equation_iff _ _).mp hxy
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom]
  linear_combination e

def coordEval : W.toAffine.CoordinateRing →+* Λ :=
  AdjoinRoot.lift (eval₂RingHom j x) y (eval₂_polynomial_of_equation W j hxy)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
theorem coordEval_mk (p : 𝒪[X][Y]) :
    coordEval W j hxy (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom j x) y :=
  AdjoinRoot.lift_mk _ _

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
theorem coordEval_algebraMap (c : 𝒪) :
    coordEval W j hxy (algebraMap 𝒪 W.toAffine.CoordinateRing c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    coordEval, AdjoinRoot.lift_of]
  simp

include hxy in
theorem equation_residue_of_equation :
    ((W.map (residue 𝒪)).map (ResidueField.map j)).toAffine.Equation (residue Λ x)
      (residue Λ y) := by
  have e := (equation_iff _ _).mp hxy
  rw [equation_iff]
  have := congrArg (residue Λ) e
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow] at this ⊢
  simp only [← RingHom.comp_apply (ResidueField.map j), ResidueField.map_comp_residue]
  simpa only [RingHom.comp_apply] using this

include hxy in
def coordEvalRed :
    (W.map (residue 𝒪)).toAffine.CoordinateRing →+* ResidueField Λ :=
  AdjoinRoot.lift (eval₂RingHom (ResidueField.map j) (residue Λ x)) (residue Λ y)
    (eval₂_polynomial_of_equation (W.map (residue 𝒪)) (ResidueField.map j)
      (equation_residue_of_equation W j hxy))

theorem coordReduce_of (q : 𝒪[X]) :
    coordReduce W (AdjoinRoot.of _ q) = AdjoinRoot.of _ (q.map (residue 𝒪)) := by
  rw [← AdjoinRoot.mk_C, coordReduce, CoordinateRing.map_mk, Polynomial.map_C, ← AdjoinRoot.mk_C]
  rfl

theorem coordReduce_root :
    coordReduce W (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.map (residue 𝒪)).toAffine.polynomial := by
  rw [← AdjoinRoot.mk_X, coordReduce, CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]

theorem residue_coordEval (a : W.toAffine.CoordinateRing) :
    residue Λ (coordEval W j hxy a) = coordEvalRed W j hxy (coordReduce W a) := by
  have : (residue Λ).comp (coordEval W j hxy) = (coordEvalRed W j hxy).comp (coordReduce W) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_C, coe_eval₂RingHom, eval₂_C, ResidueField.map_residue]
      · simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_X, coe_eval₂RingHom, eval₂_X]
    · simp only [RingHom.comp_apply, coordReduce_root, coordEval, coordEvalRed,
        AdjoinRoot.lift_root]
  exact congrArg (· a) this

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem coordinateRing_ringHom_ext {S : Type*} [CommRing S]
    {f g : W.toAffine.CoordinateRing →+* S}
    (h₁ : ∀ c : 𝒪, f (algebraMap 𝒪 _ c) = g (algebraMap 𝒪 _ c))
    (h₂ : f (CoordinateRing.mk W (C X)) = g (CoordinateRing.mk W (C X)))
    (h₃ : f (CoordinateRing.mk W Y) = g (CoordinateRing.mk W Y)) : f = g := by
  have hc : ∀ c : 𝒪, algebraMap 𝒪 W.toAffine.CoordinateRing c =
      AdjoinRoot.of W.toAffine.polynomial (C c) := fun c => by
    rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, hc] using h₁ c
    · simpa only [RingHom.comp_apply, AdjoinRoot.mk_C] using h₂
  · simpa only [AdjoinRoot.mk_X] using h₃

variable (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

include hx in
theorem coordEvalRed_injective : Function.Injective (coordEvalRed W j hxy) := by
  let : Module.Finite (ResidueField 𝒪)[X] (W.map (residue 𝒪)).toAffine.CoordinateRing :=
    Module.Finite.of_basis (CoordinateRing.basis (W.map (residue 𝒪)).toAffine)
  let : Algebra.IsIntegral (ResidueField 𝒪)[X] (W.map (residue 𝒪)).toAffine.CoordinateRing :=
    Algebra.IsIntegral.of_finite _ _
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_under_eq_bot (R := (ResidueField 𝒪)[X])
  ext p
  simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
    AdjoinRoot.algebraMap_eq, coordEvalRed, AdjoinRoot.lift_of]
  exact map_eq_zero_iff _ hx

include hx in
theorem isUnit_coordEval (s : (gaussPrime W).primeCompl) : IsUnit (coordEval W j hxy s) := by
  by_contra hs
  have h0 : residue Λ (coordEval W j hxy s) = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hs)
  rw [residue_coordEval] at h0
  exact s.2 (RingHom.mem_ker.2 ((map_eq_zero_iff _ (coordEvalRed_injective W j hxy hx)).1 h0))

def gaussLift : gaussRing W →+* Λ :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W)
    (isUnit_coordEval W j hxy hx)

theorem gaussLift_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussLift W j hxy hx (algebraMap _ _ a) = coordEval W j hxy a :=
  IsLocalization.lift_eq _ _

theorem gaussLift_algebraMap_base (c : 𝒪) :
    gaussLift W j hxy hx (algebraMap 𝒪 (gaussRing W) c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussLift_algebraMap, coordEval_algebraMap]

instance isLocalHom_gaussLift : IsLocalHom (gaussLift W j hxy hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussPrime W).primeCompl a
  dsimp only at ha ⊢
  have hspec := IsLocalization.mk'_spec (gaussRing W) r s
  have hr : IsUnit (coordEval W j hxy r) := by
    have := congrArg (gaussLift W j hxy hx) hspec
    rw [map_mul, gaussLift_algebraMap, gaussLift_algebraMap] at this
    rw [← this]
    exact ha.mul (isUnit_coordEval W j hxy hx s)
  have hr' : r ∈ (gaussPrime W).primeCompl := by
    intro hP
    have h0 : coordReduce W r = 0 := hP
    have h1 : residue Λ (coordEval W j hxy r) = 0 := by rw [residue_coordEval, h0, map_zero]
    exact (residue_ne_zero_iff_isUnit _).2 hr h1
  have hu : IsUnit (IsLocalization.mk' (gaussRing W) r s *
      algebraMap W.toAffine.CoordinateRing (gaussRing W) (s : W.toAffine.CoordinateRing)) := by
    rw [hspec]; exact IsLocalization.map_units _ ⟨r, hr'⟩
  exact isUnit_of_mul_isUnit_left hu

def fieldEvalRed : (W.map (residue 𝒪)).toAffine.FunctionField →+* ResidueField Λ :=
  IsFractionRing.lift (coordEvalRed_injective W j hxy hx)

theorem residueField_map_gaussLift :
    ResidueField.map (gaussLift W j hxy hx) = (fieldEvalRed W j hxy hx).comp (gaussResidue W) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (W.toAffine.CoordinateRing ⧸ gaussPrime W))
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
  have e : algebraMap W.toAffine.CoordinateRing (gaussPrime W).ResidueField a =
      residue (gaussRing W) (algebraMap _ (gaussRing W) a) := by
    rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime (gaussPrime W))
      (gaussPrime W).ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rw [e, ResidueField.map_residue, gaussLift_algebraMap, gaussResidue_residue, fieldEvalRed,
    IsFractionRing.lift_algebraMap, residue_coordEval]

theorem fieldEvalRed_genX : fieldEvalRed W j hxy hx (genX (W.map (residue 𝒪))) = residue Λ x := by
  rw [genX, fieldEvalRed, IsFractionRing.lift_algebraMap, coordEvalRed, AdjoinRoot.lift_mk]
  simp

theorem fieldEvalRed_genY : fieldEvalRed W j hxy hx (genY (W.map (residue 𝒪))) = residue Λ y := by
  rw [genY, fieldEvalRed, IsFractionRing.lift_algebraMap, coordEvalRed, AdjoinRoot.lift_mk]
  simp

theorem fieldEvalRed_algebraMap (c : ResidueField 𝒪) :
    fieldEvalRed W j hxy hx (algebraMap (ResidueField 𝒪) _ c) = ResidueField.map j c := by
  rw [IsScalarTower.algebraMap_apply (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.CoordinateRing,
    fieldEvalRed, IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply (ResidueField 𝒪)
      (ResidueField 𝒪)[X], AdjoinRoot.algebraMap_eq, coordEvalRed, AdjoinRoot.lift_of]
  simp

section Fraction

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (M : Type*) [Field M]
  [Algebra Λ M]

theorem comp_algebraMap_gaussLift (σ : (W.baseChange K).toAffine.FunctionField →+* M)
    (hσ : ∀ c : 𝒪, σ (algebraMap 𝒪 _ c) = algebraMap Λ M (j c))
    (hX : σ (genX (W.baseChange K)) = algebraMap Λ M x)
    (hY : σ (genY (W.baseChange K)) = algebraMap Λ M y) :
    σ.comp (algebraMap (gaussRing W) _) = (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
  apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
  apply coordinateRing_ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hσ, gaussLift_algebraMap_base]
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussX, algebraMap_gaussX, hX]
    simp
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussY, algebraMap_gaussY, hY]
    simp

end Fraction
end

section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section AlgPts

variable (E : WeierstrassCurve F) (L : Type*) {M : Type*} [Field L] [Algebra F L] [Field M]
  [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq M]

def TransOver : (E.baseChange M).toAffine.Point → Prop
  | .zero => False
  | .some x _ _ => Transcendental L x

def algPts : AddSubgroup (E.baseChange M).toAffine.Point :=
  (Point.map (W' := E) ((algebraicClosure L M).val.restrictScalars F)).range

omit [DecidableEq M] in
theorem isIntegral_y {x y : M} (h : (E.baseChange M).toAffine.Equation x y)
    (hx : x ∈ algebraicClosure L M) : y ∈ algebraicClosure L M := by
  set S := algebraicClosure L M
  have e := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  have hc : ∀ c : F, algebraMap F M c ∈ S := fun c => by
    rw [IsScalarTower.algebraMap_apply F L M]; exact S.algebraMap_mem _
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : S, (c₁ : M) = algebraMap F M E.a₁ * x + algebraMap F M E.a₃ :=
    ⟨⟨_, S.add_mem (S.mul_mem (hc _) hx) (hc _)⟩, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : S, (c₀ : M) = x ^ 3 + algebraMap F M E.a₂ * x ^ 2 +
      algebraMap F M E.a₄ * x + algebraMap F M E.a₆ :=
    ⟨⟨_, S.add_mem (S.add_mem (S.add_mem (pow_mem hx 3)
      (S.mul_mem (hc _) (pow_mem hx 2))) (S.mul_mem (hc _) hx)) (hc _)⟩, rfl⟩
  have hy : IsIntegral S y := by
    refine ⟨X ^ 2 + C c₁ * X - C c₀, ?_, ?_⟩
    · have : (X ^ 2 + C c₁ * X - C c₀ : S[X]) = X ^ 2 + (C c₁ * X - C c₀) := by ring
      rw [this]
      exact monic_X_pow_add (by compute_degree!)
    · have key : y ^ 2 + (algebraMap F M E.a₁ * x + algebraMap F M E.a₃) * y -
          (x ^ 3 + algebraMap F M E.a₂ * x ^ 2 + algebraMap F M E.a₄ * x + algebraMap F M E.a₆) =
            0 := by linear_combination e
      simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
        IntermediateField.algebraMap_apply, hc₁, hc₀]
      exact key
  exact mem_algebraicClosure_iff'.2 (isIntegral_trans (R := L) (A := S) y hy)

theorem mem_algPts_iff_of_ne_zero {x y : M} (h : (E.baseChange M).toAffine.Nonsingular x y) :
    (Point.some x y h) ∈ algPts E L ↔ IsAlgebraic L x := by
  constructor
  · rintro ⟨P, hP⟩
    cases P with
    | zero => exact absurd hP (Point.some_ne_zero h).symm
    | some u v h' =>
      rw [Point.map_some, Point.some.injEq] at hP
      rw [← hP.1]
      exact mem_algebraicClosure_iff.1 u.2
  · intro hx
    have hx' := mem_algebraicClosure_iff.2 hx
    have hy := isIntegral_y E L h.1 hx'
    have h' : (E.baseChange (algebraicClosure L M)).toAffine.Nonsingular ⟨x, hx'⟩ ⟨y, hy⟩ :=
      (E.toAffine.baseChange_nonsingular (f := (algebraicClosure L M).val.restrictScalars F)
        (algebraicClosure L M).val.injective _ _).mp h
    exact ⟨.some _ _ h', by rw [Point.map_some]; rfl⟩

end AlgPts

section Trans

variable (E : WeierstrassCurve F) {L M : Type*} [Field L] [Algebra F L] [Field M]
  [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq L] [DecidableEq M]

variable {E} in
theorem TransOver.isGenPt {P : (E.baseChange M).toAffine.Point} (h : TransOver E L P) :
    IsGenPt E P := by
  cases P with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.of_tower_top F h

theorem transOver_of_notMem {P : (E.baseChange M).toAffine.Point} (h : P ∉ algPts E L) :
    TransOver E L P := by
  cases P with
  | zero => exact h (zero_mem _)
  | some x y hxy => exact fun hx => h ((mem_algPts_iff_of_ne_zero E L hxy).2 hx)

theorem notMem_of_transOver {P : (E.baseChange M).toAffine.Point} (h : TransOver E L P) :
    P ∉ algPts E L := by
  cases P with
  | zero => exact h.elim
  | some x y hxy => exact fun hm => h ((mem_algPts_iff_of_ne_zero E L hxy).1 hm)

theorem map_mem_algPts (A : (E.baseChange L).toAffine.Point) :
    Point.map (IsScalarTower.toAlgHom F L M) A ∈ algPts E L := by
  refine ⟨Point.map ((IsScalarTower.toAlgHom L L (algebraicClosure L M)).restrictScalars F) A, ?_⟩
  rw [Point.map_map]
  congr 1

variable {E} in
theorem TransOver.add_left {B : (E.baseChange M).toAffine.Point} (hB : TransOver E L B)
    (A : (E.baseChange L).toAffine.Point) :
    TransOver E L (Point.map (IsScalarTower.toAlgHom F L M) A + B) := by
  refine transOver_of_notMem E fun hm => notMem_of_transOver E hB ?_
  have := sub_mem hm (map_mem_algPts E A)
  rwa [add_sub_cancel_left] at this

variable {E} in
theorem TransOver.neg {B : (E.baseChange M).toAffine.Point} (hB : TransOver E L B) :
    TransOver E L (-B) := by
  cases B with
  | zero => exact hB.elim
  | some x y h => exact hB

end Trans

section BaseChange

omit [Field F] in
theorem baseChange_baseChange {F : Type*} [CommRing F] (E : WeierstrassCurve F) (A B : Type*)
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B] :
    (E.baseChange A).baseChange B = E.baseChange B := by
  show E.map ((algebraMap A B).comp (algebraMap F A)) = E.map (algebraMap F B)
  rw [← IsScalarTower.algebraMap_eq]

end BaseChange

section Universal

variable (E : WeierstrassCurve F) [E.IsElliptic]

abbrev univField : Type u := (E.baseChange E.toAffine.FunctionField).toAffine.FunctionField

def univPt₁ : (E.baseChange (univField E)).toAffine.Point :=
  Point.map (IsScalarTower.toAlgHom F E.toAffine.FunctionField (univField E)) (genericPoint E)

def univPt₂ : (E.baseChange (univField E)).toAffine.Point :=
  pointCongr (baseChange_baseChange E _ _) (genericPoint (E.baseChange E.toAffine.FunctionField))

theorem isGenPt_univPt₁ : IsGenPt E (univPt₁ E) :=
  isGenPt_map E _ (transcendental_genX E)

theorem transOver_univPt₂ : TransOver E E.toAffine.FunctionField (univPt₂ E) := by
  rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

theorem isGenPt_univPt₂ : IsGenPt E (univPt₂ E) := (transOver_univPt₂ E).isGenPt

theorem isGenPt_univPt₁₂ : IsGenPt E (univPt₁ E + univPt₂ E) := by
  have := (transOver_univPt₂ E).add_left (genericPoint E)
  exact this.isGenPt

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]
  (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)

def UnivAdd : Prop :=
  Point.map (genEval E (univPt₁ E + univPt₂ E) (isGenPt_univPt₁₂ E)) Q =
    Point.map (genEval E (univPt₁ E) (isGenPt_univPt₁ E)) Q +
      Point.map (genEval E (univPt₂ E) (isGenPt_univPt₂ E)) Q

theorem map_genEval_map {L M : Type*} [Field L] [Algebra F L] [Field M] [Algebra F M]
    [DecidableEq L] [DecidableEq M] (τ : L →ₐ[F] M) {P : (E.baseChange L).toAffine.Point}
    (hP : IsGenPt E P) (hP' : IsGenPt E (Point.map τ P)) :
    Point.map (genEval E (Point.map τ P) hP') Q = Point.map τ (Point.map (genEval E P hP) Q) := by
  rw [Point.map_map, ← genEval_map E τ hP]

theorem halfUniversal (hQ : UnivAdd Q) {L M : Type*} [Field L] [Algebra F L] [Field M]
    [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq L] [DecidableEq M]
    (A : (E.baseChange L).toAffine.Point) (hA : IsGenPt E A) (B : (E.baseChange M).toAffine.Point)
    (hB : TransOver E L B) :
    Point.map (genEval E _ (hB.add_left A).isGenPt) Q =
      Point.map (genEval E _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA)) Q +
        Point.map (genEval E B hB.isGenPt) Q := by
  set Fv := E.toAffine.FunctionField
  set σA := genEval E A hA
  letI : Algebra Fv L := σA.toRingHom.toAlgebra
  letI : Algebra Fv M := ((algebraMap L M).comp σA.toRingHom).toAlgebra
  haveI : IsScalarTower Fv L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F Fv M := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap F M c = algebraMap L M (σA (algebraMap F Fv c))
    rw [σA.commutes, ← IsScalarTower.algebraMap_apply]
  cases B with
  | zero => exact hB.elim
  | some x y h =>
  have h' : ((E.baseChange Fv).baseChange M).toAffine.Nonsingular x y := by
    rw [baseChange_baseChange]; exact h
  have hB' : IsGenPt (E.baseChange Fv) (Point.some x y h') :=
    Transcendental.restrictScalars (R := Fv) (S := L) σA.toRingHom.injective hB
  set τ₀ := genEval (E.baseChange Fv) _ hB'
  set τ : univField E →ₐ[F] M := τ₀.restrictScalars F
  have c₂ : Point.map τ (univPt₂ E) = Point.some x y h := by
    rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]
    exact ⟨genEval_genX (E.baseChange Fv) _ hB', genEval_genY (E.baseChange Fv) _ hB'⟩
  have hcomp : τ.comp (IsScalarTower.toAlgHom F Fv (univField E)) =
      (IsScalarTower.toAlgHom F L M).comp σA := by
    exact AlgHom.ext fun f => τ₀.commutes f
  have c₁ : Point.map τ (univPt₁ E) = Point.map (IsScalarTower.toAlgHom F L M) A := by
    rw [univPt₁, Point.map_map, hcomp, ← Point.map_map, map_genEval_genericPoint]
  have e := congrArg (Point.map τ) hQ
  rw [map_add (f := _), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E))] at e
  rw [genEval_congr E (by rw [map_add (f := _), c₁, c₂]) _ (hB.add_left A).isGenPt,
    genEval_congr E c₁ _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA),
    genEval_congr E c₂ _ hB.isGenPt] at e
  exact e

end Universal

section Criterion

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)

theorem respectsAdd_of_univAdd (hQ : UnivAdd Q) : RespectsAdd E E' Q := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  set M := (E.baseChange L).toAffine.FunctionField
  set ι := IsScalarTower.toAlgHom F L M
  set T : (E.baseChange M).toAffine.Point :=
    pointCongr (baseChange_baseChange E L M) (genericPoint (E.baseChange L))
  have hT : TransOver E L T := by
    simp only [T, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
    exact transcendental_genX _
  have hnT := hT.neg
  have hU := hnT.add_left P₂
  have e₁ := halfUniversal Q hQ P₁ h₁ _ hU
  have e₂ := halfUniversal Q hQ P₂ h₂ _ hnT
  have e₃ := halfUniversal Q hQ (P₁ + P₂) h₃ _ hnT
  have hsum : Point.map ι P₁ + (Point.map ι P₂ + -T) = Point.map ι (P₁ + P₂) + -T := by
    rw [map_add (f := _), add_assoc]
  rw [genEval_congr E hsum _ (hnT.add_left (P₁ + P₂)).isGenPt, e₃, e₂] at e₁
  have key : Point.map (genEval E _ (isGenPt_map E ι h₃)) Q =
      Point.map (genEval E _ (isGenPt_map E ι h₁)) Q +
        Point.map (genEval E _ (isGenPt_map E ι h₂)) Q := by
    have := congrArg (· - Point.map (genEval E (-T) hnT.isGenPt) Q) e₁
    simp only [add_sub_cancel_right] at this
    rw [this]
    abel
  rw [map_genEval_map Q ι h₃, map_genEval_map Q ι h₁, map_genEval_map Q ι h₂, ← map_add (f := _)] at key
  exact Point.map_injective ι key

end Criterion
end

end GroundTheory.Global
