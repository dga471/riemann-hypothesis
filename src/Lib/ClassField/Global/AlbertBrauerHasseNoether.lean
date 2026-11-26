import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.HeckeL.EulerProduct
import Lib.General.NumberTheory.SUnitsAndClassNumber
import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation

/-!
# Real place symbols, the second inequality and Albert–Brauer–Hasse–Noether

Let `K` be a number field and let `Γ` act as the Galois group of `Ω/K`, where `Ω` (`New.Ω`) is the
algebraic closure of `ℚ`. The first section treats complex conjugations in `Γ` and the symbols of
totally positive elements of `K`. The second section proves the second inequality for a Galois
extension `L / K`; the proof compares Dirichlet densities of primes of degree one. In the last
section `L` is the field cut out by a character `χ` of `Γ`; it treats local norms and Artin symbols,
proves Hasse's norm theorem in prime degree when the real places of `K` stay real in `L` and deduces
the Albert–Brauer–Hasse–Noether theorem.

## Main definitions and results

* `New.IsTotallyPositive.exists_resH2_cyclicClass_eq_zero`: the symbol of a totally positive `x`
  restricts to zero on an open subgroup containing every complex conjugation.
* `New.second_inequality`: for `L / K` Galois, an open subgroup `W` of the finite ideles that
  contains the totally positive principal ideles and the norms from `L` has index at most `[L : K]`.
  Each of its cosets contains the uniformiser idele `ϖ_v` for infinitely many `v` of prime norm
  (`New.frequently_prime_uniformizer_div_mem_of_adeleNorm_mem`).
* `New.exists_hasPrimeDensity_addChar_uniformizer`: the values of a character `f` of the quotient by
  `W` at the `ϖ_v` have mean `1 - m` if `f` is trivial and `-m` otherwise, for some `m : ℕ`.
* `New.exists_localNorm_of_abelianLift_artinAt`: an element of a completion with trivial local
  symbol is a local norm.
* `New.albert_brauer_hasse_noether`: a class in H²(Γ, Ωˣ) is zero if it dies at every finite place
  and over a finite extension in which the real places stay real.

Notions from other files:
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K as its Galois group, with
  open stabilisers.
* `New.QZChar.abelianLift`: The homomorphism induced by the continuous character χ on the
  topological abelianisation of Γ, with values in ℚ/ℤ written multiplicatively.
* `New.artinAt`: The local Artin map K_v^× → Γ^ab: the Artin map to the abelianised decomposition
  group of the chosen place above v, followed by the map induced by inclusion.

## Relation to the literature

Known result: Global class field theory, comprising Albert–Brauer–Hasse–Noether, reciprocity,
existence and norms. Only finite ideles are used, with real places handled by total positivity, and
existence is proved only for totally complex fields. Reciprocity starts from cyclotomic characters
of prime conductor, with the auxiliary character chosen by B. H. Neumann's covering lemma. Source:
J. S. Milne, Class Field Theory (v4.03, 2020), VI 4.9, VII 4–9, VIII 4; Tate, Global class field
theory, in Cassels–Fröhlich 1967, ch. VII; H. Hasse, Die Struktur der R. Brauerschen
Algebrenklassengruppe, Math. Ann. 107 (1933) (reciprocity from the sum formula).

See also `Lib.ClassField.Places.LocalFields` and `Lib.ClassField.HeckeL.ContinuationAtOne`.
-/

/-!
## Symbols of totally positive elements at the real places

`New.IsComplexConj c` says that `c` acts as complex conjugation under some embedding of `Ω` in `ℂ`.
`New.cyclicClass _ χ w` is the class in `H²` of the cocycle `(g, h) ↦ carry (χ g) (χ h) • w`, which
stands for `δχ ∪ w`. For `w` coming from `x : Kˣ` with coefficients `Ωˣ`, it is the symbol `(χ, x)`.
-/

namespace New

open NumberField Complex DiscreteUnits Cohomology QZChar DiscreteModule ComplexEmbedding NeZero
  PadicInt Units

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K]

/-- In a totally complex field `K` every element `x` is totally positive (`New.IsTotallyPositive`:
`φ x > 0` for every ring homomorphism `φ : K →+* ℝ`), since there is no such `φ`. -/
lemma Cohomology.isTotallyPositive_of_isTotallyComplex [t : IsTotallyComplex K] (x : K) :
    IsTotallyPositive x := by
  intro φ
  -- There is no `φ : K →+* ℝ`: it would give a real embedding of `K` in `ℂ`.
  refine (t.complexEmbedding_not_isReal (ofRealHom.comp φ) ?_).elim
  ext
  simp

variable {c : Γ} [Algebra K Ω] [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω]

/-- Let `c` act on `Ω` as complex conjugation under the embedding `j : Ω →+* ℂ` (`hj`). Then `j`
restricted to `K` is a real embedding, since `c` fixes `K`. -/
lemma Cohomology.isReal_comp_algebraMap {j : Ω →+* ℂ} (hj : ∀ x : Ω, j (c • x) = star (j x)) :
    IsReal (j.comp (algebraMap K Ω)) := by
  ext
  simp [← hj, ← star_def]

variable (Γ) in
/-- If the number field `K` has a real place `w`, some `c` in `Γ` acts on the field `Ω` (`New.Ω`,
the algebraic closure of `ℚ`) as complex conjugation (`New.IsComplexConj`: under some embedding
`j : Ω →+* ℂ`, `j (c • x)` is the complex conjugate of `j x`). -/
lemma exists_isComplexConj [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) :
    ∃ c : Γ, IsComplexConj c := by
  -- An extension `j` of the real embedding to `Ω` and its conjugate agree on `K`, so they differ
  -- by an element `c` of `Γ`.
  let j : Ω →+* ℂ := lift Ω w.embedding
  have h_agree : j.comp (algebraMap K Ω) = (star j).comp (algebraMap K Ω) := by aesop
  obtain ⟨c, hc⟩ := exists_apply_smul_eq_of_comp_algebraMap_eq Γ (K := K) j (star j) h_agree
  exact ⟨c, j, hc⟩

include G in
/-- A complex conjugation `c` (`hc`) is an involution, as `Γ` acts faithfully on `Ω`. -/
lemma IsComplexConj.mul_self (hc : IsComplexConj c) : c * c = 1 := by
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
  -- `c * c` acts on `Ω` as the identity: `j` turns it into conjugating twice.
  refine G.faithful.eq_of_smul_eq_smul fun x : Ω ↦ j.injective ?_
  simp [mul_smul, hj]

/-- For a character `χ` of `Γ` and a totally positive `x : Kˣ` there is an open subgroup `U` that
(a) contains every complex conjugation (the real places of `K` stay real in its fixed field)
and (b) on which the symbol `(χ, x) ∈ H²(Γ, Ωˣ)` restricts to zero. Here `Ω` is the field `New.Ω`,
the algebraic closure of `ℚ`, on which `Γ` acts as the Galois group over `K`. -/
lemma IsTotallyPositive.exists_resH2_cyclicClass_eq_zero {χ : ↥(QZChar Γ)} {x : Kˣ}
    (hx : IsTotallyPositive x.val) :
    ∃ U : OpenSubgroup Γ,
      (∀ c : Γ, IsComplexConj c → c ∈ U) ∧
      (unitsModule Γ).resH2 U
        (cyclicClass (unitsModule Γ).ρ χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x))) = 0 := by
  -- Take a square root `y` of `x` in `Ω`. The symbol `(χ, y ^ 2)` dies on the elements that fix
  -- `y` and lie in the kernel of `χ + χ`, and every complex conjugation is among them.
  obtain ⟨y, hy⟩ : ∃ y : DiscreteUnits Ω, 2 • y = (DiscreteUnits.ofBase Γ Ω (.ofMul x)).val :=
    exists_nsmul _ two_ne_zero
  let U : OpenSubgroup Γ := ⟨_, G.isOpen_stabilizer (y.toMul : Ω)⟩ ⊓ ⟨_, isOpen_ker (χ + χ)⟩
  have h_on_U (g : U.toSubgroup) : (unitsModule Γ).ρ g y = y ∧ 2 • χ.val g = 0 := by
    obtain ⟨hg_fix, hg_ker⟩ := g.property
    exact ⟨DiscreteUnits.ext hg_fix, (two_nsmul _).trans hg_ker⟩
  refine ⟨U, fun c hc ↦ ⟨?_, ?_⟩, resH2_cyclicClass_eq_zero hy h_on_U⟩
  · -- The square of `j y` is the value of `x` at a real embedding, which is positive; so `j y` is
    -- real and `c` fixes `y`.
    obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
    let φ : K →+* ℝ := (isReal_comp_algebraMap hj).embedding
    have h_sq : j (y.toMul : Ω) ^ 2 = φ x := by
      simpa [φ, toMul_nsmul, val_pow_eq_pow_val] using
        congrArg (fun z : DiscreteUnits Ω ↦ j (z.toMul : Ω)) hy
    have h_real : (j (y.toMul : Ω)).im = 0 := by simpa [← sq_nonneg_iff, h_sq] using (hx φ).le
    exact j.injective ((hj _).trans (conj_eq_iff_im.mpr h_real))
  · -- `χ c + χ c = χ (c * c) = 0`, as `c` is an involution.
    exact map_mul_eq_one (toHom χ) hc.mul_self

/-- A totally complex field `K` has no complex conjugation `c` (`hc`) in `Γ`: it would give a real
embedding of `K`. -/
lemma IsComplexConj.false_of_isTotallyComplex (hc : IsComplexConj c) [t : IsTotallyComplex K] :
    False := by
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
  exact t.complexEmbedding_not_isReal _ (isReal_comp_algebraMap hj)

omit [TopologicalSpace Γ] in
/-- A complex conjugation `c` (`hc`) inverts the `N`-th roots of unity: the cyclotomic character
mod `N` (`New.cyclotomicCharMod`) is `-1` at `c`. Here `Ω` is the field `New.Ω`, the algebraic
closure of `ℚ`. -/
lemma IsComplexConj.cyclotomicCharMod_eq_neg_one (hc : IsComplexConj c) {N : ℕ} [NeZero N] :
    cyclotomicCharMod Ω N c = -1 := by
  -- For an `N`-th root of unity `ζ`, both `c • ζ` and `ζ ^ (N - 1)` are inverse to `ζ`.
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
  have h_val : (New.cyclotomicCharMod Ω N c).val = (N - 1 : ℕ) := by
    refine cyclotomicCharMod_eq_iff.mpr fun ζ hζ ↦
      left_inv_eq_right_inv (a := ζ) (j.injective ?_) ?_
    · have h_norm : ‖j ζ‖ = 1 :=
        norm_eq_one_of_pow_eq_one (by simp [← map_pow, hζ]) (NeZero.ne N)
      simp [hj, conj_mul', h_norm]
    · rw [mul_pow_sub_one (NeZero.ne N), hζ]
  ext
  simp [h_val, NeZero.pos, ZMod.natCast_self]

omit [TopologicalSpace Γ] in
/-- The `l`-adic cyclotomic character `New.cyclotomicChar` is `-1` at a complex conjugation `c`
(`hc`). -/
lemma IsComplexConj.cyclotomicChar_eq_neg_one (hc : IsComplexConj c) (l : ℕ) [Fact (Nat.Prime l)] :
    cyclotomicChar Ω l c = -1 := by
  -- The value is `-1` modulo every `l ^ r`.
  refine ext (ext_of_toZModPow.mp fun r ↦ ?_)
  simpa [cyclotomicCharMod_prime_pow_eq, ← val_inj] using
    hc.cyclotomicCharMod_eq_neg_one (N := l ^ r)

end New

/-! ## The second inequality and equidistribution of primes in norm cosets -/

section SecondInequality

open Complex Module QuotientGroup Subgroup AddChar Finset DFunLike New

attribute [local instance low] Fintype.ofFinite

/-- Let ψ and finitely many c_i be homomorphisms from a monoid to ℂ, with ψ(x) = 1 whenever no
c_i(x) is −1. Then ψ times the product of some of the c_i is trivial. -/
lemma New.exists_mul_prod_eq_one {G ι : Type*} [Monoid G] [Fintype ι] (ψ : G →* ℂ) (c : ι → G →* ℂ)
    (h : ∀ x : G, (∀ i : ι, c i x ≠ -1) → ψ x = 1) :
    ∃ T : Finset ι, ψ * T.prod c = 1 := by
  classical
  -- The product `∏ i, (1 + c i x)` vanishes unless `ψ x = 1`, so multiplying it by `ψ x` changes
  -- nothing. Expanded over subsets `T`, this is a linear relation between characters; by their
  -- independence the trivial character, the term `T = ∅` on the left, occurs on the right too.
  by_contra! hne
  have h_expand (x : G) : ∑ T : Finset ι, (T.prod c) x = ∏ i, (1 + c i x) := by
    simp [← powerset_univ, ← prod_one_add]
  have hψ (x : G) : ∏ i, (1 + c i x) = ψ x * ∏ i, (1 + c i x) := by grind [prod_eq_zero_iff]
  have h_coeffs : ∑ T : Finset ι, Finsupp.single (T.prod c) (1 : ℂ) =
      ∑ T : Finset ι, Finsupp.single (ψ * T.prod c) 1 :=
    linearIndependent_monoidHom G ℂ (funext fun x ↦ by simpa [← mul_sum, ← h_expand] using hψ x)
  -- The coefficient of `1` is zero on the right; on the left it counts the `T` with product `1`.
  have h_prod_ne_one : ∀ ⦃T : Finset ι⦄, T.prod c ≠ 1 := by
    simpa [Finsupp.single_apply, hne] using DFunLike.congr_fun h_coeffs 1
  exact h_prod_ne_one prod_empty

variable {K : Type*}
  (L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  {W : Subgroup (𝔸f K)ˣ} (hW_open : W.IsOpen)
  (hW_pos : ∀ x : Kˣ, IsTotallyPositive x.val → principalIdele (x : Kˣ) ∈ W)

include hW_open hW_pos

/-- Let `W` be an open subgroup of the finite ideles (`hW_open`) containing the principal ideles of
the totally positive elements (`hW_pos`), and `f` a character of the quotient by `W`, written
additively (so `f = 0` is the trivial character). The mean of `f` at the uniformiser ideles
(`New.HasPrimeDensity`, Dirichlet density over the finite places) is `1 - m` if `f = 0` and `-m`
otherwise, for some natural number `m`. -/
lemma New.exists_hasPrimeDensity_addChar_uniformizer (f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ) :
    ∃ m : ℕ,
      HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
        ((if f = 0 then 1 else 0) - m) := by
  classical
  split_ifs with hf
  · exact ⟨0, by simp_all [hasPrimeDensity_const]⟩
  open scoped NumberField nonZeroDivisors WithZero in
  open TauCeti TauCeti.GlobalNumberFields IsDedekindDomain in
  have h_res : ∃ m : ℕ,
      HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
        (-(m : ℂ)) := by
    let ψ : (𝔸f K)ˣ →* ℂˣ := (f.toMonoidHom.comp (mk' W)).toHomUnits
    have hψ_val (a : (𝔸f K)ˣ) : (ψ a : ℂ) = f (Additive.ofMul ⟦a⟧) := rfl
    have hW_le : W ≤ ψ.ker := fun a ha ↦ Units.ext (by simp [hψ_val, (eq_one_iff a).mpr ha])
    have hψ_ne : ψ ≠ 1 := fun h1 ↦ hf <| AddChar.ext _ _ <| Quot.ind fun a ↦
      congrArg Units.val (DFunLike.congr_fun h1 a)
    -- Choose a finite set `T` of places outside which local units lie in `W`, and a level `e v`
    -- at each `v ∈ T` so that `1 + v ^ (e v) 𝒪_v ⊆ W`.
    obtain ⟨T, hT⟩ := exists_finset_cover_mulSupport_ideleAt hW_open W.one_mem
    have hW_unram (v : FinPlace K) (hv : v ∉ T) (u : (LocField v)ˣ) (hu : Valued.v u.val = 1) :
        locIdele v u ∈ W := by
      by_contra hnot
      obtain ⟨w, hw, hw_ne⟩ : ∃ w ∈ T, ideleAt w (locIdele v u) ≠ 1 := by
        simpa using hT ⟨locIdele_mem_idelesUnitOff hu, hnot⟩
      exact hw_ne (ideleAt_locIdele_of_ne (ne_of_mem_of_not_mem hw hv) u)
    have h_level (v : FinPlace K) : ∃ e : ℕ, 1 ≤ e ∧
        ∀ u : (LocField v)ˣ, Valued.v (u.val - 1) ≤ WithZero.exp (-(e : ℤ)) →
          locIdele v u ∈ W := by
      have hcont : Continuous (locIdele v) := by
        have hval : Continuous (fun u : (LocField v)ˣ ↦ ((locIdele v u : (𝔸f K)ˣ) : 𝔸f K)) := by
          have : (fun u : (LocField v)ˣ ↦ ((locIdele v u : (𝔸f K)ˣ) : 𝔸f K)) =
              fun u ↦ 1 + singleAdele v (u.val - 1) := by
            funext u
            ext w
            by_cases hw : w = v
            · subst hw; simp [locIdele, singleAdele]
            · simp [locIdele, singleAdele]
          rw [this]
          exact continuous_const.add ((continuous_singleAdele v).comp
            (Units.continuous_val.sub continuous_const))
        refine continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨hval, ?_⟩)
        exact MulOpposite.continuous_op.comp (show Continuous fun u : (LocField v)ˣ ↦
            ((locIdele v u⁻¹ : (𝔸f K)ˣ) : 𝔸f K) from hval.comp continuous_inv)
      have hnhds : (locIdele v) ⁻¹' (W : Set (𝔸f K)ˣ) ∈ nhds (1 : (LocField v)ˣ) :=
        (hW_open.preimage hcont).mem_nhds (by simp [W.one_mem])
      rw [nhds_induced, Filter.mem_comap] at hnhds
      obtain ⟨U, hU, hUW⟩ := hnhds
      rw [nhds_prod_eq, Filter.mem_prod_iff] at hU
      obtain ⟨U₁, hU₁, U₂, hU₂, hU12⟩ := hU
      have hU₁' : {y : LocField v | y + 1 ∈ U₁} ∈ nhds (0 : LocField v) :=
        (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU₁)
      have hU₂' : {y : LocField v | MulOpposite.op (y + 1)⁻¹ ∈ U₂} ∈ nhds (0 : LocField v) := by
        have h2 : ContinuousAt (fun y : LocField v ↦ MulOpposite.op (y + 1)⁻¹) 0 := by
          fun_prop (disch := simp)
        exact h2.preimage_mem_nhds (by simpa using hU₂)
      obtain ⟨γ₁, hγ₁⟩ := Valued.mem_nhds_zero.mp hU₁'
      obtain ⟨γ₂, hγ₂⟩ := Valued.mem_nhds_zero.mp hU₂'
      obtain ⟨k₁, hk₁⟩ := WithZero.ne_zero_iff_exists.mp
        (show MonoidWithZeroHom.ValueGroup₀.embedding γ₁.val ≠ 0 from
          (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective).mpr
            γ₁.ne_zero)
      obtain ⟨k₂, hk₂⟩ := WithZero.ne_zero_iff_exists.mp
        (show MonoidWithZeroHom.ValueGroup₀.embedding γ₂.val ≠ 0 from
          (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective).mpr
            γ₂.ne_zero)
      let n₁ : ℤ := Multiplicative.toAdd k₁
      let n₂ : ℤ := Multiplicative.toAdd k₂
      let e : ℕ := max 1 (max (-n₁).toNat (-n₂).toNat + 1)
      refine ⟨e, le_max_left _ _, fun u hu ↦ hUW (hU12 ⟨?_, ?_⟩)⟩
      · have hlt : Valued.v.restrict (u.val - 1) < γ₁.val := by
          rw [Valuation.restrict_lt_iff_lt_embedding]
          refine hu.trans_lt ?_
          rw [← hk₁]
          change WithZero.exp (-(e : ℤ)) < WithZero.exp n₁
          exact WithZero.exp_lt_exp.mpr (by omega)
        simpa using hγ₁ hlt
      · have hlt : Valued.v.restrict (u.val - 1) < γ₂.val := by
          rw [Valuation.restrict_lt_iff_lt_embedding]
          refine hu.trans_lt ?_
          rw [← hk₂]
          change WithZero.exp (-(e : ℤ)) < WithZero.exp n₂
          exact WithZero.exp_lt_exp.mpr (by omega)
        simpa [u.inv_eq_val_inv] using hγ₂ hlt
    choose e he1 heW using h_level
    -- Build the modulus `𝔪` with finite part `∏ v ∈ T, v ^ (e v)` and all real places.
    let 𝔪 : Modulus K :=
      ⟨∏ v ∈ T, v.asIdeal ^ e v,
        Finset.prod_ne_zero_iff.mpr fun v _ ↦ pow_ne_zero (e v) v.ne_bot,
        (narrowModulus K).infinitePart⟩
    have h𝔪_supp (v : FinPlace K) : v ∈ 𝔪.support ↔ v ∈ T := by
      rw [Modulus.mem_support_iff]
      simp only [𝔪, Ideal.dvd_iff_le]
      constructor
      · intro hle
        rw [v.isPrime.prod_le] at hle
        obtain ⟨w, hwT, hw⟩ := hle
        have := v.isPrime.le_of_pow_le hw
        have : w = v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top this)
        exact this ▸ hwT
      · intro hvT
        exact (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem _ hvT)).trans
          (Ideal.pow_le_self (by have := he1 v; omega))
    have he_le (v : FinPlace K) (hv : v ∈ T) : e v ≤ 𝔪.exponent v := by
      have hdvd : v.asIdeal ^ e v ∣ 𝔪.finitePart := Finset.dvd_prod_of_mem _ hv
      rw [Modulus.exponent_def]
      have h1 : (Associates.mk v.asIdeal).count (Associates.mk (v.asIdeal ^ e v)).factors ≤
          (Associates.mk v.asIdeal).count (Associates.mk 𝔪.finitePart).factors :=
        Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr 𝔪.finitePart_ne_zero)
          v.associates_irreducible (Associates.mk_le_mk_of_dvd hdvd)
      rwa [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot)
        v.associates_irreducible, Associates.count_self v.associates_irreducible, mul_one] at h1
    -- Divisor homomorphism from finite ideles to fractional ideals.
    obtain ⟨d, hd_int, hd_ker, hd_unif, hd_prin⟩ := exists_idele_divisor_hom (K := K)
    -- Map `idealsPrimeTo 𝔪` into `(𝔸f K)ˣ` by taking `uniformizer v ^ count_v(I)`.
    have h_supp_fin (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
        (Function.mulSupport fun v : FinPlace K ↦
          locIdele v (uniformizer v ^ FractionalIdeal.count K v I.val)).Finite := by
      have hfin : (Function.support fun v : FinPlace K ↦ FractionalIdeal.count K v I.val).Finite := by
        obtain ⟨a, J, ha0, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I.val
        have hJ0 : J ≠ ⊥ := by
          intro hbot
          exact I.ne_zero (by simp [hI, hbot])
        have ha : a ∈ (𝓞 K)⁰ := mem_nonZeroDivisors_of_ne_zero ha0
        have hmem_nf (L : Ideal (𝓞 K)) (hL0 : L ≠ ⊥) (v : FinPlace K)
            (h : (Associates.mk v.asIdeal).count (Associates.mk L).factors ≠ 0) :
            v.asIdeal ∈ (UniqueFactorizationMonoid.normalizedFactors L).toFinset := by
          have hdvd : v.asIdeal ∣ L :=
            (Associates.count_ne_zero_iff_dvd hL0
              (Associates.irreducible_mk.mp v.associates_irreducible)).mp h
          obtain ⟨q, hq, hass⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
            hL0 (Associates.irreducible_mk.mp v.associates_irreducible) hdvd
          exact Multiset.mem_toFinset.mpr (associated_iff_eq.mp hass ▸ hq)
        have hsub : (Function.support fun v : FinPlace K ↦ FractionalIdeal.count K v I.val) ⊆
            (fun v : FinPlace K ↦ v.asIdeal) ⁻¹'
              (((UniqueFactorizationMonoid.normalizedFactors J).toFinset ∪
                (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset :
                  Finset (Ideal (𝓞 K))) : Set (Ideal (𝓞 K))) := by
          intro v hv
          simp only [Function.mem_support] at hv
          have haK : algebraMap (𝓞 K) K a ≠ 0 :=
            map_ne_zero_of_mem_nonZeroDivisors _ (FaithfulSMul.algebraMap_injective (𝓞 K) K) ha
          have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a)⁻¹ =
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a))⁻¹ := by
            refine eq_inv_of_mul_eq_one_left ?_
            rw [← map_mul, inv_mul_cancel₀ haK, map_one]
          have hcnt : FractionalIdeal.count K v I.val =
              ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
                ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) := by
            rw [hI, hsp, FractionalIdeal.count_mul K v
              (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr haK))
              (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0),
              FractionalIdeal.count_inv, FractionalIdeal.count_coeIdeal K v hJ0,
              ← FractionalIdeal.coeIdeal_span_singleton,
              FractionalIdeal.count_coeIdeal K v (by simp [ha0])]
            ring
          rw [hcnt] at hv
          have hne : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 ∨
              (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
            by_contra! h0
            exact hv (by simp [h0.1, h0.2])
          simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_union]
          exact hne.imp (hmem_nf J hJ0 v) (hmem_nf (Ideal.span {a}) (by simp [ha0]) v)
        exact ((Finset.finite_toSet _).preimage
          (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h)).subset hsub
      exact hfin.subset fun v hv ↦ by
        simp only [Function.mem_mulSupport, Function.mem_support] at hv ⊢
        intro h0
        exact hv (by simp [h0])
    let ideleOfIdeal : idealsPrimeTo 𝔪 →* (𝔸f K)ˣ :=
      { toFun I := ∏ᶠ v : FinPlace K,
          locIdele v (uniformizer v ^ FractionalIdeal.count K v (I.1 : FractionalIdeal _ K))
        map_one' := by simp [FractionalIdeal.count_one]
        map_mul' I J := by
          simp only [Subgroup.coe_mul, Units.val_mul,
            FractionalIdeal.count_mul K _ I.1.ne_zero J.1.ne_zero, zpow_add, map_mul]
          exact finprod_mul_distrib (h_supp_fin I.1) (h_supp_fin J.1) }
    have h_d_ideleOfIdeal (I : idealsPrimeTo 𝔪) : d (ideleOfIdeal I) = I.1 := by
      apply Units.ext
      change ((Units.coeHom _).comp d) (∏ᶠ v : FinPlace K, _) = _
      rw [map_finprod ((Units.coeHom _).comp d) (h_supp_fin I.1)]
      have hterm (v : FinPlace K) :
          ((Units.coeHom _).comp d)
            (locIdele v (uniformizer v ^ FractionalIdeal.count K v (I.1 : FractionalIdeal _ K))) =
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^
            FractionalIdeal.count K v (I.1 : FractionalIdeal _ K) := by
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, map_zpow, hd_unif,
          FractionalIdeal.coe_mk0]
      simp_rw [hterm]
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.1.ne_zero
    have h_at_ideleOfIdeal (I : idealsPrimeTo 𝔪) (w : FinPlace K) :
        ideleAt w (ideleOfIdeal I) =
          uniformizer w ^ FractionalIdeal.count K w (I.1 : FractionalIdeal _ K) := by
      change ideleAt w (∏ᶠ v : FinPlace K, _) = _
      rw [map_finprod (ideleAt w) (h_supp_fin I.1),
        finprod_eq_single _ w fun v hv ↦ ideleAt_locIdele_of_ne hv.symm _, ideleAt_locIdele]
    -- Show `ψ.comp ideleOfIdeal` kills `ray 𝔪`.
    have h_ray : ray 𝔪 ≤ (ψ.comp ideleOfIdeal).ker := by
      intro I hI
      rw [mem_ray_iff] at hI
      obtain ⟨x, hx_congr, hxI⟩ := hI
      have hx_pos : IsTotallyPositive x.val := by
        intro φ
        let w : NumberField.InfinitePlace K := .mk (ofRealHom.comp φ)
        have hw : w.IsReal := NumberField.InfinitePlace.isReal_mk_iff.mpr
          (by ext a; simp)
        have hpos := hx_congr.2 ⟨w, hw⟩ (mem_narrowModulus_infinitePart _)
        have hemb : NumberField.InfinitePlace.embedding_of_isReal hw x.val = φ x.val := by
          apply Complex.ofReal_injective
          rw [NumberField.InfinitePlace.embedding_of_isReal_apply,
            NumberField.InfinitePlace.embedding_mk_eq_of_isReal (by ext a; simp)]
          rfl
        rwa [hemb] at hpos
      have h_prin_mem : principalIdele x ∈ W := hW_pos x hx_pos
      let u : (𝔸f K)ˣ := ideleOfIdeal I * (principalIdele x)⁻¹
      have hu_unit : u ∈ idelesUnitOff ∅ := by
        rw [← hd_ker, MonoidHom.mem_ker, map_mul, map_inv, h_d_ideleOfIdeal, hd_prin, hxI,
          mul_inv_cancel]
      have hu_W : u ∈ W := by
        refine mem_of_locIdele_mem (Subgroup.isClosed_of_isOpen W hW_open) fun v ↦ ?_
        by_cases hv : v ∈ T
        · have hv_supp : v ∈ 𝔪.support := (h𝔪_supp v).mpr hv
          have hv_dvd : v.asIdeal ∣ 𝔪.finitePart := (Modulus.mem_support_iff 𝔪 v).mp hv_supp
          have hcnt : FractionalIdeal.count K v (I.1 : FractionalIdeal _ K) = 0 :=
            I.2 v hv_supp
          have hu_at : ideleAt v u = (ideleAt v (principalIdele x))⁻¹ := by
            simp [u, h_at_ideleOfIdeal, hcnt]
          rw [hu_at, map_inv]
          refine W.inv_mem (heW v _ ?_)
          have hval := hx_congr.1 v hv_dvd
          have h_exp : WithZero.exp (-(𝔪.exponent v : ℤ)) ≤ WithZero.exp (-(e v : ℤ)) :=
            WithZero.exp_le_exp.mpr (by have := he_le v hv; omega)
          have hcoe : ((ideleAt v (principalIdele x) : (LocField v)ˣ) : LocField v) - 1 =
              algebraMap K (LocField v) (x.val - 1) := by
            simp [ideleAt, principalIdele, map_sub]
            rfl
          rw [hcoe, v_algebraMap_eq_valuation]
          exact hval.trans h_exp
        · exact hW_unram v hv _ (mem_idelesUnitOff.mp hu_unit v (Set.notMem_empty v))
      have h_mem : ideleOfIdeal I ∈ W := by
        simpa [u] using W.mul_mem hu_W h_prin_mem
      exact hW_le h_mem
    let χ : RayClassCharacter 𝔪 := rayClassLift (ψ.comp ideleOfIdeal) h_ray
    -- `χ` is nontrivial because weak approximation shows `ideleOfIdeal` + `W` + `Kˣ₊` generate `(𝔸f K)ˣ`.
    have hχ_ne : χ ≠ 1 := by
      intro hχ1
      apply hψ_ne
      ext1 a
      suffices ha : a ∈ ψ.ker from ha
      have hker_open : ψ.ker.IsOpen := isOpen_mono hW_le hW_open
      -- Approximate `a.val v` by a rational `t v : K` at each `v ∈ T`.
      have h_rat (v : FinPlace K) : ∃ t : K,
          Valued.v (a.val v - algebraMap K (LocField v) t) <
            Valued.v (a.val v) * WithZero.exp (-(e v : ℤ)) := by
        let r : (Valued.v : Valuation (LocField v) ℤᵐ⁰).ValueGroup₀ :=
          Valued.v.restrict (a.val v * (uniformizer v : LocField v) ^ e v)
        have hr_emb : MonoidWithZeroHom.ValueGroup₀.embedding r =
            Valued.v (a.val v) * WithZero.exp (-(e v : ℤ)) := by
          simp [r, map_mul, map_pow, v_uniformizer, ← WithZero.exp_nsmul]
        have hpos : Valued.v (a.val v) * WithZero.exp (-(e v : ℤ)) ≠ 0 :=
          mul_ne_zero (Valued.v.ne_zero_iff.mpr (Units.ne_zero (ideleAt v a))) WithZero.exp_ne_zero
        have hopen : IsOpen {y : LocField v | Valued.v (a.val v - y) <
            Valued.v (a.val v) * WithZero.exp (-(e v : ℤ))} := by
          have heq : {y : LocField v | Valued.v (a.val v - y) <
              Valued.v (a.val v) * WithZero.exp (-(e v : ℤ))} =
              (fun y ↦ a.val v - y) ⁻¹' {z : LocField v | Valued.v.restrict z < r} := by
            ext y
            simp [Valuation.restrict_lt_iff_lt_embedding, hr_emb]
          rw [heq]
          exact (Valued.isOpen_ball (R := LocField v) r).preimage (continuous_const.sub continuous_id)
        have hnhds : {y : LocField v | Valued.v (a.val v - y) <
            Valued.v (a.val v) * WithZero.exp (-(e v : ℤ))} ∈ nhds (a.val v) :=
          hopen.mem_nhds (by simp [pos_iff_ne_zero.mpr hpos])
        obtain ⟨t, ht⟩ := (v.denseRange_algebraMap K).exists_mem_open
          hopen ⟨a.val v, mem_of_mem_nhds hnhds⟩
        exact ⟨t, ht⟩
      choose t ht using h_rat
      -- Approximate `t` at `T` by a totally positive `x : Kˣ`.
      obtain ⟨x, hx_fin, hx_sign⟩ := exists_fieldUnit_valuation_sub_lt_and_signHom_eq (S := T) t
        (fun v ↦ Valued.v (a.val v) * WithZero.exp (-(e v : ℤ)))
        (fun v _ ↦ mul_ne_zero (Valued.v.ne_zero_iff.mpr (Units.ne_zero (ideleAt v a)))
          WithZero.exp_ne_zero)
        (fun _ ↦ 1)
      have hx_pos : IsTotallyPositive x.val := by
        intro φ
        let w : NumberField.InfinitePlace K := .mk (ofRealHom.comp φ)
        have hw : w.IsReal := NumberField.InfinitePlace.isReal_mk_iff.mpr (by ext a; simp)
        have hs := congrFun hx_sign ⟨w, hw⟩
        rw [signHom_apply_eq_one_iff] at hs
        have hemb : NumberField.InfinitePlace.embedding_of_isReal hw x.val = φ x.val := by
          apply Complex.ofReal_injective
          rw [NumberField.InfinitePlace.embedding_of_isReal_apply,
            NumberField.InfinitePlace.embedding_mk_eq_of_isReal (by ext a; simp)]
          rfl
        rwa [hemb] at hs
      have hx_mem : principalIdele x ∈ ψ.ker := hW_le (hW_pos x hx_pos)
      let b : (𝔸f K)ˣ := a * (principalIdele x)⁻¹
      have hb_at (v : FinPlace K) (hv : v ∈ T) :
          Valued.v ((ideleAt v b : (LocField v)ˣ).val - 1) ≤ WithZero.exp (-(e v : ℤ)) := by
        have hdiff : Valued.v (a.val v - algebraMap K (LocField v) x.val) <
            Valued.v (a.val v) * WithZero.exp (-(e v : ℤ)) := by
          have h1 : a.val v - algebraMap K (LocField v) x.val =
              (a.val v - algebraMap K (LocField v) (t v)) -
                algebraMap K (LocField v) (x.val - t v) := by
            simp [map_sub]
          rw [h1]
          refine (Valued.v.map_sub _ _).trans_lt (max_lt (ht v) ?_)
          rw [v_algebraMap_eq_valuation]
          exact hx_fin v hv
        have hlt1 : WithZero.exp (-(e v : ℤ)) < 1 :=
          WithZero.exp_lt_one_iff.mpr (by have := he1 v; omega)
        have hval_eq : Valued.v (algebraMap K (LocField v) x.val) = Valued.v (a.val v) := by
          have hlt : Valued.v (a.val v - algebraMap K (LocField v) x.val) < Valued.v (a.val v) :=
            hdiff.trans_le (mul_le_of_le_one_right' hlt1.le)
          have := Valuation.map_sub_eq_of_lt_left Valued.v hlt
          simpa using this
        have hsub : ((ideleAt v b : (LocField v)ˣ) : LocField v) - 1 =
            (a.val v - algebraMap K (LocField v) x.val) * (algebraMap K (LocField v) x.val)⁻¹ := by
          have hx0 : algebraMap K (LocField v) x.val ≠ 0 := by simp
          have h_id : ((ideleAt v b : (LocField v)ˣ) : LocField v) =
              a.val v * (algebraMap K (LocField v) x.val)⁻¹ := by
            simp only [b, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
            rfl
          rw [h_id, sub_mul, mul_inv_cancel₀ hx0]
        rw [hsub, map_mul, map_inv₀, hval_eq]
        have ha0 : Valued.v (a.val v) ≠ 0 := Valued.v.ne_zero_iff.mpr (Units.ne_zero (ideleAt v a))
        exact le_of_lt (by rwa [mul_inv_lt_iff₀ (pos_iff_ne_zero.mpr ha0), mul_comm])
      have hb_primeTo : d b ∈ idealsPrimeTo 𝔪 := by
        intro v hv
        have hvT : v ∈ T := (h𝔪_supp v).mp hv
        have hv1 : Valued.v (b.val v) = 1 := by
          have hlt : Valued.v ((ideleAt v b : (LocField v)ˣ).val - 1) < 1 :=
            (hb_at v hvT).trans_lt (WithZero.exp_lt_one_iff.mpr (by have := he1 v; omega))
          simpa [ideleAt] using Valuation.map_one_add_of_lt Valued.v hlt
        have hle := (hd_int b v).mp hv1.le
        have hge : 0 ≤ FractionalIdeal.count K v (d b⁻¹).val :=
          (hd_int b⁻¹ v).mp (by
            have hbv : Valued.v (b⁻¹.val v) = 1 := by
              have : b⁻¹.val v = (b.val v)⁻¹ :=
                (congrArg Units.val (map_inv (ideleAt v) b)).trans
                  (Units.val_inv_eq_inv_val (ideleAt v b))
              rw [this, map_inv₀, hv1, inv_one]
            exact hbv.le)
        rw [map_inv, Units.val_inv_eq_inv_val, FractionalIdeal.count_inv] at hge
        omega
      let I : idealsPrimeTo 𝔪 := ⟨d b, hb_primeTo⟩
      have hI_ker : ideleOfIdeal I ∈ ψ.ker := by
        have := DFunLike.congr_fun hχ1 (rayClassMk 𝔪 I)
        simpa [χ] using this
      have hb_u : b * (ideleOfIdeal I)⁻¹ ∈ idelesUnitOff ∅ := by
        rw [← hd_ker, MonoidHom.mem_ker, map_mul, map_inv, h_d_ideleOfIdeal, mul_inv_cancel]
      have hb_diff : b * (ideleOfIdeal I)⁻¹ ∈ ψ.ker := by
        refine mem_of_locIdele_mem (Subgroup.isClosed_of_isOpen ψ.ker hker_open) fun v ↦ ?_
        by_cases hv : v ∈ T
        · have hv_supp : v ∈ 𝔪.support := (h𝔪_supp v).mpr hv
          have hcnt : FractionalIdeal.count K v (I.1 : FractionalIdeal _ K) = 0 := I.2 v hv_supp
          have hat : ideleAt v (b * (ideleOfIdeal I)⁻¹) = ideleAt v b := by
            simp [h_at_ideleOfIdeal, hcnt]
          rw [hat]
          exact hW_le (heW v _ (hb_at v hv))
        · exact hW_le (hW_unram v hv _ (mem_idelesUnitOff.mp hb_u v (Set.notMem_empty v)))
      have hb_mem : b ∈ ψ.ker := by
        simpa using ψ.ker.mul_mem hb_diff hI_ker
      simpa [b] using ψ.ker.mul_mem hb_mem hx_mem
    -- Now `χ ≠ 1` gives cancellation and analyticity of `L(s, χ)` at `s = 1`.
    have hC : HasCancellation χ.toUnitaryIdealWeight :=
      RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ_ne
    have hDiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight)
        {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
      differentiableOn_continuedLFunctionOfWeight hC
    let F : ℝ → ℂ := fun s ↦ continuedLFunctionOfWeight χ.toUnitaryIdealWeight (s : ℂ)
    have hF_an : AnalyticAt ℝ F 1 := by
      have hAnC : AnalyticAt ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) 1 :=
        hDiff.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by simpa using cancellationExponent_lt_one (K := K)))
      have hAnR : AnalyticAt ℝ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight)
          (Complex.ofRealCLM 1) := by
        simpa using hAnC.restrictScalars (𝕜 := ℝ)
      exact hAnR.comp (Complex.ofRealCLM.analyticAt 1)
    let wFun : Ideal (𝓞 K) →* ℂ := χ.toMultiplicativeIdealWeight.toMonoidWithZeroHom.toMonoidHom
    have hwFun_norm (I : Ideal (𝓞 K)) : ‖wFun I‖ ≤ 1 := by
      by_cases hI : I = ⊥
      · simp [wFun, hI]
      · exact χ.toUnitaryIdealWeight.norm_le_one (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰)
    have hF_eq {s : ℝ} (hs : 1 < s) : F s = eulerProd (fun v : FinPlace K ↦ wFun v.asIdeal) s := by
      have hsC : 1 < (s : ℂ).re := by simpa using hs
      rw [show F s = LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s from
        continuedLFunctionOfWeight_eq_LSeries _ hsC]
      rw [LSeries_normCoeff K (summable_idealTerm_of_unitary_of_one_lt_re _ hsC)]
      have hsum := hasSum_eulerProd wFun hwFun_norm hs
      rw [← hsum.tsum_eq]
      symm
      refine tsum_eq_tsum_of_ne_zero_bij (fun I ↦ (I.1 : Ideal (𝓞 K)))
        (fun _ _ h ↦ Subtype.ext (Subtype.ext h)) ?_ fun I ↦ ?_
      · intro I hI
        have hI0 : I ≠ ⊥ := fun hbot ↦ by simp [hbot, wFun] at hI
        refine ⟨⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, ?_⟩, rfl⟩
        simpa [Function.mem_support, idealTerm, wFun, cpow_neg, div_eq_mul_inv] using hI
      · simp [idealTerm, wFun, cpow_neg, div_eq_mul_inv]
    -- Order of vanishing `m` of `F` at `1` gives `HasPrimeDensity (fun v ↦ wFun v.asIdeal) (-m)`.
    have hF_ne : ¬∀ᶠ s in nhds (1 : ℝ), F s = 0 := by
      intro h_zero
      obtain ⟨s, hs, hs_zero⟩ := ((frequently_gt_nhds (1 : ℝ)).and_eventually h_zero).exists
      have hne : eulerProd (fun v : FinPlace K ↦ wFun v.asIdeal) s ≠ 0 := by
        rw [(eulerProd_eq_exp (fun v ↦ hwFun_norm v.asIdeal) hs).1]
        exact exp_ne_zero _
      exact hne ((hF_eq hs).symm.trans hs_zero)
    obtain ⟨m, g, hg_an, hg_ne, hF_fac⟩ := hF_an.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hF_ne
    have hdens_w : HasPrimeDensity (fun v : FinPlace K ↦ wFun v.asIdeal) (-(m : ℂ)) := by
      refine hasPrimeDensity_of_tendsto (fun v ↦ hwFun_norm v.asIdeal) hg_ne ?_
      refine hg_an.continuousAt.continuousWithinAt.congr' (eventually_nhdsWithin_iff.mpr ?_)
      filter_upwards [hF_fac] with s h_fac hs
      have hs_ne : (s : ℂ) - 1 ≠ 0 := mod_cast sub_ne_zero.mpr (Set.mem_Ioi.mp hs).ne'
      rw [← hF_eq hs, h_fac]
      simp [cpow_neg, hs_ne]
    -- `wFun v.asIdeal` agrees with `f (.ofMul ⟦locIdele v (uniformizer v)⟧)` outside the finite set `T`.
    have hwFun_eq (v : FinPlace K) (hv : v ∉ T) :
        wFun v.asIdeal = f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧) := by
      have hv_primeTo : Ideal.IsPrimeTo v.asIdeal 𝔪.support := by
        rw [Ideal.isPrimeTo_iff]
        refine ⟨v.ne_bot, fun w hw hdvd ↦ hv ?_⟩
        have hwT : w ∈ T := (h𝔪_supp w).mp hw
        exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top
          (Ideal.dvd_iff_le.mp hdvd))) ▸ hwT
      have hval : wFun v.asIdeal =
          (χ.onIdeals ⟨v.asIdeal, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
            (Ideal.isPrimeTo_iff.mp hv_primeTo)⟩ : ℂ) :=
        RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hv_primeTo
      rw [hval, RayClassCharacter.onIdeals_apply, idealClass_apply]
      change (ψ (ideleOfIdeal (NumberFieldArithmetic.integralIdealsAwayHom K 𝔪.support _)) : ℂ) = _
      rw [hψ_val]
      congr 2
      have h_id : ideleOfIdeal (NumberFieldArithmetic.integralIdealsAwayHom K 𝔪.support
          ⟨v.asIdeal, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
            (Ideal.isPrimeTo_iff.mp hv_primeTo)⟩) = locIdele v (uniformizer v) := by
        change (∏ᶠ w : FinPlace K, locIdele w (uniformizer w ^
          FractionalIdeal.count K w (v.asIdeal : FractionalIdeal _ K))) = locIdele v (uniformizer v)
        rw [finprod_eq_single _ v]
        · simp [FractionalIdeal.count_maximal]
        · intro w hw
          simp [FractionalIdeal.count_maximal, hw.symm]
      rw [h_id]
    -- Adding the finitely many terms in `T` changes the Dirichlet series by `O(1)`.
    obtain ⟨err, herr_bdd, herr_sum⟩ := hdens_w
    let diff (v : FinPlace K) : ℂ :=
      f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧) - wFun v.asIdeal
    refine ⟨m, fun s ↦ err s + ∑ v ∈ T, ite v.q.Prime (diff v) 0 * v.q ^ (-s : ℂ), ?_, ?_⟩
    · refine herr_bdd.add ?_
      have hcont : ContinuousAt (fun s : ℝ ↦ ∑ v ∈ T, ite v.q.Prime (diff v) 0 * v.q ^ (-s : ℂ)) 1 :=
        by fun_prop (disch := simp)
      exact hcont.continuousWithinAt.isBigO_one ℝ
    · filter_upwards [herr_sum] with s hs
      have hfin : HasSum (fun v : FinPlace K ↦ ite v.q.Prime (diff v) 0 * v.q ^ (-s : ℂ))
          (∑ v ∈ T, ite v.q.Prime (diff v) 0 * v.q ^ (-s : ℂ)) :=
        hasSum_sum_of_ne_finset_zero fun v hv ↦ by simp [diff, hwFun_eq v hv]
      convert hs.add hfin using 1
      · funext v
        by_cases hq : v.q.Prime <;> simp [diff, hq, sub_mul]
      · ring
  simpa using h_res

omit hW_pos in
/-- Let `L / K` be Galois and `W` an open subgroup of finite index of the finite ideles of `K` that
contains the norms from `L` (`h_norm`). If each character `f` of the quotient by `W` has mean `d f`
at the uniformiser ideles, then the index of `W` is at most `Re (∑ f, [L : K] * d f)`. -/
private lemma index_re_le_sum_of_hasPrimeDensity [FiniteIndex W]
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W)
    (d : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ → ℂ)
    (hd : ∀ f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ,
      HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
        (d f)) :
    (W.index : ℂ).re ≤ (∑ f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ, (finrank K L : ℂ) * d f).re := by
  classical
  -- `D v`: the primes above `v` of the same norm; `#(D v)` has mean 1.
  let D (v : FinPlace K) : Set (FinPlace L) := {w : FinPlace L | w.below K = v ∧ w.q = v.q}
  -- The Galois group permutes the primes above `v` transitively, so there are at most `[L : K]`.
  have h_card (v : FinPlace K) : (D v).ncard ≤ finrank K L := by
    rcases (D v).eq_empty_or_nonempty with hD | ⟨w, rfl, -⟩
    · simp [hD]
    grw [← IsGalois.card_aut_eq_finrank,
      ← Finite.card_range_le fun g : Gal(L/K) ↦ w.comap (g : L →+* L)]
    exact Set.ncard_le_ncard fun u ⟨hu_below, _⟩ ↦ w.exists_gal_comap_eq hu_below.symm
  -- Write `ϖ_v = locIdele v (uniformizer v)` for the uniformiser idele at `v`. If `W` holds the
  -- units at `v` and `w ∈ D v`, then `ϖ_v` is the norm of `ϖ_w` up to a unit.
  have h_mem : ∀ᶠ v in .cofinite, (D v).Nonempty → locIdele v (uniformizer v) ∈ W := by
    filter_upwards [eventually_unramified (mk' W) (by simpa)] with v h_unit ⟨w, hw, hq⟩
    subst hw
    specialize h_unit (uniformizer _ / localNorm K w (uniformizer w))
    simp_all [v_localNorm (f := 1), ← adeleNorm_locIdele, (eq_one_iff _).mpr]
  -- For almost all `v`, `[W] * #(D v) ≤ [L : K] * ∑ f, f(ϖ_v)` with `[W]` the index: the sum is
  -- `[W]` if `ϖ_v ∈ W` and `0` otherwise. Compare the densities of the two sides.
  refine (hasPrimeDensity_card_degree_one L W.index).re_le_re (.sum (fun _ ↦ finrank K L) hd)
    (h_mem.mono fun v hv _ ↦ ?_)
  rcases (D v).eq_empty_or_nonempty with hD | hD
  · simp_all [D, ← mul_sum, sum_apply_eq_ite, apply_ite, mul_nonneg]
  · have h_mul : (W.index : ℝ) * (D v).ncard ≤ finrank K L * W.index := by grw [h_card, mul_comm]
    simpa [(eq_one_iff _).mpr (hv hD), index, mul_comm, D] using h_mul

/-- Let `L / K` be Galois and `W` an open subgroup of the finite ideles of `K` (`hW_open`) that
contains the totally positive principal ideles (`hW_pos`) and the norms from `L` (`h_norm`). A
character `f` of the quotient by `W` has mean `1` at the uniformiser ideles if it is trivial
(`f = 0`), and mean `0` otherwise. -/
private lemma hasPrimeDensity_addChar_uniformizer_of_adeleNorm_mem
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W)
    (f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ) :
    HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
      (if f = 0 then 1 else 0) := by
  classical
  have h_fin : FiniteIndex W := finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos
  -- The means are `1 - m g` or `-m g` with `m g : ℕ`, and the positive index is at most their sum
  -- times `[L : K]`, so every `m g` vanishes.
  choose m hm using exists_hasPrimeDensity_addChar_uniformizer (K := K) hW_open hW_pos
  have h_le : (W.index : ℂ).re ≤
      (∑ g, (finrank K L : ℂ) * ((if g = 0 then 1 else 0) - m g)).re :=
    index_re_le_sum_of_hasPrimeDensity L hW_open h_norm _ hm
  have h_pos : (0 : ℝ) < (∑ g, (finrank K L : ℂ) * ((if g = 0 then 1 else 0) - m g)).re :=
    (Nat.cast_pos.mpr Nat.card_pos).trans_le h_le
  have hm0 (g : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ) : m g = 0 := by
    simp_all [← Nat.cast_sum, ← mul_sum, finrank_pos]
  simpa [hm0 f] using hm f

/-- Let `L / K` be Galois and `W` an open subgroup of the finite ideles of `K` (`hW_open`) that
contains the totally positive principal ideles (`hW_pos`) and the norms from `L` (`h_norm`). Then
the index of `W` is at most `[L : K]`. -/
private lemma index_le_finrank_of_adeleNorm_mem
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W) :
    W.index ≤ finrank K L := by
  have h_fin : FiniteIndex W := finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos
  simpa using index_re_le_sum_of_hasPrimeDensity L hW_open h_norm _
    (hasPrimeDensity_addChar_uniformizer_of_adeleNorm_mem L hW_open hW_pos h_norm)

/-- Let `L / K` be Galois and `W` an open subgroup of the finite ideles of `K` (`hW_open`) that
contains the totally positive principal ideles (`hW_pos`) and the norms from `L` (`h_norm`). Then
every coset `a W` contains the uniformiser ideles of infinitely many primes `v` of prime norm
`v.q`. -/
lemma New.frequently_prime_uniformizer_div_mem_of_adeleNorm_mem
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W) (a : (𝔸f K)ˣ) :
    ∃ᶠ v : FinPlace K in Filter.cofinite, v.q.Prime ∧ locIdele v (uniformizer v) / a ∈ W := by
  classical
  have h_fin : FiniteIndex W := finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos
  -- With `ϖ_v` the uniformiser idele at `v`, `∑ f, f(ϖ_v / a)` has mean 1. If the claim failed,
  -- this sum would vanish for almost all `v` of prime norm, so its mean would be 0.
  intro h_not
  refine ((HasPrimeDensity.sum (fun f ↦ f (.ofMul a⁻¹))
      (hasPrimeDensity_addChar_uniformizer_of_adeleNorm_mem L hW_open hW_pos h_norm)).re_le_re
      (hasPrimeDensity_const 0) (h_not.mono ?_)).not_gt (by simp)
  simp +contextual [← map_add_eq_mul, sum_apply_eq_ite, neg_add_eq_sub, eq_iff_div_mem, sub_eq_zero]

/-- The second inequality of class field theory, with equidistribution. Let `L / K` be Galois and
`W` an open subgroup of the finite ideles of `K` (`hW_open`) containing the principal ideles of the
totally positive elements (`hW_pos`) and the norms of finite ideles of `L` (`h_norm`). Then (a)
`W` has finite index at most `[L : K]`, and (b) each coset `a W` contains the uniformiser ideles of
infinitely many primes of prime norm: `frequently_prime_uniformizer_div_mem_of_adeleNorm_mem`. -/
lemma New.second_inequality (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W) :
    FiniteIndex W ∧
    W.index ≤ finrank K L ∧
    ∀ a : (𝔸f K)ˣ, ∃ᶠ v : FinPlace K in Filter.cofinite,
      v.q.Prime ∧ locIdele v (uniformizer v) / a ∈ W :=
  ⟨finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos,
    index_le_finrank_of_adeleNorm_mem L hW_open hW_pos h_norm,
    frequently_prime_uniformizer_div_mem_of_adeleNorm_mem L hW_open hW_pos h_norm⟩

end SecondInequality

/-!
## Albert–Brauer–Hasse–Noether with a stronger hypothesis at real places

Γ is the Galois group of an algebraic closure Ω of a number field K, and χ is a character of Γ
(`New.QZChar`). L is the field cut out by χ, that is, the fixed field of its kernel. The local
symbol of x at v is `New.QZChar.abelianLift χ (New.artinAt Γ v x)`, and `New.adeleNorm` is the
adelic norm.
-/

namespace New

open Ideal NumberField Cohomology Units NeZero Algebra QZChar

variable {Γ K L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra K L]

/-- The adelic norm `New.adeleNorm K L` takes the principal idele of `x` in `Lˣ` to the principal
idele of the norm of `x`. -/
@[local simp]
lemma map_adeleNorm_principalIdele (x : Lˣ) :
    (principalIdele x).map (adeleNorm K L) = principalIdele (x.map (Algebra.norm K)) := by
  aesop

/-- For a finite adele `y` of `L` and a finite place `v` of `K`, the `v`-component of the adelic
norm of `y` is a limit, in the completion of `K` at `v`, of norms of elements of `L`. -/
lemma adeleNorm_mem_closure {y : 𝔸f L} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} :
    adeleNorm K L y v ∈
      closure (Set.range fun x : L ↦ algebraMap K (v.adicCompletion K) (Algebra.norm K x)) := by
  -- `y ↦ adeleNorm K L y v` is continuous, `L` is dense in the finite adeles, and on `L` it is the
  -- norm.
  have h_cont : Continuous fun y ↦ adeleNorm K L y v := (continuous_evalAt v).comp (by fun_prop)
  have h_on_L (x : L) : adeleNorm K L (algebraMap L (𝔸f L) x) v =
      algebraMap K (v.adicCompletion K) (Algebra.norm K x) := by aesop
  exact map_mem_closure h_cont (denseRange_algebraMap_finAdele y)
    (Set.mapsTo_range_iff.mpr fun x ↦ ⟨x, (h_on_L x).symm⟩)

variable [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] [Algebra L Ω]
  [IsScalarTower K L Ω] {χ : QZChar Γ} [IsProGalois (ker χ) L Ω]

/-- Let the continuous character χ : Γ → ℚ/ℤ cut out the finite extension L of K, and let K_v be the
completion of K at the finite place v. If a unit u of K_v is a limit in K_v of norms from L to K,
then χ vanishes on the local Artin symbol `artinAt Γ v u`. When `u` is a component of the adelic
norm of a finite idele of L, the hypothesis is `adeleNorm_mem_closure`. -/
lemma abelianLift_artinAt_eq_one_of_mem_closure {v : FinPlace K} {u : (v.adicCompletion K)ˣ}
    (hu : u.val ∈
      closure (Set.range fun x : L ↦ algebraMap K (v.adicCompletion K) (Algebra.norm K x))) :
    abelianLift χ (artinAt Γ v u) = 1 := by
  -- The kernel of `abelianLift χ ∘ artinAt Γ v` is closed, since the target is discrete, and it
  -- contains the norms, whose global symbol `(χ, x)` is zero.
  have h_closed : IsClosed {w : (v.adicCompletion K)ˣ | abelianLift χ (artinAt Γ v w) = 1} :=
    (isClosed_discrete {1}).preimage
      ((continuous_abelianLift χ).comp (continuous_hom_locField_units _))
  refine closure_minimal ?_ h_closed (isOpenMap_val.preimage_closure_subset_closure_preimage hu)
  rintro w ⟨z, hz⟩
  have hz_ne : z ≠ 0 := fun h_zero ↦ by simpa [h_zero] using hz.symm
  let x : Kˣ := .map (norm K) (.mk0 z hz_ne)
  have hw : ideleAt v (principalIdele x) = w := ext hz
  rw [← hw, Set.mem_ofPred, v.isPlaceOver_placeOver.abelianLift_artinAt_eq_one_iff,
    (cyclicClass_eq_zero_iff_norm (L := L) x).mpr ⟨.mk0 z hz_ne, rfl⟩, map_zero]

/-- The character χ kills the Artin symbol of the norm of every finite idele of the field L that it
cuts out. -/
@[simp]
lemma abelianLift_artinMap_adeleNorm (y : (𝔸f L)ˣ) :
    abelianLift χ (artinMap Γ (Units.map (adeleNorm K L) y)) = 1 := by
  rw [abelianLift_artinMap_eq_finprod, finprod_eq_one_of_forall_eq_one fun _ ↦
    abelianLift_artinAt_eq_one_of_mem_closure adeleNorm_mem_closure]

/-- The kernel of the local symbol consists of local norms. Let L be the field cut out by χ, let w
be a finite place of L over the place v = `w.below K` of K, and let x be a unit of the completion
K_v of K at v with `χ (artinAt Γ v x)` trivial. Then there is a unit y of the completion
`LocField w` of L at w whose local norm to K_v is x. -/
lemma exists_localNorm_of_abelianLift_artinAt {w : FinPlace L} {x : (LocField (w.below K))ˣ}
    (hx : abelianLift χ (artinAt Γ (w.below K) x) = 1) :
    ∃ y : (LocField w)ˣ, localNorm K w y = x := by
  rw [w.isPlaceOver_placeOver.isPlaceOver_below.abelianLift_artinAt] at hx
  -- Inside the decomposition group, `χ` kills exactly the elements that come from `Gal(Ω/L)`.
  have h_ker (g : decompGroup Γ (placeOver w)) :
      (χ : Γ → QZ) g = 0 ↔ ∃ g' : decompGroup (ker χ) (placeOver w), (ker χ).subtype g' = g := by
    aesop
  exact (w.isPlaceOver_placeOver.isNormCompatible (ker χ).subtype 1 (fun _ _ ↦ rfl)
    (IsScalarTower.algebraMap_apply K L Ω)).exists_localNorm_eq
    (χ := QZChar.comap (subgroupIncl _) χ) h_ker hx

open InfinitePlace Subgroup Finset Nat SUnit DiscreteModule MulSemiringAction Function

/-- Let f : E → G be a homomorphism to a commutative group, J, N subgroups of G with f(E)·J = G,
and U = f⁻¹J. Then [G : f(E)(N ∩ J)] · [U : U ∩ f⁻¹N] = [J : J ∩ N]. -/
lemma relIndex_mul_index_sup {E G : Type*} [Group E] [CommGroup G] {f : E →* G} {J N : Subgroup G}
    {U : Subgroup E} (h_top : f.range ⊔ J = ⊤) (h_mem : ∀ {x : E}, f x ∈ J ↔ x ∈ U) :
    (N.comap f).relIndex U * (f.range ⊔ N ⊓ J).index = N.relIndex J := by
  -- The tower formula for the subgroups `N ⊓ J ≤ (N ⊓ J ⊔ f.range) ⊓ J ≤ J`; its two steps
  -- are the two factors on the left.
  obtain rfl : J.comap f = U := Subgroup.ext fun _ ↦ h_mem
  -- Upper step: joining `J` to `N ⊓ J ⊔ f.range` gives all of `G`.
  have h_relIndex_upper : (N ⊓ J ⊔ f.range).relIndex J = (f.range ⊔ N ⊓ J).index := by
    rw [← relIndex_sup_left J, sup_comm (N ⊓ J), sup_assoc, sup_of_le_right (inf_le_right (a := N)),
      h_top, relIndex_top_right]
  -- Lower step: by the modular law the middle group is `N ⊓ J ⊔ f.range ⊓ J`, and
  -- `f.range ⊓ J` is the image of `U`.
  have h_relIndex_lower :
      (N ⊓ J).relIndex ((N ⊓ J ⊔ f.range) ⊓ J) = (N.comap f).relIndex (J.comap f) := by
    rw [sup_inf_assoc_of_le _ inf_le_right, relIndex_sup_left, ← map_comap_eq, ← relIndex_comap,
      N.comap_inf, inf_relIndex_right]
  rw [← h_relIndex_upper, ← h_relIndex_lower, relIndex_inf_mul_relIndex,
    inf_of_le_left le_sup_left, inf_relIndex_right]

omit [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] in
/-- Index of the norms among the `S`-units. Let `L / K` be Galois of prime degree `l`, `S` a finite
set of places of `K` containing the ramified ones such that the principal ideles and the ideles that
are units off `S` generate all ideles (`h_gen`), and `T` the places above `S`. Then
`([E_S : N E_T] * l) ^ (l - 1) * l ^ (#T + r_L) = (l ^ l) ^ (#S + r_K)`, with `[E_S : N E_T]` the
index of the norms of the `T`-units in the `S`-units and `r` the number of infinite places. -/
lemma relIndex_norm_unit_pow [IsGalois K L] {l : ℕ} (hl : l.Prime) (hL : Module.finrank K L = l)
    {S : Set (FinPlace K)} (hS : S.Finite) (h_gen : principalIdele.range ⊔ idelesUnitOff S = ⊤)
    (h_unr : ∀ w : FinPlace L, w.below K ∉ S → w.asIdeal.ramificationIdx (𝓞 K) = 1)
    {T : Set (FinPlace L)} (hT : T = FinPlace.comap (algebraMap K L) ⁻¹' S) :
    (((T.unit L).map (Units.map (Algebra.norm K))).relIndex (S.unit K) * l) ^ (l - 1) *
        l ^ (T.ncard + Fintype.card (InfinitePlace L)) =
      (l ^ l) ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
  have : Fact l.Prime := ⟨hl⟩
  -- Dirichlet: the rank of the `S`-units is `#S` plus the number of infinite places minus one.
  obtain ⟨finite_S, rank_S⟩ := dirichlet_unit_theorem hS
  obtain ⟨finite_T, rank_T⟩ := dirichlet_unit_theorem (S := T)
    (by simpa [hT] using tendsto_place_comap_cofinite _ hS.compl_mem_cofinite)
  -- Tate's index formula suffices, as the indices `#(A / l A) / #A[l]` in it are `l ^ rank A`.
  suffices h_tate_index :
      ((T.unit L).map (Units.map (Algebra.norm K))).relIndex (S.unit K) ^ (l - 1) *
          cokerKerIndex (l : Module.End ℤ (Additive (T.unit L))) =
        cokerKerIndex (l : Module.End ℤ (Additive (S.unit K))) ^ l by
    simp only [cokerKerIndex_eq_pow_finrank, ← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_inj]
      at h_tate_index
    rw [← rank_S, ← rank_T, mul_pow, pow_succ, mul_mul_mul_comm, h_tate_index, pow_right_comm,
      pow_sub_one_mul hl.ne_zero, pow_succ]
  subst hT
  -- Off `S` the valuations of `L` extend those of `K`, as there is no ramification.
  have h_val {w : FinPlace L} (hw : w.below K ∉ S) (x : K) :
      (w.below K).valuation K x = w.valuation L (algebraMap K L x) := by
    simpa [h_unr w hw, (w.comap _).ne_bot, ramificationIdx'_eq_ramificationIdx]
      using (w.below K).valuation_liesOver L (K := K) w x
  refine tate_index_formula_norm l hL _ (S.unit K) ?_ ?_ ?_ cokerKerIndex_eq_pow_finrank.left
  · -- An element of `K` is an `S`-unit exactly when it is one in `L`.
    ext
    simp +contextual [Set.unit, (FinPlace.comap_surjective (algebraMap K L)).forall, h_val,
      Subgroup.copy]
  · -- The Galois group permutes the places that are not above `S`.
    intro g y hy w hw
    rw [← g.toAlgHom.comp_algebraMap] at hw
    -- The goal is over `LocField w` with the Galois action on units, the lemmas over the completion
    -- with ring homomorphisms; the two forms agree by unfolding.
    erw [← v_algebraMap_eq_valuation, ← locMap_algebraMap g.toRingHom rfl,
      v_locMap_eq_of_surjective _ _ g.surjective, v_algebraMap_eq_valuation, hy _ hw]
  · -- Let the divisor of `z` off `S` be invariant. The idele `a` of `K` with orders those of the
    -- norm of `z` divided by the degree has that divisor, and is principal off `S`.
    intro z hz
    let n : (𝔸f K)ˣ := principalIdele (z.map (norm K))
    obtain ⟨a, ha⟩ := exists_idele_eq_uniformizer_zpow
      (fun v ↦ (Valued.v (n.val v)).log / Nat.card Gal(L/K))
      ((finite_setOf_valued_val_ne_one n).subset fun v ↦ mt fun hv ↦ by simp [hv])
    obtain ⟨x, hx⟩ : ∃ x : Kˣ, ∀ v ∉ S, v.valuation K x.val = Valued.v (a.val v) :=
      exists_valuation_eq_of_mem_sup (h_gen.ge (mem_top a))
    refine ⟨x, fun w hw ↦ ?_⟩
    have h_conj (g : Gal(L/K)) : w.valuation L (g z) = w.valuation L z := by
      simpa [div_eq_iff] using hz g w hw
    simp [← h_val hw, hx _ hw, h_val hw, ha, n, norm_eq_prod_automorphisms, h_conj]

omit [NumberField K] [NumberField L] in
/-- If `χ` kills all complex conjugations, the real places stay real in the field `L` it cuts out:
`L / K` is unramified at the infinite places. -/
lemma isUnramifiedAtInfinitePlaces_of_mem_ker (hc : ∀ c : Γ, IsComplexConj c → c ∈ ker χ) :
    IsUnramifiedAtInfinitePlaces K L := by
  refine ⟨(comap_surjective (K := Ω)).forall.mpr ?_⟩
  rintro ⟨_, j, rfl⟩
  refine isUnramified_iff.mpr ((isReal_or_isComplex _).imp_left fun h_real ↦ ?_)
  -- If `j` is real on `K`, it differs from its conjugate by a complex conjugation `g` fixing `L`.
  replace h_real : (InfinitePlace.mk (j.comp (algebraMap K Ω))).IsReal := by
    rwa [IsScalarTower.algebraMap_eq K L Ω]
  obtain ⟨g, hg⟩ : ∃ g : Γ, ∀ x : Ω, j (g • x) = star j x :=
    exists_apply_smul_eq_of_comp_algebraMap_eq Γ j (star j) (isReal_mk_iff.mp h_real).symm
  exact ⟨_, isReal_comp_algebraMap (c := (⟨g, hc g ⟨j, hg⟩⟩ : ker χ)) hg, rfl⟩

/-- Let `L / K` be Galois of prime degree `l`, cut out by `χ`. A finite place `v` of `K` either
splits into `l` places of `L`, and the local symbol `χ ∘ artinAt Γ v` takes one value, or has one
place above it, and the local symbol takes `l` values. In both cases
`#(range of the local symbol) ^ (l - 1) * l ^ #(places above v) = l ^ l`. -/
lemma card_range_abelianLift_comp_artinAt [IsGalois K L] {l : ℕ} (hl : l.Prime)
    (hL : Module.finrank K L = l) (v : FinPlace K) :
    Nat.card ((abelianLift χ).comp (artinAt Γ v)).range ^ (l - 1) *
      l ^ {w : FinPlace L | w.below K = v}.ncard = l ^ l := by
  -- The local symbol has the same range as `χ` on the decomposition group, and the number of places
  -- above `v` times the order of this range is the prime `l`.
  have h_mul : {w : FinPlace L | w.below K = v}.ncard *
      (ker χ).relIndex (decompGroup Γ (placeOver v)) = l :=
    (v.isPlaceOver_placeOver.ncard_above_mul_relIndex_eq_finrank (ker χ)).trans hL
  rw [v.isPlaceOver_placeOver.range_abelianLift_comp_artinAt, ← relIndex_ker]
  rw [← h_mul] at hl
  rcases Nat.prime_mul_iff.mp hl with ⟨-, h_range_one⟩ | ⟨h_range_prime, h_one_place⟩
  · -- `v` splits into `l` places, and the local symbol takes one value.
    simp [← h_mul, h_range_one]
  · -- One place lies above `v`, and the local symbol takes `l` values.
    simp [← h_mul, h_one_place, h_range_prime.pos]

/-- The tuple of the local symbols `χ ∘ artinAt Γ v` at the places `v` of a finite set `S` of
finite places of `K`, as a homomorphism on the finite ideles of `K`; each symbol takes its values in
its range. -/
private noncomputable def localSymbols (χ : QZChar Γ) (S : Finset (FinPlace K)) :
    (𝔸f K)ˣ →* (i : S) → ((abelianLift χ).comp (artinAt Γ i)).range :=
  MonoidHom.pi fun v : SetLike.coe S ↦
    ((abelianLift χ).comp (artinAt Γ v.val)).rangeRestrict.comp (ideleAt v.val)

/-- The local count in Hasse's norm theorem. Let `L / K` be Galois of prime degree `l`, cut out by
`χ`, and let `S` be a finite set of finite places of `K`, with a finite set `T` of places of `L`
above it (`hT`). Then the index `i` of the kernel of the local symbols at `S` in the ideles that
are units off `S` satisfies `i ^ (l - 1) * l ^ #T = (l ^ l) ^ #S`. -/
private lemma relIndex_ker_localSymbols_pow_mul_pow [IsGalois K L]
    (hl : (Module.finrank K L).Prime) (S : Finset (FinPlace K))
    (hT : (FinPlace.comap (algebraMap K L) ⁻¹' (S : Set (FinPlace K))).Finite) :
    (localSymbols χ S).ker.relIndex (idelesUnitOff S) ^ (Module.finrank K L - 1) *
        Module.finrank K L ^ (FinPlace.comap (algebraMap K L) ⁻¹' (S : Set (FinPlace K))).ncard =
      (Module.finrank K L ^ Module.finrank K L) ^ #S := by
  classical
  -- The local symbols map `idelesUnitOff S` onto the product of their ranges: use ideles with one
  -- component.
  have h_onto : (idelesUnitOff S).map (localSymbols χ S) = ⊤ := by
    refine (eq_top_iff' _).mpr fun a ↦ pi_mem_of_mulSingle_mem a fun v ↦ ?_
    obtain ⟨y, hy⟩ : ∃ y, (abelianLift χ).comp (artinAt Γ v) y = a v := (a v).prop
    refine ⟨locIdele v.val y, ?_, eq_update_iff.mpr ?_⟩
    · simp +contextual [← and_forall_ne v.val]
    · unfold localSymbols
      aesop
  -- So the index of the kernel is the order of the product of the ranges.
  have h_index : (localSymbols χ S).ker.relIndex (idelesUnitOff S) =
      ∏ v ∈ S, Nat.card ((abelianLift χ).comp (artinAt Γ v)).range := by
    rw [relIndex_ker, h_onto, card_top, Nat.card_pi, ← prod_coe_sort S]
  -- `T` is the union of the fibres over `S`.
  have h_card : (FinPlace.comap (algebraMap K L) ⁻¹' (S : Set (FinPlace K))).ncard =
      ∑ v ∈ S, {w : FinPlace L | w.below K = v}.ncard :=
    card_preimage_eq_sum_card_image_eq fun v hv ↦ hT.subset fun w (hw : _ = v) ↦ by simpa [hw]
  -- Multiply the local counts `card_range_abelianLift_comp_artinAt` over `S`.
  rw [h_index, h_card, ← prod_pow, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  exact prod_eq_pow_card fun v _ ↦ card_range_abelianLift_comp_artinAt hl rfl v

/-- Hasse's norm theorem in prime degree. Let `L / K` be Galois of prime degree, cut out by `χ`, and
let `χ` kill every complex conjugation. If `x` in `Kˣ` has trivial local symbol
`χ (artinAt Γ v x)` at every finite place `v` of `K`, then `x` is the norm of some `z` in
`Lˣ`. -/
lemma exists_map_norm_eq_of_abelianLift_artinAt_eq_one [IsGalois K L]
    (hl : (Module.finrank K L).Prime) (hc : ∀ c : Γ, IsComplexConj c → c ∈ ker χ) {x : Kˣ}
    (hx : ∀ v : FinPlace K, abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1) :
    ∃ z : Lˣ, z.map (Algebra.norm K) = x := by
  classical
  -- For `S` large let `τ` be the tuple of the local symbols at `S`. Among the `S`-units, the norms
  -- lie in the kernel of `τ`, and a count shows that the two groups have the same index.
  -- `S` holds the ramified places, the divisor of `x`, the divisors of the norms of ideles `rep c`
  -- that represent the ideal classes of `L`, and generators of the class group of `K`.
  obtain ⟨cl, h_cl : cl.ker = principalIdele.range ⊔ idelesUnitOff ∅⟩ :=
    exists_idele_classGroup_hom (K := L)
  let rep : ClassGroup (𝓞 L) → (𝔸f L)ˣ := invFun cl
  have h_rep : (⋃ c : ClassGroup (𝓞 L), {v | Valued.v (adeleNorm K L (rep c).val v) ≠ 1}).Finite :=
    Set.finite_iUnion fun c ↦ finite_setOf_valued_val_ne_one (.map (adeleNorm K L) (rep c))
  obtain ⟨S, hS : S.Finite, h_sub, h_gen : principalIdele.range ⊔ idelesUnitOff S = ⊤⟩ :=
    exists_superset_sup_idelesUnitOff_eq_top
      ((h_rep.union (finite_ramified (isOpen_ker χ))).union
        (finite_setOf_valued_val_ne_one (principalIdele x)))
  obtain ⟨S, rfl⟩ : ∃ s' : Finset (FinPlace K), s' = S := hS.exists_finset_coe
  have h_off (v : FinPlace K) (hv : v ∉ SetLike.coe S) :
      ((∀ c : ClassGroup (𝓞 L), Valued.v (adeleNorm K L (rep c).val v) = 1) ∧
        ∀ A : ClosurePlace, IsPlaceOver A v → inertiaGroup Γ A ≤ ker χ) ∧
      v.valuation K x.val = 1 := by
    simpa using Set.notMem_subset h_sub hv
  let τ : (𝔸f K)ˣ →* (i : S) → ((abelianLift χ).comp (artinAt Γ i)).range := localSymbols χ S
  have h_norm (y : (𝔸f L)ˣ) : τ (Units.map (adeleNorm K L) y) = 1 :=
    funext fun _ ↦ Subtype.ext (abelianLift_artinAt_eq_one_of_mem_closure adeleNorm_mem_closure)
  -- Second inequality: the group `W = Kˣ (ker τ ∩ idelesUnitOff S)` is open and contains all norms,
  -- as every idele of `L` is `rep c` times a principal idele times a unit idele; so the index of
  -- `W` is at most the degree `l`.
  let W : Subgroup (𝔸f K)ˣ := principalIdele.range ⊔ τ.ker ⊓ idelesUnitOff S
  have h_open : IsOpen (SetLike.coe W) := by
    refine W.isOpen_of_mem_nhds ((eventually_artinAt_eq_one χ).mono ?_)
    rintro a ⟨h_unit, h_symbol⟩
    refine mem_sup_right ⟨funext fun v ↦ Subtype.ext (h_symbol v), ?_⟩
    exact mem_idelesUnitOff.2 fun v _ ↦ mem_idelesUnitOff.1 h_unit v (Set.notMem_empty v)
  have h_norms (y : (𝔸f L)ˣ) : Units.map (adeleNorm K L) y ∈ W := by
    obtain ⟨_, ⟨z, rfl⟩, u, hu, h_eq⟩ :
        ∃ a ∈ principalIdele.range, ∃ u ∈ idelesUnitOff ∅, a * u = (rep (cl y))⁻¹ * y :=
      mem_sup.mp (h_cl.le (cl.eq_iff.mp (invFun_eq ⟨y, rfl⟩).symm))
    rw [← mul_eq_of_eq_inv_mul h_eq, mul_rotate', map_mul]
    -- The norm of `rep (cl y)` times a unit idele is killed by `τ` and is a unit off `S`.
    have hu_val (w : FinPlace L) : Valued.v (u.val w) = 1 :=
      mem_idelesUnitOff.1 hu w (Set.notMem_empty w)
    exact Subgroup.mul_mem_sup (by simp)
      (by simp +contextual [h_norm, h_off, v_adeleNorm_eq_one, hu_val])
  have h_index : W.index ≤ Module.finrank K L :=
    index_le_finrank_of_adeleNorm_mem L h_open (fun y _ ↦ mem_sup_left ⟨y, rfl⟩) h_norms
  set l : ℕ := Module.finrank K L
  let T : Set (FinPlace L) := FinPlace.comap (algebraMap K L) ⁻¹' S
  have hT : T.Finite := by simpa using tendsto_place_comap_cofinite _ hS.compl_mem_cofinite
  let E : Subgroup Kˣ := (SetLike.coe S).unit K
  let N : Subgroup Kˣ := (T.unit L).map (Units.map (norm K))
  -- The local count: the index of `τ.ker` among the units off `S`.
  have h_local : τ.ker.relIndex (idelesUnitOff S) ^ (l - 1) * l ^ T.ncard = (l ^ l) ^ #S :=
    relIndex_ker_localSymbols_pow_mul_pow (χ := χ) hl S hT
  -- Compare with Tate's formula; the infinite places contribute the same power of `l`.
  have h_count : N.relIndex E * l = τ.ker.relIndex (idelesUnitOff S) := by
    have h_unr (w : FinPlace L) (hw : w.below K ∉ SetLike.coe S) :
        w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      have h_above : IsPlaceOver (placeOver w) w := w.isPlaceOver_placeOver
      obtain ⟨⟨-, h_inertia⟩, -⟩ := h_off (w.below K) hw
      obtain ⟨-, h_unramified : inertiaGroup Γ (placeOver w) ≤ ker χ → _ = 1, -⟩ :=
        h_above.isPlaceOver_below.ramification_in_tower (ker χ) h_above
      exact h_unramified (h_inertia _ h_above.isPlaceOver_below)
    have h_tate : (N.relIndex E * l) ^ (l - 1) * l ^ (T.ncard + Fintype.card (InfinitePlace L)) =
        (l ^ l) ^ ((S : Set (FinPlace K)).ncard + Fintype.card (InfinitePlace K)) :=
      relIndex_norm_unit_pow hl rfl hS h_gen h_unr rfl
    rw [Set.ncard_coe_finset, pow_add (l ^ l), ← h_local, mul_assoc, ← pow_mul, ← pow_add,
      (isUnramifiedAtInfinitePlaces_of_mem_ker hc).card_infinitePlace K L, mul_comm l] at h_tate
    exact (pow_left_inj hl.pred_pos.ne').mp (mul_right_cancel₀ (pow_ne_zero _ hl.ne_zero) h_tate)
  -- By `relIndex_mul_index_sup` the right side of `h_count` is `W.index ≤ l` times the index of the
  -- kernel.
  have h_le : N.relIndex E ≤ (τ.ker.comap principalIdele).relIndex E := by
    grw [← Nat.mul_le_mul_right_iff hl.pos, h_count,
      ← relIndex_mul_index_sup h_gen principalIdele_mem_idelesUnitOff, h_index]
  -- So `N` is all of the kernel of `τ` on the `S`-units, which contains `x`.
  have h_ker : N ≤ τ.ker.comap principalIdele := by
    rintro _ ⟨z, -, rfl⟩
    rw [Subgroup.mem_comap, ← map_adeleNorm_principalIdele]
    exact h_norm (principalIdele z)
  -- Index zero would make the left side of `h_local` vanish.
  have h_finite : (N.subgroupOf E).FiniteIndex := ⟨fun h_zero : N.relIndex E = 0 ↦ by
    simp [← h_count, h_zero, Nat.sub_ne_zero_of_lt hl.one_lt, eq_comm] at h_local⟩
  have h_eq : N.subgroupOf E = (τ.ker.comap principalIdele).subgroupOf E :=
    (comap_mono (f := E.subtype) h_ker).eq_of_not_lt fun h ↦ h_le.not_gt (index_strictAnti h)
  obtain ⟨z, -, hz⟩ : x ∈ N :=
    h_eq.ge (x := ⟨x, fun v hv ↦ (h_off v hv).right⟩) (funext fun v ↦ Subtype.ext (hx v))
  exact ⟨z, hz⟩

/-- Albert–Brauer–Hasse–Noether. Let α be a class in H²(Γ, Ωˣ), where Γ acts as the Galois group of
`New.Ω` (the algebraic closure of ℚ) over the number field K. If α restricts to zero on the
decomposition group of every place of Ω over a finite place of K (`h_dec`) and on an open subgroup
U of Γ containing all complex conjugations (`h_conj`, `h_res`: over an extension in which the real
places stay real), then α = 0. -/
lemma albert_brauer_hasse_noether (α : (unitsModule Γ).H2)
    (h_dec : ∀ {A : ClosurePlace} {v : FinPlace K}, IsPlaceOver A v →
      (unitsModule Γ).resH2 (decompGroup Γ A) α = 0)
    (U : OpenSubgroup Γ) (h_conj : ∀ g : Γ, IsComplexConj g → g ∈ U)
    (h_res : (unitsModule Γ).resH2 U α = 0) :
    α = 0 := by
  -- Reduce to the case where `U` is normal of prime index.
  wlog hU : U.Normal ∧ U.index.Prime with h_step
  · -- `α` dies on the normal core `W` of `U`; climb to `Γ` in steps `V ≤ U'` of prime index
    -- (`mem_of_prime_step`), applying the reduced case over the fixed field of `U'`.
    have h_finiteIndex : U.toSubgroup.FiniteIndex := U.finiteIndex_of_finite_quotient
    let W : OpenSubgroup Γ :=
      ⟨U.normalCore, isOpen_of_isClosed_of_finiteIndex _ (normalCore_isClosed _ U.isClosed)⟩
    -- Restriction to `W` factors through restriction to `U`.
    have h_factor : (unitsModule Γ).resH2 W α =
        (pairMapH2 (.mk (inclusion U.normalCore_le) (continuous_subtype_val.subtype_mk _)) .id)
          ((unitsModule Γ).resH2 U α) := by
      induction α using QuotientAddGroup.induction_on
      rfl
    have hW : (unitsModule Γ).resH2 W α = 0 := by rw [h_factor, h_res, map_zero]
    refine mem_of_prime_step ⊥ hW fun U' V hV _ h_le h_index s hs h_resV ↦ ⟨s, hs, ?_⟩
    obtain rfl : s = 0 := hs
    rw [sub_zero] at h_resV ⊢
    refine h_step ((unitsModule Γ).resH2 U' α) ?_ V ?_ h_resV ⟨hV, h_index⟩
    · -- `α` dies on the decomposition group in `Γ`, so on its intersection with `U'`, which is the
      -- decomposition group in `U'`.
      intro A v hA
      refine resH2_subgroupOf_eq_zero_symm (M := unitsModule Γ) (U := U') (V := decompGroup Γ A) ?_
      rw [h_dec hA.isPlaceOver_below, map_zero]
    · -- The conjugates of a complex conjugation are complex conjugations, so lie in `U`.
      rintro g ⟨j, hj⟩
      refine h_le fun b ↦ h_conj _ ⟨j.comp (toRingHom _ _ b⁻¹), fun x ↦ ?_⟩
      -- `b⁻¹ • (b g b⁻¹) • x = g • (b⁻¹ • x)`, so this is `hj` at `b⁻¹ • x`.
      simpa [mul_smul, Subgroup.smul_def] using hj (b⁻¹ • x)
  -- Now `U` is the kernel of a character `χ`, so `α` is a symbol `(χ, x)` (`cyclicClass_spec`). The
  -- local symbols of `x` are trivial, so `x` is a norm.
  obtain ⟨h_normal, h_prime⟩ := hU
  obtain ⟨U, hU_open⟩ := U
  obtain ⟨χ, rfl⟩ : ∃ χ : QZChar Γ, ker χ = U :=
    exists_ker_eq_of_isCyclic ⟨U, hU_open⟩ (isCyclic_of_prime_card (hp := ⟨h_prime⟩) rfl)
  obtain ⟨x, rfl⟩ : ∃ x : Kˣ, α = cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω (.ofMul x)) :=
    ((cyclicClass_spec χ).left α).mp h_res
  have h_symbol (v : FinPlace K) :
      abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1 :=
    v.isPlaceOver_placeOver.abelianLift_artinAt_eq_one_iff.mpr (h_dec v.isPlaceOver_placeOver)
  exact (cyclicClass_eq_zero_iff_norm (L := fixedFieldOf (ker χ)) x).mpr
    (exists_map_norm_eq_of_abelianLift_artinAt_eq_one (by rwa [finrank_fixedFieldOf]) h_conj
      h_symbol)

end New
