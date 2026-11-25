module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Vertical

noncomputable section

namespace SecFiniteUnit

theorem prod_natDegree_coeff {R ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R)
    (D : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, D i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (f i).coeff (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le_of_le ha' h1,
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' h1, h2]⟩

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}

abbrev lineSub (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial R :=
  SecAlgFinite.lineSub y m ij

def lineTop (y : Par e n → R) (ij : Fin (e + 1) × Fin n) : R :=
  Fin.cases (motive := fun _ => R) (y (.inr ij.2)) (fun i => y (.inl (i, ij.2))) ij.1

theorem lineSub_natDegree_le (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).natDegree ≤ groupWeight (e + 1) n ij 0 := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, SecAlgFinite.lineSub, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    · split_ifs <;> simp
  | succ i => simp [lineSub, SecAlgFinite.lineSub]

theorem lineSub_coeff (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).coeff (groupWeight (e + 1) n ij 0) = lineTop y ij := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, SecAlgFinite.lineSub, lineTop, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    split_ifs <;> simp [Polynomial.coeff_one]
  | succ i => simp [lineSub, SecAlgFinite.lineSub, lineTop, groupWeight, Fin.succ_ne_zero]

theorem weight_sum {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : Heights.IsMultiHomog δ g)
    {d : Fin (e + 1) × Fin n →₀ ℕ} (hd : AddMonoidAlgebra.coeff g d ≠ 0) :
    ∑ ij, d ij * groupWeight (e + 1) n ij 0 = δ := by
  have h := congrFun (hg hd) 0
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simpa [Finset.sum_apply, smul_eq_mul] using h

theorem lineSub_aeval {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : Heights.IsMultiHomog δ g)
    (y : Par e n → R) (m : Fin n) :
    (aeval (lineSub y m) g).natDegree ≤ δ ∧
      (aeval (lineSub y m) g).coeff δ =
        eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) := by
  have hprod : ∀ d ∈ g.support, (∏ ij, lineSub y m ij ^ d ij).natDegree ≤ δ ∧
      (∏ ij, lineSub y m ij ^ d ij).coeff δ = ∏ ij, lineTop y ij ^ d ij := by
    intro d hd
    have h := prod_natDegree_coeff Finset.univ (fun ij => lineSub y m ij ^ d ij)
      (fun ij => d ij * groupWeight (e + 1) n ij 0)
      (fun ij _ => Polynomial.natDegree_pow_le_of_le _ (lineSub_natDegree_le y m ij))
    rw [weight_sum hg (mem_support_iff.mp hd)] at h
    refine ⟨h.1, h.2.trans (Finset.prod_congr rfl fun ij _ => ?_)⟩
    rw [Polynomial.coeff_pow_of_natDegree_le (lineSub_natDegree_le y m ij), lineSub_coeff]
  rw [aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hprod d hd).1, ?_⟩
  have hspec : eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) = aeval (lineTop y) g := by
    rw [specRest, eval₂_comp_left, aeval_def]
    congr 1
    · ext a; simp
    · funext ⟨i, j⟩
      induction i using Fin.cases with
      | zero => simp [lineTop]
      | succ i => simp [lineTop]
  rw [hspec, aeval_def, eval₂_eq', Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, (hprod d hd).2]

theorem coord_integral {δ : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → R)
    (hg : IsChowForm Q (e + 1) g) (hδ : Heights.IsMultiHomog δ g)
    (hu : IsUnit (eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y))) (m : Fin n) :
    IsIntegral R (secCoord (Q.map (MvPolynomial.map (algebraMap k R))) y m) := by
  set P : Polynomial R := aeval (lineSub y m) g
  obtain ⟨N, hN⟩ := SecAlgFinite.isNilpotent_aeval_lineSub IncidenceNull.full Q g y hg m
  obtain ⟨hdeg, hcoeff⟩ := lineSub_aeval hδ y m
  obtain ⟨u, hu'⟩ := hu
  have hmonic : (Polynomial.C ((u⁻¹ : Rˣ) : R) * P).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one δ
      ((Polynomial.natDegree_C_mul_le _ _).trans hdeg)
      (by rw [Polynomial.coeff_C_mul, hcoeff, ← hu', Units.inv_mul])
  refine ⟨(Polynomial.C ((u⁻¹ : Rˣ) : R) * P) ^ N, hmonic.pow N, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, map_mul, mul_pow, hN, mul_zero]

end SecFiniteUnit

theorem SecFiniteUnit.proof : SecFiniteUnit.Statement :=
  fun _ _ _ _ _ _ _ _ Q g y hg hδ hu =>
    SecAlgFinite.finite_secAlg_of_isIntegral _ y (SecFiniteUnit.coord_integral Q g y hg hδ hu)

end

end GroundTheory.Heights₂.Heights
