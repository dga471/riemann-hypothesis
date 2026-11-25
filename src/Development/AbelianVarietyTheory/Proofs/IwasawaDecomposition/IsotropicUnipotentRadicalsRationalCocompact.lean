module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

namespace GlobalTheory.Mem.UnipCocompact

section Abstract

variable {S : Type} [Ring S] {st : S →+ S}

def cay (M : ℕ) (y : S) : S := (1 + y) * ∑ j ∈ Finset.range M, y ^ j

theorem cay_unitary (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) {M : ℕ} {y : S}
    (h0 : y ^ M = 0) (hy : st y = -y) : st (cay M y) * cay M y = 1 ∧ cay M y * st (cay M y) = 1 :=
  GlobalTheory.UnipFlagCore.cay_unitary hm hi h0 hy

theorem cay_sub {M : ℕ} {y : S} (h0 : y ^ M = 0) :
    cay M y - 1 - (y + y) = (y + y) * ∑ j ∈ Finset.range M, y ^ (j + 1) :=
  GlobalTheory.UnipFlagCore.cay_sub h0

variable {ι : Type} (ε : ι → S) (w : ι → ℤ)

def raise (i : ℕ) : AddSubgroup S where
  carrier := {x | ∀ a b, w a ≤ w b + i → ε a * x * ε b = 0}
  zero_mem' := by simp
  add_mem' hx hy a b hab := by rw [mul_add, add_mul, hx a b hab, hy a b hab, add_zero]
  neg_mem' hx a b hab := by rw [mul_neg, neg_mul, hx a b hab, neg_zero]

variable {ε w}

theorem raise_mul [Fintype ι] (he : CompleteOrthogonalIdempotents ε) (i : ℕ) {x y : S} (hx : x ∈ raise ε w i) (hy : y ∈ raise ε w i) :
    x * y ∈ raise ε w (i + 1) :=
  GlobalTheory.UnipFlagCore.raise_mul he i hx hy

theorem raise_le (i : ℕ) : raise ε w (i + 1) ≤ raise ε w i :=
  GlobalTheory.UnipFlagCore.raise_le i

theorem raise_st (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a) (i : ℕ) {x : S} (hx : x ∈ raise ε w i) : st x ∈ raise ε w i :=
  GlobalTheory.UnipFlagCore.raise_st hm hi hs i hx

theorem compact_mod_of_weights [Fintype ι] [TopologicalSpace S] [IsTopologicalRing S] (S₀ : Subring S) (h : S) (K : Set S)
    (hcont : Continuous st) (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K) (he : CompleteOrthogonalIdempotents ε)
    (he0 : ∀ a, ε a ∈ S₀) (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a) :
    ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0 →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ raise ε w 0) ∧ ∃ k ∈ K', g = γ * k := by
  apply GlobalTheory.UnipFlagCore.compact_mod_of_weights <;> assumption

variable {κ : Type} [Fintype κ]

def fam (st : S →+ S) (u : κ → S) : Option (κ ⊕ κ) → S :=
  fun x => x.elim (1 - ∑ j, Sum.elim u (fun j => st (u j)) j) (Sum.elim u fun j => st (u j))

def wt (d : κ → ℕ) (M : ℕ) : Option (κ ⊕ κ) → ℤ :=
  fun x => x.elim 0 (Sum.elim (fun j => (M : ℤ) - d j) fun j => (d j : ℤ) - M)

theorem fam_complete (hm : ∀ x y, st (x * y) = st y * st x) {u : κ → S} (hu : OrthogonalIdempotents u)
    (h13 : ∀ i j, u i * st (u j) = 0) (h31 : ∀ i j, st (u i) * u j = 0) : CompleteOrthogonalIdempotents (fam st u) :=
  GlobalTheory.UnipFlagCore.fam_complete hm hu h13 h31

theorem fam_st (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (u : κ → S) (d : κ → ℕ) (M : ℕ) :
    ∀ a, ∃ a', st (fam st u a) = fam st u a' ∧ wt d M a' = - wt d M a :=
  GlobalTheory.UnipFlagCore.fam_st hm hi u d M

theorem mem_raise_fam (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) {u : κ → S}
    (he : CompleteOrthogonalIdempotents (fam st u)) {d : κ → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (x : S) :
    x ∈ raise (fam st u) (wt d M) 0 ↔ (1 - ∑ j, u j) * x * (1 - st (∑ j, u j)) = 0 ∧
      (∀ i j, d i ≤ d j → u j * x * u i = 0) ∧ ∀ i j, d i ≤ d j → u j * st x * u i = 0 := by
  apply GlobalTheory.UnipFlagCore.mem_raise_fam <;> assumption

end Abstract

section Concrete

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem sandwich_eq_zero {A : Type} [CommRing A] {n r : ℕ} {C : Matrix (Fin n) (Fin r) A} {L : Matrix (Fin r) (Fin n) A}
    (hL : L * C = 1) (m : Matrix (Fin n) (Fin n) A) (i j : Fin r) :
    C * single j j (1 : A) * L * m * (C * single i i (1 : A) * L) = 0 ↔ (L * m * C) j i = 0 :=
  GlobalTheory.UnipFlagCore.sandwich_eq_zero hL m i j

theorem triangular_inv {A : Type} [CommRing A] {r : ℕ} (d : Fin r → ℕ) (X Y : Matrix (Fin r) (Fin r) A)
    (h : Y = -X - Y * X) (hX : ∀ i j, d i ≤ d j → X j i = 0) : ∀ i j, d i ≤ d j → Y j i = 0 :=
  GlobalTheory.UnipFlagCore.triangular_inv d X Y h hX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

private theorem sig_invol (x : E) : hc.sig (hc.sig x) = x := star_star x

private theorem isHermND_gram : IsHermND hc.sig V.gram :=
  ⟨fun i j => congrFun (congrFun (cT_gram hc V) i) j, (gram_det_isUnit V).ne_zero⟩

theorem perp_iff_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E)
    (hL : L * C = 1) (m : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) :
    (∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
        ∃ a, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ↔
      (1 - (C * L).map (inclR (F := F) (AF F))) * m * (1 - adj hc V ((C * L).map (inclR (F := F) (AF F)))) = 0 :=
  GlobalTheory.UnipFlagCore.perp_iff_idem (sig_invol hc) (isHermND_gram hc V) C L hL m

def radSet {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ) : Set (GA hc V) :=
  {g | (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ∧
    ∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
      ∃ a, ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a}

noncomputable def idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E) := (C * single j j (1 : E) * L).map (inclR (F := F) (AF F))

theorem idem_eq {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (j : Fin r) :
    idem (F := F) V C L j = C.map (inclR (F := F) (AF F)) * single j j (1 : AF F ⊗[F] E) * L.map (inclR (F := F) (AF F)) :=
  GlobalTheory.UnipFlagCore.idem_eq C L j

theorem sum_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) :
    ∑ j, idem (F := F) V C L j = (C * L).map (inclR (F := F) (AF F)) :=
  GlobalTheory.UnipFlagCore.sum_idem C L

theorem idem_complete {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (hL : L * C = 1)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (hLL : L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0) :
    CompleteOrthogonalIdempotents (fam (adj hc V) (idem V C L)) :=
  GlobalTheory.UnipFlagCore.idem_complete (sig_invol hc) (isHermND_gram hc V) C L hL h0 hLL

theorem adj_mat (g : GA hc V) : adj hc V (HA.mat _ hc.sig V.gram g).1 = (HA.mat _ hc.sig V.gram g⁻¹).1 :=
  GlobalTheory.UnipFlagCore.adj_mat (sig_invol hc) (isHermND_gram hc V) g

theorem mem_radSet_iff {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (hL : L * C = 1)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (hLL : L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GA hc V) :
    g ∈ radSet hc V C d ↔ (HA.mat _ hc.sig V.gram g).1 - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 :=
  GlobalTheory.UnipFlagCore.mem_radSet_iff (sig_invol hc) (isHermND_gram hc V) C L hL h0 hLL hd g

theorem closure_radSet_cocompact {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (hC : LinearIndependent E Cᵀ)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (d : Fin r → ℕ) :
    ∃ K : Set (Subgroup.closure (radSet hc V C d)), IsCompact K ∧
      ∀ n, ∃ γ ∈ (ratPts hc V).subgroupOf (Subgroup.closure (radSet hc V C d)), ∃ k ∈ K, n = γ * k := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.UnipFlagCore.closure_radSet_cocompact (sig_invol hc) (isHermND_gram hc V) C hC h0 d
  refine ⟨K, hK, fun n => ?_⟩
  obtain ⟨γ, ⟨a, ha1, ha2⟩, k, hk, rfl⟩ := hcov n
  exact ⟨γ, ⟨⟨a, ha1⟩, Subtype.ext ha2⟩, k, hk, rfl⟩

end Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

theorem radicals_cocompact : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → (∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k) ∧ (∃ K : Set (NI B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ B e, ∃ k ∈ K, n = γ * k) := by
  intro D B ρ e he
  have key : ∀ (d : Fin ρ → ℕ) (H : Subgroup (GA D B)), H = Subgroup.closure (radSet D.sp.cm B e d) →
      ∃ K : Set H, IsCompact K ∧ ∀ n, ∃ γ ∈ (GQ B).subgroupOf H, ∃ k ∈ K, n = γ * k := by
    rintro d _ rfl
    rw [GlobalTheory.AutFunCompare.GQ_eq]
    exact closure_radSet_cocompact D.sp.cm B e he.1 he.2 d
  refine ⟨key Fin.val _ rfl, key (fun _ => 0) _ ?_⟩
  have hs : (NI B e : Set (GA D B)) = radSet D.sp.cm B e fun _ => 0 := by
    ext g
    rw [GlobalTheory.AutFunCompare.NI_eq, SetLike.mem_coe, GlobalTheory.AutFunCompare.mem_unipRad_colSpan]
    refine and_congr ⟨fun h i => ⟨0, fun _ _ => rfl, ?_⟩, fun h => ?_⟩ Iff.rfl
    · rw [Matrix.mulVec_zero]
      exact funext fun k => congrFun (congrFun h k) i
    · ext k i
      obtain ⟨a, ha, h'⟩ := h i
      rw [show a = 0 from funext fun j => ha j le_rfl, Matrix.mulVec_zero] at h'
      exact congrFun h' k
  rw [← hs, Subgroup.closure_eq]

end GlobalTheory.Mem.UnipCocompact
