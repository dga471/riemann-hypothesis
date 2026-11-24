module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
set_option linter.style.haveILetI false

local elab "exact_kern " t:term : tactic => do
  Lean.Elab.Tactic.closeMainGoalUsing `exact_kern fun _ _ => do
    Lean.Elab.Term.elabTerm t none

section Spaces


variable (a) in
def goodPartB : type_of% (@goodPart b.D) := @fun V S θ M J χ e => (by with_unfolding_all exact ((@goodPart a.D ((V)) ((S)) ((θ)) (((ds a M))) ((J)) ((χ)) ((e))) : _))


variable (a) in
theorem goodPart_eq : @goodPart b.D = @goodPartB B C a b := by
  funext V S θ M J χ e
  delta goodPart
  rewrite [mult_eq a b]
  exact_kern Eq.refl (@goodPartB B C a b V S θ M J χ e)


variable (a) in
def partFullB : type_of% (@partFull b.D) := @fun V S θ M J χ Sb c => (by with_unfolding_all exact ((@partFull a.D ((V)) ((S)) ((θ)) (((ds a M))) ((J)) ((χ)) ((Sb)) ((c))) : _))


variable (a) in
theorem partFull_eq : @partFull b.D = @partFullB B C a b := by
  funext V S θ M J χ Sb c
  delta partFull
  rewrite [mult_eq a b]
  exact_kern Eq.refl (@partFullB B C a b V S θ M J χ Sb c)

end Spaces

section General

variable {D : D7} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev ccW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Submodule ℂ (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  m R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv))

def pIoYW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T) (k : ℕ) (io : ccW (@m) R t (k + 1) →ₗ[ℂ] ccW (@m) R t k) : Prop :=
  Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k) (ccW (@m) R t (k + 1)) (ccW (@m) R t k) io

def pIoXW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T)
    (io : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] ccW (@m) R t (D.R.m - 1)) : Prop :=
  Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (ccW (@m) R t (D.R.m - 1)) io

def thDnW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (y : IoYT (@m) R) (x : IoXT (@m) R) (t : T) :
    (R.HX t).H →ₗ[ℂ] (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) :=
  (ccW (@m) R t 0).subtype ∘ₗ Lift.thetaDn (ccW (@m) R t) (y t) (D.R.m - 1) ∘ₗ x t ∘ₗ
    (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

theorem io_congr (R : RealDat D A Ks) {m m' : type_of% (@MultT D)} (e : @m = @m') {β : Type}
    (f : ∀ m : type_of% (@MultT D), IoYT (@m) R → IoXT (@m) R → β) (y : IoYT (@m) R) (x : IoXT (@m) R) :
    f (@m) y x = f (@m') (castAlong (congrArg (fun m : type_of% (@MultT D) => IoYT (@m) R) e) y).1
      (castAlong (congrArg (fun m : type_of% (@MultT D) => IoXT (@m) R) e) x).1 := by
  subst e
  exact (congrArg₂ (f (@m)) (castAlong_rfl y) (castAlong_rfl x)).symm

end General

section Two

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) {F : Face a.D A}

theorem eeat_eq : R.EEat = (@RealDat.EEat (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) := by
  funext P
  exact_kern congrArg (fun m : type_of% (@goodPart a.D) =>
    m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0) (goodPart_eq b a)

theorem wall_eq : R.Wall = (by with_unfolding_all exact ((letI := alg b iK; (real b R).Wall) :)) := by
  funext i σ
  exact_kern congrArg (fun m : type_of% (@Mult.Mult a.D) =>
    m R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))) (mult_eq b a)

theorem wat_eq : R.Wat = (by with_unfolding_all exact ((letI := alg b iK; (real b R).Wat) :)) := by
  funext i σ P
  exact_kern congrArg (fun m : type_of% (@goodPart a.D) =>
    m R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (R.eWf i σ)) (goodPart_eq b a)

theorem thDn_eq : R.thDn = (@RealDat.thDn (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) :=
  by exact_kern io_congr R (multT_eq b a) (fun m y x => thDnW (@m) R y x) R.ioY R.ioX

theorem pTh_eq : R.PTh = (@RealDat.PTh (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 T (@famM B C a b G ‹Group G› ‹Fintype G› Pl0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real B C a b G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R)) :=
  by exact_kern congrArg (fun (d : type_of% R.thDn) (t : T) (g : (R.HX t).H →ₗ[ℂ] R.HE.H) =>
    ∀ x, R.HE.e (g x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (d t x))) (thDn_eq b R)

theorem pThF_eq : R.PThF = (by with_unfolding_all exact ((letI := alg b iK; (real b R).PThF) :)) := by
  funext i t th
  exact_kern congrArg (fun W : type_of% R.Wall =>
    (∀ x, th x ∈ W i (sg0 a.D A)) ∧
      ∃ thP, Lift.IsThetaP (R.νV i t) (R.fdV i t) (fun g h f => thetaKO (R.ωP i t) h g f) (R.ptP i t) (R.ioP i)
          (LinearMap.range (R.extV i t)) thP ∧
        ∀ x (v : ∀ ρ, lowT (R.MW i (sg0 a.D A)) ρ),
          th x (fun ρ => v ρ) = thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)) (wall_eq b R)

end Two

section Two

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A}


omit [Field Ks] [NumberField Ks] iK in
theorem levIs_tr {L : Links.LevCh a.D T} {μ0 : T} (h : L.Is μ0) : (levCh b L).Is μ0 := by
  constructor
  case mu0 => exact_kern h.mu0
  case eta => exact_kern h.eta
  case xi => exact_kern h.xi
  case xi_inj => exact_kern h.xi_inj
  case xi_base => exact_kern h.xi_base
  case xi_fin => exact_kern h.xi_fin
  case xi_triv => exact_kern h.xi_triv
  case xi_tame => exact_kern h.xi_tame
  case Pg => exact_kern h.Pg
  case Q_pl => exact_kern h.Q_pl
  case Q_off => exact_kern h.Q_off
  case Q_de => exact_kern h.Q_de
  case Q_ram => exact_kern h.Q_ram
  case chi => exact_kern h.chi
  case xiR => exact_kern h.xiR
  case βY => exact_kern h.βY
  case βX => exact_kern h.βX
  case βV => exact_kern h.βV
  case βW => exact_kern h.βW

theorem isFam_tr (h : R.IsFam) : letI := alg b iK; (real b R).IsFam := by
  letI := alg b iK
  constructor
  case tie =>
    unfold RealDat.fam_tie
    rw [famTie_eq a b]
    exact_kern h.tie
  case Sb => exact_kern h.Sb
  case roots => exact_kern h.roots
  case pl_onto => exact_kern h.pl_onto
  case degR => exact_kern h.degR
  case degL => exact_kern h.degL
  case muVal => exact_kern h.muVal
  case etaVal => exact_kern h.etaVal

theorem isModels_tr (h : R.IsModels) : letI := alg b iK; (real b R).IsModels := by
  letI := alg b iK
  constructor
  case inf => exact_kern h.inf
  case vpos => exact_kern h.vpos
  case cX => exact_kern h.cX
  case cV => exact_kern h.cV
  case prX => exact_kern h.prX
  case HX => exact_kern h.HX
  case HV => exact_kern h.HV
  case HE =>
    unfold RealDat.models_HE
    rw [← eeat_eq b R]
    exact_kern h.HE
  case HW =>
    unfold RealDat.models_HW
    rw [← wall_eq b R]
    exact_kern h.HW
  case gE => exact_kern h.gE
  case gW => exact_kern h.gW
  case jX => exact_kern h.jX
  case jV => exact_kern h.jV
  case νY => exact_kern h.νY
  case νY' => exact_kern h.νY'
  case ν0 => exact_kern h.ν0
  case νX => exact_kern h.νX
  case νV => exact_kern h.νV
  case νW => exact_kern h.νW
  case BV => exact_kern h.BV
  case order => exact_kern h.order



theorem isChainW_tr (h : R.IsChainW) : letI := alg b iK; (real b R).IsChainW := by
  letI := alg b iK
  constructor
  case ωY =>
    intro t k hk
    exact_kern weilDatum_imp b _ _ _ _ _ _ (h.ωY t k hk)
  case ωX =>
    intro t
    exact_kern weilDatum_imp b _ _ _ _ _ _ (h.ωX t)
  case vY =>
    unfold RealDat.chain_vY IsStepVecOf IsVacO IsThetaAt
    rw [vacuum_eq a b, thetaFun_eq a b, placeModel_eq a b]
    exact_kern h.vY
  case vX =>
    unfold RealDat.chain_vX IsStepVecOf IsVacO IsThetaAt
    rw [vacuum_eq a b, thetaFun_eq a b, placeModel_eq a b]
    exact_kern h.vX
  case ptY =>
    intro t k hk P
    exact_kern thetaFun_imp b _ _ _ _ (h.ptY t k hk P)
  case ptX =>
    intro t P
    exact_kern thetaFun_imp b _ _ _ _ (h.ptX t P)
  case ItY =>
    unfold RealDat.cw_ItY RealDat.PItY
    rw [itW_eq a b]
    exact_kern h.ItY
  case ItX =>
    unfold RealDat.cw_ItX RealDat.PItX
    rw [itW_eq a b]
    exact_kern h.ItX
  case ioY =>
    exact_kern cast (io_congr R (multT_eq b a)
      (fun m y _ => ∀ t k, k + 1 < a.D.R.m → OrZero (pIoYW (@m) R t k) (y t k)) R.ioY R.ioX) h.ioY
  case ioX =>
    exact_kern cast (io_congr R (multT_eq b a)
      (fun m _ x => ∀ t, OrZero (pIoXW (@m) R t) (x t)) R.ioY R.ioX) h.ioX
  case Th =>
    have e := congrArg (fun p : type_of% R.PTh => ∀ t, OrZero (p t) (R.Th t)) (pTh_eq b R)
    exact_kern e.mp h.Th



theorem isThPW_tr (h : R.IsThPW) : letI := alg b iK; (real b R).IsThPW := by
  letI := alg b iK
  constructor
  case ωP =>
    intro i t
    exact_kern weilDatum_imp b _ _ _ _ _ _ (h.ωP i t)
  case vP =>
    unfold RealDat.thP_vP IsThPVecOf IsVacO IsThetaAt
    rw [vacuum_eq a b, thetaFun_eq a b, placeModel_eq a b]
    exact_kern h.vP
  case pt_theta =>
    intro i t P
    exact_kern thetaFun_imp b _ _ _ _ (h.pt_theta i t P)
  case ioP => exact_kern h.ioP
  case thF =>
    have e := congrArg (fun p : type_of% R.PThF => ∀ i t, OrZero (p i t) (R.thF i t)) (pThF_eq b R)
    exact_kern e.mp h.thF
  case thG => exact_kern h.thG



theorem exAt_tr (h : R.ExAt) : letI := alg b iK; (real b R).ExAt := by
  letI := alg b iK
  constructor
  case ItY =>
    unfold RealDat.ex_ItY RealDat.PItY
    rw [itW_eq a b]
    exact_kern h.ItY
  case ItX =>
    unfold RealDat.ex_ItX RealDat.PItX
    rw [itW_eq a b]
    exact_kern h.ItX
  case ioY => exact_kern cast (congrArg (fun m : type_of% (@MultT a.D) => ∀ t k, k + 1 < a.D.R.m → ∃ y, pIoYW (@m) R t k y) (multT_eq b a)) h.ioY
  case ioX => exact_kern cast (congrArg (fun m : type_of% (@MultT a.D) => ∀ t, ∃ y, pIoXW (@m) R t y) (multT_eq b a)) h.ioX
  case Th => exact_kern cast (congrArg (fun p : type_of% R.PTh => ∀ t, ∃ y, p t y) (pTh_eq b R)) h.Th
  case ioP => exact_kern h.ioP
  case thF => exact_kern cast (congrArg (fun p : type_of% R.PThF => ∀ i t, ∃ y, p i t y) (pThF_eq b R)) h.thF
  case thG => exact_kern h.thG

theorem lLevelW_tr (h : R.LLevelW F) : letI := alg b iK; (real b R).LLevelW (face b F) := by
  exact_kern cast (congrArg (fun W : type_of% R.Wat => ∀ c i σ, R.WS F c i σ = (W i σ (R.levL F c σ)).comap (R.HW i σ).e) (wat_eq b R)) h

end Two

end GlobalTheory.Mem.R3.Tr

end
