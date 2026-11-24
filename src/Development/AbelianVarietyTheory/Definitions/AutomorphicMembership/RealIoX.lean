module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
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

local elab "exact_kern " t:term : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `exact_kern fun _ _ =>
    Lean.Elab.Tactic.elabTerm t none

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def real {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @RealDat b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) :=
  @RealDat.mk b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK)
    (toLevCh := levCh b R.toLevCh)
    (hv0 := (by exact_kern R.hv0))
    (eG := (by exact_kern R.eG))
    (pl := (by exact_kern R.pl))
    (Sb := (by exact_kern R.Sb))
    (θ := (by exact_kern R.θ))
    (ψ := (by exact_kern R.ψ))
    (MY := fun j => (by exact_kern (ds b (R.MY j))))
    (MX := (by exact_kern (ds b R.MX)))
    (MW := fun i σ => (by exact_kern (ds b (R.MW (by exact_kern i) (by exact_kern σ)))))
    (cX := (by exact_kern (coefA b R.cX)))
    (cV := fun i => (by exact_kern (coefA b (R.cV (by exact_kern i)))))
    (B := (by exact_kern (famReal b R.B)))
    (prX := (by exact_kern R.prX))
    (HX := (by exact_kern R.HX))
    (HV := (by exact_kern R.HV))
    (HE := (by exact_kern R.HE))
    (HW := (by exact_kern R.HW))
    (gE := (by exact_kern R.gE))
    (gW := (by exact_kern R.gW))
    (jX := (by exact_kern R.jX))
    (jV := (by exact_kern R.jV))
    (νY := (by exact_kern R.νY))
    (fdY := (by exact_kern R.fdY))
    (ν0 := (by exact_kern R.ν0))
    (fd0 := (by exact_kern R.fd0))
    (νX := (by exact_kern R.νX))
    (fdX := (by exact_kern R.fdX))
    (νV := (by exact_kern R.νV))
    (fdV := (by exact_kern R.fdV))
    (νW := (by exact_kern R.νW))
    (fdW := (by exact_kern R.fdW))
    (ωY := (by exact_kern R.ωY))
    (ωX := (by exact_kern R.ωX))
    (ωP := (by exact_kern R.ωP))
    (vac := (by exact_kern R.vac))
    (vacX := (by exact_kern R.vacX))
    (vacP := (by exact_kern R.vacP))
    (vY := (by exact_kern R.vY))
    (vX := (by exact_kern R.vX))
    (vP := (by exact_kern R.vP))
    (ItY := (by exact_kern R.ItY))
    (ItX := (by exact_kern R.ItX))
    (ioY := (by exact_kern (ioYB b R)))
    (ioX := (by exact_kern (ioXB b R)))
    (Th := (by exact_kern R.Th))
    (BV := (by exact_kern R.BV))
    (ioP := (by exact_kern R.ioP))
    (thF := (by exact_kern R.thF))
    (thG := (by exact_kern R.thG))
    (nW := (by exact_kern R.nW))
    (FW := (by exact_kern R.FW))
    (mu := (by exact_kern R.mu))
    (twPl := (by exact_kern R.twPl))
    (kap := (by exact_kern R.kap))
    (lam := (by exact_kern R.lam))
    (err0 := (by exact_kern R.err0))

theorem real_ioY {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoYT (@MultT a.D) R) ((R.ioY)) _ (@RealDat.ioY b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by exact_kern (castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoYT (@m) R) (multT_eq b a)) (by exact_kern R.ioY)).2)

theorem real_ioX {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoXT (@MultT a.D) R) ((R.ioX)) _ (@RealDat.ioX b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by exact_kern (castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoXT (@m) R) (multT_eq b a)) (by exact_kern R.ioX)).2)

def real3 {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) :
    @RealDat3 b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) :=
  @RealDat3.mk b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) (by exact_kern (real b R.toRealDat)) (by exact_kern R.plI) (by exact_kern R.SF) (by exact_kern R.phs)
    (by exact_kern R.lam3)

end GlobalTheory.Mem.R3.Tr

end
