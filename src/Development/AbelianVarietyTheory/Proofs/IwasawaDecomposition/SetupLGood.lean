module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar




variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))

local elab "exact_kern " t:term : tactic => do
  Lean.Elab.Tactic.closeMainGoalUsing `exact_kern fun _ _ => do
    Lean.Elab.Term.elabTerm t none

def twL {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (Dof x) A) : GlobalTheory.ExportSeries.Twist (DL x L) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def twB {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (DL x L) A) : GlobalTheory.ExportSeries.Twist (Dof x) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def frL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (F : GlobalTheory.ExportSeries.Frame S U) : @GlobalTheory.ExportSeries.Frame (DL x L) ((S)) ((U)) where
  ψ := (by with_unfolding_all exact (F.ψ :))
  θ := (by with_unfolding_all exact (F.θ :))
  sT := (by with_unfolding_all exact (F.sT :))
  BS := (by with_unfolding_all exact (F.BS :))
  BT := (by with_unfolding_all exact (F.BT :))
  ΛS := (by with_unfolding_all exact (F.ΛS :))
  ΛT := (by with_unfolding_all exact (F.ΛT :))
  βS := (by with_unfolding_all exact (F.βS :))
  βT := (by with_unfolding_all exact (F.βT :))
  f₀ := (by with_unfolding_all exact (F.f₀ :))

def tdL {r : ℕ} (G : GlobalTheory.ExportSeries.TypeDat (Dof x) r) : GlobalTheory.ExportSeries.TypeDat (DL x L) r := ⟨(by with_unfolding_all exact (G.Pg :)), (by with_unfolding_all exact (G.P :)), (by with_unfolding_all exact (G.mu :))⟩

def wtL {n : ℕ} (u : GlobalTheory.ExportSeries.Weight (Dof x) n) : GlobalTheory.ExportSeries.Weight (DL x L) n :=
  ⟨(by with_unfolding_all exact (u.p :)), (by with_unfolding_all exact (u.q :)), (by with_unfolding_all exact (u.ap :)), (by with_unfolding_all exact (u.am :)), (by with_unfolding_all exact (u.c :)), (by with_unfolding_all exact (u.lam :))⟩

def baseL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (Z : GlobalTheory.ExportSeries.Base S U) : @GlobalTheory.ExportSeries.Base (DL x L) ((S)) ((U)) where
  hr := (by with_unfolding_all exact (Z.hr :))
  F := frL L Z.F
  G := (by with_unfolding_all exact ((tdL L Z.G) :))
  de := twL L Z.de
  w := (by with_unfolding_all exact ((wtL L Z.w) :))
  mu0 := (by with_unfolding_all exact (Z.mu0 :))
  eta := (by with_unfolding_all exact (Z.eta :))

def setupL (ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw) : GlobalTheory.SeriesTie.Setup (DL x L).ntw where
  rc := ⟨(by with_unfolding_all exact (ρ.rc.κ :)), (by with_unfolding_all exact (ρ.rc.art :))⟩
  ch := (by with_unfolding_all exact (ρ.ch :))
  bad := (by with_unfolding_all exact (ρ.bad :))
  e := (by with_unfolding_all exact (ρ.e :))
  ek := (by with_unfolding_all exact (ρ.ek :))
  B := fun i j b => (by with_unfolding_all exact ((baseL L (ρ.B ((i)) ((j)) b)) : _))
  om := fun i j b χ => (by with_unfolding_all exact ((ρ.om ((i)) ((j)) b ((χ))) : _))
  Cl := fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  finCl := fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  rep := fun i j b t c => (by with_unfolding_all exact ((ρ.rep ((i)) ((j)) b (twB L t) c) : _))
  β := (by with_unfolding_all exact (ρ.β :))
  eG := (by with_unfolding_all exact (ρ.eG :))

theorem twL_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (Dof x) A} (h : t.Good) : (twL L t).Good :=
  ⟨by exact_kern h.isOpen, by exact_kern h.rat, by exact_kern h.real, by exact_kern h.split, by exact_kern h.unram, by exact_kern h.res⟩

theorem twB_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (DL x L) A} (h : t.Good) : (twB L t).Good :=
  ⟨by exact_kern h.isOpen, by exact_kern h.rat, by exact_kern h.real, by exact_kern h.split, by exact_kern h.unram, by exact_kern h.res⟩

theorem placesOK_L {Pg Q : Finset (HeightOneSpectrum (𝓞 (Dof x).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (Dof x) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (DL x L) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem placesOK_B {Pg Q : Finset (HeightOneSpectrum (𝓞 (DL x L).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (DL x L) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (Dof x) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem wtL_good {n : ℕ} {u : GlobalTheory.ExportSeries.Weight (Dof x) n} (h : u.Good) : (wtL L u).Good := ⟨by exact_kern h.le, by exact_kern h.lam_eq⟩

theorem thetaFun_L_iff {S U : Formalism.BasicNotions.TH.HSp (Dof x)}
    (F : GlobalTheory.ExportSeries.Frame S U) (f : Formalism.IndefR.Datum.WO S U → ℂ) :
    @Formalism.IndefR.Datum.IsThetaFunO (DL x L) (frL L F).ψ S U f ↔
      @Formalism.IndefR.Datum.IsThetaFunO (Dof x) F.ψ S U f := by
  constructor <;> intro h <;>
    exact ⟨by exact_kern h.quasi, by exact_kern h.level, by exact_kern h.cont, by exact_kern h.smooth⟩

theorem frL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {F : GlobalTheory.ExportSeries.Frame S U} (h : F.Good) : (frL L F).Good :=
  { rank_le := by exact_kern h.rank_le
    onbS := by exact_kern h.onbS
    cartT := by exact_kern h.cartT
    onbT := by exact_kern h.onbT
    sdS := by exact_kern h.sdS
    sdT := by exact_kern h.sdT
    frS := by exact_kern h.frS
    frT := by exact_kern h.frT
    vac := by
      rcases h.vac with ⟨hstd, hinf, htheta, hlat, hfock, hnorm⟩
      exact ⟨by exact_kern hstd, by exact_kern hinf,
        ⟨by exact_kern htheta.quasi, by exact_kern htheta.level, by exact_kern htheta.cont, by exact_kern htheta.smooth⟩,
        by exact_kern hlat, by exact_kern hfock, by exact_kern hnorm⟩ }

theorem baseL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {Z : GlobalTheory.ExportSeries.Base S U} (h : Z.Good) : (baseL L Z).Good :=
  { even := by exact_kern h.even
    odd := by exact_kern h.odd
    frame := frL_good L h.frame
    de := twL_good L h.de
    places := by exact_kern placesOK_L L h.places
    wt := by exact_kern wtL_good L h.wt
    sig := by exact_kern h.sig
    sigOK := by exact_kern h.sigOK
    eta := by exact_kern h.eta
    hecke := by exact_kern h.hecke
    real := by exact_kern h.real
    unram := by exact_kern h.unram
    tame := by exact_kern h.tame
    inf := by exact_kern h.inf }

theorem setupL_good {ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw} (h : ρ.Good) : (setupL L ρ).Good :=
  { rc := ⟨by exact_kern h.rc.cont, by exact_kern h.rc.rat, by exact_kern h.rc.loc, by exact_kern h.rc.artin⟩
    ch := fun i => ⟨by exact_kern (h.ch ((i))).pair, by exact_kern (h.ch ((i))).one⟩
    bad_ne := by exact_kern h.bad_ne
    goodSetup_bad_mem_badPlaces := by exact_kern h.goodSetup_bad_mem_badPlaces
    goodSetup_badPlaces_conj := by exact_kern h.goodSetup_badPlaces_conj
    goodSetup_placesOverTwo_subset := by exact_kern h.goodSetup_placesOverTwo_subset
    goodSetup_count_eq_zero_off_badPlaces := by exact_kern h.goodSetup_count_eq_zero_off_badPlaces
    e_LL0 := by exact_kern h.e_LL0
    ek_e := by exact_kern h.ek_e
    base := fun i j b => by exact_kern baseL_good L (h.base ((i)) ((j)) b)
    latS := by exact_kern h.latS
    latT := by exact_kern h.latT
    Pg := by exact_kern h.Pg
    delta := fun i j b => by
      have hd := congrArg (twL L) (h.delta i j b)
      exact_kern hd
    weil := fun i j b t ht => by
      let t₀ := twB L t
      have hw := GlobalTheory.Mem.R3.Tr.weilDatum_imp (a := x.o.Z) (oL x L).Z
        _ _ _ _ _ _ (h.weil i j b t₀ (twB_good L ht))
      exact_kern hw
    classes := fun i j b t ht hA =>
      have h' := h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t) (twB_good L ht) ⟨(by with_unfolding_all exact ((placesOK_B L hA.1) :)), (by with_unfolding_all exact (hA.2 :))⟩
      ⟨by exact_kern h'.fin, by exact_kern h'.reps, by exact_kern h'.stab⟩ }


open GlobalTheory.SeriesTie in
theorem theta_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).theta = fun i j b h P => (by exact ρ.theta i j b h P) := by
  funext i j b h P
  delta GlobalTheory.SeriesTie.Setup.theta GlobalTheory.ExportSeries.Base.theta GlobalTheory.ExportSeries.Base.vecBase GlobalTheory.ExportSeries.Base.vecAt
    GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  rewrite [GlobalTheory.Mem.R3.Tr.placeModel_eq x.o.Z (oL x L).Z]
  exact_kern Eq.refl (ρ.theta i j b h P)


open GlobalTheory.SeriesTie in
theorem isDatum_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsDatum = fun i j b s h P => (by exact ρ.IsDatum i j b s h P) := by
  funext i j b s h P
  refine propext ⟨fun d => ?_, fun d => ?_⟩ <;>
    exact ⟨by exact_kern d.split, by exact_kern d.off,
      by exact_kern d.fin, by exact_kern d.supp, by exact_kern d.mem⟩

end GlobalTheory.HeightCounting.Fin3

end
