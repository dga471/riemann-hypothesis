module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
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
open Formalism.IndefR.FWT GlobalTheory.RealGeo

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}

local elab "exact_kern " t:term : tactic => do
  Lean.Elab.Tactic.closeMainGoalUsing `exact_kern fun _ _ => do
    Lean.Elab.Term.elabTerm t none

abbrev setCd (c : CDHaar) : Late B C := { b with G := { b.G with cd := c } }

theorem lawsM_tr {T : Core a.D} (h : LawsM T) : LawsM (core b T) := by
  have key : ∀ c : CDHaar, c = a.G.cd → LawsM (core (setCd b c) T) := by
    rintro _ rfl
    constructor
    case pins => exact_kern h.pins
    case half => exact_kern h.half
    case evalWD => exact_kern h.evalWD
    case unf => exact_kern h.unf
    case unTest => exact_kern h.unTest
    case chiTriv => exact_kern h.chiTriv
    case dictU => exact_kern h.dictU
    case spaceW => exact_kern h.spaceW
    case levelK => exact_kern h.levelK
    case xiAbs => exact_kern h.xiAbs
    case muUnit => exact_kern h.muUnit
    case muCont => exact_kern h.muCont
    case finVol => exact_kern h.finVol
    case cuspFD => exact_kern h.cuspFD
    case supDef => exact_kern h.supDef
    case cuspidalL2Subspace => exact_kern h.cuspidalL2Subspace
    case l2Def => exact_kern h.l2Def
    case unitIndep => exact_kern h.unitIndep
    case ptNe => exact_kern h.ptNe
  exact_kern key b.G.cd (cd_eq _ _)

theorem lawsJ_tr {T : CoreJ a.D} (h : LawsJ T) : LawsJ (coreJ b T) := by
  constructor
  case toLawsM => exact_kern lawsM_tr b h.toLawsM
  case cUnit => exact_kern h.cUnit
  case muVal => exact_kern h.muVal
  case muConj => exact_kern h.muConj
  case intAll => exact_kern h.intAll
  case modelW => exact_kern h.modelW
  case familyUniformisationBasePointOrthogonal => exact_kern h.familyUniformisationBasePointOrthogonal
  case kfHalf => exact_kern h.kfHalf
  case adPin => exact_kern h.adPin

variable {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m}

section Theta

variable {T : Core a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F} {i : Fin a.D.R.m} {Tp : Type} {tup : Tp → T0}

def omDat (O : OMDat T R i Tp tup) :
    @OMDat b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (inferInstance) iK A R)) ((i)) Tp tup :=
  @OMDat.mk b.D G _ _ Pl0 T0 (famM b A) (core b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (i :))) Tp tup
    (c' := (by with_unfolding_all exact (O.c' :)))
    (hle := (by with_unfolding_all exact (O.hle :)))
    (jL := (by with_unfolding_all exact (O.jL :)))
    (hV := (by with_unfolding_all exact (O.hV :)))
    (c0' := (by with_unfolding_all exact (O.c0' :)))
    (lev := (by with_unfolding_all exact (O.lev :)))
    (dδ := (by with_unfolding_all exact (O.dδ :)))
    (Cl' := (by with_unfolding_all exact (O.Cl' :)))
    (fCl := (by with_unfolding_all exact (O.fCl :)))
    (bad := (by with_unfolding_all exact (O.bad :)))
    (Lh := (by with_unfolding_all exact (O.Lh :)))
    (La := (by with_unfolding_all exact (O.La :)))
    (Nc := (by with_unfolding_all exact (O.Nc :)))
    (gam := (by with_unfolding_all exact (O.gam :)))
    (vol := (by with_unfolding_all exact (O.vol :)))
    (ep := (by with_unfolding_all exact (O.ep :)))
    (B := (by with_unfolding_all exact (O.B :)))
    (epF := (by with_unfolding_all exact (O.epF :)))
    (io := (by with_unfolding_all exact (O.io :)))
    (hw := (by with_unfolding_all exact (O.hw :)))
    (φ := (by with_unfolding_all exact (O.φ :)))
    (w := (by with_unfolding_all exact (O.w :)))
    (U₂ := (by with_unfolding_all exact (O.U₂ :)))
    (dict₂ := (by with_unfolding_all exact (O.dict₂ :)))
    (xi := (by with_unfolding_all exact (O.xi :)))
    (thAd := (by with_unfolding_all exact (O.thAd :)))
    (Plc := (by with_unfolding_all exact (O.Plc :)))

theorem omPins_tr {O : OMDat T R i Tp tup} {κ v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) :
    @OMDat.Pins b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (inferInstance) iK A R)) ((i)) Tp tup (omDat b O) ((@wt B C a b (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Late.D B C a).R.m i) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) κ)) ((v₀))
      ((ι)) ((x₀)) := by
  apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
  case lift =>
    have lift := h.lift
    apply (config := { synthAssignedInstances := false }) ThPinsR.mk
    case field => exact_kern lift.field
    case std => exact_kern lift.std
    case v0 => exact_kern lift.v0
    case lev => exact_kern lift.lev
    case c0 =>
      obtain ⟨x, y, z, h1, h2⟩ := lift.c0
      refine ⟨(by exact_kern x), (by exact_kern y), (by exact_kern z), ?_, (by exact_kern h2)⟩
      exact_kern famTie_imp b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1
  case tuple =>
    intro t
    have ht := h.tuple t
    apply (config := { synthAssignedInstances := false }) ThPinsT.mk
    case reps => exact_kern ht.reps
    case B => exact_kern ht.B
    case xi => exact_kern ht.xi
    case phi => exact_kern ht.phi
    case half => exact_kern ht.half
  case act => exact_kern h.act
  case bad => exact_kern h.bad
  case reps => exact_kern h.reps
  case ep => exact_kern h.ep
  case io => exact_kern h.io
  case w => exact_kern h.w
  case cov => exact_kern h.cov
  case cxi => exact_kern h.cxi
  case model₂ => exact_kern h.model₂

end Theta

variable {T : CoreJ a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F}

def fwTie {κ v₀} (x : FWTie T R κ v₀) :
    @FWTie b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) (by with_unfolding_all exact (alg b iK :)) (by with_unfolding_all exact (real b R :)) (fun i => by with_unfolding_all exact (wt b (κ (by with_unfolding_all exact (i :))) :)) (by with_unfolding_all exact (v₀ :)) :=
  @FWTie.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) (fun i => (by with_unfolding_all exact ((wt b (κ ((i)))) : _))) ((by with_unfolding_all exact (v₀ :)))
    (alg_eq := (by exact_kern x.alg_eq))
    (e := (by exact_kern x.e))
    (ks := (by exact_kern x.ks))
    (kap := (by exact_kern x.kap))
    (pt := (by exact_kern x.pt))
    (nrm_eq := (by exact_kern x.nrm_eq))
    (laws := lawsJ_tr b x.laws)
    (chiR := (by exact_kern x.chiR))
    (hv₀ := (by exact_kern x.hv₀))
    (x0 := (by exact_kern x.x0))
    (ev0 := (by exact_kern x.ev0))
    (ev := (by exact_kern x.ev))

def geoHalf {ph : Fin a.D.R.m → ℂ} (x : GeoHalf T R ph) :
    @GeoHalf b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (inferInstance) iK A R)) ((ph)) :=
  @GeoHalf.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (ph :)))
    (κ := fun i => (by with_unfolding_all exact ((wt b (x.κ ((i)))) : _)))
    (v₀ := (by with_unfolding_all exact (x.v₀ :)))
    (fw := (by with_unfolding_all exact ((fwTie b x.fw) :)))
    (bar := (by exact_kern x.bar))
    (O := fun i => (by with_unfolding_all exact ((omDat b (x.O ((i)))) : _)))
    (pins := fun i => (by exact_kern And.intro (x.pins ((i))).1 (omPins_tr b (x.pins ((i))).2)))
    (rhoGeo := (by exact_kern x.rhoGeo))
    (equivAll := (by exact_kern x.equivAll))
    (cTie := (by exact_kern x.cTie))
    (phase := (by exact_kern x.phase))

set_option maxHeartbeats 16000000 in
theorem inGeo_tr {ph : Fin a.D.R.m → ℂ} {x : GeoHalf T R ph} (h : InGeo x) :
    @InGeo b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (inferInstance) iK A R)) ((ph)) (geoHalf b x) := by
  -- Build the constructor using the indices in the goal so the kernel handles
  -- conversion of the transported fields.
  run_tac
    Lean.Elab.Tactic.closeMainGoalUsing `inGeo_tr fun target _ => do
      let source ← Lean.Meta.getFVarFromUserName `h
      let fields ← (Lean.getStructureFields (← Lean.getEnv) ``InGeo).mapM fun field => do
        Lean.Meta.mkProjection source field
      let ctor := Lean.mkConst ``InGeo.mk target.getAppFn.constLevels!
      return Lean.mkAppN (Lean.mkAppN ctor target.getAppArgs) fields

end GlobalTheory.Mem.R3.Tr

end
