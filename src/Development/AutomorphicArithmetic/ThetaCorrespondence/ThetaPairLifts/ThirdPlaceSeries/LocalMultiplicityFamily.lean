module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
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



section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

-- Compare the types in the kernel to avoid unfolding the stage records in the elaborator.
open Lean Elab Tactic in
local elab "exact_by_kernel " term:term : tactic =>
  closeMainGoalUsing `exact_by_kernel fun target _ => do
    let value ← elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    let actual ← instantiateMVars (← Meta.inferType value)
    let target ← instantiateMVars target
    let lctx ← instantiateLCtxMVars (← getLCtx)
    match Kernel.isDefEq (← getEnv) lctx actual target with
    | .ok true => pure value
    | .ok false => throwError "expected{indentExpr target}\nbut the term has type{indentExpr actual}"
    | .error error => throwError (error.toMessageData (← getOptions))



variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)


def yStructureLocal : NExpRealS (datL x L).R (datL x L).cG (SL L l.rat) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := {
    fi := by exact_by_kernel l.b.YS.fi
    geq := by exact_by_kernel l.b.YS.geq
    rho := by exact_by_kernel l.b.YS.rho
    chi := by exact_by_kernel l.b.YS.chi
    eF := by
      intro i j b h1 h2
      exact_by_kernel (l.b.YS.eF i j b h1 h2)
    bsup := by
      intro i j b h1 h2
      exact_by_kernel (l.b.YS.bsup i j b h1 h2)
    act := by
      intro i j b h1 h2 g y
      exact_by_kernel (l.b.YS.act i j b h1 h2 g y) }
  exact_by_kernel Y

def heckeHeightData : NExpRealH x.m.z.R x.m.z.cG l.rat.S l.b.YS where
  hL := l.rat.In.hL
  hs := l.b.Bs.hs
  cHk := fun i b k Q => algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) (l.b.Bs.cHk i b Q) ^ k
  cHk_zero := fun i b Q => pow_zero _
  cHk_unit := fun i b Q =>
    ((l.b.Bs.cHk i b Q).isUnit.map (algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)))).pow 1
  cHk_pow := fun i b k Q => by simp only [pow_one]
  hkEq := by rw [l.b.eF]; exact l.b.Bs.hkEq

def localHeckeHeightData : NExpRealH (datL x L).R (datL x L).cG (SL L l.rat) (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) := by
  let Y : NExpRealS (datL x L).R (datL x L).cG (ratL L l.rat.S) := by
    exact_by_kernel (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l)
  let H : NExpRealH (datL x L).R (datL x L).cG (ratL L l.rat.S) Y := {
    hL := by exact_by_kernel (heckeHeightData l).hL
    hs := by exact_by_kernel (heckeHeightData l).hs
    cHk := by exact_by_kernel (heckeHeightData l).cHk
    cHk_zero := by exact_by_kernel (heckeHeightData l).cHk_zero
    cHk_unit := by exact_by_kernel (heckeHeightData l).cHk_unit
    cHk_pow := by exact_by_kernel (heckeHeightData l).cHk_pow
    hkEq := by
      intro i j b h1 h2 k Q y hQ hsplit hk
      exact_by_kernel ((heckeHeightData l).hkEq i j b h1 h2 k Q y hQ hsplit hk) }
  exact_by_kernel H

def psiVectorLocal : ∀ i : Fin (DL x L).R.m, principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (DL x L) i) (DL x L).R.nV :=
  fun i => (rowPsi (a := x.o.Z) (oL x L).Z (l.mt.ad.PV i) :)
def characterChoiceLocal : NChoice (DL x L) := { l.c.ch with }
def localCharacterTupleAgreement : TupTied (DL x L) (cfD x L) (characterChoiceLocal L l) :=
  { l.c.tp with }
def localMultiplicityFamily : MtFam (DL x L) := fun μ j h1 h2 =>
  { l.mt.M μ j h1 h2 with }
def placeMapLocal : HeightOneSpectrum (𝓞 (maximalRealSubfield (DL x L).host.E)) → PlE (DL x L).host := l.Pq
def localEigenvalueDegree : ℕ → (DL x L).what₂.FT → ℕ → PlE (DL x L).host → ↥(DL x L).LL0 := l.rat.In.eig
def smallPlaceSet : Finset (PlE (DL x L).host) := l.rat.In.Sb
theorem twist_ok_local : ∀ v, TwistedAt (DL x L) v → IntegralHeckeForms.TwOK ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).k' v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v)
    (((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).psi' v).comp ((DL x L).ntw.art ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v))) := by
  exact_by_kernel l.c.ok


theorem thetaTie_yStructureLocal_nonempty : Nonempty (GlobalTheory.GeoTie.ThetaTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.fw (DL x L).nth) := by
  obtain ⟨g⟩ := l.b.geo
  refine ⟨{ side := ?_, isUnramified₂ := ?_ }⟩
  · intro i j b
    let side := g.side (i :) (j :) b
    exact { pt := by exact_by_kernel side.pt, cover := by exact_by_kernel side.cover,
            ev_eq := by exact_by_kernel side.ev_eq, fmUr := by exact_by_kernel side.fmUr,
            hk := by exact_by_kernel side.hk, hk_none := by exact_by_kernel side.hk_none }
  · exact_by_kernel g.isUnramified₂

theorem kept_characterChoiceLocal : Kept l.c.ch (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) :=
  ⟨sameGaloisL L, twistDataAgreeAcrossCoefficients_localized L, sameFormsL L, HEq.refl (Dof x).ntwbr, HEq.refl l.c.ch.twI, HEq.refl l.c.ch.sd,
    HEq.refl l.c.ch.Q, HEq.refl l.c.ch.k', HEq.refl l.c.ch.psi'⟩
theorem yStructureLocal_fi_e_heq : ∀ i y, HEq (((_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l).fi i).e y) y := l.b.fi
end GlobalTheory.HeightCounting.Fin3
end
end
