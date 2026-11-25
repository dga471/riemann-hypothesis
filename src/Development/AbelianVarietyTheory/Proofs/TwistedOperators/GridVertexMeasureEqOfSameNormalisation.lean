module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun

noncomputable section

namespace GlobalTheory.HaarNorm

theorem measLevW_unique {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) {μ μ' : Measure (GA D V)}
    (h : Formalism.IndefR.Lev.IsMeasLevW V K good μ) (h' : Formalism.IndefR.Lev.IsMeasLevW V K good μ') : μ = μ' := by
  apply _root_.GlobalTheory.FunObjModel.isMeasLevW_unique <;> assumption

theorem vol_nu_eq_of_isAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  apply GlobalTheory.FunObjModel.isAt_unique

end GlobalTheory.HaarNorm
