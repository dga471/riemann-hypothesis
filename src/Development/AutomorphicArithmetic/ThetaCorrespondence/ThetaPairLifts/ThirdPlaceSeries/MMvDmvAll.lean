module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LiftToGlobalDescentData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

/-- File-local kernel-checked exact: elaborates the term with no expected type
and lets the kernel perform the conversion check, avoiding the elaborator
`TransparencyMode.all` defeq blowup caused by `with_unfolding_all exact`. -/
elab "exact_kern " t:term : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `exact_kern fun _ _ => Lean.Elab.Term.elabTerm t none


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LiftToGlobalDescentData\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre\npublic import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove

noncomputable section
namespace UpperTheory.One.M


def New.nMv (_ : TrivialCondition) {D : D7} (m : Mv D) (n : NTiedGPlaceholder D) : NTiedGPlaceholder m.D :=
  @NTiedGPlaceholder.mk _

end UpperTheory.One.M
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\n\n"}
section -- clump:auto
@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M

def mvAll_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {C : NChoice D} (a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C) : _root_.GlobalTheory.HeightCounting.NAllCAlt m.D (m.ch C) := @_root_.GlobalTheory.HeightCounting.NAllCAlt.mk (_) (_)
    (gal := @_root_.Formalism.L2.NGalTiedAlt.mk (_)
      (fr := @_root_.Formalism.L2.OmFrame.mk (_)
        (jE := (by exact_kern (a.gal.fr.jE :)))
        (eOm := (by exact_kern (a.gal.fr.eOm :)))
        (comm := (by exact_kern (a.gal.fr.comm :))))
      (lp := @_root_.Formalism.L2.LPTiedPlaceholder.mk (_))
      (mt := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @_root_.Formalism.L2.MtReal.mk (_) (_) (_)
        (wt := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).wt : _)))
        (J := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).J : _)))
        (χ := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).χ : _)))
        (J_open := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).J_open : _)))
        (real := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).real : _)))
        (real_inj := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).real_inj : _)))
        (real_range := (by exact_kern ((@_root_.Formalism.L2.NGalTiedAlt.mt (_) a.gal ((x1)) ((x2)) ((x3)) ((x4))).real_range : _))))
      (hecke := @_root_.Formalism.L2.HeckeTied.mk (_) (_)
        (J_hyp := (by exact_kern (a.gal.hecke.J_hyp :)))
        (hT := (by exact_kern (a.gal.hecke.hT :)))
        (sameO := (by exact_kern (a.gal.hecke.sameO :)))
        (sep := (by exact_kern (a.gal.hecke.sep :)))
        (Q_conj := (by exact_kern (a.gal.hecke.Q_conj :)))
        (Q_same := (by exact_kern (a.gal.hecke.Q_same :))))
      (av := @_root_.Formalism.L2.AVTied.mk (_) (_)
        (S := (by exact_kern (a.gal.av.S :)))
        (irr := (by exact_kern (a.gal.av.irr :)))
        (inj := (by exact_kern (a.gal.av.inj :)))
        (surj := (by exact_kern (a.gal.av.surj :)))
        (typeV := (by exact_kern (a.gal.av.typeV :)))
        (ptV := (by exact_kern (a.gal.av.ptV :))))
      (au := @_root_.Formalism.L2.AUTiedAlt.mk (_) (_) (_) (_)
        (cls := (by exact_kern (a.gal.au.cls :)))
        (surj := (by exact_kern (a.gal.au.surj :)))
        (iso := (by exact_kern (a.gal.au.iso :)))
        (mult := (by exact_kern (a.gal.au.mult :)))
        (sph := (by exact_kern (a.gal.au.sph :)))
        (sat := (by exact_kern (a.gal.au.sat :)))
        (clsWt := (by exact_kern (a.gal.au.clsWt :)))
        (surjWt := (by exact_kern (a.gal.au.surjWt :)))
        (isoWt := (by exact_kern (a.gal.au.isoWt :)))
        (wt := (by exact_kern (a.gal.au.wt :)))
        (infW := (by exact_kern (a.gal.au.infW :)))
        (emb := (by exact_kern (a.gal.au.emb :))))
      (rational := (by exact_kern (a.gal.rational :)))
      (tup := (by exact_kern (a.gal.tup :)))
      (level := @_root_.Formalism.L2.LevelTied.mk (_) (_) (_)
        (prod := (by exact_kern (a.gal.level.prod :)))
        (para := (by exact_kern (a.gal.level.para :)))
        (uni := (by exact_kern (a.gal.level.uni :)))
        (wt := (by exact_kern (a.gal.level.wt :)))
        (hyp := (by exact_kern (a.gal.level.hyp :)))))
    (n := _root_.UpperTheory.One.M.New.nMv s m a.n)
    (loc := @_root_.Formalism.L2.LocTied.mk (_)
      (arith := (by exact_kern (a.loc.arith :)))
      (nbr := (by exact_kern (a.loc.nbr :)))
      (ntwbr := (by exact_kern (a.loc.ntwbr :))))
    (data := @_root_.Formalism.L2.NormalizedDataCompatibility.mk (_)
      (bj := (by exact_kern (a.data.bj :)))
      (bj_span := (by exact_kern (a.data.bj_span :)))
      (bj_rel := (by exact_kern (a.data.bj_rel :))))
    (cover := @_root_.Formalism.L2.NormalizedLocalCompatibility.mk (_) (_)
      (B := @_root_.Formalism.L2.NLocBase.mk (_) (_)
        (Oc := (by exact_kern (a.cover.B.Oc :)))
        (ringOc := (by exact_kern (a.cover.B.ringOc :)))
        (domOc := (by exact_kern (a.cover.B.domOc :)))
        (dvrOc := (by exact_kern (a.cover.B.dvrOc :)))
        (ec := (by exact_kern (a.cover.B.ec :)))
        (ec_w := (by exact_kern (a.cover.B.ec_w :)))
        (V := (by exact_kern (a.cover.B.V :)))
        (acgV := (by exact_kern (a.cover.B.acgV :)))
        (modV := (by exact_kern (a.cover.B.modV :)))
        (modVO := (by exact_kern (a.cover.B.modVO :)))
        (towV := (by exact_kern (a.cover.B.towV :)))
        (iV := (by exact_kern (a.cover.B.iV :)))
        (iV_basis := (by exact_kern (a.cover.B.iV_basis :)))
        (Qc := (by exact_kern (a.cover.B.Qc :)))
        (hL := (by exact_kern (a.cover.B.hL :)))
        (hL_def := (by exact_kern (a.cover.B.hL_def :)))
        (hK := (by exact_kern (a.cover.B.hK :)))
        (hK_def := (by exact_kern (a.cover.B.hK_def :)))
        (split := (by exact_kern (a.cover.B.split :)))
        (Qc_over := (by exact_kern (a.cover.B.Qc_over :)))
        (Qc_conj := (by exact_kern (a.cover.B.Qc_conj :))))
      (Q_eq := (by exact_kern (a.cover.Q_eq :)))
      (mx := (by exact_kern (a.cover.mx :)))
      (mx_max := (by exact_kern (a.cover.mx_max :)))
      (mx_inj := (by exact_kern (a.cover.mx_inj :)))
      (mx_all := (by exact_kern (a.cover.mx_all :)))
      (phO := (by exact_kern (a.cover.phO :)))
      (phK := (by exact_kern (a.cover.phK :)))
      (phK_alg := (by exact_kern (a.cover.phK_alg :)))
      (phK_emb := (by exact_kern (a.cover.phK_emb :)))
      (Psi := (by exact_kern (a.cover.Psi :)))
      (Psi_inj := (by exact_kern (a.cover.Psi_inj :)))
      (Psi_range := (by exact_kern (a.cover.Psi_range :)))
      (Psi_pr := (by exact_kern (a.cover.Psi_pr :)))
      (ptX := (by exact_kern (a.cover.ptX :)))
      (ptX_hT := (by exact_kern (a.cover.ptX_hT :)))
      (iotaC := (by exact_kern (a.cover.iotaC :)))
      (iotaC_coh := (by exact_kern (a.cover.iotaC_coh :))))
    (chiD := @_root_.Formalism.L2.NC.NChiData.mk (_)
      (mu0 := (by exact_kern (a.chiD.mu0 :)))
      (etaT := (by exact_kern (a.chiD.etaT :)))
      (del := (by exact_kern (a.chiD.del :)))
      (psi := (by exact_kern (a.chiD.psi :)))
      (chiI := (by exact_kern (a.chiD.chiI :)))
      (embO := (by exact_kern (a.chiD.embO :))))
    (chi := @_root_.Formalism.L2.NC.NormalizedCharacterCompatibility.mk (_) (_)
      (psi := (by exact_kern (a.chi.psi :)))
      (del_fix := (by exact_kern (a.chi.del_fix :)))
      (delta := (by exact_kern (a.chi.delta :)))
      (chi1 := (by exact_kern (a.chi.chi1 :)))
      (ringSpec_sidedEmbedding_fixedField := (by exact_kern (a.chi.ringSpec_sidedEmbedding_fixedField :)))
      (etaT_unr := (by exact_kern (a.chi.etaT_unr :)))
      (etaT_inf := (by exact_kern (a.chi.etaT_inf :)))
      (lamG := (by exact_kern (a.chi.lamG :))))
    (rho := @_root_.Formalism.L2.NR.NRhoTied.mk (_)
      (rbarSS := (by exact_kern (a.rho.rbarSS :)))
      (rbar := (by exact_kern (a.rho.rbar :)))
      (rhoS := (by exact_kern (a.rho.rhoS :))))
    (types := @_root_.Formalism.L2.NormalizedTypesCompatibility.mk (_) (_)
      (eM := (by exact_kern (a.types.eM :)))
      (eM_K := (by exact_kern (a.types.eM_K :)))
      (tA := (by exact_kern (a.types.tA :)))
      (tκ := (by exact_kern (a.types.tκ :)))
      (teichC_def := (by exact_kern (a.types.teichC_def :)))
      (iota_loc := (by exact_kern (a.types.iota_loc :)))
      (ζ := (by exact_kern (a.types.ζ :)))
      (ζ_gen := (by exact_kern (a.types.ζ_gen :)))
      (O := (by exact_kern (a.types.O :)))
      (eSer_def := (by exact_kern (a.types.eSer_def :)))
      (kv := (by exact_kern (a.types.kv :)))
      (tg_tame := (by exact_kern (a.types.tg_tame :)))
      (O_equiv := (by exact_kern (a.types.O_equiv :)))
      (O_tw := (by exact_kern (a.types.O_tw :)))
      (eP := (by exact_kern (a.types.eP :)))
      (locPar_def := (by exact_kern (a.types.locPar_def :))))
    (twF := @_root_.Formalism.L2.TwFrame.mk (_)
      (K0 := (by exact_kern (a.twF.K0 :)))
      (eO0 := (by exact_kern (a.twF.eO0 :)))
      (j0 := (by exact_kern (a.twF.j0 :)))
      (Lw := (by exact_kern (a.twF.Lw :)))
      (eO := (by exact_kern (a.twF.eO :)))
      (eOk := (by exact_kern (a.twF.eOk :)))
      (iCq := (by exact_kern (a.twF.iCq :)))
      (S0x := (by exact_kern (a.twF.S0x :))))
    (tw := @_root_.Formalism.L2.NTwTied.mk (_) (_)
      (pl_emb := (by exact_kern (a.tw.pl_emb :)))
      (ringSpec_baseIntegersEquiv_algebraMap := (by exact_kern (a.tw.ringSpec_baseIntegersEquiv_algebraMap :)))
      (ringSpec_baseEmbedding_compatible := (by exact_kern (a.tw.ringSpec_baseEmbedding_compatible :)))
      (eO_alg := (by exact_kern (a.tw.eO_alg :)))
      (eOk_alg := (by exact_kern (a.tw.eOk_alg :)))
      (mu_g := (by exact_kern (a.tw.mu_g :)))
      (hk_split := (by exact_kern (a.tw.hk_split :)))
      (ringSpec_excludedPlaces_eq := (by exact_kern (a.tw.ringSpec_excludedPlaces_eq :)))
      (concreteTwistFrame_extraExcludedPlaces_conj := (by exact_kern (a.tw.concreteTwistFrame_extraExcludedPlaces_conj :)))
      (B_range := (by exact_kern (a.tw.B_range :)))
      (sig_inj := (by exact_kern (a.tw.sig_inj :)))
      (qs_pos := (by exact_kern (a.tw.qs_pos :)))
      (S0x_contains_ccK_places := (by exact_kern (a.tw.S0x_contains_ccK_places :)))
      (S0x_contains_q0_places := (by exact_kern (a.tw.S0x_contains_q0_places :)))
      (S0x_contains_two_places := (by exact_kern (a.tw.S0x_contains_two_places :)))
      (S0x_contains_ramified_places := (by exact_kern (a.tw.S0x_contains_ramified_places :))))
    (nct := @_root_.Formalism.BasicNotions.NChTie.mk (_) (_)
      (twOf_eq := (by exact_kern (a.nct.twOf_eq :)))
      (twSide_eq := (by exact_kern (a.nct.twSide_eq :)))
      (Q_eq := (by exact_kern (a.nct.Q_eq :)))
      (psi_eq := (by exact_kern (a.nct.psi_eq :)))
      (embedding_baseField_condition := (by exact_kern (a.nct.embedding_baseField_condition :))))
    (exp := @_root_.Formalism.L2.NExpTied.mk (_)
      (U_eq := (by exact_kern (a.exp.U_eq :)))
      (psiU_gen := (by exact_kern (a.exp.psiU_gen :)))
      (psiU_side := (by exact_kern (a.exp.psiU_side :)))
      (psiU_xi := (by exact_kern (a.exp.psiU_xi :)))
      (delU_cont := (by exact_kern (a.exp.delU_cont :)))
      (delU_ine := (by exact_kern (a.exp.delU_ine :)))
      (thU_empty := (by exact_kern (a.exp.thU_empty :)))
      (sgnT := (by exact_kern (a.exp.sgnT :)))
      (sgnT_one := (by exact_kern (a.exp.sgnT_one :)))
      (Wt := (by exact_kern (a.exp.Wt :)))
      (acgWt := (by exact_kern (a.exp.acgWt :)))
      (modWt := (by exact_kern (a.exp.modWt :)))
      (fdWt := (by exact_kern (a.exp.fdWt :)))
      (rhoW := (by exact_kern (a.exp.rhoW :)))
      (rhoW_irr := (by exact_kern (a.exp.rhoW_irr :)))
      (rhoW_alg := (by exact_kern (a.exp.rhoW_alg :)))
      (tauG := (by exact_kern (a.exp.tauG :)))
      (sgnG := (by exact_kern (a.exp.sgnG :)))
      (sgnG_one := (by exact_kern (a.exp.sgnG_one :)))
      (tau_galois_first_character := (by exact_kern (a.exp.tau_galois_first_character :)))
      (mtV := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => @fun x6 => @fun x7 => @fun x8 => @fun x9 => @_root_.Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).W : _)))
        (acg := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).acg : _)))
        (mod := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).mod : _)))
        (fd := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).fd : _)))
        (ρ := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).ρ : _)))
        (irr := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).irr : _)))
        (alg := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).alg : _)))
        (bc := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).bc : _)))
        (J := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J : _)))
        (χ := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).χ : _)))
        (J_open := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_open : _)))
        (hyp := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).hyp : _)))
        (QP := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP : _)))
        (QP_sub := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_sub : _)))
        (QP_cover := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_cover : _)))
        (QP_nconj := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).QP_nconj : _)))
        (DP := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP : _)))
        (DP_sub := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_sub : _)))
        (DP_cover := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_cover : _)))
        (DP_nconj := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).DP_nconj : _)))
        (sp := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp : _)))
        (sp_w := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).sp_w : _)))
        (redG := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).redG : _)))
        (J_mem := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).J_mem : _)))
        (chi_eq := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).chi_eq : _)))
        (real := (by exact_kern ((@_root_.Formalism.L2.NExpTied.mtV (_) a.exp ((x1)) ((x2)) ((x3)) ((x4)) ((x5)) ((x6)) ((x7)) ((x8)) ((x9))).real : _))))
      (rhoW_hw := (by exact_kern (a.exp.rhoW_hw :)))
      (rhoW_wt := (by exact_kern (a.exp.rhoW_wt :))))
    (choice := @_root_.GlobalTheory.HeightCounting.ChoiceC.mk (_) (_)
      (twI_conj := (by exact_kern (a.choice.twI_conj :)))
      (sd_place := (by exact_kern (a.choice.sd_place :)))
      (emb_side := (by exact_kern (a.choice.emb_side :)))
      (sd_conj := (by exact_kern (a.choice.sd_conj :)))
      (one := (by exact_kern (a.choice.one :)))
      (conj := (by exact_kern (a.choice.conj :))))
    (eMt_level := (by exact_kern (a.eMt_level :)))
    (cf := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by exact_kern (a.cf.P :)))
      (W := (by exact_kern (a.cf.W :)))
      (mu0 := (by exact_kern (a.cf.mu0 :)))
      (eta := (by exact_kern (a.cf.eta :)))
      (chiPsi := (by exact_kern (a.cf.chiPsi :)))
      (del := (by exact_kern (a.cf.del :)))
      (del' := (by exact_kern (a.cf.del' :)))
      (isMu0 := (by exact_kern (a.cf.isMu0 :)))
      (isEta := (by exact_kern (a.cf.isEta :)))
      (isChi := (by exact_kern (a.cf.isChi :)))
      (isDel := (by exact_kern (a.cf.isDel :)))
      (isDel' := (by exact_kern (a.cf.isDel' :))))
    (tp := @_root_.Formalism.L2.Host.TupTied.mk (_) (_) (_)
      (xi := (by exact_kern (a.tp.xi :)))
      (xi_inj := (by exact_kern (a.tp.xi_inj :)))
      (xi_fin := (by exact_kern (a.tp.xi_fin :)))
      (xi_triv := (by exact_kern (a.tp.xi_triv :)))
      (xi_tame := (by exact_kern (a.tp.xi_tame :)))
      (psi := (by exact_kern (a.tp.psi :)))
      (trueColumnChoices_heckeChar_reference_eq_one := (by exact_kern (a.tp.trueColumnChoices_heckeChar_reference_eq_one :)))
      (xi_star := (by exact_kern (a.tp.xi_star :)))
      (xi_star' := (by exact_kern (a.tp.xi_star' :)))
      (xi_tw := (by exact_kern (a.tp.xi_tw :)))
      (psi_is := (by exact_kern (a.tp.psi_is :)))
      (psi_un := (by exact_kern (a.tp.psi_un :))))
    (tupLink := (by exact_kern (a.tupLink :)))
    (eta_eq := (by exact_kern (a.eta_eq :)))
    (ringSpec_normalisedCharacter_eq := (by exact_kern (a.ringSpec_normalisedCharacter_eq :)))
    (del_eq := (by exact_kern (a.del_eq :)))
    (psi_eq := (by exact_kern (a.psi_eq :)))
    (plB := (by exact_kern (a.plB :)))
    (plκ := (by exact_kern (a.plκ :)))
    (plB_loc := (by exact_kern (a.plB_loc :)))
    (plB_iota := (by exact_kern (a.plB_iota :)))
    (etaT_link := (by exact_kern (a.etaT_link :)))
    (muC_link := (by exact_kern (a.muC_link :)))
    (iCq_embO := (by exact_kern (a.iCq_embO :)))
    (embO_star := (by exact_kern (a.embO_star :)))
end UpperTheory.One.M
end
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll =====
