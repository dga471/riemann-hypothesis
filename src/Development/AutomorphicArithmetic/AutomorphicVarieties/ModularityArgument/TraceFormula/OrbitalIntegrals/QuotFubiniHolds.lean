module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper

@[expose] public section

namespace UpperTheory.V.Z.Tf.Orb

theorem orbProper_holds : OrbProper := UpperTheory.ConvolutionTheory.Loc.orbProper

alias gLTop_holds := _root_.UpperTheory.V.Z.Tf.Orb.gLTop

alias extCont_holds := _root_.UpperTheory.V.Z.Tf.Orb.extCont

alias centComm_holds := _root_.UpperTheory.V.Z.Tf.Orb.centComm

alias twCent_holds := _root_.UpperTheory.V.Z.Tf.Orb.twCent_of

alias haarComm_holds := _root_.UpperTheory.V.Z.Tf.Orb.haarComm

alias quotIndep_holds := _root_.UpperTheory.V.Z.Tf.Orb.quotIndep

alias normEx_holds := _root_.UpperTheory.V.Z.Tf.Orb.normEx

alias quotInt_holds := _root_.UpperTheory.V.Z.Tf.Orb.quotInt_of

alias untwist_holds := _root_.UpperTheory.V.Z.Tf.Orb.untwist

theorem twOrbLin_holds : TwOrbLin := twOrbLin_of orbProper_holds

theorem orbLin_holds : OrbLin := orbLin_of orbProper_holds

theorem twOrbComm_holds : TwOrbComm := twOrbComm_of orbProper_holds

theorem orbComm_holds : OrbComm := orbComm_of orbProper_holds

end UpperTheory.V.Z.Tf.Orb
