module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.gluing_law_holds : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  first | exact @GlobalTheory.Chain.RealIt.GlueProof.glueLaw
