module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour


open Classical in
theorem factor_isAddHaar (F : Type) [Field F] [NumberField F] :
    ((Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _


open Classical in
instance measI_isAddHaar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (measI F κ).IsAddHaarMeasure := by
  haveI := factor_isAddHaar F
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

end GlobalTheory.WeylFour
