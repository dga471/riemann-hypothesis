module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace
open scoped Pointwise

namespace GlobalTheory.CompactRight

theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) : Measure.map (· * k) μ = μ := by
  first | exact _root_.GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup | exact @_root_.GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup | apply _root_.GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup <;> assumption

end GlobalTheory.CompactRight
