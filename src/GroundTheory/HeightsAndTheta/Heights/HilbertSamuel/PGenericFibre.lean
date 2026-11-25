module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨hprime, hdim⟩ := ShiftDegreePolynomial.genericFibre hP
  refine ⟨hprime, ?_⟩
  simpa only [Fintype.card_unit] using hdim

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
