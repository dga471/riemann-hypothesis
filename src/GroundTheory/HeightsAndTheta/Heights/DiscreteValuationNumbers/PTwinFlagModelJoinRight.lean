module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar midDeg midVar FlagModel)

namespace FlagModelJoinRightAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem midDeg_pullDeg (a : K → ℤ) :
    midDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K₂ ⊕ K') a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midVar_comp_liftVar :
    midVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι₂ ι') :=
  rfl

end FlagModelJoinRightAlt


open FlagModelJoinRightAlt in
theorem FlagModelJoinRightAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinRight.Statement) (hNum : PairNumberJoinRight.Statement) :
    FlagModelJoinRightAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  unfold FlagModel.value
  rw [hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r)
    _ _ _ _ (FlagModelJoinLeftAlt.joinVert F hVert hv) _ (FlagModelJoinLeftAlt.homog_mul hc hG hQ)]
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, midDeg_pullDeg, midVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
