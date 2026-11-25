module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GoodPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PxIsCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FlagLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefIs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ValIntLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.SgnEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

theorem UpperTheory.V.Th.rigPtOf_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigPtOfAlt := by
  intro hG hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f n ka R hL hka A _ _ _ ρ hρ hψ r hr hirr haut hfree
  exact UpperTheory.V.Th.rigPtOf_core hG Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f n ka R hL hka (_root_.UpperTheory.V.Z.Win.IsAutCsdA ι) A ρ hρ hψ r hr hirr haut hfree
    fun x ρ0 hdeg hcont hrep harith haut0 hunr0 hflag hirr0 hfree0 hdist hpar =>
      hAd l L Ω R.s R.V R.hV hdeg c₁ hL n (by have := R.n23; omega) (by have := R.n23; omega) R.r R.v0 R.B₀ ι x ρ0
        (_root_.UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free ι x ρ0 R.n23 ⟨hcont, hrep, harith, haut0, hunr0, hflag⟩ hirr0 hfree0 hdist) hpar

theorem UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.LinkedRigAlt := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed
  have hP : _root_.UpperTheory.V.Af.Hypotheses' := hH.toClassicalTheorems
  have hN := hP.litN
  have hA : GlobalTheory.Published.GlobalArtinReciprocity := hN.aut.art
  have hC : Pa.CohP :=
    ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hLoc : W.LocCFTAll := W.locCFT hA hC
  have hB0 : W.ProModularRingExists := W.b0Ex (W.phiAll hC)
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hker : η.ker = Base.galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  have := hD.imag
  obtain ⟨κ, hκ⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := Pr.kaOf (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hP) Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, -⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  have := Pr.coefIs l c₁
  obtain ⟨R₂⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  exact ⟨_root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hL hk3,
    ka, hk2, _root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hL hk2⟩
