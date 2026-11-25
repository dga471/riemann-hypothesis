module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

def weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 0 1 (-1) 0

def leviM (A : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks A 0 0 A⁻¹ᵀ

def unipM (S : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 1 0 S 1

def IsSymp (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := G.transpose * weylM * G = weylM

def gens : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {G | ∃ A : Matrix κ κ F, IsUnit A.det ∧ G = leviM A} ∪ {G | ∃ S : Matrix κ κ F, S.transpose = S ∧ G = unipM S} ∪ {weylM}

variable [NumberField F]

def indO (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

end GlobalTheory.SympChange
