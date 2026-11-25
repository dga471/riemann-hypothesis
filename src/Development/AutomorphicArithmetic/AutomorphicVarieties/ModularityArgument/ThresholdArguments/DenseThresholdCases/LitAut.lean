module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

@[expose] public section




section
namespace GlobalTheory.Mem.LiteralAutomorphy
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published
structure LitLocAlt : Prop where
  bz : BernsteinZelevinskyFiniteness
  bern : BernsteinUnitaryProductIrreducible
  geo : GeometricLemma
  zel : ZelevinskyPolynomialRing
  disj : TotallyDisjointProductIrreducible
  gen : GenericUnlinkedGL
  exh : LanglandsExhaustionGL
  cos : StandardCosocleGL
  chev : ChevalleyUnits
structure LiteratureAutomorphyHypothesis : Prop where
  fin : AutomorphicFormsFiniteGL
  js : JacquetShalika
  bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN
  gk : GelfandKazhdanDual
  gal : _root_.UpperTheory.V.Z.Win.RowT
  coh : ClozelCohomological
  art : GlobalArtinReciprocity
  chA : HeckeLAdicCharacterAbove
  chW : AlgebraicCharacterWD
  berger : DeRhamPotSemistable
structure LiteratureRankNHypothesis : Prop where
  loc : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt
  aut : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis
  coh : LitCoh
end GlobalTheory.Mem.LiteralAutomorphy
end
