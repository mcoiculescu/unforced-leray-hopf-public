import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.StatementsCanonical

/-!
# Part I of the shorter proof: the planar train and Gaussian instability (statements)

Source of record: `the November 2 reference manuscript`, lines 241-1195
(modules `seed-train/train.tex` 241-552, `seed-train/lin-seed.tex` 556-958,
`seed-train/canonical.tex` 960-1177).  The statements are in

* `StatementsTrain.lean`: Lemma `sct:train` and Lemma `sct:heat` (lines 301-552), for the
  train of the Gallay-Slijepcevic (`BUC`) class `IsBUCTrain` (`TrainClass.lean`): existence of a
  member of the class for `c ≥ 1`, forward uniqueness (`s ≥ 0`) inside the class, and the ten
  estimates for every member;
* `StatementsSeed.lean`: Proposition `short-gaussian-seed` and Corollary `short-seed-dilation`
  (lines 592-953);
* `StatementsCanonical.lean`: Lemmas `short-compact-duhamel`, `short-diffusion-complement`,
  Proposition `short-canonical`, Corollary `short-mellin` (lines 978-1174).

`PartIResults` bundles the numbered results of the scope; `Compose.lean` proves it from the leaf
statements that are not already derived there.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- The numbered results of Part I (train, Gaussian seed, canonical branch). -/
structure PartIResults : Prop where
  trainExistence : TrainGlobalExistence
  trainUniqueness : TrainUniqueness
  trainComparison : TrainComparison
  trainOverlap : TrainOverlap
  trainL2Decay : TrainL2Decay
  trainStrainIntegral : TrainStrainIntegral
  trainFluctuationIntegral : TrainFluctuationIntegral
  trainMeanEquations : TrainMeanEquations
  trainFluctuationDecay : TrainFluctuationDecay
  trainMeanExpansion : TrainMeanExpansion
  trainTransverseTails : TrainTransverseTails
  trainFixedBand : TrainFixedBand
  seedXGExists : SeedXGExists
  seedModeRegularity : SeedModeRegularity
  seedXGSpectrum : SeedXGSpectrum
  seedFunctional : SeedFunctional
  seedStrainCoupling : SeedStrainCoupling
  seedEulerSpectrum : SeedEulerSpectrum
  seedEulerComplement : SeedEulerComplement
  seedXGComplement : SeedXGComplement
  seedOscillator : SeedOscillator
  seedDilationGenerator : SeedDilationGenerator
  seedDilationProjection : SeedDilationProjection
  smallDiffusionComplement : SmallDiffusionComplement
  canonicalBranch : CanonicalBranch
  canonicalMellin : CanonicalMellin

end UnforcedLeray.Short.PartI
