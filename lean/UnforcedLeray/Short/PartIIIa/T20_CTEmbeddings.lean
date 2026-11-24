import UnforcedLeray.Short.PartIIIa.Sub.T20
import UnforcedLeray.Short.PartIIIa.T20_1_QuadQBound
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique
import UnforcedLeray.Short.PartIIIa.T20_7_BiotSavartExistsUniform

/-!
# Part III-a, task `PartIII-a:T20`: `ctEmbeddings`

Source of record: `the November 2 reference manuscript`, lines 3230-3240
(`eq:ct-embeddings`).

Target: `UnforcedLeray.Short.IIIa.CTEmbeddings` (`CanonicalTransfer.lean`, unchanged).

Proof: assembly of the three leaf theorems through `CTE.ctEmbeddings_of`
(`Sub/T20.lean`):
* `CTE.quadQ_bound` (`T20_1_QuadQBound.lean`): the moment bound;
* `CTE.isBiotSavart_unique` (`T20_2_BiotSavartUnique.lean`): uniqueness of the Biot-Savart velocity;
* `CTE.biotSavart_exists_uniform` (`T20_7_BiotSavartExistsUniform.lean`): uniform existence.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T20`: `ctEmbeddings`.** -/
theorem ctEmbeddings : CTEmbeddings :=
  CTE.ctEmbeddings_of CTE.quadQ_bound CTE.isBiotSavart_unique CTE.biotSavart_exists_uniform

end UnforcedLeray.Short.IIIa

end
