import UnforcedLeray.Lib.ConvIneq.YoungGroup
import UnforcedLeray.Lib.ConvIneq.YoungInstances
import UnforcedLeray.Lib.ConvIneq.Peetre
import UnforcedLeray.Lib.ConvIneq.MinkowskiMixed
import UnforcedLeray.Lib.ConvIneq.MellinHardy
import UnforcedLeray.Lib.ConvIneq.RadialKernelNorm
import UnforcedLeray.Lib.ConvIneq.HolderExponents

/-!
# Convolution and integral inequalities (Wave 1, block 1B part 1: INF22 A1–A6)

Layer A of the scoping note

decisions D1–D17 of `scoping/README.md` §3 (Peetre once, D14). Namespace `UnforcedLeray.Conv`.

* **A1** `YoungGroup`, `YoungInstances`: Young's inequality on a measurable abelian group
  (`eLpNorm_convAbs_le_young`, `eLpNorm_convAbs_le_L1`, `convAbs_le_eLpNorm_top_mul`,
  `convAbs_le_eLpNorm_mul_eLpNorm`, Bochner and bilinear forms), with the instances `ℝ³`, `ℝ`,
  `ℂ`, `ℝ²` and `AddCircle c × ℝ` (bypass BP1). Units B0419, B0420, B0559, B0561, B0619, B0761,
  B0795, B0975, B0172, B0178, B0592, B0658.
* **A2** `Peetre`: Peetre's inequality (`one_add_sq_rpow_le`, `peetre`) and the weighted Young
  inequality (`eLpNorm_japanese_mul_convAbs_le`); units B0172, B0178.
* **A3** `MinkowskiMixed`: Minkowski for mixed `L^q_τ L^a_y` norms (`mixedNorm_lintegral_le`,
  `mixedNorm_integral_le`), phase-translation invariance (`mixedNorm_comp_add`) and the
  normalized phase measure (`mixedNorm_volume_eq`); units B0558, B0759, B0740.
* **A4** `MellinHardy`: the Mellin–Minkowski lemma (`eLpNorm_mellin_le`, bypass BP2) and the
  Hardy family `hardy_age` / `volterra_age` (B0275), `hardy_beta` (B0611), `hardy_tail`
  (B0582).
* **A5** `RadialKernelNorm`: `gapMajorant` and its exact `L^b` norm (`eLpNorm_gapMajorant`),
  with the seven manuscript exponent pairs; units B0559, B0561, B0619, B0761, B0795, B0958,
  B0959, B0974, B0975.
* **A6** `HolderExponents`: `ENNReal.HolderTriple` instances for `(11/4, 22/3, 2)`,
  `(11/4, 2, 22/19)`, `(22/19, 22/3, 1)`, `(4, 4, 2)`, `(3, 2, 6/5)`, `(6/5, 6, 1)`;
  three-factor Hölder (`eLpNorm_mul_mul_le`, B1010); age Hölder with power weights
  (`eLpNorm_one_le_age_holder`, B0276).
-/
