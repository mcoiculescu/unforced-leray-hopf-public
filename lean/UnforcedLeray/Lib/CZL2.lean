import UnforcedLeray.Lib.CZL2.NewtonConv
import UnforcedLeray.Lib.CZL2.HessianKernel
import UnforcedLeray.Lib.CZL2.Hormander
import UnforcedLeray.Lib.CZL2.Decay
import UnforcedLeray.Lib.CZL2.TestProjection
import UnforcedLeray.Lib.CZL2.RieszL2
import UnforcedLeray.Lib.CZL2.TestOffSupport
import UnforcedLeray.Lib.CZL2.L2OffSupport
import UnforcedLeray.Lib.CZL2.PressureIdentity

/-!
# INF01 level L0: the L² Newton operator and the Newton pressure identity (Block 1C, part 1)

Blueprint: INF01 targets T1–T5 of the scoping note

decisions D5 and D6 of `scoping/README.md` §3. Manuscript: `R_j = ∂_j(-Δ)^{-1/2}`,
`R_iR_k = ∂_i∂_k(-Δ)^{-1}`, `𝔓 = I + (R_iR_k)` and `p = Σ R_iR_k(u_iu_k)`
(`paper/main.tex` lines 107–111), and unit B1032 (lines 559–561), proved for the compiled
Newton pressure as D6 decides.

Nothing here uses a Fourier transform or a Calderón–Zygmund estimate.

* T1 (`HessianKernel`, `Hormander`): `newtonHessianKernel`, `newtonHessianKernel_eq`,
  `norm_newtonHessianKernel_le`, `exists_hasFDerivAt_newtonHessianKernel`,
  `abs_newtonHessianKernel_sub_le`, `hormander_newtonHessianKernel`.
* T2 (`NewtonConv`, `RieszL2`, `TestOffSupport`): `newtonConv`, `newtonConv_contDiff`,
  `laplacian_newtonConv`, `rieszPairTest`, `rieszPairTest_offSupport`, `rieszPairTest_decay`.
* T3 (`RieszL2`): `sum_sq_l2_rieszPairTest`, `integral_rieszPairTest_mul_symm`.
* T4 (`RieszL2`, `L2OffSupport`): `rieszPairL2`, `norm_rieszPairL2_le`, `rieszPairL2_toLp`,
  `rieszPairL2_offSupport`, `inner_rieszPairL2`, `lerayNewtonL2`,
  `lerayNewtonL2_eq_projection`.
* T5 (`PressureIdentity`): `newtonPressure_identity`, `velocityPressure_pressure_identity`,
  `velocityPressure_projected_identity`.

Status: these are drafts. They do not prove Theorem A or `UnforcedLeray.MainClaim`.
-/
