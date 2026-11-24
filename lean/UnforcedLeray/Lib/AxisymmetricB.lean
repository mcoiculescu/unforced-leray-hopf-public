import UnforcedLeray.Lib.AxisymmetricB.Lift
import UnforcedLeray.Lib.AxisymmetricB.DSS
import UnforcedLeray.Lib.AxisymmetricB.Jv
import UnforcedLeray.Lib.AxisymmetricB.Range
import UnforcedLeray.Lib.AxisymmetricB.Stream
import UnforcedLeray.Lib.AxisymmetricB.AxisRegularity
import UnforcedLeray.Lib.AxisymmetricB.Hessian
import UnforcedLeray.Lib.AxisymmetricB.Average
import UnforcedLeray.Lib.AxisymmetricB.Unitary
import UnforcedLeray.Lib.AxisymmetricB.Bridge
import UnforcedLeray.Lib.AxisymmetricB.BridgeRange
import UnforcedLeray.Lib.AxisymmetricB.StokesGauge
import UnforcedLeray.Lib.AxisymmetricB.FlatExtension

/-!
# Wave 2, block 2J AXI1: axisymmetric lift, streams, axis regularity, DSS
(INF23 targets AX04, AX06, AX07 and the rest of AX08)


block 2J AXI1; critic correction 3 of `scoping/critic.md` moves `Nv_dss`/`physical_dss` here)
and scoping note `scoping/INF13-INF23-Cylinder.md` (§5, Layer 3; bypasses BP5, BP6, BP8, BP10).
Built on Wave 1 `Lib/Axisymmetric` (AX01–AX03), `Lib/Cylinder` (CY01), `Lib/Sobolev/Axis`
(the axis cutoff) and `Lib/PhaseSpace/PointSingularity`. Namespace `UnforcedLeray.Axi`.

| Target | Module | Main declarations |
|---|---|---|
| AX04 | `Lift` | `ageμ`, `lintegral_ageμ`, `frameL`, `Nv`, `norm_Nv`, `enorm_Nv_rpow`, `lintegral_Nv_rpow`, `lintegral_Ms`, `eLpNorm_Ms` (`Ms_isometry`), `frameTensor`, `NT`, `frobenius_NT`, `lintegral_NT_sq` |
| AX04 | `Jv` | `cellRep`, `perExt`, `ae_ageμ_mem`, `phaseμ`, `lintegral_phaseμ`, `measurable_Nv`, `lintegral_phaseμ_Nv`, `eLpNorm_Nv`, `liftFun`, `eLpNorm_liftFun`, `Jv` (linear isometry), `coeFn_Jv` |
| AX04 | `Range` | `Nv_eq_liftMer`, `isAxisymmetricNoSwirl_Nv`, `isAxisymmetricNoSwirl_liftFun`, `liftFun_add_period`, `Jv_mem_axisymmetric` (inclusion `⊆` of `range_Jv`) |
| AX08 | `DSS` | `Nv_dss`, `Np`, `Np_dss`, `selfSim`, `selfSim_dss`, `physNv`, `physNp`, `physical_dss`, `physNv_eq` |
| AX06 | `Stream` | `streamProfile`, `streamLift`, `streamLift_apply`, `div_streamLift_eq_zero`, `isSolenoidal_streamLift`, `streamLift_mul`, `streamCutoff_eq`, `merChart`, `ringStream`, `ringStreamProfile`, `ringStreamLift_components`, `ringStreamProfile_cutoff`, `streamLift_datum` |
| AX07 | `AxisRegularity` | `hasWeakSpatialDerivative_of_offAxis`, `isSolenoidal_of_point_singularity`, `parityField`, `contDiff_of_parity`, `parityField_eq_liftMer` |
| AX07 | `Hessian` | `radialField`, `radialField_eq_liftMer`, `second_radialField`, `hessian_bound_axis`, `abs_dρ_le_of_tendsto` |
| AX04 | `Average` | `rotZ`, `reflY`, `fixesAxis_rotZ`, `fixesAxis_reflY`, `angμ`, `measurePreserving_rotPar`, `angAvg`, `ae_eq_angAvg`, `ae_map_comm`, `ae_aziC_eq_zero` (reflection), `avgR`, `avgZ`, `ae_eq_avgLift` |
| AX04 | `Unitary` | `isAxisymmetricNoSwirl_congr`, `Y2Axi` (submodule), `Jv_mem_Y2Axi`, `perRep`, `invLift`, `liftFun_invLift`, `mem_range_Jv` (inclusion `⊇`), `range_Jv`, `JvAxi`, `JvEquiv` (unitary onto `Y2Axi P`), `coe_JvEquiv` |
| AX04 | `Bridge` | `cplxV`, `cplxLp`, `phaseRep`, `measurePreserving_phaseRep`, `toY2` (`L²(phaseμ P; ℝ³) →ₗᵢ[ℝ] Yq P 2`), `toY2_ae`, `toY2_ae_Ioc`, `JvY2`, `JvY2_ae` |
| AX04 | `BridgeRange` | `reC`, `IsRealAxiY`, `realPart`, `realPart_mem_Y2Axi`, `toY2_realPart`, `range_JvY2` (`range J_v` in `Yq P 2`) |
| AX06 | `StokesGauge` | `hasDerivAt_integral_Ioi`, `stokesGauge`, `IsStokesData`, `div_zero_of_divergence`, `dρ_stokesGauge`, `dz_stokesGauge`, `hasStrictFDerivAt_stokesGauge`, `streamLift_stokesGauge` (B0846), `abs_stokesGauge_le`, `abs_dρ_stokesGauge_le`, `abs_dz_stokesGauge_le` |
| AX07 | `FlatExtension` | `continuous_of_tendsto_axis`, `hasFDerivAt_zero_of_tendsto_axis`, `contDiff_of_tendsto_axis`, `extendByZeroOnAxis`, `contDiff_flat_extension` (B0195) |

Not built (missing): the primitive bounds `eq:affine-4-99d` of the Stokes gauge for derivative
orders `j ≥ 2` (outside the scoping signature of `stokesGauge`; `j = 0, 1` are
`abs_stokesGauge_le`, `abs_dρ_stokesGauge_le`, `abs_dz_stokesGauge_le`). Every target of the
block (AX04 `range_Jv` both inclusions and `JvEquiv`, the bridge to `Y₂`, AX06 `stokesGauge`,
AX07 `contDiff_flat_extension`) is built.

Deviations from the scoping signatures, each recorded in its module: `Nv` uses the frame map
`frameL` at the chart point instead of `liftMer` of a constant; `Jv` maps into the joint
`L²(phaseμ P)` (period average × Lebesgue) instead of `Y2 P` (the composite with the bridge
`toY2` is `JvY2 : H →ₗᵢ[ℝ] Yq P 2`); `range_Jv` and `JvEquiv` use the subspace `Y2Axi P` of the
joint space (slices 𝒪-invariant for a.e. `τ ∈ (0, P]`, the a.e. convention of
`Statement.IsAxisymmetricNoSwirl`), and `range_JvY2` reads the 𝒪-invariant subspace of the
complex `Y₂` as `IsRealAxiY` (slices are complexified real 𝒪-invariant fields); `stokesGauge` takes the field as a meridional profile `b`
with the hypotheses `IsStokesData a C b` on an exterior half-plane `{ρ > a}` (decay of `b` and
of its profile derivative, `eq:affine-4-99b` at `j = 0, 1`); `contDiff_flat_extension` takes
`k : ℕ` and the flatness bound only near the axis (`ϱ < 1`); `isSolenoidal_streamLift` assumes
compact support of the stream in `{ρ > 0}` (the annular core of BP5);
`hessian_bound_axis` bounds `ρ|∂²g|` instead of `|∂²g|` (the factor `ρ` is that of
`∂²(ρ g)`), with all hypotheses on the open half-plane.

Status: infrastructure. No unit is proved in full here, and Theorem A is not proved in Lean.
-/
