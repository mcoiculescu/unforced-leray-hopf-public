import UnforcedLeray.Lib.PlanarSectorsB.Coupling
import UnforcedLeray.Lib.PlanarSectorsB.Sector
import UnforcedLeray.Lib.PlanarSectorsB.Transfer
import UnforcedLeray.Lib.PlanarSectorsB.SectorSum
import UnforcedLeray.Lib.PlanarSectorsB.EulerGroup
import UnforcedLeray.Lib.PlanarSectorsB.BiotSavartSector
import UnforcedLeray.Lib.PlanarSectorsB.LaterIdentities
import UnforcedLeray.Lib.PlanarSectorsB.Dilation
import UnforcedLeray.Lib.PlanarSectorsB.DilationPlane
import UnforcedLeray.Lib.PlanarSectorsB.TransportDuhamel
import UnforcedLeray.Lib.PlanarSectorsB.TransportFormula
import UnforcedLeray.Lib.PlanarSectorsB.LaterIdentitiesB
import UnforcedLeray.Lib.PlanarSectorsB.StressMoments

/-!
# Planar Gaussian-vortex infrastructure, block 2H part 1 (INF12 P6, P7, P8, P10; INF10 G-1)


§5, Levels P and G; plan `scoping/README.md` §5, Wave 2, block 2H (PLAN1), finished in Wave 3
(target 2H-fin); decision D7 (G1/G2 at `j = 0`, sector by sector, bounded generators) and
bypasses B1, B2 of the note. Builds on the
Wave 1 drafts `Lib/PlanarSectors` (P1–P5, P9), `Lib/PlanarSpectral` (S3, S4), `Lib/Semigroups`
(T0.1, T0.2, T7.1) and the unit drafts `Units/B0011`, `B0012`, `B0079`.

| Target | Module | Main declarations | Manuscript |
|---|---|---|---|
| P6 | `Coupling`, `Sector` | `ProfL2`, `crepLp`, `greenN_eq_inner`, `norm_greenN_le_wrep`, `couplingSec`, `coeFn_couplingSec`, `norm_couplingSec_le`, `couplingSec_zero`, `couplingSec_neg`, `isCompactOperator_couplingSec`, `tendsto_norm_couplingSec`, `omegaP`, `transportSec`, `adjoint_transportSec`, `Lsec`, `coeFn_Lsec`, `Lsec_zero`, `lsecBound`, `norm_exp_Lsec_le` | tex 662–670 (B0009), 1206–1222 (B0059–B0061 at `j = 0`), 1356 (B0078), 1366–1379 (B0079) |
| P7 | `SectorSum`, `EulerGroup` | `secProf`, `secEmb`, `eq_of_secProf`, `orthogonalFamily_secEmb`, `sectorSum`, `secProf_sectorSum`, `massCLM_secEmb`, `massCLM_eq_secEmb_zero`; `expSec`, `norm_expSec_le`, `expSec_eq_duhamel`, `eulerGroupW`, `eulerGroupW_add`, `continuous_eulerGroupW_apply`, `massCLM_eulerGroupW`, `eulerSemigroup`, `eulerSemigroup_add`, `eulerSemigroup_zero`, `norm_eulerSemigroup_le`, `continuous_eulerSemigroup_apply`, `secProf_eulerSemigroup`, `eulerExpSemigroup` | tex 653–670, 1228–1245 (B0062–B0064 at `j = 0`), 1561–1567 (B0101) |
| P7 (dilation) | `Dilation`, `DilationPlane` | `dilP`, `coeFn_dilP`, `norm_dilP_le_of_one_le`, `norm_dilP_inv_le_of_one_le`, `dilP_comp`, `dilUnit`, `greenN_comp_mul`, `frozenK_eq`, `frozenVelocity_eq`, `LsecDil`, `coeFn_LsecDil`, `dilation_conj_sec`, `LsecDil_one`, `exp_LsecDil`, `norm_exp_LsecDil_le_uniform`; `dilW`, `coeFn_dilW`, `norm_dilW_le_of_one_le`, `norm_dilW_inv_le_of_one_le`, `massCLM_dilW`, `sectorProjW_dilW`, `secProf_dilW`, `dilW_comp_inv`, `eulerGroupDil`, `dilation_conj`, `dilX0`, `eulerSemigroupDil`, `dilation_conj_X0`, `norm_dilX0_conj_le`, `norm_eulerSemigroupDil_le_uniform`, `LsecDil_eigen` | tex 1569–1580 (B0102, `eq:st18-t00074`) |
| P7 (mild form) | `TransportDuhamel`, `TransportFormula` | `transportExpSec`, `norm_transportExpSec_le`, `transportGroupW`, `transportGroupW_add`, `continuous_transportGroupW_apply`, `couplingW`, `eulerGroupW_eq_duhamel`, `eulerSemigroup_eq_duhamel`; `exp_smul_omegaP_apply`, `coeFn_transportExpSec`, `coeFn_transportGroupW_secEmb` | tex 1228–1245 (B0062–B0064) |
| P8 (partial) | `BiotSavartSector` | `fderiv_sector_rot`, `ofProfile_rot`, `velocity_dot_gradE0_sector` | tex 662–670, 1356 |
| P10 (partial) | `LaterIdentities`, `LaterIdentitiesB`, `StressMoments` | `quadrupole_ofProfile_two`, `integral_sin_sq_mul_exp_two` (B0364(d)); `quadrupolePoly_annihilated` (B0372); `integral_outer_variables` (B0400); `rE0'_eq`, `unitSource_eq` (B0638); `harmonic_separation` (B0856); `integral_radial_source_eq_zero`, `integral_rE0'_add_two_E0`, `integral_plane_rE0'_add_two_E0` (B0857); `cartSheet`, `integratedSheet`, `integratedSheet_eq_diagonal`, `Tz_sub_Th`, `integral_sheet_subst` (B0832); `angularTwo_farField` (B0232 core); `fderiv_ofProfile_two_one`, `fderiv_ofProfile_two_I`, `integral_v2u2`, `integral_v1u1`, `integral_v1u2_add_v2u1`, `stressEq_eq_I_mul_stressC`, `stressEη_eq_neg_stressEq`, `stressDefects_eq_zero` (B0388, plane part) | tex 3978–3987, 6788–6801, 6955–6962, 7004–7005, 6868, 7109–7118, 12268–12286, 12572–12582, 12737–12756 |
| G-1 | `Transfer` | `greenN_exp`, `greenN_exp_eq_neg_freeResolvent`, `Wlog_mul_J`, `transferFun`, `transfer`, `memLp_transferFun`, `freeResolvent_eigen`, `phaseSpeedOp_transfer`, `eq_zero_of_transfer_eq_zero`, `transfer_sector_eigen` | tex 1281–1306 (B0069–B0071), 1380–1388 (B0081(a), B0082) |

**Main statements.**
* `couplingSec hM n w = i n k(r) · greenN |n| w r` (a.e.), `‖couplingSec hM n‖ ≤ B_M` uniformly
  in `n`, compact, `→ 0` as `n → ∞`, `= 0` at `n = 0`.
* `Lsec hM n = -inΩ + couplingSec hM n`, `‖exp(t Lsec n)‖ ≤ e^{|t|B_M}` for all `t`, `n`.
* `eulerSemigroup hM t = ⊕ₙ exp(t Lsec n)` on `𝒳_{0,M}`: a strongly continuous group with
  `‖e^{t𝓛}‖ ≤ e^{|t|B_M}`, sector profiles `exp(t Lsec n) f_n`, and mass conservation on `L²_M`.
* B0102: with `J_af(y) = a⁻²f(y/√a)` (`dilW`, `dilP`) and the frozen generator `𝓛_a` defined
  sector by sector by the formula of `-V_a·∇ - (K·)·∇E_a` (`LsecDil`):
  `𝓛_{a,n} = a⁻²J_a𝓛ₙJ_a⁻¹` (`dilation_conj_sec`), `e^{t𝓛_a} = J_a e^{(t/a²)𝓛} J_a⁻¹` on `L²_M`
  and on `𝒳_{0,M}` (`dilation_conj`, `dilation_conj_X0`), `‖J_a‖ ≤ a^{(M-3)/2}`,
  `‖J_a⁻¹‖ ≤ a^{3/2}` for `a ≥ 1`, hence uniform transferred bounds for `a ∈ [1,A]`
  (`norm_dilX0_conj_le`).
* Mild form: `e^{t𝓛}f = T(t)f + ∫₀ᵗ T(t-τ)A_E e^{τ𝓛}f dτ` in `L²_M` (`eulerGroupW_eq_duhamel`),
  where `T(t)` acts on `w(r)e^{inϑ}` as the rotation by `-Ω(r)t` (`coeFn_transportGroupW_secEmb`).
* B0832: the integrated Cartesian sheet tensor is `diag(T_h, T_h, T_z)`, `T_z - T_h = (π/2)I_T`;
  B0388: `E_q = iC`, `E_η = -E_q` for the plane radial vortex and an angular-two stream.
* G-1: for `m ≠ 0`, `Lsec hM m w = z • w`, `Re z ≠ 0`, `c m = iz`: `Im c ≠ 0`,
  `phaseSpeedOp |m| (transfer w) = c • transfer w` and `w ≠ 0 → transfer w ≠ 0`.

**Not built here** (scoping-note items of this block that remain open):
* P7: `𝒫_a = J_a𝒫J_a⁻¹` and the norm continuity of `a ↦ 𝒫_a` (B0102, last sentences), since
  the spectral projection `𝒫` (target G-4) is not yet defined; the conjugacy of the evolutions,
  the generator conjugacy on each sector and the uniform bounds are built.
* P8: the identification of the Biot–Savart convolution `Kf` with `∇^⊥Σ_{n≠0}(greenN |n| f_n)e^{inϑ}`
  for `f ∈ L¹ ∩ L²_M` (so `couplingW` is `-(K·)·∇E₀` by its sector formula, not yet by the
  convolution).
* P10: B0824 (curl of the isolated affine source; its force `F_{Y,isol}` is defined in later
  sections not yet in Lean), the heat scaling and remainder bounds of B0232 (only the angular
  identity is built), the convergence of the scaled defects in B0388 (the plane identities
  `E_q = iC`, `E_η = -E_q` are built), the receiver contraction of B0832, and the consequence
  `Q_∞D = 0` of B0372.

Status: a draft; every listed declaration compiles. Theorem A is not proved and the audit items

-/
