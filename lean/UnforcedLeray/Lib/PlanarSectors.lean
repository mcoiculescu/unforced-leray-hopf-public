import UnforcedLeray.Lib.PlanarSectors.Weighted
import UnforcedLeray.Lib.PlanarSectors.Profile
import UnforcedLeray.Lib.PlanarSectors.GreenUnique
import UnforcedLeray.Lib.PlanarSectors.Green
import UnforcedLeray.Lib.PlanarSectors.XG
import UnforcedLeray.Lib.PlanarSectors.AngularTwo
import UnforcedLeray.Lib.PlanarSectors.NUE.PolarAngularAverage

/-!
# Planar Gaussian-vortex infrastructure, block 1H part 1 (INF12 targets P1–P5, P9)


§5, Level P; plan `scoping/README.md` §5, Wave 1, block 1H (PLAN0). Decisions D7 (G1/G2 at
`j = 0`, sector by sector, bounded generators) and bypass B1 of the note.

Manuscript (`paper/main.tex`): the weighted spaces `H^0_M`, `𝒳_{0,M}` (lines 653–660,
`eq:st18-t00003`, blueprint unit `B0008`); `X_G`, `L₀`, `R` (lines 672–689, `eq:st18-t00005`–
`t00007`, units `B0010`, `B0011`, `B0012`); the Green formula on `L²_M` (lines 1366–1379,
`eq:st18-t00060`, unit `B0079`); the Green bound and compactness on `X_G` (lines 1417–1425,
`eq:st18-t00062`); Cartesian smoothness of angular-two functions (lines 698, 1864).

Modules (namespace `UnforcedLeray.Planar`):
* `Weighted` — **P1** `wMeasure`, `L2w`, `measurePreserving_rot_wMeasure`, `massCLM`, `X0`;
  **P2** `weightIso`, `sectorProjW`, `coeFn_sectorProjW`, `hasSum_sectorProjW`,
  `hasSum_norm_sq_sectorProjW`, `inner_sectorProjW_of_ne`, `inner_sectorProjW`,
  `sectorProjW_comp`, `sectorProjW_conj`.
* `Profile` — **P3** `profileMeasure`, `memLp_ofProfile_iff`, `ofProfileLin`,
  `range_ofProfileLin`, `sectorIso`, `coeFn_sectorIso_symm`, `coeFn_sectorIso`.
* `GreenUnique`, `Green` — **P4** `greenN`, `isRadialPoissonSol_greenN`,
  `tendsto_greenN_nhdsGT_zero`, `tendsto_greenN_atTop`, `eqOn_greenN_of_tendsto_mul`,
  `eqOn_greenN_of_tendsto`, `eqOn_greenN_of_bounded`, `norm_greenN_le_L2w`,
  `integral_greenN_mul_symm`, `tendsto_sq_mul_greenN_two`.
* `XG` — **P4** `norm_greenN_two_le_XG` (`eq:st18-t00062`); **P5** `L0`, `coeFn_L0`,
  `isCompactOperator_kR`, `L0_eq_mul_add_compact`, `isCompactOperator_L0_sub_mul`.
* `AngularTwo` — **P9** `contDiff_angularTwo`, `norm_iteratedFDeriv_angularTwo_le`.
* `NUE/*` — the NonUniqueEuler angular Fourier library I-ANG on `L²(ℂ)` (copied verbatim from
  `NonUniqueEuler/lean/NonUniqueEuler/{Statement/Plane, Defs/Infra/{Polar,AngularFourier},
  P/Infra/Polar/{Radial,Fubini,AngularAverage},
  P/Infra/AngularFourier/{Sector,SectorL2,Parseval,Symmetry},
  H/Infra/AngularFourier/Parseval/{Circle,Hilbert,PolarSum}}.lean`, namespace renamed to
  `UnforcedLeray.Planar.NUE`); it includes `NUE.Polar.ae_eq_angAvg_of_isRadial` (a radial
  function equals its angular average a.e.).

Nothing here proves Theorem A or any audit item; these are leaf infrastructure statements.
-/
