import UnforcedLeray.Lib.PlanarSpectral.IndexLemma
import UnforcedLeray.Lib.PlanarSpectral.PhaseSpeed
import UnforcedLeray.Lib.PlanarSpectral.Laguerre
import UnforcedLeray.Lib.PlanarSpectral.LaguerreOscillator

/-!
# Planar spectral infrastructure (Wave 1, block 1H part 2: INF10 S3--S4 and H1--H2)

Main file of the INF10 replacement layer of the Lean build plan

`scoping/INF10-INF12-INF18-Planar.md` §5, Levels S and H; bypasses B2 and B6 of §4).
Manuscript: Gaussian chapter, `paper/main.tex` lines 802--958 (neutral Sturm operator),
1296--1349 (phase-speed operator, Lin--Zeng step), 1498--1518 (oscillator, adjoint pairing).
Namespaces: `UnforcedLeray.Sturm` (S3, S4; helpers in `UnforcedLeray.Sturm.PlanarIndex`) and
`UnforcedLeray.PlanarSpectral` (H1, H2).

| Target | Module | Main declarations | Units replaced or served |
|---|---|---|---|
| S3 | `IndexLemma` | `not_exists_two_dim_nonpositive`, `PlanarIndex.not_neutral_pair`, `PlanarIndex.eq_zero_of_nonpositive_of_trace_zero`, `PlanarIndex.inner_freeResolventOperator_self` | B0029 (tex 948), B0072--B0073 (tex 1308--1320); uses B0028 (tex 941--947) |
| S4 | `PhaseSpeed` | `aStar`, `omegaOp`, `JOp`, `phaseSpeedOp`, `phaseSpeedOp_eq`, `adjoint_phaseSpeedOp_comp`, `inner_B_eq_zero_of_eigen`, `eq_zero_of_phaseSpeed_eigen_of_three_le`, `phaseSpeed_two_eigenvector_unique`, `phaseSpeed_two_unique`, `phaseSpeed_two_no_jordan`, `bilinear_pairing_ne_zero` | B0074--B0077 (tex 1296--1349), B0096 (tex 1518) |
| H1 | `Laguerre` | `laguerreMeasure`, `LaguerreL2`, `xGToLaguerre`, `coeFn_xGToLaguerre`, `coeFn_xGToLaguerre_symm` | B0010 (tex 672--678) |
| H2 | `Laguerre`, `LaguerreOscillator` | `laguerreMono`, `xGToLaguerre_vmono`, `linearIndependent_laguerreMono`, `span_monomials_orthogonal_eq_bot`, `laguerreBasis`, `coe_laguerreBasis`, `xGLaguerreBasis`, `xGToLaguerre_oscBasis` | B0094 (tex 1503--1515), via the compiled draft `Units/B0094` |

Status: every target listed above compiles; this is a draft, not audited. Theorem A is not

-/
