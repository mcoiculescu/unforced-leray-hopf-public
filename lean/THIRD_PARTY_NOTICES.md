# Third-party code

`UnforcedLeray/Analysis/WeakL2.lean` and `WeakCompactness.lean` are adapted from
Matei P. Coiculescu's NonUniqueEuler repository, commit
`d81c3f456505f8a3e8211f2a9f63313d0599ed5a`, under Apache-2.0.
Original paths: `Defs/Infra/WeakL2.lean` (general Hilbert-space portion) and
`P/Infra/WeakL2/Compact.lean`. Changes: namespace and imports; planar definitions omitted.
The original license is preserved in `LICENSE-NonUniqueEuler`.

Mathlib is a pinned dependency under its own Apache-2.0 license.

`UnforcedLeray/TestFunctions.lean` adapts the general compact-test derivative
argument from `NonUniqueEuler/Defs/Infra/Sobolev.lean`, at the same pinned
commit and license above, to real scalar tests on three-dimensional space.

The sources listed in `NONUNIQUEEULER-SOURCES.json` under `NonUniqueEuler/`
are unmodified source copies from
the same pinned repository. They supply the one-dimensional Yukawa kernel,
weak derivatives, energy identities, and the general convolution Minkowski inequality. Their exact original paths and
SHA-256 digests are recorded in `NONUNIQUEEULER-SOURCES.json`. The original
copyright headers are preserved; `LICENSE-NonUniqueEuler` applies; the original repository NOTICE is preserved
in `NOTICE-NonUniqueEuler`.

The seven files under `NavierStokes/` are unmodified copies from OpenAI's
NavierStokesAndEuler repository, commit
`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, Apache-2.0. Their exact original
paths and SHA-256 digests are recorded in `BASELINE-SOURCES.json`; the license
is preserved in `LICENSE-NavierStokesAndEuler`. They supply the actual R³
smooth Sobolev inequality and its analytic prerequisites.

Files under `UnforcedLeray/Analysis/Heat/` that cite the baseline Gaussian
files in their headers adapt those OpenAI proofs at the same pinned commit,
with project-local namespaces and minimal imports. Their headers identify
the source paths and modifications. The baseline Apache-2.0 license applies.

`UnforcedLeray/Analysis/SobolevEmbedding/Smooth.lean` also adapts the elementary
coordinate-sum argument from baseline `NavierStokes/R3CutoffSobolev.lean:191`
(`operator_norm_sq_le`), at the same pinned baseline commit and Apache-2.0 license.

The heat adaptations also include baseline `Euler/LpTranslation.lean`,
`Euler/WholeSpaceGaussian.lean`, and `Euler/WholeSpaceGaussianTimeKernel.lean`.
Exact source references and changes are stated in the corresponding
`Heat/Translation.lean`, `Heat/Averaging.lean`, and `Heat/KernelEvolution.lean` headers.

The twelve-file generic ODE library from the same pinned NonUniqueEuler
repository is included in `NONUNIQUEEULER-SOURCES.json`. The original
NOTICE covers its adapted OpenAI GlobalPicard source.

`UnforcedLeray/Analysis/Pressure/Young.lean` adapts the public NonUniqueEuler
Young convolution argument to actual three-dimensional Lebesgue space;
its source header records the precise provenance. The same Apache-2.0
license and preserved original NOTICE apply.
