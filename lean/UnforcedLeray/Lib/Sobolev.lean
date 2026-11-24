import UnforcedLeray.Lib.Sobolev.TestDomain
import UnforcedLeray.Lib.Sobolev.Cylinder
import UnforcedLeray.Lib.Sobolev.WeakDeriv
import UnforcedLeray.Lib.Sobolev.Pairing
import UnforcedLeray.Lib.Sobolev.Space
import UnforcedLeray.Lib.Sobolev.Complexify
import UnforcedLeray.Lib.Sobolev.Bridge
import UnforcedLeray.Lib.Sobolev.NUEBridge
import UnforcedLeray.Lib.Sobolev.SmoothCoeff
import UnforcedLeray.Lib.Sobolev.Axis
import UnforcedLeray.Lib.Sobolev.Jacobian
import UnforcedLeray.Lib.Sobolev.ChainRule
import UnforcedLeray.Lib.Sobolev.HigherChain
import UnforcedLeray.Lib.Sobolev.CompDiffeo

/-!
# Sobolev spaces `Sob.W` (Wave 1, block 1D part 1: INF11 targets S0–S3, S6)


§5.0–§5.1; decisions D1, D3 and D11 of the scoping README §3.

| Target | Module | Main declarations |
|---|---|---|
| S0 | `TestDomain`, `Cylinder` | `Sob.TestDomain`, `iterDirDeriv`, `iterDirDeriv_perm`, `wholeSpace`, `cylinder` |
| S1 | `WeakDeriv`, `SmoothCoeff`, `Axis` | `HasWeakDeriv`, `.ae_unique`, `.cons`, `.append`, `.of_append`, `.perm`, `.smul_left`, `hasWeakSpatialDerivative_iff`, `HasWeakDeriv.of_bdd_off_axis` |
| S2 | `Pairing`, `Space`, `Complexify` | `Weight`, `wμ`, `testPair`, `SobSub`, `W`, `mem_SobSub_iff`, `W.value`, `W.value_injective`, `W.ofFields`, `W.restrict`, `W.partialDeriv`, `W.complexify`, `W.conj`, `W.realPart`, `W.imagPart` |
| S3 | `Bridge`, `NUEBridge` | `h1Equiv`, `h2Equiv`, `nue_hasWeakDerivOn_iff` |
| S6 | `Jacobian`, `ChainRule`, `HigherChain`, `CompDiffeo` | `hasWeakDeriv_comp_symm`, `hasWeakDeriv_comp_symm_word`, `W.compDiffeo`, `W.value_compDiffeo`, `W.deriv_compDiffeo` |

Not built here: S15 (one-dimensional `H¹(ℝ) ⊂ C₀` with `‖f‖²_∞ ≤ ‖f‖₂‖f'‖₂`, point traces);
see the status report of this wave.
-/
