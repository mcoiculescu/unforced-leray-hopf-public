import UnforcedLeray.Lib.CZCore.Density
import UnforcedLeray.Lib.CZCore.WeakType
import UnforcedLeray.Lib.CZCore.Marcinkiewicz
import UnforcedLeray.Lib.CZCore.Norming
import UnforcedLeray.Lib.CZCore.L2Limit
import UnforcedLeray.Lib.CZCore.Gauge
import UnforcedLeray.Lib.CZCore.Dyadic
import UnforcedLeray.Lib.CZCore.Decomp
import UnforcedLeray.Lib.CZCore.CZWeak
import UnforcedLeray.Lib.CZCore.Extension
import UnforcedLeray.Lib.CZCore.LpBound

/-!
# Anisotropic Calderón–Zygmund core (Wave 1, block 1C part 2: INF01 L1 T6–T12 and T18)

Main file of the shared Calderón–Zygmund core of the Lean build plan

one anisotropic dyadic CZ theorem with integer weights, no maximal function, INF02 T0 gauge facts
in T8). Targets and proposed signatures: `scoping/INF01-CZ.md` §5 Level 1 and Level 3 (T18).
Namespace `UnforcedLeray.CZ`.

Manuscript use: the `L^q` boundedness of the Leray projection, `1 < q < ∞` (blueprint unit
B0414, `paper/main.tex` lines 7336–7344, Grafakos Cor. 5.2.8), through INF01 Level 2, and the
parabolic estimate eq:free-stress-11 (unit B0423, lines 7447–7477), through the parabolic
instance `a = (2,1,…,1)` in INF02. Nothing here proves those units: the concrete kernels, their
`L²` bounds and their off-support representations are later targets (INF01 T1–T4, T13; INF02
T5–T7).

| Target | Module | Main declarations |
|---|---|---|
| T6 | `WeakType` | `HasWeakType11`, `hasWeakType11_of_dense` |
| T7 | `Marcinkiewicz` | `marcConst`, `marcinkiewicz` |
| T8 (+ INF02 T0) | `Gauge`, `Dyadic` | `anisoNorm`, `homDim`, `anisoNorm_add_le`, `anisoNorm_dil`, `volume_anisoClosedBall`, `volume_anisoBall`, `lintegral_anisoNorm_rpow_neg_le`, `dyadicBox`, `dyIdx`, `mem_dyadicBox_iff`, `dyadicBox_subset_of_le`, `volume_dyadicBox`, `volume_dyadicBox_pred`, `anisoNorm_sub_dyCenter_le`, `volume_dyStar` |
| T9 | `Decomp` | `CZDecomp`, `exists_czDecomp` |
| T10 | `CZWeak` | `IsCZConvolution`, `czConst`, `lintegral_far_le`, `weak11_of_isCZConvolution` |
| T11 | `Norming`, `Density` | `eLpNorm_le_of_forall_test_pairing`, `eLpNorm_le_of_forall_test_pairing_of_memLp_two`, `exists_contDiff_eLpNorm_sub_le_two` |
| T12 | `LpBound`, `Extension` | `lp_bound`, `lp_bound_ennreal`, `extendOfBound`, `extendLp`, `extendLp_apply`, `extendLp_consistent` |
| T18 | `L2Limit` | `eLpNorm_le_of_tendsto_two` |

Deviations from the indicative signatures of `INF01-CZ.md` §5:

* `CZDecomp` has finitely many boxes (`Finset`), which the construction for continuous
  compactly supported `f` gives; the bad parts' properties hold for every index.
* `IsCZConvolution` asks the size bound only for `x ≠ 0` (weaker than the sketch, which at
  `x = 0` would force `K 0 = 0` through `0 ^ (-|a|) = 0`), and asks `K` measurable.
* `lp_bound` takes any Calderón–Zygmund transpose `T'` (kernel `K'`, constant `B'`), not only
  the reflected kernel `K (-x)`.
* `extendLp` takes `[Fact (1 ≤ p)]` (needed for the normed structure of `Lp`) and `1 < p`,
  `p ≠ ∞` as hypotheses.
-/
