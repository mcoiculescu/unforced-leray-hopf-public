import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.Assembly
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.SliceProof

/-!
# Part II-b, task `PartII-b:F8/2`: `FlatKInteractionFromH2` (SP 2311-2314)

Source of record: `the November 2 reference manuscript` (SP), lines 2311-2314:
"Since `s‖v(s)‖_∞ + s‖Dv(s)‖_∞ ≤ 𝒫_ν` for `s ≥ 1`, these estimates bound `sB_vz` in `H_p`".

The proof combines (helpers in `FlatKFromH2/`):
* `Smooth2D`, `Strip`, `PlaneSobolev`: the periodic-strip Sobolev inequality
  `‖u‖_{L^{11/4}(C_c)} ≤ C (‖u‖_{L²} + ‖∂_qu‖_{L²} + ‖∂_ηu‖_{L²})` (Mathlib's
  Gagliardo-Nirenberg-Sobolev inequality applied to `|u|²`, Hölder, cutoff, mollification and
  Fatou), with `C` independent of `c ≥ 4`;
* `SliceProof`: periodicity of weak chart derivatives and slicing of the weak identities, giving
  `SliceSobolev` on almost every age slice;
* `Assembly`: the train amplitude bounds `FreeInteractionAux.trainVel_band_bound` (ages `(0, H]`)
  and `FreeInteractionAux.trainVel_tail_bound` (ages `≥ 1`), Tonelli on `H_p`, and the weights
  `s^{-9/8} s^{11/4} = s^{13/8}` on `(0, H]`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:F8/2`** (SP 2311-2314): the flat interaction `sB_vz = flatK p.train z zq zη` of an
`H²(C_c)`-valued profile is bounded in `H_p` by its weighted `L^p(H²)` norms. -/
theorem flatKInteractionFromH2_proof : UnforcedLeray.Short.IIb.FlatKInteractionFromH2 :=
  FlatKH2.flatKInteractionFromH2_of FlatKH2.sliceSobolev_proof

end UnforcedLeray.Short.IIb
