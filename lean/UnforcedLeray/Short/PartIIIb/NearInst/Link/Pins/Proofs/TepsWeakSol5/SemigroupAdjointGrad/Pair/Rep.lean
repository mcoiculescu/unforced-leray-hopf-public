import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair.Good

/-!
# Leaf R: the a.e. representative formula `repX (S_ε(t) F) = e^{t/2} ∫ G_a(w) repX F (· - t, e^{t/2}· - w)`
(`AdjPairRep`)

Source `the November 2 reference manuscript`
1339-1362, 3346-3352.

Proof: `B0223.S_formula` gives the a.e. formula on `PSpace P = ℝ³ × AddCircle P`; the map
`rgQmap P (τ, y) = (y, τ mod P)` is quasi-measure preserving (`rgQmap_qmp`), so the formula pulls
back a.e. to `ℝ × ℝ³`.  Pointwise, `heatConv (ιx P)` unfolds to `∫ G_a(w) • u((e^{t/2}y, τ) - (w, 0))`
and `AddCircle.coe_sub` identifies `u(e^{t/2}y - w, τ - t)` with
`repX P F (τ - t, e^{t/2}y - w)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0223 (SpaceC X outerS PSpace)

theorem adjPairRep : AdjPairRep := by
  intro ν ε hν hε P _ t ht F
  have hS := UnforcedLeray.B0223.S_formula (E := SpaceC) (P := P) hν hε ht F
  filter_upwards [(rgQmap_qmp P).ae hS] with x hx
  change ((outerS (E := SpaceC) (P := P) hν ε).T t F : UnforcedLeray.B0223.PSpace P → SpaceC) (rgQmap P x) = _ at hx ⊢
  rw [hx]
  unfold UnforcedLeray.Heat.heatConv
  congr 1
  congr 1
  funext w
  simp only [rgQmap, UnforcedLeray.B0223.ιx_apply, Prod.mk_sub_mk, sub_zero]
  congr 1

end UnforcedLeray.Short.PartIIIb.NearInst
