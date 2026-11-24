import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth.Periodic

/-!
# `PartIII-a:T21/c5/1/1/2/2`: joint smoothness of the periodized physical dual rows

Source `the November 2 reference manuscript`
lines 593-610 (`eq:short-seed-functional`) and 2891-2905 (the planar dual kernels and their
fixed derivatives decay like `|y|^{-2-j}`; the dual rows are periodized).

**Theorem** (`physFrameLam0Smooth`): for a Part I seed kernel `κ`, `ν > 0`, `t ≥ 0`, the map
`(r, x) ↦ perSum (ν^{-2}) (physAdj (clockA ν r) (κ.lamP j)) x` is `C^∞` on `Ici t ×ˢ univ`.

**Proof.**
1. `LamJetInf.good_lamP` (`PhysFrameLam0Smooth/LamJet.lean`, `Good.lean`): `κ.lamP j` is `C^∞`
   with `‖D^k λ_j(z)‖ (1+‖z‖)^{k+2} ≤ C_k` for all `k`; this is derived from `IsSeedKernels κ`
   through the explicit form `λ₀(z) = F(conj w)`, `F(u) = u² β(|u|²)` of `SeedJet.lean`, by
   induction on the regular equation for `b` and rescaling `F(u) = R^{-2}F_R(u/R)`.
2. `LamJetInf.contDiffOn_perPhys` (`Periodic.lean`): for every such `Good` kernel `L`, termwise
   differentiation on boxes gives `∂_v P_L = ν v₁ a⁻¹ P_{EL} + a^{-1/2} P_{∂_{v₂}L}` with
   `EL = L - ½ DL·z` again `Good`; induction on the order gives `C^∞` on `{1 + ν r > 0}`.
3. Restrict to `Ici t ×ˢ univ`, where `clockA ν r ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T21/c5/1/1/2/2`** (SP 593-610, 2891-2905): joint `C^∞` smoothness of the
unnormalised periodized physical dual rows. -/
theorem physFrameLam0Smooth (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PhysFrameLam0Smooth κ := by
  intro hκ ν t hν ht j
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν _).ne'
  have h : ContDiffOn ℝ ∞ (LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (κ.lamP j)) (LamJetInf.physU ν) :=
    LamJetInf.contDiffOn_perPhys hν hc (LamJetInf.good_lamP hκ j)
  refine h.mono fun p hp => ?_
  show 0 < clockA ν p.1
  have hp0 : 0 ≤ p.1 := ht.trans hp.1
  unfold clockA
  nlinarith

end UnforcedLeray.Short.IIIa
