import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# PartII-b:G4/2/2/3 — `GreenRemSmooth` from smoothness of the two Green integrals

Source: the November 2 reference manuscript
lines 2349-2352.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem greenRemSmooth_of (hA : SmoothA) (hB : SmoothB) (hZ : PolyZpow) : GreenRemSmooth := by
  intro lam q hq
  have hA' := hA q hq.memXG hq.smooth
  have hB' := hB q hq.memXG hq.smooth
  have hz1 := (hZ (-2)).1
  have hz2 := (hZ 2).1
  have hfun : Set.EqOn (greenRem q)
      (fun r : ℝ => -(1 / 4 : ℂ) * ((r : ℂ) ^ (-2 : ℤ) * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) +
        (r : ℂ) ^ (2 : ℤ) * ∫ s in Ioi r, (s : ℂ)⁻¹ * q s) -
        (-(1 / 4 : ℂ) * Planar.quadrupole q) * (r : ℂ) ^ (-2 : ℤ)) (Ioi 0) := by
    intro r _
    have e1 : (r : ℂ) ^ (-2 : ℤ) = ((r : ℂ) ^ 2)⁻¹ := by simp [zpow_neg]
    have e2 : (r : ℂ) ^ (2 : ℤ) = (r : ℂ) ^ 2 := by norm_cast
    simp only [greenRem, Planar.greenInverse, e1, e2]
  exact ContDiffOn.congr
    ((contDiffOn_const.mul ((hz1.mul hA').add (hz2.mul hB'))).sub (contDiffOn_const.mul hz1)) hfun

end UnforcedLeray.Short.IIb
