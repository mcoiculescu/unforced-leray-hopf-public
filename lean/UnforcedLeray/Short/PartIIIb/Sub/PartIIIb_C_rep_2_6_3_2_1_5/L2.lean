import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.D

/-!
# `KdHasDerivAt` (`PartIII-b:C/rep/2/6/3/2/1/5/2`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200.

`Kd ν μ h = (1 - e^{-h}) G_μ` (`kd_eq_gker`), and `∂_h G_μ = L G_μ - (μ - 1/2) G_μ` for `h > 0`
(`gkerHasDerivH`).  The product rule with `∂_h (1 - e^{-h}) = e^{-h}` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem kdHasDerivAt : KdHasDerivAt := by
  intro ν μ hν h hh y z i j k
  have h1 : HasDerivAt (fun h' : ℝ => 1 - Real.exp (-h')) (Real.exp (-h)) h := by
    have := ((hasDerivAt_id h).neg.exp).const_sub (1 : ℝ)
    simpa using this
  have hf : HasDerivAt (fun h' : ℝ => ((1 - Real.exp (-h') : ℝ) : ℂ))
      ((Real.exp (-h) : ℝ) : ℂ) h := h1.ofReal_comp
  have hg := gkerHasDerivH ν (μ : ℂ) hν h hh y z i j k
  have hprod := hf.mul hg
  have hfun : (fun h' => Kd ν μ h' y z i j k) =
      fun h' => ((1 - Real.exp (-h') : ℝ) : ℂ) * Gker ν (μ : ℂ) h' y z i j k :=
    funext fun h' => kd_eq_gker ν μ h' y z i j k
  rw [hfun]
  exact hprod

end UnforcedLeray.Short.PartIIIb.Concrete
