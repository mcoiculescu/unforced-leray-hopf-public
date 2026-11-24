import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeGenerator
import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.Left
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.Right

/-!
# Spine: time derivative of the free Gaussian part on `𝒟(D)` (task `Spine:SP-CAN/4/2/1`)

Partial work toward `mildDomainDerivative : MildDomainDerivative`. This file proves the free-part
derivative lemma only. The Duhamel integral part (variable upper limit, `D` passed through the


Source: `the November 2 reference manuscript` line 1086 and lines 1134-1145.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010

/-- Time derivative of the Gaussian semigroup on `𝒟(D)` (local copy of the private
`Cons.G3b.hasDerivAt_expD_apply_domain`, `Cons/L2/CanonicalBranch/CanonicalComplementMild.lean:18`). -/
theorem hasDerivAt_expD_domain {a : ℝ} (ha : 0 < a) (z : B0094.D.domain) :
    HasDerivAt (fun u : ℝ => B0123.expD u (z : XG)) (B0123.expD a (B0094.D z)) a := by
  have hcont : Continuous (fun u : ℝ => B0123.expD u (B0094.D z)) :=
    UnforcedLeray.Cons.G3b.continuous_expD_apply _
  have hInt : IntervalIntegrable (fun u : ℝ => B0123.expD u (B0094.D z)) volume 0 a :=
    hcont.continuousOn.intervalIntegrable_of_Icc ha.le
  have hderInt := intervalIntegral.integral_hasDerivAt_right hInt
    (hcont.stronglyMeasurableAtFilter volume (nhds a)) hcont.continuousAt
  have hder := hderInt.const_add (z : XG)
  refine HasDerivAt.congr_of_eventuallyEq hder ?_
  filter_upwards [Ioi_mem_nhds ha] with u hu
  simpa using (UnforcedLeray.Cons.G3b.expD_integral_generator (le_of_lt hu) z)

/-- Free part of the Duhamel identity: `s ↦ e^{(log θ'' - log s) D} z` on `𝒟(D)` has derivative
`-θ⁻¹ e^{(log θ'' - log θ) D} (D z)` at `θ`, for `0 < θ < θ''`. -/
theorem hasDerivAt_freeLeft_domain {θ θ'' : ℝ} (hθ : 0 < θ) (hθθ : θ < θ'')
    (z : B0094.D.domain) :
    HasDerivAt (fun s : ℝ => B0123.expD (Real.log θ'' - Real.log s) (z : XG))
      ((0 - θ⁻¹) • B0123.expD (Real.log θ'' - Real.log θ) (B0094.D z)) θ := by
  have ha : 0 < Real.log θ'' - Real.log θ := by
    have := Real.log_lt_log hθ hθθ
    linarith
  have h1 := hasDerivAt_expD_domain ha z
  have hu : HasDerivAt (fun s : ℝ => Real.log θ'' - Real.log s) (0 - θ⁻¹) θ :=
    (hasDerivAt_const θ (Real.log θ'')).sub (Real.hasDerivAt_log hθ.ne')
  exact h1.scomp θ hu

/-- The two one-sided derivatives (`mdLeft`, `mdRight`) give `MildDomainDerivative`. -/
theorem mildDomainDerivative : UnforcedLeray.Short.Spine.MildDomainDerivative :=
  mildDomainDerivative_of mdLeft mdRight

end UnforcedLeray.Short.Spine
