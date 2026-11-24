import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerSmooth
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerVanish

/-!
# `PartII-b:T10/6/3/1/1`: the lift profile is nice

Target `liftNice_proof : UnforcedLeray.Short.IIb.ChartLift.LiftNice`.

Smoothness: at a point with `s < s₀` the profile vanishes on the open set `{s < s₀}` (leaf 1c),
so it is locally zero; at a point with `s > 0` the factor `s^{3/2}` is smooth (`Real.contDiffAt_rpow_const_of_ne`)
and `perCoord` is smooth (leaf 1a). Periodicity is leaf 1b; compact support is leaf 1c.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ChartLift

theorem liftNice_proof : UnforcedLeray.Short.IIb.ChartLift.LiftNice := by
  intro c ε φ i hc hε hφ
  obtain ⟨s₀, s₁, L, hs₀, hvan⟩ := perVanish_proof c φ hc hφ
  have hpc : ContDiff ℝ ∞ (perCoord c φ) := perSmooth_proof c φ hc hφ
  unfold NiceProf
  refine ⟨?_, ?_, ⟨s₀, s₁, L, hs₀, ?_⟩⟩
  · rw [contDiff_iff_contDiffAt]
    intro x0
    by_cases hx0 : x0.1 < s₀
    · have hopen : IsOpen {x : Coord | x.1 < s₀} := isOpen_lt continuous_fst continuous_const
      have hev : liftB c ε φ i =ᶠ[𝓝 x0] fun _ => (0 : CMerid) := by
        filter_upwards [hopen.mem_nhds hx0] with x hx
        have h0 : perCoord c φ x = 0 := hvan x (Or.inl hx)
        simp [liftB, h0]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hx0' : s₀ ≤ x0.1 := not_lt.mp hx0
      have hpos : 0 < x0.1 := lt_of_lt_of_le hs₀ hx0'
      have hr : ContDiffAt ℝ ∞ (fun x : Coord => x.1 ^ ((3 : ℝ) / 2)) x0 :=
        (Real.contDiffAt_rpow_const_of_ne hpos.ne').comp x0 contDiffAt_fst
      have hf : ContDiffAt ℝ ∞
          (fun x : Coord => (c * ε ^ 2 / Real.pi) * x.1 ^ ((3 : ℝ) / 2) * perCoord c φ x) x0 :=
        ((contDiffAt_const.mul hr)).mul hpc.contDiffAt
      have hC : ContDiffAt ℝ ∞
          (fun x : Coord => (((c * ε ^ 2 / Real.pi) * x.1 ^ ((3 : ℝ) / 2) * perCoord c φ x : ℝ) : ℂ))
          x0 :=
        Complex.ofRealCLM.contDiff.comp_contDiffAt x0 hf
      unfold liftB
      exact hC.smul contDiffAt_const
  · intro x
    have hp := perPeriodic_proof c φ x
    simp only [liftB]
    rw [hp]
    rfl
  · intro x hx
    have h0 : perCoord c φ x = 0 := hvan x hx
    simp [liftB, h0]

end UnforcedLeray.Short.IIb.ChartLift
