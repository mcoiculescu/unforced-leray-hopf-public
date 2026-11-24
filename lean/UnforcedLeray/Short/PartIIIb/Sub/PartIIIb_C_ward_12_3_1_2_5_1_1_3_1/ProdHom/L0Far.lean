import UnforcedLeray.Units.B0411.Operators
import UnforcedLeray.Lib.PhaseSpace.Ops

/-!
# Far-field derivative of `L₀E` (helper for `ProdHom`)

Source `the November 2 reference manuscript`
lines 2542-2549: on the open far set where the drift identity `(T₀ - ½)E = 0` holds, `L₀E = -νΔE`,
so `∂_j L₀E = -ν ∂_j ΔE` there (part (a) of the far product rule).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProdHom

/-- On an open set where the drift identity holds, `L₀E` agrees with `-ν ΔE` near each point. -/
theorem L0_eventuallyEq_neg_nuLapT (ν : ℝ) (E : ℝ × UnforcedLeray.Space → CVec3)
    (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U)
    (hdrift : ∀ x ∈ U, dτ E x - (1 / 2 : ℝ) • radialT E x - (1 / 2 : ℝ) • E x = 0)
    (x : ℝ × UnforcedLeray.Space) (hx : x ∈ U) :
    (UnforcedLeray.B0411.L0 ν E) =ᶠ[nhds x] (fun y => -(ν • lapT E y)) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := hdrift y hy
  have key : UnforcedLeray.B0411.L0 ν E y =
      (dτ E y - (1 / 2 : ℝ) • radialT E y - (1 / 2 : ℝ) • E y) - ν • lapT E y := by
    simp only [UnforcedLeray.B0411.L0, UnforcedLeray.B0411.T0]
    abel
  rw [key, h, zero_sub]

theorem dy_contDiff (j : Fin 3) (G : ℝ × UnforcedLeray.Space → CVec3) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (dy j G) := by
  unfold dy
  exact (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem lapT_contDiff (E : ℝ × UnforcedLeray.Space → CVec3) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (lapT E) := by
  unfold lapT
  exact ContDiff.sum fun j _ => dy_contDiff j _ (dy_contDiff j _ hE)

/-- `∂_j L₀E = -ν ∂_j ΔE` on the open set where the drift identity holds (source 2542-2549). -/
theorem dy_L0_far (ν : ℝ) (E : ℝ × UnforcedLeray.Space → CVec3)
    (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U) (hE : ContDiff ℝ ∞ E)
    (hdrift : ∀ x ∈ U, dτ E x - (1 / 2 : ℝ) • radialT E x - (1 / 2 : ℝ) • E x = 0)
    (j : Fin 3) (x : ℝ × UnforcedLeray.Space) (hx : x ∈ U) :
    dy j (UnforcedLeray.B0411.L0 ν E) x = -(ν • dy j (lapT E) x) := by
  have hlap : DifferentiableAt ℝ (lapT E) x :=
    ((lapT_contDiff E hE).differentiable (by simp)) x
  simp only [dy]
  rw [(L0_eventuallyEq_neg_nuLapT ν E U hU hdrift x hx).fderiv_eq]
  rw [fderiv_fun_neg, fderiv_fun_const_smul hlap]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.ProdHom
