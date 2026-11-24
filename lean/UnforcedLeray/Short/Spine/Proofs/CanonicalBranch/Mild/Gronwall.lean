import NonUniqueEuler.P.Infra.ODE.Gronwall

/-!
# Helper for `Spine:SP-CAN` Bridge 3: a backward Grönwall inequality

Helper module of `Short/Spine/Proofs/CanonicalBranch/Mild.lean`. The difference of two mild
solutions satisfies a backward integral inequality `f(s) ≤ K ∫_s^β f`, with `f ≥ 0` continuous.
It is reflected to the forward form `g(r) = f(β - r)` and handled by the integral Grönwall
inequality `NonUniqueEuler.LinODE.int_gronwall` (vendored, `P/Infra/ODE/Gronwall.lean`).

Main declaration (namespace `UnforcedLeray.Short.Spine.CanonicalMild`):
* `backward_gronwall`: `f = 0` on `[α, β]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.Spine.CanonicalMild

/-- **Backward Grönwall inequality.** A nonnegative continuous `f` on `[α, β]` with
`f s ≤ K ∫_s^β f` for all `s ∈ [α, β]` vanishes on `[α, β]`. -/
theorem backward_gronwall {α β K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc α β)) (hnn : ∀ s ∈ Icc α β, 0 ≤ f s)
    (hineq : ∀ s ∈ Icc α β, f s ≤ K * ∫ v in s..β, f v) :
    ∀ s ∈ Icc α β, f s = 0 := by
  have hgc : ContinuousOn (fun r : ℝ => f (β - r)) (Icc 0 (β - α)) := by
    apply ContinuousOn.comp hf (continuousOn_const.sub continuousOn_id)
    intro r hr
    show β - r ∈ Icc α β
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have key : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, f (β - t) = ∫ v in β - x..β, f v := by
    intro x
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := x) f β
    simpa only [sub_zero] using h
  have hh : ∀ x ∈ Icc 0 (β - α),
      f (β - x) ≤ ∫ t in (0 : ℝ)..x, K * (0 + f (β - t)) := by
    intro x hx
    simp only [zero_add]
    rw [intervalIntegral.integral_const_mul, key x]
    exact hineq (β - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hres := NonUniqueEuler.LinODE.int_gronwall hgc continuousOn_const
    (fun _ _ => hK) le_rfl hh
  intro s hs
  have hr : β - s ∈ Icc 0 (β - α) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 := hres (β - s) hr
  simp only [zero_add, zero_mul, sub_sub_cancel] at h1
  exact le_antisymm h1 (hnn s hs)

end UnforcedLeray.Short.Spine.CanonicalMild
