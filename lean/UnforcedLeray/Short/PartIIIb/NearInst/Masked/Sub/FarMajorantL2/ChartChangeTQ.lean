import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The phase change of variables over one period (source 2667)

For a `2c/R`-periodic measurable `Ξ` and any `a`,
`∫_{[0,2c/R)} Ξ = (2/R) ∫_{q ∈ [-c/2, c/2)} Ξ(2q/R + a) dq`.

Proof: the window `[a - c/R, a + c/R)` has length `2c/R`, so its integral equals the integral over
one period (any window of one period is the integral over the circle `AddCircle (2c/R)`); the affine
map `q ↦ 2q/R + a` sends `[-c/2, c/2)` onto that window with derivative `2/R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem chartChangeTQ_holds : ChartChangeTQ := by
  intro R c hR hc Ξ hΞm hΞp a
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have : Fact (0 < 2 * c / R) := ⟨hP⟩
  have hp : Function.Periodic Ξ (2 * c / R) := hΞp
  -- any window of one period is the integral over the circle
  have window : ∀ b : ℝ, ∫⁻ τ in Ico b (b + 2 * c / R), Ξ τ =
      ∫⁻ x : AddCircle (2 * c / R), hp.lift x := by
    intro b
    rw [← AddCircle.lintegral_preimage (2 * c / R) b hp.lift]
    rw [setLIntegral_congr (Ico_ae_eq_Ioc : Ico b (b + 2 * c / R) =ᵐ[volume] Ioc b (b + 2 * c / R))]
    rfl
  have hwin : a - c / R + 2 * c / R = a + c / R := by ring
  have h0 : ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), Ξ τ = ∫⁻ x : AddCircle (2 * c / R), hp.lift x := by
    have := window 0
    rw [zero_add] at this
    exact this
  have hw1 : ∫⁻ τ in Ico (a - c / R) (a + c / R), Ξ τ = ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), Ξ τ := by
    rw [h0, ← hwin, window (a - c / R)]
  rw [← hw1]
  -- the affine change of variables `q ↦ 2q/R + a`
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have e1 : c / R * R = c := div_mul_cancel₀ c hR.ne'
  have himg : (fun q : ℝ => 2 * q / R + a) '' Ico (-c / 2) (c / 2) = Ico (a - c / R) (a + c / R) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ico]
    constructor
    · rintro ⟨q, ⟨h1, h2⟩, rfl⟩
      have u1 : 0 ≤ (2 * q + c) * R⁻¹ := mul_nonneg (by linarith) hRi.le
      have u2 : 0 < (c - 2 * q) * R⁻¹ := mul_pos (by linarith) hRi
      have v1 : (2 * q + c) * R⁻¹ = 2 * q / R + c / R := by ring
      have v2 : (c - 2 * q) * R⁻¹ = c / R - 2 * q / R := by ring
      constructor
      · linarith
      · linarith
    · rintro ⟨h1, h2⟩
      have w1 : 0 ≤ (y - a + c / R) * R := mul_nonneg (by linarith) hR.le
      have w2 : 0 < (a + c / R - y) * R := mul_pos (by linarith) hR
      have x1 : (y - a + c / R) * R = (y - a) * R + c := by rw [add_mul, e1]
      have x2 : (a + c / R - y) * R = a * R + c - y * R := by rw [sub_mul, add_mul, e1]
      refine ⟨(y - a) * R / 2, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · field_simp
        ring
  have hd : ∀ x : ℝ, HasDerivAt (fun q : ℝ => 2 * q / R + a) (2 / R) x := by
    intro x
    have := (((hasDerivAt_id x).const_mul 2).div_const R).add_const a
    simpa using this
  have hdiff : ∀ x ∈ Ico (-c / 2) (c / 2),
      HasDerivWithinAt (fun q : ℝ => 2 * q / R + a) (2 / R) (Ico (-c / 2) (c / 2)) x :=
    fun x _ => (hd x).hasDerivWithinAt
  have hinj : InjOn (fun q : ℝ => 2 * q / R + a) (Ico (-c / 2) (c / 2)) := by
    intro x _ y _ hxy
    have h' : 2 * x / R = 2 * y / R := by
      simp only at hxy
      linarith
    have h'' : 2 * x = 2 * y := by
      have := h'
      field_simp at this
      linarith
    linarith
  have key := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (f := fun q : ℝ => 2 * q / R + a) (f' := fun _ => 2 / R) measurableSet_Ico hdiff hinj Ξ
  rw [← himg, key]
  simp only [abs_of_pos (div_pos two_pos hR)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
