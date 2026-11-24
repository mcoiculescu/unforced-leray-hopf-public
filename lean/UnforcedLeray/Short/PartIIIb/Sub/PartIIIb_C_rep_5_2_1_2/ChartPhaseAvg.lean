import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2

/-!
# `PartIII-b:C/rep/5/2/1/2`: phase average `ChartPhaseAvg`

Source `the November 2 reference manuscript` 2683-2689, step (i):
for a measurable `2c/R`-periodic `H`, `c⁻¹∫_{[-c/2,c/2)} H(2q/R + a) dq = (2c/R)⁻¹∫_{(0,2c/R]} H`.
Proof: an affine change of variables `τ = (2/R) q + a` (one-dimensional Jacobian lemma), then
shift invariance of the integral of a periodic function over a window of length one period
(via the additive circle).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The integral of a `P`-periodic lintegrand over any window `(t, t + P]` equals the integral over
`(0, P]`. -/
lemma lintegral_Ioc_periodic_shift {P : ℝ} (hP : 0 < P) {H : ℝ → ℝ≥0∞}
    (hH : Function.Periodic H P) (t : ℝ) :
    ∫⁻ τ in Ioc t (t + P), H τ = ∫⁻ τ in Ioc 0 P, H τ := by
  have : Fact (0 < P) := ⟨hP⟩
  have hF : ∀ x : ℝ, hH.lift (x : AddCircle P) = H x := fun x => hH.lift_coe x
  have e1 := AddCircle.lintegral_preimage P t (hH.lift)
  have e0 := AddCircle.lintegral_preimage P 0 (hH.lift)
  rw [zero_add] at e0
  simp only [hF] at e1 e0
  rw [e1, e0]

/-- Affine change of variables on a half-open window, `τ = k q + a`, `k > 0`. -/
lemma lintegral_affine_Ioc {k a α β : ℝ} (hk : 0 < k) (g : ℝ → ℝ≥0∞) :
    ∫⁻ τ in Ioc (k * α + a) (k * β + a), g τ =
      ENNReal.ofReal k * ∫⁻ q in Ioc α β, g (k * q + a) := by
  have himg : (fun q => k * q + a) '' Ioc α β = Ioc (k * α + a) (k * β + a) := by
    ext y
    constructor
    · rintro ⟨q, ⟨h1, h2⟩, rfl⟩
      have h1' := mul_lt_mul_of_pos_left h1 hk
      have h2' := mul_le_mul_of_nonneg_left h2 hk.le
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(y - a) / k, ⟨?_, ?_⟩, ?_⟩
      · rw [lt_div_iff₀ hk]; linarith [mul_comm k α]
      · rw [div_le_iff₀ hk]; linarith [mul_comm k β]
      · field_simp
        ring
  have hd : ∀ x ∈ Ioc α β, HasDerivWithinAt (fun q => k * q + a) k (Ioc α β) x := by
    intro x _
    have h : HasDerivAt (fun q => k * q + a) (k * 1) x :=
      ((hasDerivAt_id' x).const_mul k).add_const a
    rw [mul_one] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun q => k * q + a) (Ioc α β) := by
    intro x _ y _ hxy
    have h := add_right_cancel hxy
    exact mul_left_cancel₀ hk.ne' h
  rw [← himg, MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hd hinj]
  rw [abs_of_pos hk]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Phase average (step (i)), the statement `ChartPhaseAvg`. -/
theorem chartPhaseAvg : ChartPhaseAvg := by
  intro R c hR hc H _hm hper a
  have hk : 0 < 2 / R := div_pos two_pos hR
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hper' : Function.Periodic H (2 * c / R) := hper
  have e : ∀ q : ℝ, 2 * q / R + a = 2 / R * q + a := fun q => by ring
  simp only [e]
  have hA : ∫⁻ q in Ico (-c / 2) (c / 2), H (2 / R * q + a) =
      ∫⁻ q in Ioc (-c / 2) (c / 2), H (2 / R * q + a) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  have hB := lintegral_affine_Ioc (k := 2 / R) (a := a) (α := -c / 2) (β := c / 2) hk H
  have hend : 2 / R * (c / 2) + a = (2 / R * (-c / 2) + a) + 2 * c / R := by ring
  rw [hend] at hB
  have hperiod := lintegral_Ioc_periodic_shift hP hper' (2 / R * (-c / 2) + a)
  have hY : ∫⁻ τ in Ioc 0 (2 * c / R), H τ =
      ENNReal.ofReal (2 / R) * ∫⁻ q in Ioc (-c / 2) (c / 2), H (2 / R * q + a) := by
    rw [← hperiod]; exact hB
  have hPc : ENNReal.ofReal (2 * c / R) = ENNReal.ofReal c * ENNReal.ofReal (2 / R) := by
    rw [← ENNReal.ofReal_mul hc.le]; congr 1; ring
  have hcne : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have h2ne : ENNReal.ofReal (2 / R) ≠ 0 := (ENNReal.ofReal_pos.2 hk).ne'
  have h2top : ENNReal.ofReal (2 / R) ≠ ∞ := ENNReal.ofReal_ne_top
  have hBB : (ENNReal.ofReal (2 / R))⁻¹ * (ENNReal.ofReal (2 / R) *
      ∫⁻ q in Ioc (-c / 2) (c / 2), H (2 / R * q + a)) =
      ∫⁻ q in Ioc (-c / 2) (c / 2), H (2 / R * q + a) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel h2ne h2top, one_mul]
  rw [hA, hPc, ENNReal.ofReal_inv_of_pos hc, ENNReal.mul_inv (Or.inl hcne) (Or.inr h2ne), hY,
    mul_assoc ((ENNReal.ofReal c)⁻¹) ((ENNReal.ofReal (2 / R))⁻¹), hBB]

end UnforcedLeray.Short.PartIIIb.Concrete
