import Mathlib.Analysis.Calculus.MeanValue
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonOrg

/-!
# Mean-value shift difference bound for `D3t` (`PartIII-b:IIIb-D3/2/G5/2/4`)

Source `the November 2 reference manuscript` lines 4879-4892.
Proves `d3tDiffBound : FlatUnif.G5.D3tDiffBound` from `NewtonVGeom.D3t_shift_bound (m + 1)`
and the convex mean-value inequality on `segment ℝ w (w - t • embPlane x')`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

open NewtonVGeom

/-- Coordinate bound for `embPlane`: `‖embPlane x'‖ ≤ √(x'₁² + x'₂²)`. -/
theorem norm_embPlane_le (x' : ℝ × ℝ) :
    ‖embPlane x'‖ ≤ Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i <;> exact Real.abs_le_sqrt (by simp [embPlane]; nlinarith)

/-- Norm bound for the planar shift `t • embPlane x'` when `0 ≤ t ≤ 1`. -/
theorem norm_smul_embPlane_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x' : ℝ × ℝ) :
    ‖t • embPlane x'‖ ≤ Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc t * ‖embPlane x'‖
      ≤ 1 * Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) :=
        mul_le_mul ht1 (norm_embPlane_le x') (norm_nonneg _) zero_le_one
    _ = Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := one_mul _

/-- Mean-value shift difference bound for `D3t` (source 4879-4892). -/
theorem d3tDiffBound : FlatUnif.G5.D3tDiffBound := by
  intro m
  obtain ⟨K, hK0, hK⟩ := NewtonVGeom.D3t_shift_bound (m + 1)
  refine ⟨K, hK0, ?_⟩
  intro ν t w x' hν ht0 ht1 hw hx
  let v : Vec3 := t • embPlane x'
  have hz_end : w - v ≠ 0 := shift_ne_zero hν ht0 ht1 hw hx
  have hw0 : w ≠ 0 := regU_ne_zero hν hw
  have hcd_shift : ContDiffAt ℝ NewtonD3.ii (fun x => D3t (x - v)) w :=
    (D3t_contDiffAt hz_end).comp w (contDiffAt_id.sub contDiffAt_const)
  have hcd_id : ContDiffAt ℝ NewtonD3.ii D3t w := D3t_contDiffAt hw0
  have hhm : (m : WithTop ℕ∞) ≤ NewtonD3.ii := by
    unfold NewtonD3.ii; exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
  have hsub : iteratedFDeriv ℝ m (fun x => D3t (x - v) - D3t x) w =
      iteratedFDeriv ℝ m D3t (w - v) - iteratedFDeriv ℝ m D3t w := by
    have h1 := iteratedFDeriv_sub_apply (i := m)
      (hcd_shift.of_le hhm) (hcd_id.of_le hhm)
    have h2 : iteratedFDeriv ℝ m (fun x => D3t (x - v)) w = iteratedFDeriv ℝ m D3t (w - v) :=
      iteratedFDeriv_comp_sub (f := D3t) m v w
    exact h1.trans (by rw [h2])
  rw [hsub]
  have hseg_form : ∀ z ∈ segment ℝ w (w - v),
      ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ z = w - (τ * t) • embPlane x' := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b, hb, by linarith, ?_⟩
    ext i
    simp only [v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc a * w i + b * (w i - t * embPlane x' i)
        = (a + b) * w i - b * t * embPlane x' i := by ring
      _ = w i - b * t * embPlane x' i := by rw [hab, one_mul]
  have hdiff_seg : ∀ z ∈ segment ℝ w (w - v),
      DifferentiableAt ℝ (iteratedFDeriv ℝ m D3t) z := by
    intro z hz
    obtain ⟨τ, hτ0, hτ1, rfl⟩ := hseg_form z hz
    have hτt0 : 0 ≤ τ * t := mul_nonneg hτ0 ht0
    have hτt1 : τ * t ≤ 1 := by nlinarith
    have hz0 : w - (τ * t) • embPlane x' ≠ 0 := shift_ne_zero hν hτt0 hτt1 hw hx
    exact (D3t_contDiffAt hz0).differentiableAt_iteratedFDeriv
      (by unfold NewtonD3.ii; exact_mod_cast WithTop.coe_lt_top m)
  have hbound_seg : ∀ z ∈ segment ℝ w (w - v),
      ‖fderiv ℝ (iteratedFDeriv ℝ m D3t) z‖ ≤
        K * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) := by
    intro z hz
    obtain ⟨τ, hτ0, hτ1, rfl⟩ := hseg_form z hz
    have hτt0 : 0 ≤ τ * t := mul_nonneg hτ0 ht0
    have hτt1 : τ * t ≤ 1 := by nlinarith
    rw [norm_fderiv_iteratedFDeriv]
    have hcomp : iteratedFDeriv ℝ (m + 1) D3t (w - (τ * t) • embPlane x') =
        iteratedFDeriv ℝ (m + 1) (fun x => D3t (x - (τ * t) • embPlane x')) w :=
      (iteratedFDeriv_comp_sub (f := D3t) (m + 1) ((τ * t) • embPlane x') w).symm
    rw [hcomp]
    have hb := hK ν (τ * t) w x' hν hτt0 hτt1 hw hx
    have hexp : (-(4 : ℝ) - (m + 1 : ℕ)) = -(5 : ℝ) - m := by push_cast; ring
    rwa [hexp] at hb
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
    hdiff_seg hbound_seg (convex_segment w (w - v))
    (left_mem_segment ℝ w (w - v)) (right_mem_segment ℝ w (w - v))
  have hsub_v : ‖(w - v) - w‖ = ‖v‖ := by
    rw [sub_sub_cancel_left, norm_neg]
  rw [hsub_v] at hmvt
  have hv_le : ‖v‖ ≤ Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) :=
    norm_smul_embPlane_le ht0 ht1 x'
  have hC0 : 0 ≤ K * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) :=
    mul_nonneg hK0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  calc ‖iteratedFDeriv ℝ m D3t (w - v) - iteratedFDeriv ℝ m D3t w‖
      ≤ K * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) * ‖v‖ := hmvt
    _ ≤ K * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) * Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) :=
        mul_le_mul_of_nonneg_left hv_le hC0
    _ = K * Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
