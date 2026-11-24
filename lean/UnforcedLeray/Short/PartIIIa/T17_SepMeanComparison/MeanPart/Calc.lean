import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailIterated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailZero
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.Part2Calculus

/-!
# Mean part helper: calculus of the kernel derivatives (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mp_fderiv_shift (κ : Space → ℝ) (a y v e : Space) (hκ : ContDiffAt ℝ 2 κ (y - a)) :
    fderiv ℝ (fun y' => fderiv ℝ κ (y' - a) e) y v = iteratedFDeriv ℝ 2 κ (y - a) ![v, e] := by
  have h1 : HasFDerivAt (fderiv ℝ κ) (fderiv ℝ (fderiv ℝ κ) (y - a)) (y - a) :=
    ((hκ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => fderiv ℝ κ (y' - a)) (fderiv ℝ (fderiv ℝ κ) (y - a)) y :=
    (h1.comp y ((hasFDerivAt_id y).sub_const a)).congr_fderiv (by simp)
  have h3 : HasFDerivAt (fun y' => fderiv ℝ κ (y' - a) e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ κ) (y - a))) y :=
    (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp y h2
  rw [h3.fderiv, iteratedFDeriv_two_apply]
  simp

theorem mp_K0_contDiffAt (u : Space) (hu : u ≠ 0) (i k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => heatLerayK0 i k y) u := by
  have hH0 : ContDiffAt ℝ ∞ (heatTail 0) u := (heatTailIterated 0 le_rfl u hu).1
  have hfg : (fun y : Space => (4 * Real.pi * ‖y‖)⁻¹) =ᶠ[𝓝 u] heatTail 0 := by
    filter_upwards [isOpen_ne.mem_nhds hu] with y hy
    exact (heatTailZero y hy).symm
  have hf : ContDiffAt ℝ ∞ (fun y : Space => (4 * Real.pi * ‖y‖)⁻¹) u :=
    hH0.congr_of_eventuallyEq hfg
  exact (part2Calculus _ _ u hf hf i k).1

theorem mp_rho_sub (u₀ u : Space) (h0 : u 0 = u₀ 0) (h1 : u 1 = u₀ 1) :
    Real.sqrt (u 0 ^ 2 + u 1 ^ 2) = Real.sqrt (u₀ 0 ^ 2 + u₀ 1 ^ 2) := by
  rw [h0, h1]

/-- Kernel difference estimate: heat error plus vertical Taylor error (SP 3760-3766). -/
theorem mp_kernel_diff (hK : SepKernelBounds) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i k : Fin 3) (s : ℝ), 0 < s → ∀ (u₀ u : Space) (D : ℝ), 0 < D →
      D ≤ Real.sqrt (u₀ 0 ^ 2 + u₀ 1 ^ 2) → u 0 = u₀ 0 → u 1 = u₀ 1 →
        ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK s i k x) u -
            iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u₀‖ ≤
          C * (s + ‖u - u₀‖) * (D ^ (-7 : ℝ) + D ^ (-6 : ℝ)) := by
  obtain ⟨C, hCb⟩ := hK 2
  have hC0 : 0 ≤ C := by
    have h := hCb (!₂[1, 0, 0]) (by
      intro h0
      have := congrArg (fun x : Space => x 0) h0
      simp at this) 0 0
    have h1 := (h.2.2 1 one_pos)
    have h2 := norm_nonneg (iteratedFDeriv ℝ 2 (fun y => heatLerayK 1 0 0 y - heatLerayK0 0 0 y) (!₂[1, 0, 0]))
    have h3 : 0 ≤ ‖(!₂[1, 0, 0] : Space)‖ ^ (-5 - ((2 : ℕ) : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    by_contra hneg
    push_neg at hneg
    have : C * 1 * ‖(!₂[1, 0, 0] : Space)‖ ^ (-5 - ((2 : ℕ) : ℝ)) ≤ 0 := by
      have : C * 1 * ‖(!₂[1, 0, 0] : Space)‖ ^ (-5 - ((2 : ℕ) : ℝ)) = C * (1 * ‖(!₂[1, 0, 0] : Space)‖ ^ (-5 - ((2 : ℕ) : ℝ))) := by ring
      rw [this]
      exact mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
    have hpos : 0 < ‖(!₂[1, 0, 0] : Space)‖ := by
      rw [norm_pos_iff]
      intro h0
      have := congrArg (fun x : Space => x 0) h0
      simp at this
    have : 0 < ‖(!₂[1, 0, 0] : Space)‖ ^ (-5 - ((2 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hpos _
    nlinarith
  refine ⟨2 * C, by positivity, ?_⟩
  intro i k s hs u₀ u D hD hDu₀ hu0 hu1
  have hρ := mp_rho_sub u₀ u hu0 hu1
  have hnormu : D ≤ ‖u‖ := by
    refine hDu₀.trans ?_
    rw [← hρ]
    exact rho_le_norm u
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnormu
    linarith
  have hu₀_ne : u₀ ≠ 0 := by
    intro h0
    have : Real.sqrt (u₀ 0 ^ 2 + u₀ 1 ^ 2) = 0 := by rw [h0]; simp
    linarith
  -- heat error
  have hK1 : ContDiffAt ℝ 2 (fun x => heatLerayK s i k x) u :=
    by simpa using contDiffAt_nat ((heatLerayKSmoothAll s hs i k).contDiffAt) 2
  have hK0 : ContDiffAt ℝ 2 (fun x => heatLerayK0 i k x) u :=
    by simpa using contDiffAt_nat (mp_K0_contDiffAt u hu_ne i k) 2
  have hdiff : iteratedFDeriv ℝ 2 (fun x => heatLerayK s i k x) u -
      iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u =
      iteratedFDeriv ℝ 2 (fun y => heatLerayK s i k y - heatLerayK0 i k y) u :=
    (iteratedFDeriv_sub_apply hK1 hK0).symm
  have hheat : ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK s i k x) u -
      iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u‖ ≤ C * s * D ^ (-7 : ℝ) := by
    rw [hdiff]
    refine ((hCb u hu_ne i k).2.2 s hs).trans ?_
    have : ‖u‖ ^ (-5 - ((2 : ℕ) : ℝ)) ≤ D ^ (-7 : ℝ) := by
      have := Real.rpow_le_rpow_of_nonpos hD hnormu (by norm_num : (-5 - ((2 : ℕ) : ℝ)) ≤ 0)
      norm_num at this ⊢
      exact this
    have hCs : 0 ≤ C * s := by positivity
    exact mul_le_mul_of_nonneg_left this hCs
  -- Taylor error along the vertical segment
  have hseg : ∀ x ∈ segment ℝ u₀ u, D ≤ ‖x‖ := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    have h0 : (a • u₀ + b • u) 0 = u₀ 0 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu0]
      rw [← add_mul, hab, one_mul]
    have h1 : (a • u₀ + b • u) 1 = u₀ 1 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu1]
      rw [← add_mul, hab, one_mul]
    refine hDu₀.trans ?_
    have := rho_le_norm (a • u₀ + b • u)
    rw [h0, h1] at this
    exact this
  have hne : ∀ x ∈ segment ℝ u₀ u, x ≠ 0 := by
    intro x hx h0
    have := hseg x hx
    rw [h0, norm_zero] at this
    linarith
  have hdf : ∀ x ∈ segment ℝ u₀ u, DifferentiableAt ℝ (iteratedFDeriv ℝ 2 (fun y => heatLerayK0 i k y)) x := by
    intro x hx
    have := (mp_K0_contDiffAt x (hne x hx) i k)
    exact (this.differentiableAt_iteratedFDeriv (m := 2) (n := ∞) (by norm_cast))
  have hbd : ∀ x ∈ segment ℝ u₀ u,
      ‖fderiv ℝ (iteratedFDeriv ℝ 2 (fun y => heatLerayK0 i k y)) x‖ ≤ C * D ^ (-6 : ℝ) := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    refine ((hCb x (hne x hx) i k).2.1).trans ?_
    have := Real.rpow_le_rpow_of_nonpos hD (hseg x hx) (by norm_num : (-4 - ((2 : ℕ) : ℝ)) ≤ 0)
    have h2 : ‖x‖ ^ (-4 - ((2 : ℕ) : ℝ)) ≤ D ^ (-6 : ℝ) := by norm_num at this ⊢; exact this
    exact mul_le_mul_of_nonneg_left h2 hC0
  have hmv := (convex_segment u₀ u).norm_image_sub_le_of_norm_fderiv_le hdf hbd
    (left_mem_segment ℝ u₀ u) (right_mem_segment ℝ u₀ u)
  have hD7 : 0 ≤ D ^ (-7 : ℝ) := Real.rpow_nonneg hD.le _
  have hD6 : 0 ≤ D ^ (-6 : ℝ) := Real.rpow_nonneg hD.le _
  calc ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK s i k x) u -
        iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u₀‖
      = ‖(iteratedFDeriv ℝ 2 (fun x => heatLerayK s i k x) u -
          iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u) +
          (iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u -
          iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u₀)‖ := by congr 1; abel
    _ ≤ ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK s i k x) u -
          iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u‖ +
        ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u -
          iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i k x) u₀‖ := norm_add_le _ _
    _ ≤ C * s * D ^ (-7 : ℝ) + C * D ^ (-6 : ℝ) * ‖u - u₀‖ := add_le_add hheat hmv
    _ ≤ 2 * C * (s + ‖u - u₀‖) * (D ^ (-7 : ℝ) + D ^ (-6 : ℝ)) := by
      have h1 : 0 ≤ ‖u - u₀‖ := norm_nonneg _
      nlinarith [mul_nonneg hC0 hs.le, mul_nonneg hC0 h1, mul_nonneg (mul_nonneg hC0 hs.le) hD6,
        mul_nonneg (mul_nonneg hC0 h1) hD7, mul_nonneg (mul_nonneg hC0 hs.le) hD7,
        mul_nonneg (mul_nonneg hC0 h1) hD6]

theorem mp_scale (i j : Fin 3) (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) (u : Space) :
    iteratedFDeriv ℝ 2 (fun x => heatLerayK t i j x) (ε⁻¹ • u) =
      ε ^ 5 • iteratedFDeriv ℝ 2 (fun x => heatLerayK (t * ε ^ 2) i j x) u := by
  have hK1 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (fun x => heatLerayK 1 i j x) :=
    (heatLerayKSmoothAll 1 one_pos i j).of_le (by norm_cast)
  have hs : 0 < t * ε ^ 2 := by positivity
  rw [l2_iteratedFDeriv_scale i j 2 t ht _ hK1, l2_iteratedFDeriv_scale i j 2 (t * ε ^ 2) hs u hK1,
    smul_smul]
  have hsq : Real.sqrt (t * ε ^ 2) = Real.sqrt t * ε := by
    rw [Real.sqrt_mul ht.le, Real.sqrt_sq hε.le]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have harg : ((Real.sqrt t)⁻¹ * ε⁻¹) • u = (Real.sqrt (t * ε ^ 2))⁻¹ • u := by
    rw [hsq, mul_inv]
  rw [harg]
  have h1 : ((ε : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) = (ε ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    have : (((2 : ℕ) : ℝ) * (-(3 / 2 : ℝ))) = -((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg hε.le, Real.rpow_natCast]
  have h2 : (Real.sqrt t)⁻¹ ^ 2 = t⁻¹ := by
    rw [inv_pow, Real.sq_sqrt ht.le]
  have h3 : (Real.sqrt (t * ε ^ 2))⁻¹ ^ 2 = t⁻¹ * (ε ^ 2)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hs.le, mul_inv]
  have hcoef : t ^ (-(3 / 2 : ℝ)) * (Real.sqrt t)⁻¹ ^ 2 =
      ε ^ 5 * ((t * ε ^ 2) ^ (-(3 / 2 : ℝ)) * (Real.sqrt (t * ε ^ 2))⁻¹ ^ 2) := by
    rw [h2, h3, Real.mul_rpow ht.le (sq_nonneg ε), h1]
    field_simp
  rw [hcoef, smul_smul]

end UnforcedLeray.Short.IIIa

end
