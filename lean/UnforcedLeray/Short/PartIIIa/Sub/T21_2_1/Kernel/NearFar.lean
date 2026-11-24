import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# Part III-a, `PartIII-a:T21/2/1/2/1`: the near/far split of the periodic kernel `K_d`

Source of record: `the November 2 reference manuscript` lines 2117-2121, 2876-2881.
Proof of `kerNearFar` from the library split `UnforcedLeray.Cyl.bsKernel_split`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem cell_eq_Cyl' (c : ℝ) : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem bsC_neg' (c : ℝ) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.bsC c (-z) = -UnforcedLeray.Cyl.bsC c z := by
  have key : ∀ w : ℂ, UnforcedLeray.Kernels.cylinderBS c (-w) =
      -UnforcedLeray.Kernels.cylinderBS c w := by
    intro w
    unfold UnforcedLeray.Kernels.cylinderBS
    have hcot : ∀ x : ℂ, Complex.cot (-x) = -Complex.cot x := by
      intro x
      rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cos_neg,
        Complex.sin_neg, div_neg]
    rw [show (Real.pi : ℂ) * -w / c = -((Real.pi : ℂ) * w / c) by ring, hcot]
    ring
  have e : (((-z).1 : ℝ) : ℂ) + (((-z).2 : ℝ) : ℂ) * Complex.I =
      -((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) := by
    simp only [Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg]
    ring
  unfold UnforcedLeray.Cyl.bsC
  rw [e, key]

theorem bsKernel_neg' (c : ℝ) (z : ℝ × ℝ) (j : Fin 2) :
    UnforcedLeray.Cyl.bsKernel c (-z) j = -UnforcedLeray.Cyl.bsKernel c z j := by
  unfold UnforcedLeray.Cyl.bsKernel
  rw [bsC_neg']
  fin_cases j <;> simp

theorem enorm_comp_le' (v : UnforcedLeray.Cyl.Vec2) :
    ∑ j, ‖v j‖ₑ ≤ 2 * ‖v‖ₑ := by
  have h : ∀ j, ‖v j‖ₑ ≤ ‖v‖ₑ := fun j => PiLp.enorm_apply_le v j
  calc ∑ j, ‖v j‖ₑ ≤ ∑ _j : Fin 2, ‖v‖ₑ := Finset.sum_le_sum fun j _ => h j
    _ = 2 * ‖v‖ₑ := by simp [two_mul]

/-- **The near/far split of the periodic kernel** (`KerNearFar`, SP 2117-2121, 2876-2881). -/
theorem kerNearFar : UnforcedLeray.Short.IIIa.KerNearFar := by
  obtain ⟨C0, hC0, hsplit⟩ := UnforcedLeray.Cyl.bsKernel_split
  refine ⟨2 * C0 + 2, by linarith, fun d hd => ?_⟩
  simp only [cell_eq_Cyl']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ((PiLp.continuous_apply 2 _ j).measurable).comp (UnforcedLeray.Cyl.measurable_bsKernel d)
  · intro z j
    show UnforcedLeray.Cyl.bsKernel d (z.1 + d, z.2) j = UnforcedLeray.Cyl.bsKernel d z j
    rw [UnforcedLeray.Cyl.isPeriodic_bsKernel d z]
  · intro z j
    exact bsKernel_neg' d z j
  · have hmeas : MeasurableSet (UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) :=
      (UnforcedLeray.Cyl.measurableSet_cell d).inter Metric.isOpen_ball.measurableSet
    have hpt : ∀ z ∈ UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
        ∑ j, ‖UnforcedLeray.Cyl.bsKernel d z j‖ₑ ≤
          2 * ‖UnforcedLeray.Cyl.kNear d z‖ₑ := by
      intro z hz
      have hk : UnforcedLeray.Cyl.kNear d z = UnforcedLeray.Cyl.bsKernel d z := by
        rw [UnforcedLeray.Cyl.kNear, Set.indicator_of_mem hz]
      rw [hk]
      exact enorm_comp_le' _
    have hsplit_d := (hsplit d hd).1
    calc ∫⁻ z in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
          ∑ j, ‖UnforcedLeray.Cyl.bsKernel d z j‖ₑ
        ≤ ∫⁻ z in UnforcedLeray.Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            2 * ‖UnforcedLeray.Cyl.kNear d z‖ₑ :=
          setLIntegral_mono' hmeas hpt
      _ ≤ ∫⁻ z in UnforcedLeray.Cyl.cell d, 2 * ‖UnforcedLeray.Cyl.kNear d z‖ₑ :=
          lintegral_mono_set inter_subset_left
      _ = 2 * ∫⁻ z in UnforcedLeray.Cyl.cell d, ‖UnforcedLeray.Cyl.kNear d z‖ₑ :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 2 * ENNReal.ofReal C0 := by gcongr
      _ = ENNReal.ofReal (2 * C0) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (2 * C0 + 2) := ENNReal.ofReal_le_ofReal (by linarith)
  · intro z hz hball j
    have h1 : 1 ≤ ‖z‖ := not_lt.1 (fun h => hball (mem_ball_zero_iff.2 h))
    calc |UnforcedLeray.Cyl.bsKernel d z j|
        = ‖UnforcedLeray.Cyl.bsKernel d z j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖UnforcedLeray.Cyl.bsKernel d z‖ := PiLp.norm_apply_le _ _
      _ ≤ 2 := UnforcedLeray.Cyl.norm_bsKernel_le_far hd hz h1
      _ ≤ 2 * C0 + 2 := by linarith

end UnforcedLeray.Short.IIIa
