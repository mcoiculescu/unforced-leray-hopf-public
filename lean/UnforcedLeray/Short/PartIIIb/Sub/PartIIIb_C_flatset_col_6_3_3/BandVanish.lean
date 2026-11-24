import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3

/-!
# Vanishing of derivatives outside an `η`-band

A function vanishing on the open set `{R < |η|}` has all partial derivatives vanishing there, hence so
do `Δφ` and `νΔφ + v·∇φ`.  Used by the box versions of the pairing bounds (source 3511-3514,
4464-4467 of `the November 2 reference manuscript`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.Short.IIIa (lapP)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Partial derivatives of a function vanishing for `|η| > R` vanish for `|η| > R`. -/
theorem pd_vanish {R : ℝ} {φ : ℝ × ℝ → ℝ} (h : ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) (j : Fin 2) :
    ∀ x : ℝ × ℝ, R < |x.2| → B0579.pd j φ x = 0 := by
  intro x hx
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => h y hy
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

/-- `νΔφ + v·∇φ` vanishes for `|η| > R` when `φ` does. -/
theorem vtvFlowTest_vanish {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) {R : ℝ}
    {φ : ℝ × ℝ → ℝ} (h : ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) :
    ∀ x : ℝ × ℝ, R < |x.2| → vtvFlowTest tr s φ x = 0 := by
  intro x hx
  have h0 := pd_vanish h 0
  have h1 := pd_vanish h 1
  have h00 := pd_vanish h0 0 x hx
  have h11 := pd_vanish h1 1 x hx
  simp [vtvFlowTest, lapP, h00, h11, h0 x hx, h1 x hx]

/-- The derivative in the age of a stream test vanishes for `|η| > R`. -/
theorem deriv_age_vanish {η : ℝ → ℝ × ℝ → ℝ} {R : ℝ}
    (h : ∀ s (x : ℝ × ℝ), R < |x.2| → η s x = 0) (s : ℝ) :
    ∀ x : ℝ × ℝ, R < |x.2| → deriv (fun s' => η s' x) s = 0 := by
  intro x hx
  have : (fun s' => η s' x) = fun _ => (0 : ℝ) := funext fun s' => h s' x hx
  rw [this, deriv_const]

theorem measurableSet_vtvBox (c R : ℝ) : MeasurableSet (vtvBox c R) :=
  (B0579.measurableSet_cell c).inter
    (measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const)

theorem vtvBox_subset_cell (c R : ℝ) : vtvBox c R ⊆ B0579.cell c := inter_subset_left

/-- The box has finite measure. -/
theorem volume_vtvBox_lt_top (c R : ℝ) : volume (vtvBox c R) < ⊤ := by
  have hsub : vtvBox c R ⊆ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R := by
    intro x hx
    obtain ⟨⟨h1, -⟩, h2⟩ := hx
    exact ⟨⟨h1.1, h1.2.le⟩, abs_le.1 h2⟩
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top

/-- `L²(cell)` functions are `L¹` on every box. -/
theorem integrableOn_vtvBox_of_memLp {c : ℝ} (R : ℝ) {u : ℝ × ℝ → ℂ}
    (h : MemLp u 2 (volume.restrict (B0579.cell c))) : IntegrableOn u (vtvBox c R) := by
  have h' : MemLp u 2 (volume.restrict (vtvBox c R)) :=
    h.mono_measure (Measure.restrict_mono (vtvBox_subset_cell c R) le_rfl)
  have : IsFiniteMeasure (volume.restrict (vtvBox c R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_vtvBox_lt_top c R⟩
  exact h'.integrable (by norm_num)

/-- **Box pairing estimate**: for `ψ` vanishing for `|η| > R` with `|∇ψ| ≤ K` and `u₀,u₁` integrable
on the box, `‖∫_cell (u₀∂_ηψ - u₁∂_qψ)‖ ≤ K ∫_box (‖u₀‖+‖u₁‖)`. -/
theorem pair_le (c R : ℝ) (u0 u1 : ℝ × ℝ → ℂ) (h0 : IntegrableOn u0 (vtvBox c R))
    (h1 : IntegrableOn u1 (vtvBox c R)) (ψ : ℝ × ℝ → ℝ)
    (hz : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) (K : ℝ) (hK : ∀ x j, |B0579.pd j ψ x| ≤ K) :
    ‖∫ x in B0579.cell c, (u0 x * (B0579.pd 1 ψ x : ℂ) - u1 x * (B0579.pd 0 ψ x : ℂ))‖ ≤
      K * ∫ x in vtvBox c R, (‖u0 x‖ + ‖u1 x‖) := by
  have d0 := pd_vanish hz 0
  have d1 := pd_vanish hz 1
  have hG : IntegrableOn (fun x => K * (‖u0 x‖ + ‖u1 x‖)) (vtvBox c R) :=
    ((h0.norm).add h1.norm).const_mul K
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B0579.measurableSet_cell c)
    (vtvBox_subset_cell c R) (f := fun x => u0 x * (B0579.pd 1 ψ x : ℂ) - u1 x * (B0579.pd 0 ψ x : ℂ))
    fun x hx => by
      have hx2 : R < |x.2| := by
        by_contra hcon
        exact hx.2 ⟨hx.1, not_lt.1 hcon⟩
      simp [d0 x hx2, d1 x hx2], ← integral_const_mul]
  refine norm_integral_le_of_norm_le hG (Eventually.of_forall fun x => ?_)
  have e0 := hK x 0
  have e1 := hK x 1
  calc ‖u0 x * (B0579.pd 1 ψ x : ℂ) - u1 x * (B0579.pd 0 ψ x : ℂ)‖
      ≤ ‖u0 x * (B0579.pd 1 ψ x : ℂ)‖ + ‖u1 x * (B0579.pd 0 ψ x : ℂ)‖ := norm_sub_le _ _
    _ = ‖u0 x‖ * |B0579.pd 1 ψ x| + ‖u1 x‖ * |B0579.pd 0 ψ x| := by simp
    _ ≤ ‖u0 x‖ * K + ‖u1 x‖ * K := by gcongr
    _ = K * (‖u0 x‖ + ‖u1 x‖) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
