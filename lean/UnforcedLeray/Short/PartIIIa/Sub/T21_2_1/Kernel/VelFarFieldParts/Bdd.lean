import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar

/-!
# Part III-a, `KerVelBdd`: uniform boundedness of the kernel velocity (SP 3052-3055, 2117-2121)

Swapping the convolution (`integral_cell_mul_comp_sub`) puts the periodic kernel at the cell
variable `y`, so that only `K_d` on the cell and the bounded test `ψ(x - y)` appear. `ψ` is bounded
and vanishes off the band `|η| ≤ R`, so only the strip `|x.2 - y.2| ≤ R` contributes. On the strip,
the near part is integrable (`KerNearFar`) and the far part is bounded.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A test is bounded, and vanishes beyond a band of width `R ≥ 0`. -/
theorem test_data {d : ℝ} (hd : 1 ≤ d) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧ (∀ x : ℝ × ℝ, |ψ x| ≤ M) ∧
      (∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) := by
  obtain ⟨R0, hR0⟩ := hψ.band
  have hd0 : 0 < d := by linarith
  have hR : ∀ x : ℝ × ℝ, |R0| < |x.2| → ψ x = 0 := fun x hx =>
    hR0 x (lt_of_le_of_lt (le_abs_self R0) hx)
  have hcpt : IsCompact (Icc (-(d / 2)) (d / 2) ×ˢ Icc (-|R0|) |R0|) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨max C 0, |R0|, le_max_right _ _, abs_nonneg _, fun x => ?_, hR⟩
  by_cases hx : |R0| < |x.2|
  · rw [hR x hx, abs_zero]
    exact le_max_right _ _
  · push Not at hx
    have hper : Function.Periodic (fun t : ℝ => ψ (t, x.2)) d := fun t => hψ.periodic (t, x.2)
    obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico hd0 x.1 (-(d / 2))
    have hmem : (y, x.2) ∈ Icc (-(d / 2)) (d / 2) ×ˢ Icc (-|R0|) |R0| := by
      refine ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      exact abs_le.mp hx
    have h1 := hC (y, x.2) hmem
    have hxeq : ψ x = ψ (y, x.2) := hyeq
    have h2 : |ψ (y, x.2)| ≤ C := by simpa [Real.norm_eq_abs] using h1
    rw [hxeq]
    exact le_trans h2 (le_max_left _ _)

/-- The volume of a strip of the cell. -/
theorem vol_strip (d R t : ℝ) :
    volume (Ico (-(d / 2)) (d / 2) ×ˢ Icc (t - R) (t + R)) =
      ENNReal.ofReal d * ENNReal.ofReal (2 * R) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
    show d / 2 - -(d / 2) = d by ring, show t + R - (t - R) = 2 * R by ring]

/-- **Uniform boundedness of the kernel velocity** (`KerVelBdd`, SP 3054-3055). -/
theorem kerVelBdd : UnforcedLeray.Short.IIIa.KerVelBdd := by
  intro d hd ψ hψ
  have hd0 : 0 < d := by linarith
  have hNF0 := kerNearFar
  unfold KerNearFar at hNF0
  obtain ⟨C, hC0, hNF⟩ := hNF0
  obtain ⟨-, hperk, -, hnear, hfar⟩ := hNF d hd
  obtain ⟨M, R, hM0, hR0, hMb, hRb⟩ := test_data hd hψ
  refine ⟨M * C + M * C * (d * (2 * R)), fun x j => ?_⟩
  have hMC : 0 ≤ M * C := mul_nonneg hM0 hC0
  have hB0 : 0 ≤ M * C + M * C * (d * (2 * R)) := by
    have h2 : 0 ≤ d * (2 * R) := mul_nonneg hd0.le (by linarith)
    exact add_nonneg hMC (mul_nonneg hMC h2)
  -- swap the convolution: the kernel is now evaluated on the cell
  have hkp : UnforcedLeray.Cyl.IsPeriodic d (fun z => kerD d z j) := fun z => hperk z j
  have hψp : UnforcedLeray.Cyl.IsPeriodic d ψ := fun z => hψ.periodic z
  have hrep : kerVel d ψ x j =
      ∫ y in B0579.cell d, kerD d y j • ψ (x - y) := by
    have h := UnforcedLeray.Cyl.integral_cell_mul_comp_sub (c := d) hd0 hkp hψp x
    unfold kerVel
    rw [cell_eq_Cyl' d]
    refine Eq.trans ?_ h
    congr 1
    funext y
    simp only [smul_eq_mul]
    ring
  have hmeas : MeasurableSet (B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) :=
    (B0579.measurableSet_cell d).inter Metric.isOpen_ball.measurableSet
  have hmeasd : MeasurableSet (B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1) :=
    (B0579.measurableSet_cell d).diff Metric.isOpen_ball.measurableSet
  have hstrip : MeasurableSet ((fun y : ℝ × ℝ => y.2) ⁻¹' Icc (x.2 - R) (x.2 + R)) :=
    measurableSet_Icc.preimage measurable_snd
  -- near part: the sum of the components of the kernel on the ball
  have h1 : ∫⁻ y in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
      ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal M := by
    calc ∫⁻ y in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ
        ≤ ∫⁻ y in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            (∑ j', ‖kerD d y j'‖ₑ) * ENNReal.ofReal M := by
          refine setLIntegral_mono' hmeas fun y _ => ?_
          have hk : ‖kerD d y j‖ₑ ≤ ∑ j', ‖kerD d y j'‖ₑ :=
            Finset.single_le_sum (f := fun j' => ‖kerD d y j'‖ₑ) (fun _ _ => by positivity)
              (Finset.mem_univ j)
          have hψ' : ‖ψ (x - y)‖ₑ ≤ ENNReal.ofReal M := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hMb _)
          gcongr
      _ = (∫⁻ y in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j', ‖kerD d y j'‖ₑ) *
            ENNReal.ofReal M := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal M := by
          gcongr
  -- far part: outside the ball, only the strip `|x.2 - y.2| ≤ R` contributes
  have h2 : ∫⁻ y in B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1,
      ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ ≤
        (ENNReal.ofReal C * ENNReal.ofReal M) * (ENNReal.ofReal d * ENNReal.ofReal (2 * R)) := by
    calc ∫⁻ y in B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ
        ≤ ∫⁻ y in B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1,
            ((fun y : ℝ × ℝ => y.2) ⁻¹' Icc (x.2 - R) (x.2 + R)).indicator
              (fun _ => ENNReal.ofReal C * ENNReal.ofReal M) y := by
          refine setLIntegral_mono' hmeasd fun y hy => ?_
          by_cases hs : y ∈ (fun y : ℝ × ℝ => y.2) ⁻¹' Icc (x.2 - R) (x.2 + R)
          · rw [indicator_of_mem hs]
            have hk : ‖kerD d y j‖ₑ ≤ ENNReal.ofReal C := by
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (hfar y hy.1 hy.2 j)
            have hψ' : ‖ψ (x - y)‖ₑ ≤ ENNReal.ofReal M := by
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (hMb _)
            gcongr
          · rw [indicator_of_notMem hs]
            have hlt : R < |(x - y).2| := by
              rw [Prod.snd_sub, lt_abs]
              simp only [mem_preimage, mem_Icc, not_and_or, not_le] at hs
              rcases hs with h | h
              · left; linarith
              · right; linarith
            rw [hRb (x - y) hlt]
            simp
      _ = ENNReal.ofReal C * ENNReal.ofReal M *
            volume ((fun y : ℝ × ℝ => y.2) ⁻¹' Icc (x.2 - R) (x.2 + R) ∩
              (B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1)) := by
          rw [lintegral_indicator_const hstrip, Measure.restrict_apply hstrip]
      _ ≤ (ENNReal.ofReal C * ENNReal.ofReal M) * (ENNReal.ofReal d * ENNReal.ofReal (2 * R)) := by
          rw [← vol_strip d R x.2]
          gcongr
          intro y hy
          exact ⟨hy.2.1.1, hy.1⟩
  -- combine the two regions
  have hnorm : ‖kerVel d ψ x j‖ₑ ≤
      ENNReal.ofReal (M * C + M * C * (d * (2 * R))) := by
    rw [hrep]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp only [enorm_smul]
    calc ∫⁻ y in B0579.cell d, ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ
        = ∫⁻ y in (B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) ∪
            (B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1), ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ := by
          rw [Set.inter_union_diff]
      _ ≤ (∫⁻ y in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ) +
            ∫⁻ y in B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d y j‖ₑ * ‖ψ (x - y)‖ₑ :=
          lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal M +
            (ENNReal.ofReal C * ENNReal.ofReal M) * (ENNReal.ofReal d * ENNReal.ofReal (2 * R)) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (M * C + M * C * (d * (2 * R))) := by
          rw [ENNReal.ofReal_add hMC (mul_nonneg hMC (mul_nonneg hd0.le (by linarith))),
            ENNReal.ofReal_mul hMC, ENNReal.ofReal_mul hM0, ENNReal.ofReal_mul hd0.le]
          ring
  have hfin := (ENNReal.ofReal_le_ofReal_iff hB0).1
    (by rw [← Real.enorm_eq_ofReal_abs]; exact hnorm)
  exact hfin

end UnforcedLeray.Short.IIIa
