import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Sep

/-!
# Slice estimates on a compact cylinder block (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The compact block `[0,c] × [-N,N]`. -/
def hj3Block (c : ℝ) (N : ℝ) : Set (ℝ × ℝ) := Icc 0 c ×ˢ Icc (-N) N

theorem hj3Block_compact (c N : ℝ) : IsCompact (hj3Block c N) :=
  isCompact_Icc.prod isCompact_Icc

theorem hj3Block_meas (c N : ℝ) : MeasurableSet (hj3Block c N) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- The pointwise integrand `⟨B(x), ∇ψ(x)⟩` on the slice. -/
def hj3H (B : ℝ × ℝ → UnforcedLeray.B0223.MeridC) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  B x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) + B x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)

theorem hj3_coord_aesm {μ : Measure (ℝ × ℝ)} {B : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (hB : AEStronglyMeasurable B μ) (j : Fin 2) :
    AEStronglyMeasurable (fun x => B x j) μ :=
  (EuclideanSpace.proj j : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hB

theorem hj3_slice_integrable {c N : ℝ} {μ : Measure (ℝ × ℝ)} {B : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (hB : AEStronglyMeasurable B μ)
    (hBi : IntegrableOn (fun x => ‖B x‖) (hj3Block c N) μ)
    {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    IntegrableOn (hj3H B ψ) (hj3Block c N) μ := by
  obtain ⟨M0, hM0⟩ := (hj3Block_compact c N).exists_bound_of_continuousOn
    (f := fun x => ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hj3_pd_continuous hψ 0)).continuousOn
  obtain ⟨M1, hM1⟩ := (hj3Block_compact c N).exists_bound_of_continuousOn
    (f := fun x => ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hj3_pd_continuous hψ 1)).continuousOn
  have hmeas : AEStronglyMeasurable (hj3H B ψ) (μ.restrict (hj3Block c N)) := by
    refine (((hj3_coord_aesm hB 0).restrict).mul
      (Complex.continuous_ofReal.comp (hj3_pd_continuous hψ 0)).aestronglyMeasurable).add
      (((hj3_coord_aesm hB 1).restrict).mul
      (Complex.continuous_ofReal.comp (hj3_pd_continuous hψ 1)).aestronglyMeasurable)
  refine Integrable.mono' (hBi.const_mul (2 * (|M0| + |M1|))) hmeas ?_
  filter_upwards [ae_restrict_mem (hj3Block_compact c N).isClosed.measurableSet] with x hx
  have h0 := hM0 x hx
  have h1 := hM1 x hx
  have hn0 : ‖B x 0‖ ≤ ‖B x‖ := PiLp.norm_apply_le (B x) 0
  have hn1 : ‖B x 1‖ ≤ ‖B x‖ := PiLp.norm_apply_le (B x) 1
  simp only [Complex.norm_real] at h0 h1
  unfold hj3H
  calc ‖B x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) + B x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)‖
      ≤ ‖B x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ)‖ + ‖B x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ = ‖B x 0‖ * ‖(UnforcedLeray.B0579.pd 0 ψ x : ℝ)‖ + ‖B x 1‖ * ‖(UnforcedLeray.B0579.pd 1 ψ x : ℝ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    _ ≤ ‖B x‖ * (|M0| + |M1|) + ‖B x‖ * (|M0| + |M1|) := by
        have hp0 : ‖(UnforcedLeray.B0579.pd 0 ψ x : ℝ)‖ ≤ |M0| + |M1| :=
          h0.trans (le_trans (le_abs_self M0) (by linarith [abs_nonneg M1]))
        have hp1 : ‖(UnforcedLeray.B0579.pd 1 ψ x : ℝ)‖ ≤ |M0| + |M1| :=
          h1.trans (le_trans (le_abs_self M1) (by linarith [abs_nonneg M0]))
        exact add_le_add (mul_le_mul hn0 hp0 (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hn1 hp1 (norm_nonneg _) (norm_nonneg _))
    _ = 2 * (|M0| + |M1|) * ‖B x‖ := by ring

theorem hj3_strip_to_block {c N : ℝ} {B : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    {ψ : ℝ × ℝ → ℝ} (hvan : ∀ x : ℝ × ℝ, N < |x.2| → ψ x = 0) :
    ∫ x in stripSet c, hj3H B ψ x = ∫ x in hj3Block c N, hj3H B ψ x ∂(volume.restrict (stripSet c)) := by
  rw [← integral_indicator (hj3Block_meas c N)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with x hx
  by_cases hK : x ∈ hj3Block c N
  · rw [indicator_of_mem hK]
  · rw [indicator_of_notMem hK]
    have hfar : N < |x.2| := by
      by_contra hle
      push_neg at hle
      exact hK ⟨⟨hx.1.1.le, hx.1.2⟩, abs_le.1 hle⟩
    have h0 := hj3_pd_eq_zero_of_far (fun y hy => hvan y hy) 0 x hfar
    have h1 := hj3_pd_eq_zero_of_far (fun y hy => hvan y hy) 1 x hfar
    unfold hj3H
    rw [h0, h1]
    simp

theorem hj3_slice_diff {c N ε : ℝ} {B : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    {μ : Measure (ℝ × ℝ)} (hBi : IntegrableOn (fun x => ‖B x‖) (hj3Block c N) μ)
    (hBm : AEStronglyMeasurable B μ)
    {ψ φ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ)
    (hφ : UnforcedLeray.B0579.IsCylTest c φ)
    (hε : ∀ x ∈ hj3Block c N,
      dist ((UnforcedLeray.B0579.pd 0 ψ x, UnforcedLeray.B0579.pd 1 ψ x) : ℝ × ℝ)
        ((UnforcedLeray.B0579.pd 0 φ x, UnforcedLeray.B0579.pd 1 φ x) : ℝ × ℝ) < ε) :
    ‖∫ x in hj3Block c N, hj3H B ψ x ∂μ - ∫ x in hj3Block c N, hj3H B φ x ∂μ‖ ≤
      2 * ε * ∫ x in hj3Block c N, ‖B x‖ ∂μ := by
  rw [← integral_sub (hj3_slice_integrable hBm hBi hψ) (hj3_slice_integrable hBm hBi hφ)]
  have hbound : ∀ᵐ x ∂(μ.restrict (hj3Block c N)),
      ‖hj3H B ψ x - hj3H B φ x‖ ≤ 2 * ε * ‖B x‖ := by
    filter_upwards [ae_restrict_mem (hj3Block_compact c N).isClosed.measurableSet] with x hx
    have hd := hε x hx
    rw [Prod.dist_eq] at hd
    have hd0 : |UnforcedLeray.B0579.pd 0 ψ x - UnforcedLeray.B0579.pd 0 φ x| < ε := by
      rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) hd
    have hd1 : |UnforcedLeray.B0579.pd 1 ψ x - UnforcedLeray.B0579.pd 1 φ x| < ε := by
      rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) hd
    have hn0 : ‖B x 0‖ ≤ ‖B x‖ := PiLp.norm_apply_le (B x) 0
    have hn1 : ‖B x 1‖ ≤ ‖B x‖ := PiLp.norm_apply_le (B x) 1
    have hrw : hj3H B ψ x - hj3H B φ x =
        B x 0 * ((UnforcedLeray.B0579.pd 0 ψ x - UnforcedLeray.B0579.pd 0 φ x : ℝ) : ℂ) +
          B x 1 * ((UnforcedLeray.B0579.pd 1 ψ x - UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ) := by
      unfold hj3H; push_cast; ring
    rw [hrw]
    have e0 : ‖((UnforcedLeray.B0579.pd 0 ψ x - UnforcedLeray.B0579.pd 0 φ x : ℝ) : ℂ)‖ ≤ ε := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hd0.le
    have e1 : ‖((UnforcedLeray.B0579.pd 1 ψ x - UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)‖ ≤ ε := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hd1.le
    calc ‖B x 0 * ((UnforcedLeray.B0579.pd 0 ψ x - UnforcedLeray.B0579.pd 0 φ x : ℝ) : ℂ) +
          B x 1 * ((UnforcedLeray.B0579.pd 1 ψ x - UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)‖
        ≤ ‖B x 0 * ((UnforcedLeray.B0579.pd 0 ψ x - UnforcedLeray.B0579.pd 0 φ x : ℝ) : ℂ)‖ +
          ‖B x 1 * ((UnforcedLeray.B0579.pd 1 ψ x - UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = ‖B x 0‖ * ‖((UnforcedLeray.B0579.pd 0 ψ x - UnforcedLeray.B0579.pd 0 φ x : ℝ) : ℂ)‖ +
          ‖B x 1‖ * ‖((UnforcedLeray.B0579.pd 1 ψ x - UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖B x‖ * ε + ‖B x‖ * ε :=
          add_le_add (mul_le_mul hn0 e0 (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul hn1 e1 (norm_nonneg _) (norm_nonneg _))
      _ = 2 * ε * ‖B x‖ := by ring
  have hint2 : Integrable (fun x => 2 * ε * ‖B x‖) (μ.restrict (hj3Block c N)) :=
    hBi.const_mul _
  have key := norm_integral_le_of_norm_le hint2 hbound
  rw [integral_const_mul] at key
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
