import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelSmooth.LocInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelSmooth.Dir
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smoothness of the kernel convolution (helper for `kerVelSmooth`)

`kvsConv d l ψ x = ∫_{C_d} K_d(z)_l ψ(x - z) dz` is smooth in `x` for every cylinder test `ψ`,
and `fderiv (kvsConv ψ) x v = kvsConv (∂_v ψ) x`. The derivative falls on the test: the
integrands are dominated on `x + ball 1` by a constant times `|K_d|` restricted to a fixed
finite-measure strip of the cell (`kerD_cell_integrableOn`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The convolution `x ↦ ∫_{C_d} K_d(z)_l ψ(x - z) dz`. -/
def kvsConv (d : ℝ) (l : Fin 2) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ z in B0579.cell d, kerD d z l * ψ (x - z)

theorem kvs_meas {d : ℝ} (hd : 1 ≤ d) (l : Fin 2) : Measurable fun z => kerD d z l := by
  have hNF0 := kerNearFar
  unfold KerNearFar at hNF0
  obtain ⟨C, _, hNF⟩ := hNF0
  exact (hNF d hd).1 l

/-- The strip of the cell in which the integrands live. -/
def kvsBand (d T : ℝ) : Set (ℝ × ℝ) := Icc (-(d / 2)) (d / 2) ×ˢ Icc (-T) T

theorem kvsBand_compact (d T : ℝ) : IsCompact (kvsBand d T) :=
  isCompact_Icc.prod isCompact_Icc

theorem kvsBand_indicator_integrable {d : ℝ} (hd : 1 ≤ d) (l : Fin 2) (T : ℝ) :
    Integrable ((kvsBand d T).indicator (fun z => |kerD d z l|))
      (volume.restrict (B0579.cell d)) := by
  have hB : MeasurableSet (kvsBand d T) := (kvsBand_compact d T).isClosed.measurableSet
  have h2 := (kerD_cell_integrableOn hd l (kvsBand d T) hB
    (kvsBand_compact d T).measure_lt_top.ne).norm
  have h3 : IntegrableOn (fun z => |kerD d z l|) (B0579.cell d ∩ kvsBand d T) := by
    simp only [Real.norm_eq_abs] at h2
    exact h2
  have h1 : IntegrableOn (fun z => |kerD d z l|) (kvsBand d T ∩ B0579.cell d) := by
    rw [Set.inter_comm]
    exact h3
  refine (integrable_indicator_iff hB).2 ?_
  rw [IntegrableOn, Measure.restrict_restrict hB]
  exact h1

/-- The strip `kvsBand d T` contains `y - z` as soon as `y` is near `x` and `z` is in the strip,
and `y - z` stays in a fixed compact box. -/
def kvsBox (d : ℝ) (x : ℝ × ℝ) (T : ℝ) : Set (ℝ × ℝ) :=
  Icc (x.1 - 1 - d / 2) (x.1 + 1 + d / 2) ×ˢ Icc (-(|x.2| + 1 + T)) (|x.2| + 1 + T)

theorem kvsBox_compact (d : ℝ) (x : ℝ × ℝ) (T : ℝ) : IsCompact (kvsBox d x T) :=
  isCompact_Icc.prod isCompact_Icc

theorem kvs_mem_box {d T : ℝ} {x y z : ℝ × ℝ} (hy : y ∈ Metric.ball x 1)
    (hz : z ∈ kvsBand d T) : y - z ∈ kvsBox d x T := by
  have h1 : ‖(y - x).1‖ ≤ ‖y - x‖ := norm_fst_le (y - x)
  have h2 : ‖(y - x).2‖ ≤ ‖y - x‖ := norm_snd_le (y - x)
  have h3 : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
  rw [Real.norm_eq_abs] at h1 h2
  have hy1 : |y.1 - x.1| < 1 := by
    have := lt_of_le_of_lt h1 h3
    simpa [Prod.fst_sub] using this
  have hy2 : |y.2 - x.2| < 1 := by
    have := lt_of_le_of_lt h2 h3
    simpa [Prod.snd_sub] using this
  rw [abs_lt] at hy1 hy2
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz1a, hz1b⟩ := hz1
  obtain ⟨hz2a, hz2b⟩ := hz2
  have hx2a := neg_abs_le x.2
  have hx2b := le_abs_self x.2
  simp only [kvsBox, mem_prod, mem_Icc, Prod.fst_sub, Prod.snd_sub]
  refine ⟨⟨by linarith [hy1.1, hy1.2], by linarith [hy1.1, hy1.2]⟩,
    ⟨by linarith [hy2.1, hy2.2], by linarith [hy2.1, hy2.2]⟩⟩

/-- Outside the strip, the test and its derivative vanish at `y - z` for `y` near `x`. -/
theorem kvs_zero_outside {d R : ℝ} {ψ : ℝ × ℝ → ℝ}
    (hR : ∀ w : ℝ × ℝ, R < |w.2| → ψ w = 0) {x y z : ℝ × ℝ} (hy : y ∈ Metric.ball x 1)
    (hzc : z ∈ B0579.cell d) (hzB : z ∉ kvsBand d (R + |x.2| + 1)) :
    ψ (y - z) = 0 ∧ fderiv ℝ ψ (y - z) = 0 := by
  have h1 : ‖(y - x).2‖ ≤ ‖y - x‖ := norm_snd_le (y - x)
  have h3 : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
  rw [Real.norm_eq_abs] at h1
  have hyx : |y.2 - x.2| < 1 := by
    have := lt_of_le_of_lt h1 h3
    simpa [Prod.snd_sub] using this
  have hz2 : R + |x.2| + 1 < |z.2| := by
    by_contra hcon
    apply hzB
    refine ⟨Ico_subset_Icc_self hzc.1, ?_⟩
    exact abs_le.1 (not_lt.1 hcon)
  have hy2 : |y.2| ≤ |x.2| + 1 := by
    have := abs_sub_abs_le_abs_sub y.2 x.2
    linarith
  have h4 := abs_sub_abs_le_abs_sub z.2 y.2
  rw [abs_sub_comm z.2 y.2] at h4
  have hwR : R < |(y - z).2| := by
    rw [Prod.snd_sub]
    linarith
  exact ⟨hR _ hwR, kvsFderiv_eq_zero hR hwR⟩

/-- Continuity constants of `ψ` and `fderiv ψ` on the box. -/
theorem kvs_consts {d : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest d ψ)
    (x : ℝ × ℝ) (T : ℝ) :
    ∃ C0 C1 : ℝ, (∀ w ∈ kvsBox d x T, |ψ w| ≤ C0) ∧ (∀ w ∈ kvsBox d x T, ‖fderiv ℝ ψ w‖ ≤ C1) := by
  obtain ⟨C0, hC0⟩ := (kvsBox_compact d x T).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  obtain ⟨C1, hC1⟩ := (kvsBox_compact d x T).exists_bound_of_continuousOn
    (hψ.smooth.continuous_fderiv (by simp)).continuousOn
  refine ⟨max C0 0, max C1 0, fun w hw => ?_, fun w hw => ?_⟩
  · have := hC0 w hw
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · exact le_trans (hC1 w hw) (le_max_left _ _)

/-- Pointwise domination of the integrands for `y` in the unit ball around `x`. -/
theorem kvs_dom_pt {d : ℝ} {ψ : ℝ × ℝ → ℝ} (l : Fin 2) (x : ℝ × ℝ) (R : ℝ)
    (hR : ∀ w : ℝ × ℝ, R < |w.2| → ψ w = 0) {C0 C1 : ℝ}
    (hC0 : ∀ w ∈ kvsBox d x (R + |x.2| + 1), |ψ w| ≤ C0)
    (hC1 : ∀ w ∈ kvsBox d x (R + |x.2| + 1), ‖fderiv ℝ ψ w‖ ≤ C1)
    {y z : ℝ × ℝ} (hy : y ∈ Metric.ball x 1) (hz : z ∈ B0579.cell d) :
    ‖kerD d z l * ψ (y - z)‖ ≤
        C0 * (kvsBand d (R + |x.2| + 1)).indicator (fun z => |kerD d z l|) z ∧
      ‖kerD d z l • fderiv ℝ ψ (y - z)‖ ≤
        C1 * (kvsBand d (R + |x.2| + 1)).indicator (fun z => |kerD d z l|) z := by
  by_cases hzB : z ∈ kvsBand d (R + |x.2| + 1)
  · rw [indicator_of_mem hzB]
    have hm := kvs_mem_box hy hzB
    constructor
    · rw [Real.norm_eq_abs, abs_mul]
      calc |kerD d z l| * |ψ (y - z)| ≤ |kerD d z l| * C0 :=
            mul_le_mul_of_nonneg_left (hC0 _ hm) (abs_nonneg _)
        _ = C0 * |kerD d z l| := mul_comm _ _
    · rw [norm_smul, Real.norm_eq_abs]
      calc |kerD d z l| * ‖fderiv ℝ ψ (y - z)‖ ≤ |kerD d z l| * C1 :=
            mul_le_mul_of_nonneg_left (hC1 _ hm) (abs_nonneg _)
        _ = C1 * |kerD d z l| := mul_comm _ _
  · have hzero := kvs_zero_outside hR hy hz hzB
    rw [indicator_of_notMem hzB]
    constructor
    · rw [hzero.1]
      simp
    · rw [hzero.2]
      simp

/-- **Smoothness, derivative and integrability at one point.** -/
theorem kvs_main {d : ℝ} (hd : 1 ≤ d) {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest d ψ)
    (l : Fin 2) (x : ℝ × ℝ) :
    HasFDerivAt (kvsConv d l ψ) (∫ z in B0579.cell d, kerD d z l • fderiv ℝ ψ (x - z)) x ∧
      Integrable (fun z => kerD d z l • fderiv ℝ ψ (x - z)) (volume.restrict (B0579.cell d)) := by
  obtain ⟨R, hR⟩ := hψ.band
  obtain ⟨C0, C1, hC0, hC1⟩ := kvs_consts hψ x (R + |x.2| + 1)
  have hmeasK := kvs_meas hd l
  have hψc : Continuous ψ := hψ.continuous
  have hfc : Continuous (fun z => fderiv ℝ ψ (x - z)) :=
    (hψ.smooth.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)
  have hball : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x one_pos
  have hbound_int : Integrable
      (fun z => C1 * (kvsBand d (R + |x.2| + 1)).indicator (fun z => |kerD d z l|) z)
      (volume.restrict (B0579.cell d)) :=
    (kvsBand_indicator_integrable hd l _).const_mul C1
  have hbound0_int : Integrable
      (fun z => C0 * (kvsBand d (R + |x.2| + 1)).indicator (fun z => |kerD d z l|) z)
      (volume.restrict (B0579.cell d)) :=
    (kvsBand_indicator_integrable hd l _).const_mul C0
  have hint : Integrable (fun z => kerD d z l • fderiv ℝ ψ (x - z))
      (volume.restrict (B0579.cell d)) := by
    refine Integrable.mono' hbound_int ?_ ?_
    · exact (hmeasK.smul hfc.measurable).aestronglyMeasurable
    · refine (ae_restrict_mem (B0579.measurableSet_cell d)).mono fun z hz => ?_
      exact (kvs_dom_pt l x R hR hC0 hC1 (Metric.mem_ball_self one_pos) hz).2
  refine ⟨?_, hint⟩
  unfold kvsConv
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y z => kerD d z l * ψ (y - z))
    (F' := fun y z => kerD d z l • fderiv ℝ ψ (y - z))
    (bound := fun z => C1 * (kvsBand d (R + |x.2| + 1)).indicator (fun z => |kerD d z l|) z)
    hball ?_ ?_ ?_ ?_ hbound_int ?_
  · refine Eventually.of_forall fun y => ?_
    exact (hmeasK.mul ((hψc.comp (continuous_const.sub continuous_id)).measurable)).aestronglyMeasurable
  · refine Integrable.mono' hbound0_int ?_ ?_
    · exact (hmeasK.mul ((hψc.comp (continuous_const.sub continuous_id)).measurable)).aestronglyMeasurable
    · refine (ae_restrict_mem (B0579.measurableSet_cell d)).mono fun z hz => ?_
      exact (kvs_dom_pt l x R hR hC0 hC1 (Metric.mem_ball_self one_pos) hz).1
  · exact (hmeasK.smul hfc.measurable).aestronglyMeasurable
  · refine (ae_restrict_mem (B0579.measurableSet_cell d)).mono fun z hz y hy => ?_
    exact (kvs_dom_pt l x R hR hC0 hC1 hy hz).2
  · refine Eventually.of_forall fun z y _ => ?_
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ (y - z)) (y - z) :=
      (hψ.differentiable (y - z)).hasFDerivAt
    exact ((hasFDerivAt_comp_sub z).2 hψd).const_mul (kerD d z l)

theorem kvs_fderiv_apply {d : ℝ} (hd : 1 ≤ d) {ψ : ℝ × ℝ → ℝ}
    (hψ : UnforcedLeray.B0579.IsCylTest d ψ) (l : Fin 2) (x v : ℝ × ℝ) :
    fderiv ℝ (kvsConv d l ψ) x v = kvsConv d l (kvsDirDer ψ v) x := by
  rw [(kvs_main hd hψ l x).1.fderiv, ContinuousLinearMap.integral_apply (kvs_main hd hψ l x).2 v]
  unfold kvsConv kvsDirDer
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm]

/-- The convolution is smooth. -/
theorem kvs_contDiff {d : ℝ} (hd : 1 ≤ d) (l : Fin 2) (n : ℕ) :
    ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest d ψ → ContDiff ℝ n (kvsConv d l ψ) := by
  induction n with
  | zero =>
    intro ψ hψ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x => (kvs_main hd hψ l x).1.differentiableAt.continuousAt
  | succ n ih =>
    intro ψ hψ
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (kvs_main hd hψ l x).1.differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [contDiff_clm_apply_iff]
      intro v
      have hfun : (fun x => fderiv ℝ (kvsConv d l ψ) x v) = kvsConv d l (kvsDirDer ψ v) :=
        funext fun x => kvs_fderiv_apply hd hψ l x v
      rw [hfun]
      exact ih _ (kvsDirDer_isCylTest hψ v)

end UnforcedLeray.Short.IIIa
