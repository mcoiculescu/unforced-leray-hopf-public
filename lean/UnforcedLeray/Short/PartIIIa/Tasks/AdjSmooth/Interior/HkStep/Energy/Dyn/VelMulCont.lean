import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Dominated convergence in `L²`: `‖d_k φ‖_{L²} → 0` when `d_k → 0` a.e., `|d_k| ≤ K`. -/
theorem eLpNorm_mul_tendsto_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : Type*}
    {l : Filter κ} [l.IsCountablyGenerated] {φ : α → ℂ} (hφ : MemLp φ 2 μ)
    {d : κ → α → ℂ} {K : ℝ} (hmeas : ∀ᶠ k in l, AEStronglyMeasurable (d k) μ)
    (hbd : ∀ᶠ k in l, ∀ᵐ x ∂μ, ‖d k x‖ ≤ K)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => d k x) l (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => d k x * φ x) 2 μ) l (𝓝 0) := by
  have hrw : ∀ g : α → ℂ, eLpNorm g 2 μ = (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := by
    intro g
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
    norm_num
  have hfin : ∫⁻ x, ‖φ x‖ₑ ^ (2:ℝ) ∂μ < ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (p := 2)
      (by norm_num) (by simp)).1 hφ.eLpNorm_lt_top
    simpa using h
  have hdct : Tendsto (fun k => ∫⁻ x, ‖d k x * φ x‖ₑ ^ (2:ℝ) ∂μ) l (𝓝 0) := by
    have hmeasF : ∀ᶠ k in l, AEMeasurable (fun x => ‖d k x * φ x‖ₑ ^ (2:ℝ)) μ :=
      hmeas.mono fun k hk =>
        (AEMeasurable.pow_const ((hk.mul hφ.1).enorm) (2:ℝ))
    have hbdF : ∀ᶠ k in l, ∀ᵐ x ∂μ, ‖d k x * φ x‖ₑ ^ (2:ℝ) ≤
        ENNReal.ofReal K ^ (2:ℝ) * ‖φ x‖ₑ ^ (2:ℝ) := by
      refine hbd.mono fun k hk => ?_
      filter_upwards [hk] with x hx
      have h1 : ‖d k x * φ x‖ₑ ≤ ENNReal.ofReal K * ‖φ x‖ₑ := by
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal hx
      calc ‖d k x * φ x‖ₑ ^ (2:ℝ) ≤ (ENNReal.ofReal K * ‖φ x‖ₑ) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal K ^ (2:ℝ) * ‖φ x‖ₑ ^ (2:ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    have hfinB : ∫⁻ x, ENNReal.ofReal K ^ (2:ℝ) * ‖φ x‖ₑ ^ (2:ℝ) ∂μ ≠ ∞ := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        ENNReal.ofReal_ne_top)]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        ENNReal.ofReal_ne_top) hfin.ne
    have hlimF : ∀ᵐ x ∂μ, Tendsto (fun k => ‖d k x * φ x‖ₑ ^ (2:ℝ)) l (𝓝 ((fun _ => (0:ℝ≥0∞)) x)) := by
      filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun k => d k x * φ x) l (𝓝 0) := by
        simpa using hx.mul_const (φ x)
      have h2 : Tendsto (fun k => ‖d k x * φ x‖ₑ) l (𝓝 ‖(0:ℂ)‖ₑ) :=
        (continuous_enorm.tendsto (0:ℂ)).comp h1
      rw [enorm_zero] at h2
      have h3 := (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto 0 |>.comp h2
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using h3
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := l)
      (F := fun k x => ‖d k x * φ x‖ₑ ^ (2:ℝ)) (f := fun _ => (0:ℝ≥0∞))
      (fun x => ENNReal.ofReal K ^ (2:ℝ) * ‖φ x‖ₑ ^ (2:ℝ)) hmeasF hbdF hfinB hlimF
    simpa using this
  have hfun := ((ENNReal.continuous_rpow_const (y := 1 / (2:ℝ))).tendsto 0).comp hdct
  simp only [Function.comp_def] at hfun
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hfun
  simpa [hrw] using hfun

set_option maxHeartbeats 1600000 in
/-- **(C2) `r ↦ v_l(r) φ(r)` is continuous into `X_{-m,c}` on `(a, b)`.** -/
theorem velMulCont (m : ℝ) : UnforcedLeray.Short.IIIa.VelMulCont m := by
  unfold VelMulCont
  intro ν tr t s g φ a b χ hctx r hr l
  obtain ⟨hν, hν1, hLad, ht0, hts, hA, hT, hta, hab, hbs, hchi⟩ := hctx
  have hr0 : 0 ≤ r := le_trans ht0 (le_trans hta hr.1.le)
  have hsub : Ioo a b ⊆ Icc t s := fun x hx => ⟨le_trans hta hx.1.le, le_trans hx.2.le hbs.le⟩
  have hrI : r ∈ Icc t s := hsub hr
  obtain ⟨C, hC⟩ := hLad s (le_trans ht0 hts.le)
  have hsm : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hyr : ∀ ρ : ℝ, 0 ≤ ρ → Continuous (fun y : ℝ × ℝ => tr.v ρ y l) := by
    intro ρ hρ
    have hcont : Continuous (fun y : ℝ × ℝ => tr.v ρ y) :=
      hsm.comp_continuous (f := fun y : ℝ × ℝ => (ρ, y)) (by fun_prop)
        (fun y => ⟨hρ, mem_univ _⟩)
    exact (continuous_apply l).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).comp hcont)
  have hFc : Continuous (fun w : EuclideanSpace ℝ (Fin 2) => ((w l : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply l).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)))
  have htc : ∀ y : ℝ × ℝ, Tendsto (fun r' => ((tr.v r' y l : ℝ) : ℂ)) (𝓝[Ioo a b] r)
      (𝓝 ((tr.v r y l : ℝ) : ℂ)) := by
    intro y
    have h1 : ContinuousWithinAt (fun r' : ℝ => ((r', y) : ℝ × (ℝ × ℝ))) (Ioo a b) r :=
      continuousWithinAt_id.prodMk continuousWithinAt_const
    have h2 : ContinuousWithinAt (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) (r, y) :=
      hsm.continuousWithinAt ⟨hr0, mem_univ _⟩
    have h3 : ContinuousWithinAt (fun r' : ℝ => tr.v r' y) (Ioo a b) r :=
      ContinuousWithinAt.comp (f := fun r' : ℝ => ((r', y) : ℝ × (ℝ × ℝ))) (x := r) h2 h1
        (fun x hx => ⟨le_trans ht0 (le_trans hta hx.1.le), mem_univ _⟩)
    exact hFc.continuousAt.comp_continuousWithinAt h3
  have hvb : ∀ ρ ∈ Ioo a b, ∀ y ∈ B0579.cell (ν ^ (-2 : ℝ)),
      |tr.v ρ y l| ≤ |C| := by
    intro ρ hρ y hy
    have hρs : ρ ∈ Icc (0 : ℝ) s :=
      ⟨le_trans ht0 (le_trans hta hρ.1.le), le_trans hρ.2.le hbs.le⟩
    exact (hC ρ hρs y hy).1 l |>.trans (le_abs_self C)
  have hae : ∀ᵐ y ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)), y ∈ B0579.cell (ν ^ (-2 : ℝ)) :=
    (B0579.cellMeasure_ac _ _).ae_le (ae_restrict_mem (B0579.measurableSet_cell _))
  -- the `L²` dominated convergence for the velocity increment
  have hBt : Tendsto (fun r' => eLpNorm (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y)
      2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) (𝓝[Ioo a b] r) (𝓝 0) := by
    refine eLpNorm_mul_tendsto_zero (φ := φ r) (K := 2 * |C|) (hA.memX r hrI) ?_ ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun r' hr' =>
        (Complex.continuous_ofReal.comp ((hyr r' (le_trans ht0 (le_trans hta hr'.1.le))).sub
          (hyr r hr0))).aestronglyMeasurable
    · refine eventually_nhdsWithin_of_forall fun r' hr' => ?_
      filter_upwards [hae] with y hy
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 := hvb r' hr' y hy
      have h2 := hvb r hr y hy
      rw [abs_le]
      constructor <;> linarith [abs_le.1 h1, abs_le.1 h2]
    · filter_upwards [hae] with y hy
      have := ((htc y).sub_const ((tr.v r y l : ℝ) : ℂ))
      simp only [sub_self] at this
      simpa [Complex.ofReal_sub] using this
  have hsc : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r)) (𝓝[Ioo a b] r)
      (𝓝 0) :=
    (hA.strongCont r hrI).mono_left (nhdsWithin_mono r hsub)
  have hAt : Tendsto (fun r' => ‖((|C| : ℝ) : ℂ)‖ₑ * xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r))
      (𝓝[Ioo a b] r) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hsc (Or.inr (enorm_ne_top (x := ((|C| : ℝ) : ℂ))))
    simpa using this
  have hsum : Tendsto (fun r' =>
      ‖((|C| : ℝ) : ℂ)‖ₑ * xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r) +
        eLpNorm (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) (𝓝[Ioo a b] r) (𝓝 0) := by
    simpa using hAt.add hBt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (eventually_nhdsWithin_of_forall fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _))
    (eventually_nhdsWithin_of_forall fun r' hr' => ?_)
  have hr'I : r' ∈ Icc t s := hsub hr'
  have hdec : (fun y => ((tr.v r' y l : ℝ) : ℂ) * φ r' y) - (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y)
      = (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y)) +
        (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply]
    push_cast
    ring
  have hAm : AEStronglyMeasurable (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y))
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (Complex.continuous_ofReal.comp (hyr r' (le_trans ht0 (le_trans hta hr'.1.le)))).aestronglyMeasurable.mul
      ((hA.memX r' hr'I).1.sub (hA.memX r hrI).1)
  have hBm : AEStronglyMeasurable (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y)
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (Complex.continuous_ofReal.comp ((hyr r' (le_trans ht0 (le_trans hta hr'.1.le))).sub
      (hyr r hr0))).aestronglyMeasurable.mul (hA.memX r hrI).1
  have hAbound : eLpNorm (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y)) 2
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      ‖((|C| : ℝ) : ℂ)‖ₑ * xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r) := by
    unfold xNorm
    rw [← eLpNorm_const_smul ((|C| : ℝ) : ℂ) (φ r' - φ r) 2]
    refine eLpNorm_mono_ae ?_
    filter_upwards [hae] with y hy
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right (hvb r' hr' y hy) (norm_nonneg _)
  rw [xNorm, hdec]
  calc eLpNorm ((fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y)) +
          (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y)) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
      ≤ eLpNorm (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y)) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) +
        eLpNorm (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
        eLpNorm_add_le hAm hBm (by norm_num)
    _ ≤ ‖((|C| : ℝ) : ℂ)‖ₑ * xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r) +
        eLpNorm (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := add_le_add hAbound le_rfl

end UnforcedLeray.Short.IIIa
