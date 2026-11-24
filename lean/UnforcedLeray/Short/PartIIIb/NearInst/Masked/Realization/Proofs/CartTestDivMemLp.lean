import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.ChartConj

/-!
# `CartTestDivMemLp` (source 1655-1665)

The divergence of a smooth, `P`-periodic, spatially bounded Cartesian tensor is in `L²(dx dτ)` over
one period.  The outer field `M(x, τ) = T(τ, ε⁻¹ x)` has entries that are smooth in `(x, τ)`; its
divergence is continuous (partial derivatives of a `C^∞` function) and vanishes once `‖x‖ > ε r`,
where `r` bounds the spatial support of `T`.  So it is continuous with compact support on
`B(0, ε r) × [0, P]`, which contains the period, and `B0226.memLp_of_continuous_of_ae_vanish` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The partial derivative of `x ↦ F(R x, τ)` in the direction `v`. -/
theorem cdm_partial (F : Space × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (R τ : ℝ) (x v : Space) :
    fderiv ℝ (fun x' : Space => F (R • x', τ)) x v = fderiv ℝ F (R • x, τ) (R • v, 0) := by
  have h1 : HasFDerivAt (fun x' : Space => (R • x', τ))
      ((R • ContinuousLinearMap.id ℝ Space).prod 0) x :=
    ((hasFDerivAt_id x).const_smul R).prodMk (hasFDerivAt_const τ x)
  have h2 := ((hF.differentiable (by simp)) (R • x, τ)).hasFDerivAt.comp x h1
  rw [show (fun x' : Space => F (R • x', τ)) = F ∘ (fun x' : Space => (R • x', τ)) from rfl,
    h2.fderiv]
  simp

/-- Continuity of the partial derivative `(x, τ) ↦ DF(R x, τ)(v, 0)`. -/
theorem cdm_cont_partial (F : Space × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (v : Space) :
    Continuous (fun y : Space × ℝ => fderiv ℝ F (R • y.1, y.2) (R • v, 0)) := by
  have hd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hm1 : Continuous (fun y : Space × ℝ => R • y.1) := continuous_fst.const_smul R
  have hm : Continuous (fun y : Space × ℝ => (R • y.1, y.2)) := hm1.prodMk continuous_snd
  exact (hd.comp hm).clm_apply continuous_const

/-- **The divergence of a smooth Cartesian tensor is in `L²(dx dτ)`** (source 1655-1665). -/
theorem cartTestDivMemLp : CartTestDivMemLp := by
  intro ε c P hε hc hP T hT
  obtain ⟨r, hr⟩ := hT.bounded
  have : Fact (0 < P) := ⟨by rw [hP]; positivity⟩
  -- the entries of the outer field vanish for `‖x‖ > ε r`
  have hpt : ∀ (i j : Fin 3) (x' : Space) (τ : ℝ), ε * r < ‖x'‖ → T τ (ε⁻¹ • x') i j = 0 := by
    intro i j x' τ hx'
    by_contra hne
    have hTne : T τ (ε⁻¹ • x') ≠ 0 := by
      intro h
      apply hne
      rw [h]
      simp
    have hb := hr τ (ε⁻¹ • x') hTne
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)] at hb
    rw [inv_mul_le_iff₀ hε] at hb
    linarith
  have hderiv0 : ∀ (i j : Fin 3) (x : Space) (τ : ℝ), ε * r < ‖x‖ →
      fderiv ℝ (fun x' : Space => outerField ε⁻¹ T (x', τ) i j) x = 0 := by
    intro i j x τ hx
    have hev : (fun x' : Space => outerField ε⁻¹ T (x', τ) i j) =ᶠ[𝓝 x]
        fun _ => (0 : ℝ) := by
      filter_upwards [(continuous_norm.tendsto x).eventually (lt_mem_nhds hx)] with x' hx'
      exact hpt i j x' τ hx'
    rw [hev.fderiv_eq]
    simp
  -- the divergence vanishes outside the ball `‖x‖ ≤ ε r`
  have hfar : ∀ y : Space × ℝ, ε * r < ‖y.1‖ → cartDiv (outerField ε⁻¹ T) y = 0 := by
    intro y hy
    have hz : ∀ i j : Fin 3,
        fderiv ℝ (fun x : Space => outerField ε⁻¹ T (x, y.2) i j) y.1 = 0 :=
      fun i j => hderiv0 i j y.1 y.2 hy
    ext i
    simp [cartDiv, hz]
  -- continuity of the divergence
  have hcont : Continuous (cartDiv (outerField ε⁻¹ T)) := by
    have hDc : ∀ i j : Fin 3, Continuous fun y : Space × ℝ =>
        fderiv ℝ (fun x : Space => outerField ε⁻¹ T (x, y.2) i j) y.1
          (UnforcedLeray.coordinateVector j) := by
      intro i j
      exact (cdm_cont_partial (fun y : Space × ℝ => T y.2 y.1 i j) (hT.smooth i j) ε⁻¹
        (UnforcedLeray.coordinateVector j)).congr fun y =>
          (cdm_partial (fun y : Space × ℝ => T y.2 y.1 i j) (hT.smooth i j) ε⁻¹ y.2 y.1
            (UnforcedLeray.coordinateVector j)).symm
    have hcomp : Continuous (fun y : Space × ℝ => fun i : Fin 3 =>
        ∑ j : Fin 3, fderiv ℝ (fun x : Space => outerField ε⁻¹ T (x, y.2) i j) y.1
          (UnforcedLeray.coordinateVector j)) :=
      continuous_pi fun i => continuous_finsetSum _ fun j _ => hDc i j
    exact (PiLp.continuous_toLp _ _).comp hcomp
  -- the support set and the period
  have hAc : IsCompact (Metric.closedBall (0 : Space) (ε * r) ×ˢ Icc (0 : ℝ) P) :=
    (isCompact_closedBall 0 (ε * r)).prod isCompact_Icc
  have hS : MeasurableSet ((univ : Set Space) ×ˢ Ioc (0 : ℝ) P) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  rw [UnforcedLeray.B0223.physMeasure_eq hP]
  refine UnforcedLeray.B0226.memLp_of_continuous_of_ae_vanish hcont hAc ?_ ?_ 2
  · rw [Measure.restrict_apply hAc.isClosed.measurableSet]
    exact ((measure_mono Set.inter_subset_left).trans_lt hAc.measure_lt_top).ne
  · refine ae_restrict_of_forall_mem hS fun y hy hyA => ?_
    apply hfar y
    by_contra hle
    push_neg at hle
    exact hyA ⟨mem_closedBall_zero_iff.2 hle, Ioc_subset_Icc_self hy.2⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
