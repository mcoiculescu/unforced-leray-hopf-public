import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.WPart

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 UnforcedLeray.B0223 N05_4Aux N05_4_1Aux

namespace SHH

structure WD (c : ℝ) (j : Fin 2) (u dq : Profile → MeridC) : Prop where
  mu : Measurable u
  mdq : Measurable dq
  pu : QPeriodic c u
  pdq : QPeriodic c dq
  lu : MemLp u 2 (cellMeasure c)
  ldq : MemLp dq 2 (cellMeasure c)
  weak : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (dq p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (u p) (pdSpatial j φ p) ∂(cellMeasure c)

theorem measurable_test {c : ℝ} {φ : Profile → MeridC} (hφ : IsMeridTest c φ) : Measurable φ :=
  hφ.smooth.continuous.measurable

theorem key_identity {c : ℝ} (hc : 0 < c) {j : Fin 2} {u dq : Profile → MeridC}
    (hd : WD c j u dq) {h : ℝ} (hh0 : 0 < h) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (u (sj j h p) - u p) (φ p) ∂(cellMeasure c) =
      ∫ p, inner ℂ (Wd j h dq p) (φ p) ∂(cellMeasure c) := by
  set μ := cellMeasure c with hμ
  have hgT : IsMeridTest c (pdSpatial j φ) := isMeridTest_pdSpatial hφ j
  have hφL : MemLp φ 2 μ := memLp_of_isMeridTest_cellMeasure hc hφ
  have hφ' : ∀ t, IsMeridTest c (fun p => φ (sj j t p)) := fun t => isMeridTest_comp_sj hφ j t
  have hgL : ∀ t, MemLp (fun p => pdSpatial j φ (sj j t p)) 2 μ := fun t =>
    memLp_of_isMeridTest_cellMeasure hc (isMeridTest_comp_sj hgT j t)
  have huS : ∀ t, MemLp (fun p => u (sj j t p)) 2 μ := fun t => memLp_comp_sj hc j t hd.mu hd.pu hd.lu
  have hdS : ∀ t, MemLp (fun p => dq (sj j t p)) 2 μ := fun t =>
    memLp_comp_sj hc j t hd.mdq hd.pdq hd.ldq
  -- Step 1
  have hA : ∫ p, inner ℂ (u (sj j h p)) (φ p) ∂μ = ∫ p, inner ℂ (u p) (φ (sj j (-h) p)) ∂μ := by
    have := integral_sj_eq hc j h
      (G := fun p => inner ℂ (u p) (φ (sj j (-h) p)))
      (hd.mu.inner (measurable_test (hφ' (-h))))
      (fun p => by simp only [hd.pu p, (hφ' (-h)).periodic p])
    simp only [sj_neg_sj] at this
    exact this
  have hI1 : Integrable (fun p => inner ℂ (u (sj j h p)) (φ p)) μ :=
    integrable_inner_cellMeasure (huS h) hφL
  have hI2 : Integrable (fun p => inner ℂ (u p) (φ p)) μ :=
    integrable_inner_cellMeasure hd.lu hφL
  have hI3 : Integrable (fun p => inner ℂ (u p) (φ (sj j (-h) p))) μ :=
    integrable_inner_cellMeasure hd.lu (memLp_of_isMeridTest_cellMeasure hc (hφ' (-h)))
  have hL1 : ∫ p, inner ℂ (u (sj j h p) - u p) (φ p) ∂μ =
      ∫ p, inner ℂ (u p) (φ (sj j (-h) p) - φ p) ∂μ := by
    simp_rw [inner_sub_left, inner_sub_right]
    rw [integral_sub hI1 hI2, integral_sub hI3 hI2, hA]
  -- Step 2
  have hpt : ∀ p, inner ℂ (u p) (φ (sj j (-h) p) - φ p) =
      -∫ t in Ioc (0 : ℝ) h, inner ℂ (u p) (pdSpatial j φ (sj j (-t) p)) := by
    intro p
    rw [ftc_sj j hφ.smooth h p, intervalIntegral.integral_of_le hh0.le, inner_neg_right]
    congr 1
    have hint : Integrable (fun t : ℝ => pdSpatial j φ (sj j (-t) p))
        (volume.restrict (Ioc (0 : ℝ) h)) := by
      have : Continuous fun t : ℝ => pdSpatial j φ (sj j (-t) p) :=
        hgT.smooth.continuous.comp (by unfold sj; fun_prop)
      exact this.integrableOn_Ioc
    exact (integral_inner (𝕜 := ℂ) hint (u p)).symm
  -- Step 3 : Fubini for F1
  set F1 : ℝ → Profile → ℂ := fun t p => inner ℂ (u p) (pdSpatial j φ (sj j (-t) p)) with hF1
  have hF1m : Measurable (fun tp : ℝ × Profile => F1 tp.1 tp.2) := by
    refine (hd.mu.comp measurable_snd).inner ?_
    exact (measurable_test hgT).comp ((measurable_sj_uncurry j).comp
      ((measurable_fst.neg).prodMk measurable_snd))
  have hswap1 := fubini_swap (c := c) (h := h) F1 hF1m
    (fun t _ => integrable_inner_cellMeasure hd.lu (hgL (-t)))
    (((∫ p, ‖u p‖ ^ 2 ∂μ) + ∫ p, ‖pdSpatial j φ p‖ ^ 2 ∂μ) / 2)
    (fun t _ => by
      refine (int_norm_inner_le hd.lu (hgL (-t))).trans (le_of_eq ?_)
      rw [integral_sq_comp_sj hc j (-t) (measurable_test hgT) hgT.periodic])
  -- Step 4
  have hstep4 : ∀ t ∈ Ioc (0 : ℝ) h, ∫ p, F1 t p ∂μ =
      -∫ p, inner ℂ (dq (sj j t p)) (φ p) ∂μ := by
    intro t _
    have hw := hd.weak _ (hφ' (-t))
    simp_rw [pdSpatial_comp_sj] at hw
    have hs := integral_sj_eq hc j t
      (G := fun p => inner ℂ (dq p) (φ (sj j (-t) p)))
      (hd.mdq.inner (measurable_test (hφ' (-t))))
      (fun p => by simp only [hd.pdq p, (hφ' (-t)).periodic p])
    simp only [sj_neg_sj] at hs
    have : ∫ p, F1 t p ∂μ = -∫ p, inner ℂ (dq p) (φ (sj j (-t) p)) ∂μ := by
      rw [hw, neg_neg]
    rw [this, hs]
  -- Step 5: Fubini for F2
  set F2 : ℝ → Profile → ℂ := fun t p => inner ℂ (dq (sj j t p)) (φ p) with hF2
  have hF2m : Measurable (fun tp : ℝ × Profile => F2 tp.1 tp.2) := by
    refine (hd.mdq.comp (measurable_sj_uncurry j)).inner ?_
    exact (measurable_test hφ).comp measurable_snd
  have hswap2 := fubini_swap (c := c) (h := h) F2 hF2m
    (fun t _ => integrable_inner_cellMeasure (hdS t) hφL)
    (((∫ p, ‖dq p‖ ^ 2 ∂μ) + ∫ p, ‖φ p‖ ^ 2 ∂μ) / 2)
    (fun t _ => by
      refine (int_norm_inner_le (hdS t) hφL).trans (le_of_eq ?_)
      rw [integral_sq_comp_sj hc j t hd.mdq hd.pdq])
  -- assemble
  have hchain : ∫ p, inner ℂ (u p) (φ (sj j (-h) p) - φ p) ∂μ =
      ∫ p, (∫ t in Ioc (0 : ℝ) h, F2 t p) ∂μ := by
    simp_rw [hpt]
    rw [integral_neg, ← hswap1, ← hswap2]
    have : ∫ t in Ioc (0 : ℝ) h, ∫ p, F1 t p ∂μ =
        -∫ t in Ioc (0 : ℝ) h, ∫ p, F2 t p ∂μ := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      exact hstep4 t ht
    rw [this, neg_neg]
  rw [hL1, hchain]
  refine integral_congr_ae ?_
  filter_upwards [ae_good hc j (h := h) hd.mdq hd.pdq hd.ldq] with p hp
  exact integral_inner_right (good_bound hh0 hd.mdq p hp).1 (φ p)

end SHH
end UnforcedLeray.Short.PartIIa
