import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.CylEnergy

/-!
# Uniform continuity at the start age of free cylinder flows (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2960-2970 (continuity of the free
cylinder flow in the start age).  For a cylinder test `g` vanishing near the cell boundary lines,
`φ = per(g ⟨x⟩^{2m})` is again a cylinder test, so the weak formulation tested against `φ` computes
the `X_{m,c}` pairing `⟨ω(σ), g⟩`; with the energy bound this gives
`‖ω(σ) - g‖² ≤ (e^{2K(σ-s)} - 1)‖g‖² + 2M(σ - s)` uniformly in the start age `s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa.RelB4locAux

/-- The weighted test `per(g · ⟨x⟩^{2m})`. -/
def wTest (c m : ℝ) (g : B0579.Plane → ℝ) : B0579.Plane → ℝ :=
  cellPer c (fun x => g x * B0579.jb x ^ m)

theorem contDiff_jb_rpow (m : ℝ) : ContDiff ℝ ∞ (fun x : B0579.Plane => B0579.jb x ^ m) := by
  have h : ContDiff ℝ ∞ (fun x : B0579.Plane => B0579.jb x) := by
    unfold B0579.jb; fun_prop
  exact h.rpow_const_of_ne (fun x => (B0579.jb_pos x).ne')

theorem isCylTest_wTest {c m η : ℝ} (hc : 0 < c) (hη : 0 < η) (hηc : η < c)
    {g : B0579.Plane → ℝ} (hg : B0579.IsCylTest c g)
    (hvan : ∀ x : B0579.Plane, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → g x = 0) :
    B0579.IsCylTest c (wTest c m g) := by
  obtain ⟨R, hR⟩ := hg.band
  exact isCylTest_cellPer hc hη hηc (hg.smooth.mul (contDiff_jb_rpow m))
    (fun x h1 h2 => by simp [hvan x h1 h2]) (R := R) (fun x hx => by simp [hR x hx])

theorem wTest_of_mem {c m : ℝ} (hc : 0 < c) (g : B0579.Plane → ℝ) {x : B0579.Plane}
    (hx : x ∈ B0579.cell c) : wTest c m g x = g x * (B0579.density m x : ℝ) := by
  rw [wTest, cellPer_of_mem hc _ hx, B0579.coe_density]

theorem integrableOn_sq_density {c m : ℝ} {f : B0579.Plane → ℝ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    IntegrableOn (fun x => f x ^ 2 * (B0579.density m x : ℝ)) (B0579.cell c) := by
  have h1 : Integrable (fun x => f x ^ 2) (B0579.cellMeasure c m) :=
    (memLp_two_iff_integrable_sq hf.1).1 hf
  rw [B0579.integrable_cellMeasure_iff] at h1
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  ring

theorem cylEnergy_sub_expand {c m : ℝ} {f g : B0579.Plane → ℝ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    cylEnergy c m (fun x => f x - g x) =
      cylEnergy c m f - 2 * (∫ x in B0579.cell c, f x * g x * (B0579.density m x : ℝ)) +
        cylEnergy c m g := by
  have hf2 := integrableOn_sq_density hf
  have hg2 := integrableOn_sq_density hg
  have hfm : AEStronglyMeasurable f (volume.restrict (B0579.cell c)) :=
    hf.1.mono_ac (B0579.ac_cellMeasure c m)
  have hgm : AEStronglyMeasurable g (volume.restrict (B0579.cell c)) :=
    hg.1.mono_ac (B0579.ac_cellMeasure c m)
  have hρm : AEStronglyMeasurable (fun x : B0579.Plane => (B0579.density m x : ℝ))
      (volume.restrict (B0579.cell c)) :=
    (NNReal.continuous_coe.comp (B0579.continuous_density m)).aestronglyMeasurable
  have hfg : IntegrableOn (fun x => f x * g x * (B0579.density m x : ℝ)) (B0579.cell c) := by
    refine Integrable.mono' ((hf2.add hg2).div_const 2) ((hfm.mul hgm).mul hρm)
      (Eventually.of_forall fun x => ?_)
    have hρ : 0 ≤ (B0579.density m x : ℝ) := NNReal.coe_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ, abs_mul]
    have : 2 * (|f x| * |g x|) ≤ f x ^ 2 + g x ^ 2 := by
      nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
    simp only [Pi.add_apply]
    nlinarith
  unfold cylEnergy
  have hpt : ∀ x, (f x - g x) ^ 2 * (B0579.density m x : ℝ) =
      (f x ^ 2 * (B0579.density m x : ℝ) - 2 * (f x * g x * (B0579.density m x : ℝ))) +
        g x ^ 2 * (B0579.density m x : ℝ) := fun x => by ring
  simp_rw [hpt]
  have h1 : ∫ x in B0579.cell c, ((f x ^ 2 * (B0579.density m x : ℝ) -
        2 * (f x * g x * (B0579.density m x : ℝ))) + g x ^ 2 * (B0579.density m x : ℝ)) =
      (∫ x in B0579.cell c, (f x ^ 2 * (B0579.density m x : ℝ) -
        2 * (f x * g x * (B0579.density m x : ℝ)))) +
        ∫ x in B0579.cell c, g x ^ 2 * (B0579.density m x : ℝ) :=
    integral_add (hf2.sub (hfg.const_mul 2)) hg2
  have h2 : ∫ x in B0579.cell c, (f x ^ 2 * (B0579.density m x : ℝ) -
        2 * (f x * g x * (B0579.density m x : ℝ))) =
      (∫ x in B0579.cell c, f x ^ 2 * (B0579.density m x : ℝ)) -
        ∫ x in B0579.cell c, 2 * (f x * g x * (B0579.density m x : ℝ)) :=
    integral_sub hf2 (hfg.const_mul 2)
  rw [h1, h2, integral_const_mul]

/-- **Uniform start continuity** of free cylinder flows from a fixed cylinder test vanishing near the
cell boundary (weak-strong argument). -/
theorem start_cont_bound {m ν c T : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T)
    {g : B0579.Plane → ℝ} (hg : B0579.IsCylTest c g) {η : ℝ} (hη : 0 < η) (hηc : η < c)
    (hvan : ∀ x : B0579.Plane, c / 2 - η < |x.1| → |x.1| ≤ c / 2 → g x = 0) :
    ∃ K M : ℝ, 0 < K ∧ 0 ≤ M ∧ ∀ s σ : ℝ, 0 ≤ s → s ≤ σ → σ ≤ T →
      ∀ G : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s g G →
        eLpNorm (G σ - g) 2 (B0579.cellMeasure c m) ≤
          ENNReal.ofReal (Real.sqrt ((Real.exp (2 * K * (σ - s)) - 1) * cylEnergy c m g +
            2 * (σ - s) * M)) := by
  obtain ⟨K, hK, hE⟩ := weak_energy hm hν hc hbu hT
  obtain ⟨V, hV0, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu hT
  set φ := wTest c m g with hφ_def
  have hφ : B0579.IsCylTest c φ := isCylTest_wTest hc hη hηc hg hvan
  -- bands and bounds of the derivatives of `φ`
  obtain ⟨R₀, hR₀⟩ := (hφ.pd 0).band
  obtain ⟨R₁, hR₁⟩ := (hφ.pd 1).band
  obtain ⟨R₀₀, hR₀₀⟩ := ((hφ.pd 0).pd 0).band
  obtain ⟨R₁₁, hR₁₁⟩ := ((hφ.pd 1).pd 1).band
  set R := max (max R₀ R₁) (max R₀₀ R₁₁) with hR_def
  have hlap_cont : Continuous (lapP φ) :=
    ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
  obtain ⟨L, hL⟩ := B0579.exists_bound_cell_band c R hlap_cont
  obtain ⟨P₀, hP₀⟩ := B0579.exists_bound_cell_band c R (hφ.pd 0).continuous
  obtain ⟨P₁, hP₁⟩ := B0579.exists_bound_cell_band c R (hφ.pd 1).continuous
  set C₁ := ν * max L 0 + V * max P₀ 0 + V * max P₁ 0 with hC₁_def
  have hC₁ : 0 ≤ C₁ := by positivity
  set B : Set B0579.Plane := {x | |x.2| ≤ R} with hB_def
  have hBm : MeasurableSet B := measurableSet_le (by fun_prop) measurable_const
  set vB := (volume.restrict (B0579.cell c) B).toReal with hvB_def
  have hvB : 0 ≤ vB := ENNReal.toReal_nonneg
  set Eg := cylEnergy c m g
  have hEg : 0 ≤ Eg := t22_energy_nonneg c m g
  set M := C₁ / 2 * (Real.exp (2 * K * T) * Eg + vB) with hM_def
  have hM0 : 0 ≤ M := by positivity
  refine ⟨K, M, hK, hM0, fun s σ hs hsσ hσT G hG => ?_⟩
  have hgm : MemLp g 2 (B0579.cellMeasure c m) := hg.memLp m
  have hGσ : MemLp (G σ) 2 (B0579.cellMeasure c m) := hG.memX σ hsσ
  -- the pointwise bound of the tested right-hand side
  have hBint : IntegrableOn (B.indicator (fun _ => (1 : ℝ))) (B0579.cell c) := by
    refine (integrable_indicator_iff hBm).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hBm]
    refine (lt_of_le_of_lt (measure_mono ?_) (((isCompact_Icc (a := -(c / 2)) (b := c / 2)).prod
      (isCompact_Icc (a := -R) (b := R))).measure_lt_top)).ne
    intro x hx
    simp only [B0579.cell, mem_inter_iff, mem_prod, mem_Ico, mem_univ, and_true, hB_def,
      mem_setOf_eq] at hx
    exact ⟨⟨hx.2.1, hx.2.2.le⟩, abs_le.1 hx.1⟩
  have hJ : ∀ r, s ≤ r → r ≤ T →
      ‖∫ x in B0579.cell c, cylFreeIntegrand tr (G r) r φ x‖ ≤
        C₁ / 2 * (cylEnergy c m (G r) + vB) := by
    intro r hsr hrT
    have hr0 : r ∈ Icc (0 : ℝ) T := ⟨hs.trans hsr, hrT⟩
    have hGr := integrableOn_sq_density (hG.memX r hsr)
    have hbound : ∀ x ∈ B0579.cell c, ‖cylFreeIntegrand tr (G r) r φ x‖ ≤
        C₁ / 2 * (G r x ^ 2 * (B0579.density m x : ℝ) + B.indicator (fun _ => (1 : ℝ)) x) := by
      intro x hx
      have hρ1 : 1 ≤ (B0579.density m x : ℝ) := by
        rw [B0579.coe_density]
        exact Real.one_le_rpow (by unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2])
          (by linarith)
      by_cases hxB : |x.2| ≤ R
      · have hind : B.indicator (fun _ => (1 : ℝ)) x = 1 := by
          rw [indicator_of_mem (show x ∈ B from hxB)]
        rw [hind]
        have hψ : |ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)|
            ≤ C₁ := by
          have h1 := hL x hx hxB
          have h2 := hP₀ x hx hxB
          have h3 := hP₁ x hx hxB
          have hv0 := (hV r hr0 x 0).1
          have hv1 := (hV r hr0 x 1).1
          calc _ ≤ |ν * lapP φ x| + (|tr.v r x 0 * B0579.pd 0 φ x| +
                  |tr.v r x 1 * B0579.pd 1 φ x|) :=
                (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
            _ = ν * |lapP φ x| + (|tr.v r x 0| * |B0579.pd 0 φ x| +
                  |tr.v r x 1| * |B0579.pd 1 φ x|) := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_pos hν]
            _ ≤ ν * max L 0 + (V * max P₀ 0 + V * max P₁ 0) := by
                gcongr
                · exact h1.trans (le_max_left _ _)
                · exact h2.trans (le_max_left _ _)
                · exact h3.trans (le_max_left _ _)
            _ = C₁ := by rw [hC₁_def]; ring
        rw [cylFreeIntegrand, Real.norm_eq_abs, abs_mul]
        have h2 : 2 * |G r x| ≤ G r x ^ 2 * (B0579.density m x : ℝ) + 1 := by
          nlinarith [sq_nonneg (|G r x| - 1), sq_abs (G r x), sq_nonneg (G r x)]
        calc |G r x| * _ ≤ |G r x| * C₁ := mul_le_mul_of_nonneg_left hψ (abs_nonneg _)
          _ ≤ C₁ / 2 * (G r x ^ 2 * (B0579.density m x : ℝ) + 1) := by nlinarith
      · have hxR : R < |x.2| := lt_of_not_ge hxB
        have e0 : B0579.pd 0 φ x = 0 := hR₀ x (lt_of_le_of_lt (by
          simp only [hR_def]; exact (le_max_left _ _).trans (le_max_left _ _)) hxR)
        have e1 : B0579.pd 1 φ x = 0 := hR₁ x (lt_of_le_of_lt (by
          simp only [hR_def]; exact (le_max_right _ _).trans (le_max_left _ _)) hxR)
        have e00 : B0579.pd 0 (B0579.pd 0 φ) x = 0 := hR₀₀ x (lt_of_le_of_lt (by
          simp only [hR_def]; exact (le_max_left _ _).trans (le_max_right _ _)) hxR)
        have e11 : B0579.pd 1 (B0579.pd 1 φ) x = 0 := hR₁₁ x (lt_of_le_of_lt (by
          simp only [hR_def]; exact (le_max_right _ _).trans (le_max_right _ _)) hxR)
        have hz : cylFreeIntegrand tr (G r) r φ x = 0 := by
          simp only [cylFreeIntegrand, lapP, e0, e1, e00, e11]; ring
        rw [hz, norm_zero]
        have : 0 ≤ G r x ^ 2 * (B0579.density m x : ℝ) + B.indicator (fun _ => (1 : ℝ)) x :=
          add_nonneg (mul_nonneg (sq_nonneg _) (NNReal.coe_nonneg _))
            (indicator_nonneg (fun _ _ => zero_le_one) _)
        positivity
    have hle := norm_integral_le_of_norm_le ((hGr.add hBint).const_mul (C₁ / 2))
      ((ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall hbound))
    refine hle.trans (le_of_eq ?_)
    have h1 : ∫ x in B0579.cell c, (G r x ^ 2 * (B0579.density m x : ℝ) +
          B.indicator (fun _ => (1 : ℝ)) x) =
        (∫ x in B0579.cell c, G r x ^ 2 * (B0579.density m x : ℝ)) +
          ∫ x in B0579.cell c, B.indicator (fun _ => (1 : ℝ)) x :=
      integral_add hGr hBint
    simp only [Pi.add_apply]
    rw [integral_const_mul, h1]
    congr 2
    exact integral_indicator_one hBm
  -- the weak formulation tested against `φ`
  have hweak := hG.weak φ hφ σ hsσ
  have hpair : ∫ x in B0579.cell c, G σ x * φ x =
      ∫ x in B0579.cell c, G σ x * g x * (B0579.density m x : ℝ) := by
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x hx => ?_)
    simp only [hφ_def, wTest_of_mem hc g hx]; ring
  have hgg : ∫ x in B0579.cell c, g x * φ x = Eg := by
    refine (setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x hx => ?_)).trans rfl
    simp only [hφ_def, wTest_of_mem hc g hx]; ring
  set I := ∫ r in s..σ, ∫ x in B0579.cell c, cylFreeIntegrand tr (G r) r φ x with hI_def
  have hI : |I| ≤ M * (σ - s) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := σ) (C := M)
      (f := fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (G r) r φ x) (fun r hr => by
        rw [uIoc_of_le hsσ] at hr
        refine (hJ r hr.1.le (hr.2.trans hσT)).trans ?_
        rw [hM_def]
        gcongr
        refine (hE s r hs hr.1.le (hr.2.trans hσT) g hg G hG).trans ?_
        gcongr
        nlinarith [hr.1, hr.2])
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hsσ)] at this
  have hEσ := hE s σ hs hsσ hσT g hg G hG
  have hexp := cylEnergy_sub_expand hGσ hgm
  have hen : cylEnergy c m (fun x => G σ x - g x) ≤
      (Real.exp (2 * K * (σ - s)) - 1) * Eg + 2 * (σ - s) * M := by
    have key : cylEnergy c m (fun x => G σ x - g x) = cylEnergy c m (G σ) - Eg - 2 * I := by
      linarith [hexp, hpair, hweak, hgg]
    have e1 : (Real.exp (2 * K * (σ - s)) - 1) * Eg = Real.exp (2 * K * (σ - s)) * Eg - Eg := by
      ring
    have e2 : 2 * (σ - s) * M = 2 * (M * (σ - s)) := by ring
    have := neg_abs_le I
    linarith
  rw [eLpNorm_eq_sqrt_energy (hGσ.sub hgm)]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hen)

end UnforcedLeray.Short.IIIa.RelB4locAux
