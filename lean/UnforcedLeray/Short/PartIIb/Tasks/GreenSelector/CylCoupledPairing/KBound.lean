import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.PlanarKernel
import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing.Norms

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CCP

open UnforcedLeray

/-- A measurable representative of `w` supported in the cell with norm control. -/
theorem exists_rep {c m : ℝ} (hm : 1 / 2 < m) (C1 : ℝ)
    (hC1 : ∀ w : B0579.X c m, eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal C1 * ‖w‖ₑ) (w : B0579.X c m) :
    ∃ g : B0579.Plane → ℝ, Measurable g ∧ Integrable g volume ∧
      (∀ x, x ∉ B0579.cell c → g x = 0) ∧
      (⇑w =ᵐ[volume.restrict (B0579.cell c)] g) ∧
      eLpNorm g 2 volume ≤ ‖w‖ₑ ∧
      eLpNorm g 1 volume ≤ ENNReal.ofReal C1 * ‖w‖ₑ := by
  have hw : AEStronglyMeasurable (⇑w) (volume.restrict (B0579.cell c)) :=
    (Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure c m)
  set g0 := hw.mk (⇑w) with hg0
  have hg0m : Measurable g0 := hw.stronglyMeasurable_mk.measurable
  have hae : ⇑w =ᵐ[volume.restrict (B0579.cell c)] g0 := hw.ae_eq_mk
  set g := (B0579.cell c).indicator g0 with hg
  have hgm : Measurable g := hg0m.indicator (B0579.measurableSet_cell c)
  have hnorm : ∀ p : ℝ≥0∞, eLpNorm g p volume = eLpNorm (⇑w) p (volume.restrict (B0579.cell c)) := by
    intro p
    rw [hg, eLpNorm_indicator_eq_eLpNorm_restrict (B0579.measurableSet_cell c)]
    exact (eLpNorm_congr_ae hae).symm
  have h2 : eLpNorm g 2 volume ≤ ‖w‖ₑ := by
    rw [hnorm]
    exact eLpNorm_two_le_Xmc (by linarith) w
  have h1 := hC1 w
  refine ⟨g, hgm, ?_, fun x hx => by simp [hg, hx], ?_, h2, by rw [hnorm]; exact h1⟩
  · rw [← memLp_one_iff_integrable]
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hnorm]
    exact h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by rw [Lp.enorm_def]; exact (Lp.memLp w).eLpNorm_lt_top))
  · have : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), g x = g0 x := by
      refine (ae_restrict_iff' (B0579.measurableSet_cell c)).mpr (Eventually.of_forall fun x hx => ?_)
      simp [hg, hx]
    exact hae.trans (this.mono fun x hx => hx.symm)

theorem K_eq_rep {c m : ℝ} (w : B0579.X c m) (g : B0579.Plane → ℝ)
    (hg : ⇑w =ᵐ[volume.restrict (B0579.cell c)] g) (x : B0579.Plane) :
    Cyl.K c (⇑w) x = Cyl.K c g x := by
  unfold Cyl.K
  rw [← b0579_cell_eq_cyl_cell]
  refine integral_congr_ae ?_
  filter_upwards [hg] with y hy
  rw [hy]

/-- The `K`-pairing bound on a strip. -/
theorem K_pair_bound {c : ℝ} (hc1 : 1 ≤ c) {m : ℝ} (hm : 1 / 2 < m) (R Gb : ℝ) (hR : 0 ≤ R) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ ψ : B0579.Plane → ℝ, (∀ x, |x.1| ≤ c / 2 → |ψ x| ≤ Gb) →
      (∀ x, R < |x.2| → ψ x = 0) → ∀ (w : B0579.X c m) (i : Fin 2),
      ∫⁻ x in B0579.cell c, ‖Cyl.K c (⇑w) x i * ψ x‖ₑ ≤ ENNReal.ofReal CK * ‖w‖ₑ := by
  obtain ⟨C1, hC1, hC1w⟩ := exists_L1_const c m hm
  set T0 : Set B0579.Plane := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R with hT0
  have hT0m : MeasurableSet T0 := (isClosed_Icc.prod isClosed_Icc).measurableSet
  have hT0fin : volume T0 < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  set W : B0579.Plane → ℝ := T0.indicator (fun _ => (1 : ℝ)) with hW
  have hWm : Measurable W := measurable_const.indicator hT0m
  have hWl2fin : eLpNorm W 2 volume < ⊤ := by
    rw [hW, eLpNorm_indicator_const hT0m (by norm_num) (by norm_num)]
    exact ENNReal.mul_lt_top (by simp) (ENNReal.rpow_lt_top_of_nonneg (by positivity) hT0fin.ne)
  set B : ℝ := max 1 (eLpNorm W 2 volume).toReal with hB
  have hB0 : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hWl2 : eLpNorm W 2 volume ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hWl2fin.ne]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hWnn : ∀ x, 0 ≤ W x := fun x => by simp only [hW]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hWsup : ∀ x, W x ≤ B := fun x => by
    simp only [hW]
    refine (Set.indicator_le_self' (fun _ _ => zero_le_one) x).trans ?_
    exact le_max_left _ _
  set e0 : ℝ := 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal with he0
  have he0nn : 0 ≤ e0 := by simp only [he0]; norm_num
  set V : ℝ≥0∞ := volume T0 ^ e0 with hV
  have hVfin : V < ⊤ := ENNReal.rpow_lt_top_of_nonneg he0nn hT0fin.ne
  set CKe : ℝ≥0∞ := ENNReal.ofReal Gb * V * (ENNReal.ofReal B *
    (ENNReal.ofReal cylSplitConst + ENNReal.ofReal 2 * ENNReal.ofReal C1)) with hCKe
  have hCKefin : CKe ≠ ⊤ := by
    simp only [hCKe]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin.ne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩))
  refine ⟨CKe.toReal, ENNReal.toReal_nonneg, fun ψ hψ1 hψ2 w i => ?_⟩
  rw [ENNReal.ofReal_toReal hCKefin]
  obtain ⟨g, hgm, hgi, hgs, hge, hg2, hg1⟩ := exists_rep hm C1 hC1w w
  have hKeq : ∀ x, Cyl.K c (⇑w) x = Cyl.K c g x := K_eq_rep w g hge
  set F : B0579.Plane → ℝ := fun x => W x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x
    with hF
  have key := eLpNorm_weighted_cyl_K_le hc1 hWm hWnn hB0 hWsup hWl2 hgm hgi
  have hFm : AEStronglyMeasurable F volume := by
    have h1 : AEStronglyMeasurable (fun x => ‖Cyl.K c g x‖) volume :=
      (aestronglyMeasurable_cyl_K c hgm).norm
    exact hWm.aestronglyMeasurable.mul (h1.indicator (B0579.measurableSet_cell c))
  have hpt : ∀ x ∈ B0579.cell c, ‖Cyl.K c (⇑w) x i * ψ x‖ₑ ≤ ENNReal.ofReal Gb * ‖F x‖ₑ := by
    intro x hx
    have hx1 : |x.1| ≤ c / 2 := abs_le.mpr ⟨hx.1.1, hx.1.2.le⟩
    by_cases hx2 : |x.2| ≤ R
    · have hxT : x ∈ T0 := ⟨abs_le.mp hx1, abs_le.mp hx2⟩
      have hFx : F x = ‖Cyl.K c g x‖ := by
        simp [hF, hW, hxT, hx]
      rw [hFx, hKeq x, enorm_mul, ← ofReal_norm (ψ x), mul_comm]
      gcongr
      · exact (Real.norm_eq_abs _ ▸ hψ1 x hx1)
      · rw [enorm_norm]
        exact enorm_le_iff_norm_le.mpr (by simpa using PiLp.norm_apply_le (Cyl.K c g x) i)
    · rw [hψ2 x (not_le.mp hx2)]
      simp
  have hsupp : F.support ⊆ T0 := by
    intro x hx
    by_contra hxT
    exact hx (by simp [hF, hW, hxT])
  have hF1 : eLpNorm F 1 volume ≤ eLpNorm F 2 volume * V := by
    calc eLpNorm F 1 volume = eLpNorm F 1 (volume.restrict T0) :=
          (eLpNorm_restrict_eq_of_support_subset hsupp).symm
      _ ≤ eLpNorm F 2 (volume.restrict T0) * (volume.restrict T0) Set.univ ^ e0 :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hFm.restrict
      _ ≤ eLpNorm F 2 volume * V := by
          rw [Measure.restrict_apply_univ]
          exact mul_le_mul_left (eLpNorm_restrict_le F 2 volume T0) _
  have hF2 : eLpNorm F 2 volume ≤ ENNReal.ofReal B *
      (ENNReal.ofReal cylSplitConst * ‖w‖ₑ + ENNReal.ofReal 2 * (ENNReal.ofReal C1 * ‖w‖ₑ)) :=
    key.trans (by gcongr)
  calc ∫⁻ x in B0579.cell c, ‖Cyl.K c (⇑w) x i * ψ x‖ₑ
      ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal Gb * ‖F x‖ₑ :=
        setLIntegral_mono' (B0579.measurableSet_cell c) hpt
    _ ≤ ∫⁻ x, ENNReal.ofReal Gb * ‖F x‖ₑ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal Gb * eLpNorm F 1 volume := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ENNReal.ofReal Gb * ((ENNReal.ofReal B *
      (ENNReal.ofReal cylSplitConst * ‖w‖ₑ + ENNReal.ofReal 2 * (ENNReal.ofReal C1 * ‖w‖ₑ))) * V) := by
        gcongr
        exact hF1.trans (by gcongr)
    _ = CKe * ‖w‖ₑ := by simp only [hCKe]; ring

end UnforcedLeray.Short.IIb.CCP
