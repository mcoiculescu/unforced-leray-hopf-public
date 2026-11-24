import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarOutCellPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ChartQEtaPull
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# `FarOutChartQ` (source 2713-2721, 2666-2689, 5345-5352)

Tonelli in `(s, η, q)` on the cell, `L^∞_q` of the coefficient against `L²_q` of `v`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace FarOutChartQAux

instance sfin_avg (c : ℝ) : SFinite (UnforcedLeray.Cyl.avgμ c) := by
  unfold UnforcedLeray.Cyl.avgμ
  infer_instance

theorem avg_eq (c : ℝ) :
    UnforcedLeray.Cyl.avgμ c = ENNReal.ofReal c⁻¹ •
      (volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume : Measure ℝ) := by
  have h : (volume.restrict (Ico (-(c / 2)) (c / 2))).prod ((volume : Measure ℝ).restrict univ) =
      ((volume : Measure ℝ).prod volume).restrict (Ico (-(c / 2)) (c / 2) ×ˢ univ) :=
    Measure.prod_restrict _ _
  rw [Measure.restrict_univ, ← Measure.volume_eq_prod] at h
  rw [h]
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
  rw [neg_div]

theorem slice {c : ℝ} {P : Chart → Prop} (hc : 0 < c) (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ η : ℝ,
      ∀ᵐ q ∂(volume.restrict (Ico (-(c / 2)) (c / 2))), P (s, (q, η)) := by
  unfold ageμ at h
  have h1 := Measure.ae_ae_of_ae_prod h
  have hab : (volume.restrict (Ioi (0 : ℝ))) ≪
      ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) := by
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow _).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs _)).ne'
  have h2 : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), P (s, z) :=
    hab.ae_le h1
  filter_upwards [h2] with s hs
  rw [avg_eq] at hs
  replace hs := (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne').ae_le hs
  exact UnforcedLeray.Short.PartIIIb.Concrete.ChartQEtaPull.ae_slices
    (P := fun z => P (s, z)) hs

theorem cell_split (c : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (qCell c) =
      (volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume : Measure ℝ) := by
  have h : (volume.restrict (Ico (-(c / 2)) (c / 2))).prod ((volume : Measure ℝ).restrict univ) =
      ((volume : Measure ℝ).prod volume).restrict (Ico (-(c / 2)) (c / 2) ×ˢ univ) :=
    Measure.prod_restrict _ _
  rw [Measure.restrict_univ, ← Measure.volume_eq_prod] at h
  rw [h]
  unfold qCell
  rw [neg_div]

theorem lint_cell {c : ℝ} {G : ℝ × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z in qCell c, G z =
      ∫⁻ η : ℝ, ∫⁻ q in Ico (-(c / 2)) (c / 2), G (q, η) := by
  rw [cell_split]
  exact lintegral_prod_symm _ hG.aemeasurable

theorem ofReal_sq_eq (W a' : ℝ) (hW : 0 ≤ W) (ha : 0 ≤ a') :
    ENNReal.ofReal (W ^ 2 * a' ^ 2) = (ENNReal.ofReal W * ENNReal.ofReal a') ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ← ENNReal.ofReal_mul hW, ← ENNReal.ofReal_pow (mul_nonneg hW ha)]
  congr 1; ring

end FarOutChartQAux

open FarOutChartQAux in
theorem farOutChartQ : FarOutChartQ := by
  intro R c ν μ δ S mZ hR hc hS a v f H κ₀ hk Φ hHm hvm hH hv hΦ
  set nu : Measure ℝ := volume.restrict (Ico (-(c / 2)) (c / 2)) with hnu
  have hW0 : ∀ p : Chart, 0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := fun p => by
    unfold UnforcedLeray.Short.IIIa.transWeight
    exact Real.rpow_nonneg (by positivity) _
  have hcinv : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.2 hc.le
  -- slices
  have hH' := slice hc hH
  have hv' : ∀ᵐ p ∂(ageμ c (-1 / 2)), v p = NearInst.Masked.farOut R c ν μ δ S f p :=
    (UnforcedLeray.Short.PartIIIb.NearInst.ageμ_absCont c (-1 / 2) (-3 / 2)).ae_le hv
  have hv'' := slice hc hv'
  -- the iterated form
  have hF : Measurable fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * H p :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (measurable_fst.pow_const _))).mul hHm
  rw [lintegral_ageμ hc (-1 / 2) hHm]
  have hprod : (volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ qCell c) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (qCell c)) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.prod_restrict]
  rw [hprod, lintegral_prod _ hF.aemeasurable]
  -- the s-wise bound
  set E : ℝ → ℝ≥0∞ := fun s => UnforcedLeray.Short.IIIa.etaL2QSup c mZ a s with hE
  have hcore : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ z in qCell c, ENNReal.ofReal (c⁻¹ * (s, z).1 ^ (-1 / 2 : ℝ)) * H (s, z) ≤
        2 * κ₀ * (if s < S then ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * E s ^ (2 : ℝ) *
          Φ s ^ (2 : ℝ) else 0) := by
    filter_upwards [hH', hv'', ae_restrict_mem measurableSet_Ioi] with s hHs hvs hs
    have hs : (0 : ℝ) < s := hs
    have hHs' : ∀ᵐ η : ℝ, ∀ᵐ q ∂nu, ENNReal.ofReal c⁻¹ * H (s, (q, η)) ≤
        κ₀ * (essSup (fun q => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) *
            ‖a (s, (q, η))‖ₑ) nu ^ (2 : ℝ)) *
          (ENNReal.ofReal c⁻¹ * ‖v (s, (q, η))‖ₑ ^ (2 : ℝ)) := by
      filter_upwards [hHs] with η hη
      filter_upwards [hη, ENNReal.ae_le_essSup (μ := nu)
        (fun q => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) *
            ‖a (s, (q, η))‖ₑ)] with q hq hq2
      have hA : ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) ^ 2 *
          ‖a (s, (q, η))‖ ^ 2) =
          (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) *
            ‖a (s, (q, η))‖ₑ) ^ (2 : ℝ) := by
        rw [ofReal_sq_eq _ _ (hW0 _) (norm_nonneg _), ofReal_norm_eq_enorm]
      rw [hA] at hq
      have hq3 := ENNReal.rpow_le_rpow hq2 (show (0 : ℝ) ≤ 2 by norm_num)
      calc ENNReal.ofReal c⁻¹ * H (s, (q, η))
          ≤ ENNReal.ofReal c⁻¹ * (κ₀ * ((ENNReal.ofReal
              (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) *
                ‖a (s, (q, η))‖ₑ) ^ (2 : ℝ) * ‖v (s, (q, η))‖ₑ ^ (2 : ℝ))) := by gcongr
        _ = κ₀ * (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) *
                ‖a (s, (q, η))‖ₑ) ^ (2 : ℝ) *
              (ENNReal.ofReal c⁻¹ * ‖v (s, (q, η))‖ₑ ^ (2 : ℝ)) := by ring
        _ ≤ _ := by gcongr
    have hK : ∀ᵐ η : ℝ, ∫⁻ q, ENNReal.ofReal c⁻¹ * ‖v (s, (q, η))‖ₑ ^ (2 : ℝ) ∂nu ≤
        (if s < S then ENNReal.ofReal (2 * s⁻¹) * Φ s ^ (2 : ℝ) else 0) := by
      filter_upwards [hvs] with η hη
      have hcongr : ∫⁻ q, ENNReal.ofReal c⁻¹ * ‖v (s, (q, η))‖ₑ ^ (2 : ℝ) ∂nu =
          ∫⁻ q, ENNReal.ofReal c⁻¹ *
            ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ) ∂nu := by
        refine lintegral_congr_ae ?_
        filter_upwards [hη] with q hq
        rw [hq]
      rw [hcongr]
      refine (farOutCellPhase R c ν μ δ S hR hc f s η hs).trans ?_
      split_ifs with hsS
      · gcongr
        exact hΦ (s, (0, η)) hs hsS
      · exact le_rfl
    have hmeasH : Measurable fun x : ℝ × ℝ => ENNReal.ofReal c⁻¹ * H (s, (x.1, x.2)) :=
      measurable_const.mul (hHm.comp measurable_prodMk_left)
    have hmeasW : Measurable fun x : ℝ × ℝ => ENNReal.ofReal c⁻¹ * ‖v (s, (x.1, x.2))‖ₑ ^ (2 : ℝ) :=
      measurable_const.mul (((hvm.comp measurable_prodMk_left).enorm).pow_const _)
    have hwt : ∀ x : ℝ × ℝ, ENNReal.ofReal c⁻¹ * ‖v (s, (x.1, x.2))‖ₑ ^ (2 : ℝ) ≠ ⊤ := fun x =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
    have hpull := UnforcedLeray.Short.PartIIIb.Concrete.ChartQEtaPull.etaPull
      (ν := nu) (h := fun x : ℝ × ℝ => ENNReal.ofReal c⁻¹ * H (s, (x.1, x.2)))
      (w := fun x : ℝ × ℝ => ENNReal.ofReal c⁻¹ * ‖v (s, (x.1, x.2))‖ₑ ^ (2 : ℝ))
      (M := fun η => essSup (fun q => ENNReal.ofReal
          (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) * ‖a (s, (q, η))‖ₑ) nu ^ (2 : ℝ))
      (κ₀ := κ₀) (K := if s < S then ENNReal.ofReal (2 * s⁻¹) * Φ s ^ (2 : ℝ) else 0)
      hk hmeasH hmeasW hwt hHs' hK
    have hM : ∫⁻ η, essSup (fun q => ENNReal.ofReal
          (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η))) * ‖a (s, (q, η))‖ₑ) nu ^ (2 : ℝ)
        = E s ^ (2 : ℝ) := by
      simp only [hE, UnforcedLeray.Short.IIIa.etaL2QSup]
      rw [← ENNReal.rpow_mul]
      norm_num
      rfl
    rw [hM] at hpull
    have hm : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) * H (s, z) :=
      measurable_const.mul (hHm.comp measurable_prodMk_left)
    show ∫⁻ z in qCell c, ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) * H (s, z) ≤ _
    rw [lint_cell hm]
    have hsplit : ∀ z : ℝ × ℝ, ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) * H (s, z) =
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal c⁻¹ * H (s, z)) := fun z => by
      rw [ENNReal.ofReal_mul hcinv]; ring
    simp only [hsplit]
    have hin : ∀ η : ℝ, ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * H (s, (q, η))) = ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * H (s, (q, η)) := fun η =>
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    simp only [hin]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases hsS : s < S
    · simp only [if_pos hsS] at hpull ⊢
      have hrel : ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (2 * s⁻¹) =
          2 * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
        have : s ^ (-1 / 2 : ℝ) * (2 * s⁻¹) = 2 * s ^ (-3 / 2 : ℝ) := by
          rw [show (-3 / 2 : ℝ) = -1 / 2 + (-1) by norm_num, Real.rpow_add hs, Real.rpow_neg_one]
          ring
        rw [this, ENNReal.ofReal_mul (by norm_num)]
        simp
      calc ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
            ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * H (s, (q, η))
          ≤ ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
              (κ₀ * (ENNReal.ofReal (2 * s⁻¹) * Φ s ^ (2 : ℝ)) * E s ^ (2 : ℝ)) := by
            gcongr
        _ = (ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (2 * s⁻¹)) *
              (κ₀ * Φ s ^ (2 : ℝ) * E s ^ (2 : ℝ)) := by ring
        _ = _ := by rw [hrel]; ring
    · simp only [if_neg hsS] at hpull ⊢
      simp only [mul_zero, zero_mul, zero_le, nonpos_iff_eq_zero] at hpull ⊢
      rw [hpull, mul_zero]
  refine (lintegral_mono_ae hcore).trans ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) hk)]
  have hind : ∫⁻ s in Ioi (0 : ℝ), (if s < S then ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * E s ^ (2 : ℝ) *
          Φ s ^ (2 : ℝ) else 0) =
      ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * E s ^ (2 : ℝ) * Φ s ^ (2 : ℝ) := by
    have : (fun s : ℝ => if s < S then ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * E s ^ (2 : ℝ) *
          Φ s ^ (2 : ℝ) else 0) =
        (Iio S).indicator (fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * E s ^ (2 : ℝ) *
          Φ s ^ (2 : ℝ)) := by
      funext s; simp [Set.indicator_apply]
    rw [this, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Set.Ioi_inter_Iio]
  rw [hind]
