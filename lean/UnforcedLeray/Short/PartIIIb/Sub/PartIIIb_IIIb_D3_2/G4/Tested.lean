import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.GBPoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.Majorant
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatSrcBdd
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.BclassAeBound
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.FpmInvBound

/-!
# `PartIII-b:IIIb-D3/2/G4/3`: tested source norm bound `flatTestedConj`

Source of record: `the November 2 reference manuscript`, lines 4475, 4665-4667.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF

theorem flatTestedConj (D : SeqData) : TestedConj D := by
  intro dm dp hst κ _ m _ _ S hS
  obtain ⟨Csrc, hCsrc⟩ := FlatSettingInst.flatSrcBdd m
  have hγ : 0 < D.Pl.eigenvalue.re := hst.gamma_pos
  obtain ⟨Cfpm, hCfpm⟩ := fpmInvBound D.Pl.eigenvalue D.Pl.kappa hγ
  set b : ℝ := D.Pl.eigenvalue.re / 3 - D.K.as with hb_def
  have hb : 0 < b := by
    have has : D.K.as < D.Pl.eigenvalue.re / 16 := hst.as_lt
    linarith
  have hm1_nonneg : 0 ≤ D.σ₀ / 2 := by
    have := hst.sigma_pos
    linarith
  obtain ⟨Cmaj, hCmaj⟩ := testedMajorant b hb (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hm1_nonneg
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hν_ev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds one_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hS.and (hmu_ev.and hν_ev))
  refine ⟨3 * |Csrc| * |Cfpm| * |Cmaj|, N, fun n hn z hz B hB => ?_⟩
  obtain ⟨⟨FI, hSn⟩, hmu_z, hν1⟩ := hN n hn
  have hmu : D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) := hmu_z z hz
  set ν : ℝ := nu D n with hν_def
  set μ : ℝ := D.mu n z with hμ_def
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hν_le : ν ≤ 1 := hν1.le
  have hbN : 0 ≤ bNorm D.K.as B := ENNReal.toReal_nonneg
  have hC_Sn : ∀ t ∈ Icc (0 : ℝ) (1.1 / ν),
      ‖(S n).Hper t‖ ≤ |Csrc| ∧ ‖(S n).conjX ((S n).Hper t)‖ ≤ |Csrc| ∧ ‖(S n).Rper t‖ ≤ |Csrc| := by
    intro t ht
    obtain ⟨hH, hR⟩ := hCsrc ν hν hν_le FI.src t ht
    rw [hSn]
    change ‖FI.src.H t‖ ≤ |Csrc| ∧ ‖FlatSettingInst.conjX (FI.src.H t)‖ ≤ |Csrc| ∧ ‖FI.src.R t‖ ≤ |Csrc|
    rw [FlatSettingInst.norm_conjX]
    exact ⟨hH.trans (le_abs_self _), hH.trans (le_abs_self _), hR.trans (le_abs_self _)⟩
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν))),
      matNorm (B t) ≤ bNorm D.K.as B * (Real.exp (D.K.as * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (bclassAeBound D.K.as ν B hB)
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν))), t ∈ Ioc (0 : ℝ) (1.1 / ν) :=
    ae_restrict_mem measurableSet_Ioc
  set K : ℝ := 3 * |Csrc| * |Cfpm| * bNorm D.K.as B with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hIntIoi : IntegrableOn (fun t : ℝ => t ^ (μ + 3 / 2) * Real.exp (-b * t)) (Ioi 0) := by
    have hμ_gt : -1 < μ + 3 / 2 := by linarith [hmu.1, hm1_nonneg]
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := μ + 3 / 2) (b := b)
      hμ_gt one_pos hb
  have hIntIoc : Integrable (fun t : ℝ => t ^ (μ + 3 / 2) * Real.exp (-b * t))
      (volume.restrict (Ioc (0 : ℝ) (1.1 / ν))) :=
    hIntIoi.mono_set Ioc_subset_Ioi_self
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν))),
      0 ≤ t ^ (μ : ℂ).re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖ := by
    filter_upwards [hmem] with t ht
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.mpr (norm_nonneg _)))
      (norm_nonneg _)
  have hpw : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν))),
      t ^ (μ : ℂ).re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖ ≤
        K * (t ^ (μ + 3 / 2) * Real.exp (-b * t)) := by
    filter_upwards [hae, hmem] with t hm ht
    have ht0 : 0 < t := ht.1
    have htIcc : t ∈ Icc (0 : ℝ) (1.1 / ν) := ⟨ht.1.le, ht.2⟩
    have hgB : ‖(S n).gB B t‖ ≤ 3 * |Csrc| * (bNorm D.K.as B * (Real.exp (D.K.as * t) * t ^ (3 / 2 : ℝ))) :=
      (gBPointwise (S n) (1.1 / ν) |Csrc| hC_Sn B t htIcc).trans
        (mul_le_mul_of_nonneg_left hm (by positivity))
    have hF : ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ ≤
        |Cfpm| * Real.exp (-(D.Pl.eigenvalue.re / 3) * t) := by
      rw [← norm_inv]
      exact (hCfpm ν hν t htIcc).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    have h1 : t ^ (μ : ℂ).re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ ≤
        t ^ μ * (|Cfpm| * Real.exp (-(D.Pl.eigenvalue.re / 3) * t)) := by
      rw [Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_left hF (Real.rpow_nonneg ht0.le _)
    have h2 : t ^ (μ : ℂ).re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖ ≤
        (t ^ μ * (|Cfpm| * Real.exp (-(D.Pl.eigenvalue.re / 3) * t))) *
          (3 * |Csrc| * (bNorm D.K.as B * (Real.exp (D.K.as * t) * t ^ (3 / 2 : ℝ)))) :=
      mul_le_mul h1 hgB (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg ht0.le _) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
    have hpow : t ^ μ * t ^ (3 / 2 : ℝ) = t ^ (μ + 3 / 2) := (Real.rpow_add ht0 μ (3 / 2)).symm
    have hexp : Real.exp (-(D.Pl.eigenvalue.re / 3) * t) * Real.exp (D.K.as * t) = Real.exp (-b * t) := by
      rw [← Real.exp_add, hb_def]
      congr 1
      ring
    calc t ^ (μ : ℂ).re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖
        ≤ (t ^ μ * (|Cfpm| * Real.exp (-(D.Pl.eigenvalue.re / 3) * t))) *
            (3 * |Csrc| * (bNorm D.K.as B * (Real.exp (D.K.as * t) * t ^ (3 / 2 : ℝ)))) := h2
      _ = K * ((t ^ μ * t ^ (3 / 2 : ℝ)) *
            (Real.exp (-(D.Pl.eigenvalue.re / 3) * t) * Real.exp (D.K.as * t))) := by
          rw [hK_def]; ring
      _ = K * (t ^ (μ + 3 / 2) * Real.exp (-b * t)) := by rw [hpow, hexp]
  unfold testedNorm
  calc ∫ t in Ioc 0 (1.1 / ν),
        t ^ (μ : ℂ).re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖
      ≤ ∫ t in Ioc 0 (1.1 / ν), K * (t ^ (μ + 3 / 2) * Real.exp (-b * t)) :=
        integral_mono_of_nonneg hnonneg (hIntIoc.const_mul K) hpw
    _ = K * ∫ t in Ioc 0 (1.1 / ν), (t ^ (μ + 3 / 2) * Real.exp (-b * t)) :=
        integral_const_mul K _
    _ ≤ K * ∫ t in Ioi (0 : ℝ), (t ^ (μ + 3 / 2) * Real.exp (-b * t)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        refine setIntegral_mono_set hIntIoi ?_ (LE.le.eventuallyLE Ioc_subset_Ioi_self)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    _ ≤ K * Cmaj := mul_le_mul_of_nonneg_left (hCmaj μ hmu) hK0
    _ ≤ K * |Cmaj| := mul_le_mul_of_nonneg_left (le_abs_self _) hK0
    _ = 3 * |Csrc| * |Cfpm| * |Cmaj| * bNorm D.K.as B := by rw [hK_def]; ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
