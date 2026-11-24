import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtCongr
import UnforcedLeray.Short.PartIIIa.T03_PlaneRadialInv

/-!
# Integrability of the Cartesian source `Σ_M` (`SigmaInt`, source 4766-4775, 4924-4937)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete

/-- Outward majorant of the phase mean: `χ_o(νu) ∫ |M(u,·)|_F`. -/
def cbdAux (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (u : ℝ) : ℝ :=
  χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)

theorem frob_nonneg_aux (A : Mat3) : 0 ≤ frob A := by
  unfold frob
  exact Real.sqrt_nonneg _

theorem abs_entry_le_frob_aux2 (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem chi_zero_aux {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {ν u : ℝ} (hν : 0 < ν)
    (hu : u ∉ Ioi (6 / 5 / ν)) : χo (ν * u) = 0 := by
  apply hχo.zero
  have : u ≤ 6 / 5 / ν := not_lt.mp hu
  rw [le_div_iff₀ hν] at this
  linarith

theorem oldThin_parts_aux (c ν : ℝ) (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    AEStronglyMeasurable M ((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) ∧
      Integrable (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * frob (M p))
        ((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) := by
  unfold OldThinFinite oldMeasure at hM
  exact hM

theorem abs_coord_div_aux (a b : ℝ) : |a / Real.sqrt (a ^ 2 + b ^ 2)| ≤ 1 := by
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (a ^ 2 + b ^ 2)) with h0 | hpos
  · rw [← h0, div_zero, abs_zero]; norm_num
  · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg b])

theorem rotQ_abs_aux (x' : ℝ × ℝ) (a i : Fin 3) : |rotQ x' a i| ≤ 1 := by
  have h1 : |x'.1 / Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)| ≤ 1 := abs_coord_div_aux _ _
  have h2 : |x'.2 / Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)| ≤ 1 := by
    have := abs_coord_div_aux x'.2 x'.1
    rwa [add_comm] at this
  fin_cases a <;> fin_cases i <;> simp [rotQ, h1, h2]

theorem rotQ_meas_aux (a i : Fin 3) : Measurable (fun x' : ℝ × ℝ => rotQ x' a i) := by
  fin_cases a <;> fin_cases i <;> simp [rotQ] <;> fun_prop

theorem rad_qmp_aux :
    Measure.QuasiMeasurePreserving (fun x' : ℝ × ℝ => (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) volume volume := by
  refine ⟨by fun_prop, ?_⟩
  intro s hs0
  obtain ⟨N', hsN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hs0
  refine measure_mono_null hsN' ?_
  rw [Measure.map_apply (by fun_prop) hN'm]
  exact vol_preimage_radius_sq_null N' hN'0

theorem radial_aesm_aux {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x' : ℝ × ℝ => f ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) volume :=
  hf.comp_quasiMeasurePreserving rad_qmp_aux

theorem aesm_of_restrict_zero_aux {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : ∀ u, u ∉ s → g u = 0) (hg : AEStronglyMeasurable g (volume.restrict s)) :
    AEStronglyMeasurable g volume := by
  have hind : s.indicator g = g := by
    funext u
    by_cases hu : u ∈ s
    · simp [hu]
    · simp [hu, h0 u hu]
  rw [← hind]
  exact (aestronglyMeasurable_indicator_iff hs).mpr hg

theorem phase_aesm_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) (i j : Fin 3) :
    AEStronglyMeasurable (fun u => phaseMean c ν χo M u i j) volume := by
  have hSF : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  obtain ⟨hMm, -⟩ := oldThin_parts_aux c ν M hM
  apply aesm_of_restrict_zero_aux (measurableSet_Ioi : MeasurableSet (Ioi (6 / 5 / ν)))
  · intro u hu
    simp [phaseMean, chi_zero_aux hχo hν hu]
  · have hf : AEStronglyMeasurable (fun p : Chart => M p i j)
        ((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) :=
      (show Continuous fun A : Mat3 => A i j by fun_prop).comp_aestronglyMeasurable hMm
    have hI := hf.integral_prod_right'
    have hχc : Continuous fun u => χo (ν * u) :=
      hχo.smooth.continuous.comp (continuous_const.mul continuous_id)
    by_cases hij : i = 1 ∨ j = 1
    · have : (fun u => phaseMean c ν χo M u i j) = fun _ => (0 : ℝ) := by
        funext u; simp [phaseMean, hij]
      rw [this]
      exact aestronglyMeasurable_const
    · have : (fun u => phaseMean c ν χo M u i j) =
          fun u => χo (ν * u) * ∫ x, M (u, x) i j ∂(Cyl.avgμ c) := by
        funext u; simp [phaseMean, hij]
      rw [this]
      exact hχc.aestronglyMeasurable.mul hI

theorem cbd_aesm_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    AEStronglyMeasurable (cbdAux c ν χo M) volume := by
  have hSF : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  obtain ⟨hMm, -⟩ := oldThin_parts_aux c ν M hM
  apply aesm_of_restrict_zero_aux (measurableSet_Ioi : MeasurableSet (Ioi (6 / 5 / ν)))
  · intro u hu
    simp [cbdAux, chi_zero_aux hχo hν hu]
  · have hfr : AEStronglyMeasurable (fun p : Chart => frob (M p))
        ((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) :=
      (show Continuous frob by unfold frob; fun_prop).comp_aestronglyMeasurable hMm
    have hI := hfr.integral_prod_right'
    have hχc : Continuous fun u => χo (ν * u) :=
      hχo.smooth.continuous.comp (continuous_const.mul continuous_id)
    unfold cbdAux
    exact hχc.aestronglyMeasurable.mul hI

theorem frob_slice_ae_aux (c ν : ℝ) (hν : 0 < ν) (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi (6 / 5 / ν) →
      Integrable (fun x => frob (M (u, x))) (Cyl.avgμ c) := by
  have hSF : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  obtain ⟨-, hMi⟩ := oldThin_parts_aux c ν M hM
  have h1 := hMi.prod_right_ae
  rw [ae_restrict_iff' measurableSet_Ioi] at h1
  filter_upwards [h1] with u hu1 hu
  have hpos : 0 < u := lt_trans (div_pos (by norm_num) hν) (Set.mem_Ioi.mp hu)
  have hid : ∀ x, u ^ (3 / 2 : ℝ) * (u ^ (-(3 / 2) : ℝ) * frob (M (u, x))) = frob (M (u, x)) := by
    intro x
    rw [← mul_assoc, ← Real.rpow_add hpos]
    norm_num
  have hg := (hu1 hu).const_mul (u ^ (3 / 2 : ℝ))
  exact hg.congr (Filter.Eventually.of_forall fun x => hid x)

theorem entry_int_bound_aux (c : ℝ) (M : Chart → Mat3) (u : ℝ) (i j : Fin 3)
    (hI : Integrable (fun x => frob (M (u, x))) (Cyl.avgμ c)) :
    |∫ x, M (u, x) i j ∂(Cyl.avgμ c)| ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := by
  calc |∫ x, M (u, x) i j ∂(Cyl.avgμ c)| = ‖∫ x, M (u, x) i j ∂(Cyl.avgμ c)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖M (u, x) i j‖ ∂(Cyl.avgμ c) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := by
      by_cases hJ : Integrable (fun x => ‖M (u, x) i j‖) (Cyl.avgμ c)
      · exact integral_mono hJ hI (fun x => by
          rw [Real.norm_eq_abs]; exact abs_entry_le_frob_aux2 _ i j)
      · rw [integral_undef hJ]
        exact integral_nonneg fun x => frob_nonneg_aux _

theorem phase_le_cbd_ae_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∀ᵐ u ∂(volume : Measure ℝ), ∀ i j, |phaseMean c ν χo M u i j| ≤ cbdAux c ν χo M u := by
  filter_upwards [frob_slice_ae_aux c ν hν M hM] with u hu
  intro i j
  by_cases hu' : u ∈ Ioi (6 / 5 / ν)
  · have hI := hu hu'
    have hχ0 : 0 ≤ χo (ν * u) := (hχo.range _).1
    simp only [phaseMean, cbdAux]
    by_cases hij : i = 1 ∨ j = 1
    · rw [if_pos hij, abs_zero]
      exact mul_nonneg hχ0 (integral_nonneg fun x => frob_nonneg_aux _)
    · rw [if_neg hij, abs_mul, abs_of_nonneg hχ0]
      exact mul_le_mul_of_nonneg_left (entry_int_bound_aux c M u i j hI) hχ0
  · simp [phaseMean, cbdAux, chi_zero_aux hχo hν hu']

theorem sigma_abs_le_aux (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (x' : ℝ × ℝ) (j k : Fin 3)
    (hE : ∀ i l, |phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l| ≤
      cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) :
    |sigmaM c ν χo M x' j k| ≤
      9 * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
  have hinv : 0 ≤ (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have term : ∀ i l, |rotQ x' j i * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) * rotQ x' k l| ≤
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ := by
    intro i l
    have h1 := rotQ_abs_aux x' j i
    have h2 := rotQ_abs_aux x' k l
    have h3 := hE i l
    have hC0 : 0 ≤ cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ := le_trans (abs_nonneg _) h3
    have h4 : |rotQ x' j i| * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
        |phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l|) * |rotQ x' k l| ≤
        1 * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) * 1 :=
      mul_le_mul (mul_le_mul h1 (mul_le_mul_of_nonneg_left h3 hinv) (mul_nonneg hinv (abs_nonneg _))
        zero_le_one) h2 (abs_nonneg _) (mul_nonneg zero_le_one (mul_nonneg hinv hC0))
    have h5 : |rotQ x' j i * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
        phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) * rotQ x' k l| =
        |rotQ x' j i| * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
        |phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l|) * |rotQ x' k l| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hinv]
    rw [h5]
    linarith
  calc |sigmaM c ν χo M x' j k|
      = |∑ i : Fin 3, ∑ l : Fin 3, rotQ x' j i * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) * rotQ x' k l| := rfl
    _ ≤ ∑ i : Fin 3, ∑ l : Fin 3, |rotQ x' j i * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) * rotQ x' k l| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ l : Fin 3, (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => term i l
    _ = 9 * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem sigma_term_aesm_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) (j k i l : Fin 3) :
    AEStronglyMeasurable (fun x' : ℝ × ℝ => rotQ x' j i * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) * rotQ x' k l) volume := by
  have hρ : Measurable (fun x' : ℝ × ℝ => (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹) := by fun_prop
  have A1 : AEStronglyMeasurable (fun x' : ℝ × ℝ => rotQ x' j i) volume :=
    (rotQ_meas_aux j i).aestronglyMeasurable
  have A2 : AEStronglyMeasurable (fun x' : ℝ × ℝ => (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) volume :=
    hρ.aestronglyMeasurable.mul (radial_aesm_aux (phase_aesm_aux c ν χo hχo hν M hM i l))
  have A3 : AEStronglyMeasurable (fun x' : ℝ × ℝ => rotQ x' k l) volume :=
    (rotQ_meas_aux k l).aestronglyMeasurable
  exact (A1.mul A2).mul A3

theorem sigma_aesm_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) (j k : Fin 3) :
    AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k) volume := by
  have key : AEStronglyMeasurable (fun x' : ℝ × ℝ => ∑ i : Fin 3, ∑ l : Fin 3,
      rotQ x' j i * ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
        phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l) * rotQ x' k l) volume :=
    Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3)) fun i _ =>
      Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3)) fun l _ =>
        sigma_term_aesm_aux c ν χo hχo hν M hM j k i l
  exact key

theorem ofReal_cbd_le_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo)
    (M : Chart → Mat3) (u : ℝ) (hI : Integrable (fun x => frob (M (u, x))) (Cyl.avgμ c)) :
    ENNReal.ofReal (cbdAux c ν χo M u) ≤ ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c) := by
  have hχ := hχo.range (ν * u)
  have hI0 : 0 ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := integral_nonneg fun x => frob_nonneg_aux _
  have hC : cbdAux c ν χo M u ≤ ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := by
    unfold cbdAux
    exact mul_le_of_le_one_left hI0 hχ.2
  calc ENNReal.ofReal (cbdAux c ν χo M u)
      ≤ ENNReal.ofReal (∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := ENNReal.ofReal_le_ofReal hC
    _ = ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c) :=
        ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun x => frob_nonneg_aux _)

theorem cbd_lint_aux (c ν : ℝ) (χo : ℝ → ℝ) (hc : 0 < c) (hν : 0 < ν) (hχo : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      cbdAux c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) < ⊤ := by
  have hSF : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  obtain ⟨hMm, hMi⟩ := oldThin_parts_aux c ν M hM
  have hCae : AEMeasurable (fun u => ENNReal.ofReal (cbdAux c ν χo M u)) volume :=
    (cbd_aesm_aux c ν χo hχo hν M hM).aemeasurable.ennreal_ofReal
  obtain ⟨f', hf'm, hf'ae⟩ : ∃ f' : ℝ → ℝ≥0∞, Measurable f' ∧
      f' =ᵐ[volume] (fun u => ENNReal.ofReal (cbdAux c ν χo M u)) :=
    ⟨hCae.mk _, hCae.measurable_mk, hCae.ae_eq_mk.symm⟩
  have hFm : Measurable (fun v : ℝ => ENNReal.ofReal (v ^ (1 / 2 : ℝ)) * f' v) := by
    have h1 : Measurable (fun v : ℝ => ENNReal.ofReal (v ^ (1 / 2 : ℝ))) := by fun_prop
    exact h1.mul hf'm
  have hPR := UnforcedLeray.Short.IIIa.planeRadialInv
    (fun v : ℝ => ENNReal.ofReal (v ^ (1 / 2 : ℝ)) * f' v) hFm
  have hsq : ∀ s : ℝ, 0 ≤ s → (s⁻¹) ^ (1 / 2 : ℝ) = (Real.sqrt s)⁻¹ := by
    intro s hs
    rw [Real.inv_rpow hs, Real.sqrt_eq_rpow]
  have hae2 : ∀ᵐ x' ∂(volume : Measure (ℝ × ℝ)),
      f' ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) = ENNReal.ofReal (cbdAux c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) := by
    refine ae_iff.mpr (measure_mono_null (fun x' hx' => hx') ?_)
    exact vol_preimage_radius_sq_null _ (ae_iff.mp hf'ae)
  have hL : ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      cbdAux c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) =
      ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ^ (1 / 2 : ℝ)) *
        f' ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae2] with x' hx
    rw [hx, hsq _ (by positivity), ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [hL]
  refine (hPR).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (u ^ (-2 : ℝ)) * (ENNReal.ofReal (u ^ (1 / 2 : ℝ)) * f' u) ≤
        (Ioi (6 / 5 / ν)).indicator (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) *
          ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c)) u := by
    apply ae_restrict_of_ae
    filter_upwards [hf'ae, frob_slice_ae_aux c ν hν M hM] with u hu1 hu2
    by_cases hu : u ∈ Ioi (6 / 5 / ν)
    · rw [Set.indicator_of_mem hu]
      have hpos : 0 < u := lt_trans (div_pos (by norm_num) hν) (Set.mem_Ioi.mp hu)
      have e : ENNReal.ofReal (u ^ (-2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 2 : ℝ)) =
          ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos]
        norm_num
      rw [hu1, ← mul_assoc, e]
      have hC := ofReal_cbd_le_aux c ν χo hχo M u (hu2 hu)
      gcongr
    · rw [Set.indicator_of_notMem hu, hu1]
      have h0 : cbdAux c ν χo M u = 0 := by
        unfold cbdAux
        rw [chi_zero_aux hχo hν hu, zero_mul]
      rw [h0, ENNReal.ofReal_zero, mul_zero, mul_zero]
  have hbound : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-2 : ℝ)) *
      (ENNReal.ofReal (u ^ (1 / 2 : ℝ)) * f' u) ≤
      ∫⁻ u in Ioi (6 / 5 / ν), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) *
        ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c) := by
    have h1 := lintegral_mono_ae hpt
    have h2 := setLIntegral_le_lintegral (μ := (volume : Measure ℝ)) (Ioi (0 : ℝ)) (fun u => (Ioi (6 / 5 / ν)).indicator
      (fun u => ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) *
        ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c)) u)
    have h3 := lintegral_indicator (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (6 / 5 / ν))) (fun u =>
      ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) * ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c))
    exact h1.trans (h2.trans h3.le)
  refine lt_of_le_of_lt hbound ?_
  have hAE := hMi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have e1 : ∫⁻ u in Ioi (6 / 5 / ν), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) *
        ∫⁻ x, ENNReal.ofReal (frob (M (u, x))) ∂(Cyl.avgμ c) =
      ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (M p))
        ∂((volume.restrict (Ioi (6 / 5 / ν))).prod (Cyl.avgμ c)) := by
    rw [lintegral_prod _ hAE]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hpos : 0 < u := lt_trans (div_pos (by norm_num) hν) (Set.mem_Ioi.mp hu)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    dsimp only
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
  rw [e1]
  exact hMi.lintegral_lt_top

theorem sigmaM_integrable : UnforcedLeray.Short.PartIIIb.Concrete.SigmaInt := by
  intro c ν χo hc hν hχo M hM j k
  have hnn : ∀ x' : ℝ × ℝ, 0 ≤ (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      cbdAux c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := fun x' =>
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (mul_nonneg (hχo.range _).1 (integral_nonneg fun x => frob_nonneg_aux _))
  have hint : Integrable (fun x' : ℝ × ℝ => (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
      cbdAux c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) := by
    refine ⟨?_, ?_⟩
    · exact ((show Measurable (fun x' : ℝ × ℝ => (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹) by
          fun_prop).aestronglyMeasurable).mul
        (radial_aesm_aux (cbd_aesm_aux c ν χo hχo hν M hM))
    · exact (lintegral_congr (fun x' => Real.enorm_eq_ofReal (hnn x'))).trans_lt
        (cbd_lint_aux c ν χo hc hν hχo M hM)
  refine (hint.const_mul 9).mono' (sigma_aesm_aux c ν χo hχo hν M hM j k) ?_
  have hN0 := ae_iff.mp (phase_le_cbd_ae_aux c ν χo hχo hν M hM)
  have hx : ∀ᵐ x' ∂(volume : Measure (ℝ × ℝ)), ∀ i l,
      |phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i l| ≤ cbdAux c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ := by
    refine ae_iff.mpr (measure_mono_null (fun x' hx' => hx') ?_)
    exact vol_preimage_radius_sq_null _ hN0
  filter_upwards [hx] with x' hx'
  rw [Real.norm_eq_abs]
  exact sigma_abs_le_aux c ν χo M x' j k hx'
