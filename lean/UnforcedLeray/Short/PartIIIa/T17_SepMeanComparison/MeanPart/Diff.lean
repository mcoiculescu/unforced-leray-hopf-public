import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.WMain

/-!
# Mean part helper: the pointwise comparison of the two integrands (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mp_mlm_apply_le (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) ℝ) (v : Space)
    (k : Fin 3) : |M ![v, coordinateVector k]| ≤ ‖M‖ * ‖v‖ := by
  have h := M.le_opNorm ![v, coordinateVector k]
  rw [Fin.prod_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mp_norm_e, mul_one] at h
  simpa using h

theorem mp_diff_pointwise (hK : SepKernelBounds) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ε : ℝ) (μ : ℂ) (ρo ρi : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
      -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (v : Space) (i : Fin 3)
        (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 →
        ‖mpHW ν ε μ G xo v i p - mpVd μ G p xo v i‖ ≤
          C * ε * (1 + |p.2.2|) * ((ρi - ρo) ^ (-7 : ℝ) + (ρi - ρo) ^ (-6 : ℝ)) * ‖v‖ *
            tensorNorm (G p.2.1 p.2.2) := by
  obtain ⟨Ck, hCk0, hCk⟩ := mp_kernel_diff hK
  refine ⟨18 * Ck, by positivity, ?_⟩
  intro ν ε μ ρo ρi hν hν1 hε hε1 hμ hρo hρ G hGs xo hxo v i p hp
  obtain ⟨l, w⟩ := p
  simp only at hp
  have hD : 0 < ρi - ρo := by linarith
  have hD7 : 0 ≤ (ρi - ρo) ^ (-7 : ℝ) := Real.rpow_nonneg hD.le _
  have hD6 : 0 ≤ (ρi - ρo) ^ (-6 : ℝ) := Real.rpow_nonneg hD.le _
  by_cases hw : Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) ≤ ρo
  · have hs : 0 < ν * (1 - l ^ 2) * ε ^ 2 := mul_pos (mul_pos hν (by nlinarith [hp.1, hp.2])) (by positivity)
    have hgap := mp_gap ρo ρi xo xo hxo l hp w hw
    simp only [sub_self, norm_zero, sub_zero] at hgap
    set u0 : Space := xo - l • mpV3 w with hu0
    set u : Space := xo - l • (!₂[w.1.1, w.1.2, ε * w.2] : Space) with hu
    have hu0c : u 0 = u0 0 := by simp [hu, hu0, mpV3]
    have hu1c : u 1 = u0 1 := by simp [hu, hu0, mpV3]
    have hnorm : ‖u - u0‖ ≤ ε * |w.2| := by
      have : u - u0 = (-(l * (ε * w.2))) • coordinateVector 2 := by
        ext n
        fin_cases n <;> simp [hu, hu0, mpV3, coordinateVector] <;> ring
      rw [this, norm_smul, mp_norm_e, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
        abs_of_pos hp.1, abs_of_pos hε]
      calc l * (ε * |w.2|) ≤ 1 * (ε * |w.2|) := by
            gcongr; exact hp.2.le
        _ = ε * |w.2| := one_mul _
    have hsle : ν * (1 - l ^ 2) * ε ^ 2 ≤ ε := by
      have h1 : ν * (1 - l ^ 2) ≤ 1 := by nlinarith [hp.1, hp.2]
      have h2 : ε ^ 2 ≤ ε := by nlinarith
      calc ν * (1 - l ^ 2) * ε ^ 2 ≤ 1 * ε ^ 2 := by gcongr
        _ ≤ ε := by linarith
    have hkd := hCk
    -- the difference of the two integrands
    have hdiff : mpHW ν ε μ G xo v i (l, w) - mpVd μ G (l, w) xo v i =
        -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
          ((((iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
            iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) u0) ![v, coordinateVector k] : ℝ) : ℂ) *
              ((G w.1 w.2 j k : ℝ) : ℂ))) := by
      unfold mpHW mpVd
      simp only [ContinuousMultilinearMap.sub_apply, Complex.ofReal_sub, sub_mul,
        Finset.sum_sub_distrib]
      ring
    rw [hdiff]
    have hb : ∀ j k : Fin 3, ‖((((iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
            iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) u0) ![v, coordinateVector k] : ℝ) : ℂ) *
              ((G w.1 w.2 j k : ℝ) : ℂ))‖ ≤
          (Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-7 : ℝ) + (ρi - ρo) ^ (-6 : ℝ)) * ‖v‖) *
            tensorNorm (G w.1 w.2) := by
      intro j k
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := mp_mlm_apply_le (iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
            iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) u0) v k
      have h2 := hCk i j (ν * (1 - l ^ 2) * ε ^ 2) hs u0 u (ρi - ρo) hD hgap hu0c hu1c
      have h3 : ‖iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
            iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) u0‖ ≤
          Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-7 : ℝ) + (ρi - ρo) ^ (-6 : ℝ)) := by
        refine h2.trans ?_
        have hsum : ν * (1 - l ^ 2) * ε ^ 2 + ‖u - u0‖ ≤ ε + ε * |w.2| := add_le_add hsle hnorm
        have hDD : 0 ≤ (ρi - ρo) ^ (-7 : ℝ) + (ρi - ρo) ^ (-6 : ℝ) := add_nonneg hD7 hD6
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCk0) hDD
      have h4 : |((iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u -
            iteratedFDeriv ℝ 2 (fun x => heatLerayK0 i j x) u0) ![v, coordinateVector k])| ≤
          (Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-7 : ℝ) + (ρi - ρo) ^ (-6 : ℝ))) * ‖v‖ :=
        h1.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
      exact mul_le_mul h4 (mp_entry_le _ j k) (abs_nonneg _) (by positivity)
    have hs9 := mp_sum9 _ _ hb
    have hw1 := mp_norm_cpow_le μ hμ l hp
    rw [norm_mul, norm_mul]
    have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [hn2]
    calc 2 * (‖(l : ℂ) ^ (2 * μ + 2)‖ * ‖∑ j : Fin 3, ∑ k : Fin 3, _‖)
        ≤ 2 * (1 * (9 * ((Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-7 : ℝ) + (ρi - ρo) ^ (-6 : ℝ)) * ‖v‖) *
            tensorNorm (G w.1 w.2)))) := by gcongr
      _ = _ := by ring
  · push_neg at hw
    have h0 : G w.1 w.2 = 0 := hGs _ _ hw
    have : mpHW ν ε μ G xo v i (l, w) - mpVd μ G (l, w) xo v i = 0 := by
      simp [mpHW, mpVd, h0]
    rw [this, norm_zero]
    have : 0 ≤ tensorNorm (G w.1 w.2) := Real.sqrt_nonneg _
    positivity

end UnforcedLeray.Short.IIIa

end
