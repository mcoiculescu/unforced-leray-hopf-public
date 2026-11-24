import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.CellPairBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10

/-!
# Proof of `FcvGInt` (source 4614-4615, 4562-4574)

`g_B = gBD D (Bmat ..)` is a continuous combination of `H`, `conjX H`, `R` with coefficients linear
in `B(t)`; `B` is continuous on `(0,∞)`, vanishes past the cutoff and is `O(t^{3/2})` before it
(`bmatBound`).  Hence `t ↦ t^μ ⟨g_B(t), φ⟩` is continuous on `(0,s]` and bounded there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem abs_entry_le_frob (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  have h1 : A i j ^ 2 ≤ ∑ l, A i l ^ 2 :=
    Finset.single_le_sum (f := fun l => A i l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ l, A i l ^ 2 ≤ ∑ k, ∑ l, A k l ^ 2 :=
    Finset.single_le_sum (f := fun k => ∑ l, A k l ^ 2)
      (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem abs_Bd_le (M : Mat3) (K : ℝ) (h : ∀ i j, |M i j| ≤ K) : |Bd M| ≤ K := by
  unfold Bd
  rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith [abs_sub (M 0 0) (M 2 2), h 0 0, h 2 2]

theorem abs_Be_le (M : Mat3) (K : ℝ) (h : ∀ i j, |M i j| ≤ K) : |Be M| ≤ K := by
  unfold Be
  rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith [abs_add_le (M 0 2) (M 2 0), h 0 2, h 2 0]

theorem abs_Bbeta_le (M : Mat3) (K : ℝ) (h : ∀ i j, |M i j| ≤ K) :
    |ConcreteYF.Bbeta M| ≤ K := by
  unfold ConcreteYF.Bbeta
  rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith [abs_add_le (M 0 0) (M 2 2), h 0 0, h 2 2]

theorem norm_coef_minus_le (x y K : ℝ) (hx : |x| ≤ K) (hy : |y| ≤ K) :
    ‖-(1 / 2 : ℂ) * (((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))‖ ≤ K := by
  have h2 : ‖((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)‖ ≤ |x| + |y| := by
    calc ‖((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)‖
        ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * ((y : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = |x| + |y| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : ‖-(1 / 2 : ℂ) * (((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))‖ =
      (1 / 2) * ‖((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)‖ := by
    rw [norm_mul]
    norm_num
  rw [h1]
  linarith [h2, hx, hy]

theorem norm_coef_plus_le (x y K : ℝ) (hx : |x| ≤ K) (hy : |y| ≤ K) :
    ‖-(1 / 2 : ℂ) * (((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ K := by
  have h2 : ‖((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖ ≤ |x| + |y| := by
    calc ‖((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖
        ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * ((y : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |x| + |y| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : ‖-(1 / 2 : ℂ) * (((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ =
      (1 / 2) * ‖((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖ := by
    rw [norm_mul]
    norm_num
  rw [h1]
  linarith [h2, hx, hy]

/-- `B = Bmat ν μ χ A` is continuous on `(0,∞)` (`A ∈ C^6`, `χ` smooth). -/
theorem bmat_continuousOn {ν μ : ℝ} {χ : ℝ → ℝ} {as : ℝ} {A : ℝ → Mat3}
    (hχ : IsSourceCutoffC χ) (hA : IsAffElem as A) :
    ContinuousOn (Bmat ν μ χ A) (Ioi 0) := by
  have hχ6 : ContDiff ℝ 6 χ := hχ.smooth.of_le (by simp)
  have hf : ContDiffOn ℝ 6 (fun s => χ (ν * s)) (Ioi 0) :=
    (hχ6.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hAy : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := by
    unfold Ay
    exact hf.smul hA.smooth
  have hd : ContinuousOn (deriv (Ay ν χ A)) (Ioi 0) :=
    hAy.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc : ContinuousOn (Ay ν χ A) (Ioi 0) := hAy.continuousOn
  have hmu : ContinuousOn (fun s : ℝ => μ / s) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt hs)
  show ContinuousOn (fun s => deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s) (Ioi 0)
  exact hd.add (hmu.smul hc)

/-- `B(t) = 0` past the cutoff `11/(10ν)`. -/
theorem bmat_zero_of_large {ν μ : ℝ} {χ : ℝ → ℝ} {A : ℝ → Mat3} (hχ : IsSourceCutoffC χ)
    (hν : 0 < ν) {t : ℝ} (ht : (11 / 10) / ν < t) : Bmat ν μ χ A t = 0 := by
  have hz : Ay ν χ A =ᶠ[𝓝 t] (fun _ => (0 : Mat3)) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    have hτ2 : (11 / 10) / ν < τ := hτ
    have h1 : 11 / 10 < τ * ν := (div_lt_iff₀ hν).1 hτ2
    unfold Ay
    rw [hχ.zero (ν * τ) (by linarith [mul_comm ν τ]), zero_smul]
  have hd : deriv (Ay ν χ A) t = 0 := by
    rw [hz.deriv_eq]
    exact deriv_const _ _
  have hA0 : Ay ν χ A t = 0 := by
    unfold Ay
    have h1 : 11 / 10 < t * ν := (div_lt_iff₀ hν).1 ht
    rw [hχ.zero (ν * t) (by linarith [mul_comm ν t]), zero_smul]
  unfold Bmat
  rw [hd, hA0, smul_zero, add_zero]

/-- `‖g_B(t)‖` is bounded on `(0,s]` when the entries of `B` are. -/
theorem gBD_norm_le {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (D : FlatInstData κ ν c m tr)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s K : ℝ) (hK : 0 ≤ K)
    (hB : ∀ t, 0 < t → t ≤ s → ∀ i j, |B t i j| ≤ K) :
    ∃ C : ℝ, ∀ t, 0 < t → t ≤ s → ‖gBD D B t‖ ≤ C := by
  obtain ⟨CH, hCH⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn
    (f := fun t => D.src.H t) D.src.H_cont.continuousOn
  obtain ⟨CR, hCR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn
    (f := fun t => D.src.R t) D.src.R_cont.continuousOn
  refine ⟨K * (2 * |CH| + |CR|), fun t ht0 hts => ?_⟩
  have hH : ‖D.src.H t‖ ≤ |CH| := (hCH t ⟨ht0.le, hts⟩).trans (le_abs_self _)
  have hR : ‖D.src.R t‖ ≤ |CR| := (hCR t ⟨ht0.le, hts⟩).trans (le_abs_self _)
  have hb := hB t ht0 hts
  have ha1 := norm_coef_minus_le (Bd (B t)) (Be (B t)) K (abs_Bd_le _ K hb) (abs_Be_le _ K hb)
  have ha2 := norm_coef_plus_le (Bd (B t)) (Be (B t)) K (abs_Bd_le _ K hb) (abs_Be_le _ K hb)
  have hbeta : ‖((ConcreteYF.Bbeta (B t) : ℝ) : ℂ)‖ ≤ K := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Bbeta_le (B t) K hb
  have hcH : ‖conjX (D.src.H t)‖ ≤ |CH| := by rw [norm_conjX]; exact hH
  have hAH : ‖(-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) •
      D.src.H t‖ ≤ K * |CH| := by
    rw [norm_smul]; exact mul_le_mul ha1 hH (norm_nonneg _) hK
  have hBH : ‖(-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) •
      conjX (D.src.H t)‖ ≤ K * |CH| := by
    rw [norm_smul]; exact mul_le_mul ha2 hcH (norm_nonneg _) hK
  have hCR' : ‖((ConcreteYF.Bbeta (B t) : ℝ) : ℂ) • D.src.R t‖ ≤ K * |CR| := by
    rw [norm_smul]; exact mul_le_mul hbeta hR (norm_nonneg _) hK
  rw [gBD_apply]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add hAH hBH)) hCR').trans ?_
  exact le_of_eq (by ring)

/-- `t ↦ g_B(t)` is continuous on `(0,∞)` when `B` is. -/
theorem gBD_continuousOn {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (D : FlatInstData κ ν c m tr)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : ContinuousOn B (Ioi 0)) :
    ContinuousOn (fun t => gBD D B t) (Ioi 0) := by
  have hent : ∀ i j, ContinuousOn (fun t => B t i j) (Ioi 0) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hB)
  have hBd : ContinuousOn (fun t => ((Bd (B t) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((((hent 0 0).sub (hent 2 2)).div_const 2))
  have hBe : ContinuousOn (fun t => ((Be (B t) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((((hent 0 2).add (hent 2 0)).div_const 2))
  have hBb : ContinuousOn (fun t => ((ConcreteYF.Bbeta (B t) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((((hent 0 0).add (hent 2 2)).div_const 2))
  have hcoefA : ContinuousOn (fun t => -(1 / 2 : ℂ) *
      (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) (Ioi 0) :=
    continuousOn_const.mul (hBd.sub (continuousOn_const.mul hBe))
  have hcoefB : ContinuousOn (fun t => -(1 / 2 : ℂ) *
      (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) (Ioi 0) :=
    continuousOn_const.mul (hBd.add (continuousOn_const.mul hBe))
  have hH : ContinuousOn (fun t => D.src.H t) (Ioi 0) := D.src.H_cont.continuousOn
  have hHc : ContinuousOn (fun t => conjX (D.src.H t)) (Ioi 0) :=
    continuous_conjX.comp_continuousOn hH
  have hR : ContinuousOn (fun t => D.src.R t) (Ioi 0) := D.src.R_cont.continuousOn
  refine ContinuousOn.congr (f := fun t =>
      (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))) • D.src.H t
      + (-(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ) + Complex.I * ((Be (B t) : ℝ) : ℂ))) •
        conjX (D.src.H t)
      - ((ConcreteYF.Bbeta (B t) : ℝ) : ℂ) • D.src.R t) ?_ (fun t _ => gBD_apply D B t)
  exact ((hcoefA.smul hH).add (hcoefB.smul hHc)).sub (hBb.smul hR)

/-- The main integrability statement. -/
theorem fcvGInt : FcvGInt := by
  unfold FcvGInt
  intro κ ν c m hm hc tr D μ as χf A hν hμ hχ hA φ hφ s hs
  have hBc : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := bmat_continuousOn hχ hA
  have hG : ContinuousOn (fun t => gBD D (Bmat ν μ χf A) t) (Ioi 0) :=
    gBD_continuousOn D hBc
  obtain ⟨K, hK0, hK⟩ := cellPair_bound (m := m) hφ
  -- entrywise bound of `B` on `(0,s]`
  set K0 : ℝ := (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| with hK0def
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]
    have h1 : 0 ≤ (11 / 10 / ν : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ 1 + μ := by linarith
    positivity
  have hBent : ∀ t, 0 < t → t ≤ s → ∀ i j, |Bmat ν μ χf A t i j| ≤ K0 := by
    intro t ht hts i j
    by_cases hle : t ≤ (11 / 10) / ν
    · have hbd := bmatBound as χf hχ ν μ hν hμ.le A hA t ht hle
      refine (abs_entry_le_frob _ i j).trans (hbd.trans ?_)
      have h1 : t ^ (3 / 2 : ℝ) ≤ ((11 / 10) / ν) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow ht.le hle (by norm_num)
      have hX0 : 0 ≤ (1 + μ) * t ^ (3 / 2 : ℝ) := by
        have : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
        have : 0 ≤ 1 + μ := by linarith
        positivity
      calc (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χf A
          ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * |affM ν χf A| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hX0
        _ ≤ (1 + μ) * ((11 / 10) / ν) ^ (3 / 2 : ℝ) * |affM ν χf A| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left h1 (by linarith)
    · rw [bmat_zero_of_large hχ hν (not_le.1 hle)]
      simp only [Pi.zero_apply, abs_zero]
      exact hK00
  obtain ⟨C, hC⟩ := gBD_norm_le D (Bmat ν μ χf A) s K0 hK00 hBent
  -- continuity of the integrand on `Ioi 0`
  have hPc : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      cellPair φ (gBD D (Bmat ν μ χf A) t)) (Ioi 0) := by
    have hp : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ))) (Ioi 0) := by
      refine ContinuousOn.cpow_const ?_ ?_
      · exact Complex.continuous_ofReal.continuousOn
      · intro t ht
        exact Or.inl (by simpa using ht)
    have hq : ContinuousOn (fun t : ℝ => cellPair φ (gBD D (Bmat ν μ χf A) t)) (Ioi 0) := by
      have := (cellPairCLM hφ).continuous.comp_continuousOn hG
      simpa only [Function.comp_def, cellPairCLM_apply] using this
    exact hp.mul hq
  -- integrability via boundedness on a finite measure set
  have hmeas : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      cellPair φ (gBD D (Bmat ν μ χf A) t)) (Ioc 0 s) :=
    hPc.mono (fun t ht => ht.1)
  have hmeasR : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      cellPair φ (gBD D (Bmat ν μ χf A) t)) (volume.restrict (Ioc 0 s)) :=
    hmeas.aestronglyMeasurable measurableSet_Ioc
  have hfin : (volume.restrict (Ioc 0 s)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top.ne
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc 0 s)),
      ‖((t : ℂ) ^ (μ : ℂ)) * cellPair φ (gBD D (Bmat ν μ χf A) t)‖ ≤ s ^ μ * (K * C) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have hts : t ≤ s := ht.2
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.ofReal_re]
    have h1 : t ^ μ ≤ s ^ μ := Real.rpow_le_rpow ht0.le hts hμ.le
    have h2 : ‖cellPair φ (gBD D (Bmat ν μ χf A) t)‖ ≤ K * C :=
      (hK _).trans (mul_le_mul_of_nonneg_left (hC t ht0 hts) hK0)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg hs.le _)
  have hbound' : ∀ᵐ t : ℝ ∂((volume.restrict (Ioc 0 s)).restrict univ),
      ‖((t : ℂ) ^ (μ : ℂ)) * cellPair φ (gBD D (Bmat ν μ χf A) t)‖ ≤ s ^ μ * (K * C) := by
    rw [Measure.restrict_univ]
    exact hbound
  exact integrableOn_univ.1 (Measure.integrableOn_of_bounded hfin hmeasR hbound')

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
