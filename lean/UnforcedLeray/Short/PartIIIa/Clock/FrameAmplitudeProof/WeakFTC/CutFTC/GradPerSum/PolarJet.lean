import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_1

/-!
# Part III-a, leaf `PolarKernelJet1Decay` (`PartIII-a:T21/c5/1/1/1/2`, SP 601-610, 2891-2905)

Source of record: `the November 2 reference manuscript` (SP), lines 601-610
(`eq:short-seed-functional`) and 2891-2905 (`eq:short-causal-moving-eq`).

For a radial profile `G` that is smooth on `(0, ∞)`, is `O(r²)` with `O(r)` derivative at `0`,
and is `O(r⁻²)` with `O(r⁻²)` derivative at `∞`, the planar kernel
`F(y) = c G(|y|) e^{± 2 i θ}` is `C¹` with `‖DF(y)‖ = O((1 + |y₁| + |y₂|)⁻²)`.

Proof: write `F(y) = c K(|z|) L(y)²` with `K(r) = G(r) / r²`, `z = planeToC y`, and `L = planeToC`
(sector `2`) or `L = conj ∘ planeToC` (sector `-2`). Away from the origin the chain and product
rules give `‖DF(y)‖ ≤ ‖c‖ (2 |G'(r)| + 8 |G(r)| / r)`; at the origin `|F(y)| ≤ ‖c‖ C₀ |z|²`
gives `DF(0) = 0`, and the near-origin bound gives continuity of `DF` at `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace GradPerSumLeaves

/-- `planeToC` as a continuous real-linear map. -/
def planeCLM : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ).toContinuousLinearMap

theorem planeCLM_apply (y : ℝ × ℝ) : planeCLM y = planeToC y := rfl

theorem planeToC_zero' : planeToC (0 : ℝ × ℝ) = 0 :=
  Complex.ext (by simp [planeToC]) (by simp [planeToC])

theorem planeToC_sub' (a b : ℝ × ℝ) : planeToC (a - b) = planeToC a - planeToC b :=
  Complex.ext (by simp [planeToC]) (by simp [planeToC])

theorem eq_zero_of_planeToC_eq_zero {y : ℝ × ℝ} (hy : planeToC y = 0) : y = 0 := by
  have h1 : y.1 = 0 := by simpa [planeToC] using congrArg Complex.re hy
  have h2 : y.2 = 0 := by simpa [planeToC] using congrArg Complex.im hy
  exact Prod.ext h1 h2

theorem norm_planeToC_le_two (v : ℝ × ℝ) : ‖planeToC v‖ ≤ 2 * ‖v‖ := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_snd_le v
  linarith [norm_planeToC_le v]

theorem lipschitz_norm_planeToC : LipschitzWith 2 (fun y : ℝ × ℝ => ‖planeToC y‖) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, dist_eq_norm]
  calc |‖planeToC a‖ - ‖planeToC b‖| ≤ ‖planeToC a - planeToC b‖ := abs_norm_sub_norm_le _ _
    _ = ‖planeToC (a - b)‖ := by rw [planeToC_sub']
    _ ≤ 2 * ‖a - b‖ := norm_planeToC_le_two _
    _ = _ := by norm_num

theorem norm_fderiv_norm_planeToC_le (y : ℝ × ℝ) :
    ‖fderiv ℝ (fun y : ℝ × ℝ => ‖planeToC y‖) y‖ ≤ 2 := by
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := y) lipschitz_norm_planeToC
  simpa using this

/-- The `C¹` and first-derivative decay statement for `F(y) = c (G(r) / r²) L(y)²`,
`r = |planeToC y|`, for a real-linear `L` with `|L v| = |planeToC v|`. -/
theorem sqForm_jet1 (G : ℝ → ℂ) (c : ℂ) (L : ℝ × ℝ →L[ℝ] ℂ)
    (hL : ∀ v, ‖L v‖ = ‖planeToC v‖) (hG : ContDiffOn ℝ ∞ G (Ioi 0)) {C₀ C₁ : ℝ}
    (hC₀ : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C₀ * r ^ 2 ∧ ‖deriv G r‖ ≤ C₀ * r)
    (hC₁ : ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C₁ / r ^ 2 ∧ ‖deriv G r‖ ≤ C₁ / r ^ 2) :
    ContDiff ℝ 1 (fun y => c * (G ‖planeToC y‖ * (((‖planeToC y‖ ^ 2)⁻¹ : ℝ) : ℂ)) * L y ^ 2) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ,
      ‖fderiv ℝ (fun y => c * (G ‖planeToC y‖ * (((‖planeToC y‖ ^ 2)⁻¹ : ℝ) : ℂ)) * L y ^ 2) z‖
        ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
  set N : ℝ × ℝ → ℝ := fun y => ‖planeToC y‖ with hNdef
  set K : ℝ → ℂ := fun r => G r * (((r ^ 2)⁻¹ : ℝ) : ℂ) with hKdef
  set F : ℝ × ℝ → ℂ :=
    fun y => c * (G ‖planeToC y‖ * (((‖planeToC y‖ ^ 2)⁻¹ : ℝ) : ℂ)) * L y ^ 2 with hFdef
  have hC₀nn : 0 ≤ C₀ := by
    have := (hC₀ 1 one_pos le_rfl).1
    simp only [one_pow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hC₁nn : 0 ≤ C₁ := by
    have := (hC₁ 1 le_rfl).1
    simp only [one_pow, div_one] at this
    exact (norm_nonneg _).trans this
  have hLn : ‖L‖ ≤ 2 :=
    L.opNorm_le_bound (by norm_num) fun v => (hL v).trans_le (norm_planeToC_le_two v)
  have hLy0 : ∀ y, planeToC y = 0 → L y = 0 := fun y hy =>
    norm_eq_zero.mp ((hL y).trans (by rw [hy, norm_zero]))
  -- values
  have hF_zero : ∀ y, planeToC y = 0 → F y = 0 := by
    intro y hy
    simp [F, hLy0 y hy]
  have hF_pos : ∀ y, planeToC y ≠ 0 → ‖F y‖ = ‖c‖ * ‖G (N y)‖ := by
    intro y hy
    have hr : 0 < ‖planeToC y‖ := norm_pos_iff.mpr hy
    simp only [F, N]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hL y, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos hr 2))]
    field_simp
  -- derivative data away from the origin
  have hderiv : ∀ y : ℝ × ℝ, planeToC y ≠ 0 →
      ContDiffAt ℝ 1 F y ∧
        ‖fderiv ℝ F y‖ ≤ ‖c‖ * (2 * ‖deriv G (N y)‖ + 8 * ‖G (N y)‖ / N y) := by
    intro y hy
    have hr : 0 < N y := norm_pos_iff.mpr hy
    set r := N y with hr_def
    have hGc : ContDiffAt ℝ ∞ G r := hG.contDiffAt (Ioi_mem_nhds hr)
    have hGd : HasDerivAt G (deriv G r) r := (hGc.differentiableAt (by simp)).hasDerivAt
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have hinv : HasDerivAt (fun s : ℝ => (s ^ 2)⁻¹) (-(2 * r) / (r ^ 2) ^ 2) r :=
      hsq.inv (pow_ne_zero 2 hr.ne')
    have hinvC : HasDerivAt (fun s : ℝ => (((s ^ 2)⁻¹ : ℝ) : ℂ))
        ((-(2 * r) / (r ^ 2) ^ 2 : ℝ) : ℂ) r := hinv.ofReal_comp
    set K' : ℂ := deriv G r * (((r ^ 2)⁻¹ : ℝ) : ℂ) + G r * ((-(2 * r) / (r ^ 2) ^ 2 : ℝ) : ℂ)
      with hK'
    have hK : HasDerivAt K K' r := hGd.mul hinvC
    have hNd : DifferentiableAt ℝ N y := by
      have h1 : DifferentiableAt ℝ (fun y => ‖planeCLM y‖) y :=
        (planeCLM.differentiableAt (x := y)).norm ℝ (by rw [planeCLM_apply]; exact hy)
      exact h1
    set N' := fderiv ℝ N y with hN'def
    have hN : HasFDerivAt N N' y := hNd.hasFDerivAt
    have hN' : ‖N'‖ ≤ 2 := norm_fderiv_norm_planeToC_le y
    set A : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) K').comp N'
      with hAdef
    have hKN0 : HasFDerivAt (K ∘ N) A y := hK.hasFDerivAt.comp y hN
    have hKN : HasFDerivAt (fun y => K (N y)) A y := hKN0
    have hQ : HasFDerivAt (fun y => L y * L y) (L y • L + L y • L) y :=
      L.hasFDerivAt.mul L.hasFDerivAt
    have hFeq : F = (fun y => c * K (N y)) * (fun y => L y * L y) := by
      funext z
      simp only [F, K, N, Pi.mul_apply]
      ring
    have hF : HasFDerivAt F ((c * K (N y)) • (L y • L + L y • L) + (L y * L y) • (c • A)) y := by
      rw [hFeq]
      exact (hKN.const_mul c).mul hQ
    -- smoothness
    have hNc : ContDiffAt ℝ 1 N y := by
      have h1 : ContDiffAt ℝ 1 (fun y => ‖planeCLM y‖) y :=
        (contDiffAt_norm ℝ (by rw [planeCLM_apply]; exact hy)).comp y
          planeCLM.contDiff.contDiffAt
      exact h1
    have hinvc : ContDiffAt ℝ 1 (fun s : ℝ => (((s ^ 2)⁻¹ : ℝ) : ℂ)) r :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp r
        ((contDiffAt_id.pow 2).inv (pow_ne_zero 2 hr.ne'))
    have hKc : ContDiffAt ℝ 1 K r := (hGc.of_le (by exact_mod_cast le_top)).mul hinvc
    have hFc : ContDiffAt ℝ 1 F y := by
      have := (contDiffAt_const (c := c)).mul (hKc.comp y hNc) |>.mul
        ((L.contDiff.contDiffAt (x := y)).pow 2)
      exact this
    refine ⟨hFc, ?_⟩
    rw [hF.fderiv]
    have hKr : ‖K r‖ = ‖G r‖ * (r ^ 2)⁻¹ := by
      simp only [K]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hr 2))]
    have hK'n : ‖K'‖ ≤ ‖deriv G r‖ * (r ^ 2)⁻¹ + ‖G r‖ * (2 * r / (r ^ 2) ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hr 2)), neg_div, abs_neg,
        abs_of_pos (by positivity)]
    have hAn : ‖A‖ ≤ 2 * ‖K'‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, norm_smul]
      calc ‖N' v‖ * ‖K'‖ ≤ (‖N'‖ * ‖v‖) * ‖K'‖ := by gcongr; exact N'.le_opNorm v
        _ ≤ (2 * ‖v‖) * ‖K'‖ := by gcongr
        _ = 2 * ‖K'‖ * ‖v‖ := by ring
    have hLy : ‖L y‖ = r := hL y
    have e1 : ‖c * K (N y)‖ = ‖c‖ * (‖G r‖ * (r ^ 2)⁻¹) := by rw [norm_mul, hKr]
    have e2 : ‖L y • L + L y • L‖ ≤ 4 * r := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, hLy]
      nlinarith [hr.le]
    have e3 : ‖L y * L y‖ = r * r := by rw [norm_mul, hLy]
    have e4 : ‖c • A‖ ≤ ‖c‖ * (2 * (‖deriv G r‖ * (r ^ 2)⁻¹ + ‖G r‖ * (2 * r / (r ^ 2) ^ 2))) := by
      rw [norm_smul]
      gcongr
      exact hAn.trans (by gcongr)
    calc ‖(c * K (N y)) • (L y • L + L y • L) + (L y * L y) • (c • A)‖
        ≤ ‖(c * K (N y)) • (L y • L + L y • L)‖ + ‖(L y * L y) • (c • A)‖ := norm_add_le _ _
      _ = ‖c * K (N y)‖ * ‖L y • L + L y • L‖ + ‖L y * L y‖ * ‖c • A‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ (‖c‖ * (‖G r‖ * (r ^ 2)⁻¹)) * (4 * r) +
          (r * r) * (‖c‖ * (2 * (‖deriv G r‖ * (r ^ 2)⁻¹ + ‖G r‖ * (2 * r / (r ^ 2) ^ 2)))) := by
          rw [e1, e3]
          gcongr
      _ = ‖c‖ * (2 * ‖deriv G r‖ + 8 * ‖G r‖ / r) := by
          field_simp
          ring
  -- derivative at the origin
  have hF0 : HasFDerivAt F (0 : ℝ × ℝ →L[ℝ] ℂ) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hF00 : F 0 = 0 := hF_zero 0 planeToC_zero'
    simp only [zero_add, hF00, sub_zero, ContinuousLinearMap.zero_apply]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ × ℝ => ‖h‖ ^ 2) ?_
      (Asymptotics.isLittleO_norm_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound (4 * ‖c‖ * C₀) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
    rw [mem_ball_zero_iff] at hh
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases h0 : planeToC h = 0
    · rw [hF_zero h h0, norm_zero]
      positivity
    · rw [hF_pos h h0]
      have hr : 0 < N h := norm_pos_iff.mpr h0
      have hr1 : N h ≤ 1 := by
        have := norm_planeToC_le_two h
        simp only [N]
        linarith
      have hG := (hC₀ (N h) hr hr1).1
      have h2 : N h ≤ 2 * ‖h‖ := norm_planeToC_le_two h
      calc ‖c‖ * ‖G (N h)‖ ≤ ‖c‖ * (C₀ * N h ^ 2) := by gcongr
        _ ≤ ‖c‖ * (C₀ * (2 * ‖h‖) ^ 2) := by gcongr
        _ = 4 * ‖c‖ * C₀ * ‖h‖ ^ 2 := by ring
  -- near and far bounds on the derivative
  have hnear : ∀ y, N y ≤ 1 → ‖fderiv ℝ F y‖ ≤ 10 * ‖c‖ * C₀ * N y := by
    intro y hy1
    by_cases h0 : planeToC y = 0
    · rw [eq_zero_of_planeToC_eq_zero h0, hF0.fderiv, norm_zero]
      have : 0 ≤ N y := norm_nonneg _
      positivity
    · have hr : 0 < N y := norm_pos_iff.mpr h0
      obtain ⟨hG1, hG2⟩ := hC₀ (N y) hr hy1
      refine (hderiv y h0).2.trans ?_
      rw [mul_div_assoc]
      have h8 : ‖G (N y)‖ / N y ≤ C₀ * N y := by
        rw [div_le_iff₀ hr]
        nlinarith
      calc ‖c‖ * (2 * ‖deriv G (N y)‖ + 8 * (‖G (N y)‖ / N y)) ≤
          ‖c‖ * (2 * (C₀ * N y) + 8 * (C₀ * N y)) := by gcongr
        _ = 10 * ‖c‖ * C₀ * N y := by ring
  have hfar : ∀ y, 1 ≤ N y → ‖fderiv ℝ F y‖ ≤ 10 * ‖c‖ * C₁ / N y ^ 2 := by
    intro y hy1
    have hr : 0 < N y := by linarith
    have h0 : planeToC y ≠ 0 := norm_pos_iff.mp hr
    obtain ⟨hG1, hG2⟩ := hC₁ (N y) hy1
    refine (hderiv y h0).2.trans ?_
    rw [mul_div_assoc]
    have h8 : ‖G (N y)‖ / N y ≤ C₁ / N y ^ 2 := by
      calc ‖G (N y)‖ / N y ≤ ‖G (N y)‖ := div_le_self (norm_nonneg _) hy1
        _ ≤ C₁ / N y ^ 2 := hG1
    calc ‖c‖ * (2 * ‖deriv G (N y)‖ + 8 * (‖G (N y)‖ / N y)) ≤
        ‖c‖ * (2 * (C₁ / N y ^ 2) + 8 * (C₁ / N y ^ 2)) := by gcongr
      _ = 10 * ‖c‖ * C₁ / N y ^ 2 := by ring
  -- continuity of the derivative at the origin
  have hNcont : Continuous N := by
    have hpl : Continuous (fun y : ℝ × ℝ => planeToC y) := by
      unfold planeToC
      exact Complex.equivRealProdCLM.symm.continuous
    exact continuous_norm.comp hpl
  have hcont0 : ContinuousAt (fderiv ℝ F) 0 := by
    rw [ContinuousAt, hF0.fderiv]
    refine squeeze_zero_norm' (a := fun y => 10 * ‖c‖ * C₀ * N y) ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
      rw [mem_ball_zero_iff] at hy
      refine hnear y ?_
      have := norm_planeToC_le_two y
      simp only [N]
      linarith
    · have h := (hNcont.tendsto 0).const_mul (10 * ‖c‖ * C₀)
      have hN0 : N 0 = 0 := by simp [N, planeToC_zero']
      rw [hN0, mul_zero] at h
      exact h
  have hdiff : Differentiable ℝ F := by
    intro y
    by_cases h0 : planeToC y = 0
    · rw [eq_zero_of_planeToC_eq_zero h0]
      exact hF0.differentiableAt
    · exact (hderiv y h0).1.differentiableAt one_ne_zero
  have hcont : Continuous (fderiv ℝ F) := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases h0 : planeToC y = 0
    · rw [eq_zero_of_planeToC_eq_zero h0]
      exact hcont0
    · exact (hderiv y h0).1.continuousAt_fderiv one_ne_zero
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨hdiff, hcont⟩, 9 * (10 * ‖c‖ * (C₀ + C₁)), by positivity,
    fun z => ?_⟩
  set S := 1 + |z.1| + |z.2| with hS
  have hSpos : 0 < S := by positivity
  have hz1 : |z.1| ≤ N z := abs_fst_le z
  have hz2 : |z.2| ≤ N z := abs_snd_le z
  have key : ‖fderiv ℝ F z‖ * S ^ 2 ≤ 9 * (10 * ‖c‖ * (C₀ + C₁)) := by
    by_cases h1 : N z ≤ 1
    · have hb : S ^ 2 ≤ 9 := by
        have : S ≤ 3 := by linarith
        nlinarith
      have hd := hnear z h1
      have hN0 : 0 ≤ N z := norm_nonneg _
      calc ‖fderiv ℝ F z‖ * S ^ 2 ≤ (10 * ‖c‖ * C₀ * N z) * 9 := by gcongr
        _ ≤ (10 * ‖c‖ * C₀ * 1) * 9 := by gcongr
        _ ≤ 9 * (10 * ‖c‖ * (C₀ + C₁)) := by nlinarith [norm_nonneg c]
    · have h1 : 1 < N z := not_le.mp h1
      have hr : 0 < N z := by linarith
      have hb : S ^ 2 ≤ 9 * N z ^ 2 := by
        have : S ≤ 3 * N z := by linarith
        nlinarith
      have hd := hfar z h1.le
      calc ‖fderiv ℝ F z‖ * S ^ 2 ≤ (10 * ‖c‖ * C₁ / N z ^ 2) * (9 * N z ^ 2) := by gcongr
        _ = 9 * (10 * ‖c‖ * C₁) := by field_simp
        _ ≤ 9 * (10 * ‖c‖ * (C₀ + C₁)) := by nlinarith [norm_nonneg c]
  calc ‖fderiv ℝ F z‖ = ‖fderiv ℝ F z‖ * S ^ 2 * (S⁻¹) ^ 2 := by field_simp
    _ ≤ 9 * (10 * ‖c‖ * (C₀ + C₁)) * (S⁻¹) ^ 2 := by gcongr

/-- `angPhase 2 z = z² / |z|²`. -/
theorem angPhase_two_eq (z : ℂ) :
    Planar.NUE.Ang.angPhase 2 z = (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * z ^ 2 := by
  unfold Planar.NUE.Ang.angPhase
  push_cast
  rw [zpow_two]
  ring

/-- `angPhase (-2) z = conj(z)² / |z|²`. -/
theorem angPhase_neg_two_eq (z : ℂ) :
    Planar.NUE.Ang.angPhase (-2) z = (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * conj z ^ 2 := by
  by_cases hz : z = 0
  · subst hz
    simp [Planar.NUE.Ang.angPhase]
  · unfold Planar.NUE.Ang.angPhase
    have hr : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
    have hconj : conj z = (‖z‖ : ℂ) ^ 2 / z := by
      rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hconj, zpow_neg, zpow_two]
    push_cast
    field_simp

/-- **Leaf `PolarKernelJet1Decay` (`PartIII-a:T21/c5/1/1/1/2`, SP 601-610, 2891-2905).** -/
theorem polarKernelJet1Decay_proof : PolarKernelJet1Decay := by
  intro G c n hn hG _hG0 hC₀ hC₁
  obtain ⟨C₀, hC₀⟩ := hC₀
  obtain ⟨C₁, hC₁⟩ := hC₁
  obtain ⟨L, hL, hEq⟩ : ∃ L : ℝ × ℝ →L[ℝ] ℂ, (∀ v, ‖L v‖ = ‖planeToC v‖) ∧
      (fun y : ℝ × ℝ => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase n (planeToC y)) =
        (fun y => c * (G ‖planeToC y‖ * (((‖planeToC y‖ ^ 2)⁻¹ : ℝ) : ℂ)) * L y ^ 2) := by
    rcases hn with rfl | rfl
    · refine ⟨(Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp planeCLM,
        fun v => ?_, ?_⟩
      · simp [planeCLM_apply]
      · funext y
        rw [angPhase_neg_two_eq]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          Complex.conjCLE_apply, planeCLM_apply]
        ring
    · refine ⟨planeCLM, fun v => by rw [planeCLM_apply], ?_⟩
      funext y
      rw [angPhase_two_eq, planeCLM_apply]
      ring
  show ContDiff ℝ 1 (fun y : ℝ × ℝ => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase n (planeToC y)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ,
      ‖fderiv ℝ (fun y : ℝ × ℝ => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase n (planeToC y)) z‖
        ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2
  rw [hEq]
  exact sqForm_jet1 G c L hL hG hC₀ hC₁

end GradPerSumLeaves

end UnforcedLeray.Short.IIIa
