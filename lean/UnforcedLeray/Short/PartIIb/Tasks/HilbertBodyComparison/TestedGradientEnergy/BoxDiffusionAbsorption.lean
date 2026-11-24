import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16_2

/-!
# Part II-b, task `PartII-b:T16/2/2`: `BoxDiffusionAbsorption`

Source of record: `the November 2 reference manuscript`, lines 1963-1977, 1982-1985.

Proves `boxDiffusionAbsorption_proof : BoxDiffusionAbsorption`:
1. Bounds `|cpd 0 χ|` and `|cpd 2 χ|` by `K * Γ` (without assuming `σ ≤ 1` or `1 ≤ H₁`, using
   `0 < σ ≤ H₁` and `σ⁻¹ ≤ Γ`), with `cpd 1 χ = 0`.
2. Expands `Qt`, `Et`, `St` via `vGrad v (χ²) = 2 χ vGrad v χ`, localizes every term to
   `obsBox (σ / 2) (2 * H₁) (L₁ + 1)`, and absorbs `1/4` of the gradient energy from the cutoff
   cross terms and `1/4` from the first diffusion difference term using pointwise Young's inequality.
3. Bounds the remaining terms using the `r = 2` graph bounds (`phys_graph_poly_two_given` and
   `flat_graph_poly_two_given`) and the enlarged-box `H_2` bound `om` on `w = bε - b0`, divides by
   `ν / 2` via `ν⁻¹ ≤ Γ`, and concludes the `χ`-weighted `H_2` gradient bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## 1. First-order derivative bounds for `boxCutoff σ H₁ L₁` (no `σ ≤ 1` assumption) -/

private theorem exists_deriv_smoothTransition_bound :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M := by
  have hcd : ContDiff ℝ (2 : ℕ) Real.smoothTransition := Real.smoothTransition.contDiff
  have hcont : Continuous (deriv Real.smoothTransition) := hcd.continuous_deriv (by decide)
  obtain ⟨M₀, hM₀⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-1 : ℝ) 2) hcont.continuousOn
  refine ⟨max M₀ 1, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-1 : ℝ) 2
  · have h1 := hM₀ t ht
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  · have hzero : deriv Real.smoothTransition t = 0 := by
      rcases not_and_or.mp ht with ht1 | ht2
      · have hlt : t < 0 := by linarith [not_le.mp ht1]
        have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
          Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hlt) fun y hy =>
            Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
      · have hgt : 1 < t := by linarith [not_le.mp ht2]
        have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
          Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hgt) fun y hy =>
            Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
    rw [hzero, abs_zero]
    linarith [le_max_right M₀ 1]

private theorem hasDerivAt_sBoxCut {σ H₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (s : ℝ) :
    HasDerivAt (sBoxCut σ H₁)
      ((deriv Real.smoothTransition ((2 * σ⁻¹) * s - 1) * (2 * σ⁻¹)) *
          Real.smoothTransition ((-H₁⁻¹) * s + 2) +
        Real.smoothTransition ((2 * σ⁻¹) * s - 1) *
          (deriv Real.smoothTransition ((-H₁⁻¹) * s + 2) * (-H₁⁻¹))) s := by
  have hH₁ : 0 < H₁ := lt_of_lt_of_le hσ hσH₁
  have hcd : ContDiff ℝ (2 : ℕ) Real.smoothTransition := Real.smoothTransition.contDiff
  have hst_diff : Differentiable ℝ Real.smoothTransition := hcd.differentiable (by decide)
  have hl1 : HasDerivAt (fun t : ℝ => (2 * σ⁻¹) * t - 1) (2 * σ⁻¹) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 * σ⁻¹)).sub_const (1 : ℝ)
  have hl2 : HasDerivAt (fun t : ℝ => (-H₁⁻¹) * t + 2) (-H₁⁻¹) s := by
    simpa using ((hasDerivAt_id s).const_mul (-H₁⁻¹)).add_const (2 : ℝ)
  have hd1 := (hst_diff _).hasDerivAt.comp s hl1
  have hd2 := (hst_diff _).hasDerivAt.comp s hl2
  have heq : sBoxCut σ H₁ = fun t : ℝ =>
      Real.smoothTransition ((2 * σ⁻¹) * t - 1) * Real.smoothTransition ((-H₁⁻¹) * t + 2) := by
    funext t
    unfold sBoxCut
    have e1 : 2 * t / σ - 1 = (2 * σ⁻¹) * t - 1 := by ring
    have e2 : (2 * H₁ - t) / H₁ = (-H₁⁻¹) * t + 2 := by
      rw [sub_div, mul_div_cancel_right₀ 2 hH₁.ne']
      ring
    rw [e1, e2]
  rw [heq]
  exact hd1.mul hd2

private theorem hasDerivAt_etaBoxCut (L₁ η : ℝ) :
    HasDerivAt (etaBoxCut L₁)
      ((deriv Real.smoothTransition (L₁ + 1 + η) * 1) *
          Real.smoothTransition (L₁ + 1 - η) +
        Real.smoothTransition (L₁ + 1 + η) *
          (deriv Real.smoothTransition (L₁ + 1 - η) * (-1))) η := by
  have hcd : ContDiff ℝ (2 : ℕ) Real.smoothTransition := Real.smoothTransition.contDiff
  have hst_diff : Differentiable ℝ Real.smoothTransition := hcd.differentiable (by decide)
  have hl1 : HasDerivAt (fun t : ℝ => L₁ + 1 + t) 1 η := by
    simpa using (hasDerivAt_id η).const_add (L₁ + 1)
  have hl2 : HasDerivAt (fun t : ℝ => L₁ + 1 - t) (-1) η := by
    have h := ((hasDerivAt_id η).neg).const_add (L₁ + 1)
    simpa [sub_eq_add_neg] using h
  have hd1 := (hst_diff _).hasDerivAt.comp η hl1
  have hd2 := (hst_diff _).hasDerivAt.comp η hl2
  exact hd1.mul hd2

private theorem boxCutoff_cpd_bounds {M : ℝ} (hM1 : 1 ≤ M)
    (hM : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    {σ H₁ L₁ Γ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (hσΓ : σ⁻¹ ≤ Γ) (hΓ1 : 1 ≤ Γ)
    (x : Coord) :
    |cpd 0 (boxCutoff σ H₁ L₁) x| ≤ 3 * M * Γ ∧
      cpd 1 (boxCutoff σ H₁ L₁) x = 0 ∧
      |cpd 2 (boxCutoff σ H₁ L₁) x| ≤ 3 * M * Γ := by
  have hH₁ : 0 < H₁ := lt_of_lt_of_le hσ hσH₁
  have hH₁_inv : H₁⁻¹ ≤ Γ := (inv_anti₀ hσ hσH₁).trans hσΓ
  set L_s : Coord →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  set L_η : Coord →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  set ds := (deriv Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1) * (2 * σ⁻¹)) *
      Real.smoothTransition ((-H₁⁻¹) * x.1 + 2) +
    Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1) *
      (deriv Real.smoothTransition ((-H₁⁻¹) * x.1 + 2) * (-H₁⁻¹))
  set de := (deriv Real.smoothTransition (L₁ + 1 + x.2.2) * 1) *
      Real.smoothTransition (L₁ + 1 - x.2.2) +
    Real.smoothTransition (L₁ + 1 + x.2.2) *
      (deriv Real.smoothTransition (L₁ + 1 - x.2.2) * (-1))
  have hfs : HasFDerivAt (fun y : Coord => sBoxCut σ H₁ y.1) (ds • L_s) x := by
    exact (hasDerivAt_sBoxCut hσ hσH₁ x.1).comp_hasFDerivAt x L_s.hasFDerivAt
  have hfe : HasFDerivAt (fun y : Coord => etaBoxCut L₁ y.2.2) (de • L_η) x := by
    exact (hasDerivAt_etaBoxCut L₁ x.2.2).comp_hasFDerivAt x L_η.hasFDerivAt
  have hf : HasFDerivAt (boxCutoff σ H₁ L₁)
      (sBoxCut σ H₁ x.1 • (de • L_η) + etaBoxCut L₁ x.2.2 • (ds • L_s)) x :=
    hfs.mul hfe
  have hcpd0 : cpd 0 (boxCutoff σ H₁ L₁) x = etaBoxCut L₁ x.2.2 * ds := by
    unfold cpd
    rw [hf.fderiv]
    simp [L_s, L_η, cdir]
  have hcpd1 : cpd 1 (boxCutoff σ H₁ L₁) x = 0 := by
    unfold cpd
    rw [hf.fderiv]
    simp [L_s, L_η, cdir]
  have hcpd2 : cpd 2 (boxCutoff σ H₁ L₁) x = sBoxCut σ H₁ x.1 * de := by
    unfold cpd
    rw [hf.fderiv]
    simp [L_s, L_η, cdir]
  have hds_bd : |ds| ≤ 3 * M * Γ := by
    have b1 := hM ((2 * σ⁻¹) * x.1 - 1)
    have b2 := hM ((-H₁⁻¹) * x.1 + 2)
    have s1_0 := Real.smoothTransition.nonneg ((-H₁⁻¹) * x.1 + 2)
    have s1_1 := Real.smoothTransition.le_one ((-H₁⁻¹) * x.1 + 2)
    have s2_0 := Real.smoothTransition.nonneg ((2 * σ⁻¹) * x.1 - 1)
    have s2_1 := Real.smoothTransition.le_one ((2 * σ⁻¹) * x.1 - 1)
    have h2σ_pos : 0 ≤ 2 * σ⁻¹ := by positivity
    have hH₁i_pos : 0 ≤ H₁⁻¹ := inv_nonneg.mpr hH₁.le
    calc |ds|
        ≤ |(deriv Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1) * (2 * σ⁻¹)) *
              Real.smoothTransition ((-H₁⁻¹) * x.1 + 2)| +
            |Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1) *
              (deriv Real.smoothTransition ((-H₁⁻¹) * x.1 + 2) * (-H₁⁻¹))| := abs_add_le _ _
      _ = |deriv Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1)| * (2 * σ⁻¹) *
              Real.smoothTransition ((-H₁⁻¹) * x.1 + 2) +
            Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1) *
              (|deriv Real.smoothTransition ((-H₁⁻¹) * x.1 + 2)| * H₁⁻¹) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h2σ_pos, abs_of_nonneg s1_0,
            abs_mul, abs_mul, abs_of_nonneg s2_0, abs_neg, abs_of_nonneg hH₁i_pos]
      _ ≤ M * (2 * Γ) * 1 + 1 * (M * Γ) := by
          have p1 : |deriv Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1)| * (2 * σ⁻¹) ≤ M * (2 * Γ) :=
            mul_le_mul b1 (by linarith) h2σ_pos (by linarith)
          have p1' : |deriv Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1)| * (2 * σ⁻¹) *
              Real.smoothTransition ((-H₁⁻¹) * x.1 + 2) ≤ (M * (2 * Γ)) * 1 :=
            mul_le_mul p1 s1_1 s1_0 (by positivity)
          have p2 : |deriv Real.smoothTransition ((-H₁⁻¹) * x.1 + 2)| * H₁⁻¹ ≤ M * Γ :=
            mul_le_mul b2 hH₁_inv hH₁i_pos (by linarith)
          have p2' : Real.smoothTransition ((2 * σ⁻¹) * x.1 - 1) *
              (|deriv Real.smoothTransition ((-H₁⁻¹) * x.1 + 2)| * H₁⁻¹) ≤ 1 * (M * Γ) :=
            mul_le_mul s2_1 p2 (by positivity) zero_le_one
          linarith
      _ = 3 * M * Γ := by ring
  have hde_bd : |de| ≤ 3 * M * Γ := by
    have b1 := hM (L₁ + 1 + x.2.2)
    have b2 := hM (L₁ + 1 - x.2.2)
    have e1_0 := Real.smoothTransition.nonneg (L₁ + 1 - x.2.2)
    have e1_1 := Real.smoothTransition.le_one (L₁ + 1 - x.2.2)
    have e2_0 := Real.smoothTransition.nonneg (L₁ + 1 + x.2.2)
    have e2_1 := Real.smoothTransition.le_one (L₁ + 1 + x.2.2)
    calc |de|
        ≤ |(deriv Real.smoothTransition (L₁ + 1 + x.2.2) * 1) *
              Real.smoothTransition (L₁ + 1 - x.2.2)| +
            |Real.smoothTransition (L₁ + 1 + x.2.2) *
              (deriv Real.smoothTransition (L₁ + 1 - x.2.2) * (-1))| := abs_add_le _ _
      _ = |deriv Real.smoothTransition (L₁ + 1 + x.2.2)| * Real.smoothTransition (L₁ + 1 - x.2.2) +
            Real.smoothTransition (L₁ + 1 + x.2.2) *
              |deriv Real.smoothTransition (L₁ + 1 - x.2.2)| := by
          rw [mul_one, abs_mul, abs_of_nonneg e1_0, abs_mul, abs_mul, abs_of_nonneg e2_0,
            abs_neg, abs_one, mul_one]
      _ ≤ M * 1 + 1 * M :=
          add_le_add (mul_le_mul b1 e1_1 e1_0 (by linarith))
            (mul_le_mul e2_1 b2 (abs_nonneg _) zero_le_one)
      _ ≤ 3 * M * Γ := by nlinarith
  refine ⟨?_, hcpd1, ?_⟩
  · rw [hcpd0, abs_mul, abs_of_nonneg (etaBoxCut_nonneg L₁ x.2.2)]
    calc etaBoxCut L₁ x.2.2 * |ds| ≤ 1 * (3 * M * Γ) :=
          mul_le_mul (etaBoxCut_le_one L₁ x.2.2) hds_bd (abs_nonneg _) zero_le_one
      _ = 3 * M * Γ := one_mul _
  · rw [hcpd2, abs_mul, abs_of_nonneg (sBoxCut_nonneg σ H₁ x.1)]
    calc sBoxCut σ H₁ x.1 * |de| ≤ 1 * (3 * M * Γ) :=
          mul_le_mul (sBoxCut_le_one σ H₁ x.1) hde_bd (abs_nonneg _) zero_le_one
      _ = 3 * M * Γ := one_mul _

/-! ## 2. `vGrad` of `χ²` and enlarged-box bounds -/

private theorem cpd_sq (j : Fin 3) {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : Coord) :
    cpd j (fun y => χ y ^ 2) x = 2 * χ x * cpd j χ x := by
  have hd : DifferentiableAt ℝ χ x := (hχ.differentiable (by simp)) x
  have h : HasFDerivAt (fun y => χ y ^ 2) ((2 * χ x) • fderiv ℝ χ x) x := by
    simpa [pow_one] using hd.hasFDerivAt.pow 2
  unfold cpd
  rw [h.fderiv]
  simp [mul_assoc]

private theorem vGrad_sq (v : Coord → Fin 3 → ℝ) {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (x : Coord) :
    vGrad v (fun y => χ y ^ 2) x = 2 * χ x * vGrad v χ x := by
  unfold vGrad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cpd_sq j hχ x]
  ring

private theorem enl_coord_bounds {σ H₁ L₁ Γ : ℝ} (hσ : 0 < σ) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ)
    (hΓ1 : 1 ≤ Γ) {x : Coord} (hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)) :
    0 < x.1 ∧ x.1 ≤ 2 * Γ ∧ Real.sqrt x.1 ≤ 2 * Γ ∧ |x.2.2| ≤ 2 * Γ := by
  have hx1_pos : 0 < x.1 := lt_of_lt_of_le (half_pos hσ) hx.1.1
  have hx1_le : x.1 ≤ 2 * Γ := hx.1.2.trans (by linarith)
  have hsq : Real.sqrt x.1 ≤ 2 * Γ := by
    calc Real.sqrt x.1 ≤ Real.sqrt ((2 * Γ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Γ := Real.sqrt_sq (by linarith)
  have hη : |x.2.2| ≤ 2 * Γ := (abs_le.mpr hx.2.2).trans (by linarith)
  exact ⟨hx1_pos, hx1_le, hsq, hη⟩

private theorem vGrad_boxCutoff_enl_bounds {K σ H₁ L₁ Γ ε : ℝ}
    (hK : 0 ≤ K) (hσ : 0 < σ) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ) (hΓ1 : 1 ≤ Γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {χ : Coord → ℝ}
    (hcpd : ∀ y, |cpd 0 χ y| ≤ K * Γ ∧ cpd 1 χ y = 0 ∧ |cpd 2 χ y| ≤ K * Γ)
    {x : Coord} (hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)) :
    |2 * Real.sqrt x.1 * vGrad (vQ ε) χ x| ≤ 24 * K * Γ ^ 3 ∧
      |2 * Real.sqrt x.1 * vGrad vEta χ x| ≤ 24 * K * Γ ^ 3 ∧
      |2 * vGrad vS χ x| ≤ 4 * K * Γ ^ 2 := by
  obtain ⟨hx1_pos, hx1_le, hsq, hη⟩ := enl_coord_bounds hσ hH₁ hL₁ hΓ1 hx
  obtain ⟨hc0, hc1, hc2⟩ := hcpd x
  have hvQ : |vGrad (vQ ε) χ x| ≤ 6 * K * Γ ^ 2 := by
    unfold vGrad
    rw [Fin.sum_univ_three]
    change |(-2 * ε * x.1) * cpd 0 χ x + 1 * cpd 1 χ x + (-ε * x.2.2) * cpd 2 χ x| ≤ _
    rw [hc1, mul_zero, add_zero]
    have e1 : |(-2 * ε * x.1) * cpd 0 χ x| = (2 * ε * x.1) * |cpd 0 χ x| := by
      rw [show (-2 * ε * x.1) * cpd 0 χ x = -((2 * ε * x.1) * cpd 0 χ x) by ring,
        abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε * x.1)]
    have e2 : |(-ε * x.2.2) * cpd 2 χ x| = (ε * |x.2.2|) * |cpd 2 χ x| := by
      rw [show (-ε * x.2.2) * cpd 2 χ x = -((ε * x.2.2) * cpd 2 χ x) by ring,
        abs_neg, abs_mul, abs_mul, abs_of_nonneg hε0.le]
    calc |(-2 * ε * x.1) * cpd 0 χ x + (-ε * x.2.2) * cpd 2 χ x|
        ≤ |(-2 * ε * x.1) * cpd 0 χ x| + |(-ε * x.2.2) * cpd 2 χ x| := abs_add_le _ _
      _ = (2 * ε * x.1) * |cpd 0 χ x| + (ε * |x.2.2|) * |cpd 2 χ x| := by rw [e1, e2]
      _ ≤ (2 * 1 * (2 * Γ)) * (K * Γ) + (1 * (2 * Γ)) * (K * Γ) := by
          have p1 : 2 * ε * x.1 ≤ 2 * 1 * (2 * Γ) := by nlinarith
          have p2 : ε * |x.2.2| ≤ 1 * (2 * Γ) :=
            mul_le_mul hε1 hη (abs_nonneg _) zero_le_one
          exact add_le_add
            (mul_le_mul p1 hc0 (abs_nonneg _) (by positivity))
            (mul_le_mul p2 hc2 (abs_nonneg _) (by positivity))
      _ = 6 * K * Γ ^ 2 := by ring
  have hvE : |vGrad vEta χ x| ≤ K * Γ := by
    unfold vGrad
    rw [Fin.sum_univ_three]
    change |0 * cpd 0 χ x + 0 * cpd 1 χ x + 1 * cpd 2 χ x| ≤ _
    simpa using hc2
  have hvS : |vGrad vS χ x| ≤ 2 * K * Γ ^ 2 := by
    unfold vGrad
    rw [Fin.sum_univ_three]
    change |x.1 * cpd 0 χ x + 0 * cpd 1 χ x + 0 * cpd 2 χ x| ≤ _
    simp only [zero_mul, add_zero, abs_mul, abs_of_pos hx1_pos]
    calc x.1 * |cpd 0 χ x| ≤ (2 * Γ) * (K * Γ) :=
          mul_le_mul hx1_le hc0 (abs_nonneg _) (by positivity)
      _ = 2 * K * Γ ^ 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc 2 * Real.sqrt x.1 * |vGrad (vQ ε) χ x|
        ≤ (2 * (2 * Γ)) * (6 * K * Γ ^ 2) :=
          mul_le_mul (by linarith) hvQ (abs_nonneg _) (by positivity)
      _ = 24 * K * Γ ^ 3 := by ring
  · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hKΓ : K * Γ ≤ 6 * K * Γ ^ 2 := by
      have h1 : K * Γ ≤ K * Γ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hK
      have h2 : 0 ≤ K * Γ ^ 2 := by positivity
      linarith
    calc 2 * Real.sqrt x.1 * |vGrad vEta χ x|
        ≤ (2 * (2 * Γ)) * (6 * K * Γ ^ 2) :=
          mul_le_mul (by linarith) (hvE.trans hKΓ) (abs_nonneg _) (by positivity)
      _ = 24 * K * Γ ^ 3 := by ring
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc 2 * |vGrad vS χ x| ≤ 2 * (2 * K * Γ ^ 2) :=
          mul_le_mul_of_nonneg_left hvS (by norm_num)
      _ = 4 * K * Γ ^ 2 := by ring

/-! ## 3. Euclidean `Fin 2` Cauchy-Schwarz & `L²(hMeas c 2)` norm-squared bridge -/

private theorem le_of_sq_le_sq_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (abs_le_of_sq_le_sq' h hb).2

private theorem cmerid_norm_sq (v : CMerid) : ‖v‖ ^ 2 = ∑ i : Fin 2, ‖v i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq v

private theorem cmerid_inner_norm_le (a b : CMerid) :
    ‖∑ i : Fin 2, a i * (starRingEnd ℂ) (b i)‖ ≤ ‖a‖ * ‖b‖ := by
  have ha : ‖a‖ ^ 2 = ‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 := by
    rw [cmerid_norm_sq, Fin.sum_univ_two]
  have hb : ‖b‖ ^ 2 = ‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 := by
    rw [cmerid_norm_sq, Fin.sum_univ_two]
  have htri : ‖∑ i : Fin 2, a i * (starRingEnd ℂ) (b i)‖ ≤
      ‖a 0‖ * ‖b 0‖ + ‖a 1‖ * ‖b 1‖ := by
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ?_
    simp
  have hcs : (‖a 0‖ * ‖b 0‖ + ‖a 1‖ * ‖b 1‖) ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    have hprod : (‖a‖ * ‖b‖) ^ 2 = (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2) := by
      rw [mul_pow, ha, hb]
    rw [hprod]
    nlinarith [sq_nonneg (‖a 0‖ * ‖b 1‖ - ‖a 1‖ * ‖b 0‖)]
  exact htri.trans (le_of_sq_le_sq_nonneg (mul_nonneg (norm_nonneg a) (norm_nonneg b)) hcs)

private theorem hNorm_two_eq (c : ℝ) (u : CProf) :
    hNorm c 2 u = eLpNorm u 2 (hMeas c 2) := by
  unfold hNorm
  rw [ENNReal.ofReal_ofNat]

private theorem integral_norm_sq_eq_toReal_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {u : α → E}
    (hu_meas : AEStronglyMeasurable u μ) (hu_fin : eLpNorm u 2 μ < ⊤) :
    Integrable (fun x => ‖u x‖ ^ 2) μ ∧
      ∫ x, ‖u x‖ ^ 2 ∂μ = (eLpNorm u 2 μ).toReal ^ 2 := by
  have hmem : MemLp u 2 μ := ⟨hu_meas, hu_fin⟩
  have hint : Integrable (fun x => ‖u x‖ ^ 2) μ := hmem.integrable_norm_pow (by norm_num)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg ‖u x‖)
    (hu_meas.norm.pow 2)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  have hcongr : (fun x => ENNReal.ofReal (‖u x‖ ^ 2)) = fun x => ‖u x‖ₑ ^ (2 : ℝ) := by
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
    norm_num
  rw [hcongr, ← ENNReal.toReal_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

private theorem integral_sq_le_of_eLpNorm_le {c A : ℝ} (hA : 0 ≤ A)
    {f : Coord → ℝ} (hf_meas : AEStronglyMeasurable f (hMeas c 2))
    (hf_bd : eLpNorm f (ENNReal.ofReal 2) (hMeas c 2) ≤ ENNReal.ofReal A) :
    Integrable (fun x => f x ^ 2) (hMeas c 2) ∧
      ∫ x, f x ^ 2 ∂(hMeas c 2) ≤ A ^ 2 := by
  rw [ENNReal.ofReal_ofNat] at hf_bd
  have hfin : eLpNorm f 2 (hMeas c 2) < ⊤ := lt_of_le_of_lt hf_bd ENNReal.ofReal_lt_top
  obtain ⟨hint_norm, heq⟩ := integral_norm_sq_eq_toReal_sq hf_meas hfin
  have hsq_eq : (fun x => f x ^ 2) = fun x => ‖f x‖ ^ 2 := by
    funext x
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsq_eq]
  refine ⟨hint_norm, ?_⟩
  rw [heq]
  have hle : (eLpNorm f 2 (hMeas c 2)).toReal ≤ A := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hf_bd
    rwa [ENNReal.toReal_ofReal hA] at this
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2

private theorem eLpNorm_two_lt_top_of_norm_le {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure α}
    {u : α → E} {v : α → F} {C : ℝ}
    (hpt : ∀ x, ‖u x‖ ≤ C * ‖v x‖) (hv : eLpNorm v 2 μ < ⊤) :
    eLpNorm u 2 μ < ⊤ := by
  have h1 : eLpNorm u 2 μ ≤ eLpNorm (C • fun x => ‖v x‖) 2 μ :=
    eLpNorm_mono_real fun x => by simpa [Pi.smul_apply, smul_eq_mul] using hpt x
  refine lt_of_le_of_lt h1 ?_
  rw [eLpNorm_const_smul, eLpNorm_norm]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hv

/-! ## 4. LHS quadratic + cross-term expansion on `hMeas c 2` -/

private theorem lhs_pairing_lower_bound {c σ H₁ L₁ : ℝ}
    (hσ : 0 < σ) (hσH₁ : σ ≤ H₁)
    (v : Coord → Fin 3 → ℝ) (w Dw : CProf)
    (hg_meas : AEStronglyMeasurable (fun x => (boxCutoff σ H₁ L₁ x : ℂ) • sqrtS Dw x) (hMeas c 2))
    (hg_fin : eLpNorm (fun x => (boxCutoff σ H₁ L₁ x : ℂ) • sqrtS Dw x) 2 (hMeas c 2) < ⊤)
    (hr_meas : AEStronglyMeasurable
      (fun x => (((2 * Real.sqrt x.1 * vGrad v (boxCutoff σ H₁ L₁) x : ℝ) : ℂ)) •
        indBox (σ / 2) (2 * H₁) (L₁ + 1) w x) (hMeas c 2))
    (hr_fin : eLpNorm
      (fun x => (((2 * Real.sqrt x.1 * vGrad v (boxCutoff σ H₁ L₁) x : ℝ) : ℂ)) •
        indBox (σ / 2) (2 * H₁) (L₁ + 1) w x) 2 (hMeas c 2) < ⊤) :
    let χ := boxCutoff σ H₁ L₁
    let ψ := fun x : Coord => χ x ^ 2
    let Dt := weakSmul v ψ w Dw
    let g : CProf := fun x => (χ x : ℂ) • sqrtS Dw x
    let r : CProf := fun x =>
      (((2 * Real.sqrt x.1 * vGrad v χ x : ℝ) : ℂ)) • indBox (σ / 2) (2 * H₁) (L₁ + 1) w x
    (3 / 4) * ∫ x, ‖g x‖ ^ 2 ∂(hMeas c 2) - ∫ x, ‖r x‖ ^ 2 ∂(hMeas c 2) ≤
      (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Dw x i * (starRingEnd ℂ) (Dt x i) ∂(hMeas c 2)).re := by
  intro χ ψ Dt g r
  have hχ_cd : ContDiff ℝ ∞ χ := boxCutoff_contDiff σ H₁ L₁
  obtain ⟨hint_g, _⟩ := integral_norm_sq_eq_toReal_sq hg_meas hg_fin
  obtain ⟨hint_r, _⟩ := integral_norm_sq_eq_toReal_sq hr_meas hr_fin
  set z : Coord → ℂ := fun x =>
    ((‖g x‖ ^ 2 : ℝ) : ℂ) + ∑ i : Fin 2, g x i * (starRingEnd ℂ) (r x i)
  have hpt_eq : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2, Dw x i * (starRingEnd ℂ) (Dt x i)) = z := by
    funext x
    by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
    · have hs0 : 0 ≤ x.1 := le_trans (half_pos hσ).le hx.1.1
      have hsq_s : (Real.sqrt x.1 : ℂ) * (Real.sqrt x.1 : ℂ) = (x.1 : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt hs0
      have hw_eq : indBox (σ / 2) (2 * H₁) (L₁ + 1) w x = w x := by
        unfold indBox
        exact Set.indicator_of_mem hx _
      have hv_eq : vGrad v ψ x = 2 * χ x * vGrad v χ x := vGrad_sq v hχ_cd x
      dsimp only [z]
      rw [cmerid_norm_sq (g x), Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hgi : g x i = (χ x : ℂ) * ((Real.sqrt x.1 : ℂ) * Dw x i) := by
        simp [g, sqrtS]
      have hri : r x i = (((2 * Real.sqrt x.1 * vGrad v χ x : ℝ) : ℂ)) * w x i := by
        simp [r, hw_eq]
      have hDti : Dt x i = ((χ x ^ 2 : ℝ) : ℂ) * Dw x i +
          ((2 * χ x * vGrad v χ x : ℝ) : ℂ) * w x i := by
        change ((ψ x : ℂ) • Dw x + (vGrad v ψ x : ℂ) • w x) i = _
        simp [ψ, hv_eq]
      have hnorm_gi : ((‖g x i‖ ^ 2 : ℝ) : ℂ) = g x i * (starRingEnd ℂ) (g x i) := by
        push_cast
        exact (Complex.mul_conj' (g x i)).symm
      rw [hDti, hnorm_gi, hgi, hri, ← hsq_s]
      push_cast
      simp only [map_add, map_mul, map_pow, map_ofNat, Complex.conj_ofReal]
      ring
    · have hχ0 : χ x = 0 := boxCutoff_eq_zero_of_notMem hσ hσH₁ hx
      have hψ0 : ψ x = 0 := by simp [ψ, hχ0]
      have hvg0 : vGrad v ψ x = 0 := by rw [vGrad_sq v hχ_cd x, hχ0]; ring
      have hw0 : indBox (σ / 2) (2 * H₁) (L₁ + 1) w x = 0 := by
        unfold indBox
        exact Set.indicator_of_notMem hx _
      have hg0 : g x = 0 := by simp [g, hχ0]
      have hr0 : r x = 0 := by simp [r, hw0]
      have hDt0 : Dt x = 0 := by simp [Dt, weakSmul, hψ0, hvg0]
      simp [z, hg0, hr0, hDt0]
  have hz_meas : AEStronglyMeasurable z (hMeas c 2) := by
    have hm1 : AEStronglyMeasurable (fun x : Coord => ((‖g x‖ ^ 2 : ℝ) : ℂ)) (hMeas c 2) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hg_meas.norm.pow 2)
    have hm2 : ∀ i : Fin 2, AEStronglyMeasurable
        (fun x : Coord => g x i * (starRingEnd ℂ) (r x i)) (hMeas c 2) := by
      intro i
      have hgi : AEStronglyMeasurable (fun x => g x i) (hMeas c 2) :=
        (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hg_meas
      have hri : AEStronglyMeasurable (fun x => r x i) (hMeas c 2) :=
        (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hr_meas
      exact hgi.mul (Complex.continuous_conj.comp_aestronglyMeasurable hri)
    exact hm1.add (Finset.aestronglyMeasurable_sum Finset.univ fun i _ => hm2 i)
  have hz_int : Integrable z (hMeas c 2) := by
    refine Integrable.mono' ((hint_g.const_mul 2).add hint_r) hz_meas (ae_of_all _ fun x => ?_)
    dsimp only [z]
    have hcs := cmerid_inner_norm_le (g x) (r x)
    calc ‖((‖g x‖ ^ 2 : ℝ) : ℂ) + ∑ i : Fin 2, g x i * (starRingEnd ℂ) (r x i)‖
        ≤ ‖((‖g x‖ ^ 2 : ℝ) : ℂ)‖ + ‖∑ i : Fin 2, g x i * (starRingEnd ℂ) (r x i)‖ :=
          norm_add_le _ _
      _ ≤ ‖g x‖ ^ 2 + ‖g x‖ * ‖r x‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
          exact add_le_add le_rfl hcs
      _ ≤ 2 * ‖g x‖ ^ 2 + ‖r x‖ ^ 2 := by
          nlinarith [sq_nonneg (‖g x‖ - ‖r x‖)]
  rw [hpt_eq]
  have hre_comm : (∫ x, z x ∂(hMeas c 2)).re = ∫ x, (z x).re ∂(hMeas c 2) :=
    (Complex.reCLM.integral_comp_comm hz_int).symm
  rw [hre_comm, ← integral_const_mul, ← integral_sub (hint_g.const_mul _) hint_r]
  refine integral_mono (hint_g.const_mul (3 / 4) |>.sub hint_r) (Complex.reCLM.integrable_comp hz_int)
    fun x => ?_
  dsimp only [z, Complex.reCLM_apply]
  rw [Complex.add_re, Complex.ofReal_re]
  have hcs : |(∑ i : Fin 2, g x i * (starRingEnd ℂ) (r x i)).re| ≤ ‖g x‖ * ‖r x‖ :=
    (Complex.abs_re_le_norm _).trans (cmerid_inner_norm_le (g x) (r x))
  have hlow : -(‖g x‖ * ‖r x‖) ≤ (∑ i : Fin 2, g x i * (starRingEnd ℂ) (r x i)).re :=
    (abs_le.mp hcs).1
  nlinarith [sq_nonneg ((1 / 2 : ℝ) * ‖g x‖ - ‖r x‖)]

/-! ## 5. Pointwise Young bound on the combined diffusion-difference integrand -/

private theorem diff_integrand_pointwise_bound {K σ H₁ L₁ Γ ε : ℝ}
    (hK3 : 3 ≤ K) (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ)
    (hΓ1 : 1 ≤ Γ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf)
    (hcpd : ∀ y, |cpd 0 (boxCutoff σ H₁ L₁) y| ≤ K * Γ ∧
      cpd 1 (boxCutoff σ H₁ L₁) y = 0 ∧ |cpd 2 (boxCutoff σ H₁ L₁) y| ≤ K * Γ)
    (x : Coord) :
    let χ := boxCutoff σ H₁ L₁
    let ψ := fun y : Coord => χ y ^ 2
    let w := bε - b0
    let Sw := Sbε - Sb0
    let Qv := qepsOf ε b0 Sb0 Qb0 Eb0
    let Qw := Qbε - Qv
    let Ew := Ebε - Eb0
    let t : CProf := fun y => (ψ y : ℂ) • w y
    let St := weakSmul vS ψ w Sw
    let Qt := weakSmul (vQ ε) ψ w Qw
    let Et := weakSmul vEta ψ w Ew
    let gQ : CProf := fun y => (χ y : ℂ) • sqrtS Qw y
    let rq : CProf := fun y =>
      (((2 * Real.sqrt y.1 * vGrad (vQ ε) χ y : ℝ) : ℂ)) •
        indBox (σ / 2) (2 * H₁) (L₁ + 1) w y
    let fε : Coord → ℝ := fun y => ‖bε y‖ + ‖Sbε y‖ + ‖sqrtS Qbε y‖ + ‖sqrtS Ebε y‖
    let f0 : Coord → ℝ := fun y => ‖b0 y‖ + ‖Sb0 y‖ + ‖sqrtS Qb0 y‖ + ‖sqrtS Eb0 y‖
    ε * ‖(x.1 : ℂ) * ∑ i : Fin 2,
          ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
            Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))‖ ≤
      (1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 +
        168 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) := by
  intro χ ψ w Sw Qv Qw Ew t St Qt Et gQ rq fε f0
  have hK0 : 0 ≤ K := by linarith
  have hχ_cd : ContDiff ℝ ∞ χ := boxCutoff_contDiff σ H₁ L₁
  by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
  · obtain ⟨hx1_pos, hx1_le, hsq, hη⟩ := enl_coord_bounds hσ hH₁ hL₁ hΓ1 hx
    obtain ⟨-, hbe, hbS⟩ := vGrad_boxCutoff_enl_bounds hK0 hσ hH₁ hL₁ hΓ1 hε0 hε1 hcpd hx
    have hχ0 : 0 ≤ χ x := boxCutoff_nonneg σ H₁ L₁ x
    have hχ1 : χ x ≤ 1 := boxCutoff_le_one σ H₁ L₁ x
    have hψ0 : 0 ≤ ψ x := sq_nonneg _
    have hψ1 : ψ x ≤ 1 := by
      dsimp only [ψ]
      simpa using pow_le_pow_left₀ hχ0 hχ1 2
    have hw_eq : indBox (σ / 2) (2 * H₁) (L₁ + 1) w x = w x := by
      unfold indBox; exact Set.indicator_of_mem hx _
    have hsq_s : (Real.sqrt x.1 : ℂ) * (Real.sqrt x.1 : ℂ) = (x.1 : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hx1_pos.le
    set A1 : CMerid := (Real.sqrt x.1 : ℂ) •
      ((2 : ℂ) • Sb0 x + (x.2.2 : ℂ) • Eb0 x + b0 x)
    set B1 : CMerid := (Real.sqrt x.1 : ℂ) • Qt x
    set A2 : CMerid := sqrtS Qb0 x
    set B2 : CMerid := (Real.sqrt x.1 : ℂ) •
      ((2 : ℂ) • St x + (x.2.2 : ℂ) • Et x + t x)
    have hZ_eq : (x.1 : ℂ) * ∑ i : Fin 2,
          ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
            Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i)) =
        (∑ i : Fin 2, A1 i * (starRingEnd ℂ) (B1 i)) +
          (∑ i : Fin 2, A2 i * (starRingEnd ℂ) (B2 i)) := by
      rw [← hsq_s, Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [A1, B1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
          map_mul, Complex.conj_ofReal]
        ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [A2, B2, sqrtS, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
          map_mul, Complex.conj_ofReal]
        ring
    have hZ_norm : ‖(x.1 : ℂ) * ∑ i : Fin 2,
          ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
            Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))‖ ≤
        ‖A1‖ * ‖B1‖ + ‖A2‖ * ‖B2‖ := by
      rw [hZ_eq]
      exact (norm_add_le _ _).trans
        (add_le_add (cmerid_inner_norm_le A1 B1) (cmerid_inner_norm_le A2 B2))
    have hA1_bd : ‖A1‖ ≤ 4 * Γ * f0 x := by
      have heq : A1 = (2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x := by
        ext i; simp [A1, sqrtS]; ring
      rw [heq]
      have nS : ‖sqrtS Sb0 x‖ ≤ 2 * Γ * ‖Sb0 x‖ := by
        rw [norm_sqrtS]; exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
      have nB : ‖sqrtS b0 x‖ ≤ 2 * Γ * ‖b0 x‖ := by
        rw [norm_sqrtS]; exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
      have nE : ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ ≤ 2 * Γ * ‖sqrtS Eb0 x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hη (norm_nonneg _)
      have htri : ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖ ≤
          2 * ‖sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ := by
        calc ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖
            ≤ ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ :=
              norm_add_le _ _
          _ ≤ ‖(2 : ℂ) • sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ :=
              add_le_add (norm_add_le _ _) le_rfl
          _ = 2 * ‖sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ := by
              simp [norm_smul]
      have pB : 2 * Γ * ‖b0 x‖ ≤ 4 * Γ * ‖b0 x‖ :=
        mul_le_mul_of_nonneg_right (by linarith only [hΓ1]) (norm_nonneg _)
      have pE : 2 * Γ * ‖sqrtS Eb0 x‖ ≤ 4 * Γ * ‖sqrtS Eb0 x‖ :=
        mul_le_mul_of_nonneg_right (by linarith only [hΓ1]) (norm_nonneg _)
      have pQ : 0 ≤ 4 * Γ * ‖sqrtS Qb0 x‖ :=
        mul_nonneg (by linarith only [hΓ1]) (norm_nonneg _)
      dsimp only [f0]
      linarith only [htri, nS, nB, nE, pB, pE, pQ]
    have hB1_bd : ‖B1‖ ≤ ‖gQ x‖ + ‖rq x‖ := by
      have hv_eq : vGrad (vQ ε) ψ x = 2 * χ x * vGrad (vQ ε) χ x :=
        vGrad_sq (vQ ε) hχ_cd x
      have heq : B1 = (χ x : ℂ) • gQ x + (χ x : ℂ) • rq x := by
        ext i
        change (Real.sqrt x.1 : ℂ) * (((ψ x : ℂ) • Qw x + (vGrad (vQ ε) ψ x : ℂ) • w x) i) = _
        simp only [gQ, rq, sqrtS, ψ, hv_eq, hw_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [heq]
      calc ‖(χ x : ℂ) • gQ x + (χ x : ℂ) • rq x‖
          ≤ ‖(χ x : ℂ) • gQ x‖ + ‖(χ x : ℂ) • rq x‖ := norm_add_le _ _
        _ = χ x * ‖gQ x‖ + χ x * ‖rq x‖ := by
            simp [norm_smul, Real.norm_of_nonneg hχ0]
        _ ≤ 1 * ‖gQ x‖ + 1 * ‖rq x‖ :=
            add_le_add (mul_le_mul_of_nonneg_right hχ1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_right hχ1 (norm_nonneg _))
        _ = ‖gQ x‖ + ‖rq x‖ := by ring
    have hA2_bd : ‖A2‖ ≤ f0 x := by
      dsimp only [A2, f0]
      have n1 := norm_nonneg (b0 x)
      have n2 := norm_nonneg (Sb0 x)
      have n3 := norm_nonneg (sqrtS Eb0 x)
      linarith only [n1, n2, n3]
    have hB2_bd : ‖B2‖ ≤ 72 * K * Γ ^ 4 * (fε x + f0 x) := by
      have hvS_eq : vGrad vS ψ x = 2 * χ x * vGrad vS χ x := vGrad_sq vS hχ_cd x
      have hvE_eq : vGrad vEta ψ x = 2 * χ x * vGrad vEta χ x := vGrad_sq vEta hχ_cd x
      have nw : ‖w x‖ ≤ fε x + f0 x := by
        have hsub : ‖w x‖ ≤ ‖bε x‖ + ‖b0 x‖ := by
          dsimp only [w]
          rw [Pi.sub_apply]
          exact norm_sub_le _ _
        dsimp only [fε, f0]
        have n1 := norm_nonneg (Sbε x); have n2 := norm_nonneg (sqrtS Qbε x)
        have n3 := norm_nonneg (sqrtS Ebε x); have n4 := norm_nonneg (Sb0 x)
        have n5 := norm_nonneg (sqrtS Qb0 x); have n6 := norm_nonneg (sqrtS Eb0 x)
        linarith only [hsub, n1, n2, n3, n4, n5, n6]
      have nSw : ‖Sw x‖ ≤ fε x + f0 x := by
        have hsub : ‖Sw x‖ ≤ ‖Sbε x‖ + ‖Sb0 x‖ := by
          dsimp only [Sw]
          rw [Pi.sub_apply]
          exact norm_sub_le _ _
        dsimp only [fε, f0]
        have n1 := norm_nonneg (bε x); have n2 := norm_nonneg (sqrtS Qbε x)
        have n3 := norm_nonneg (sqrtS Ebε x); have n4 := norm_nonneg (b0 x)
        have n5 := norm_nonneg (sqrtS Qb0 x); have n6 := norm_nonneg (sqrtS Eb0 x)
        linarith only [hsub, n1, n2, n3, n4, n5, n6]
      have nEw : ‖sqrtS Ew x‖ ≤ fε x + f0 x := by
        have hsub : ‖sqrtS Ew x‖ ≤ ‖sqrtS Ebε x‖ + ‖sqrtS Eb0 x‖ := by
          have hsp : sqrtS Ew x = sqrtS Ebε x - sqrtS Eb0 x :=
            congrFun (flatCls_sqrtS_sub Ebε Eb0) x
          rw [hsp]
          exact norm_sub_le _ _
        dsimp only [fε, f0]
        have n1 := norm_nonneg (bε x); have n2 := norm_nonneg (Sbε x)
        have n3 := norm_nonneg (sqrtS Qbε x); have n4 := norm_nonneg (b0 x)
        have n5 := norm_nonneg (Sb0 x); have n6 := norm_nonneg (sqrtS Qb0 x)
        linarith only [hsub, n1, n2, n3, n4, n5, n6]
      have p_St : ‖(Real.sqrt x.1 : ℂ) • ((2 : ℂ) • St x)‖ ≤
          (4 * Γ + 16 * K * Γ ^ 3) * (fε x + f0 x) := by
        have heq : (Real.sqrt x.1 : ℂ) • ((2 : ℂ) • St x) =
            (((2 * Real.sqrt x.1 * ψ x : ℝ) : ℂ)) • Sw x +
              (((2 * Real.sqrt x.1 * χ x * (2 * vGrad vS χ x) : ℝ) : ℂ)) • w x := by
          ext i
          change (Real.sqrt x.1 : ℂ) * ((2 : ℂ) *
            (((ψ x : ℂ) • Sw x + (vGrad vS ψ x : ℂ) • w x) i)) = _
          simp only [hvS_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          push_cast; ring
        rw [heq]
        have h2sq : 2 * Real.sqrt x.1 ≤ 4 * Γ := by linarith only [hsq]
        have c1 : |2 * Real.sqrt x.1 * ψ x| ≤ 4 * Γ := by
          rw [abs_of_nonneg (by positivity)]
          calc (2 * Real.sqrt x.1) * ψ x ≤ (4 * Γ) * 1 :=
                mul_le_mul h2sq hψ1 hψ0 (by positivity)
            _ = 4 * Γ := mul_one _
        have c2 : |2 * Real.sqrt x.1 * χ x * (2 * vGrad vS χ x)| ≤ 16 * K * Γ ^ 3 := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt x.1 * χ x)]
          have p1 : 2 * Real.sqrt x.1 * χ x ≤ 4 * Γ := by
            calc (2 * Real.sqrt x.1) * χ x ≤ (4 * Γ) * 1 :=
                  mul_le_mul h2sq hχ1 hχ0 (by positivity)
              _ = 4 * Γ := mul_one _
          calc (2 * Real.sqrt x.1 * χ x) * |2 * vGrad vS χ x|
              ≤ (4 * Γ) * (4 * K * Γ ^ 2) :=
                mul_le_mul p1 hbS (abs_nonneg _) (by positivity)
            _ = 16 * K * Γ ^ 3 := by ring
        calc ‖(((2 * Real.sqrt x.1 * ψ x : ℝ) : ℂ)) • Sw x +
              (((2 * Real.sqrt x.1 * χ x * (2 * vGrad vS χ x) : ℝ) : ℂ)) • w x‖
            ≤ ‖(((2 * Real.sqrt x.1 * ψ x : ℝ) : ℂ)) • Sw x‖ +
                ‖(((2 * Real.sqrt x.1 * χ x * (2 * vGrad vS χ x) : ℝ) : ℂ)) • w x‖ :=
              norm_add_le _ _
          _ = |2 * Real.sqrt x.1 * ψ x| * ‖Sw x‖ +
                |2 * Real.sqrt x.1 * χ x * (2 * vGrad vS χ x)| * ‖w x‖ := by
              simp [norm_smul, Real.norm_eq_abs]
          _ ≤ (4 * Γ) * (fε x + f0 x) + (16 * K * Γ ^ 3) * (fε x + f0 x) :=
              add_le_add (mul_le_mul c1 nSw (norm_nonneg _) (by positivity))
                (mul_le_mul c2 nw (norm_nonneg _) (by positivity))
          _ = (4 * Γ + 16 * K * Γ ^ 3) * (fε x + f0 x) := by ring
      have p_Et : ‖(Real.sqrt x.1 : ℂ) • ((x.2.2 : ℂ) • Et x)‖ ≤
          (2 * Γ + 48 * K * Γ ^ 4) * (fε x + f0 x) := by
        have heq : (Real.sqrt x.1 : ℂ) • ((x.2.2 : ℂ) • Et x) =
            (((x.2.2 * ψ x : ℝ) : ℂ)) • sqrtS Ew x +
              (((x.2.2 * χ x * (2 * Real.sqrt x.1 * vGrad vEta χ x) : ℝ) : ℂ)) • w x := by
          ext i
          change (Real.sqrt x.1 : ℂ) * ((x.2.2 : ℂ) *
            (((ψ x : ℂ) • Ew x + (vGrad vEta ψ x : ℂ) • w x) i)) = _
          simp only [hvE_eq, sqrtS, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          push_cast; ring
        rw [heq]
        have c1 : |x.2.2 * ψ x| ≤ 2 * Γ := by
          rw [abs_mul, abs_of_nonneg hψ0]
          calc |x.2.2| * ψ x ≤ (2 * Γ) * 1 :=
                mul_le_mul hη hψ1 hψ0 (by positivity)
            _ = 2 * Γ := mul_one _
        have c2 : |x.2.2 * χ x * (2 * Real.sqrt x.1 * vGrad vEta χ x)| ≤ 48 * K * Γ ^ 4 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hχ0]
          have p1 : |x.2.2| * χ x ≤ 2 * Γ := by
            calc |x.2.2| * χ x ≤ (2 * Γ) * 1 :=
                  mul_le_mul hη hχ1 hχ0 (by positivity)
              _ = 2 * Γ := mul_one _
          calc |x.2.2| * χ x * |2 * Real.sqrt x.1 * vGrad vEta χ x|
              ≤ (2 * Γ) * (24 * K * Γ ^ 3) :=
                mul_le_mul p1 hbe (abs_nonneg _) (by positivity)
            _ = 48 * K * Γ ^ 4 := by ring
        calc ‖(((x.2.2 * ψ x : ℝ) : ℂ)) • sqrtS Ew x +
              (((x.2.2 * χ x * (2 * Real.sqrt x.1 * vGrad vEta χ x) : ℝ) : ℂ)) • w x‖
            ≤ ‖(((x.2.2 * ψ x : ℝ) : ℂ)) • sqrtS Ew x‖ +
                ‖(((x.2.2 * χ x * (2 * Real.sqrt x.1 * vGrad vEta χ x) : ℝ) : ℂ)) • w x‖ :=
              norm_add_le _ _
          _ = |x.2.2 * ψ x| * ‖sqrtS Ew x‖ +
                |x.2.2 * χ x * (2 * Real.sqrt x.1 * vGrad vEta χ x)| * ‖w x‖ := by
              simp [norm_smul, Real.norm_eq_abs]
          _ ≤ (2 * Γ) * (fε x + f0 x) + (48 * K * Γ ^ 4) * (fε x + f0 x) :=
              add_le_add (mul_le_mul c1 nEw (norm_nonneg _) (by positivity))
                (mul_le_mul c2 nw (norm_nonneg _) (by positivity))
          _ = (2 * Γ + 48 * K * Γ ^ 4) * (fε x + f0 x) := by ring
      have p_t : ‖(Real.sqrt x.1 : ℂ) • t x‖ ≤ 2 * Γ * (fε x + f0 x) := by
        have heq : (Real.sqrt x.1 : ℂ) • t x = (((Real.sqrt x.1 * ψ x : ℝ) : ℂ)) • w x := by
          ext i; simp [t]; ring
        rw [heq, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hψ0)]
        have c1 : Real.sqrt x.1 * ψ x ≤ 2 * Γ := by
          calc Real.sqrt x.1 * ψ x ≤ (2 * Γ) * 1 :=
                mul_le_mul hsq hψ1 hψ0 (by positivity)
            _ = 2 * Γ := mul_one _
        exact mul_le_mul c1 nw (norm_nonneg _) (by positivity)
      have hB2_split : B2 = (Real.sqrt x.1 : ℂ) • ((2 : ℂ) • St x) +
          (Real.sqrt x.1 : ℂ) • ((x.2.2 : ℂ) • Et x) +
          (Real.sqrt x.1 : ℂ) • t x := by
        ext i; simp [B2]
      rw [hB2_split]
      have htri : ‖(Real.sqrt x.1 : ℂ) • ((2 : ℂ) • St x) +
            (Real.sqrt x.1 : ℂ) • ((x.2.2 : ℂ) • Et x) +
            (Real.sqrt x.1 : ℂ) • t x‖ ≤
          (8 * Γ + 16 * K * Γ ^ 3 + 48 * K * Γ ^ 4) * (fε x + f0 x) := by
        calc _ ≤ ‖(Real.sqrt x.1 : ℂ) • ((2 : ℂ) • St x) +
                  (Real.sqrt x.1 : ℂ) • ((x.2.2 : ℂ) • Et x)‖ +
                ‖(Real.sqrt x.1 : ℂ) • t x‖ := norm_add_le _ _
          _ ≤ ‖(Real.sqrt x.1 : ℂ) • ((2 : ℂ) • St x)‖ +
                ‖(Real.sqrt x.1 : ℂ) • ((x.2.2 : ℂ) • Et x)‖ +
                ‖(Real.sqrt x.1 : ℂ) • t x‖ := add_le_add (norm_add_le _ _) le_rfl
          _ ≤ (4 * Γ + 16 * K * Γ ^ 3) * (fε x + f0 x) +
                (2 * Γ + 48 * K * Γ ^ 4) * (fε x + f0 x) +
                2 * Γ * (fε x + f0 x) := add_le_add (add_le_add p_St p_Et) p_t
          _ = (8 * Γ + 16 * K * Γ ^ 3 + 48 * K * Γ ^ 4) * (fε x + f0 x) := by ring
      have h_coef_le : 8 * Γ + 16 * K * Γ ^ 3 + 48 * K * Γ ^ 4 ≤ 72 * K * Γ ^ 4 := by
        have hΓ34 : Γ ^ 3 ≤ Γ ^ 4 := pow_le_pow_right₀ hΓ1 (by omega)
        have hΓ14 : Γ ≤ Γ ^ 4 := by
          calc Γ = Γ ^ 1 := (pow_one Γ).symm
            _ ≤ Γ ^ 4 := pow_le_pow_right₀ hΓ1 (by omega)
        have p1 : 8 * Γ ≤ 8 * K * Γ ^ 4 := by
          have hk : (1 : ℝ) ≤ K := by linarith only [hK3]
          have hm : 1 * Γ ≤ K * Γ ^ 4 := mul_le_mul hk hΓ14 (by linarith only [hΓ1]) hK0
          linarith only [hm]
        have p2 : 16 * K * Γ ^ 3 ≤ 16 * K * Γ ^ 4 :=
          mul_le_mul_of_nonneg_left hΓ34 (by positivity)
        have p3 : 0 ≤ K * Γ ^ 4 := by positivity
        linarith only [p1, p2, p3]
      have hf_nn : 0 ≤ fε x + f0 x := by dsimp only [fε, f0]; positivity
      exact htri.trans (mul_le_mul_of_nonneg_right h_coef_le hf_nn)
    have hy1 : ε * (‖A1‖ * ‖B1‖) ≤
        (1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 + 24 * Γ ^ 2 * ε * f0 x ^ 2 := by
      have hp : ε * (‖A1‖ * ‖B1‖) ≤
          (4 * Γ * ε * f0 x) * ‖gQ x‖ + (4 * Γ * ε * f0 x) * ‖rq x‖ := by
        have h1 : ‖A1‖ * ‖B1‖ ≤ (4 * Γ * f0 x) * (‖gQ x‖ + ‖rq x‖) :=
          mul_le_mul hA1_bd hB1_bd (norm_nonneg _) (by dsimp only [f0]; positivity)
        calc ε * (‖A1‖ * ‖B1‖)
            ≤ ε * ((4 * Γ * f0 x) * (‖gQ x‖ + ‖rq x‖)) :=
              mul_le_mul_of_nonneg_left h1 hε0.le
          _ = (4 * Γ * ε * f0 x) * ‖gQ x‖ + (4 * Γ * ε * f0 x) * ‖rq x‖ := by ring
      have hε_sq : ε ^ 2 ≤ ε := by
        calc ε ^ 2 = ε * ε := sq ε
          _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε0.le
          _ = ε := mul_one _
      have h_f0_sq : (4 * Γ * ε * f0 x) ^ 2 ≤ 16 * Γ ^ 2 * ε * f0 x ^ 2 := by
        calc (4 * Γ * ε * f0 x) ^ 2 = 16 * Γ ^ 2 * f0 x ^ 2 * ε ^ 2 := by ring
          _ ≤ 16 * Γ ^ 2 * f0 x ^ 2 * ε :=
              mul_le_mul_of_nonneg_left hε_sq (by positivity)
          _ = 16 * Γ ^ 2 * ε * f0 x ^ 2 := by ring
      have y1 : (4 * Γ * ε * f0 x) * ‖gQ x‖ ≤ (1 / 4) * ‖gQ x‖ ^ 2 + (4 * Γ * ε * f0 x) ^ 2 := by
        have hsq1 := sq_nonneg ((1 / 2 : ℝ) * ‖gQ x‖ - 4 * Γ * ε * f0 x)
        have hexp : ((1 / 2 : ℝ) * ‖gQ x‖ - 4 * Γ * ε * f0 x) ^ 2 =
            (1 / 4) * ‖gQ x‖ ^ 2 - (4 * Γ * ε * f0 x) * ‖gQ x‖ + (4 * Γ * ε * f0 x) ^ 2 := by ring
        linarith only [hsq1, hexp]
      have y2 : (4 * Γ * ε * f0 x) * ‖rq x‖ ≤ (1 / 2) * ‖rq x‖ ^ 2 + (1 / 2) * (4 * Γ * ε * f0 x) ^ 2 := by
        have hsq2 := sq_nonneg (‖rq x‖ - 4 * Γ * ε * f0 x)
        have hexp : (‖rq x‖ - 4 * Γ * ε * f0 x) ^ 2 =
            ‖rq x‖ ^ 2 - 2 * ((4 * Γ * ε * f0 x) * ‖rq x‖) + (4 * Γ * ε * f0 x) ^ 2 := by ring
        linarith only [hsq2, hexp]
      linarith only [hp, h_f0_sq, y1, y2]
    have hy2 : ε * (‖A2‖ * ‖B2‖) ≤
        144 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) := by
      have hp : ε * (‖A2‖ * ‖B2‖) ≤
          72 * K * Γ ^ 4 * ε * (f0 x * (fε x + f0 x)) := by
        have h1 : ‖A2‖ * ‖B2‖ ≤ f0 x * (72 * K * Γ ^ 4 * (fε x + f0 x)) :=
          mul_le_mul hA2_bd hB2_bd (norm_nonneg _) (by dsimp only [f0]; positivity)
        calc ε * (‖A2‖ * ‖B2‖)
            ≤ ε * (f0 x * (72 * K * Γ ^ 4 * (fε x + f0 x))) :=
              mul_le_mul_of_nonneg_left h1 hε0.le
          _ = 72 * K * Γ ^ 4 * ε * (f0 x * (fε x + f0 x)) := by ring
      have h2 : f0 x * (fε x + f0 x) ≤ 2 * (f0 x ^ 2 + fε x ^ 2) := by
        have s1 := sq_nonneg (f0 x - fε x)
        have s2 := sq_nonneg (fε x)
        have hexp : 2 * (f0 x ^ 2 + fε x ^ 2) - f0 x * (fε x + f0 x) =
            (1 / 2) * (f0 x - fε x) ^ 2 + (1 / 2) * f0 x ^ 2 + (3 / 2) * fε x ^ 2 := by ring
        have s3 := sq_nonneg (f0 x)
        linarith only [s1, s2, s3, hexp]
      calc ε * (‖A2‖ * ‖B2‖)
          ≤ 72 * K * Γ ^ 4 * ε * (2 * (f0 x ^ 2 + fε x ^ 2)) :=
            hp.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = 144 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) := by ring
    have h24 : 24 * Γ ^ 2 * ε * f0 x ^ 2 ≤
        24 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) := by
      have hk : (1 : ℝ) ≤ K := by linarith only [hK3]
      have hΓ24 : 1 * Γ ^ 2 ≤ K * Γ ^ 4 :=
        mul_le_mul hk (pow_le_pow_right₀ hΓ1 (by omega)) (by positivity) hK0
      have p1 : 24 * Γ ^ 2 * ε * f0 x ^ 2 ≤ 24 * K * Γ ^ 4 * ε * f0 x ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hΓ24 (mul_nonneg hε0.le (sq_nonneg (f0 x)))
        linarith only [hm]
      have hsum_sq : f0 x ^ 2 ≤ f0 x ^ 2 + fε x ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      have p2 : 24 * K * Γ ^ 4 * ε * f0 x ^ 2 ≤
          24 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_sq (by positivity)
      exact p1.trans p2
    calc ε * ‖(x.1 : ℂ) * ∑ i : Fin 2,
            ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
              Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))‖
        ≤ ε * (‖A1‖ * ‖B1‖ + ‖A2‖ * ‖B2‖) :=
          mul_le_mul_of_nonneg_left hZ_norm hε0.le
      _ = ε * (‖A1‖ * ‖B1‖) + ε * (‖A2‖ * ‖B2‖) := mul_add _ _ _
      _ ≤ ((1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 + 24 * Γ ^ 2 * ε * f0 x ^ 2) +
            144 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) := add_le_add hy1 hy2
      _ ≤ (1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 +
            168 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2) := by linarith only [h24]
  · have hχ0 : χ x = 0 := boxCutoff_eq_zero_of_notMem hσ hσH₁ hx
    have hψ0 : ψ x = 0 := by simp [ψ, hχ0]
    have hvgQ0 : vGrad (vQ ε) ψ x = 0 := by rw [vGrad_sq (vQ ε) hχ_cd x, hχ0]; ring
    have hvgS0 : vGrad vS ψ x = 0 := by rw [vGrad_sq vS hχ_cd x, hχ0]; ring
    have hvgE0 : vGrad vEta ψ x = 0 := by rw [vGrad_sq vEta hχ_cd x, hχ0]; ring
    have hQt0 : Qt x = 0 := by simp [Qt, weakSmul, hψ0, hvgQ0]
    have hSt0 : St x = 0 := by simp [St, weakSmul, hψ0, hvgS0]
    have hEt0 : Et x = 0 := by simp [Et, weakSmul, hψ0, hvgE0]
    have ht0 : t x = 0 := by simp [t, hψ0]
    simp only [hQt0, hSt0, hEt0, ht0, PiLp.zero_apply, mul_zero, add_zero, map_zero,
      Finset.sum_const_zero, norm_zero]
    positivity

/-! ## 6. Helper assembly lemmas & `boxDiffusionAbsorption_proof` (`PartII-b:T16/2/2`) -/

private theorem gQ_gE_eLpNorm_lt_top
    {Γ c σ H₁ L₁ ε Aε A0 : ℝ}
    (hΓ1 : 1 ≤ Γ) (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf)
    (mb0 : AEStronglyMeasurable b0 (hMeas c 2))
    (mQε : AEStronglyMeasurable (sqrtS Qbε) (hMeas c 2))
    (mEε : AEStronglyMeasurable (sqrtS Ebε) (hMeas c 2))
    (mS0 : AEStronglyMeasurable Sb0 (hMeas c 2))
    (mQ0 : AEStronglyMeasurable (sqrtS Qb0) (hMeas c 2))
    (mE0 : AEStronglyMeasurable (sqrtS Eb0) (hMeas c 2))
    (mfε : AEStronglyMeasurable
      (fun x : Coord => ‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) (hMeas c 2))
    (mf0 : AEStronglyMeasurable
      (fun x : Coord => ‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖) (hMeas c 2))
    (hfε_lp : eLpNorm (fun x : Coord => ‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖)
      (ENNReal.ofReal 2) (hMeas c 2) ≤ ENNReal.ofReal Aε)
    (hf0_lp : eLpNorm (fun x : Coord => ‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖)
      (ENNReal.ofReal 2) (hMeas c 2) ≤ ENNReal.ofReal A0) :
    let χ := boxCutoff σ H₁ L₁
    let Qv := qepsOf ε b0 Sb0 Qb0 Eb0
    let Qw := Qbε - Qv
    let Ew := Ebε - Eb0
    let gQ : CProf := fun x => (χ x : ℂ) • sqrtS Qw x
    let gE : CProf := fun x => (χ x : ℂ) • sqrtS Ew x
    AEStronglyMeasurable gQ (hMeas c 2) ∧ eLpNorm gQ 2 (hMeas c 2) < ⊤ ∧
      AEStronglyMeasurable gE (hMeas c 2) ∧ eLpNorm gE 2 (hMeas c 2) < ⊤ := by
  intro χ Qv Qw Ew gQ gE
  set fε : Coord → ℝ := fun x => ‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖
  set f0 : Coord → ℝ := fun x => ‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖
  have hχ_cd : ContDiff ℝ ∞ χ := boxCutoff_contDiff σ H₁ L₁
  have mχ : Measurable (fun x : Coord => (χ x : ℂ)) :=
    Complex.measurable_ofReal.comp hχ_cd.continuous.measurable
  have mQw : AEStronglyMeasurable (sqrtS Qw) (hMeas c 2) := by
    rw [show sqrtS Qw = sqrtS Qbε - sqrtS Qv from flatCls_sqrtS_sub Qbε Qv]
    exact mQε.sub (aestronglyMeasurable_sqrtS_qepsOf ε mb0 mS0 mQ0 mE0)
  have mEw : AEStronglyMeasurable (sqrtS Ew) (hMeas c 2) := by
    rw [show sqrtS Ew = sqrtS Ebε - sqrtS Eb0 from flatCls_sqrtS_sub Ebε Eb0]
    exact mEε.sub mE0
  have mgQ : AEStronglyMeasurable gQ (hMeas c 2) := mχ.aestronglyMeasurable.smul mQw
  have mgE : AEStronglyMeasurable gE (hMeas c 2) := mχ.aestronglyMeasurable.smul mEw
  have hsum_fin : eLpNorm (fε + f0) 2 (hMeas c 2) < ⊤ := by
    refine lt_of_le_of_lt (eLpNorm_add_le mfε mf0 (by norm_num)) ?_
    rw [ENNReal.ofReal_ofNat] at hfε_lp hf0_lp
    exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt hfε_lp ENNReal.ofReal_lt_top,
      lt_of_le_of_lt hf0_lp ENNReal.ofReal_lt_top⟩
  have hgQ_fin : eLpNorm gQ 2 (hMeas c 2) < ⊤ := by
    have hpt : ∀ x : Coord, ‖gQ x‖ ≤ (4 * Γ) * (fε x + f0 x) := by
      intro x
      by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
      · obtain ⟨-, -, hsq, hη⟩ := enl_coord_bounds hσ hH₁ hL₁ hΓ1 hx
        have hχ1 : |χ x| ≤ 1 := by
          rw [abs_of_nonneg (boxCutoff_nonneg σ H₁ L₁ x)]
          exact boxCutoff_le_one σ H₁ L₁ x
        have hsp : sqrtS Qw x = sqrtS Qbε x - sqrtS Qb0 x +
            (ε : ℂ) • ((2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x) := by
          ext i; simp [Qw, Qv, sqrtS, qepsOf]; ring
        have h_norm_Qw : ‖sqrtS Qw x‖ ≤ (4 * Γ) * (fε x + f0 x) := by
          rw [hsp]
          have n1 : ‖sqrtS Qbε x - sqrtS Qb0 x‖ ≤ ‖sqrtS Qbε x‖ + ‖sqrtS Qb0 x‖ :=
            norm_sub_le _ _
          have nS : ‖sqrtS Sb0 x‖ ≤ 2 * Γ * ‖Sb0 x‖ := by
            rw [norm_sqrtS]; exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
          have nB : ‖sqrtS b0 x‖ ≤ 2 * Γ * ‖b0 x‖ := by
            rw [norm_sqrtS]; exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
          have nE : ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ ≤ 2 * Γ * ‖sqrtS Eb0 x‖ := by
            rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hη (norm_nonneg _)
          have n2 : ‖(ε : ℂ) • ((2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x)‖ ≤
              4 * Γ * ‖Sb0 x‖ + 2 * Γ * ‖sqrtS Eb0 x‖ + 2 * Γ * ‖b0 x‖ := by
            rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε0.le]
            have hsum : ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖ ≤
                4 * Γ * ‖Sb0 x‖ + 2 * Γ * ‖sqrtS Eb0 x‖ + 2 * Γ * ‖b0 x‖ := by
              calc ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖
                  ≤ ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ :=
                    norm_add_le _ _
                _ ≤ ‖(2 : ℂ) • sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ :=
                    add_le_add (norm_add_le _ _) le_rfl
                _ = 2 * ‖sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ := by
                    simp [norm_smul]
                _ ≤ 2 * (2 * Γ * ‖Sb0 x‖) + 2 * Γ * ‖sqrtS Eb0 x‖ + 2 * Γ * ‖b0 x‖ := by gcongr
                _ = 4 * Γ * ‖Sb0 x‖ + 2 * Γ * ‖sqrtS Eb0 x‖ + 2 * Γ * ‖b0 x‖ := by ring
            calc ε * ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖
                ≤ 1 * (4 * Γ * ‖Sb0 x‖ + 2 * Γ * ‖sqrtS Eb0 x‖ + 2 * Γ * ‖b0 x‖) :=
                  mul_le_mul hε1 hsum (norm_nonneg _) zero_le_one
              _ = 4 * Γ * ‖Sb0 x‖ + 2 * Γ * ‖sqrtS Eb0 x‖ + 2 * Γ * ‖b0 x‖ := one_mul _
          have ntot := (norm_add_le _ _).trans (add_le_add n1 n2)
          have p1 : ‖sqrtS Qbε x‖ ≤ 4 * Γ * ‖sqrtS Qbε x‖ := by
            calc ‖sqrtS Qbε x‖ = 1 * ‖sqrtS Qbε x‖ := (one_mul _).symm
              _ ≤ (4 * Γ) * ‖sqrtS Qbε x‖ :=
                mul_le_mul_of_nonneg_right (by linarith only [hΓ1]) (norm_nonneg _)
          have p2 : ‖sqrtS Qb0 x‖ ≤ 4 * Γ * ‖sqrtS Qb0 x‖ := by
            calc ‖sqrtS Qb0 x‖ = 1 * ‖sqrtS Qb0 x‖ := (one_mul _).symm
              _ ≤ (4 * Γ) * ‖sqrtS Qb0 x‖ :=
                mul_le_mul_of_nonneg_right (by linarith only [hΓ1]) (norm_nonneg _)
          have p3 : 2 * Γ * ‖sqrtS Eb0 x‖ ≤ 4 * Γ * ‖sqrtS Eb0 x‖ :=
            mul_le_mul_of_nonneg_right (by linarith only [hΓ1]) (norm_nonneg _)
          have p4 : 2 * Γ * ‖b0 x‖ ≤ 4 * Γ * ‖b0 x‖ :=
            mul_le_mul_of_nonneg_right (by linarith only [hΓ1]) (norm_nonneg _)
          have z1 : 0 ≤ 4 * Γ * ‖bε x‖ :=
            mul_nonneg (by linarith only [hΓ1]) (norm_nonneg _)
          have z2 : 0 ≤ 4 * Γ * ‖Sbε x‖ :=
            mul_nonneg (by linarith only [hΓ1]) (norm_nonneg _)
          have z3 : 0 ≤ 4 * Γ * ‖sqrtS Ebε x‖ :=
            mul_nonneg (by linarith only [hΓ1]) (norm_nonneg _)
          dsimp only [fε, f0]
          linarith only [ntot, p1, p2, p3, p4, z1, z2, z3]
        dsimp only [gQ]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        calc |χ x| * ‖sqrtS Qw x‖ ≤ 1 * ((4 * Γ) * (fε x + f0 x)) :=
              mul_le_mul hχ1 h_norm_Qw (norm_nonneg _) zero_le_one
          _ = (4 * Γ) * (fε x + f0 x) := one_mul _
      · have hχ0 : χ x = 0 := boxCutoff_eq_zero_of_notMem hσ hσH₁ hx
        have : 0 ≤ (4 * Γ) * (fε x + f0 x) := by dsimp only [fε, f0]; positivity
        simpa [gQ, hχ0] using this
    refine eLpNorm_two_lt_top_of_norm_le (v := fε + f0) (C := 4 * Γ) (fun x => ?_) hsum_fin
    have h_nn : 0 ≤ fε x + f0 x := by dsimp only [fε, f0]; positivity
    simpa [Pi.add_apply, Real.norm_of_nonneg h_nn] using hpt x
  have hgE_fin : eLpNorm gE 2 (hMeas c 2) < ⊤ := by
    refine eLpNorm_two_lt_top_of_norm_le (v := fε + f0) (C := 1) (fun x => ?_) hsum_fin
    have h_nn : 0 ≤ fε x + f0 x := by dsimp only [fε, f0]; positivity
    rw [one_mul, Pi.add_apply, Real.norm_of_nonneg h_nn]
    have hχ1 : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (boxCutoff_nonneg σ H₁ L₁ x)]
      exact boxCutoff_le_one σ H₁ L₁ x
    have hsp : sqrtS Ew x = sqrtS Ebε x - sqrtS Eb0 x :=
      congrFun (flatCls_sqrtS_sub Ebε Eb0) x
    have hn : ‖sqrtS Ew x‖ ≤ fε x + f0 x := by
      have hsub : ‖sqrtS Ew x‖ ≤ ‖sqrtS Ebε x‖ + ‖sqrtS Eb0 x‖ := by
        rw [hsp]; exact norm_sub_le _ _
      dsimp only [fε, f0]
      have n1 := norm_nonneg (bε x); have n2 := norm_nonneg (Sbε x)
      have n3 := norm_nonneg (sqrtS Qbε x); have n4 := norm_nonneg (b0 x)
      have n5 := norm_nonneg (Sb0 x); have n6 := norm_nonneg (sqrtS Qb0 x)
      linarith only [hsub, n1, n2, n3, n4, n5, n6]
    dsimp only [gE]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |χ x| * ‖sqrtS Ew x‖ ≤ 1 * (fε x + f0 x) :=
          mul_le_mul hχ1 hn (norm_nonneg _) zero_le_one
      _ = fε x + f0 x := one_mul _
  exact ⟨mgQ, hgQ_fin, mgE, hgE_fin⟩

private theorem final_rate_norm_bound
    {k_chart : ℕ} {C_chart K Cf Cp Γ ν c om ε F_norm EQ EE IR IE If0 Ifε : ℝ}
    {gQ gE : CProf} {F : CProf}
    (hC_chart : 0 < C_chart) (hK0 : 0 < K) (hΓ1 : 1 ≤ Γ)
    (hν : 0 < ν) (hνΓ1 : ν ≤ Γ) (hνΓ : ν⁻¹ ≤ Γ)
    (hom0 : 0 ≤ om) (hε0 : 0 < ε) (hF_norm0 : 0 ≤ F_norm)
    (hF_ofReal : ENNReal.ofReal F_norm = hNorm c 2 F)
    (hgQ_fin : eLpNorm gQ 2 (hMeas c 2) < ⊤)
    (hgE_fin : eLpNorm gE 2 (hMeas c 2) < ⊤)
    (hgQ_sq_eq : EQ = (eLpNorm gQ 2 (hMeas c 2)).toReal ^ 2)
    (hgE_sq_eq : EE = (eLpNorm gE 2 (hMeas c 2)).toReal ^ 2)
    (_hEE_nn : 0 ≤ EE) (hIR_nn : 0 ≤ IR) (hIE_nn : 0 ≤ IE)
    (hIf0_nn : 0 ≤ If0) (hIfε_nn : 0 ≤ Ifε)
    (h_int_rq_le : IR ≤ 576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2)
    (h_int_re_le : IE ≤ 576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2)
    (h_int_f0_le : If0 ≤ (Cf * Γ ^ 3 * F_norm) ^ 2)
    (h_int_fε_le : Ifε ≤ (Cp * Γ ^ 3 * F_norm) ^ 2)
    (h_abs_step :
      (1 / 2) * ν * (EQ + EE) ≤
        (3 / 2) * ν * IR + ν * IE +
          2 * K * Γ ^ 2 * om ^ 2 * F_norm ^ 2 +
          168 * K * Γ ^ 4 * ν * ε * (If0 + Ifε) +
          C_chart * Γ ^ k_chart * (om + om ^ 2 + ε) * F_norm ^ 2) :
    let B_tot := 1440 * K ^ 2 + 2 * K + 168 * K * (Cf ^ 2 + Cp ^ 2) + C_chart
    let k_abs := k_chart + 12
    let C_abs := 4 * B_tot + 1
    hNorm c 2 gQ + hNorm c 2 gE ≤
      ENNReal.ofReal (C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F := by
  intro B_tot k_abs C_abs
  have hB_pos : 0 < B_tot := by dsimp only [B_tot]; positivity
  set R_rate : ℝ := om + om ^ 2 + ε
  have hR_nn : 0 ≤ R_rate := add_nonneg (add_nonneg hom0 (sq_nonneg om)) hε0.le
  have hom2_le : om ^ 2 ≤ R_rate := by
    dsimp only [R_rate]
    have h0 := hε0.le
    linarith only [hom0, h0]
  have hε_le_R : ε ≤ R_rate := by
    dsimp only [R_rate]
    have hs := sq_nonneg om
    linarith only [hom0, hs]
  have h_rhs_tot :
      (1 / 2) * ν * (EQ + EE) ≤
        B_tot * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by
    have p_rq : (3 / 2) * ν * IR + ν * IE ≤
        1440 * K ^ 2 * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by
      have h1 : (3 / 2) * ν * IR + ν * IE ≤
          1440 * K ^ 2 * (Γ ^ 7 * om ^ 2) * F_norm ^ 2 := by
        have a1 : ν * IR ≤ Γ * (576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2) :=
          mul_le_mul hνΓ1 h_int_rq_le hIR_nn (by linarith only [hΓ1])
        have a2 : ν * IE ≤ Γ * (576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2) :=
          mul_le_mul hνΓ1 h_int_re_le hIE_nn (by linarith only [hΓ1])
        have hexp : (3 / 2) * (Γ * (576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2)) +
            Γ * (576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2) =
            1440 * K ^ 2 * (Γ ^ 7 * om ^ 2) * F_norm ^ 2 := by ring
        linarith only [a1, a2, hexp]
      have hpow : Γ ^ 7 ≤ Γ ^ (k_chart + 11) := pow_le_pow_right₀ hΓ1 (by omega)
      have hprod := mul_le_mul hpow hom2_le (sq_nonneg om) (by positivity)
      calc (3 / 2) * ν * IR + ν * IE
          ≤ 1440 * K ^ 2 * (Γ ^ 7 * om ^ 2) * F_norm ^ 2 := h1
        _ ≤ 1440 * K ^ 2 * (Γ ^ (k_chart + 11) * R_rate) * F_norm ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hprod (by positivity)) (sq_nonneg F_norm)
        _ = 1440 * K ^ 2 * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by ring
    have p_dr : 2 * K * Γ ^ 2 * om ^ 2 * F_norm ^ 2 ≤
        2 * K * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by
      have hpow : Γ ^ 2 ≤ Γ ^ (k_chart + 11) := pow_le_pow_right₀ hΓ1 (by omega)
      have hprod := mul_le_mul hpow hom2_le (sq_nonneg om) (by positivity)
      calc 2 * K * Γ ^ 2 * om ^ 2 * F_norm ^ 2
          = 2 * K * (Γ ^ 2 * om ^ 2) * F_norm ^ 2 := by ring
        _ ≤ 2 * K * (Γ ^ (k_chart + 11) * R_rate) * F_norm ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hprod (by positivity)) (sq_nonneg F_norm)
        _ = 2 * K * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by ring
    have p_df : 168 * K * Γ ^ 4 * ν * ε * (If0 + Ifε) ≤
        168 * K * (Cf ^ 2 + Cp ^ 2) * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by
      have hf_sum : If0 + Ifε ≤ (Cf ^ 2 + Cp ^ 2) * Γ ^ 6 * F_norm ^ 2 := by
        have hexp : (Cf * Γ ^ 3 * F_norm) ^ 2 + (Cp * Γ ^ 3 * F_norm) ^ 2 =
            (Cf ^ 2 + Cp ^ 2) * Γ ^ 6 * F_norm ^ 2 := by ring
        linarith only [h_int_f0_le, h_int_fε_le, hexp]
      have hν_le : 168 * K * Γ ^ 4 * ν * ε ≤ 168 * K * Γ ^ 5 * R_rate := by
        have h1 : ν * ε ≤ Γ * R_rate := mul_le_mul hνΓ1 hε_le_R hε0.le (by linarith only [hΓ1])
        calc 168 * K * Γ ^ 4 * ν * ε
            = 168 * K * Γ ^ 4 * (ν * ε) := by ring
          _ ≤ 168 * K * Γ ^ 4 * (Γ * R_rate) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 168 * K * Γ ^ 5 * R_rate := by ring
      have hpow : Γ ^ 11 ≤ Γ ^ (k_chart + 11) := pow_le_pow_right₀ hΓ1 (by omega)
      calc 168 * K * Γ ^ 4 * ν * ε * (If0 + Ifε)
          ≤ (168 * K * Γ ^ 5 * R_rate) * ((Cf ^ 2 + Cp ^ 2) * Γ ^ 6 * F_norm ^ 2) :=
            mul_le_mul hν_le hf_sum (add_nonneg hIf0_nn hIfε_nn) (by positivity)
        _ = 168 * K * (Cf ^ 2 + Cp ^ 2) * R_rate * F_norm ^ 2 * Γ ^ 11 := by ring
        _ ≤ 168 * K * (Cf ^ 2 + Cp ^ 2) * R_rate * F_norm ^ 2 * Γ ^ (k_chart + 11) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 168 * K * (Cf ^ 2 + Cp ^ 2) * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by ring
    have p_ch : C_chart * Γ ^ k_chart * R_rate * F_norm ^ 2 ≤
        C_chart * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by
      have hpow : Γ ^ k_chart ≤ Γ ^ (k_chart + 11) := pow_le_pow_right₀ hΓ1 (by omega)
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hC_chart.le) (mul_nonneg hR_nn (sq_nonneg F_norm))
      have hexp : C_chart * Γ ^ k_chart * (R_rate * F_norm ^ 2) =
          C_chart * Γ ^ k_chart * R_rate * F_norm ^ 2 := by ring
      have hexp2 : C_chart * Γ ^ (k_chart + 11) * (R_rate * F_norm ^ 2) =
          C_chart * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by ring
      linarith only [hm, hexp, hexp2]
    dsimp only [B_tot]
    have hsum_eq :
        1440 * K ^ 2 * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 +
          2 * K * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 +
          168 * K * (Cf ^ 2 + Cp ^ 2) * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 +
          C_chart * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 =
        (1440 * K ^ 2 + 2 * K + 168 * K * (Cf ^ 2 + Cp ^ 2) + C_chart) *
          Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2 := by ring
    linarith only [h_abs_step, p_rq, p_dr, p_df, p_ch, hsum_eq]
  have hEQ_EE : EQ + EE ≤ 2 * B_tot * Γ ^ k_abs * R_rate * F_norm ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h_rhs_tot (by positivity : 0 ≤ 2 * ν⁻¹)
    have h_cancel : 2 * ν⁻¹ * ((1 / 2) * ν * (EQ + EE)) = EQ + EE := by
      field_simp [hν.ne']
    rw [h_cancel] at hmul
    calc EQ + EE
        ≤ 2 * ν⁻¹ * (B_tot * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2) := hmul
      _ ≤ 2 * Γ * (B_tot * Γ ^ (k_chart + 11) * R_rate * F_norm ^ 2) := by
          gcongr
      _ = 2 * B_tot * Γ ^ k_abs * R_rate * F_norm ^ 2 := by
          dsimp only [k_abs]
          rw [pow_succ]
          ring
  set NQ : ℝ := (eLpNorm gQ 2 (hMeas c 2)).toReal
  set NE : ℝ := (eLpNorm gE 2 (hMeas c 2)).toReal
  have hNQ0 : 0 ≤ NQ := ENNReal.toReal_nonneg
  have hNE0 : 0 ≤ NE := ENNReal.toReal_nonneg
  set S_rate : ℝ := Real.sqrt om + om + Real.sqrt ε
  have hS_nn : 0 ≤ S_rate :=
    add_nonneg (add_nonneg (Real.sqrt_nonneg om) hom0) (Real.sqrt_nonneg ε)
  have hR_le_S2 : R_rate ≤ S_rate ^ 2 := by
    dsimp only [R_rate, S_rate]
    have sq_om : Real.sqrt om ^ 2 = om := Real.sq_sqrt hom0
    have sq_ε : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0.le
    have p1 : 0 ≤ Real.sqrt om * om := mul_nonneg (Real.sqrt_nonneg om) hom0
    have p2 : 0 ≤ Real.sqrt om * Real.sqrt ε := mul_nonneg (Real.sqrt_nonneg om) (Real.sqrt_nonneg ε)
    have p3 : 0 ≤ om * Real.sqrt ε := mul_nonneg hom0 (Real.sqrt_nonneg ε)
    have hexp : (Real.sqrt om + om + Real.sqrt ε) ^ 2 =
        Real.sqrt om ^ 2 + om ^ 2 + Real.sqrt ε ^ 2 +
          2 * (Real.sqrt om * om) + 2 * (Real.sqrt om * Real.sqrt ε) +
          2 * (om * Real.sqrt ε) := by ring
    linarith only [sq_om, sq_ε, p1, p2, p3, hexp]
  have hΓ_pow_sq : Γ ^ k_abs ≤ (Γ ^ k_abs) ^ 2 := by
    have h1 : 1 ≤ Γ ^ k_abs := one_le_pow₀ hΓ1
    calc Γ ^ k_abs = 1 * Γ ^ k_abs := (one_mul _).symm
      _ ≤ Γ ^ k_abs * Γ ^ k_abs := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (Γ ^ k_abs) ^ 2 := (sq _).symm
  have hC_sq : 4 * B_tot ≤ C_abs ^ 2 := by
    dsimp only [C_abs]
    have hs : 0 ≤ (4 * B_tot) ^ 2 := sq_nonneg _
    have hexp : (4 * B_tot + 1) ^ 2 = (4 * B_tot) ^ 2 + 8 * B_tot + 1 := by ring
    linarith only [hs, hexp, hB_pos]
  have hC_pos : 0 < C_abs := by dsimp only [C_abs]; linarith only [hB_pos]
  have h_sum_sq : (NQ + NE) ^ 2 ≤ (C_abs * Γ ^ k_abs * S_rate * F_norm) ^ 2 := by
    have h1 : (NQ + NE) ^ 2 ≤ 2 * (EQ + EE) := by
      have hs := sq_nonneg (NQ - NE)
      have hexp : 2 * (NQ ^ 2 + NE ^ 2) - (NQ + NE) ^ 2 = (NQ - NE) ^ 2 := by ring
      linarith only [hs, hexp, hgQ_sq_eq, hgE_sq_eq]
    have h2 : 2 * (EQ + EE) ≤ 4 * B_tot * Γ ^ k_abs * R_rate * F_norm ^ 2 := by
      linarith only [hEQ_EE]
    have h3 : 4 * B_tot * Γ ^ k_abs * R_rate ≤
        C_abs ^ 2 * (Γ ^ k_abs) ^ 2 * S_rate ^ 2 := by
      have p1 : (4 * B_tot) * Γ ^ k_abs ≤ C_abs ^ 2 * (Γ ^ k_abs) ^ 2 :=
        mul_le_mul hC_sq hΓ_pow_sq (by positivity) (by positivity)
      exact mul_le_mul p1 hR_le_S2 hR_nn (by positivity)
    calc (NQ + NE) ^ 2
        ≤ 4 * B_tot * Γ ^ k_abs * R_rate * F_norm ^ 2 := h1.trans h2
      _ ≤ (C_abs ^ 2 * (Γ ^ k_abs) ^ 2 * S_rate ^ 2) * F_norm ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg F_norm)
      _ = (C_abs * Γ ^ k_abs * S_rate * F_norm) ^ 2 := by ring
  have hRHS_nn : 0 ≤ C_abs * Γ ^ k_abs * S_rate * F_norm := by positivity
  have h_sum_le : NQ + NE ≤ C_abs * Γ ^ k_abs * S_rate * F_norm :=
    le_of_sq_le_sq_nonneg hRHS_nn h_sum_sq
  rw [hNorm_two_eq c gQ, hNorm_two_eq c gE,
    ← ENNReal.ofReal_toReal hgQ_fin.ne, ← ENNReal.ofReal_toReal hgE_fin.ne,
    ← ENNReal.ofReal_add hNQ0 hNE0, ← hF_ofReal,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h_sum_le

/-- **Proof of `BoxDiffusionAbsorption` (`PartII-b:T16/2/2`, SP 1963-1977 & 1982-1985)**. -/
theorem boxDiffusionAbsorption_proof : UnforcedLeray.Short.IIb.BoxDiffusionAbsorption := by
  intro k_chart C_chart hC_chart
  obtain ⟨Cp, hCp, hphys2⟩ := phys_graph_poly_two_given
  obtain ⟨Cf, hCf, hflat2⟩ := flat_graph_poly_two_given
  obtain ⟨M_st, hM_st1, hM_st⟩ := exists_deriv_smoothTransition_bound
  set K : ℝ := 3 * M_st
  have hK3 : 3 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := by linarith
  set B_tot : ℝ :=
    1440 * K ^ 2 + 2 * K + 168 * K * (Cf ^ 2 + Cp ^ 2) + C_chart
  have hB_pos : 0 < B_tot := by positivity
  set k_abs : ℕ := k_chart + 12
  set C_abs : ℝ := 4 * B_tot + 1
  refine ⟨k_abs, C_abs, by positivity, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ _h_cΓ _h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap
    hν hc hσ hσH₁ _hL₁0 ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0
    hF hbε_in hbε_resp hb0_resp hb0_class
    hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hom
  dsimp only
  intro henergy
  set χ := boxCutoff σ H₁ L₁
  set w := bε - b0
  set Qv := qepsOf ε b0 Sb0 Qb0 Eb0
  set Qw := Qbε - Qv
  set Ew := Ebε - Eb0
  set w_enl : CProf := indBox (σ / 2) (2 * H₁) (L₁ + 1) w
  set gQ : CProf := fun x => (χ x : ℂ) • sqrtS Qw x
  set gE : CProf := fun x => (χ x : ℂ) • sqrtS Ew x
  set rq : CProf := fun x => (((2 * Real.sqrt x.1 * vGrad (vQ ε) χ x : ℝ) : ℂ)) • w_enl x
  set re_eta : CProf := fun x => (((2 * Real.sqrt x.1 * vGrad vEta χ x : ℝ) : ℂ)) • w_enl x
  set F_norm : ℝ := (hNorm c 2 F).toReal
  have hF_norm0 : 0 ≤ F_norm := ENNReal.toReal_nonneg
  have hF_ofReal : ENNReal.ofReal F_norm = hNorm c 2 F :=
    ENNReal.ofReal_toReal hF.finite.ne
  have hχ_cd : ContDiff ℝ ∞ χ := boxCutoff_contDiff σ H₁ L₁
  have hcpd : ∀ y, |cpd 0 χ y| ≤ K * Γ ∧ cpd 1 χ y = 0 ∧ |cpd 2 χ y| ≤ K * Γ :=
    fun y => boxCutoff_cpd_bounds hM_st1 hM_st hσ hσH₁ hσΓ hΓ1 y
  have hgε := hphys2 Γ ν c ε μ hΓ1 hμΓ hgap hν hc hε0 hε1 hP F bε Sbε Qbε Ebε
    hF hbε_resp hSε hQε hEε
  have hg0 := hflat2 Γ ν c μ hΓ1 hμΓ hgap hν hc F b0 Sb0 Qb0 Eb0
    hF hb0_resp hb0_class hS0 hQ0 hE0
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  set fε : Coord → ℝ := fun x => ‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖
  set f0 : Coord → ℝ := fun x => ‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖
  have mbε : AEStronglyMeasurable bε (hMeas c 2) := hbε_in.meas
  have mb0 : AEStronglyMeasurable b0 (hMeas c 2) := hb0_class.inHr.meas
  have mfε : AEStronglyMeasurable fε (hMeas c 2) :=
    ((mbε.norm.add mSε.norm).add mQε.norm).add mEε.norm
  have mf0 : AEStronglyMeasurable f0 (hMeas c 2) :=
    ((mb0.norm.add mS0.norm).add mQ0.norm).add mE0.norm
  have hfε_lp : eLpNorm fε (ENNReal.ofReal 2) (hMeas c 2) ≤
      ENNReal.ofReal (Cp * Γ ^ 3 * F_norm) := by
    calc eLpNorm fε (ENNReal.ofReal 2) (hMeas c 2)
        ≤ ENNReal.ofReal Γ * (ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c 2 F) :=
          (eLpNorm_add4_norm_le hp1 mbε mSε mQε mEε).trans
            (graph_sum_le_of_graphBound hν hνΓ hΓ1 hgε)
      _ = ENNReal.ofReal (Cp * Γ ^ 3 * F_norm) := by
          rw [← hF_ofReal, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hf0_lp : eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2) ≤
      ENNReal.ofReal (Cf * Γ ^ 3 * F_norm) := by
    calc eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2)
        ≤ ENNReal.ofReal Γ * (ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F) :=
          (eLpNorm_add4_norm_le hp1 mb0 mS0 mQ0 mE0).trans
            (graph_sum_le_of_graphBound hν hνΓ hΓ1 hg0)
      _ = ENNReal.ofReal (Cf * Γ ^ 3 * F_norm) := by
          rw [← hF_ofReal, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  obtain ⟨hint_fε, h_int_fε_le⟩ :=
    integral_sq_le_of_eLpNorm_le (by positivity) mfε hfε_lp
  obtain ⟨hint_f0, h_int_f0_le⟩ :=
    integral_sq_le_of_eLpNorm_le (by positivity) mf0 hf0_lp
  have mw_enl : AEStronglyMeasurable w_enl (hMeas c 2) :=
    aestronglyMeasurable_indBox (σ / 2) (2 * H₁) (L₁ + 1) (mbε.sub mb0)
  have hw_enl_lp : eLpNorm w_enl 2 (hMeas c 2) ≤ ENNReal.ofReal (om * F_norm) := by
    rw [← hNorm_two_eq]
    calc hNorm c 2 w_enl ≤ ENNReal.ofReal om * hNorm c 2 F := hom
      _ = ENNReal.ofReal (om * F_norm) := by
          rw [← hF_ofReal, ← ENNReal.ofReal_mul hom0]
  have hw_enl_fin : eLpNorm w_enl 2 (hMeas c 2) < ⊤ :=
    lt_of_le_of_lt hw_enl_lp ENNReal.ofReal_lt_top
  obtain ⟨hint_wenl, h_wenl_eq⟩ := integral_norm_sq_eq_toReal_sq mw_enl hw_enl_fin
  have h_int_wenl_le : ∫ x, ‖w_enl x‖ ^ 2 ∂(hMeas c 2) ≤ om ^ 2 * F_norm ^ 2 := by
    rw [h_wenl_eq]
    have hle : (eLpNorm w_enl 2 (hMeas c 2)).toReal ≤ om * F_norm := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw_enl_lp
      rwa [ENNReal.toReal_ofReal (mul_nonneg hom0 hF_norm0)] at this
    calc (eLpNorm w_enl 2 (hMeas c 2)).toReal ^ 2
        ≤ (om * F_norm) ^ 2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
      _ = om ^ 2 * F_norm ^ 2 := by ring
  have mrq : AEStronglyMeasurable rq (hMeas c 2) := by
    have hm_coef : Measurable (fun x : Coord => (((2 * Real.sqrt x.1 * vGrad (vQ ε) χ x : ℝ) : ℂ))) :=
      Complex.measurable_ofReal.comp
        (((measurable_const.mul (Real.continuous_sqrt.measurable.comp measurable_fst)).mul
          (contDiff_vGrad (contDiff_vQ ε) hχ_cd).continuous.measurable))
    exact hm_coef.aestronglyMeasurable.smul mw_enl
  have mre_eta : AEStronglyMeasurable re_eta (hMeas c 2) := by
    have hm_coef : Measurable (fun x : Coord => (((2 * Real.sqrt x.1 * vGrad vEta χ x : ℝ) : ℂ))) :=
      Complex.measurable_ofReal.comp
        (((measurable_const.mul (Real.continuous_sqrt.measurable.comp measurable_fst)).mul
          (contDiff_vGrad contDiff_vEta hχ_cd).continuous.measurable))
    exact hm_coef.aestronglyMeasurable.smul mw_enl
  have hrq_ptw : ∀ x : Coord, ‖rq x‖ ≤ (24 * K * Γ ^ 3) * ‖w_enl x‖ := by
    intro x
    by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
    · obtain ⟨hbq, -, -⟩ := vGrad_boxCutoff_enl_bounds hK0.le hσ hH₁ hL₁ hΓ1 hε0 hε1 hcpd hx
      dsimp only [rq]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hbq (norm_nonneg _)
    · have hw0 : w_enl x = 0 := Set.indicator_of_notMem hx _
      simp [rq, hw0]
  have hre_ptw : ∀ x : Coord, ‖re_eta x‖ ≤ (24 * K * Γ ^ 3) * ‖w_enl x‖ := by
    intro x
    by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
    · obtain ⟨-, hbe, -⟩ := vGrad_boxCutoff_enl_bounds hK0.le hσ hH₁ hL₁ hΓ1 hε0 hε1 hcpd hx
      dsimp only [re_eta]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hbe (norm_nonneg _)
    · have hw0 : w_enl x = 0 := Set.indicator_of_notMem hx _
      simp [re_eta, hw0]
  have hrq_fin : eLpNorm rq 2 (hMeas c 2) < ⊤ :=
    eLpNorm_two_lt_top_of_norm_le hrq_ptw hw_enl_fin
  have hre_fin : eLpNorm re_eta 2 (hMeas c 2) < ⊤ :=
    eLpNorm_two_lt_top_of_norm_le hre_ptw hw_enl_fin
  obtain ⟨hint_rq, _⟩ := integral_norm_sq_eq_toReal_sq mrq hrq_fin
  obtain ⟨hint_re, _⟩ := integral_norm_sq_eq_toReal_sq mre_eta hre_fin
  have h_int_rq_le : ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2) ≤
      576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2 := by
    have hm : ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2) ≤
        ∫ x, ((24 * K * Γ ^ 3) ^ 2 * ‖w_enl x‖ ^ 2) ∂(hMeas c 2) := by
      refine integral_mono hint_rq (hint_wenl.const_mul _) fun x => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hrq_ptw x) 2
      simpa [mul_pow] using this
    rw [integral_const_mul] at hm
    calc ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2)
        ≤ (24 * K * Γ ^ 3) ^ 2 * (om ^ 2 * F_norm ^ 2) :=
          hm.trans (mul_le_mul_of_nonneg_left h_int_wenl_le (by positivity))
      _ = 576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2 := by ring
  have h_int_re_le : ∫ x, ‖re_eta x‖ ^ 2 ∂(hMeas c 2) ≤
      576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2 := by
    have hm : ∫ x, ‖re_eta x‖ ^ 2 ∂(hMeas c 2) ≤
        ∫ x, ((24 * K * Γ ^ 3) ^ 2 * ‖w_enl x‖ ^ 2) ∂(hMeas c 2) := by
      refine integral_mono hint_re (hint_wenl.const_mul _) fun x => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hre_ptw x) 2
      simpa [mul_pow] using this
    rw [integral_const_mul] at hm
    calc ∫ x, ‖re_eta x‖ ^ 2 ∂(hMeas c 2)
        ≤ (24 * K * Γ ^ 3) ^ 2 * (om ^ 2 * F_norm ^ 2) :=
          hm.trans (mul_le_mul_of_nonneg_left h_int_wenl_le (by positivity))
      _ = 576 * K ^ 2 * Γ ^ 6 * om ^ 2 * F_norm ^ 2 := by ring
  obtain ⟨mgQ, hgQ_fin, mgE, hgE_fin⟩ :=
    gQ_gE_eLpNorm_lt_top hΓ1 hσ hσH₁ hH₁ hL₁ hε0 hε1
      bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 mb0 mQε mEε mS0 mQ0 mE0 mfε mf0 hfε_lp hf0_lp
  obtain ⟨hint_gQ, hgQ_sq_eq⟩ := integral_norm_sq_eq_toReal_sq mgQ hgQ_fin
  obtain ⟨hint_gE, hgE_sq_eq⟩ := integral_norm_sq_eq_toReal_sq mgE hgE_fin
  have hLHS_Q := lhs_pairing_lower_bound hσ hσH₁ (vQ ε) w Qw mgQ hgQ_fin mrq hrq_fin
  have hLHS_E := lhs_pairing_lower_bound hσ hσH₁ vEta w Ew mgE hgE_fin mre_eta hre_fin
  have hRHS_drift :
      ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) ≤
        2 * K * Γ ^ 2 * om ^ 2 * F_norm ^ 2 := by
    have hnorm_le : ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) ≤
        ∫ x, ‖x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2‖ ∂(hMeas c 2) :=
      (le_abs_self _).trans (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _)
    have hm : ∫ x, ‖x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2‖ ∂(hMeas c 2) ≤
        ∫ x, ((2 * K * Γ ^ 2) * ‖w_enl x‖ ^ 2) ∂(hMeas c 2) := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (hint_wenl.const_mul _) (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
      · obtain ⟨hx1_pos, hx1_le, -, -⟩ := enl_coord_bounds hσ hH₁ hL₁ hΓ1 hx
        obtain ⟨hc0, -, -⟩ := hcpd x
        have hw_eq : w_enl x = w x := Set.indicator_of_mem hx _
        dsimp only
        rw [← cmerid_norm_sq (w x), ← hw_eq, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_pos hx1_pos, abs_of_nonneg (boxCutoff_nonneg σ H₁ L₁ x),
          abs_of_nonneg (sq_nonneg ‖w_enl x‖)]
        have hcoef : x.1 * χ x * |cpd 0 χ x| ≤ 2 * K * Γ ^ 2 := by
          calc x.1 * χ x * |cpd 0 χ x|
              ≤ (2 * Γ) * 1 * (K * Γ) := by
                have p1 : x.1 * χ x ≤ (2 * Γ) * 1 :=
                  mul_le_mul hx1_le (boxCutoff_le_one σ H₁ L₁ x)
                    (boxCutoff_nonneg σ H₁ L₁ x) (by linarith only [hΓ1])
                exact mul_le_mul p1 hc0 (abs_nonneg _) (by linarith only [hΓ1])
            _ = 2 * K * Γ ^ 2 := by ring
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      · have hχ0 : χ x = 0 := boxCutoff_eq_zero_of_notMem hσ hσH₁ hx
        have hw0 : w_enl x = 0 := Set.indicator_of_notMem hx _
        simp [hχ0, hw0]
    rw [integral_const_mul] at hm
    calc ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2)
        ≤ (2 * K * Γ ^ 2) * (om ^ 2 * F_norm ^ 2) :=
          (hnorm_le.trans hm).trans
            (mul_le_mul_of_nonneg_left h_int_wenl_le (by positivity))
      _ = 2 * K * Γ ^ 2 * om ^ 2 * F_norm ^ 2 := by ring
  set ψ : Coord → ℝ := fun x => χ x ^ 2
  set Sw := Sbε - Sb0
  set t : CProf := fun x => (ψ x : ℂ) • w x
  set St := weakSmul vS ψ w Sw
  set Qt := weakSmul (vQ ε) ψ w Qw
  set Et := weakSmul vEta ψ w Ew
  set Z_diff : Coord → ℂ := fun x =>
    (x.1 : ℂ) * ∑ i : Fin 2,
      ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
        Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))
  have hRHS_diff :
      ε * (∫ x, Z_diff x ∂(hMeas c 2)).re ≤
        (1 / 4) * ∫ x, ‖gQ x‖ ^ 2 ∂(hMeas c 2) +
          (1 / 2) * ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2) +
          168 * K * Γ ^ 4 * ε *
            (∫ x, f0 x ^ 2 ∂(hMeas c 2) + ∫ x, fε x ^ 2 ∂(hMeas c 2)) := by
    have hre_le : ε * (∫ x, Z_diff x ∂(hMeas c 2)).re ≤
        ∫ x, ε * ‖Z_diff x‖ ∂(hMeas c 2) := by
      rw [integral_const_mul]
      have h1 : (∫ x, Z_diff x ∂(hMeas c 2)).re ≤ ‖∫ x, Z_diff x ∂(hMeas c 2)‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      exact mul_le_mul_of_nonneg_left (h1.trans (norm_integral_le_integral_norm _)) hε0.le
    have hint_maj : Integrable (fun x : Coord =>
        (1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 +
          168 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2)) (hMeas c 2) :=
      ((hint_gQ.const_mul (1 / 4)).add (hint_rq.const_mul (1 / 2))).add
        ((hint_f0.add hint_fε).const_mul (168 * K * Γ ^ 4 * ε))
    have hm := integral_mono_of_nonneg
      (ae_of_all _ fun _ => mul_nonneg hε0.le (norm_nonneg _)) hint_maj
      (ae_of_all _ fun x =>
        diff_integrand_pointwise_bound hK3 hσ hσH₁ hH₁ hL₁ hΓ1 hε0 hε1
          bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 hcpd x)
    have h_maj_eq : ∫ x, ((1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 +
          168 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2)) ∂(hMeas c 2) =
        (1 / 4) * ∫ x, ‖gQ x‖ ^ 2 ∂(hMeas c 2) +
          (1 / 2) * ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2) +
          168 * K * Γ ^ 4 * ε *
            (∫ x, f0 x ^ 2 ∂(hMeas c 2) + ∫ x, fε x ^ 2 ∂(hMeas c 2)) := by
      calc ∫ x, ((1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2 +
              168 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2)) ∂(hMeas c 2)
          = ∫ x, ((1 / 4) * ‖gQ x‖ ^ 2 + (1 / 2) * ‖rq x‖ ^ 2) ∂(hMeas c 2) +
              ∫ x, (168 * K * Γ ^ 4 * ε * (f0 x ^ 2 + fε x ^ 2)) ∂(hMeas c 2) :=
            integral_add ((hint_gQ.const_mul (1 / 4)).add (hint_rq.const_mul (1 / 2)))
              ((hint_f0.add hint_fε).const_mul _)
        _ = ((1 / 4) * ∫ x, ‖gQ x‖ ^ 2 ∂(hMeas c 2) +
              (1 / 2) * ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2)) +
            168 * K * Γ ^ 4 * ε *
              (∫ x, f0 x ^ 2 ∂(hMeas c 2) + ∫ x, fε x ^ 2 ∂(hMeas c 2)) := by
            rw [integral_add (hint_gQ.const_mul (1 / 4)) (hint_rq.const_mul (1 / 2)),
                integral_const_mul, integral_const_mul, integral_const_mul,
                integral_add hint_f0 hint_fε]
    exact (hre_le.trans hm).trans_eq h_maj_eq
  set EQ : ℝ := ∫ x, ‖gQ x‖ ^ 2 ∂(hMeas c 2)
  set EE : ℝ := ∫ x, ‖gE x‖ ^ 2 ∂(hMeas c 2)
  set IR : ℝ := ∫ x, ‖rq x‖ ^ 2 ∂(hMeas c 2)
  set IE : ℝ := ∫ x, ‖re_eta x‖ ^ 2 ∂(hMeas c 2)
  have hEE_nn : 0 ≤ EE := integral_nonneg fun _ => sq_nonneg _
  have hIR_nn : 0 ≤ IR := integral_nonneg fun _ => sq_nonneg _
  have hIE_nn : 0 ≤ IE := integral_nonneg fun _ => sq_nonneg _
  have hIf0_nn : 0 ≤ ∫ x, f0 x ^ 2 ∂(hMeas c 2) := integral_nonneg fun _ => sq_nonneg _
  have hIfε_nn : 0 ≤ ∫ x, fε x ^ 2 ∂(hMeas c 2) := integral_nonneg fun _ => sq_nonneg _
  have h_abs_step :
      (1 / 2) * ν * (EQ + EE) ≤
        (3 / 2) * ν * IR + ν * IE +
          2 * K * Γ ^ 2 * om ^ 2 * F_norm ^ 2 +
          168 * K * Γ ^ 4 * ν * ε *
            (∫ x, f0 x ^ 2 ∂(hMeas c 2) + ∫ x, fε x ^ 2 ∂(hMeas c 2)) +
          C_chart * Γ ^ k_chart * (om + om ^ 2 + ε) * F_norm ^ 2 := by
    have hLHS_Q' : (3 / 4) * EQ - IR ≤
        (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)).re :=
      hLHS_Q
    have hLHS_E' : (3 / 4) * EE - IE ≤
        (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2)).re :=
      hLHS_E
    have hL1 := mul_le_mul_of_nonneg_left hLHS_Q' hν.le
    have hL2 := mul_le_mul_of_nonneg_left hLHS_E' hν.le
    have hR2 := mul_le_mul_of_nonneg_left hRHS_diff hν.le
    have hexp_L : ν * ((3 / 4) * EQ - IR) + ν * ((3 / 4) * EE - IE) =
        (3 / 4) * ν * EQ + (3 / 4) * ν * EE - ν * IR - ν * IE := by ring
    have hexp_R : ν * ((1 / 4) * EQ + (1 / 2) * IR +
          168 * K * Γ ^ 4 * ε * (∫ x, f0 x ^ 2 ∂(hMeas c 2) + ∫ x, fε x ^ 2 ∂(hMeas c 2))) =
        (1 / 4) * ν * EQ + (1 / 2) * ν * IR +
          168 * K * Γ ^ 4 * ν * ε *
            (∫ x, f0 x ^ 2 ∂(hMeas c 2) + ∫ x, fε x ^ 2 ∂(hMeas c 2)) := by ring
    have hexp_Z : ν * (ε * (∫ x, Z_diff x ∂(hMeas c 2)).re) =
        ν * ε * (∫ x, Z_diff x ∂(hMeas c 2)).re := by ring
    have hexp_goal : (1 / 2) * ν * (EQ + EE) = (1 / 2) * ν * EQ + (1 / 2) * ν * EE := by ring
    have hEE_pos : 0 ≤ (1 / 4) * ν * EE := by positivity
    linarith only [hL1, hL2, hR2, hRHS_drift, henergy, hexp_L, hexp_R, hexp_Z, hexp_goal, hEE_pos]
  exact final_rate_norm_bound hC_chart hK0 hΓ1 hν hνΓ1 hνΓ hom0 hε0 hF_norm0 hF_ofReal
    hgQ_fin hgE_fin hgQ_sq_eq hgE_sq_eq hEE_nn hIR_nn hIE_nn hIf0_nn hIfε_nn
    h_int_rq_le h_int_re_le h_int_f0_le h_int_fε_le h_abs_step

end UnforcedLeray.Short.IIb

end
