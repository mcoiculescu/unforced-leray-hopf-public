import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.HDeriv3

/-!
# `primH_main`: differentiation of `h ↦ primInt (xKerA h) (λ(h) z) q` under the integral
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem primE0_norm : ‖(primE0 : Space)‖ = 1 := by simp [primE0]

theorem lam_mul_le {l a ρ₀ : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hρ₀ : 0 ≤ ρ₀) (ha : a ≤ ρ₀) :
    l * a ≤ ρ₀ := by
  by_cases h : 0 ≤ a
  · nlinarith
  · push Not at h; nlinarith

theorem primH_main (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ),
      ContDiff ℝ 2 (fun x' => xKer ν μ h x' M) ∧
      (∀ x : Space, DifferentiableAt ℝ (fun h' => xKer ν μ h' x M) h) ∧
      ∀ x : Space, x ≠ 0 →
        ‖xKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M ∧
        ‖fderiv ℝ (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 5)⁻¹ * IIIa.tensorNorm M ∧
        ‖iteratedFDeriv ℝ 2 (fun x' => xKer ν μ h x' M) x‖ ≤
          C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 6)⁻¹ * IIIa.tensorNorm M ∧
        ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
          C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M ∧
        ‖wKer ν μ h x M‖ ≤ C * pdLam h ^ (2 * μ + 3) * (‖x‖ ^ 4)⁻¹ * IIIa.tensorNorm M)
    (ν μ : ℝ) (hν : 0 < ν) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (z q : Space) {ρ₀ δ Yq : ℝ} (hρ₀ : 0 ≤ ρ₀) (hδ : 0 < δ) (hY : 0 ≤ Yq) (hqY : ‖q‖ ≤ Yq)
    (hz0 : z 0 ≤ ρ₀) (hq : ρ₀ + δ < q 0) {h0 : ℝ} (hh0 : 0 < h0) :
    ∃ d : ℝ, HasDerivAt (fun h' => primInt (xKerA ν μ h' M) (pdLam h' • z) q) d h0 ∧
      |d| ≤ ((ρ₀ / δ + 1) * (3 + ν * (δ ^ 2)⁻¹ + Yq / δ)) *
        (C * pdLam h0 ^ (2 * μ + 3) * IIIa.tensorNorm M) *
        (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - pdLam h0 * z 2) ^ 2))) := by
  set T := IIIa.tensorNorm M with hT
  have hT0 : 0 ≤ T := kb_tensor_nonneg M
  set C₃ := (ρ₀ / δ + 1) * (3 + ν * (δ ^ 2)⁻¹ + Yq / δ) with hC₃
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  set x : ℝ → ℝ → Space := fun h u => q + (u • primE0 - pdLam h • z) with hx
  set F' : ℝ → ℝ → ℝ := fun h u =>
    (q 0 + u) * fderiv ℝ (Jt ν μ M) (h, x h u) (1, (pdLam h / 2) • z) with hF'
  set F : ℝ → ℝ → ℝ := fun h u => primF (xKerA ν μ h M) (pdLam h • z) q u with hF
  set μm : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμm
  have hae : ∀ᵐ u ∂μm, 0 < u := by
    rw [hμm]; exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => hu)
  -- the pointwise bound for F'
  have Fp : ∀ h' : ℝ, 0 < h' → ∀ u : ℝ, 0 < u → ∀ b : ℝ, b ^ 2 ≤ (q 2 - pdLam h' * z 2) ^ 2 →
      ∀ K : ℝ, C * pdLam h' ^ (2 * μ + 3) * T ≤ K →
      |F' h' u| ≤ C₃ * K * ((q 0 + u - ρ₀) * ((((q 0 + u - ρ₀) ^ 2 + b ^ 2) ^ 2)⁻¹)) := by
    intro h' hh' u hu b hb K hK
    have hl0 := pdLam_pos h'
    have hl1 := (pdLam_lt_one hh').le
    have hw0 : (pdLam h' • z) 0 ≤ ρ₀ := by
      simpa using lam_mul_le hl0 hl1 hρ₀ hz0
    have hlow := prim_shift_lower q (pdLam h' • z) u ρ₀ hw0 (by linarith)
    set v := q 0 + u - ρ₀ with hv
    have hvδ : δ ≤ v := by rw [hv]; linarith
    have hb' : v ^ 2 + b ^ 2 ≤ ‖x h' u‖ ^ 2 := by
      have : (q 2 - (pdLam h' • z) 2) ^ 2 = (q 2 - pdLam h' * z 2) ^ 2 := by simp
      simp only [hx]; nlinarith
    have hxne : x h' u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hb'
      have : 0 < v ^ 2 := by have := lt_of_lt_of_le hδ hvδ; positivity
      nlinarith [sq_nonneg b]
    have hdir := Jt_dir_bound C hC0 hC ν μ hν hμ0 hμ1 hh' M hxne ((pdLam h' / 2) • z)
    have hvn : ‖(pdLam h' / 2) • z‖ ≤ ‖pdLam h' • z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl0,
        abs_of_pos (by linarith : 0 < pdLam h' / 2)]
      have := norm_nonneg z
      nlinarith
    have hWle : ‖pdLam h' • z‖ ≤ ‖x h' u‖ + Yq + v := by
      have e : pdLam h' • z = q + u • primE0 - x h' u := by simp only [hx]; abel
      rw [e]
      calc ‖q + u • primE0 - x h' u‖ ≤ ‖q + u • primE0‖ + ‖x h' u‖ := norm_sub_le _ _
        _ ≤ (‖q‖ + ‖u • primE0‖) + ‖x h' u‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖x h' u‖ + Yq + v := by
          rw [norm_smul, Real.norm_eq_abs, primE0_norm, abs_of_pos hu, mul_one]
          have : u ≤ v := by rw [hv]; have : ρ₀ ≤ q 0 := by linarith
                             linarith
          linarith
    have hKe : C * pdLam h' ^ (2 * μ + 3) * T ≤ K := hK
    have hbd := primPtH (K := K) (ρ₀ := ρ₀) (δ := δ) (v := v) (b := b) (t := ‖x h' u‖) (Yq := Yq)
      (ν := ν) (W := ‖pdLam h' • z‖) ((by positivity : 0 ≤ C * pdLam h' ^ (2 * μ + 3) * T).trans hKe)
      hρ₀ hδ hvδ hν.le hY hb' (norm_nonneg _) (norm_nonneg _) hWle
    have hpos : q 0 + u = ρ₀ + v := by rw [hv]; ring
    have hab : |q 0 + u| = ρ₀ + v := by rw [hpos]; exact abs_of_nonneg (by linarith)
    have h1 : |fderiv ℝ (Jt ν μ M) (h', x h' u) (1, (pdLam h' / 2) • z)| ≤
        K * ((‖x h' u‖ ^ 4)⁻¹ + ν * (‖x h' u‖ ^ 6)⁻¹ + (‖x h' u‖ ^ 5)⁻¹ * ‖pdLam h' • z‖) := by
      refine hdir.trans ?_
      have hnn : 0 ≤ ((‖x h' u‖ ^ 4)⁻¹ + ν * (‖x h' u‖ ^ 6)⁻¹ + (‖x h' u‖ ^ 5)⁻¹ * ‖(pdLam h' / 2) • z‖) := by
        positivity
      have h2 : (‖x h' u‖ ^ 5)⁻¹ * ‖(pdLam h' / 2) • z‖ ≤ (‖x h' u‖ ^ 5)⁻¹ * ‖pdLam h' • z‖ :=
        mul_le_mul_of_nonneg_left hvn (by positivity)
      calc C * pdLam h' ^ (2 * μ + 3) * T * ((‖x h' u‖ ^ 4)⁻¹ + ν * (‖x h' u‖ ^ 6)⁻¹ +
            (‖x h' u‖ ^ 5)⁻¹ * ‖(pdLam h' / 2) • z‖)
          ≤ K * ((‖x h' u‖ ^ 4)⁻¹ + ν * (‖x h' u‖ ^ 6)⁻¹ + (‖x h' u‖ ^ 5)⁻¹ * ‖(pdLam h' / 2) • z‖) :=
            mul_le_mul_of_nonneg_right hKe hnn
        _ ≤ K * ((‖x h' u‖ ^ 4)⁻¹ + ν * (‖x h' u‖ ^ 6)⁻¹ + (‖x h' u‖ ^ 5)⁻¹ * ‖pdLam h' • z‖) := by
            apply mul_le_mul_of_nonneg_left _ ((by positivity : 0 ≤ C * pdLam h' ^ (2 * μ + 3) * T).trans hKe)
            linarith
    show |(q 0 + u) * _| ≤ _
    rw [abs_mul, hab]
    calc (ρ₀ + v) * |fderiv ℝ (Jt ν μ M) (h', x h' u) (1, (pdLam h' / 2) • z)|
        ≤ (ρ₀ + v) * (K * ((‖x h' u‖ ^ 4)⁻¹ + ν * (‖x h' u‖ ^ 6)⁻¹ +
            (‖x h' u‖ ^ 5)⁻¹ * ‖pdLam h' • z‖)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ _ := hbd
  -- crude majorant
  have hJ0 := primJ2 hδ 0
  set Bm : ℝ → ℝ := fun u => C₃ * (C * T) * ((δ + u) * (((δ + u) ^ 2 + 0 ^ 2) ^ 2)⁻¹) with hBm
  have hBmi : Integrable Bm μm := hJ0.1.const_mul _
  set s : Set ℝ := Metric.ball h0 (h0 / 2) with hs
  have hspos : ∀ h' ∈ s, 0 < h' := fun h' hh' => by
    have := Metric.mem_ball.1 hh'
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).1
    linarith
  have hsmem : s ∈ 𝓝 h0 := Metric.ball_mem_nhds _ (by linarith)
  have hKmono : ∀ h' : ℝ, 0 < h' → C * pdLam h' ^ (2 * μ + 3) * T ≤ C * T := by
    intro h' hh'
    have hlam := (kb_coef_bounds μ h' hμ0 hμ1 hh').2.2.2
    have h1 := mul_le_mul_of_nonneg_left hlam hC0
    have := mul_le_mul_of_nonneg_right h1 hT0
    simpa using this
  have hzero : ∀ h' : ℝ, (0 : ℝ) ^ 2 ≤ (q 2 - pdLam h' * z 2) ^ 2 := fun h' => by
    simpa using sq_nonneg (q 2 - pdLam h' * z 2)
  have hcrude : ∀ᵐ u ∂μm, ∀ h' ∈ s, ‖F' h' u‖ ≤ Bm u := hae.mono fun u hu h' hh' => by
    have hh'0 := hspos h' hh'
    have := Fp h' hh'0 u hu 0 (hzero h') (C * T) (hKmono h' hh'0)
    have hv : δ + u ≤ q 0 + u - ρ₀ := by linarith
    have hd := prim_dec (by linarith : 0 < δ + u) hv
    rw [Real.norm_eq_abs]
    refine this.trans ?_
    have hc : 0 ≤ C₃ * (C * T) := by positivity
    calc C₃ * (C * T) * ((q 0 + u - ρ₀) * ((((q 0 + u - ρ₀) ^ 2 + 0 ^ 2) ^ 2)⁻¹))
        ≤ C₃ * (C * T) * ((δ + u) * (((δ + u) ^ 2 + 0 ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hd hc
      _ = Bm u := rfl
  -- derivative
  have hdiff : ∀ᵐ u ∂μm, ∀ h' ∈ s, HasDerivAt (fun h => F h u) (F' h' u) h' := by
    refine Filter.Eventually.of_forall fun u h' hh' => ?_
    have hh'0 := hspos h' hh'
    have hxd : HasDerivAt (fun h => x h u) ((pdLam h' / 2) • z) h' := by
      have h1 := (pdLam_hasDerivAt h').smul_const z
      have h2 := (h1.const_sub (u • primE0)).const_add q
      refine h2.congr_deriv ?_
      rw [← neg_smul]; congr 1; ring
    have hJd := (Jt_diffAt ν μ hν M hh'0 (x h' u)).hasFDerivAt.comp_hasDerivAt h'
      ((hasDerivAt_id h').prodMk hxd)
    exact hJd.const_mul (q 0 + u)
  -- measurability
  have hcont_x : Continuous (fun u : ℝ => x h0 u) := by
    simp only [hx]
    exact continuous_const.add ((continuous_id.smul continuous_const).sub continuous_const)
  have hFmeas : ∀ h' : ℝ, 0 < h' → Continuous (F h') := by
    intro h' hh'
    obtain ⟨hcd, -⟩ := xKerA_props C hC0 hC ν μ h' hν hμ0 hμ1 hh' M
    show Continuous (fun u => (q 0 + u) * xKerA ν μ h' M (x h' u))
    exact (continuous_const.add continuous_id).mul
      (hcd.continuous.comp (continuous_const.add ((continuous_id.smul continuous_const).sub continuous_const)))
  have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hF'cont : Continuous (F' h0) := by
    have hfc : ContinuousOn (fderiv ℝ (Jt ν μ M)) {p : ℝ × Space | 0 < p.1} :=
      (Jt_contDiffOn ν μ hν M).continuousOn_fderiv_of_isOpen hopen (by norm_num)
    have hap : ContinuousOn (fun p : ℝ × Space => fderiv ℝ (Jt ν μ M) p (1, (pdLam h0 / 2) • z))
        {p : ℝ × Space | 0 < p.1} :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (pdLam h0 / 2) • z)).continuous.comp_continuousOn hfc
    have hmaps : ∀ u, (h0, x h0 u) ∈ {p : ℝ × Space | 0 < p.1} := fun u => hh0
    have hcomp : Continuous (fun u : ℝ => fderiv ℝ (Jt ν μ M) (h0, x h0 u) (1, (pdLam h0 / 2) • z)) :=
      hap.comp_continuous (continuous_const.prodMk hcont_x) hmaps
    exact (continuous_const.add continuous_id).mul hcomp
  -- integrability of F h0
  have hFint : Integrable (F h0) μm := by
    obtain ⟨hcd, b0, b1, b2⟩ := xKerA_props C hC0 hC ν μ h0 hν hμ0 hμ1 hh0 M
    have hKm := hKmono h0 hh0
    have hcT : 0 ≤ C * T := by positivity
    have hw0 : (pdLam h0 • z) 0 ≤ ρ₀ := by
      simpa using lam_mul_le (pdLam_pos h0) (pdLam_lt_one hh0).le hρ₀ hz0
    have hBi : Integrable (fun u => primCp ρ₀ δ * (C * T) * ((δ + u) * (((δ + u) ^ 2 + 0 ^ 2) ^ 2)⁻¹)) μm :=
      hJ0.1.const_mul _
    refine Integrable.mono' hBi (hFmeas h0 hh0).aestronglyMeasurable (hae.mono fun u hu => ?_)
    have hp := (prim_pt hcd (pdLam h0 • z) q hcT hρ₀ hδ hw0
      (fun y hy => (b0 y hy).trans (mul_le_mul_of_nonneg_right hKm (by positivity)))
      (fun y hy => (b1 y hy).trans (mul_le_mul_of_nonneg_right hKm (by positivity)))
      (fun y hy => (b2 y hy).trans (mul_le_mul_of_nonneg_right hKm (by positivity)))
      u hu.le (by linarith) 0 (hzero h0)).1
    rw [norm_iteratedFDeriv_zero] at hp
    have hv : δ + u ≤ q 0 + u - ρ₀ := by linarith
    have hd := prim_dec (by linarith : 0 < δ + u) hv
    have hc : 0 ≤ primCp ρ₀ δ * (C * T) := mul_nonneg (primCp_nonneg hρ₀ hδ) hcT
    refine hp.trans ?_
    calc primCp ρ₀ δ * (C * T) * ((q 0 + u - ρ₀) * ((((q 0 + u - ρ₀) ^ 2 + 0 ^ 2) ^ 2)⁻¹))
        ≤ primCp ρ₀ δ * (C * T) * ((δ + u) * (((δ + u) ^ 2 + 0 ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hd hc
      _ = _ := rfl
  obtain ⟨-, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μm) (F := F) (F' := F')
    hsmem (Filter.eventually_of_mem hsmem fun h' hh' => (hFmeas h' (hspos h' hh')).aestronglyMeasurable)
    hFint hF'cont.aestronglyMeasurable hcrude hBmi hdiff
  refine ⟨∫ u, F' h0 u ∂μm, hder, ?_⟩
  -- the sharp bound
  have ha : 0 < q 0 - ρ₀ := by linarith
  obtain ⟨hJi, hJv⟩ := primJ2 ha (q 2 - pdLam h0 * z 2)
  have hI : ∫ u in Ioi (0 : ℝ), C₃ * (C * pdLam h0 ^ (2 * μ + 3) * T) *
      ((q 0 - ρ₀ + u) * ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - pdLam h0 * z 2) ^ 2) ^ 2)⁻¹))
      = C₃ * (C * pdLam h0 ^ (2 * μ + 3) * T) * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - pdLam h0 * z 2) ^ 2))) := by
    rw [integral_const_mul, hJv]
  have hIi : Integrable (fun u : ℝ => C₃ * (C * pdLam h0 ^ (2 * μ + 3) * T) *
      ((q 0 - ρ₀ + u) * ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - pdLam h0 * z 2) ^ 2) ^ 2)⁻¹))) μm :=
    hJi.const_mul _
  have := norm_integral_le_of_norm_le (μ := μm) hIi (hae.mono fun u hu => by
    have := Fp h0 hh0 u hu (q 2 - pdLam h0 * z 2) le_rfl _ le_rfl
    have e : q 0 + u - ρ₀ = q 0 - ρ₀ + u := by ring
    rw [e] at this
    rw [Real.norm_eq_abs]
    exact this)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_of_eq hI)

end UnforcedLeray.Short.PartIIIb.Concrete

end
