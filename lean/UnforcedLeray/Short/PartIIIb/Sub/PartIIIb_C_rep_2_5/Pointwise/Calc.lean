import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Cutoff

/-!
# `PartIII-b:C/rep/2/5`, pointwise leaf: the derivative of the stream cutoff (source 4181-4192)

On the annulus, `D(𝒞_y Z) = χ_y DZ + Z ⊗ ∇χ_y + D((χ_y'/ϱ) Ψ e_z)`; here the operator-norm bound
`‖D(𝒞_y Z)‖ ≤ ‖DZ‖ + 2M₁L⁻¹‖Z‖ + 2M₁L⁻²‖DΨ‖ + (4M₂+8M₁)L⁻³|Ψ|` for `L ≤ ϱ`, `L² = νR²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `‖Dϱ‖ ≤ 1` off the axis. -/
theorem wgx_ϱD_le {y : Space} (hy : 0 < ϱ y) (v : Space) : |ϱD y v| ≤ ‖v‖ := by
  rw [ϱD_apply, abs_div, abs_of_pos hy, div_le_iff₀ hy]
  have hn : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three]
  have h : (y 0 * v 0 + y 1 * v 1) ^ 2 ≤ (‖v‖ * ϱ y) ^ 2 := by
    rw [mul_pow, ϱ_sq, hn]
    nlinarith [sq_nonneg (y 0 * v 1 - y 1 * v 0), sq_nonneg (v 2), sq_nonneg (y 0),
      sq_nonneg (y 1)]
  exact abs_le_of_sq_le_sq h (by positivity)

theorem wgx_norm_ϱD_le {y : Space} (hy : 0 < ϱ y) : ‖ϱD y‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [Real.norm_eq_abs, one_mul]
  exact wgx_ϱD_le hy v

theorem wgx_abs_apply_le (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

/-- The outward primitive is differentiable in `y`, with the derivative `ϱ Z_z Dϱ - ϱ Z_r dy₃`
(`∂_rΨ = ϱ Z_z`, `∂_zΨ = -ϱ Z_r`, source 4178-4179). -/
theorem wgx_outPrim_hasFDerivAt {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {Z : ℝ → Space → Space}
    {τ : ℝ} (hZ : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdr : ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim Z τ r' z) (r * Z τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim Z τ r z') (-(r * Z τ !₂[r, 0, z] 0)) z)
    {y : Space} (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    HasFDerivAt (fun y : Space => outPrim Z τ (ϱ y) (y 2))
      ((ϱ y * Z τ !₂[ϱ y, 0, y 2] 2) • ϱD y +
        (-(ϱ y * Z τ !₂[ϱ y, 0, y 2] 0)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ))
      y := by
  have hS : IsOpen {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hm : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := by
    have hv : ContDiff ℝ 2 (fun p : ℝ × ℝ => (![p.1, 0, p.2] : Fin 3 → ℝ)) :=
      contDiff_pi.2 (fun i => by fin_cases i <;> simp <;> fun_prop)
    have : ContDiff ℝ 2 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) :=
      PiLp.contDiff_toLp.comp hv
    exact this.contDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} (youngOpen ν R) := by
    intro p hp
    have hp' : R * Real.sqrt (5 * ν / 6) < p.1 := hp
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[p.1, 0, p.2] : Space)
    have hϱ : ϱ (!₂[p.1, 0, p.2] : Space) = |p.1| := by simp [ϱ, Real.sqrt_sq_eq_abs]
    rw [hϱ]
    exact lt_of_lt_of_le hp' (le_abs_self _)
  have hPc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    contDiffOn_fst.mul ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hZ.comp hm hmaps))
  have hQc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    (contDiffOn_fst.mul ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hZ.comp hm hmaps))).neg
  have hpS : (ϱ y, y 2) ∈ {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := hy
  have hD := t9_hasFDerivAt_of_partials _ hS (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
      (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      hPc.continuousOn hQc.continuousOn
      (fun p hp => (hdr p.1 p.2 hp).1) (fun p hp => (hdr p.1 p.2 hp).2) (ϱ y, y 2) hpS
  have hna : y ∉ axis := t9_not_axis hν hR hy
  have hmer := hasFDerivAt_mer hna
  have hc := hD.comp y hmer
  refine hc.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [merD_apply]

/-- The cutoff field `χ_y(ν age) Z + G(ϱ) Ψ e_z` is differentiable, with an operator-norm bound
on its derivative (source 4181-4192). -/
theorem wgx_cut_hasFDerivAt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {M1 M2 : ℝ}
    (hM1 : ∀ t, |deriv χ t| ≤ M1) (hM2 : ∀ t, |deriv (deriv χ) t| ≤ M2)
    {ν R L : ℝ} (hν : 0 < ν) (hL : 0 < L) (hLsq : ν * R ^ 2 = L ^ 2) {y : Space}
    (hy1 : L ≤ ϱ y) {Z : Space → Space} {Zd : Space →L[ℝ] Space} (hZ : HasFDerivAt Z Zd y)
    {Ψ : Space → ℝ} {Ψd : Space →L[ℝ] ℝ} (hΨ : HasFDerivAt Ψ Ψd y) {K : ℝ} (hK : ‖Ψd‖ ≤ K) :
    ∃ D : Space →L[ℝ] Space, HasFDerivAt
      (fun y => χ (ν * age R y) • Z y +
        (deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y * Ψ y) • coordinateVector 2)
      D y ∧
      ‖D‖ ≤ ‖Zd‖ + 2 * M1 * L⁻¹ * ‖Z y‖ + 2 * M1 * (L⁻¹) ^ 2 * K +
        (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 * |Ψ y| := by
  have hρ0 : 0 < ϱ y := lt_of_lt_of_le hL hy1
  have hna : y ∉ axis := fun h => by
    have := (mem_axis_iff y).1 h
    linarith
  obtain ⟨G', hG', hG'b⟩ := wgx_G_deriv hχ hM1 hM2 hν hL hLsq hy1
  have hage := (hasFDerivAt_age R hna).const_mul ν
  have hχd : HasDerivAt χ (deriv χ (ν * age R y)) (ν * age R y) :=
    ((hχ.smooth.differentiable (by simp)) _).hasDerivAt
  have ha := hχd.comp_hasFDerivAt y hage
  have hc := hG'.comp_hasFDerivAt y (hasFDerivAt_ϱ hna)
  have hcΨ := hc.mul hΨ
  have hX := (ha.smul hZ).add (hcΨ.smul_const (coordinateVector 2))
  refine ⟨_, hX, ?_⟩
  have hℓ : 0 < L⁻¹ := inv_pos.2 hL
  have hpl : (ϱ y)⁻¹ ≤ L⁻¹ := inv_anti₀ hL hy1
  have hM1n : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2n : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hB0 : 0 ≤ ‖Zd‖ + 2 * M1 * L⁻¹ * ‖Z y‖ + 2 * M1 * (L⁻¹) ^ 2 * K +
        (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 * |Ψ y| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun v => ?_
  have hR2 : R ^ 2 = L ^ 2 / ν := eq_div_of_mul_eq hν.ne' (by rw [mul_comm]; exact hLsq)
  -- the three scalar bounds
  have hϱv : |ϱD y v| ≤ ‖v‖ := wgx_ϱD_le hρ0 v
  have hage_b : |deriv χ (ν * age R y) * (ν * ((-(2 * R ^ 2 / ϱ y ^ 3)) * ϱD y v))| ≤
      2 * M1 * L⁻¹ * ‖v‖ := by
    have e : ν * (-(2 * R ^ 2 / ϱ y ^ 3)) = -(2 * (L ^ 2 * ((ϱ y)⁻¹) ^ 3)) := by
      rw [hR2]; field_simp
    have h3 : L ^ 2 * ((ϱ y)⁻¹) ^ 3 ≤ L⁻¹ := by
      calc L ^ 2 * ((ϱ y)⁻¹) ^ 3 ≤ L ^ 2 * (L⁻¹) ^ 3 := by gcongr
        _ = L⁻¹ := by field_simp
    have e2 : deriv χ (ν * age R y) * (ν * ((-(2 * R ^ 2 / ϱ y ^ 3)) * ϱD y v)) =
        deriv χ (ν * age R y) * (ν * (-(2 * R ^ 2 / ϱ y ^ 3))) * ϱD y v := by ring
    rw [e2, e, abs_mul, abs_mul, abs_neg, abs_mul, abs_two,
      abs_of_nonneg (by positivity : 0 ≤ L ^ 2 * ((ϱ y)⁻¹) ^ 3)]
    calc |deriv χ (ν * age R y)| * (2 * (L ^ 2 * ((ϱ y)⁻¹) ^ 3)) * |ϱD y v|
        ≤ M1 * (2 * L⁻¹) * ‖v‖ := by
          gcongr
          · exact hM1 _
        _ = 2 * M1 * L⁻¹ * ‖v‖ := by ring
  have hG_b := wgx_G_bound hM1 hν hL hLsq hy1
  have hcb : |(deriv χ (ν * (R ^ 2 / ϱ y ^ 2)) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y) * Ψd v +
      Ψ y * (G' * ϱD y v)| ≤ 2 * M1 * (L⁻¹) ^ 2 * K * ‖v‖ +
        (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 * |Ψ y| * ‖v‖ := by
    have hΨv : |Ψd v| ≤ K * ‖v‖ := by
      have := Ψd.le_opNorm v
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
    calc _ ≤ |(deriv χ (ν * (R ^ 2 / ϱ y ^ 2)) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y) * Ψd v| +
          |Ψ y * (G' * ϱD y v)| := abs_add_le _ _
      _ = |(deriv χ (ν * (R ^ 2 / ϱ y ^ 2)) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y)| * |Ψd v| +
          |Ψ y| * (|G'| * |ϱD y v|) := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ 2 * M1 * (L⁻¹) ^ 2 * (K * ‖v‖) + |Ψ y| * ((4 * M2 + 8 * M1) * (L⁻¹) ^ 3 * ‖v‖) := by
          gcongr
      _ = _ := by ring
  have hχr := hχ.range (ν * age R y)
  have hχabs : |χ (ν * age R y)| ≤ 1 := by
    rw [abs_of_nonneg hχr.1]; exact hχr.2
  have hec : ‖(coordinateVector 2 : Space)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have hZv : ‖Zd v‖ ≤ ‖Zd‖ * ‖v‖ := Zd.le_opNorm v
  calc ‖χ (ν * age R y) • Zd v +
        (deriv χ (ν * age R y) * (ν * ((-(2 * R ^ 2 / ϱ y ^ 3)) * ϱD y v))) • Z y +
        ((deriv χ (ν * (R ^ 2 / ϱ y ^ 2)) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y) * Ψd v +
          Ψ y * (G' * ϱD y v)) • coordinateVector 2‖
      ≤ ‖χ (ν * age R y) • Zd v‖ +
        ‖(deriv χ (ν * age R y) * (ν * ((-(2 * R ^ 2 / ϱ y ^ 3)) * ϱD y v))) • Z y‖ +
        ‖((deriv χ (ν * (R ^ 2 / ϱ y ^ 2)) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y) * Ψd v +
          Ψ y * (G' * ϱD y v)) • (coordinateVector 2 : Space)‖ := norm_add₃_le
    _ ≤ ‖Zd‖ * ‖v‖ + 2 * M1 * L⁻¹ * ‖v‖ * ‖Z y‖ +
        (2 * M1 * (L⁻¹) ^ 2 * K * ‖v‖ + (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 * |Ψ y| * ‖v‖) := by
        rw [norm_smul, norm_smul, norm_smul, hec, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs]
        have s1 : |χ (ν * age R y)| * ‖Zd v‖ ≤ ‖Zd‖ * ‖v‖ :=
          calc |χ (ν * age R y)| * ‖Zd v‖ ≤ 1 * ‖Zd v‖ := by gcongr
            _ ≤ ‖Zd‖ * ‖v‖ := by rw [one_mul]; exact hZv
        have s2 := mul_le_mul_of_nonneg_right hage_b (norm_nonneg (Z y))
        exact add_le_add (add_le_add s1 s2) hcb
    _ = (‖Zd‖ + 2 * M1 * L⁻¹ * ‖Z y‖ + 2 * M1 * (L⁻¹) ^ 2 * K +
        (4 * M2 + 8 * M1) * (L⁻¹) ^ 3 * |Ψ y|) * ‖v‖ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
