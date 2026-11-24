import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_1

/-!
# Part II-b, task `PartII-b:G4/2/1/2/1/3` (`sqFCalculus`)

Pure calculus for `sqF h u = -(1/8)[u⁻² ∫₀^u v² h + ∫_u^∞ h]`, for `h` integrable on `(0,∞)`,
continuous on `(0,∞)` and bounded on `(0,1]`.  Route: `∫_u^∞ h = ∫_{(0,∞)} h - ∫₀^u h` for `u > 0`,
and both primitives are continuous on `(0,∞)`; near `0`, `|∫₀^u v²h| ≤ C u³` and `|∫₀^u h| ≤ C u`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace UnforcedLeray.Short.IIb

/-- The primitive `u ↦ ∫₀^u f` is continuous on `(0,∞)` when `f` is locally integrable on `(0,R]`. -/
lemma sqPrim_continuousOn {f : ℝ → ℂ} (hf : ∀ R : ℝ, IntegrableOn f (Ioc 0 R)) :
    ContinuousOn (fun u : ℝ => ∫ v in (0 : ℝ)..u, f v) (Ioi 0) := by
  intro u0 hu0
  have hu0' : (0 : ℝ) < u0 := hu0
  have hR : u0 < u0 + 1 := by linarith
  have hint : IntegrableOn f (uIcc 0 (u0 + 1)) := by
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ u0 + 1), integrableOn_Icc_iff_integrableOn_Ioc]
    exact hf _
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
  have hmem : uIcc 0 (u0 + 1) ∈ 𝓝 u0 := by
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ u0 + 1)]
    exact Icc_mem_nhds hu0' hR
  exact (hc.continuousAt hmem).continuousWithinAt

/-- Pointwise bound for the primitive near `0`. -/
lemma sqPrim_norm_le {f : ℝ → ℂ} {C u : ℝ} (hu : 0 < u)
    (hb : ∀ v : ℝ, 0 < v → v ≤ u → ‖f v‖ ≤ C) :
    ‖∫ v in (0 : ℝ)..u, f v‖ ≤ C * u := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u) (C := C) (f := f)
    (by
      intro x hx
      rw [uIoc_of_le hu.le] at hx
      exact hb x hx.1 hx.2)
  rw [sub_zero, abs_of_pos hu] at h
  exact h

/-- The bound `‖v² h v‖ ≤ u² C` for `0 < v ≤ u`. -/
lemma sqSq_norm_le {h : ℝ → ℂ} {C u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) (hb : ‖h v‖ ≤ C) :
    ‖(v : ℂ) ^ 2 * h v‖ ≤ u ^ 2 * C := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv.le]
  have h1 : v ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hv.le hvu 2
  have hC : 0 ≤ C := le_trans (norm_nonneg _) hb
  calc v ^ 2 * ‖h v‖ ≤ u ^ 2 * ‖h v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ u ^ 2 * C := mul_le_mul_of_nonneg_left hb (sq_nonneg u)

/-- **Sub 3** (`sqFCalculus`): the calculus of `sqF`. -/
theorem sqFCalculus : UnforcedLeray.Short.IIb.SqFCalculus := by
  intro h hint hcont hb
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 one_pos le_rfl)
  -- local integrability
  have hloc : ∀ R : ℝ, IntegrableOn h (Ioc 0 R) := fun R =>
    hint.mono_set Ioc_subset_Ioi_self
  have hloc2 : ∀ R : ℝ, IntegrableOn (fun v : ℝ => (v : ℂ) ^ 2 * h v) (Ioc 0 R) := by
    intro R
    refine Integrable.mono' ((hloc R).norm.const_mul (R ^ 2)) ?_ ?_
    · exact (by fun_prop : Continuous fun v : ℝ => (v : ℂ) ^ 2).aestronglyMeasurable.mul
        (hloc R).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      show ‖(v : ℂ) ^ 2 * h v‖ ≤ R ^ 2 * ‖h v‖
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv.1.le]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.1.le hv.2 2) (norm_nonneg _)
  have hP := sqPrim_continuousOn hloc2
  have hI := sqPrim_continuousOn hloc
  -- the tail identity
  have hT : ∀ u : ℝ, 0 < u →
      ∫ v in Ioi u, h v = (∫ v in Ioi (0 : ℝ), h v) - ∫ v in (0 : ℝ)..u, h v := by
    intro u hu
    have hdisj : Disjoint (Ioc (0 : ℝ) u) (Ioi u) :=
      Set.disjoint_left.2 (fun x hx hx' => absurd hx.2 (not_le.2 hx'))
    have hsplit : ∫ v in Ioi (0 : ℝ), h v = (∫ v in Ioc (0 : ℝ) u, h v) + ∫ v in Ioi u, h v := by
      rw [← Ioc_union_Ioi_eq_Ioi hu.le]
      exact setIntegral_union hdisj measurableSet_Ioi (hloc u)
        (hint.mono_set (Ioi_subset_Ioi hu.le))
    rw [hsplit, intervalIntegral.integral_of_le hu.le]
    ring
  -- continuity on (0, ∞)
  have hTc : ContinuousOn (fun u : ℝ => ∫ v in Ioi u, h v) (Ioi 0) :=
    (continuousOn_const.sub hI).congr (fun u hu => hT u hu)
  have hsq : ContinuousOn (fun u : ℝ => ((u : ℂ) ^ 2)⁻¹) (Ioi 0) :=
    ContinuousOn.inv₀ (by fun_prop : Continuous fun u : ℝ => (u : ℂ) ^ 2).continuousOn
      (fun u hu => pow_ne_zero _ (Complex.ofReal_ne_zero.2 (show (0 : ℝ) < u from hu).ne'))
  have hcont' : ContinuousOn (sqF h) (Ioi 0) := by
    unfold sqF
    exact continuousOn_const.mul ((hsq.mul hP).add hTc)
  refine ⟨hcont', ?_⟩
  -- limit at 0⁺
  have hl : Tendsto (fun u : ℝ => C * u) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun u : ℝ => C * u) (𝓝 0) (𝓝 (C * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto (fun u : ℝ => ((u : ℂ) ^ 2)⁻¹ * ∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * h v)
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hP1 : ‖∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * h v‖ ≤ (u ^ 2 * C) * u :=
      sqPrim_norm_le hu0 (fun v hv0 hvu => sqSq_norm_le hv0 hvu
        (hC v hv0 (hvu.trans hu1.le)))
    have hne : u ≠ 0 := hu0.ne'
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc ((u ^ 2)⁻¹) * ‖∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * h v‖
        ≤ (u ^ 2)⁻¹ * ((u ^ 2 * C) * u) :=
          mul_le_mul_of_nonneg_left hP1 (inv_nonneg.2 (sq_nonneg u))
      _ = C * u := by field_simp
  have hlim2 : Tendsto (fun u : ℝ => ∫ v in (0 : ℝ)..u, h v) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
    obtain ⟨hu0, hu1⟩ := hu
    exact sqPrim_norm_le hu0 (fun v hv0 hvu => hC v hv0 (hvu.trans hu1.le))
  have hfun : sqF h =ᶠ[𝓝[>] 0] (fun u : ℝ =>
      -(1 / 8 : ℂ) * (((u : ℂ) ^ 2)⁻¹ * (∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * h v) +
        ((∫ v in Ioi (0 : ℝ), h v) - ∫ v in (0 : ℝ)..u, h v))) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    unfold sqF
    rw [hT u hu]
  refine Tendsto.congr' hfun.symm ?_
  have hlim0 : Tendsto (fun _ : ℝ => ∫ v in Ioi (0 : ℝ), h v) (𝓝[>] 0)
      (𝓝 (∫ v in Ioi (0 : ℝ), h v)) := tendsto_const_nhds
  have hlim := (hlim1.add (hlim0.sub hlim2)).const_mul (-(1 / 8 : ℂ))
  have e : -(1 / 8 : ℂ) * (0 + ((∫ v in Ioi (0 : ℝ), h v) - 0)) =
      -(1 / 8 : ℂ) * ∫ v in Ioi (0 : ℝ), h v := by ring
  rw [e] at hlim
  exact hlim

end UnforcedLeray.Short.IIb
