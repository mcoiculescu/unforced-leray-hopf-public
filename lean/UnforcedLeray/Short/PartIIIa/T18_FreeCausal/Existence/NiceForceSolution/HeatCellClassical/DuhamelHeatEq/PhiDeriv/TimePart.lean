import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.PhiDeriv.SpacePart

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/3` (time part): `(r'-r)⁻¹ ∫ G_{νr'} (h(s-r') - h(s-r)) → -A(r)`

Target: `duhEqTimePart : DuhEqTimePart`. Source: `the November 2 reference manuscript`,
lines 3427-3440. Taylor in the source time with a uniform second-derivative bound, unit mass of
`G_{νr'}`, and continuity of `θ ↦ ∫ G_θ ∂_t h(s-r, ·)` (from `sp_theta_complex`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The time derivative of a nice source as a nice source. -/
abbrev spD (h : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  duhDir ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) h

theorem sp_deriv_t {h : ℝ × (ℝ × ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) (t : ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun t' : ℝ => h (t', y)) (spD h (t, y)) t := by
  have h1 : HasDerivAt (fun t' : ℝ => ((t', y) : ℝ × (ℝ × ℝ))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  exact ((hh.differentiable (by simp)) (t, y)).hasFDerivAt.comp_hasDerivAt t h1

/-- Taylor bound in the time variable with a uniform bound on the second time derivative. -/
theorem sp_taylor (h D : ℝ × (ℝ × ℝ) → ℂ)
    (hderiv : ∀ (t : ℝ) (y : ℝ × ℝ), HasDerivAt (fun t' : ℝ => h (t', y)) (D (t, y)) t)
    (hDC : ContDiff ℝ ∞ D) {K : ℝ} (hDK : ∀ q, ‖iteratedFDeriv ℝ 1 D q‖ ≤ K)
    (a δ : ℝ) (y : ℝ × ℝ) :
    ‖h (a + δ, y) - h (a, y) - (δ : ℂ) * D (a, y)‖ ≤ K * δ ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hDK 0)
  have hbd : ∀ τ : ℝ, ‖D (a + τ, y) - D (a, y)‖ ≤ K * |τ| := by
    intro τ
    have hb := duhAI_time_lip hDC hDK a (-τ) y
    rw [sub_neg_eq_add, abs_neg] at hb
    exact hb
  have hgd : ∀ τ : ℝ, HasDerivAt (fun τ' : ℝ => h (a + τ', y) - h (a, y) - (τ' : ℂ) * D (a, y))
      (D (a + τ, y) - D (a, y)) τ := by
    intro τ
    have hlin : HasDerivAt (fun τ' : ℝ => a + τ') 1 τ := (hasDerivAt_id τ).const_add a
    have h2 : HasDerivAt (fun τ' : ℝ => h (a + τ', y)) (D (a + τ, y)) τ := by
      have := (hderiv (a + τ) y).scomp τ hlin
      rw [one_smul] at this
      exact this
    have h3 : HasDerivAt (fun τ' : ℝ => (τ' : ℂ) * D (a, y)) (D (a, y)) τ := by
      simpa using ((hasDerivAt_id τ).ofReal_comp).mul_const (D (a, y))
    exact (h2.sub_const (h (a, y))).sub h3
  have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun τ' : ℝ => h (a + τ', y) - h (a, y) - (τ' : ℂ) * D (a, y))
    (s := Icc (-|δ|) |δ|) (C := K * |δ|) (fun τ _ => (hgd τ).differentiableAt)
    (fun τ hτ => by
      rw [(hgd τ).deriv]
      have hτ' : |τ| ≤ |δ| := abs_le.mpr ⟨hτ.1, hτ.2⟩
      exact (hbd τ).trans (mul_le_mul_of_nonneg_left hτ' hK0))
    (convex_Icc _ _)
    (⟨by linarith [abs_nonneg δ], abs_nonneg δ⟩ : (0 : ℝ) ∈ Icc (-|δ|) |δ|)
    (⟨neg_abs_le δ, le_abs_self δ⟩ : δ ∈ Icc (-|δ|) |δ|)
  have hsq : |δ| * |δ| = δ ^ 2 := by rw [abs_mul_abs_self, sq]
  calc ‖h (a + δ, y) - h (a, y) - (δ : ℂ) * D (a, y)‖
      = ‖(h (a + δ, y) - h (a, y) - (δ : ℂ) * D (a, y)) -
          (h (a + 0, y) - h (a, y) - ((0 : ℝ) : ℂ) * D (a, y))‖ := by simp
    _ ≤ K * |δ| * ‖δ - 0‖ := hMVT
    _ = K * δ ^ 2 := by rw [sub_zero, Real.norm_eq_abs, ← hsq]; ring


/-- **Time part** (SP 3427-3440): the difference quotient in the source time with the kernel at
`νr'` tends to `-A(r)`. -/
theorem duhEqTimePart : UnforcedLeray.Short.IIIa.DuhEqTimePart := by
  intro c ν h hc hν hn s x r hr
  have hDn : NiceScalar c (spD h) := duhDir_nice hn _
  obtain ⟨Kd, hKd⟩ := duhFd_norm_fderiv_bdd hc hDn
  have hDK : ∀ q, ‖iteratedFDeriv ℝ 1 (spD h) q‖ ≤ Kd := fun q => by
    simpa [norm_iteratedFDeriv_one] using hKd q
  obtain ⟨MD, hMD⟩ := duhFd_bdd hc hDn
  obtain ⟨Mh, hMh⟩ := duhFd_bdd hc hn
  have hderiv : ∀ (t : ℝ) (y : ℝ × ℝ), HasDerivAt (fun t' : ℝ => h (t', y)) (spD h (t, y)) t :=
    fun t y => sp_deriv_t hn.1 t y
  have hψc : Continuous (fun y : ℝ × ℝ => spD h (s - r, y)) := hDn.1.continuous.comp (by fun_prop)
  have hψM : ∀ y : ℝ × ℝ, ‖spD h (s - r, y)‖ ≤ MD := fun y => hMD _
  have hθ0 : 0 < ν * r := mul_pos hν hr
  set Θ : ℝ → ℂ := fun θ => ∫ w : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 θ w : ℝ) : ℂ) *
      spD h (s - r, (x.1 - w.1, x.2 - w.2)) with hΘdef
  have hΘc : ContinuousAt Θ (ν * r) := (sp_theta_complex hψc hψM hθ0 x).continuousAt
  have hA : duhDt ν h s x r = Θ (ν * r) := by
    unfold duhDt
    simp only [hΘdef]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [(hderiv (s - r) (x.1 - z.1, x.2 - z.2)).deriv]
  have hΘlim : Tendsto (fun r' : ℝ => Θ (ν * r')) (𝓝[≠] r) (𝓝 (Θ (ν * r))) := by
    have hu : Tendsto (fun r' : ℝ => ν * r') (𝓝 r) (𝓝 (ν * r)) :=
      (continuous_const.mul continuous_id).tendsto r
    exact (hΘc.tendsto.comp hu).mono_left nhdsWithin_le_nhds
  set F : ℝ → ℂ := fun r' => (((r' - r)⁻¹ : ℝ) : ℂ) * ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
        (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))) with hFdef
  have hkey : ∀ r' : ℝ, 0 < r' → r' ≠ r → ‖F r' + Θ (ν * r')‖ ≤ Kd * |r' - r| := by
    intro r' hr' hne
    have hθ' : 0 < ν * r' := mul_pos hν hr'
    have hsub : r' - r ≠ 0 := sub_ne_zero.mpr hne
    have hQ : ∀ z : ℝ × ℝ,
        ‖(((r' - r)⁻¹ : ℝ) : ℂ) * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))
          + spD h (s - r, (x.1 - z.1, x.2 - z.2))‖ ≤ Kd * |r' - r| := by
      intro z
      have hT := sp_taylor h (spD h) hderiv hDn.1 hDK (s - r) (r - r') (x.1 - z.1, x.2 - z.2)
      rw [show s - r + (r - r') = s - r' by ring] at hT
      have hu : (((r' - r)⁻¹ : ℝ) : ℂ) * ((r' - r : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hsub, Complex.ofReal_one]
      have hid : (((r' - r)⁻¹ : ℝ) : ℂ) * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))
          + spD h (s - r, (x.1 - z.1, x.2 - z.2)) =
          (((r' - r)⁻¹ : ℝ) : ℂ) * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))
            - ((r - r' : ℝ) : ℂ) * spD h (s - r, (x.1 - z.1, x.2 - z.2))) := by
        have hu' := hu
        push_cast at hu' ⊢
        linear_combination (-(spD h (s - r, (x.1 - z.1, x.2 - z.2)))) * hu'
      rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
      have hab : 0 < |r' - r| := abs_pos.mpr hsub
      calc |r' - r|⁻¹ * ‖h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))
            - ((r - r' : ℝ) : ℂ) * spD h (s - r, (x.1 - z.1, x.2 - z.2))‖
          ≤ |r' - r|⁻¹ * (Kd * (r - r') ^ 2) := mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hab.le)
        _ = Kd * |r' - r| := by
          rw [show (r - r') ^ 2 = |r' - r| ^ 2 by rw [sq_abs]; ring]
          field_simp
    have hcont1 : Continuous (fun z : ℝ × ℝ => h (s - r', (x.1 - z.1, x.2 - z.2))
        - h (s - r, (x.1 - z.1, x.2 - z.2))) :=
      (hn.1.continuous.comp (by fun_prop)).sub (hn.1.continuous.comp (by fun_prop))
    have hint1 : Integrable (fun z : ℝ × ℝ =>
        ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))) :=
      duhAI_intC (UnforcedLeray.B0284.integrable_heatKernel2 hθ') hcont1 (M := Mh + Mh)
        (fun z => (norm_sub_le _ _).trans (add_le_add (hMh _) (hMh _)))
    have hcont2 : Continuous (fun z : ℝ × ℝ => spD h (s - r, (x.1 - z.1, x.2 - z.2))) :=
      hψc.comp (by fun_prop)
    have hint2 : Integrable (fun z : ℝ × ℝ =>
        ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          spD h (s - r, (x.1 - z.1, x.2 - z.2))) :=
      duhAI_intC (UnforcedLeray.B0284.integrable_heatKernel2 hθ') hcont2 (M := MD)
        (fun z => hψM _)
    set c' : ℂ := (((r' - r)⁻¹ : ℝ) : ℂ) with hc'
    have hc1 : ∫ z : ℝ × ℝ, c' * (((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))) =
        c' * ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))) := by
      rw [← integral_const_mul]
    have hid2 : c' * (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))) + Θ (ν * r') =
        ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (c' * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))
            + spD h (s - r, (x.1 - z.1, x.2 - z.2))) := by
      have hsplit : (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (c' * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))
            + spD h (s - r, (x.1 - z.1, x.2 - z.2)))) =
          ∫ z : ℝ × ℝ, (c' * (((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
            (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))))
            + ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
              spD h (s - r, (x.1 - z.1, x.2 - z.2))) := by
        congr 1
        funext z
        ring
      rw [hsplit, integral_add (hint1.const_mul c') hint2, hc1]
    simp only [hFdef]
    rw [show c' * (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))) + Θ (ν * r') =
        ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (c' * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2)))
            + spD h (s - r, (x.1 - z.1, x.2 - z.2))) from hid2]
    calc ‖∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r') z : ℝ) : ℂ) *
          (c' * (h (s - r', (x.1 - z.1, x.2 - z.2)) - h (s - r, (x.1 - z.1, x.2 - z.2))) +
            spD h (s - r, (x.1 - z.1, x.2 - z.2)))‖
        ≤ ∫ z : ℝ × ℝ, (Kd * |r' - r|) * UnforcedLeray.B0284.heatKernel2 (ν * r') z := by
          apply norm_integral_le_of_norm_le ((UnforcedLeray.B0284.integrable_heatKernel2 hθ').const_mul _)
          refine Eventually.of_forall fun z => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ' z), mul_comm (Kd * |r' - r|)]
          exact mul_le_mul_of_nonneg_left (hQ z) (UnforcedLeray.B0284.heatKernel2_nonneg hθ' z)
      _ = Kd * |r' - r| := by
          rw [integral_const_mul, UnforcedLeray.B0284.integral_heatKernel2 hθ', mul_one]
  have hpos : ∀ᶠ r' in 𝓝[≠] r, 0 < r' := nhdsWithin_le_nhds (Ioi_mem_nhds hr)
  have hne : ∀ᶠ r' in 𝓝[≠] r, r' ≠ r := eventually_mem_nhdsWithin
  have hR : Tendsto (fun r' => F r' + Θ (ν * r')) (𝓝[≠] r) (𝓝 0) := by
    have ha : Tendsto (fun r' : ℝ => Kd * |r' - r|) (𝓝[≠] r) (𝓝 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      have hc0 : Tendsto (fun r' : ℝ => Kd * |r' - r|) (𝓝 r) (𝓝 (Kd * |r - r|)) :=
        (by fun_prop : Continuous fun r' : ℝ => Kd * |r' - r|).tendsto r
      simpa using hc0
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [hpos, hne] with r' hr' hne'
    exact hkey r' hr' hne'
  have hfin := hR.sub hΘlim
  have hfinal : Tendsto F (𝓝[≠] r) (𝓝 (0 - Θ (ν * r))) :=
    hfin.congr (fun r' => add_sub_cancel_right _ _)
  rw [zero_sub] at hfinal
  rw [hA]
  exact hfinal

end UnforcedLeray.Short.IIIa
