import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_2

/-!


Source: `the November 2 reference manuscript` lines 2347-2352.

Route (no second derivatives, no double integral).  For continuous `H` on `ℝ` and `u > 0`,
let `G u` be the left side and `R u` the right side.  The substitution `w = u t` gives
`∫₀¹ t² H(ut) dt = (u²)⁻¹ u⁻¹ ∫₀ᵘ v² H`, so `G` and `R` have the same derivative on
`(0,∞)`.  Both vanish at `0⁺` (`|∫₀^ε v² H| ≤ C ε³`), hence `G = R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace UnforcedLeray.Short.IIb

/-- Substitution `w = u t` in the inner integral. -/
theorem sqFub_subst (H : ℝ → ℂ) (u : ℝ) (hu : 0 < u) :
    (∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (u*t)) =
      ((u:ℂ)^2)⁻¹ * (u:ℂ)⁻¹ * ∫ v in (0:ℝ)..u, (v:ℂ)^2 * H v := by
  have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hu2 : (u:ℂ)^2 ≠ 0 := pow_ne_zero 2 hu0
  have hc := intervalIntegral.integral_comp_mul_left (f := fun w : ℝ => (w:ℂ)^2 * H w)
    (a := 0) (b := 1) (c := u) hu.ne'
  simp only [mul_zero, mul_one] at hc
  have h2a : (∫ t in (0:ℝ)..1, (u:ℂ)^2 * ((t:ℂ)^2 * H (u*t))) =
      (u:ℂ)^2 * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (u*t) :=
    intervalIntegral.integral_const_mul _ _
  have e : (∫ t in (0:ℝ)..1, ((u:ℂ)^2 * ((t:ℂ)^2 * H (u*t)))) =
      ∫ t in (0:ℝ)..1, (((u*t:ℝ)):ℂ)^2 * H (u*t) := by
    congr 1
    funext t
    push_cast
    ring
  have h2 : (u:ℂ)^2 * (∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (u*t)) =
      (u:ℂ)⁻¹ * ∫ v in (0:ℝ)..u, (v:ℂ)^2 * H v := by
    rw [← h2a, e, hc, Complex.real_smul]
    simp only [Complex.ofReal_inv]
  calc (∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (u*t))
      = ((u:ℂ)^2)⁻¹ * ((u:ℂ)^2 * (∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (u*t))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hu2, one_mul]
    _ = ((u:ℂ)^2)⁻¹ * ((u:ℂ)⁻¹ * ∫ v in (0:ℝ)..u, (v:ℂ)^2 * H v) := by rw [h2]
    _ = ((u:ℂ)^2)⁻¹ * (u:ℂ)⁻¹ * ∫ v in (0:ℝ)..u, (v:ℂ)^2 * H v := by rw [mul_assoc]

/-- Derivative bookkeeping and the derivative identity for continuous `H`. -/
theorem sqFub_hasDeriv (H : ℝ → ℂ) (hH : Continuous H) :
    (∀ x : ℝ, 0 < x → HasDerivAt
      (fun y : ℝ => (∫ v in (0:ℝ)..y, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t)) -
        (1/8:ℂ) * ((∫ v in (0:ℝ)..y, H v) - ((y:ℂ)^2)⁻¹ * ∫ v in (0:ℝ)..y, (v:ℂ)^2 * H v))
      0 x) := by
  have hcont2 : Continuous (Function.uncurry fun (v t : ℝ) => (t:ℂ)^2 * H (v*t)) := by
    have : Continuous fun p : ℝ × ℝ => (p.2:ℂ)^2 * H (p.1 * p.2) :=
      ((Complex.continuous_ofReal.comp continuous_snd).pow 2).mul
        (hH.comp (continuous_fst.mul continuous_snd))
    exact this
  have hG : Continuous fun v : ℝ => ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 0 1
  have hgc : Continuous fun v : ℝ => (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t) :=
    continuous_const.mul hG
  have hPc : Continuous fun v : ℝ => (v:ℂ)^2 * H v :=
    (Complex.continuous_ofReal.pow 2).mul hH
  have hA : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ v in (0:ℝ)..y, H v) (H x) x :=
    fun x => (hH.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ v in (0:ℝ)..y, (v:ℂ)^2 * H v)
      ((x:ℂ)^2 * H x) x :=
    fun x => (hPc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hG' : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ∫ v in (0:ℝ)..y, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t))
      ((1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (x*t)) x :=
    fun x => (hgc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hc2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y:ℂ)^2) (2*(x:ℂ)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 := h0.mul h0
    have hfun : (fun y : ℝ => (y:ℂ)^2) = fun y : ℝ => (y:ℂ) * (y:ℂ) := by
      funext y
      ring
    rw [hfun]
    exact h1.congr_deriv (by ring)
  have hinv : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y : ℝ => ((y:ℂ)^2)⁻¹)
      (-(2*(x:ℂ)) / ((x:ℂ)^2)^2) x := by
    intro x hx
    exact (hc2 x).inv (pow_ne_zero 2 (by exact_mod_cast hx))
  have hR : ∀ x : ℝ, x ≠ 0 → HasDerivAt
      (fun y : ℝ => (1/8:ℂ) * ((∫ v in (0:ℝ)..y, H v) - ((y:ℂ)^2)⁻¹ *
        ∫ v in (0:ℝ)..y, (v:ℂ)^2 * H v))
      ((1/8:ℂ) * (H x - ((-(2*(x:ℂ)) / ((x:ℂ)^2)^2) *
        (∫ v in (0:ℝ)..x, (v:ℂ)^2 * H v) + ((x:ℂ)^2)⁻¹ * ((x:ℂ)^2 * H x)))) x :=
    fun x hx => ((hA x).sub ((hinv x hx).mul (hP x))).const_mul (1/8:ℂ)
  intro x hx
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hRg : HasDerivAt
      (fun y : ℝ => (1/8:ℂ) * ((∫ v in (0:ℝ)..y, H v) - ((y:ℂ)^2)⁻¹ *
        ∫ v in (0:ℝ)..y, (v:ℂ)^2 * H v))
      ((1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (x*t)) x := by
    convert hR x hx.ne' using 1
    rw [sqFub_subst H x hx]
    field_simp
    ring
  have := (hG' x).sub hRg
  rw [sub_self] at this
  exact this

/-- A function with zero derivative on `(0,∞)` and limit `0` at `0⁺` vanishes on `(0,∞)`. -/
theorem sqFub_const (D : ℝ → ℂ) (hD : ∀ x : ℝ, 0 < x → HasDerivAt D 0 x)
    (hlim : Tendsto D (𝓝[>] 0) (𝓝 0)) (u : ℝ) (hu : 0 < u) : D u = 0 := by
  have hconst : ∀ ε : ℝ, 0 < ε → ε ≤ u → D u = D ε := by
    intro ε hε hεu
    have := constant_of_has_deriv_right_zero (f := D) (a := ε) (b := u)
      (fun x hx => (hD x (lt_of_lt_of_le hε hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => (hD x (lt_of_lt_of_le hε hx.1)).hasDerivWithinAt) u ⟨hεu, le_rfl⟩
    exact this
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), D u = D ε := by
    filter_upwards [Ioo_mem_nhdsGT hu] with ε hε
    exact hconst ε hε.1 hε.2.le
  have h1 : Tendsto (fun _ : ℝ => D u) (𝓝[>] 0) (𝓝 (D u)) := tendsto_const_nhds
  have := tendsto_nhds_unique_of_eventuallyEq hlim h1 (hev.mono fun ε hε => hε.symm)
  exact this.symm

/-- Core identity for continuous `H` on `ℝ`. -/
theorem sqFub_core (H : ℝ → ℂ) (hH : Continuous H) (u : ℝ) (hu : 0 < u) :
    (∫ v in (0 : ℝ)..u, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t)) =
      (1 / 8 : ℂ) * ((∫ v in (0 : ℝ)..u, H v) -
        ((u : ℂ) ^ 2)⁻¹ * ∫ v in (0 : ℝ)..u, (v : ℂ) ^ 2 * H v) := by
  have hD := sqFub_hasDeriv H hH
  -- continuity of the primitive `G` and of `A`
  have hG' : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ∫ v in (0:ℝ)..y, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t))
      ((1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (x*t)) x := by
    intro x
    have hcont2 : Continuous (Function.uncurry fun (v t : ℝ) => (t:ℂ)^2 * H (v*t)) := by
      have : Continuous fun p : ℝ × ℝ => (p.2:ℂ)^2 * H (p.1 * p.2) :=
        ((Complex.continuous_ofReal.comp continuous_snd).pow 2).mul
          (hH.comp (continuous_fst.mul continuous_snd))
      exact this
    have hG : Continuous fun v : ℝ => ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 0 1
    exact ((continuous_const.mul hG).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hA : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ v in (0:ℝ)..y, H v) (H x) x :=
    fun x => (hH.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hGc : Continuous (fun y : ℝ => ∫ v in (0:ℝ)..y, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t)) :=
    continuous_iff_continuousAt.2 fun x => (hG' x).continuousAt
  have hAc : Continuous (fun y : ℝ => ∫ v in (0:ℝ)..y, H v) :=
    continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
  -- the remainder tends to `0` at `0⁺`
  have hGlim : Tendsto (fun y : ℝ => ∫ v in (0:ℝ)..y, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * H (v*t))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hGc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hAlim : Tendsto (fun y : ℝ => ∫ v in (0:ℝ)..y, H v) (𝓝[>] 0) (𝓝 0) := by
    have := (hAc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  obtain ⟨C, hC0⟩ := (isCompact_Icc.image (continuous_norm.comp hH)).bddAbove
  have hC : ∀ x ∈ Icc (0:ℝ) 1, ‖H x‖ ≤ C := fun x hx => hC0 ⟨x, hx, rfl⟩
  have hbd : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖((ε:ℂ)^2)⁻¹ * ∫ v in (0:ℝ)..ε, (v:ℂ)^2 * H v‖ ≤ C * ε := by
    intro ε hε hε1
    have hint : ‖∫ v in (0:ℝ)..ε, (v:ℂ)^2 * H v‖ ≤ (ε^2 * C) * |ε - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v hv
      rw [Set.uIoc_of_le hε.le] at hv
      have hv1 : ‖(v:ℂ)^2‖ ≤ ε^2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv.1]
        exact pow_le_pow_left₀ hv.1.le hv.2 2
      calc ‖(v:ℂ)^2 * H v‖ = ‖(v:ℂ)^2‖ * ‖H v‖ := norm_mul _ _
        _ ≤ ε^2 * C := mul_le_mul hv1 (hC v ⟨hv.1.le, by linarith [hv.2]⟩) (norm_nonneg _)
            (by positivity)
    have hn : ‖((ε:ℂ)^2)⁻¹‖ = (ε^2)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    rw [norm_mul, hn]
    calc (ε^2)⁻¹ * ‖∫ v in (0:ℝ)..ε, (v:ℂ)^2 * H v‖
        ≤ (ε^2)⁻¹ * ((ε^2 * C) * |ε - 0|) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = C * ε := by
        rw [sub_zero, abs_of_pos hε]
        field_simp
  have hPlim : Tendsto (fun y : ℝ => ((y:ℂ)^2)⁻¹ * ∫ v in (0:ℝ)..y, (v:ℂ)^2 * H v)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun y : ℝ => C * y)
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with y hy
      exact hbd y hy.1 hy.2.le
    · have hlin : Continuous fun y : ℝ => C * y := continuous_const.mul continuous_id
      have := (hlin.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
  have hRlim : Tendsto (fun y : ℝ => (1/8:ℂ) * ((∫ v in (0:ℝ)..y, H v) -
      ((y:ℂ)^2)⁻¹ * ∫ v in (0:ℝ)..y, (v:ℂ)^2 * H v)) (𝓝[>] 0) (𝓝 0) := by
    have := (hAlim.sub hPlim).const_mul (1/8:ℂ)
    simpa using this
  have hlim := hGlim.sub hRlim
  have key := sqFub_const _ hD (by simpa using hlim) u hu
  exact sub_eq_zero.1 key

theorem sqFubini : UnforcedLeray.Short.IIb.SqFubini := by
  intro h hcont u hu
  have hH : Continuous (fun w : ℝ => h (max w 0)) :=
    hcont.comp_continuous (continuous_id.max continuous_const)
      (fun w => Set.mem_Ici.mpr (le_max_right w 0))
  have hL : (∫ v in (0:ℝ)..u, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * h (v*t)) =
      ∫ v in (0:ℝ)..u, (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * h (max (v*t) 0) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hu.le] at hv
    show (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * h (v*t) =
      (1/4:ℂ) * ∫ t in (0:ℝ)..1, (t:ℂ)^2 * h (max (v*t) 0)
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    show (t:ℂ)^2 * h (v*t) = (t:ℂ)^2 * h (max (v*t) 0)
    rw [max_eq_left (mul_nonneg hv.1 ht.1)]
  have hR1 : (∫ v in (0:ℝ)..u, h v) = ∫ v in (0:ℝ)..u, h (max v 0) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hu.le] at hv
    show h v = h (max v 0)
    rw [max_eq_left hv.1]
  have hR2 : (∫ v in (0:ℝ)..u, (v:ℂ)^2 * h v) = ∫ v in (0:ℝ)..u, (v:ℂ)^2 * h (max v 0) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hu.le] at hv
    show (v:ℂ)^2 * h v = (v:ℂ)^2 * h (max v 0)
    rw [max_eq_left hv.1]
  rw [hL, hR1, hR2]
  exact sqFub_core (fun w => h (max w 0)) hH u hu

end UnforcedLeray.Short.IIb
