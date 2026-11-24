import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1

/-!
# `PartIII-a:T21/c1/a/4/1`: the dominated-convergence leaf `ExtLeftDCT`

Source: `the November 2 reference manuscript`
lines 603-610.  The bound `|lamP y| <= C` (since `(1+|y1|+|y2|)^{-2} <= 1`) and the Gaussian
bound on `f` give an integrable dominating function `|C| |Cf| exp(-|y|^2/8)` for both the
integrand and every cutoff integrand `lamP * (chi(./(n+1)) f)`, since `0 <= chi <= 1`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem extLeftDCT_proof : UnforcedLeray.Short.IIIa.ExtLeftDCT := by
  intro lamP hcont hd f hfc hfG χ hχc hχb hχ1
  obtain ⟨C, hC⟩ := hd
  obtain ⟨Cf, hCf⟩ := hfG
  -- continuity of the plane-to-complex identification
  have hpc : Continuous UnforcedLeray.Short.IIIa.planeToC := by
    unfold UnforcedLeray.Short.IIIa.planeToC
    exact Complex.equivRealProdCLM.symm.continuous
  -- the Gaussian on the plane is integrable
  have hG : Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by
    have h1 : Integrable (fun x : ℝ => Real.exp (-(1 / 8 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num)
    refine (h1.mul_prod h1).congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [← Real.exp_add]
    congr 1
    ring
  -- pointwise bounds
  have hlam : ∀ y : ℝ × ℝ, ‖lamP y‖ ≤ |C| := by
    intro y
    have h0 := hC y
    have ha : 0 ≤ ((1 + |y.1| + |y.2|)⁻¹) ^ 2 := by positivity
    have hb : 1 ≤ 1 + |y.1| + |y.2| := by
      have := abs_nonneg y.1
      have := abs_nonneg y.2
      linarith
    have hinv : (1 + |y.1| + |y.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
    have ha1 : ((1 + |y.1| + |y.2|)⁻¹) ^ 2 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.2 (by positivity)) hinv
    have := mul_le_mul (le_abs_self C) ha1 ha (abs_nonneg C)
    linarith
  have hfb : ∀ y : ℝ × ℝ, ‖f (UnforcedLeray.Short.IIIa.planeToC y)‖ ≤
      |Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := fun y =>
    (hCf y).trans (mul_le_mul_of_nonneg_right (le_abs_self Cf) (Real.exp_nonneg _))
  have hχn : ∀ z : ℂ, ‖((χ z : ℝ) : ℂ)‖ ≤ 1 := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hχb z).1]
    exact (hχb z).2
  -- integrability of the limit integrand
  have hint : Integrable (fun y => lamP y * f (UnforcedLeray.Short.IIIa.planeToC y)) := by
    refine Integrable.mono' (hG.const_mul (|C| * |Cf|)) ?_ (Eventually.of_forall fun y => ?_)
    · exact (hcont.mul (hfc.comp hpc)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖lamP y‖ * ‖f (UnforcedLeray.Short.IIIa.planeToC y)‖
          ≤ |C| * (|Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
            mul_le_mul (hlam y) (hfb y) (norm_nonneg _) (abs_nonneg C)
        _ = |C| * |Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
  refine ⟨hint, ?_⟩
  -- dominated convergence for the cutoff integrands
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun y : ℝ × ℝ => lamP y *
        (((χ (UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) *
          f (UnforcedLeray.Short.IIIa.planeToC y))) volume := by
    intro n
    have hdiv : Continuous (fun y : ℝ × ℝ =>
        UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)) :=
      hpc.div_const _
    have hχd : Continuous (fun y : ℝ × ℝ =>
        ((χ (UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hχc.comp hdiv)
    exact (hcont.mul (hχd.mul (hfc.comp hpc))).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      ‖lamP y *
        (((χ (UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) *
          f (UnforcedLeray.Short.IIIa.planeToC y))‖ ≤
        |C| * |Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro n
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_mul]
    calc ‖lamP y‖ * (‖((χ (UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ)‖ *
          ‖f (UnforcedLeray.Short.IIIa.planeToC y)‖)
        ≤ |C| * (1 * (|Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))) :=
          mul_le_mul (hlam y)
            (mul_le_mul (hχn _) (hfb y) (norm_nonneg _) zero_le_one)
            (by positivity) (abs_nonneg C)
      _ = |C| * |Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring
  have hlim : ∀ y : ℝ × ℝ, Tendsto (fun n : ℕ => lamP y *
        (((χ (UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) *
          f (UnforcedLeray.Short.IIIa.planeToC y)))
      atTop (𝓝 (lamP y * f (UnforcedLeray.Short.IIIa.planeToC y))) := by
    intro y
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖UnforcedLeray.Short.IIIa.planeToC y‖⌉₊] with n hn
    have hnR : ‖UnforcedLeray.Short.IIIa.planeToC y‖ ≤ (n : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖UnforcedLeray.Short.IIIa.planeToC y‖
      have h2 : (⌈‖UnforcedLeray.Short.IIIa.planeToC y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    have hle : ‖UnforcedLeray.Short.IIIa.planeToC y / ((n : ℂ) + 1)‖ ≤ 1 := by
      rw [norm_div, hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        div_le_one (by positivity)]
      exact hnR
    rw [hχ1 _ hle]
    simp
  exact tendsto_integral_of_dominated_convergence
    (fun y : ℝ × ℝ => |C| * |Cf| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))
    hmeas (hG.const_mul (|C| * |Cf|)) hbound (Eventually.of_forall hlim)
