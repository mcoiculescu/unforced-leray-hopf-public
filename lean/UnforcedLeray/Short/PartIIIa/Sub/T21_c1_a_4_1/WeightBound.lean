import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1

/-!
# `PartIII-a:T21/c1/a/4/1`: the bounded-weight leaf `ExtWeightBound`

Source: `the November 2 reference manuscript`
lines 603-610. On `r ≥ 1` the quotient `h/k` equals the smooth extension `g` of `SeedFunctional`,
which is `O(r⁻²)`. On `0 < r ≤ 1` one has `|k r| ≥ 1` and `|h r| = |seedPlanar h r|` is bounded by
the Gaussian bound on the plane, evaluated at the point `(r, 0)`.
-/

set_option autoImplicit false

open scoped ContDiff

theorem wb_seedPlanar_ofReal (h : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    UnforcedLeray.Short.PartI.seedPlanar h (r : ℂ) = h r := by
  simp [UnforcedLeray.Short.PartI.seedPlanar, UnforcedLeray.Planar.NUE.Ang.ofProfile,
    UnforcedLeray.Planar.NUE.Ang.angPhase, abs_of_pos hr, Complex.norm_real,
    Real.norm_of_nonneg hr.le, div_self (Complex.ofReal_ne_zero.2 hr.ne')]

theorem extWeightBound_proof : UnforcedLeray.Short.IIIa.ExtWeightBound := by
  intro hSF lam h hh ℓ hIS hsm hG
  obtain ⟨C0, hC0⟩ := hG
  have hsmR : ContDiff ℝ ∞ (fun r : ℝ => UnforcedLeray.Short.PartI.seedPlanar h (r : ℂ)) :=
    hsm.comp Complex.ofRealCLM.contDiff
  have hCDO : ContDiffOn ℝ ∞ h (Set.Ioi 0) :=
    hsmR.contDiffOn.congr (fun r hr => (wb_seedPlanar_ofReal h r hr).symm)
  obtain ⟨g, _hgS, hgk, C1, hC1⟩ := ((hSF lam h hh ℓ hIS).2.2.2.2) hCDO
  refine ⟨|C1| + |C0|, fun r hr hk => ?_⟩
  rcases le_total r 1 with hr1 | hr1
  · -- the range `0 < r ≤ 1`
    have hk1 : 1 ≤ |UnforcedLeray.Blueprint.Planar.strainK r| := by
      unfold UnforcedLeray.Blueprint.Planar.strainK
      have hr2 : r ^ 2 ≤ 1 := by nlinarith
      have ha : 7 / 4 ≤ |r ^ 2 / 4 - 2| := by
        rw [abs_of_neg (show r ^ 2 / 4 - 2 < 0 by linarith)]
        linarith
      have he : 3 / 4 ≤ Real.exp (-(r ^ 2) / 4) := by
        have := Real.add_one_le_exp (-(r ^ 2) / 4)
        linarith
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have := mul_le_mul ha he (by norm_num) (abs_nonneg _)
      linarith
    have hb : ‖h r‖ ≤ |C0| := by
      have hr' : (0 : ℝ) < r := hr
      have hbase : ‖h r‖ = ‖UnforcedLeray.Short.PartI.seedPlanar h (r : ℂ)‖ := by
        rw [wb_seedPlanar_ofReal h r hr']
      have h1 := hC0 (r, 0)
      have hp : UnforcedLeray.Short.IIIa.planeToC (r, 0) = (r : ℂ) := by
        apply Complex.ext <;> simp [UnforcedLeray.Short.IIIa.planeToC]
      rw [hp] at h1
      have hE : Real.exp (-(r ^ 2) / 8) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
      have hE0 : 0 < Real.exp (-(r ^ 2) / 8) := Real.exp_pos _
      have h2 : ‖h r‖ ≤ C0 * Real.exp (-(r ^ 2) / 8) := by
        rw [hbase]
        simpa using h1
      calc ‖h r‖ ≤ C0 * Real.exp (-(r ^ 2) / 8) := h2
        _ ≤ |C0| * Real.exp (-(r ^ 2) / 8) :=
          mul_le_mul_of_nonneg_right (le_abs_self C0) hE0.le
        _ ≤ |C0| * 1 := mul_le_mul_of_nonneg_left hE (abs_nonneg C0)
        _ = |C0| := mul_one _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc ‖h r‖ / |UnforcedLeray.Blueprint.Planar.strainK r|
        ≤ ‖h r‖ / 1 := div_le_div_of_nonneg_left (norm_nonneg _) one_pos hk1
      _ = ‖h r‖ := div_one _
      _ ≤ |C0| := hb
      _ ≤ |C1| + |C0| := by linarith [abs_nonneg C1]
  · -- the range `r ≥ 1`
    have hr1' : 1 ≤ r := hr1
    have hge : h r / (UnforcedLeray.Blueprint.Planar.strainK r : ℂ) = g r :=
      (hgk r hr hk).symm
    rw [hge]
    have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
    calc ‖g r‖ ≤ C1 / r ^ 2 := hC1 r hr1'
      _ ≤ |C1 / r ^ 2| := le_abs_self _
      _ = |C1| / r ^ 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2)]
      _ ≤ |C1| := div_le_self (abs_nonneg _) hr2
      _ ≤ |C1| + |C0| := by linarith [abs_nonneg C0]
