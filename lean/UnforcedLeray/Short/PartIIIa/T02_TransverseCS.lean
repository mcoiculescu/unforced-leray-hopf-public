import UnforcedLeray.Short.PartIIIa.Targets

/-!
# Part III-a, task `PartIII-a:T02`: the transverse Cauchy-Schwarz bound

Source of record: `the November 2 reference manuscript`. The weight
`W = <eta/sqrt(1+s)>^{m_Z}` is defined on lines 2693-2695. The transverse Cauchy-Schwarz display
(`int (1+|eta|/sqrt s) ||T(s,.,eta)||_{L^2_q} d eta <= C s^{1/4} ||W T(s)||`, with the reason
`int <x>^{2-2m_Z} dx < infinity`) is on lines 2787-2792.

Target: `transverseCS : TransverseCS` (the statement lives in `Targets.lean`, not changed here).

Proof. Fix `m = m_Z > 3/2` and `s >= 1`. Write `a = sqrt(1+s)`, `B(eta) = 1 + (eta/a)^2`,
`X(eta) = 1 + |eta|/sqrt s`, `Y = B^{-m/2}`, `Z = B^{m/2}`. Then `X * G = (X Y) * (Z G)` since
`Y Z = 1`, and Cauchy-Schwarz with exponents `2, 2` applies. Pointwise `(X Y)^2 <= 8 B^{-(m-1)}`,
because `X <= 1 + 2|eta/a|` and `(1+2y)^2 <= 8 (1+y^2)`. The integral of `8 B^{-(m-1)}` is
`sqrt(1+s)` times the finite constant `int 8 (1+y^2)^{-(m-1)} dy` (finite since `2(m-1) > 1`).
The constant of the statement is `C = 1 + M`, where `M` is that finite constant, and the bound
`sqrt(1+s) M <= ((1+M) s^{1/4})^2` uses `sqrt(1+s) <= 2 s^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Scaling of the Lebesgue integral on `ℝ`: `∫ F(c x) dx = |c⁻¹| ∫ F` for `c ≠ 0`. -/
lemma lintegral_comp_smul_real {c : ℝ} (hc : c ≠ 0) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : ℝ, F (c • x) = ENNReal.ofReal |c⁻¹| * ∫⁻ y : ℝ, F y := by
  have hmeas : Measurable (fun x : ℝ => c • x) := measurable_const_smul c
  calc ∫⁻ x : ℝ, F (c • x)
      = ∫⁻ y : ℝ, F y ∂(Measure.map (fun x : ℝ => c • x) (volume : Measure ℝ)) :=
        (lintegral_map hF hmeas).symm
    _ = ∫⁻ y : ℝ, F y ∂(ENNReal.ofReal |(c ^ Module.finrank ℝ ℝ)⁻¹| • (volume : Measure ℝ)) := by
        rw [Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hc]
    _ = ENNReal.ofReal |c⁻¹| * ∫⁻ y : ℝ, F y := by
        rw [lintegral_smul_measure, smul_eq_mul, Module.finrank_self, pow_one]

/-- The majorant `8 (1+y^2)^{-(m-1)}` has finite lintegral when `m > 3/2`. -/
lemma majorant_lintegral_lt_top {m : ℝ} (hm : 3 / 2 < m) :
    ∫⁻ y : ℝ, ENNReal.ofReal (8 * (1 + y ^ 2) ^ (-(m - 1))) < ∞ := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * (m - 1) := by
    rw [Module.finrank_self]
    push_cast
    linarith
  have hfun : (fun y : ℝ => 8 * (1 + y ^ 2) ^ (-(m - 1)))
      = fun y : ℝ => 8 * (1 + ‖y‖ ^ 2) ^ (-(2 * (m - 1)) / 2) := by
    funext y
    rw [Real.norm_eq_abs, sq_abs, show -(2 * (m - 1)) / 2 = -(m - 1) by ring]
  have hI : Integrable (fun y : ℝ => 8 * (1 + y ^ 2) ^ (-(m - 1))) := by
    rw [hfun]
    exact (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) hr).const_mul 8
  exact hI.lintegral_lt_top

/-- Pointwise bound for the first Cauchy-Schwarz factor:
`(X B^{-m/2})^2 <= 8 B^{-(m-1)}` with `X = 1 + |eta|/sqrt s`, `B = 1 + (eta/sqrt(1+s))^2`. -/
lemma first_factor_sq_le (m s η : ℝ) (hs : 1 ≤ s) :
    ((1 + |η| / Real.sqrt s) * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(m / 2))) ^ (2 : ℝ)
      ≤ 8 * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(m - 1)) := by
  have hs0 : 0 < s := by linarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have ha : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 (by linarith)
  have ha2 : Real.sqrt (1 + s) ≤ 2 * Real.sqrt s := by
    rw [Real.sqrt_le_left (by positivity)]
    have h2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
    nlinarith [h2]
  have hB0 : (0 : ℝ) < 1 + (η / Real.sqrt (1 + s)) ^ 2 := by positivity
  have hX0 : (0 : ℝ) ≤ 1 + |η| / Real.sqrt s := by positivity
  have hY0 : (0 : ℝ) ≤ (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(m / 2)) := by positivity
  have hXle : 1 + |η| / Real.sqrt s ≤ 1 + 2 * (|η| / Real.sqrt (1 + s)) := by
    have h1 : |η| / Real.sqrt s ≤ 2 * (|η| / Real.sqrt (1 + s)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hsq ha]
      nlinarith [mul_le_mul_of_nonneg_left ha2 (abs_nonneg η)]
    linarith
  have hsq2 : (η / Real.sqrt (1 + s)) ^ 2 = (|η| / Real.sqrt (1 + s)) ^ 2 := by
    rw [← sq_abs (η / Real.sqrt (1 + s)), abs_div, abs_of_pos ha]
  have hX2 : (1 + |η| / Real.sqrt s) ^ 2 ≤ 8 * (1 + (η / Real.sqrt (1 + s)) ^ 2) := by
    rw [hsq2]
    have hy0 : 0 ≤ |η| / Real.sqrt (1 + s) := by positivity
    have h := pow_le_pow_left₀ hX0 hXle 2
    nlinarith [sq_nonneg (|η| / Real.sqrt (1 + s) - 1 / 2)]
  have hBm : (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(m - 1))
      = (1 + (η / Real.sqrt (1 + s)) ^ 2) * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-m) := by
    rw [show -(m - 1) = 1 + -m by ring, Real.rpow_add hB0, Real.rpow_one]
  have hYm : (0 : ℝ) ≤ (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-m) := by positivity
  rw [Real.mul_rpow hX0 hY0, ← Real.rpow_mul hB0.le, show -(m / 2) * 2 = -m by ring,
    Real.rpow_two, hBm]
  nlinarith [mul_le_mul_of_nonneg_right hX2 hYm]

/-- The transverse Cauchy-Schwarz bound (`PartIII-a:T02`). -/
theorem transverseCS : TransverseCS := by
  unfold TransverseCS
  intro mZ hmZ
  have hfin := majorant_lintegral_lt_top hmZ
  obtain ⟨M, hM0, hMdef⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∫⁻ y : ℝ, ENNReal.ofReal (8 * (1 + y ^ 2) ^ (-(mZ - 1))) = ENNReal.ofReal M :=
    ⟨(∫⁻ y : ℝ, ENNReal.ofReal (8 * (1 + y ^ 2) ^ (-(mZ - 1)))).toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal hfin.ne).symm⟩
  refine ⟨1 + M, by linarith, ?_⟩
  intro s hs G hG
  have hs0 : 0 < s := by linarith
  have ha : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 (by linarith)
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  obtain ⟨f, hf_def⟩ : ∃ f : ℝ → ℝ≥0∞, ∀ η : ℝ, f η = ENNReal.ofReal
      ((1 + |η| / Real.sqrt s) * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2))) :=
    ⟨fun η => ENNReal.ofReal
      ((1 + |η| / Real.sqrt s) * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2))), fun η => rfl⟩
  obtain ⟨g, hg_def⟩ : ∃ g : ℝ → ℝ≥0∞, ∀ η : ℝ, g η = ENNReal.ofReal
      ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2)) * G η :=
    ⟨fun η => ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2)) * G η,
      fun η => rfl⟩
  have hfm : Measurable f := by
    have hfeq : f = fun η : ℝ => ENNReal.ofReal
        ((1 + |η| / Real.sqrt s) * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2))) :=
      funext hf_def
    rw [hfeq]
    fun_prop
  have hgm : Measurable g := by
    have hgeq : g = fun η : ℝ =>
        ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2)) * G η :=
      funext hg_def
    rw [hgeq]
    fun_prop
  -- pointwise factorisation: `X * G = (X Y) * (Z G)` with `Y Z = 1`
  have hpt : ∀ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) * G η = f η * g η := by
    intro η
    rw [hf_def, hg_def]
    have hB0 : (0 : ℝ) < 1 + (η / Real.sqrt (1 + s)) ^ 2 := by positivity
    have hX0 : (0 : ℝ) ≤ 1 + |η| / Real.sqrt s := by positivity
    have hY0 : (0 : ℝ) ≤ (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2)) := by positivity
    have hZ0 : (0 : ℝ) ≤ (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2) := by positivity
    have hYZ : (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2))
        * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2) = 1 := by
      rw [← Real.rpow_add hB0, neg_add_cancel, Real.rpow_zero]
    have hYZ' : ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2)))
        * ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul hY0, hYZ, ENNReal.ofReal_one]
    rw [ENNReal.ofReal_mul hX0]
    have key : ENNReal.ofReal (1 + |η| / Real.sqrt s)
        * ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2)))
        * (ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2)) * G η)
        = ENNReal.ofReal (1 + |η| / Real.sqrt s)
          * (ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2)))
            * ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2))) * G η := by
      ring
    rw [key, hYZ', mul_one]
  have hLHS : ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) * G η
      = ∫⁻ η : ℝ, (f * g) η :=
    lintegral_congr fun η => by rw [Pi.mul_apply]; exact hpt η
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
    Real.HolderConjugate.two_two hfm.aemeasurable hgm.aemeasurable
  -- the second factor is the statement's weighted integral
  have hg2 : ∫⁻ η : ℝ, g η ^ (2 : ℝ)
      = ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) * G η ^ (2 : ℝ) := by
    refine lintegral_congr fun η => ?_
    have hB0 : (0 : ℝ) < 1 + (η / Real.sqrt (1 + s)) ^ 2 := by positivity
    have hBp : (0 : ℝ) ≤ (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (mZ / 2) := by positivity
    rw [hg_def, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hBp (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hB0.le,
      show mZ / 2 * 2 = mZ by ring]
  -- the scaled majorant: `∫ 8 B^{-(m-1)} dη = sqrt(1+s) ∫ 8 (1+y^2)^{-(m-1)} dy`
  have hscale : ∫⁻ η : ℝ, ENNReal.ofReal (8 * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ - 1)))
      = ENNReal.ofReal (Real.sqrt (1 + s))
        * ∫⁻ y : ℝ, ENNReal.ofReal (8 * (1 + y ^ 2) ^ (-(mZ - 1))) := by
    have h := lintegral_comp_smul_real (c := (Real.sqrt (1 + s))⁻¹) (inv_ne_zero ha.ne')
      (fun y : ℝ => ENNReal.ofReal (8 * (1 + y ^ 2) ^ (-(mZ - 1)))) (by fun_prop)
    simp only [smul_eq_mul, inv_inv, abs_of_pos ha, div_eq_inv_mul] at h ⊢
    exact h
  -- the first factor is bounded in `L^2` by `(C s^{1/4})`
  have hroot : (∫⁻ η : ℝ, f η ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ((1 + M) * s ^ (1 / 4 : ℝ)) := by
    have hp0 : (0 : ℝ) ≤ (1 + M) * s ^ (1 / 4 : ℝ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
    have ht4 : (s ^ (1 / 4 : ℝ)) ^ 4 = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ s)]
      norm_num
    have ha_le : Real.sqrt (1 + s) ≤ 2 * (s ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [ht4]
    have key : Real.sqrt (1 + s) * M ≤ ((1 + M) * s ^ (1 / 4 : ℝ)) ^ 2 := by
      have h1 : Real.sqrt (1 + s) * M ≤ 2 * (s ^ (1 / 4 : ℝ)) ^ 2 * M :=
        mul_le_mul_of_nonneg_right ha_le hM0
      have h2 : (0 : ℝ) ≤ (s ^ (1 / 4 : ℝ)) ^ 2 + M ^ 2 * (s ^ (1 / 4 : ℝ)) ^ 2 := by
        positivity
      nlinarith [h1, h2]
    have hsq_le : ∫⁻ η : ℝ, f η ^ (2 : ℝ) ≤ ENNReal.ofReal ((1 + M) * s ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [← ENNReal.ofReal_pow hp0]
      calc ∫⁻ η : ℝ, f η ^ (2 : ℝ)
          ≤ ∫⁻ η : ℝ, ENNReal.ofReal (8 * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ - 1))) := by
            refine lintegral_mono fun η => ?_
            have hXY0 : (0 : ℝ) ≤ (1 + |η| / Real.sqrt s)
                * (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ (-(mZ / 2)) := by positivity
            rw [hf_def, ENNReal.ofReal_rpow_of_nonneg hXY0 (by norm_num : (0 : ℝ) ≤ 2)]
            exact ENNReal.ofReal_le_ofReal (first_factor_sq_le mZ s η hs)
        _ = ENNReal.ofReal (Real.sqrt (1 + s))
              * ∫⁻ y : ℝ, ENNReal.ofReal (8 * (1 + y ^ 2) ^ (-(mZ - 1))) := hscale
        _ = ENNReal.ofReal (Real.sqrt (1 + s)) * ENNReal.ofReal M := by rw [hMdef]
        _ = ENNReal.ofReal (Real.sqrt (1 + s) * M) := (ENNReal.ofReal_mul ha.le).symm
        _ ≤ ENNReal.ofReal (((1 + M) * s ^ (1 / 4 : ℝ)) ^ 2) := ENNReal.ofReal_le_ofReal key
    calc (∫⁻ η : ℝ, f η ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ((1 + M) * s ^ (1 / 4 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hsq_le (by norm_num)
      _ = ENNReal.ofReal ((1 + M) * s ^ (1 / 4 : ℝ)) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
  rw [hLHS]
  calc ∫⁻ η : ℝ, (f * g) η
      ≤ (∫⁻ η : ℝ, f η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫⁻ η : ℝ, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hCS
    _ ≤ ENNReal.ofReal ((1 + M) * s ^ (1 / 4 : ℝ))
          * (∫⁻ η : ℝ, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by gcongr
    _ = ENNReal.ofReal ((1 + M) * s ^ (1 / 4 : ℝ))
          * (∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) * G η ^ (2 : ℝ))
            ^ (1 / 2 : ℝ) := by rw [hg2]

end UnforcedLeray.Short.IIIa
