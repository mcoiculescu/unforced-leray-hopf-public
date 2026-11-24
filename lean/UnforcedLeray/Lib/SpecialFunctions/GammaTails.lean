import UnforcedLeray.Lib.SpecialFunctions.EulerGamma
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real Gamma-type integrals and tails (INF20 T20.7)

Blueprint target INF20 T20.7 of the scoping note `INF19-INF20-INF29-INF30-Algebra.md`
(§5 Level 3). Uses:

* tex 2348–2353 (`eq:st18-t00152`, B0154): `∫ u^k e^{-bu}` after the substitution `u = c²/a`;
* tex 2722–2735 (`eq:st18-t00175`, B0179): a polynomial weight `(1+s)^L` against `e^{-κs}`
  integrates to a quantity polynomial in `1/κ`;
* tex 6406–6428 (`eq:st18-t00347`, B0339): `∫_0^∞ (1 + e_c u/θ)^M e^{-(b₁ - A e_c)u} du ≤
  ∫_0^∞ (1+u)^M e^{-b₁u/2} du` when `e_c ≤ θ` and `A e_c ≤ b₁/2`, independently of the running
  parameters;
* tex 6754–6771 (`eq:st18-t00366`, B0362): `∫_θ^b r^{C}e^{-b₃r/e_c} dr ≤ C' e_c^{C+1}`;
* tex 12875–12887 (`eq:affine-4-112`, B0863): `∫_0^∞ s^{σ+3/2} e^{-bs} ds < ∞`.

Every integrand below is shown integrable on its domain, so no Bochner junk value enters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real

namespace UnforcedLeray.Special

/-- **Euler integral with real rate** (INF20 T20.7; tex 12875–12887, B0863; tex 6754–6771,
B0362): `∫_0^∞ t^a e^{-bt} dt = Γ(a+1) (1/b)^{a+1}` for `a > -1`, `b > 0`. -/
theorem integral_Ioi_rpow_mul_exp_neg_eq {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ a * Real.exp (-(b * t)) = Gamma (a + 1) * (1 / b) ^ (a + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a + 1) (by linarith) hb
  rw [add_sub_cancel_right] at h
  rw [h, mul_comm]

/-- **Gamma tail bound** (INF20 T20.7): for `a > -1`, `b > 0`, `L ≥ 0`,
`∫_L^∞ t^a e^{-bt} dt ≤ Γ(a+1) (2/b)^{a+1} e^{-bL/2}`. -/
theorem integral_Ioi_rpow_mul_exp_neg_le {a b L : ℝ} (ha : -1 < a) (hb : 0 < b) (hL : 0 ≤ L) :
    ∫ t in Ioi L, t ^ a * Real.exp (-(b * t)) ≤
      Gamma (a + 1) * (2 / b) ^ (a + 1) * Real.exp (-(b * L) / 2) := by
  have hsub : Ioi L ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hL
  have hb2 : 0 < b / 2 := half_pos hb
  have hI0 : IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-(b / 2 * t))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi ha hb2
  have hIb : IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-(b * t))) (Ioi L) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi ha hb).mono_set hsub
  have hstep1 : ∫ t in Ioi L, t ^ a * Real.exp (-(b * t)) ≤
      ∫ t in Ioi L, Real.exp (-(b * L) / 2) * (t ^ a * Real.exp (-(b / 2 * t))) := by
    refine setIntegral_mono_on hIb ((hI0.mono_set hsub).const_mul _) measurableSet_Ioi
      fun t ht => ?_
    have ht0 : 0 < t := lt_of_le_of_lt hL ht
    have hexp : Real.exp (-(b * t)) ≤ Real.exp (-(b * L) / 2) * Real.exp (-(b / 2 * t)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : b * L ≤ b * t := mul_le_mul_of_nonneg_left (le_of_lt ht) hb.le
      linarith
    calc t ^ a * Real.exp (-(b * t))
        ≤ t ^ a * (Real.exp (-(b * L) / 2) * Real.exp (-(b / 2 * t))) :=
          mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht0.le _)
      _ = _ := by ring
  have hstep2 : ∫ t in Ioi L, t ^ a * Real.exp (-(b / 2 * t)) ≤
      ∫ t in Ioi (0 : ℝ), t ^ a * Real.exp (-(b / 2 * t)) := by
    refine setIntegral_mono_set hI0 ?_ (Eventually.of_forall hsub)
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  rw [integral_const_mul] at hstep1
  rw [integral_Ioi_rpow_mul_exp_neg_eq ha hb2] at hstep2
  have hE : 0 ≤ Real.exp (-(b * L) / 2) := (Real.exp_pos _).le
  calc ∫ t in Ioi L, t ^ a * Real.exp (-(b * t))
      ≤ Real.exp (-(b * L) / 2) * (Gamma (a + 1) * (1 / (b / 2)) ^ (a + 1)) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hE)
    _ = Gamma (a + 1) * (2 / b) ^ (a + 1) * Real.exp (-(b * L) / 2) := by
        rw [show 1 / (b / 2) = 2 / b by field_simp]
        ring

/-- **Gamma bound on a bounded window** (INF20 T20.7; tex 6754–6771, B0362): for `a > -1`,
`b > 0`, `0 ≤ θ`, `∫_{(θ, R]} r^a e^{-br} dr ≤ Γ(a+1) (1/b)^{a+1}`. -/
theorem integral_Ioc_rpow_mul_exp_neg_le {a b θ R : ℝ} (ha : -1 < a) (hb : 0 < b) (hθ : 0 ≤ θ) :
    ∫ r in Ioc θ R, r ^ a * Real.exp (-(b * r)) ≤ Gamma (a + 1) * (1 / b) ^ (a + 1) := by
  rw [← integral_Ioi_rpow_mul_exp_neg_eq ha hb]
  refine setIntegral_mono_set (integrableOn_rpow_mul_exp_neg_mul_Ioi ha hb) ?_
    (Eventually.of_forall fun r hr => lt_of_le_of_lt hθ hr.1)
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le

/-- `(1+u)^M ≤ 2^M (1 + u^M)` for `u ≥ 0`, `M ≥ 0`. -/
theorem one_add_rpow_le {u M : ℝ} (hu : 0 ≤ u) (hM : 0 ≤ M) :
    (1 + u) ^ M ≤ 2 ^ M * (1 + u ^ M) := by
  have h2 : (0 : ℝ) ≤ 2 ^ M := Real.rpow_nonneg (by norm_num) _
  have huM : 0 ≤ u ^ M := Real.rpow_nonneg hu _
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ M ≤ 2 ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ ≤ 2 ^ M * (1 + u ^ M) := by nlinarith
  · calc (1 + u) ^ M ≤ (2 * u) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = 2 ^ M * u ^ M := Real.mul_rpow (by norm_num) hu
      _ ≤ 2 ^ M * (1 + u ^ M) := by nlinarith

theorem measurable_one_add_rpow_mul_exp (M c : ℝ) :
    Measurable (fun u : ℝ => (1 + u) ^ M * Real.exp (-(c * u))) := by
  fun_prop

/-- **Polynomial weight against an exponential** (INF20 T20.7; tex 2722–2735, B0179; tex
6406–6428, B0339): `(1+u)^M e^{-cu}` is integrable on `(0, ∞)` for every real `M` and `c > 0`. -/
theorem integrableOn_one_add_rpow_mul_exp_neg {M c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (1 + u) ^ M * Real.exp (-(c * u))) (Ioi 0) := by
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-(c * u))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hc
  rcases le_total M 0 with hM | hM
  · refine Integrable.mono' hexp (measurable_one_add_rpow_mul_exp M c).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.exp_pos _).le)]
    calc (1 + u) ^ M * Real.exp (-(c * u)) ≤ 1 * Real.exp (-(c * u)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hM)
            (Real.exp_pos _).le
      _ = Real.exp (-(c * u)) := one_mul _
  · have hpow : IntegrableOn (fun u : ℝ => u ^ M * Real.exp (-(c * u))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hc
    have hdom : IntegrableOn
        (fun u : ℝ => 2 ^ M * (Real.exp (-(c * u)) + u ^ M * Real.exp (-(c * u)))) (Ioi 0) :=
      (hexp.add hpow).const_mul _
    refine Integrable.mono' hdom (measurable_one_add_rpow_mul_exp M c).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.exp_pos _).le)]
    have hE : 0 ≤ Real.exp (-(c * u)) := (Real.exp_pos _).le
    calc (1 + u) ^ M * Real.exp (-(c * u)) ≤ 2 ^ M * (1 + u ^ M) * Real.exp (-(c * u)) :=
          mul_le_mul_of_nonneg_right (one_add_rpow_le hu0.le hM) hE
      _ = 2 ^ M * (Real.exp (-(c * u)) + u ^ M * Real.exp (-(c * u))) := by ring

/-- **Explicit polynomial bound** (INF20 T20.7; tex 2722–2735, B0179): for `M ≥ 0`, `c > 0`,
`∫_0^∞ (1+u)^M e^{-cu} du ≤ 2^M (1/c + Γ(M+1) (1/c)^{M+1})`. -/
theorem integral_one_add_rpow_mul_exp_neg_le {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), (1 + u) ^ M * Real.exp (-(c * u)) ≤
      2 ^ M * (1 / c + Gamma (M + 1) * (1 / c) ^ (M + 1)) := by
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-(c * u))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hc
  have hpow : IntegrableOn (fun u : ℝ => u ^ M * Real.exp (-(c * u))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hc
  have hexpval : ∫ u in Ioi (0 : ℝ), Real.exp (-(c * u)) = 1 / c := by
    have h := integral_Ioi_rpow_mul_exp_neg_eq (a := 0) (by norm_num) hc
    simp only [Real.rpow_zero, one_mul, zero_add, Real.rpow_one, Real.Gamma_one] at h
    exact h
  calc ∫ u in Ioi (0 : ℝ), (1 + u) ^ M * Real.exp (-(c * u))
      ≤ ∫ u in Ioi (0 : ℝ), 2 ^ M * (Real.exp (-(c * u)) + u ^ M * Real.exp (-(c * u))) := by
        refine setIntegral_mono_on (integrableOn_one_add_rpow_mul_exp_neg hc)
          ((hexp.add hpow).const_mul _) measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := hu
        calc (1 + u) ^ M * Real.exp (-(c * u)) ≤ 2 ^ M * (1 + u ^ M) * Real.exp (-(c * u)) :=
              mul_le_mul_of_nonneg_right (one_add_rpow_le hu0.le hM) (Real.exp_pos _).le
          _ = _ := by ring
    _ = 2 ^ M * (1 / c + Gamma (M + 1) * (1 / c) ^ (M + 1)) := by
        rw [integral_const_mul, integral_add hexp hpow, hexpval,
          integral_Ioi_rpow_mul_exp_neg_eq (by linarith) hc]

/-- **Comparison of the B0339 integral** (INF20 T20.7; tex 6406–6428, `eq:st18-t00347`, B0339):
for `M ≥ 0`, `0 ≤ κ ≤ 1` (here `κ = e_c/θ`, `e_c ≤ θ`) and `0 < c' ≤ c` (here
`c = b₁ - A e_c ≥ c' = b₁/2`),
`∫_0^∞ (1 + κu)^M e^{-cu} du ≤ ∫_0^∞ (1+u)^M e^{-c'u} du`, a bound independent of `κ` and `c`. -/
theorem integral_one_add_mul_rpow_mul_exp_neg_le {M κ c c' : ℝ} (hM : 0 ≤ M) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (hc' : 0 < c') (hcc : c' ≤ c) :
    ∫ u in Ioi (0 : ℝ), (1 + κ * u) ^ M * Real.exp (-(c * u)) ≤
      ∫ u in Ioi (0 : ℝ), (1 + u) ^ M * Real.exp (-(c' * u)) := by
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      (1 + κ * u) ^ M * Real.exp (-(c * u)) ≤ (1 + u) ^ M * Real.exp (-(c' * u)) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hku : κ * u ≤ u := by nlinarith
    have h1 : (1 + κ * u) ^ M ≤ (1 + u) ^ M :=
      Real.rpow_le_rpow (by nlinarith) (by linarith) hM
    have h2 : Real.exp (-(c * u)) ≤ Real.exp (-(c' * u)) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
  have hmeas : Measurable (fun u : ℝ => (1 + κ * u) ^ M * Real.exp (-(c * u))) := by fun_prop
  have hint : IntegrableOn (fun u : ℝ => (1 + κ * u) ^ M * Real.exp (-(c * u))) (Ioi 0) := by
    refine Integrable.mono' (integrableOn_one_add_rpow_mul_exp_neg (M := M) hc')
      hmeas.aestronglyMeasurable
      ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by nlinarith) _)
      (Real.exp_pos _).le)]
    exact hpt u hu
  exact setIntegral_mono_on hint (integrableOn_one_add_rpow_mul_exp_neg (M := M) hc')
    measurableSet_Ioi hpt

/-- **The inversion substitution `u = c/a`** (INF20 T20.7; tex 2348–2353, B0154): for `c > 0`
and any `g`, `∫_0^∞ (c/a²) g(c/a) da = ∫_0^∞ g(u) du` (Bochner integrals; both sides are
integrable together, by the change of variables). -/
theorem integral_Ioi_comp_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 < c) (g : ℝ → E) :
    ∫ a in Ioi (0 : ℝ), (c / a ^ 2) • g (c / a) = ∫ u in Ioi (0 : ℝ), g u := by
  have h1 := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  set F : ℝ → E := fun x => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ)) with hF
  have h2 := integral_comp_mul_left_Ioi F 0 (inv_pos.2 hc)
  rw [mul_zero] at h2
  rw [← h1]
  have hcongr : ∫ a in Ioi (0 : ℝ), (c / a ^ 2) • g (c / a) =
      ∫ a in Ioi (0 : ℝ), c⁻¹ • F (c⁻¹ * a) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    have ha0 : 0 < a := ha
    have hx : 0 < c⁻¹ * a := mul_pos (inv_pos.2 hc) ha0
    simp only [hF, smul_smul]
    congr 1
    · rw [abs_neg, abs_one, one_mul, show (-1 : ℝ) - 1 = -2 by norm_num,
        Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    · rw [Real.rpow_neg_one]
      congr 1
      field_simp
  rw [hcongr, integral_smul, h2, smul_smul, mul_inv_cancel₀ (inv_ne_zero hc.ne'), one_smul]

/-- **A bounded power integral** (INF20 T20.7; tex 6754–6771, B0362): for `C > 1` and
`0 ≤ θ ≤ b`, `∫_θ^b r^{C-2} dr ≤ b^{C-1}/(C-1)`. -/
theorem integral_rpow_sub_two_le {C θ b : ℝ} (hC : 1 < C) (hθ : 0 ≤ θ) (hθb : θ ≤ b) :
    ∫ r in θ..b, r ^ (C - 2) ≤ b ^ (C - 1) / (C - 1) := by
  rw [integral_rpow (Or.inl (by linarith)), show C - 2 + 1 = C - 1 by ring]
  have hC1 : 0 < C - 1 := by linarith
  have hθp : 0 ≤ θ ^ (C - 1) := Real.rpow_nonneg hθ _
  rw [div_le_div_iff_of_pos_right hC1]
  linarith

end UnforcedLeray.Special
