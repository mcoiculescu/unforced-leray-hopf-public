import UnforcedLeray.Short.PartIIIa.Targets
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Part III-a, task `T05`: the Hardy kernel bound (SP 3499-3503, `eq:short-causal-hardy`)

Proves `hardyKernel : HardyKernel` (`Targets.lean`). Write `k(u) = u^σ (1-u)^{-1/2}` and
`B = ∫_0^1 u^{σ-1/4} (1-u)^{-1/2} du`, the constant `ofReal B` of `HardyKernel`.
With `t = s u`, `Z = ∫_0^∞ t^{-1/2} f(t)² dt`:

1. `∫_0^s (t/s)^σ (s-t)^{-1/2} f(t) dt = s^{1/2} ∫_0^1 k(u) f(su) du`;
2. weighted Cauchy-Schwarz with weights `u^{-1/4}`, `u^{1/4}`:
   `(∫_0^1 k(u) f(su) du)² ≤ B ∫_0^1 k(u) u^{1/4} f(su)² du`;
3. Tonelli, and `∫_0^∞ s^{-1/2} f(su)² ds = u^{-1/2} Z`;
4. `∫_0^1 k(u) u^{-1/4} du = B`, so the squared left side is at most `B² Z`.

Step 2 is the Minkowski step of the source (SP 3499-3503, sketch items (3)-(5)) with the same
constant `B`; it is proved here by Hölder's inequality, so no Minkowski lemma is imported.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Integrability of `u ^ a * (1 - u) ^ b` on `(0,1)` for `a, b > -1`. A copy of
`UnforcedLeray.Special.integrableOn_rpow_mul_one_sub_rpow` (`Lib/SpecialFunctions/BetaConstants.lean`),
kept local so that this file imports only Mathlib and the statement file. -/
theorem t05_integrableOn_beta {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    IntegrableOn (fun u : ℝ => u ^ a * (1 - u) ^ b) (Ioo 0 1) := by
  have hc := Complex.betaIntegral_convergent (u := ((a + 1 : ℝ) : ℂ)) (v := ((b + 1 : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)
  have hc' := hc.1.mono_set Ioo_subset_Ioc_self
  refine IntegrableOn.congr_fun hc'.norm (fun u hu => ?_) measurableSet_Ioo
  have h1 : ((a + 1 : ℝ) : ℂ) - 1 = (a : ℂ) := by push_cast; ring
  have h2 : ((b + 1 : ℝ) : ℂ) - 1 = (b : ℂ) := by push_cast; ring
  have h3 : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, h3, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1,
    Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.2 hu.2), Complex.ofReal_re, Complex.ofReal_re]

/-- Scaling on `(0, s)`: `∫_0^s g = s ∫_0^1 g(su)` (the substitution `t = s u`). -/
theorem t05_scale_Ioo {s : ℝ} (hs : 0 < s) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo (0 : ℝ) s, g t = ENNReal.ofReal s * ∫⁻ u in Ioo (0 : ℝ) 1, g (s * u) := by
  have himg : (fun u : ℝ => s * u) '' Ioo 0 1 = Ioo 0 s := by
    rw [image_mul_left_Ioo hs]
    simp
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun u : ℝ => s * u)
    (f' := fun _ => s) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul s).hasDerivWithinAt)
    (fun a _ b _ hab => mul_left_cancel₀ hs.ne' hab) g
  rw [himg] at h
  rw [h]
  simp only [abs_of_pos hs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Scaling on `(0, ∞)`: `∫_0^∞ H = u ∫_0^∞ H(su) ds` for `u > 0`. -/
theorem t05_scale_Ioi {u : ℝ} (hu : 0 < u) (H : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), H r = ENNReal.ofReal u * ∫⁻ s in Ioi (0 : ℝ), H (s * u) := by
  have himg : (fun s : ℝ => s * u) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mul_pos hy hu
    · intro hx
      exact ⟨x / u, div_pos hx hu, div_mul_cancel₀ x hu.ne'⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun s : ℝ => s * u)
    (f' := fun _ => u) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun x _ => by simpa using ((hasDerivAt_id x).mul_const u).hasDerivWithinAt)
    (fun a _ b _ hab => mul_right_cancel₀ hu.ne' hab) H
  rw [himg] at h
  rw [h]
  simp only [abs_of_pos hu]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Pull a common real factor through: `c x = d y` gives `ofReal c (ofReal x F) = ofReal d (ofReal y F)`. -/
theorem t05_ofReal_pair {c d x y : ℝ} (F : ℝ≥0∞) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : c * x = d * y) :
    ENNReal.ofReal c * (ENNReal.ofReal x * F) = ENNReal.ofReal d * (ENNReal.ofReal y * F) := by
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd, h]

/-- The scaling identity of the outer integral: for `u > 0`,
`∫_0^∞ s^{-1/2} f(su)² ds = u^{-1/2} ∫_0^∞ t^{-1/2} f(t)² dt`. -/
theorem t05_scale_identity {u : ℝ} (hu : 0 < u) (f : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2 =
      ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * f t ^ 2 := by
  have hsc : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * f r ^ 2 =
      ENNReal.ofReal u * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((s * u) ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2 :=
    t05_scale_Ioi hu _
  have hH : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((s * u) ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2 =
      ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) *
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    rw [Real.mul_rpow hs'.le hu.le, ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _)]
    ring
  have hreal : u ^ (-1 / 2 : ℝ) * u * u ^ (-1 / 2 : ℝ) = 1 := by
    have h1 : u ^ (-1 / 2 : ℝ) * u ^ (-1 / 2 : ℝ) = u⁻¹ := by
      rw [← Real.rpow_add hu, show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num, Real.rpow_neg_one]
    rw [mul_right_comm, h1, inv_mul_cancel₀ hu.ne']
  have hk : ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) * ENNReal.ofReal u *
      ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hu.le _) hu.le), hreal,
      ENNReal.ofReal_one]
  rw [hH] at hsc
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2
      = (ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) * ENNReal.ofReal u *
          ENNReal.ofReal (u ^ (-1 / 2 : ℝ))) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2 := by
        rw [hk, one_mul]
    _ = ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal u *
          (ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) *
            ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2)) := by
        ring
    _ = ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) *
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * f t ^ 2 := by
        rw [hsc]

theorem t05_rpow_half_sq (y : ℝ≥0∞) : (y ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = y := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem t05_sq_rpow_half (y : ℝ≥0∞) : (y ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = y := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `(A (A Z))^{1/2} = A Z^{1/2}`. -/
theorem t05_sqrt_aux (A Z : ℝ≥0∞) : (A * (A * Z)) ^ (1 / 2 : ℝ) = A * Z ^ (1 / 2 : ℝ) := by
  rw [show A * (A * Z) = A ^ (2 : ℕ) * Z by ring,
    ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num), t05_rpow_half_sq]

/-- Weighted Cauchy-Schwarz (Hölder with exponents `2, 2`) in the form
`(∫ a F)² ≤ (∫ a p)(∫ a q F²)` when `p q = 1` almost everywhere. -/
theorem t05_weighted_cs {μ : Measure ℝ} {a p q F : ℝ → ℝ≥0∞} (ha : Measurable a)
    (hp : Measurable p) (hq : Measurable q) (hF : Measurable F)
    (hpq : ∀ᵐ x ∂μ, p x * q x = 1) :
    (∫⁻ x, a x * F x ∂μ) ^ 2 ≤ (∫⁻ x, a x * p x ∂μ) * (∫⁻ x, a x * q x * F x ^ 2 ∂μ) := by
  have hc : Real.conjExponent 2 = 2 := by norm_num [Real.conjExponent]
  have hpq2 : Real.HolderConjugate 2 2 := by
    have h := Real.HolderConjugate.conjExponent (p := (2 : ℝ)) (by norm_num)
    rwa [hc] at h
  have hg₁ : AEMeasurable (fun x => (a x * p x) ^ (1 / (2 : ℝ))) μ :=
    ((ha.mul hp).pow_const _).aemeasurable
  have hg₂ : AEMeasurable (fun x => (a x * q x * F x ^ 2) ^ (1 / (2 : ℝ))) μ :=
    (((ha.mul hq).mul (hF.pow_const 2)).pow_const _).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq2 hg₁ hg₂
  have e1 : ∀ x, ((a x * p x) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = a x * p x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e2 : ∀ x, ((a x * q x * F x ^ 2) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = a x * q x * F x ^ 2 := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [e1, e2, Pi.mul_apply] at hH
  have hkey : ∀ x, p x * q x = 1 → a x * p x * (a x * q x * F x ^ 2) = (a x * F x) ^ 2 := by
    intro x hx
    calc a x * p x * (a x * q x * F x ^ 2) = a x ^ 2 * (p x * q x) * F x ^ 2 := by ring
      _ = (a x * F x) ^ 2 := by rw [hx]; ring
  have hae : ∫⁻ x, a x * F x ∂μ =
      ∫⁻ x, (a x * p x) ^ (1 / (2 : ℝ)) * (a x * q x * F x ^ 2) ^ (1 / (2 : ℝ)) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hpq] with x hx
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num), hkey x hx,
      t05_rpow_half_sq]
  have hJ : ∫⁻ x, a x * F x ∂μ ≤
      (∫⁻ x, a x * p x ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, a x * q x * F x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [hae]
    exact hH
  calc (∫⁻ x, a x * F x ∂μ) ^ 2
      ≤ ((∫⁻ x, a x * p x ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, a x * q x * F x ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ x, a x * p x ∂μ) * (∫⁻ x, a x * q x * F x ^ 2 ∂μ) := by
        rw [mul_pow, t05_sq_rpow_half, t05_sq_rpow_half]

/-- The pointwise identity `k(u) u^{1/4} u^{-1/2} = u^{σ+3/4-1}(1-u)^{-1/2}` (for `u ∈ (0,1)`). -/
theorem t05_key_u {σ u : ℝ} (hu : 0 < u) (h1u : 0 < 1 - u) :
    ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
      ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) =
      ENNReal.ofReal (u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ)) := by
  have hk0 : 0 ≤ u ^ σ * (1 - u) ^ (-1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg h1u.le _)
  have key : u ^ σ * u ^ (1 / 4 : ℝ) * u ^ (-1 / 2 : ℝ) = u ^ (σ + 3 / 4 - 1) := by
    rw [← Real.rpow_add hu, ← Real.rpow_add hu]
    congr 1
    ring
  rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 (Real.rpow_nonneg hu.le _))]
  congr 1
  rw [← key]
  ring

theorem hardyKernel : UnforcedLeray.Short.IIIa.HardyKernel := by
  intro σ hσ f hf
  have hσ1 : (-1 : ℝ) < σ + 3 / 4 - 1 := by linarith
  have hBint := t05_integrableOn_beta hσ1 (by norm_num : (-1 : ℝ) < -1 / 2)
  have hBnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun u : ℝ => u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (by linarith [hu.2]) _)
  have hBeq : ENNReal.ofReal (∫ u in Ioo (0 : ℝ) 1, u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ))
      = ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ)) :=
    ofReal_integral_eq_lintegral_ofReal hBint hBnn
  rw [hBeq]
  simp only [ENNReal.rpow_two]
  set Aint : ℝ≥0∞ := ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ))
    with hAint
  set Z : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * f t ^ 2 with hZ
  have hAne : Aint ≠ ⊤ := by
    rw [← hBeq]
    exact ENNReal.ofReal_ne_top
  -- (1) the inner integral, by the substitution `t = s u`
  have hI : ∀ s : ℝ, 0 < s →
      ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * f t
        = ENNReal.ofReal (s ^ (1 / 2 : ℝ)) *
          ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u) := by
    intro s hs
    have hs12 : s ^ (1 / 2 : ℝ) = s * s ^ (-1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hs, Real.rpow_one]
    calc ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * f t
        = ENNReal.ofReal s * ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (((s * u) / s) ^ σ * (s - s * u) ^ (-1 / 2 : ℝ)) * f (s * u) :=
          t05_scale_Ioo hs _
      _ = ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal s *
            (ENNReal.ofReal (((s * u) / s) ^ σ * (s - s * u) ^ (-1 / 2 : ℝ)) * f (s * u)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (s ^ (1 / 2 : ℝ)) *
            (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) := by
          refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
          have h1u : (0 : ℝ) < 1 - u := by linarith [hu.2]
          have hr : s * (((s * u) / s) ^ σ * (s - s * u) ^ (-1 / 2 : ℝ)) =
              s ^ (1 / 2 : ℝ) * (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) := by
            rw [mul_div_cancel_left₀ u hs.ne', show s - s * u = s * (1 - u) by ring,
              Real.mul_rpow hs.le h1u.le, hs12]
            ring
          exact t05_ofReal_pair _ hs.le (Real.rpow_nonneg hs.le _) hr
      _ = ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (1') the outer weight `s^{-3/2} I(s)² = s^{-1/2} J(s)²`
  have hXpt : ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * f t) ^ 2
      = ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) ^ 2 := by
    intro s hs
    have hsq : (s ^ (1 / 2 : ℝ)) ^ 2 = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      norm_num
    have e3 : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
      rw [show (-1 / 2 : ℝ) = -3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]
    rw [hI s hs, mul_pow, ← ENNReal.ofReal_pow (Real.rpow_nonneg hs.le _), hsq, e3,
      ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    ring
  -- (2) weighted Cauchy-Schwarz for each `s`
  have hwc : ∀ s : ℝ, 0 < s →
      (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) ^ 2
      ≤ Aint * ∫⁻ u in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
            f (s * u) ^ 2 := by
    intro s _
    have hF : Measurable (fun u : ℝ => f (s * u)) := hf.comp (measurable_const_mul s)
    have ha : Measurable (fun u : ℝ => ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ))) :=
      ENNReal.measurable_ofReal.comp ((measurable_id.pow_const σ).mul
        ((measurable_const.sub measurable_id).pow_const _))
    have hp : Measurable (fun u : ℝ => ENNReal.ofReal (u ^ (-1 / 4 : ℝ))) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
    have hq : Measurable (fun u : ℝ => ENNReal.ofReal (u ^ (1 / 4 : ℝ))) :=
      ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
    have hpq : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        ENNReal.ofReal (u ^ (-1 / 4 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) = 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu.1.le _), ← Real.rpow_add hu.1]
      norm_num
    have hap : ∫⁻ u in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (-1 / 4 : ℝ)) = Aint := by
      rw [hAint]
      refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
      have hk0 : 0 ≤ u ^ σ * (1 - u) ^ (-1 / 2 : ℝ) :=
        mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (by linarith [hu.2]) _)
      have key2 : u ^ σ * u ^ (-1 / 4 : ℝ) = u ^ (σ + 3 / 4 - 1) := by
        rw [← Real.rpow_add hu.1]
        congr 1
        ring
      rw [← ENNReal.ofReal_mul hk0]
      congr 1
      rw [← key2]
      ring
    have h := t05_weighted_cs ha hp hq hF hpq
    calc _ ≤ (∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (-1 / 4 : ℝ))) *
          ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
              f (s * u) ^ 2 := h
      _ = Aint * ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
              f (s * u) ^ 2 := by
          rw [hap]
  -- (3) the joint integrand and its measurability
  have m1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have m2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ σ * (1 - p.2) ^ (-1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const σ).mul
      ((measurable_const.sub measurable_snd).pow_const _))
  have m3 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (1 / 4 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)
  have m4 : Measurable (fun p : ℝ × ℝ => f (p.1 * p.2) ^ 2) :=
    (hf.comp (measurable_fst.mul measurable_snd)).pow_const 2
  have hΦ : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-1 / 2 : ℝ)) *
      (ENNReal.ofReal (p.2 ^ σ * (1 - p.2) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (p.2 ^ (1 / 4 : ℝ)) *
        f (p.1 * p.2) ^ 2)) :=
    m1.mul ((m2.mul m3).mul m4)
  have hΨ : Measurable (fun u : ℝ => ENNReal.ofReal (u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul
      ((measurable_const.sub measurable_id).pow_const _))
  -- (4) the chain
  have hbound : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
      (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) ^ 2
      ≤ Aint * (Aint * Z) := by
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
          (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) ^ 2
        ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
          (Aint * ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
              f (s * u) ^ 2) :=
          setLIntegral_mono' measurableSet_Ioi (fun s hs => mul_le_mul_of_nonneg_left (hwc s hs) (by positivity))
      _ = Aint * ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
                f (s * u) ^ 2) := by
          rw [← lintegral_const_mul' _ _ hAne]
          refine setLIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
      _ = Aint * ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
                f (s * u) ^ 2) := by
          rw [lintegral_lintegral_swap (f := fun s u =>
            ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
                f (s * u) ^ 2)) hΦ.aemeasurable]
      _ = Aint * ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ)) * Z := by
          congr 1
          refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
          have hu0 : 0 < u := hu.1
          have h1u : 0 < 1 - u := sub_pos.2 hu.2
          calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ)) *
                  f (s * u) ^ 2)
              = (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ))) *
                ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * f (s * u) ^ 2 := by
                rw [← lintegral_const_mul' _ _
                  (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
                exact lintegral_congr (fun s => by ring)
            _ = (ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (1 / 4 : ℝ))) *
                (ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) * Z) := by
                rw [t05_scale_identity hu0 f]
            _ = ENNReal.ofReal (u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ)) * Z := by
                rw [← t05_key_u hu0 h1u]
                ring
      _ = Aint * (Aint * Z) := by
          rw [lintegral_mul_const _ hΨ]
  -- (5) conclusion
  have hX : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
      (∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * f t) ^ 2
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) ^ 2 :=
    setLIntegral_congr_fun measurableSet_Ioi (fun s hs => hXpt s hs)
  rw [hX]
  calc (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
          (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (u ^ σ * (1 - u) ^ (-1 / 2 : ℝ)) * f (s * u)) ^ 2)
        ^ (1 / 2 : ℝ)
      ≤ (Aint * (Aint * Z)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = Aint * Z ^ (1 / 2 : ℝ) := t05_sqrt_aux _ _

end UnforcedLeray.Short.IIIa
