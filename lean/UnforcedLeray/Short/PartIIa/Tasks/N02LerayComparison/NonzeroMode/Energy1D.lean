import UnforcedLeray.Short.PartIIa.Sub.N02_4_4
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Part II-a, task `PartII-a:N02/4/4`: the one-mode energy identity `NzEnergy1D`

Source of record: `the November 2 reference manuscript`, lines 1713-1722 (the flat
one-mode system). Target: `NzEnergy1D` in `Sub/N02_4_4.lean`.

Proof. Pointwise, with `a = i k φ - ψ'`, `b = φ' + i k ψ`,
`‖a‖² + ‖b‖² = D - 2 Re(i k G')`, where `D` is the right-hand integrand and
`G = φ conj ψ`, `G' = φ' conj ψ + φ conj ψ'`. `G` is `C¹` and tends to `0` at `±∞`, and `G'` is
integrable, so `∫ G' = 0`. Integrability comes from the exponential bounds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-! ### Helpers -/

theorem nze_alg (k : ℝ) (x y u v : ℂ) :
    ‖Complex.I * (k : ℂ) * x - v‖ ^ 2 + ‖y + Complex.I * (k : ℂ) * u‖ ^ 2 =
      k ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 + k ^ 2 * ‖u‖ ^ 2 + ‖v‖ ^ 2
        - 2 * (Complex.I * (k : ℂ) * (y * star u + x * star v)).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem nze_tendsto_atTop (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (-b * |t|)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ => -b * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hc : Tendsto (fun t : ℝ => -b * |t|) atTop atBot :=
    Tendsto.congr' (by
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp [abs_of_nonneg ht]) h2
  exact Real.tendsto_exp_atBot.comp hc

theorem nze_tendsto_atBot (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (-b * |t|)) atBot (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ => b * t) atBot atBot := tendsto_id.const_mul_atBot hb
  have hc : Tendsto (fun t : ℝ => -b * |t|) atBot atBot :=
    Tendsto.congr' (by
      filter_upwards [eventually_le_atBot 0] with t ht
      simp [abs_of_nonpos ht]) h2
  exact Real.tendsto_exp_atBot.comp hc

theorem nze_integrable_exp (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (exp_neg_integrableOn_Ioi 0 hb)
  have hw : Integrable (Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t))) :=
    (integrable_indicator_iff measurableSet_Ici).mpr hI
  have hw' : Integrable (fun t : ℝ =>
      Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t)) (-t)) :=
    hw.comp_neg
  refine Integrable.mono' (hw.add hw') ?_ ?_
  · exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-b * |t|))).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    show ‖Real.exp (-b * |t|)‖ ≤
      Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t)) t +
        Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t)) (-t)
    have hnn : ∀ s : ℝ, 0 ≤ Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t)) s :=
      fun s => Set.indicator_nonneg (fun x _ => (Real.exp_pos _).le) s
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      have h1 : Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t)) t =
          Real.exp (-b * t) := Set.indicator_of_mem (mem_Ici.mpr ht) _
      linarith [hnn (-t)]
    · rw [abs_of_nonpos ht]
      have h1 : Set.indicator (Ici (0 : ℝ)) (fun t : ℝ => Real.exp (-b * t)) (-t) =
          Real.exp (-b * -t) := Set.indicator_of_mem (mem_Ici.mpr (by linarith)) _
      linarith [hnn t]

theorem nze_integrable_of_norm_le {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {M b : ℝ} (hb : 0 < b)
    (h : ∀ t, ‖f t‖ ≤ M * Real.exp (-b * |t|)) : Integrable f :=
  Integrable.mono' ((nze_integrable_exp b hb).const_mul M) hf.aestronglyMeasurable
    (Eventually.of_forall h)

theorem nze_mul_le {C κ : ℝ} (hC : 0 ≤ C) (t x y : ℝ) (hy : 0 ≤ y)
    (hxb : x ≤ C * Real.exp (-κ * |t|)) (hyb : y ≤ C * Real.exp (-κ * |t|)) :
    x * y ≤ C * C * Real.exp (-(2 * κ) * |t|) := by
  have he : 0 ≤ Real.exp (-κ * |t|) := (Real.exp_pos _).le
  have hE : Real.exp (-κ * |t|) * Real.exp (-κ * |t|) = Real.exp (-(2 * κ) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc x * y ≤ (C * Real.exp (-κ * |t|)) * (C * Real.exp (-κ * |t|)) :=
        mul_le_mul hxb hyb hy (mul_nonneg hC he)
    _ = C * C * (Real.exp (-κ * |t|) * Real.exp (-κ * |t|)) := by ring
    _ = C * C * Real.exp (-(2 * κ) * |t|) := by rw [hE]

/-! ### The energy identity -/

theorem nzEnergy1D : NzEnergy1D := by
  unfold NzEnergy1D
  intro k φ ψ a b hφ hψ hdec ha hb
  obtain ⟨κ, C, hκ, hbd⟩ := hdec
  have hC0 : 0 ≤ C := by
    have h := (hbd 0).1
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have hφc : Continuous φ := hφ.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv_one
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv_one
  have hφd : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
    ((hφ.differentiable (by norm_num)) t).hasDerivAt
  have hψd : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t =>
    ((hψ.differentiable (by norm_num)) t).hasDerivAt
  -- integrability of the squared norms
  have hsqInt : ∀ f : ℝ → ℂ, Continuous f → (∀ t, ‖f t‖ ≤ C * Real.exp (-κ * |t|)) →
      Integrable (fun t => ‖f t‖ ^ 2) := by
    intro f hf hfb
    have hcont : Continuous (fun t => ‖f t‖ ^ 2) := (hf.norm).pow 2
    refine nze_integrable_of_norm_le hcont (M := C * C) (b := 2 * κ) (by linarith) ?_
    intro t
    show ‖‖f t‖ ^ 2‖ ≤ C * C * Real.exp (-(2 * κ) * |t|)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    exact nze_mul_le hC0 t _ _ (norm_nonneg _) (hfb t) (hfb t)
  have hI1 : Integrable (fun t => ‖φ t‖ ^ 2) := hsqInt φ hφc (fun t => (hbd t).1)
  have hI2 : Integrable (fun t => ‖deriv φ t‖ ^ 2) :=
    hsqInt (deriv φ) hφ'c (fun t => (hbd t).2.1)
  have hI3 : Integrable (fun t => ‖ψ t‖ ^ 2) := hsqInt ψ hψc (fun t => (hbd t).2.2.1)
  have hI4 : Integrable (fun t => ‖deriv ψ t‖ ^ 2) :=
    hsqInt (deriv ψ) hψ'c (fun t => (hbd t).2.2.2)
  have hD : Integrable (fun t => k ^ 2 * ‖φ t‖ ^ 2 + ‖deriv φ t‖ ^ 2 + k ^ 2 * ‖ψ t‖ ^ 2
      + ‖deriv ψ t‖ ^ 2) :=
    (((hI1.const_mul (k ^ 2)).add hI2).add (hI3.const_mul (k ^ 2))).add hI4
  -- the cross term `G' = φ' conj ψ + φ conj ψ'` and `G = φ conj ψ`
  have hGd : ∀ t, HasDerivAt (fun s => φ s * star (ψ s))
      (deriv φ t * star (ψ t) + φ t * star (deriv ψ t)) t :=
    fun t => (hφd t).mul (hψd t).star
  have hG'c : Continuous (fun t => deriv φ t * star (ψ t) + φ t * star (deriv ψ t)) :=
    (hφ'c.mul hψc.star).add (hφc.mul hψ'c.star)
  have hG'b : ∀ t, ‖deriv φ t * star (ψ t) + φ t * star (deriv ψ t)‖ ≤
      (2 * C * C) * Real.exp (-(2 * κ) * |t|) := by
    intro t
    obtain ⟨h1, h2, h3, h4⟩ := hbd t
    calc ‖deriv φ t * star (ψ t) + φ t * star (deriv ψ t)‖
        ≤ ‖deriv φ t * star (ψ t)‖ + ‖φ t * star (deriv ψ t)‖ := norm_add_le _ _
      _ = ‖deriv φ t‖ * ‖ψ t‖ + ‖φ t‖ * ‖deriv ψ t‖ := by
          simp only [norm_mul, norm_star]
      _ ≤ C * C * Real.exp (-(2 * κ) * |t|) + C * C * Real.exp (-(2 * κ) * |t|) :=
          add_le_add (nze_mul_le hC0 t _ _ (norm_nonneg _) h2 h3)
            (nze_mul_le hC0 t _ _ (norm_nonneg _) h1 h4)
      _ = (2 * C * C) * Real.exp (-(2 * κ) * |t|) := by ring
  have hG'I : Integrable (fun t => deriv φ t * star (ψ t) + φ t * star (deriv ψ t)) :=
    nze_integrable_of_norm_le hG'c (M := 2 * C * C) (b := 2 * κ) (by linarith) hG'b
  -- decay of `G` at both ends
  have hGbound : ∀ t, ‖φ t * star (ψ t)‖ ≤ C * C * Real.exp (-(2 * κ) * |t|) := by
    intro t
    obtain ⟨h1, h2, h3, h4⟩ := hbd t
    rw [norm_mul, norm_star]
    exact nze_mul_le hC0 t _ _ (norm_nonneg _) h1 h3
  have hGtop : Tendsto (fun t : ℝ => φ t * star (ψ t)) atTop (𝓝 0) := by
    have htend : Tendsto (fun t : ℝ => C * C * Real.exp (-(2 * κ) * |t|)) atTop (𝓝 0) := by
      simpa using (nze_tendsto_atTop (2 * κ) (by linarith)).const_mul (C * C)
    exact squeeze_zero_norm hGbound htend
  have hGbot : Tendsto (fun t : ℝ => φ t * star (ψ t)) atBot (𝓝 0) := by
    have htend : Tendsto (fun t : ℝ => C * C * Real.exp (-(2 * κ) * |t|)) atBot (𝓝 0) := by
      simpa using (nze_tendsto_atBot (2 * κ) (by linarith)).const_mul (C * C)
    exact squeeze_zero_norm hGbound htend
  -- the cross term integrates to zero
  have hFTC : ∫ t, (deriv φ t * star (ψ t) + φ t * star (deriv ψ t)) = 0 := by
    have h := integral_of_hasDerivAt_of_tendsto
      (f := fun s => φ s * star (ψ s))
      (f' := fun t => deriv φ t * star (ψ t) + φ t * star (deriv ψ t))
      hGd hG'I hGbot hGtop
    simpa using h
  have hhI : Integrable (fun t => Complex.I * (k : ℂ) *
      (deriv φ t * star (ψ t) + φ t * star (deriv ψ t))) :=
    hG'I.const_mul _
  have hre : ∫ t, (Complex.I * (k : ℂ) *
      (deriv φ t * star (ψ t) + φ t * star (deriv ψ t))).re = 0 := by
    have h2 : ∫ t, Complex.I * (k : ℂ) *
        (deriv φ t * star (ψ t) + φ t * star (deriv ψ t)) = 0 := by
      rw [integral_const_mul, hFTC, mul_zero]
    have h1 := integral_re hhI
    rw [h2] at h1
    simpa using h1
  -- pointwise identity
  have hpt : ∀ t, ‖a t‖ ^ 2 + ‖b t‖ ^ 2 =
      (k ^ 2 * ‖φ t‖ ^ 2 + ‖deriv φ t‖ ^ 2 + k ^ 2 * ‖ψ t‖ ^ 2 + ‖deriv ψ t‖ ^ 2)
        - 2 * (Complex.I * (k : ℂ) *
          (deriv φ t * star (ψ t) + φ t * star (deriv ψ t))).re := by
    intro t
    rw [← ha t, ← hb t]
    exact nze_alg k (φ t) (deriv φ t) (ψ t) (deriv ψ t)
  have hR : Integrable (fun t => 2 * (Complex.I * (k : ℂ) *
      (deriv φ t * star (ψ t) + φ t * star (deriv ψ t))).re) :=
    (hhI.re).const_mul 2
  have hint : ∫ t, (‖a t‖ ^ 2 + ‖b t‖ ^ 2) = ∫ t, ((k ^ 2 * ‖φ t‖ ^ 2 + ‖deriv φ t‖ ^ 2
      + k ^ 2 * ‖ψ t‖ ^ 2 + ‖deriv ψ t‖ ^ 2)
        - 2 * (Complex.I * (k : ℂ) *
          (deriv φ t * star (ψ t) + φ t * star (deriv ψ t))).re) :=
    integral_congr_ae (Eventually.of_forall fun t => hpt t)
  rw [hint, integral_sub hD hR, integral_const_mul, hre, mul_zero, sub_zero]

end UnforcedLeray.Short.PartIIa
