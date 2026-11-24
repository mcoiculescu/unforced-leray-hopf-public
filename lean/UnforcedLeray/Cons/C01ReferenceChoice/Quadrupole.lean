import UnforcedLeray.Blueprint.Construction.Planar
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Step C1: the quadrupole is a bounded functional on `X_G`

`paper/main.tex`, the Gaussian space `X_G` (`eq:st18-t00005`, lines 672–677, blueprint unit
B0010) and the quadrupole `𝔐(f) = ∫₀^∞ r³f₂(r)dr` (`eq:st18-t00009`, line 701), which enters
the Mellin coupling `𝓙` of G4 (`eq:st18-t00017`, lines 766–772, unit B0085). The manuscript
uses without comment that `𝔐` is defined and bounded on `X_G` (Cauchy–Schwarz against the
Gaussian weight, cf. the docstring of `Blueprint/Construction/Planar.lean`).

Main declarations (namespace `UnforcedLeray.Cons.C01`), for the blueprint's
`Blueprint.Planar.MemXG`, `gaussianNorm`, `quadrupole`:
* `MemXG.sub`, `MemXG.const_mul`: `X_G` is a vector space;
* `integrableOn_moment`: `r³f ∈ L¹(0,∞)` for `f ∈ X_G` (the clause `moment_integrable`);
* `norm_quadrupole_le`: `‖𝔐(f)‖ ≤ K_𝔐 ‖f‖_{X_G}` with `K_𝔐 = (1 + ∫ r⁵G(r)dr)/2`;
* `quadrupole_sub`, `quadrupole_const_mul`: linearity.

The proof is the pointwise inequality `r³|f| ≤ (t/2)|f|²G⁻¹r + (1/(2t)) r⁵G` (`t > 0`),
integrated and optimized in `t`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Cons.C01

open Blueprint.Planar

theorem continuous_gaussianWeightInv' : Continuous gaussianWeightInv := by
  unfold gaussianWeightInv
  fun_prop

theorem gaussianWeightInv_pos (r : ℝ) : 0 < gaussianWeightInv r := by
  unfold gaussianWeightInv
  positivity

/-- `x^k e^{-x²/4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_gauss_quarter (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2 / 4))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := (k : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]
  congr 2
  ring

/-- `r⁵G(r) = r⁵/G⁻¹(r)` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_five_div_weight :
    IntegrableOn (fun r : ℝ => r ^ 5 / gaussianWeightInv r) (Ioi 0) := by
  refine IntegrableOn.congr_fun ((integrableOn_pow_mul_gauss_quarter 5).const_mul (4 * Real.pi)⁻¹)
    (fun r _ => ?_) measurableSet_Ioi
  simp only [gaussianWeightInv]
  rw [Real.exp_neg]
  field_simp

/-- The constant `∫₀^∞ r⁵G(r) dr`. -/
def momentWeight : ℝ := ∫ r in Ioi (0 : ℝ), r ^ 5 / gaussianWeightInv r

theorem momentWeight_nonneg : 0 ≤ momentWeight :=
  setIntegral_nonneg measurableSet_Ioi fun r hr =>
    div_nonneg (pow_nonneg (le_of_lt hr) 5) (gaussianWeightInv_pos r).le

/-- The bound `K_𝔐 = (1 + ∫ r⁵G)/2` of `norm_quadrupole_le`. -/
def quadrupoleBound : ℝ := (1 + momentWeight) / 2

theorem quadrupoleBound_pos : 0 < quadrupoleBound := by
  unfold quadrupoleBound
  linarith [momentWeight_nonneg]

/-- The elementary inequality `z ≤ (t/2)X + (1/(2t))Y` when `z² = XY`, `X, Y, z ≥ 0`, `t > 0`. -/
theorem le_of_sq_eq_mul {X Y z t : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hz : 0 ≤ z)
    (hzXY : z ^ 2 = X * Y) (ht : 0 < t) : z ≤ t / 2 * X + 1 / (2 * t) * Y := by
  have key : 2 * t * z ≤ t ^ 2 * X + Y := by
    rcases hX.lt_or_eq with hXp | hX0
    · have h1 : X * (2 * t * z) ≤ X * (t ^ 2 * X + Y) := by
        nlinarith [sq_nonneg (t * X - z), hzXY]
      exact le_of_mul_le_mul_left h1 hXp
    · subst hX0
      have : z = 0 := by
        have : z ^ 2 = 0 := by rw [hzXY]; ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      subst this
      nlinarith
  have e : t / 2 * X + 1 / (2 * t) * Y = (t ^ 2 * X + Y) / (2 * t) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

namespace MemXGLemmas

variable {f g : Profile}

theorem aestronglyMeasurable_integrand {f : Profile}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (fun r : ℝ => ‖f r‖ ^ 2 * gaussianWeightInv r * r)
      (volume.restrict (Ioi (0 : ℝ))) :=
  ((hf.norm.pow 2).mul continuous_gaussianWeightInv'.aestronglyMeasurable).mul
    continuous_id.aestronglyMeasurable

end MemXGLemmas

open MemXGLemmas

/-- `X_G` is closed under differences. -/
theorem MemXG.sub {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    MemXG (fun r => f r - g r) := by
  refine ⟨hf.measurable.sub hg.measurable, ?_⟩
  refine ((hf.integrable.const_mul 2).add (hg.integrable.const_mul 2)).mono'
    (aestronglyMeasurable_integrand (hf.measurable.sub hg.measurable)) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr
  have hw := gaussianWeightInv_pos r
  have hnn : 0 ≤ ‖f r - g r‖ ^ 2 * gaussianWeightInv r * r := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have h1 : ‖f r - g r‖ ≤ ‖f r‖ + ‖g r‖ := norm_sub_le _ _
  have h2 : ‖f r - g r‖ ^ 2 ≤ 2 * ‖f r‖ ^ 2 + 2 * ‖g r‖ ^ 2 := by
    nlinarith [norm_nonneg (f r - g r), norm_nonneg (f r), norm_nonneg (g r),
      sq_nonneg (‖f r‖ - ‖g r‖)]
  have hwr : 0 ≤ gaussianWeightInv r * r := by positivity
  calc ‖f r - g r‖ ^ 2 * gaussianWeightInv r * r
      = ‖f r - g r‖ ^ 2 * (gaussianWeightInv r * r) := by ring
    _ ≤ (2 * ‖f r‖ ^ 2 + 2 * ‖g r‖ ^ 2) * (gaussianWeightInv r * r) :=
        mul_le_mul_of_nonneg_right h2 hwr
    _ = 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) +
        2 * (‖g r‖ ^ 2 * gaussianWeightInv r * r) := by ring

/-- `X_G` is closed under scalar multiples. -/
theorem MemXG.const_mul {f : Profile} (a : ℂ) (hf : MemXG f) : MemXG (fun r => a * f r) := by
  refine ⟨hf.measurable.const_mul a, ?_⟩
  refine IntegrableOn.congr_fun (hf.integrable.const_mul (‖a‖ ^ 2)) (fun r _ => ?_)
    measurableSet_Ioi
  simp only [norm_mul]
  ring

/-- The pointwise inequality `r³|f| ≤ (t/2)|f|²G⁻¹r + (1/(2t))r⁵G`, `r, t > 0`. -/
theorem moment_pointwise (f : Profile) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    r ^ 3 * ‖f r‖ ≤ t / 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) +
      1 / (2 * t) * (r ^ 5 / gaussianWeightInv r) := by
  have hw := gaussianWeightInv_pos r
  refine le_of_sq_eq_mul (by positivity) (by positivity) (by positivity) ?_ ht
  field_simp

/-- **The clause `moment_integrable`**: `r³f ∈ L¹(0, ∞)` for `f ∈ X_G`. -/
theorem integrableOn_moment {f : Profile} (hf : MemXG f) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * f r) (Ioi 0) := by
  have hb : IntegrableOn (fun r : ℝ => 1 / 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) +
      1 / (2 * 1) * (r ^ 5 / gaussianWeightInv r)) (Ioi 0) :=
    (hf.integrable.const_mul _).add (integrableOn_pow_five_div_weight.const_mul _)
  refine hb.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.pow 3).aestronglyMeasurable).mul hf.measurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact moment_pointwise f hr0 one_pos

/-- `∫ r³|f| ≤ (t/2)‖f‖²_{X_G} + (1/(2t))∫ r⁵G` for every `t > 0`. -/
theorem integral_moment_le {f : Profile} (hf : MemXG f) {t : ℝ} (ht : 0 < t) :
    ∫ r in Ioi (0 : ℝ), r ^ 3 * ‖f r‖ ≤
      t / 2 * (∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * gaussianWeightInv r * r) +
        1 / (2 * t) * momentWeight := by
  have hint : IntegrableOn (fun r : ℝ => r ^ 3 * ‖f r‖) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_moment hf).norm (fun r hr => ?_) measurableSet_Ioi
    have hr0 : (0 : ℝ) < r := hr
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hb : IntegrableOn (fun r : ℝ => t / 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) +
      1 / (2 * t) * (r ^ 5 / gaussianWeightInv r)) (Ioi 0) :=
    (hf.integrable.const_mul _).add (integrableOn_pow_five_div_weight.const_mul _)
  calc ∫ r in Ioi (0 : ℝ), r ^ 3 * ‖f r‖
      ≤ ∫ r in Ioi (0 : ℝ), (t / 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) +
          1 / (2 * t) * (r ^ 5 / gaussianWeightInv r)) :=
        setIntegral_mono_on hint hb measurableSet_Ioi fun r hr => moment_pointwise f hr ht
    _ = t / 2 * (∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * gaussianWeightInv r * r) +
          1 / (2 * t) * momentWeight := by
        rw [integral_add (hf.integrable.const_mul _) (integrableOn_pow_five_div_weight.const_mul _),
          integral_const_mul, integral_const_mul, momentWeight]

/-- `‖𝔐(f)‖ ≤ ∫ r³|f|`. -/
theorem norm_quadrupole_le_integral (f : Profile) :
    ‖quadrupole f‖ ≤ ∫ r in Ioi (0 : ℝ), r ^ 3 * ‖f r‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]

/-- `‖𝔐(f)‖ ≤ (t/2)‖f‖²_{X_G} + (1/(2t))∫ r⁵G` for every `t > 0`. -/
theorem norm_quadrupole_le_of_pos {f : Profile} (hf : MemXG f) {t : ℝ} (ht : 0 < t) :
    ‖quadrupole f‖ ≤ t / 2 * gaussianNorm f ^ 2 + 1 / (2 * t) * momentWeight := by
  have hA : 0 ≤ ∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * gaussianWeightInv r * r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr => by
      have := gaussianWeightInv_pos r
      have hr0 : (0 : ℝ) < r := hr
      positivity
  rw [gaussianNorm, Real.sq_sqrt hA]
  exact (norm_quadrupole_le_integral f).trans (integral_moment_le hf ht)

/-- **`𝔐` is bounded on `X_G`**: `‖𝔐(f)‖ ≤ K_𝔐 ‖f‖_{X_G}`. -/
theorem norm_quadrupole_le {f : Profile} (hf : MemXG f) :
    ‖quadrupole f‖ ≤ quadrupoleBound * gaussianNorm f := by
  set N := gaussianNorm f with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set B := momentWeight with hB
  have hB0 : 0 ≤ B := momentWeight_nonneg
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := 2 * δ / (B + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hNε : 0 < N + ε := by linarith
  have h := norm_quadrupole_le_of_pos hf (t := 1 / (N + ε)) (by positivity)
  have h1 : 1 / (N + ε) / 2 * N ^ 2 ≤ N / 2 := by
    rw [div_div, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 1 / (2 * (1 / (N + ε))) * B = B * N / 2 + B * ε / 2 := by
    field_simp
  have h3 : B * ε / 2 ≤ δ := by
    rw [hε]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  unfold quadrupoleBound
  rw [← hB]
  nlinarith

/-- `𝔐(f - g) = 𝔐(f) - 𝔐(g)` on `X_G`. -/
theorem quadrupole_sub {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    quadrupole (fun r => f r - g r) = quadrupole f - quadrupole g := by
  unfold quadrupole
  rw [← integral_sub (integrableOn_moment hf) (integrableOn_moment hg)]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [mul_sub]

/-- `𝔐(af) = a𝔐(f)`. -/
theorem quadrupole_const_mul (a : ℂ) (f : Profile) :
    quadrupole (fun r => a * f r) = a * quadrupole f := by
  unfold quadrupole
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

end UnforcedLeray.Cons.C01
