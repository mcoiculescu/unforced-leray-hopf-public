import UnforcedLeray.GaussianPotentialSup
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Concrete Gaussian Sturm quadratic-form estimates

The form uses the manuscript's actual log-radius potential. It is written on
pairs `(f,g)` of L² functions so that a weak Sobolev graph can supply `g=f'`;
no assertion that an arbitrary pair is a derivative pair is made here.
The estimates prove the direct high-angular-mode coercivity from the actual
potential bound, with all integrals guarded by L² membership. They do not
supply a negative eigenfunction or an unbounded spectral theorem.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace UnforcedLeray.Sturm
open GaussianPotential

/-- The actual potential is positive on its radial parameter domain. -/
theorem W_pos_of_radial_domain {y : ℝ} (hy : -2 < y) : 0 < W y := by
  by_cases hzero : y = 0
  · simp [hzero]
  · simp only [W, hzero, ↓reduceIte]
    have hfac : 0 < 4 * (y + 2) := by nlinarith
    rcases lt_or_gt_of_ne hzero with hneg | hpos
    · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hfac hneg)
        (sub_neg.mpr (Real.exp_lt_one_iff.mpr hneg))
    · exact div_pos (mul_pos hfac hpos)
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr hpos))

theorem Wlog_pos (t : ℝ) : 0 < Wlog t := by
  apply W_pos_of_radial_domain
  have := Real.exp_pos (2 * t)
  linarith

theorem measurable_W : Measurable W := by
  unfold W
  exact Measurable.ite (by measurability) measurable_const (by fun_prop)

theorem measurable_Wlog : Measurable Wlog := by
  exact measurable_W.comp (by fun_prop)

theorem norm_Wlog_le_eight (t : ℝ) : ‖Wlog t‖ ≤ 8 := by
  rw [Real.norm_eq_abs, abs_of_pos (Wlog_pos t)]
  exact Wlog_le_eight t

/-- The potential term is an actual convergent integral for every L² input. -/
theorem integrable_potential {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Integrable (fun t => Wlog t * f t ^ 2) := by
  exact hf.integrable_sq.bdd_mul measurable_Wlog.aestronglyMeasurable
    (Filter.Eventually.of_forall norm_Wlog_le_eight)

/-- `g` is the derivative component supplied by a Sobolev graph. -/
def quadraticForm (n : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ t, g t ^ 2 + (n ^ 2 - Wlog t) * f t ^ 2

def freeEnergy (n : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ t, g t ^ 2 + n ^ 2 * f t ^ 2

theorem integrable_form {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (n : ℝ) :
    Integrable (fun t => g t ^ 2 + (n ^ 2 - Wlog t) * f t ^ 2) := by
  simp_rw [sub_mul, ← add_sub_assoc]
  exact (hg.integrable_sq.add (hf.integrable_sq.const_mul (n ^ 2))).sub
    (integrable_potential hf)

theorem quadraticForm_expansion {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (n : ℝ) :
    quadraticForm n f g = (∫ t, g t ^ 2) + n ^ 2 * (∫ t, f t ^ 2) -
      (∫ t, Wlog t * f t ^ 2) := by
  unfold quadraticForm
  simp_rw [sub_mul, ← add_sub_assoc]
  have hs := integral_sub (hg.integrable_sq.add (hf.integrable_sq.const_mul (n ^ 2)))
    (integrable_potential hf)
  simp only [Pi.add_apply] at hs
  rw [hs, integral_add hg.integrable_sq
    (hf.integrable_sq.const_mul (n ^ 2)), integral_const_mul]

theorem freeEnergy_expansion {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (n : ℝ) :
    freeEnergy n f g = (∫ t, g t ^ 2) + n ^ 2 * (∫ t, f t ^ 2) := by
  unfold freeEnergy
  rw [integral_add hg.integrable_sq (hf.integrable_sq.const_mul (n ^ 2)), integral_const_mul]

/-- Boundedness of the potential is integrated with explicit convergence. -/
theorem potential_energy_le_eight {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    (∫ t, Wlog t * f t ^ 2) ≤ 8 * (∫ t, f t ^ 2) := by
  rw [← integral_const_mul]
  exact integral_mono (integrable_potential hf) (hf.integrable_sq.const_mul 8)
    (fun t => mul_le_mul_of_nonneg_right (Wlog_le_eight t) (sq_nonneg _))

theorem quadraticForm_lower_bound {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (n : ℝ) :
    (∫ t, g t ^ 2) + (n ^ 2 - 8) * (∫ t, f t ^ 2) ≤ quadraticForm n f g := by
  rw [quadraticForm_expansion hf hg]
  have h := potential_energy_le_eight hf
  nlinarith

/-- The manuscript's direct positivity for angular indices at least three,
with the stronger exact potential constant eight. -/
theorem quadraticForm_coercive {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {n : ℝ} (hn : 3 ≤ n) :
    (1 - 8 / n ^ 2) * freeEnergy n f g ≤ quadraticForm n f g := by
  have hn0 : n ^ 2 ≠ 0 := by positivity
  have hG : 0 ≤ ∫ t, g t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have hratio : 0 ≤ (8 : ℝ) / n ^ 2 := by positivity
  rw [freeEnergy_expansion hf hg]
  calc
    (1 - 8 / n ^ 2) * ((∫ t, g t ^ 2) + n ^ 2 * (∫ t, f t ^ 2)) =
      ((∫ t, g t ^ 2) + (n ^ 2 - 8) * (∫ t, f t ^ 2)) -
        (8 / n ^ 2) * (∫ t, g t ^ 2) := by field_simp; ring
    _ ≤ (∫ t, g t ^ 2) + (n ^ 2 - 8) * (∫ t, f t ^ 2) :=
      sub_le_self _ (mul_nonneg hratio hG)
    _ ≤ quadraticForm n f g := quadraticForm_lower_bound hf hg n

theorem coercivity_constant_pos {n : ℝ} (hn : 3 ≤ n) : 0 < 1 - 8 / n ^ 2 := by
  have hn2 : 8 < n ^ 2 := by nlinarith
  have hdiv : (8 : ℝ) / n ^ 2 < 1 := (div_lt_one (by nlinarith)).2 hn2
  linarith

/-- A genuinely nonzero L² function has positive squared integral. -/
theorem integral_sq_pos {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hzero : ¬ f =ᵐ[volume] 0) : 0 < ∫ t, f t ^ 2 := by
  have hnonneg : 0 ≤ ∫ t, f t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  apply lt_of_le_of_ne hnonneg
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (f t))
    hf.integrable_sq).mp hz.symm
  apply hzero
  filter_upwards [hae] with t ht
  simpa only [Pi.zero_apply, sq_eq_zero_iff] using ht

/-- No nonpositive quadratic direction exists in any angular mode n≥3. -/
theorem quadraticForm_pos {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {n : ℝ} (hn : 3 ≤ n)
    (hzero : ¬ f =ᵐ[volume] 0) : 0 < quadraticForm n f g := by
  have hF := integral_sq_pos hf hzero
  have hG : 0 ≤ ∫ t, g t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have hn2 : 0 < n ^ 2 - 8 := by nlinarith
  have hbound := quadraticForm_lower_bound hf hg n
  have hpos := mul_pos hn2 hF
  linarith

end UnforcedLeray.Sturm
