import UnforcedLeray.Analysis.Sturm.QuadraticForm
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
# The codimension-one exclusion of a neutral mode

All forms below are the actual Gaussian Sturm integrals on the real line.
The linear-combination calculation keeps every integrability obligation.
The final algebraic argument applies the trace-zero coercivity theorem to
an explicit combination, rather than assuming a spectral-index statement.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace UnforcedLeray.Sturm
open GaussianPotential

private theorem integrable_cross_form {f df g dg : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hdf : MemLp df 2 volume)
    (hg : MemLp g 2 volume) (hdg : MemLp dg 2 volume) (n : ℝ) :
    Integrable (fun t => df t * dg t + (n ^ 2 - Wlog t) * (f t * g t)) := by
  have hi := hf.integrable_mul hg
  have hw : Integrable (fun t => Wlog t * (f t * g t)) :=
    hi.bdd_mul measurable_Wlog.aestronglyMeasurable
      (Filter.Eventually.of_forall norm_Wlog_le_eight)
  have hn : Integrable (fun t => n ^ 2 * (f t * g t)) := hi.const_mul _
  simpa only [Pi.mul_apply, Pi.sub_apply, sub_mul] using (hdf.integrable_mul hdg).fun_add (hn.sub hw)

/-- Exact polarization on genuine L² function/derivative pairs. -/
theorem quadraticForm_linear_combination {f df g dg : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hdf : MemLp df 2 volume)
    (hg : MemLp g 2 volume) (hdg : MemLp dg 2 volume) (n a b : ℝ) :
    quadraticForm n (fun t => a * f t + b * g t) (fun t => a * df t + b * dg t) =
      a ^ 2 * quadraticForm n f df + b ^ 2 * quadraticForm n g dg +
        (2 * a * b) * (∫ t, df t * dg t + (n ^ 2 - Wlog t) * (f t * g t)) := by
  have h1 := (integrable_form hf hdf n).const_mul (a ^ 2)
  have h2 := (integrable_form hg hdg n).const_mul (b ^ 2)
  have h3 := (integrable_cross_form hf hdf hg hdg n).const_mul (2 * a * b)
  unfold quadraticForm
  have he (t : ℝ) :
      (a * df t + b * dg t) ^ 2 + (n ^ 2 - Wlog t) * (a * f t + b * g t) ^ 2 =
      a ^ 2 * (df t ^ 2 + (n ^ 2 - Wlog t) * f t ^ 2) +
      b ^ 2 * (dg t ^ 2 + (n ^ 2 - Wlog t) * g t ^ 2) +
      (2 * a * b) * (df t * dg t + (n ^ 2 - Wlog t) * (f t * g t)) := by ring
  simp_rw [he]
  rw [integral_add (h1.fun_add h2) h3, integral_add h1 h2]
  simp only [integral_const_mul]

/-- The actual derivative of a scalar linear combination. -/
theorem deriv_real_linear_combination {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (a b : ℝ) :
    deriv (fun t => a * f t + b * g t) = fun t => a * deriv f t + b * deriv g t := by
  funext t
  exact (((hf.differentiable (by simp) t).hasDerivAt.const_mul a).add
    ((hg.differentiable (by simp) t).hasDerivAt.const_mul b)).deriv

/-- A negative direction and an orthogonal zero-energy direction are incompatible
with positive coercivity on the trace-zero subspace, unless the latter is zero.
The coercivity assumption will be discharged by the explicit neutral-profile
factorization and cutoffs. It is kept visible here to separate the algebra. -/
theorem neutral_zero_of_trace_coercivity {n a κ : ℝ} (hκ : 0 < κ)
    (hcoerc : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → MemLp F 2 volume →
      MemLp (deriv F) 2 volume → F a = 0 →
      κ * (∫ t, F t ^ 2) ≤ quadraticForm n F (deriv F))
    {f g : ℝ → ℝ} (hfc : ContDiff ℝ 1 f) (hgc : ContDiff ℝ 1 g)
    (hf : MemLp f 2 volume) (hdf : MemLp (deriv f) 2 volume)
    (hg : MemLp g 2 volume) (hdg : MemLp (deriv g) 2 volume)
    (hfneg : quadraticForm n f (deriv f) < 0)
    (hgzero : quadraticForm n g (deriv g) = 0)
    (hcross : (∫ t, deriv f t * deriv g t +
      (n ^ 2 - Wlog t) * (f t * g t)) = 0) : g =ᵐ[volume] 0 := by
  let F : ℝ → ℝ := fun t => -g a * f t + f a * g t
  have hFc : ContDiff ℝ 1 F := by dsimp [F]; fun_prop
  have hF : MemLp F 2 volume := (hf.const_mul (-g a)).add (hg.const_mul (f a))
  have hFd : deriv F = fun t => -g a * deriv f t + f a * deriv g t :=
    deriv_real_linear_combination hfc hgc (-g a) (f a)
  have hDF : MemLp (deriv F) 2 volume := by
    rw [hFd]
    exact (hdf.const_mul (-g a)).add (hdg.const_mul (f a))
  have hFa : F a = 0 := by dsimp [F]; ring
  have hQ : quadraticForm n F (deriv F) = (g a) ^ 2 * quadraticForm n f (deriv f) := by
    rw [hFd]
    dsimp [F]
    rw [quadraticForm_linear_combination hf hdf hg hdg, hgzero, hcross]
    ring
  have hnonneg : 0 ≤ quadraticForm n F (deriv F) := by
    have h := hcoerc F hFc hF hDF hFa
    have hmass : 0 ≤ ∫ t, F t ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
    exact (mul_nonneg hκ.le hmass).trans h
  have hga : g a = 0 := by
    by_contra hne
    have hs : 0 < (g a) ^ 2 := sq_pos_of_ne_zero hne
    have hneg := mul_neg_of_pos_of_neg hs hfneg
    rw [hQ] at hnonneg
    exact (not_lt_of_ge hnonneg) hneg
  have hgmass : (∫ t, g t ^ 2) = 0 := by
    have h := hcoerc g hgc hg hdg hga
    rw [hgzero] at h
    have hnonnegMass : 0 ≤ ∫ t, g t ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
    nlinarith
  have hz := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (g t)) hg.integrable_sq).mp hgmass
  filter_upwards [hz] with t ht
  simpa only [Pi.zero_apply, sq_eq_zero_iff] using ht

end UnforcedLeray.Sturm
