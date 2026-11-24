import UnforcedLeray.Analysis.Rayleigh.Evans.Coefficients
import NonUniqueEuler.P.Infra.ODE.Existence
import NonUniqueEuler.P.Infra.ODE.Smooth
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Actual normalized Gaussian Rayleigh solutions and the Evans endpoint value

For every upper-half-plane spectral speed, the coefficient is genuinely
continuous and smooth on the real log-radius line. The reused generic ODE
existence theorem therefore supplies an actual solution, with initial data
F(a)=0 and F'(a)=1. No unstable Evans zero is asserted here.
-/

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.Rayleigh.Evans
open NonUniqueEuler.LinODE

/-- The actual Gaussian Rayleigh solution pair with data (0,1) at a. -/
def normalizedPair (α a : ℝ) (c : ℂ) (t : ℝ) : ℂ × ℂ :=
  sol (fun s => rayleighPotential α s c) a (0, 1) t

def normalizedF (α a : ℝ) (c : ℂ) (t : ℝ) : ℂ :=
  (normalizedPair α a c t).1

def normalizedDerivative (α a : ℝ) (c : ℂ) (t : ℝ) : ℂ :=
  (normalizedPair α a c t).2

/-- The Evans endpoint determinant for the finite log-annulus [a,b]. -/
def evansFunction (α a b : ℝ) (c : ℂ) : ℂ := normalizedF α a c b

theorem normalizedPair_spec (α a : ℝ) {c : ℂ} (hc : 0 < c.im) :
    IsSolOn (fun t => rayleighPotential α t c) univ
      (normalizedF α a c) (normalizedDerivative α a c) ∧
      normalizedPair α a c a = (0, 1) :=
  sol_spec (continuous_rayleighPotential α hc) a (0, 1)

theorem normalizedF_initial (α a : ℝ) {c : ℂ} (hc : 0 < c.im) :
    normalizedF α a c a = 0 :=
  congrArg Prod.fst (normalizedPair_spec α a hc).2

theorem normalizedDerivative_initial (α a : ℝ) {c : ℂ} (hc : 0 < c.im) :
    normalizedDerivative α a c a = 1 :=
  congrArg Prod.snd (normalizedPair_spec α a hc).2

theorem hasDerivAt_normalizedF (α a : ℝ) {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    HasDerivAt (normalizedF α a c) (normalizedDerivative α a c t) t :=
  (isSolOn_univ_iff.mp (normalizedPair_spec α a hc).1).1 t

theorem hasDerivAt_normalizedDerivative (α a : ℝ) {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    HasDerivAt (normalizedDerivative α a c)
      (rayleighPotential α t c * normalizedF α a c t) t :=
  (isSolOn_univ_iff.mp (normalizedPair_spec α a hc).1).2 t

theorem normalizedF_smooth (α a : ℝ) {c : ℂ} (hc : 0 < c.im) :
    ContDiff ℝ ∞ (normalizedF α a c) :=
  (IsSolOn.contDiff (contDiff_rayleighPotential α hc) (normalizedPair_spec α a hc).1).1

theorem normalizedDerivative_smooth (α a : ℝ) {c : ℂ} (hc : 0 < c.im) :
    ContDiff ℝ ∞ (normalizedDerivative α a c) :=
  (IsSolOn.contDiff (contDiff_rayleighPotential α hc) (normalizedPair_spec α a hc).1).2.1

theorem deriv_normalizedF (α a : ℝ) {c : ℂ} (hc : 0 < c.im) :
    deriv (normalizedF α a c) = normalizedDerivative α a c :=
  funext fun t => (hasDerivAt_normalizedF α a hc t).deriv

theorem deriv_deriv_normalizedF (α a : ℝ) {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    deriv (deriv (normalizedF α a c)) t =
      rayleighPotential α t c * normalizedF α a c t := by
  rw [deriv_normalizedF α a hc]
  exact (hasDerivAt_normalizedDerivative α a hc t).deriv

/-- The genuine undivided Gaussian Rayleigh equation holds pointwise on all log radii. -/
theorem normalizedF_rayleigh_equation (α a : ℝ) {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    ((Sturm.neutralOmega t : ℂ) - c) *
      (deriv (deriv (normalizedF α a c)) t - (α : ℂ) ^ 2 * normalizedF α a c t) -
        (gaussianRayleighCoefficient t : ℂ) * normalizedF α a c t = 0 := by
  rw [deriv_deriv_normalizedF α a hc]
  unfold rayleighPotential
  have hd := rayleigh_denominator_ne_zero hc t
  field_simp
  ring

/-- The normalized solution is nonzero on every interval of positive length starting at a. -/
theorem normalizedF_nonzero_on_interval (α : ℝ) {a b : ℝ} (hab : a < b)
    {c : ℂ} (hc : 0 < c.im) : ∃ t ∈ Icc a b, normalizedF α a c t ≠ 0 := by
  by_contra h
  push Not at h
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hu := uniqueDiffOn_Icc hab a ha
  have h1 : HasDerivWithinAt (normalizedF α a c) 1 (Icc a b) a := by
    simpa only [normalizedDerivative_initial α a hc] using
      (hasDerivAt_normalizedF α a hc a).hasDerivWithinAt (s := Icc a b)
  have h0 : HasDerivWithinAt (normalizedF α a c) 0 (Icc a b) a :=
    (hasDerivWithinAt_const a (Icc a b) (0 : ℂ)).congr_of_mem h ha
  exact one_ne_zero ((h1.derivWithin hu).symm.trans (h0.derivWithin hu))

/-- An Evans zero at angular index two supplies the actual smooth annular mode used by
our energy estimates; it does not supply existence of such a zero. -/
theorem gaussianAnnularMode_of_evans_zero {a b : ℝ} (hab : a < b) {c : ℂ}
    (hc : 0 < c.im) (he : evansFunction 2 a b c = 0) :
    GaussianAnnularMode c (normalizedF 2 a c) a b := by
  refine ⟨hab.le, hc, (normalizedF_smooth 2 a hc).of_le (by simp),
    normalizedF_initial 2 a hc, he, ?_⟩
  intro t _
  have h := normalizedF_rayleigh_equation 2 a hc t
  norm_num at h
  exact h

end UnforcedLeray.Rayleigh.Evans
