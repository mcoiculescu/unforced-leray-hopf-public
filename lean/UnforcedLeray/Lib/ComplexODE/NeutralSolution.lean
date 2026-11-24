import UnforcedLeray.Analysis.Rayleigh.Evans.CriticalCoefficientLimit
import UnforcedLeray.Analysis.Rayleigh.Evans.Solution
import UnforcedLeray.Analysis.Rayleigh.Evans.Wronskian
import NonUniqueEuler.P.Infra.ODE.Uniqueness

/-!
# Completed neutral solution (copy of two drafts; Wave 1 block 1H part 3, INF18 O1 input)

Verbatim copy, for compilation inside `Lib/ComplexODE`, of the uncompiled drafts


(2026-10-26). The drafts themselves are not edited. Do not import those drafts together with
this module: the declarations have the same names.

The neutral Rayleigh equation of `paper/main.tex` lines 1001--1011 (eq. st18-t00032, B0034)
in logarithmic radius is `F'' = (α² - W) F`; `neutralNormalizedF α a` is its solution with
`F(a) = 0`, `F'(a) = 1`, and `neutralEvansFunction α a b = F(b)`.
-/

set_option autoImplicit false

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.Rayleigh.Evans
open NonUniqueEuler.LinODE

def neutralNormalizedPair (α a t : ℝ) : ℂ × ℂ :=
  sol (neutralPotential α) a (0, 1) t

def neutralNormalizedF (α a t : ℝ) : ℂ := (neutralNormalizedPair α a t).1

def neutralNormalizedDerivative (α a t : ℝ) : ℂ := (neutralNormalizedPair α a t).2

def neutralEvansFunction (α a b : ℝ) : ℂ := neutralNormalizedF α a b

theorem neutralNormalizedPair_spec (α a : ℝ) :
    IsSolOn (neutralPotential α) univ
      (neutralNormalizedF α a) (neutralNormalizedDerivative α a) ∧
      neutralNormalizedPair α a a = (0, 1) :=
  sol_spec (continuous_neutralPotential α) a (0, 1)

@[simp] theorem neutralNormalizedF_initial (α a : ℝ) : neutralNormalizedF α a a = 0 :=
  congrArg Prod.fst (neutralNormalizedPair_spec α a).2

@[simp] theorem neutralNormalizedDerivative_initial (α a : ℝ) :
    neutralNormalizedDerivative α a a = 1 :=
  congrArg Prod.snd (neutralNormalizedPair_spec α a).2

theorem hasDerivAt_neutralNormalizedF (α a t : ℝ) :
    HasDerivAt (neutralNormalizedF α a) (neutralNormalizedDerivative α a t) t :=
  (isSolOn_univ_iff.mp (neutralNormalizedPair_spec α a).1).1 t

theorem hasDerivAt_neutralNormalizedDerivative (α a t : ℝ) :
    HasDerivAt (neutralNormalizedDerivative α a)
      (neutralPotential α t * neutralNormalizedF α a t) t :=
  (isSolOn_univ_iff.mp (neutralNormalizedPair_spec α a).1).2 t

theorem neutralNormalizedF_smooth (α a : ℝ) : ContDiff ℝ ∞ (neutralNormalizedF α a) :=
  (IsSolOn.contDiff (contDiff_neutralPotential α) (neutralNormalizedPair_spec α a).1).1

theorem neutralNormalizedDerivative_smooth (α a : ℝ) :
    ContDiff ℝ ∞ (neutralNormalizedDerivative α a) :=
  (IsSolOn.contDiff (contDiff_neutralPotential α) (neutralNormalizedPair_spec α a).1).2.1

theorem deriv_neutralNormalizedF (α a : ℝ) :
    deriv (neutralNormalizedF α a) = neutralNormalizedDerivative α a :=
  funext fun t => (hasDerivAt_neutralNormalizedF α a t).deriv

theorem deriv_deriv_neutralNormalizedF (α a t : ℝ) :
    deriv (deriv (neutralNormalizedF α a)) t =
      neutralPotential α t * neutralNormalizedF α a t := by
  rw [deriv_neutralNormalizedF]
  exact (hasDerivAt_neutralNormalizedDerivative α a t).deriv

/-- A normalized neutral solution cannot have both value and slope zero anywhere. -/
theorem neutralNormalizedDerivative_ne_zero_of_value_zero (α a b : ℝ)
    (hb : neutralNormalizedF α a b = 0) : neutralNormalizedDerivative α a b ≠ 0 := by
  intro hb'
  have h := IsSolOn.eqOn_zero ordConnected_univ (continuous_neutralPotential α).continuousOn
    (neutralNormalizedPair_spec α a).1 (mem_univ b) hb hb'
  have hz := h.2 (mem_univ a)
  simp at hz

/-- The actual Evans endpoint satisfies the Wronskian perturbation formula
at any zero of the independently completed neutral equation. -/
theorem evansFunction_mul_neutralDerivative (α β a b : ℝ) {c : ℂ} (hc : 0 < c.im)
    (hb : neutralEvansFunction α a b = 0) :
    evansFunction β a b c * neutralNormalizedDerivative α a b =
      -(∫ t in a..b, (rayleighPotential β t c - neutralPotential α t) *
        neutralNormalizedF α a t * normalizedF β a c t) :=
  endpoint_wronskian_variation (continuous_neutralPotential α)
    (continuous_rayleighPotential β hc) (neutralNormalizedPair_spec α a).1
    (normalizedPair_spec β a hc).1 (neutralNormalizedF_initial α a)
    (normalizedF_initial β a hc) hb

end UnforcedLeray.Rayleigh.Evans

noncomputable section
open Set
namespace UnforcedLeray.Rayleigh.Evans
open NonUniqueEuler.LinODE

/-- The completed neutral coefficient is actually real. -/
@[simp] theorem conj_neutralPotential (α t : ℝ) :
    star (neutralPotential α t) = neutralPotential α t := by
  simp [neutralPotential]

theorem neutralNormalized_conj (α a : ℝ) :
    (∀ t, star (neutralNormalizedF α a t) = neutralNormalizedF α a t) ∧
    (∀ t, star (neutralNormalizedDerivative α a t) = neutralNormalizedDerivative α a t) := by
  have hconj : IsSolOn (neutralPotential α) univ
      (fun t => star (neutralNormalizedF α a t))
      (fun t => star (neutralNormalizedDerivative α a t)) := by
    apply isSolOn_univ_iff.mpr
    constructor
    · intro t
      exact (hasDerivAt_neutralNormalizedF α a t).star
    · intro t
      have hd := (hasDerivAt_neutralNormalizedDerivative α a t).star
      rw [star_mul', conj_neutralPotential] at hd
      exact hd
  have h := IsSolOn.eqOn ordConnected_univ (continuous_neutralPotential α).continuousOn
    hconj (neutralNormalizedPair_spec α a).1 (mem_univ a) (by simp) (by simp)
  exact ⟨fun t => h.1 (mem_univ t), fun t => h.2 (mem_univ t)⟩

@[simp] theorem neutralNormalizedF_im (α a t : ℝ) :
    (neutralNormalizedF α a t).im = 0 :=
  Complex.conj_eq_iff_im.mp ((neutralNormalized_conj α a).1 t)

@[simp] theorem neutralNormalizedDerivative_im (α a t : ℝ) :
    (neutralNormalizedDerivative α a t).im = 0 :=
  Complex.conj_eq_iff_im.mp ((neutralNormalized_conj α a).2 t)

theorem neutralNormalizedF_eq_ofReal_re (α a t : ℝ) :
    neutralNormalizedF α a t = ((neutralNormalizedF α a t).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp ((neutralNormalized_conj α a).1 t)).symm

theorem neutralNormalizedF_nonzero_on_interval (α : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Icc a b, neutralNormalizedF α a t ≠ 0 := by
  by_contra h
  push Not at h
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hu := uniqueDiffOn_Icc hab a ha
  have h1 : HasDerivWithinAt (neutralNormalizedF α a) 1 (Icc a b) a := by
    simpa only [neutralNormalizedDerivative_initial] using
      (hasDerivAt_neutralNormalizedF α a a).hasDerivWithinAt (s := Icc a b)
  have h0 : HasDerivWithinAt (neutralNormalizedF α a) 0 (Icc a b) a :=
    (hasDerivWithinAt_const a (Icc a b) (0 : ℂ)).congr_of_mem h ha
  exact one_ne_zero ((h1.derivWithin hu).symm.trans (h0.derivWithin hu))

/-- The real square of the actual neutral solution has strictly positive mass. -/
theorem neutralNormalized_real_mass_pos (α : ℝ) {a b : ℝ} (hab : a < b) :
    0 < ∫ t in a..b, (neutralNormalizedF α a t).re ^ 2 := by
  apply intervalIntegral.integral_pos hab
  · exact ((Complex.continuous_re.comp (neutralNormalizedF_smooth α a).continuous).pow 2).continuousOn
  · intro t _
    exact sq_nonneg _
  · obtain ⟨t, ht, hne⟩ := neutralNormalizedF_nonzero_on_interval α hab
    refine ⟨t, ht, sq_pos_of_ne_zero ?_⟩
    intro hr
    apply hne
    rw [neutralNormalizedF_eq_ofReal_re α a t, hr]
    rfl

end UnforcedLeray.Rayleigh.Evans
