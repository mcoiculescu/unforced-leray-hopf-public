import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Uniform bounds for a continuous periodic mode

The compactness step behind `paper/main.tex`, equation `loc:eq:phase-minimum`.
The positive lower bound is derived from the actual compact range of the mode.
This module does not establish the evolution equation or forward uniqueness
needed to prove that the manuscript's mode never vanishes.
-/

noncomputable section

open Set
open scoped BigOperators

namespace UnforcedLeray.PeriodicMode

variable {E : Type*} [NormedAddCommGroup E]

/-- A continuous path with a nonzero period attains its global minimum and
maximum norm. No finite-dimensional or completeness hypothesis is needed. -/
theorem exists_norm_min_max {f : ℝ → E} {p : ℝ}
    (hp : Function.Periodic f p) (hp0 : p ≠ 0) (hf : Continuous f) :
    ∃ tmin tmax : ℝ, ∀ t : ℝ, ‖f tmin‖ ≤ ‖f t‖ ∧ ‖f t‖ ≤ ‖f tmax‖ := by
  have hcompact : IsCompact (range f) := hp.compact_of_continuous hp0 hf
  have hnonempty : (range f).Nonempty := ⟨f 0, mem_range_self 0⟩
  obtain ⟨xmin, ⟨tmin, rfl⟩, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty continuous_norm.continuousOn
  obtain ⟨xmax, ⟨tmax, rfl⟩, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty continuous_norm.continuousOn
  exact ⟨tmin, tmax, fun t => ⟨hmin (mem_range_self t), hmax (mem_range_self t)⟩⟩

/-- A continuous periodic path which never vanishes has a strictly positive
uniform norm lower bound and a finite upper bound. -/
theorem exists_pos_norm_bounds {f : ℝ → E} {p : ℝ}
    (hp : Function.Periodic f p) (hp0 : p ≠ 0) (hf : Continuous f)
    (hne : ∀ t : ℝ, f t ≠ 0) :
    ∃ m M : ℝ, 0 < m ∧ ∀ t : ℝ, m ≤ ‖f t‖ ∧ ‖f t‖ ≤ M := by
  obtain ⟨tmin, tmax, hbounds⟩ := exists_norm_min_max hp hp0 hf
  exact ⟨‖f tmin‖, ‖f tmax‖, norm_pos_iff.mpr (hne tmin), hbounds⟩

/-- The positive phase minimum used in quantitative mode separation. -/
theorem exists_pos_norm_lower_bound {f : ℝ → E} {p : ℝ}
    (hp : Function.Periodic f p) (hp0 : p ≠ 0) (hf : Continuous f)
    (hne : ∀ t : ℝ, f t ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, m ≤ ‖f t‖ := by
  obtain ⟨m, M, hm, hbounds⟩ := exists_pos_norm_bounds hp hp0 hf hne
  exact ⟨m, hm, fun t => (hbounds t).1⟩

section Oscillatory

variable [NormedSpace ℝ E]

/-- The real oscillatory path determined by the real and imaginary parts of
an eigenvector. -/
def oscillatory (a b : E) (t : ℝ) : E :=
  Real.cos t • a - Real.sin t • b

theorem oscillatory_continuous (a b : E) : Continuous (oscillatory a b) :=
  (Real.continuous_cos.smul continuous_const).sub
    (Real.continuous_sin.smul continuous_const)

theorem oscillatory_periodic (a b : E) :
    Function.Periodic (oscillatory a b) (2 * Real.pi) := by
  intro t
  dsimp only [oscillatory]
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Independence of the two vectors excludes every zero phase: a zero phase
would force both cosine and sine to vanish. -/
theorem oscillatory_ne_zero (a b : E)
    (h : LinearIndependent ℝ ![a, b]) (t : ℝ) : oscillatory a b t ≠ 0 := by
  intro hz
  have hs : ∑ i : Fin 2, (![Real.cos t, -Real.sin t] : Fin 2 → ℝ) i •
      (![a, b] : Fin 2 → E) i = 0 := by
    simpa [oscillatory, Fin.sum_univ_two, neg_smul, sub_eq_add_neg] using hz
  have hcoeff := Fintype.linearIndependent_iff.mp h _ hs
  have hc : Real.cos t = 0 := by simpa using hcoeff 0
  have hsin : Real.sin t = 0 := by simpa using hcoeff 1
  have hp := Real.sin_sq_add_cos_sq t
  simp [hc, hsin] at hp

/-- The actual trigonometric path has uniform positive lower and finite
upper norm bounds, derived from independence and compact periodic range. -/
theorem oscillatory_pos_norm_bounds (a b : E)
    (h : LinearIndependent ℝ ![a, b]) :
    ∃ m M : ℝ, 0 < m ∧ ∀ t : ℝ,
      m ≤ ‖oscillatory a b t‖ ∧ ‖oscillatory a b t‖ ≤ M := by
  exact exists_pos_norm_bounds (oscillatory_periodic a b)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (oscillatory_continuous a b) (oscillatory_ne_zero a b h)

/-- The same constants bound every angular frequency, including zero. -/
theorem oscillatory_frequency_pos_norm_bounds (a b : E)
    (h : LinearIndependent ℝ ![a, b]) :
    ∃ m M : ℝ, 0 < m ∧ ∀ ω t : ℝ,
      m ≤ ‖Real.cos (ω * t) • a - Real.sin (ω * t) • b‖ ∧
      ‖Real.cos (ω * t) • a - Real.sin (ω * t) • b‖ ≤ M := by
  obtain ⟨m, M, hm, hbounds⟩ := oscillatory_pos_norm_bounds a b h
  exact ⟨m, M, hm, fun ω t => hbounds (ω * t)⟩

end Oscillatory

end UnforcedLeray.PeriodicMode
