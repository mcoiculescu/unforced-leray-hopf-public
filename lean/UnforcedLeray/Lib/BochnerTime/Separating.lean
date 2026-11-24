import UnforcedLeray.Lib.BochnerTime.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Weak time derivatives from scalar tests (INF14 target T4)


target T4. A Bochner function `u : ℝ → X` has weak time derivative `u'` as soon as `ℓ ∘ u` has
weak derivative `ℓ ∘ u'` for every `ℓ` in a separating family of continuous functionals. This is
how the manuscript identifies time derivatives of graph-space valued curves through
distributional pairings (scoping note §2.6–§2.8; decision D2 of `scoping/README.md`: phase
identities are pairings against test functions).

## Main results

* `hasWeakDerivTime_of_separating`: the separating-family criterion;
* `hasWeakDerivTime_of_dual`: the special case of the whole dual (Hahn–Banach).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.BochnerTime

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Separating-family criterion** (T4). If `u, u'` are integrable on `Ioo a b` and, for every
`ℓ` in a family `Λ` of continuous functionals that separates points, `ℓ ∘ u'` is the weak time
derivative of `ℓ ∘ u`, then `u'` is the weak time derivative of `u`. -/
theorem hasWeakDerivTime_of_separating {a b : ℝ} {u u' : ℝ → X} {Λ : Set (StrongDual ℝ X)}
    (hsep : ∀ x : X, (∀ ℓ ∈ Λ, ℓ x = 0) → x = 0)
    (hint : IntegrableOn u (Ioo a b)) (hint' : IntegrableOn u' (Ioo a b))
    (h : ∀ ℓ ∈ Λ, HasWeakDerivTime a b (fun t => ℓ (u t)) (fun t => ℓ (u' t))) :
    HasWeakDerivTime a b u u' := by
  refine ⟨hint, hint', fun φ hφ hφs hφt => ?_⟩
  have h1 := integrable_deriv_smul hφ hφs hφt hint
  have h2 := integrable_smul hφ hφs hφt hint'
  refine eq_neg_of_add_eq_zero_left (hsep _ fun ℓ hℓ => ?_)
  rw [map_add, ← ℓ.integral_comp_comm h1, ← ℓ.integral_comp_comm h2]
  simp only [map_smul, smul_eq_mul]
  have := (h ℓ hℓ).identity φ hφ hφs hφt
  simp only [smul_eq_mul] at this
  rw [this, neg_add_cancel]

/-- **Dual criterion** (T4, `Λ` = the whole dual). -/
theorem hasWeakDerivTime_of_dual {a b : ℝ} {u u' : ℝ → X}
    (hint : IntegrableOn u (Ioo a b)) (hint' : IntegrableOn u' (Ioo a b))
    (h : ∀ ℓ : StrongDual ℝ X, HasWeakDerivTime a b (fun t => ℓ (u t)) (fun t => ℓ (u' t))) :
    HasWeakDerivTime a b u u' :=
  hasWeakDerivTime_of_separating (Λ := univ)
    (fun x hx => SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => hx ℓ trivial)
    hint hint' fun ℓ _ => h ℓ

end UnforcedLeray.BochnerTime
