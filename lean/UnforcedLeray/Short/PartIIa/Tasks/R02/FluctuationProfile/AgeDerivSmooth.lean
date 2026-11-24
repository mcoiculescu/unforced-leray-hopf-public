import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, `AgeDerivSmooth` (age derivatives of jointly smooth functions)

Source of record: `the November 2 reference manuscript`, lines 397-459.

Target: `AgeDerivSmooth` (`Sub/R02_2.lean`): for `f(s, w)` that is `C^∞` on `(0, ∞) × E`, with
`E = ℝ` and `E = ℝ × ℝ`, the age derivatives `(s, w) ↦ ∂_s^k f(s, w)` are `C^∞` on the same set.

Proof: one generic lemma for a real normed space `E`, by induction on `k`. On the open set
`U = (0, ∞) × E`, `∂_s^{k+1} f(s, w) = fderiv ℝ (∂_s^k f) (s, w) (1, 0)` (the age line
`r ↦ (r, w)` has derivative `(1, 0)`), and `x ↦ fderiv ℝ G x (1, 0)` is `C^∞` on `U` whenever `G` is.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **Age derivatives of a jointly smooth function, generic normed space.** If `f : ℝ → E → ℝ` is
`C^∞` on `(0, ∞) × E` (as a function of `(s, w)`), then so is `(s, w) ↦ ∂_s^k f(s, w)`, for every
`k`. -/
theorem ageDerivIter_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → ℝ) (hf : ContDiffOn ℝ ∞ (fun x : ℝ × E => f x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ∀ k : ℕ, ContDiffOn ℝ ∞
      (fun x : ℝ × E => iteratedDeriv k (fun r => f r x.2) x.1) (Ioi 0 ×ˢ univ) := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set E)) := isOpen_Ioi.prod isOpen_univ
    -- pointwise: the age derivative of order `k+1` is the derivative of the order-`k` one along `(1, 0)`
    have hderiv : ∀ x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set E),
        iteratedDeriv (k + 1) (fun r => f r x.2) x.1 =
          fderiv ℝ (fun y : ℝ × E => iteratedDeriv k (fun r => f r y.2) y.1) x (1, 0) := by
      rintro ⟨s, w⟩ hx
      have hs : (0 : ℝ) < s := hx.1
      have hdiff : DifferentiableAt ℝ
          (fun y : ℝ × E => iteratedDeriv k (fun r => f r y.2) y.1) (s, w) :=
        (ih.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      have hline : HasDerivAt (fun r : ℝ => ((r, w) : ℝ × E)) ((1 : ℝ), (0 : E)) s :=
        (hasDerivAt_id' s).prodMk (hasDerivAt_const s w)
      have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s hline
      rw [iteratedDeriv_succ]
      exact hcomp.deriv
    have hsm : ContDiffOn ℝ ∞
        (fun y : ℝ × E => fderiv ℝ (fun z : ℝ × E => iteratedDeriv k (fun r => f r z.2) z.1) y (1, 0))
        (Ioi 0 ×ˢ univ) :=
      (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    exact hsm.congr fun x hx => hderiv x hx

/-- **`AgeDerivSmooth`** (`Sub/R02_2.lean`): the age derivatives of a jointly smooth function are
jointly smooth, for `E = ℝ` and for `E = ℝ × ℝ`. -/
theorem ageDerivSmooth : UnforcedLeray.Short.PartIIa.AgeDerivSmooth :=
  ⟨fun f hf k => ageDerivIter_contDiffOn (E := ℝ) f hf k,
    fun f hf k => ageDerivIter_contDiffOn (E := ℝ × ℝ) f hf k⟩

end UnforcedLeray.Short.PartIIa
