import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `PartIII-b:C/asrc/ra/5/2` : derivatives of the Gaussian factor `exp(-|x|²/(κ a))`

Source 4963-4968 (`V_j, p_j, ψ_j` are polynomials times `e^{-|x_j|²/(κ a)}`, `κ = 4` or `2`,
`a = 1 + ν s`).  Write `q(s,x) = |x|² (κ a(s))⁻¹`, so the Gaussian is `exp(-q)`.

Plan: (L1) `D^j(|x|²)` has size `≤ C(1+|x|²)`; (L2) `D^j((κ a)⁻¹)` is bounded for `s ∈ [s0,s1]`;
(L3) hence `‖D^j q‖ ≤ C (1+|x|²)` there (`GaussQBound`); (L4) induction
`D^{m+1}(e^{-q}) = D^m(e^{-q} · (-Dq))` with Leibniz gives `‖D^m e^{-q}‖ ≤ C (1+|x|²)^m e^{-q}`
(`GaussExpStep`); finally `a ≤ a(s1)` gives `e^{-q} ≤ e^{-|x|²/(κ a(s1))}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `q(s,x) = |x|² (κ a(s))⁻¹`. -/
def gaussQ (κ ν : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ := sq2 p.2 * (κ * ageA ν p.1)⁻¹

/-- (L3) every derivative of `q` is `O(1+|x|²)` uniformly for `s ∈ [s0,s1]`. -/
def GaussQBound (κ ν s0 s1 : ℝ) : Prop :=
  0 < κ → 0 < ν → 0 < s0 → s0 ≤ s1 →
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (gaussQ κ ν) (s, x)‖ ≤ C * (1 + sq2 x)

/-- (L4) the induction: if all derivatives of `q` are `O(1+|x|²)` on the slab, then
`‖D^m e^{-q}‖ ≤ C (1+|x|²)^m e^{-q}` there. -/
def GaussExpStep (κ ν s0 s1 : ℝ) : Prop :=
  0 < κ → 0 < ν → 0 < s0 → s0 ≤ s1 → GaussQBound κ ν s0 s1 →
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) (s, x)‖ ≤
        C * (1 + sq2 x) ^ m * Real.exp (-(gaussQ κ ν (s, x)))

/-- Assembly: `GaussQBound` and `GaussExpStep` give the iterated bound with the Gaussian of the
oldest age `s1`. -/
theorem gauss_iterated_bound_of (κ ν s0 s1 : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (hs0 : 0 < s0)
    (hs01 : s0 ≤ s1) (hQ : GaussQBound κ ν s0 s1) (hE : GaussExpStep κ ν s0 s1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, m ≤ n → ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × (ℝ × ℝ) =>
          Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) (s, x)‖ ≤
        C * (1 + sq2 x) ^ n * Real.exp (-(sq2 x) / (κ * ageA ν s1)) := by
  choose Cm hCm0 hCm using hE hκ hν hs0 hs01 hQ
  refine ⟨∑ m ∈ Finset.range (n + 1), Cm m, Finset.sum_nonneg (fun m _ => hCm0 m), ?_⟩
  intro m hm s hs x
  have hfun : (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) =
      fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p)) := by
    funext p
    simp [gaussQ, div_eq_mul_inv, neg_mul]
  rw [hfun]
  have h1 := hCm m s hs x
  have hsq : 0 ≤ sq2 x := by unfold sq2; positivity
  have hCle : Cm m ≤ ∑ m ∈ Finset.range (n + 1), Cm m :=
    Finset.single_le_sum (f := Cm) (fun m _ => hCm0 m) (Finset.mem_range.2 (by omega))
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [hs.1]
  have ha1 : ageA ν s ≤ ageA ν s1 := by unfold ageA; nlinarith [hs.2]
  have hexp : Real.exp (-(gaussQ κ ν (s, x))) ≤ Real.exp (-(sq2 x) / (κ * ageA ν s1)) := by
    apply Real.exp_le_exp.2
    have : sq2 x * (κ * ageA ν s1)⁻¹ ≤ sq2 x * (κ * ageA ν s)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ (mul_pos hκ ha) (mul_le_mul_of_nonneg_left ha1 hκ.le)) hsq
    simp only [gaussQ]
    rw [div_eq_mul_inv, neg_mul]
    linarith
  have hpow : (1 + sq2 x) ^ m ≤ (1 + sq2 x) ^ n :=
    pow_le_pow_right₀ (by linarith) hm
  calc _ ≤ Cm m * (1 + sq2 x) ^ m * Real.exp (-(gaussQ κ ν (s, x))) := h1
    _ ≤ (∑ m ∈ Finset.range (n + 1), Cm m) * (1 + sq2 x) ^ n *
          Real.exp (-(sq2 x) / (κ * ageA ν s1)) := by
        have hp0 : 0 ≤ (1 + sq2 x) ^ m := by positivity
        have hCp : Cm m * (1 + sq2 x) ^ m ≤
            (∑ m ∈ Finset.range (n + 1), Cm m) * (1 + sq2 x) ^ n :=
          mul_le_mul hCle hpow hp0 (le_trans (hCm0 m) hCle)
        exact mul_le_mul hCp hexp (Real.exp_nonneg _)
          (le_trans (mul_nonneg (hCm0 m) hp0) hCp)

end UnforcedLeray.Short.PartIIIb.Concrete
