import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!
# Leaf B7 (`OscDerivRep`): the Leibniz form of the differentiated oscillator equation

Proves `UnforcedLeray.Short.Spine.OscDerivRep` (`Sub/SP_CAN4_4_1.lean`), exactly as stated.

Source of record: `the November 2 reference manuscript`, lines 1134-1140.

Method. `iteratedDeriv_succ'` gives `φ^{(m+2)} = (φ'')^{(m)}`. On the open set `Ioi 0` the second
derivative is `c₁ φ' + c₀ φ` (`OscOde.deriv2`), so `Set.EqOn.iteratedDeriv_of_isOpen` transfers this
to the `m`-th derivative. `iteratedDeriv_add` and `iteratedDeriv_mul` (Mathlib) expand it, and
`iteratedDeriv_succ'` identifies `(φ')^{(j)} = φ^{(j+1)}`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

open UnforcedLeray.Short.Spine

/-- `oscC1 = -(1/r + r/2)` is `C^m` at every `r > 0`. -/
theorem oscDerivRep_contDiffAt_C1 {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ContDiffAt ℝ m oscC1 r := by
  have hr' : r ≠ 0 := hr.ne'
  have h : ContDiffAt ℝ m (fun x : ℝ => -(1 / x + x / 2)) r := by
    fun_prop (disch := (first | positivity | simp [hr']))
  have hfun : oscC1 = Complex.ofRealCLM ∘ (fun x : ℝ => -(1 / x + x / 2)) := by
    funext x
    simp [oscC1, Complex.ofRealCLM_apply]
  rw [hfun]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp r h

/-- `oscC0 n = 4/r² - 2 - n` is `C^m` at every `r > 0`. -/
theorem oscDerivRep_contDiffAt_C0 {r : ℝ} (hr : 0 < r) (n m : ℕ) :
    ContDiffAt ℝ m (oscC0 n) r := by
  have hr' : r ≠ 0 := hr.ne'
  have h : ContDiffAt ℝ m (fun x : ℝ => 4 / x ^ 2 - 2 - (n : ℝ)) r := by
    fun_prop (disch := (first | positivity | simp [hr']))
  have hfun : oscC0 n = Complex.ofRealCLM ∘ (fun x : ℝ => 4 / x ^ 2 - 2 - (n : ℝ)) := by
    funext x
    simp [oscC0, Complex.ofRealCLM_apply]
  rw [hfun]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp r h

theorem oscDerivRep_proof : UnforcedLeray.Short.Spine.OscDerivRep := by
  intro n φ hφ m r hr
  have hr' : r ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr hr
  have hnhds : Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds hr'
  -- smoothness at `r` of the factors, to order `m`
  have hφA : ContDiffAt ℝ m φ r := (hφ.1.contDiffAt hnhds).of_le (by simp)
  have hDOn : ContDiffOn ℝ ∞ (deriv φ) (Ioi 0) :=
    hφ.1.deriv_of_isOpen isOpen_Ioi (by simp)
  have hDA : ContDiffAt ℝ m (deriv φ) r := (hDOn.contDiffAt hnhds).of_le (by simp)
  have hC1A : ContDiffAt ℝ m oscC1 r := oscDerivRep_contDiffAt_C1 hr m
  have hC0A : ContDiffAt ℝ m (oscC0 n) r := oscDerivRep_contDiffAt_C0 hr n m
  have hAD : ContDiffAt ℝ m (oscC1 * deriv φ) r := hC1A.mul hDA
  have hBφ : ContDiffAt ℝ m (oscC0 n * φ) r := hC0A.mul hφA
  -- the second-order form, on the open set `Ioi 0`
  have hEq : EqOn (deriv (deriv φ)) (oscC1 * deriv φ + oscC0 n * φ) (Ioi 0) :=
    fun x hx => hφ.deriv2 (Set.mem_Ioi.mp hx)
  -- `φ^{(m+2)} = (φ'')^{(m)} = (c₁ φ' + c₀ φ)^{(m)}` at `r`
  have h1 : iteratedDeriv (m + 2) φ r =
      iteratedDeriv m (oscC1 * deriv φ + oscC0 n * φ) r := by
    rw [show m + 2 = (m + 1) + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ']
    exact Set.EqOn.iteratedDeriv_of_isOpen hEq isOpen_Ioi m hr'
  -- `(φ')^{(j)} = φ^{(j+1)}`
  have key : ∀ j : ℕ, iteratedDeriv (j + 1) φ r = iteratedDeriv j (deriv φ) r := by
    intro j
    rw [iteratedDeriv_succ']
  rw [h1, iteratedDeriv_add hAD hBφ, iteratedDeriv_mul hC1A hDA,
    iteratedDeriv_mul hC0A hφA, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [key (m - i)]
  ring
