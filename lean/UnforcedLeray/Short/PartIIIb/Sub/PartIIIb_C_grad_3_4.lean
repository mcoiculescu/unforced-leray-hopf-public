import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3

/-!
# `PartIII-b:C/grad/3/4`: `GradCellBound` from a lattice-sum pointwise envelope and a uniform
cell `L²` bound of the Gaussian lattice sum

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.  Proved: `gradCellBound_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Polynomially weighted Gaussian of the chart point `(u, η)`. -/
def latticeW (α : ℝ) (k : ℕ) (u η : ℝ) : ℝ :=
  (1 + |u| + |η|) ^ k * Real.exp (-α * (u ^ 2 + η ^ 2))

/-- The lattice sum `Σ_j W(q - j c, η)` over `j ∈ ℤ`. -/
def latticeS (α : ℝ) (k : ℕ) (c : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' j : ℤ, latticeW α k (x.1 - (j : ℝ) * c) x.2

/-- Pointwise envelope (source 4963-4980, 5063-5079): the entries of `s⁻¹∇ĥ_A` are `∂_q b`,
`∂_η b`, `-ε(𝒦+1)b`, `ε b_r`, `b = s^{-1/2}ĥ_A` built from the lattice sums `h^p_A, ψ^p_A`
(terms `V_j` Gaussian in `x - j c(ν)`, `a = 1+νs ∈ [1,2.1]`), `𝒦 = η∂_η + 2s∂_s`; hence
`‖s⁻¹∇ĥ_A(s,x)‖ ≤ C (|A^y(s)|+|s∂_sA^y|+|(s∂_s)²A^y|) Σ_j W(x - j c(ν))`, uniformly in
`ν, ε ≤ 1`, `0 < s ≤ 1.1/ν` (Gaussian rate `α`, polynomial degree `k` independent of the data). -/
def GradEnvelope : Prop :=
  ∃ (C α : ℝ) (k : ℕ), 0 ≤ C ∧ 0 < α ∧
    ∀ (ν ε s : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
      ∀ (χf : ℝ → ℝ) (A : ℝ → Mat3), ContDiffAt ℝ 2 (Ay ν χf A) s → ∀ x : ℝ × ℝ,
        ‖gradAcoef ν ε χf A (s, x)‖ ≤ C * (frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) +
          frob (sDeriv (sDeriv (Ay ν χf A)) s)) * latticeS α k (cOf ν) x

/-- Uniform cell `L²` bound of the Gaussian lattice sum (source 5063-5079): for `c ≥ 1`
(`c = ν⁻²`) only boundedly many lattice terms meet the cell `[-c/2,c/2)`, and the `η`-integral of
the Gaussian is finite. -/
def GradLatticeL2 : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ k : ℕ, ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ c : ℝ, 1 ≤ c →
    ∫⁻ x, ENNReal.ofReal (latticeS α k c x ^ 2) ∂(UnforcedLeray.Cyl.avgμ c) ≤ ENNReal.ofReal K0

theorem gradCellBound_of (h1 : GradEnvelope) (h2 : GradLatticeL2) : GradCellBound := by
  obtain ⟨C, α, k, hC, hα, hE⟩ := h1
  obtain ⟨K0, hK0, hL⟩ := h2 α hα k
  refine ⟨C * Real.sqrt K0, by positivity, ?_⟩
  intro ν ε s hν hν1 hε hε1 hs hsT χf A hA
  set F : ℝ := frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) +
    frob (sDeriv (sDeriv (Ay ν χf A)) s) with hF
  have hF0 : 0 ≤ F := add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  calc ∫⁻ x, ENNReal.ofReal (‖gradAcoef ν ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal ((C * F) ^ 2) * ENNReal.ofReal (latticeS α k (cOf ν) x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
        refine lintegral_mono (fun x => ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := hE ν ε s hν hν1 hε hε1 hs hsT χf A hA x
        have h0 := norm_nonneg (gradAcoef ν ε χf A (s, x))
        rw [← mul_pow]
        exact pow_le_pow_left₀ h0 (by simpa [hF, mul_assoc] using h) 2
    _ = ENNReal.ofReal ((C * F) ^ 2) *
          ∫⁻ x, ENNReal.ofReal (latticeS α k (cOf ν) x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((C * F) ^ 2) * ENNReal.ofReal K0 :=
        by gcongr; exact hL (cOf ν) hc1
    _ = ENNReal.ofReal ((C * Real.sqrt K0) ^ 2 * F ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_pow, mul_pow, Real.sq_sqrt hK0]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
