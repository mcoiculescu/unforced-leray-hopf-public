import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1` (`DualRemPointwise`): decomposition

Source: `the November 2 reference manuscript`
lines 1923-1927 (commutator of `∇^⊥` and `T` with the cutoff `φ(η/L)`).
Proved here: `dualRemPointwise_of` from four Props (vanishing off `supp χ`, smoothness of `ψ_∞`,
a generic commutator bound, and a jet bound for `ψ_∞` by the jet of `g`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Off `tsupport χ` the remainder vanishes: `ψ_L` and `ψ_∞` are `0` on the open neighbourhood
`{y | y.1 ∉ tsupport χ}` of `x`, so all their derivatives (hence `Rem_L`) vanish at `x`.
Use `fderiv` of an eventually-zero function (`Filter.EventuallyEq.fderiv_eq`) three times
(for `cpdC`, `perpC`, `flatTransposeC`), compare `deqT_cpd_vanish` in `Sub/T12_7.lean`. -/
def DualRemVanish : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (x : Coord),
    x.1 ∉ tsupport χ → ∀ i : Fin 2, dualRem ν μ χ φ H s L x i = 0

/-- `ψ_∞ = σ^{μ-1}χ(σ)H(s-σ,·)` is smooth (SP 1923-1927): outside `tsupport χ` it is `0` near the
point, inside `s - σ > 0` where `H` is smooth (`HeatSol.smooth`, `ContDiffOn` on the open set
`Ioi 0 ×ˢ univ`) and `σ^{μ-1}` is smooth for `σ > 0` (`ContDiffAt.cpow_const`-style). -/
def DualPsiInfSmooth : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (H : Coord → ℝ) (s r' : ℝ) (χ : ℝ → ℝ),
    0 < c → 0 < ν → 0 < s → HeatSol c ν r' H → DFChi s χ →
    ContDiff ℝ ∞ (dualPsiInf μ χ H s)

/-- Generic commutator bound (SP 1923-1927; Leibniz rule).  For smooth `φ` with compact support and
any smooth complex `Ψ`, the commutator
`T(∇^⊥(φ(η/L)Ψ)) - φ(η/L) T(∇^⊥Ψ)` at `x` (with `|x.1| ≤ R`) is bounded by
`C (L⁻¹+L⁻²+L⁻³) Σ_{n≤3} ‖D^nΨ(x)‖`: terms with no derivative on `φ(η/L)` cancel, the others carry
`L^{-k}φ^{(k)}(η/L)`, `k = 1,2,3`, (`φ^{(k)}` bounded: continuous with compact support), a factor
`1, x.1, ν x.1, |μ-1|` and derivatives of `Ψ` of total order `≤ 3 - k`... in all cases `≤ 3`. -/
def GenericCommBound : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ R : ℝ, 0 ≤ R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ Ψ : Coord → ℂ, ContDiff ℝ ∞ Ψ →
      ∀ x : Coord, |x.1| ≤ R → ∀ i : Fin 2,
        ‖flatTransposeC ν μ (perpC (fun y => (φ (y.2.2 / L) : ℂ) * Ψ y)) x i -
            (φ (x.2.2 / L) : ℂ) * flatTransposeC ν μ (perpC Ψ) x i‖ ≤
          C * (L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3) * ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n Ψ x‖

/-- Jet bound for `ψ_∞` (SP 1923-1927): for `σ = x.1 ∈ tsupport χ` (a compact subset of `(0,s)`),
`Σ_{n≤3}‖D^nψ_∞(x)‖ ≤ C Σ_{n≤3}‖D^n g(x)‖`, `g(z) = H(s - z.1, z.2)`, with `C` from sup bounds of
`σ^{μ-1}` and `χ` and their `σ`-derivatives of order `≤ 3` on `tsupport χ` (Leibniz,
`norm_iteratedFDeriv_mul_le`; the factor `a(σ) = σ^{μ-1}χ(σ)` is smooth, `a∘fst`). -/
def DualPsiInfJet : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (H : Coord → ℝ) (s r' : ℝ) (χ : ℝ → ℝ),
    0 < c → 0 < ν → 0 < s → HeatSol c ν r' H → DFChi s χ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Coord, x.1 ∈ tsupport χ →
      ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n (dualPsiInf μ χ H s) x‖ ≤
        C * ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖

theorem dualRemPointwise_of (h0 : DualRemVanish) (h1 : DualPsiInfSmooth)
    (h2 : GenericCommBound) (h3 : DualPsiInfJet) : DualRemPointwise := by
  intro c ν μ H s r' χ φ hc hν hs hH hχ hφ
  obtain ⟨Cg, hCg, hg⟩ := h2 ν μ φ hφ.1 hφ.2.1 s hs.le
  obtain ⟨Cj, hCj, hj⟩ := h3 c ν μ H s r' χ hc hν hs hH hχ
  have hsm := h1 c ν μ H s r' χ hc hν hs hH hχ
  refine ⟨Cg * Cj, mul_nonneg hCg hCj, ?_⟩
  intro L hL x i
  have hK : 0 ≤ L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 := by
    have : 0 < L⁻¹ := inv_pos.2 hL
    positivity
  by_cases hx : x.1 ∈ tsupport χ
  · have hG : dualG χ H s x =
        ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖ := by
      simp [dualG, hx]
    have hxs : |x.1| ≤ s := by
      have := hχ.2.2 hx
      rw [abs_of_pos this.1]; exact this.2.le
    have h4 := hg L hL (dualPsiInf μ χ H s) hsm x hxs i
    have h5 := hj x hx
    have h6 : ‖dualRem ν μ χ φ H s L x i‖ ≤
        Cg * (L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3) *
          ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n (dualPsiInf μ χ H s) x‖ := h4
    rw [hG]
    calc ‖dualRem ν μ χ φ H s L x i‖
        ≤ Cg * (L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3) *
          ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n (dualPsiInf μ χ H s) x‖ := h6
      _ ≤ Cg * (L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3) *
          (Cj * ∑ n ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖) :=
          mul_le_mul_of_nonneg_left h5 (mul_nonneg hCg hK)
      _ = Cg * Cj * (L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3) *
          ∑ n ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖ := by ring
  · rw [h0 ν μ χ φ H s L x hx i, norm_zero]
    have : 0 ≤ dualG χ H s x := by
      unfold dualG
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    positivity

end UnforcedLeray.Short.IIb
