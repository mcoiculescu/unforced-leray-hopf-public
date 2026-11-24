import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# `PartIII-b:C/grad/3/5/1/3`: `HpALocUnif` from a compact region, a joint Gaussian bound and
uniform-in-`t` Gaussian summability

Source `the November 2 reference manuscript`
4991, 5063-5079.  Proved: `hpALocUnif_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Gaussian weight of the `j`-th lattice term, with polynomial weight of degree 5 (the lattice
term `hpATm` and its `x`- and `s`-derivatives carry polynomial factors up to degree 5 in
`y = t - j c`; source 4973-4980, 5063-5079). -/
def hpAGauss (α c : ℝ) (j : ℤ) (t : ℝ) : ℝ :=
  (1 + |t - (j : ℝ) * c|) ^ 5 * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)

/-- Uniform-in-`t` summable Gaussian majorant (source 5063-5079; uniform version of
`gp_poly_summable`, via `gp_gauss_dom` with `|t| ≤ T`). -/
def HpAGaussUnif : Prop :=
  ∀ α c T : ℝ, 0 < α → 0 < c →
    ∃ D : ℤ → ℝ, Summable D ∧ ∀ t : ℝ, |t| ≤ T → ∀ j : ℤ, hpAGauss α c j t ≤ D j

/-- Compact region (source 4991): a bounded `U` with closure in `{s>0}` lies in
`s0 ≤ s ≤ s1`, `‖x‖ ≤ R`, `s0 > 0`. -/
def HpACompact : Prop :=
  ∀ U : Set Chart, Bornology.IsBounded (closure U) → closure U ⊆ {p : Chart | 0 < p.1} →
    ∃ s0 s1 R : ℝ, 0 < s0 ∧ s0 ≤ s1 ∧ ∀ p ∈ U, s0 ≤ p.1 ∧ p.1 ≤ s1 ∧ ‖p.2‖ ≤ R

/-- Joint (`s` and `x`) derivative and value bound of the lattice terms on a compact region
(source 4963-4980, 5063-5079; `a = 1 + νs ≤ 1 + ν s1`, `A^y` and `∂_s A^y` bounded on
`[s0,s1]`, `V_j` and its `s`-, `x`-derivatives Gaussian in `x - j c(ν)`). -/
def HpAJointBound (as : ℝ) : Prop :=
  ∀ (χ : ℝ → ℝ), IsSourceCutoffC χ → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s0 s1 R : ℝ, 0 < s0 → s0 ≤ s1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Chart, s0 ≤ p.1 → p.1 ≤ s1 → ‖p.2‖ ≤ R → ∀ j : ℤ,
        ‖hpATm ν χ A j p‖ ≤ K * hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1 ∧
        ‖fderiv ℝ (hpATm ν χ A j) p‖ ≤ K * hpAGauss (1 / (4 * (1 + ν * s1))) (cOf ν) j p.2.1

theorem hpALocUnif_of (as : ℝ) (h1 : HpAGaussUnif) (h2 : HpACompact) (h3 : HpAJointBound as) :
    HpALocUnif as := by
  intro χ hχ ν hν A hA U hUo _ hcl hbd
  obtain ⟨s0, s1, R, hs0, hs01, hU⟩ := h2 U hbd hcl
  obtain ⟨K, hK0, hK⟩ := h3 χ hχ ν hν A hA s0 s1 R hs0 hs01
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hα : 0 < 1 / (4 * (1 + ν * s1)) := by
    have hs1 : 0 < s1 := lt_of_lt_of_le hs0 hs01
    have : 0 < 1 + ν * s1 := by positivity
    positivity
  obtain ⟨D, hDs, hD⟩ := h1 (1 / (4 * (1 + ν * s1))) (cOf ν) R hα hc
  refine ⟨fun _ j => K * D j, fun _ _ => hDs.mul_left K, ?_⟩
  intro k hk j p hp
  obtain ⟨a1, a2, a3⟩ := hU p hp
  have hx : |p.2.1| ≤ R := by simpa [Real.norm_eq_abs] using (norm_fst_le p.2).trans a3
  have hG := hD p.2.1 hx j
  obtain ⟨b1, b2⟩ := hK p a1 a2 a3 j
  interval_cases k
  · rw [norm_iteratedFDerivWithin_zero]
    exact b1.trans (mul_le_mul_of_nonneg_left hG hK0)
  · rw [norm_iteratedFDerivWithin_one _ (hUo.uniqueDiffOn p hp), fderivWithin_of_isOpen hUo hp]
    exact b2.trans (mul_le_mul_of_nonneg_left hG hK0)

end UnforcedLeray.Short.PartIIIb.Concrete
