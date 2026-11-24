import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# `GaussianPeriodicDecay` from two leaves (SP 2356-2358)

Source `the November 2 reference manuscript` 2356-2358: the periodized Gaussian
remainder `∑_k G(r_k) e^{2iϑ_k}` is differentiated termwise (`hasFDerivAt_tsum_of_isPreconnected`
on a box around the base point) with the majorant `∑_k e^{-(ξ+kc)²/32}`, and for `c ≥ 1` the
lattice sum `∑_k e^{-(ξ+kc)²/16}` is bounded independently of `ξ, c`.

Leaves: `GaussTermBound` (chain rule, one term), `GaussLatticeSum` (lattice Gaussian sums).
Proved here: `gaussianPeriodicDecay_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Blueprint

/-- **Leaf A: one term** (SP 2356-2358; `|∇(G e^{2iϑ})| ≤ |G'||∇r| + |G|·|D e^{2iϑ}|`,
`‖∇r‖ ≤ √2` for the sup-norm on `ℝ×ℝ`, `‖D e^{2iϑ}‖ ≤ 2√2/r ≤ 4√2` for `r ≥ 1/2`, so the
constant `10` suffices).  For `Gf` as in `GaussianPeriodicDecay` and `|z.2| > 1/2`, the `k`-th
term is differentiable at `z` and `‖term‖ + ‖D term‖ ≤ 10 C_G e^{-((z.1+kc)²+z.2²)/16}`. -/
def GaussTermBound : Prop :=
  ∀ (Gf : ℝ → ℂ) (CG : ℝ),
    (∀ r : ℝ, 1 / 2 ≤ r → DifferentiableAt ℝ Gf r ∧
      ‖Gf r‖ + ‖deriv Gf r‖ ≤ CG * Real.exp (-(r ^ 2 / 16))) →
    ∀ (c : ℝ) (k : ℤ) (z : ℝ × ℝ), 1 / 2 < |z.2| →
      DifferentiableAt ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) z ∧
      ‖gaussTerm Gf c z k‖ + ‖fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) z‖ ≤
        10 * CG * Real.exp (-(((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) / 16))

/-- **Leaf B: lattice Gaussian sums** (SP 2357-2358).  For `b, c > 0` the series
`∑_{k∈ℤ} e^{-b(ξ+kc)²}` is summable for every `ξ` (re-center at the nearest lattice point,
`|ξ+(j+k₀)c| ≥ |j|c/2`); and for `c ≥ 1` the sum `∑_k e^{-(ξ+kc)²/16}` is bounded by a constant
independent of `ξ` and `c` (same re-centering, comparison with `∑_j e^{-j²/64}`). -/
def GaussLatticeSum : Prop :=
  (∀ b c : ℝ, 0 < b → 0 < c → ∀ ξ : ℝ,
      Summable (fun k : ℤ => Real.exp (-(b * (ξ + (k : ℝ) * c) ^ 2)))) ∧
  ∃ C0 : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ ξ : ℝ,
    ∑' k : ℤ, Real.exp (-((ξ + (k : ℝ) * c) ^ 2 / 16)) ≤ C0

theorem gaussianPeriodicDecay_of (h1 : GaussTermBound) (h2 : GaussLatticeSum) :
    GaussianPeriodicDecay := by
  intro Gf CG hG
  obtain ⟨hs, C0, hC0⟩ := h2
  have hterm := h1 Gf CG hG
  have hCG : 0 ≤ CG := by
    have := hG (1 / 2) le_rfl
    have h0 : 0 ≤ ‖Gf (1 / 2)‖ + ‖deriv Gf (1 / 2)‖ := by positivity
    have h3 := h0.trans this.2
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg (Real.exp_pos (-((1 / 2 : ℝ) ^ 2 / 16)))
    linarith
  -- local differentiability and summability, uniformly on a box
  have partA : ∀ c : ℝ, 0 < c → ∀ y : ℝ × ℝ, 1 / 2 < |y.2| →
      Summable (gaussTerm Gf c y) ∧
      HasFDerivAt (gaussPeriodic Gf c)
        (∑' k : ℤ, fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) y) y := by
    intro c hc y hy
    set δ : ℝ := |y.2| - 1 / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    set S : Set (ℝ × ℝ) := Ioo (y.1 - 1) (y.1 + 1) ×ˢ Ioo (y.2 - δ) (y.2 + δ) with hS
    have hSo : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
    have hSc : IsPreconnected S := ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
    have hyS : y ∈ S := by
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have hSz : ∀ z ∈ S, 1 / 2 < |z.2| := by
      intro z hz
      have h1 := hz.2.1
      have h2 := hz.2.2
      have : |y.2| - |z.2| ≤ |y.2 - z.2| := abs_sub_abs_le_abs_sub _ _
      have h3 : |y.2 - z.2| < δ := by rw [abs_lt]; constructor <;> linarith
      rw [hδ] at h3
      linarith
    set u : ℤ → ℝ := fun k => 10 * CG * Real.exp (1 / 16) *
      Real.exp (-((1 / 32 : ℝ) * (y.1 + (k : ℝ) * c) ^ 2)) with hu
    have hus : Summable u :=
      (hs (1 / 32) c (by norm_num) hc y.1).mul_left (10 * CG * Real.exp (1 / 16))
    have hbound : ∀ z ∈ S, ∀ k : ℤ,
        10 * CG * Real.exp (-(((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) / 16)) ≤ u k := by
      intro z hz k
      have ht : |z.1 - y.1| < 1 := by
        rw [abs_lt]; constructor <;> linarith [hz.1.1, hz.1.2]
      have ht2 : (z.1 - y.1) ^ 2 ≤ 1 := by
        have := abs_nonneg (z.1 - y.1)
        nlinarith [sq_abs (z.1 - y.1)]
      have key : -(((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) / 16) ≤
          1 / 16 + -((1 / 32 : ℝ) * (y.1 + (k : ℝ) * c) ^ 2) := by
        nlinarith [sq_nonneg (y.1 + (k : ℝ) * c + 2 * (z.1 - y.1)), sq_nonneg z.2]
      have hex := Real.exp_le_exp.2 key
      rw [Real.exp_add] at hex
      calc 10 * CG * Real.exp (-(((z.1 + (k : ℝ) * c) ^ 2 + z.2 ^ 2) / 16))
          ≤ 10 * CG * (Real.exp (1 / 16) * Real.exp (-((1 / 32 : ℝ) * (y.1 + (k : ℝ) * c) ^ 2))) :=
            mul_le_mul_of_nonneg_left hex (by positivity)
        _ = u k := by rw [hu]; ring
    have hfd : ∀ (k : ℤ) (z : ℝ × ℝ), z ∈ S →
        HasFDerivAt (fun w : ℝ × ℝ => gaussTerm Gf c w k)
          (fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) z) z := fun k z hz =>
      (hterm c k z (hSz z hz)).1.hasFDerivAt
    have hf' : ∀ (k : ℤ) (z : ℝ × ℝ), z ∈ S →
        ‖fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) z‖ ≤ u k := by
      intro k z hz
      have := (hterm c k z (hSz z hz)).2
      have h0 : 0 ≤ ‖gaussTerm Gf c z k‖ := norm_nonneg _
      exact (le_trans (by linarith) this).trans (hbound z hz k)
    have hf0 : Summable (fun k : ℤ => gaussTerm Gf c y k) := by
      refine Summable.of_norm_bounded hus ?_
      intro k
      have := (hterm c k y hy).2
      have h0 : 0 ≤ ‖fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) y‖ := norm_nonneg _
      exact (le_trans (by linarith) this).trans (hbound y hyS k)
    exact ⟨hf0, hasFDerivAt_tsum_of_isPreconnected hus hSo hSc hfd hf' hyS hf0 hyS⟩
  refine ⟨fun c hc y hy => ⟨(partA c hc y hy).1, (partA c hc y hy).2.differentiableAt⟩, ?_⟩
  refine ⟨20 * CG * C0, fun c hc y hcy => ?_⟩
  have hc0 : 0 < c := by linarith
  have hy1 : 1 / 2 < |y.2| := by linarith
  obtain ⟨-, hD⟩ := partA c hc0 y hy1
  rw [hD.fderiv]
  set g : ℤ → ℝ := fun k => 10 * CG * Real.exp (-(y.2 ^ 2 / 16)) *
    Real.exp (-((y.1 + (k : ℝ) * c) ^ 2 / 16)) with hg
  have hgs : Summable g := by
    have := (hs (1 / 16) c (by norm_num) hc0 y.1).mul_left (10 * CG * Real.exp (-(y.2 ^ 2 / 16)))
    refine this.congr fun k => ?_
    rw [hg]; congr 2; ring_nf
  have hgb : ∀ k : ℤ, ‖gaussTerm Gf c y k‖ + ‖fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) y‖ ≤
      g k := by
    intro k
    refine (hterm c k y hy1).2.trans (le_of_eq ?_)
    rw [hg]
    dsimp only
    rw [mul_assoc (10 * CG), ← Real.exp_add]
    have : -(y.2 ^ 2 / 16) + -((y.1 + (k : ℝ) * c) ^ 2 / 16) =
        -(((y.1 + (k : ℝ) * c) ^ 2 + y.2 ^ 2) / 16) := by ring
    rw [this]
  have hsum : ∑' k, g k ≤ 10 * CG * Real.exp (-(y.2 ^ 2 / 16)) * C0 := by
    rw [hg, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hC0 c hc y.1) (by positivity)
  have hP : ‖gaussPeriodic Gf c y‖ ≤ ∑' k, g k :=
    tsum_of_norm_bounded hgs.hasSum fun k => le_trans (by
      have : 0 ≤ ‖fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) y‖ := norm_nonneg _
      linarith) (hgb k)
  have hDP : ‖∑' k : ℤ, fderiv ℝ (fun w : ℝ × ℝ => gaussTerm Gf c w k) y‖ ≤ ∑' k, g k :=
    tsum_of_norm_bounded hgs.hasSum fun k => le_trans (by
      have : 0 ≤ ‖gaussTerm Gf c y k‖ := norm_nonneg _
      linarith) (hgb k)
  have hE : 0 < Real.exp (-(y.2 ^ 2 / 16)) := Real.exp_pos _
  calc _ ≤ 2 * ∑' k, g k := by linarith
    _ ≤ 2 * (10 * CG * Real.exp (-(y.2 ^ 2 / 16)) * C0) := by linarith
    _ = 20 * CG * C0 * Real.exp (-(y.2 ^ 2 / 16)) := by ring

end UnforcedLeray.Short.IIIa
