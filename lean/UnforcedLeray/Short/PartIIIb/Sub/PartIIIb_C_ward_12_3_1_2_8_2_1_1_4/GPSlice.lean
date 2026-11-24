import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_4
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay
import UnforcedLeray.Units.B0412

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/4/1`: slice test `GPSlice`

Target: `UnforcedLeray.Short.PartIIIb.Concrete.GPSlice` (parent module, Lemma A).
Source of record: `the November 2 reference manuscript` (the slice test of the
gradient of the phase-periodic cutoff potential; the parent file cites lines 1393-1400, 1409-1412).

Proof outline.

* `∇σ` is `P`-periodic: `σ` is `P`-periodic in `τ`, so `σ(· + (P,0))` equals `σ`, and the chain
  rule for translations (`fderiv_comp_add_right`) gives `fderiv σ (p + (P,0)) = fderiv σ p`.
* `∇σ` is continuous (`σ` is smooth).
* `|∇σ(τ,y)| ≤ C (1+|y|)^{-3}`, and `3 < 3 · (11/7)`, so the slice-continuity lemma
  `Short.PartIIa.sliceContOfDecay` (dominated convergence against `(1+|y|)^{-33/7}`, integrable
  on `ℝ³`) gives `SliceCont (q₀')` for `∇σ`, with `q₀' = conjExp q₀ = 11/7`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- **Lemma A (slice test).** Under `SigmaHyp`, `∇σ` is a `P`-periodic slice-continuous test in
`L^{q₀'}(ℝ³)`. -/
theorem gpSlice : UnforcedLeray.Short.PartIIIb.Concrete.GPSlice := by
  intro P _ σ hs
  rcases hs with ⟨hsm, hper, C, hC⟩
  -- the exponent `q₀' = conjExp q₀ = 11/7`
  have hq0gt : (1 : ℝ≥0∞) < UnforcedLeray.B0412.q0E :=
    ENNReal.one_lt_ofReal.2 (by norm_num [UnforcedLeray.B0281.q0])
  have hq0ne : UnforcedLeray.B0412.q0E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcj : (conjExp UnforcedLeray.B0412.q0E).toReal = 11 / 7 := by
    rw [UnforcedLeray.Short.PartIIa.toReal_conjExp hq0gt hq0ne, UnforcedLeray.B0412.q0E_toReal]
    norm_num
  have hcne : conjExp UnforcedLeray.B0412.q0E ≠ ⊤ := by
    intro h
    have h2 := hcj
    rw [h, ENNReal.toReal_top] at h2
    norm_num at h2
  have hlt : (3 : ℝ) < 3 * (conjExp UnforcedLeray.B0412.q0E).toReal := by
    rw [hcj]
    norm_num
  -- continuity of `∇σ`
  have hcont : Continuous (gradT σ) := by
    have hdy : ∀ j : Fin 3, Continuous fun p : ℝ × Space => UnforcedLeray.PhaseSpace.dy j σ p := by
      intro j
      unfold UnforcedLeray.PhaseSpace.dy
      exact (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
    unfold gradT
    exact continuous_finsetSum _ fun j _ => (hdy j).smul continuous_const
  have hbd : ∀ τ y, ‖gradT σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-3 : ℝ) := fun τ y => (hC τ y).2
  -- slice continuity from polynomial decay
  have hsl : SliceCont (conjExp UnforcedLeray.B0412.q0E) (gradT σ) :=
    UnforcedLeray.Short.PartIIa.sliceContOfDecay (conjExp UnforcedLeray.B0412.q0E) hcne 3 C hlt
      (gradT σ) hcont hbd
  -- periodicity of the derivatives of `σ`
  have hshift : ∀ p : ℝ × Space, fderiv ℝ σ (p + ((P, 0) : ℝ × Space)) = fderiv ℝ σ p := by
    intro p
    have h1 : (fun x : ℝ × Space => σ (x + ((P, 0) : ℝ × Space))) = σ := by
      funext x
      obtain ⟨t, z⟩ := x
      simp only [Prod.mk_add_mk, add_zero]
      exact hper t z
    have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := σ) ((P, 0) : ℝ × Space) (x := p)
    rw [h1] at h2
    exact h2.symm
  have hperg : ∀ τ y, gradT σ (τ + P, y) = gradT σ (τ, y) := by
    intro τ y
    have e : ((τ + P, y) : ℝ × Space) = (τ, y) + ((P, 0) : ℝ × Space) := by simp
    simp only [gradT, UnforcedLeray.PhaseSpace.dy, e, hshift]
  unfold IsSliceTest
  exact ⟨hperg, hsl⟩

end UnforcedLeray.Short.PartIIIb.Concrete
