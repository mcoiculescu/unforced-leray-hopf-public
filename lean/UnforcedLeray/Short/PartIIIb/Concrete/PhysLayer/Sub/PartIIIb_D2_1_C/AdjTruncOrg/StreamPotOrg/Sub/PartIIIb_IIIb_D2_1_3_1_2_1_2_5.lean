import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs

/-!
# `HardyR3` from the smooth Hardy inequality and a density statement

Source `the November 2 reference manuscript` lines 1351-1362 (Hardy inequality in
`ℝ³`, `C_c^∞` density and radial integration by parts).  Two analytic inputs:

* `HardySmooth`: the inequality for `C_c^∞` fields (radial integration by parts, constant
  `(2/(3-2))² = 4`);
* `HardyApprox`: mollification and radial cutoffs approximate `u ∈ L⁶` with weak gradient in `L²`
  a.e. by `C_c^∞` fields whose gradient `L²` energies converge (cutoff error `n⁻¹‖u‖_{L⁶(n<|y|<2n)}`
  by Hölder on annuli).

The limit passage (Fatou) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Hardy inequality for smooth compactly supported fields (source 1351-1362). -/
def HardySmooth : Prop :=
  ∀ φ : Space → CVec3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    ∫⁻ y : Space, ‖φ y‖ₑ ^ 2 / ‖y‖ₑ ^ 2 ≤
      4 * ∑ j : Fin 3, ∫⁻ y : Space,
        ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2

/-- `C_c^∞` approximation of `u ∈ L⁶` with weak gradient `D ∈ L²` (source 1351-1362, 1470-1480):
a.e. convergence and convergence of the gradient energies. -/
def HardyApprox : Prop :=
  ∀ (u : Space → CVec3) (D : Fin 3 → Space → CVec3),
    MemLp u 6 volume → (∀ j, MemLp (D j) 2 volume) →
    (∀ (j : Fin 3) (φ : Space → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ y : Space, (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) • u y
        = -∫ y : Space, φ y • D j y) →
    ∃ φ : ℕ → Space → CVec3, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      (∀ᵐ y : Space, Tendsto (fun n => φ n y) atTop (𝓝 (u y))) ∧
      ∀ j : Fin 3, Tendsto (fun n => ∫⁻ y : Space,
          ‖fderiv ℝ (φ n) y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2) atTop
        (𝓝 (∫⁻ y : Space, ‖D j y‖ₑ ^ 2))

theorem hardyR3_of (h1 : HardySmooth) (h2 : HardyApprox) : HardyR3 := by
  intro u D hu hD hweak
  obtain ⟨φ, hφ, hae, hgrad⟩ := h2 u D hu hD hweak
  have hne : ∀ᵐ y : Space, y ≠ 0 := by
    have : (volume : Measure Space) {0} = 0 := measure_singleton 0
    rw [ae_iff]
    simpa using this
  set f : ℕ → Space → ℝ≥0∞ := fun n y => ‖φ n y‖ₑ ^ 2 / ‖y‖ₑ ^ 2 with hf
  have hmeas : ∀ n, Measurable (f n) := by
    intro n
    have hc : Continuous (φ n) := (hφ n).1.continuous
    have : Measurable (fun y => ‖φ n y‖ₑ ^ 2) := (hc.measurable.enorm).pow_const 2
    exact this.div (measurable_id.enorm.pow_const 2)
  have h3 : ∫⁻ y, liminf (fun n => f n y) atTop ∂volume ≤
      liminf (fun n => ∫⁻ y, f n y) atTop := lintegral_liminf_le hmeas
  have h4 : ∫⁻ y : Space, ‖u y‖ₑ ^ 2 / ‖y‖ₑ ^ 2 ≤ ∫⁻ y, liminf (fun n => f n y) atTop := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae, hne] with y hy hy0
    have hb : (‖y‖ₑ ^ 2)⁻¹ ≠ ⊤ := by
      rw [Ne, ENNReal.inv_eq_top]
      simpa using hy0
    have ht : Tendsto (fun n => f n y) atTop (𝓝 (‖u y‖ₑ ^ 2 / ‖y‖ₑ ^ 2)) := by
      simp only [hf, div_eq_mul_inv]
      exact ENNReal.Tendsto.mul_const (((ENNReal.continuous_pow 2).tendsto _).comp hy.enorm) (Or.inr hb)
    rw [ht.liminf_eq]
  have hsum : Tendsto (fun n => 4 * ∑ j : Fin 3, ∫⁻ y : Space,
      ‖fderiv ℝ (φ n) y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2) atTop
      (𝓝 (4 * ∑ j : Fin 3, ∫⁻ y : Space, ‖D j y‖ₑ ^ 2)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr (by simp))
    exact tendsto_finsetSum _ fun j _ => hgrad j
  have h5 : liminf (fun n => ∫⁻ y, f n y) atTop ≤
      liminf (fun n => 4 * ∑ j : Fin 3, ∫⁻ y : Space,
        ‖fderiv ℝ (φ n) y (EuclideanSpace.single j (1 : ℝ))‖ₑ ^ 2) atTop := by
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    exact h1 (φ n) (hφ n).1 (hφ n).2
  rw [hsum.liminf_eq] at h5
  exact h4.trans (h3.trans h5)

end UnforcedLeray.Short.PartIIIb.Concrete
