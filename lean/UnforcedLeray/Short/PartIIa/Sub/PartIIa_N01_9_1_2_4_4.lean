import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4

/-!
# `PartII-a:N01/9/1/2/4/4` (decomposition): `HeatIntDivZero`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383, 3426-3430.  The cell divergence of the heat integral at age `s>0`
is `∫₀^s (σ/s)^μ planeHeat(ν(s-σ)) (div of the periodized slice) dσ` (derivative falls on the
slice and commutes with the Gaussian average and the `σ`-integral); the slice divergence vanishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-- The periodized slice `w ↦ (periodize c (q ↦ q.1⁻¹ • F q)) (σ, w)` in the integrand of
`smoothHeatInt` (lines 3379-3383). -/
def heatSlice (c : ℝ) (F : Profile → MeridC) (σ : ℝ) (w : ℝ × ℝ) : MeridC :=
  UnforcedLeray.B0220.periodize c (fun q : Profile => (q.1)⁻¹ • F q) (σ, w)

/-- **(D1)** The periodized slice of a smooth force with divergence free slices is divergence
free: for `c`-periodic `F`, `heatSlice c F σ w = σ⁻¹ • F (σ,w)` (`B0220.periodic_reduceIoc_eq`),
so its divergence is `σ⁻¹ slabDiv F σ w = 0` (lines 1684-1689). -/
def HeatSliceDivZero : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    (∀ σ y, slabDiv F σ y = 0) → ∀ (σ : ℝ) (z : ℝ × ℝ),
      ∑ j : Fin 2, fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w j) z
        (UnforcedLeray.B0579.dir j) = 0

/-- **(D2)** Differentiation of the heat integral in `(q,η)` at fixed age `s > 0`, under the
Gaussian average and the `σ`-integral (the slice and its derivatives are bounded, the integrand
vanishes for `σ < s₁`, so dominated differentiation applies; lines 3379-3383): the derivative of
component `j` in direction `e_j` is the heat integral of the corresponding slice derivative, and
each such integrand is interval integrable. -/
def HeatIntFderivFormula : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s : ℝ, 0 < s → ∀ (y : ℝ × ℝ) (j : Fin 2),
      IntervalIntegrable (fun σ : ℝ => ((σ / s : ℝ) : ℂ) ^ μ •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w j) z
            (UnforcedLeray.B0579.dir j)) y) volume 0 s ∧
      fderiv ℝ (fun z : ℝ × ℝ => smoothHeatInt c ν μ F (s, z) j) y (UnforcedLeray.B0579.dir j) =
        ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
          UnforcedLeray.B0224.planeHeat (ν * (s - σ))
            (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w j) z
              (UnforcedLeray.B0579.dir j)) y

/-- **(D2a)** The Gaussian average of a `C¹` function with bounded values and bounded derivative
is differentiable and the derivative falls on the function (dominated differentiation of
`x ↦ ∫ gaussKernel θ y • u (x - planeι y)`, `B0224.planeHeat_of_pos`; lines 3373-3383). -/
def PlaneHeatFderiv : Prop :=
  ∀ (θ : ℝ), 0 < θ → ∀ u : ℝ × ℝ → ℂ, ContDiff ℝ 1 u → (∃ M : ℝ, ∀ x, ‖u x‖ ≤ M) →
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ u x‖ ≤ M) →
      Differentiable ℝ (UnforcedLeray.B0224.planeHeat θ u) ∧
      ∀ (x v : ℝ × ℝ), fderiv ℝ (UnforcedLeray.B0224.planeHeat θ u) x v =
        UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ u y v) x

/-- **(D2b)** Uniform bounds and regularity of the periodized slices of a smooth force (lines
1684-1689): `heatSlice c F σ w = σ⁻¹ • F (σ,w)` is jointly `C^∞` (it vanishes for `σ < s₁`), the
values and the `w`-derivatives of every component are bounded uniformly in `(σ,w)` (`F` is
`c`-periodic in `q` and supported in a compact set of `(σ,η)`), and the slices vanish for `σ < s₁`. -/
def HeatSliceBounds : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    (∃ s₁ : ℝ, 0 < s₁ ∧ ∀ σ, σ < s₁ → ∀ w, heatSlice c F σ w = 0) ∧
    (∀ j : Fin 2, ContDiff ℝ 1 (fun p : ℝ × (ℝ × ℝ) => heatSlice c F p.1 p.2 j)) ∧
    ∃ M : ℝ, (∀ j σ w, ‖heatSlice c F σ w j‖ ≤ M) ∧
      (∀ j σ w, ‖fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w j) w‖ ≤ M)

theorem heatIntDivZero_of (h1 : HeatSliceDivZero) (h2 : HeatIntFderivFormula) :
    HeatIntDivZero := by
  intro c ν hc hν μ F hF hzero s hs y
  have hD := h1 c hc F hF hzero
  obtain ⟨i0, e0⟩ := h2 c ν hc hν μ F hF s hs y 0
  obtain ⟨i1, e1⟩ := h2 c ν hc hν μ F hF s hs y 1
  rw [Fin.sum_univ_two, e0, e1, ← intervalIntegral.integral_add i0 i1]
  have key : ∀ σ : ℝ, (((σ / s : ℝ) : ℂ) ^ μ •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w 0) z
            (UnforcedLeray.B0579.dir 0)) y) +
      (((σ / s : ℝ) : ℂ) ^ μ •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w 1) z
            (UnforcedLeray.B0579.dir 1)) y) = 0 := by
    intro σ
    have hf : (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w 1) z
        (UnforcedLeray.B0579.dir 1)) =
        fun z => (-1 : ℝ) • fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w 0) z
          (UnforcedLeray.B0579.dir 0) := by
      funext z
      have := hD σ z
      rw [Fin.sum_univ_two] at this
      rw [neg_one_smul ℝ]
      exact eq_neg_of_add_eq_zero_right this
    rw [hf, UnforcedLeray.B0224.planeHeat_smul]
    simp only [neg_one_smul ℝ, smul_neg, smul_eq_mul, mul_neg, add_neg_cancel]
  rw [show (fun x : ℝ => _) = fun _ => (0:ℂ) from funext key]
  simp

end UnforcedLeray.Short.PartIIa.N01
