import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4

/-!
# `PartII-a:N01/9/1/3/3/2/1` (decomposition): `ClassicalGradBound`

Source `the November 2 reference manuscript`
lines 1684-1689, 3541-3552.

Route (kernel version of the energy bound; no classical equation, no slab integration by parts).
For `s > 0`, `∂_j u_i(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ}(∂_j f_σ) dσ`, `f_σ = σ⁻¹ F(σ)` (`HeatIntFderivFormula`),
and `‖e^{θΔ}∂_j f‖_{L²(cell)} ≤ C₀ θ^{-1/2}‖f‖_{L²(cell)}` (Gaussian gradient in `L¹`, Young), so by
Minkowski the cell `L²` norm of `∂_j u_i(s)` is at most `C₀ ∫₀^s k(s,σ) Φ_i(σ) dσ` with
`k(s,σ) = (σ/s)^{Re μ}(ν(s-σ))^{-1/2}/σ` and `Φ_i(σ) = ‖F_i(σ)‖_{L²(cell)}`.  Then the Hardy-type
bound (Minkowski again after `σ = ts`, Beta integral `B(Re μ+1/4, 1/2) < ∞` since `Re μ > -1/4`)
`∫ s^{-1/2}(∫₀^s k Φ)² ds ≤ B ∫ σ^{-3/2}Φ²` gives `ν`-independent-of-`F` control by `‖g‖_𝓗`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (tnorm2)

/-- The kernel `k(s,σ) = (σ/s)^a (ν(s-σ))^{-1/2} / σ` of the gradient bound. -/
def gradKernel (a ν s σ : ℝ) : ℝ := (σ / s) ^ a * (ν * (s - σ)) ^ (-(1 / 2 : ℝ)) / σ

/-- **(G1)** Gaussian gradient smoothing on the cell (lines 3373-3383): for `C¹` bounded periodic `f`
with bounded derivative, `‖e^{θΔ}∂_j f‖_{L²(cell)} ≤ C₀ θ^{-1/2}‖f‖_{L²(cell)}` with `C₀` universal.
(`planeHeat θ g = gaussKernel θ ∗ g`; `e^{θΔ}∂_j f = (∂_j K_θ) ∗ f` by integration by parts, and
`‖∂_jK_θ‖_{L¹(ℝ²)} = C₀' θ^{-1/2}`; Young on the cell for `c`-periodic `f`, as in
`PlaneHeatCellContract`, which is the case `∂_j` absent.) -/
def PlaneHeatGradSmoothing : Prop :=
  ∃ C0 : ℝ, ∀ (θ c : ℝ), 0 < θ → 0 < c → ∀ f : ℝ × ℝ → ℂ, ContDiff ℝ 1 f →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) →
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ f x‖ ≤ M) → ∀ j : Fin 2,
      (∫⁻ x in UnforcedLeray.B0579.cell c,
          ‖UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ f y (UnforcedLeray.B0579.dir j)) x‖ₑ ^ 2)
        ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (C0 * θ ^ (-(1 / 2 : ℝ))) *
        (∫⁻ x in UnforcedLeray.B0579.cell c, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ)

/-- **(G2)** Slice bound for the gradient of the heat integral (lines 1684-1689, 3379-3383):
Minkowski for `∂_j u_i(s) = ∫₀^s (σ/s)^μ planeHeat(ν(s-σ))(∂_j f_σ) dσ` (`HeatIntFderivFormula`,
`f_σ = heatSlice c F σ = σ⁻¹ F(σ)`, `c`-periodic, `C¹`, bounded with bounded derivative by
`HeatSliceBounds`) together with (G1) and `|(σ/s)^μ| = (σ/s)^{Re μ}`; proof as for
`HeatIntSliceL2`, with the gradient smoothing in place of the contraction. -/
def HeatIntGradSlice : Prop :=
  ∃ C0 : ℝ, ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s : ℝ, 0 < s → ∀ i j : Fin 2,
      ∫⁻ x in UnforcedLeray.B0579.cell c,
          ‖fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) x
            (UnforcedLeray.B0579.dir j)‖ₑ ^ 2 ≤
        ENNReal.ofReal (C0 ^ 2) *
          (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel μ.re ν s σ) *
            (∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2

/-- **(G3)** Hardy-type bound for the kernel (Minkowski integral inequality after `σ = t s`):
`∫₀^∞ s^{-1/2}(∫₀^s k(s,σ)Φ(σ)dσ)² ds ≤ B ∫₀^∞ σ^{-3/2}Φ(σ)² dσ` for `a > -1/4`,
`B = ν⁻¹ B(a+1/4,1/2)²` (Beta integral `∫₀¹ t^{a-3/4}(1-t)^{-1/2} dt`, finite iff `a > -1/4`). -/
def HardyGradKernel : Prop :=
  ∀ (a ν : ℝ), -(1 / 4 : ℝ) < a → 0 < ν → ∃ B : ℝ, ∀ Φ : ℝ → ℝ≥0∞, Measurable Φ →
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel a ν s σ) * Φ σ) ^ 2 ≤
      ENNReal.ofReal B * ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2

/-- **(G4)** The `𝓗`-norm of a force given a.e. by a smooth `c`-periodic `F` (tex line 3307:
`𝓗 = L²(s^{-3/2}ds dq dη)` on the cell `s>0, q ∈ (0,c], η ∈ ℝ`): since `F` is `c`-periodic in `q`
the `q`-cell `(0,c]` may be replaced by `[-c/2,c/2)`; Tonelli. -/
def HSqNormEq : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : HSpace c MeridC) (F : Profile → MeridC), IsSmoothForceFn c F →
    (g : Profile → MeridC) =ᵐ[measureH c] F →
      ENNReal.ofReal (‖g‖ ^ 2) =
        ∑ i : Fin 2, ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) *
          ∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2

/-- **(G5)** Passage from the age-weighted integral of the classical gradient to slab integrals
(`lintegral_ageμ`, Tonelli, `velF c u = u` by `velF_of_periodic` and `HeatIntPeriodic`,
`gradOf` unfolded for `s>0`; measurability of the integrands from `HeatIntRegular`;
`tnorm2² = ∑ ‖T i j‖²`): equality with the normalisation factor `c⁻¹`, stated as `≤`. -/
def GradAgeSliceBound : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∫⁻ p, ENNReal.ofReal
        (tnorm2 (gradOf (velF c (smoothHeatInt c ν μ F)) p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
      ENNReal.ofReal c⁻¹ * ∑ i : Fin 2, ∑ j : Fin 2,
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
          ∫⁻ x in UnforcedLeray.B0579.cell c,
            ‖fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) x
              (UnforcedLeray.B0579.dir j)‖ₑ ^ 2

theorem classicalGradBound_of (h2 : HeatIntGradSlice) (h3 : HardyGradKernel) (h5 : HSqNormEq)
    (h6 : GradAgeSliceBound) : ClassicalGradBound := by
  intro c ν hc hν μ hμ
  obtain ⟨C0, hC0⟩ := h2
  obtain ⟨B, hB⟩ := h3 μ.re ν (by linarith) hν
  have hB' : ENNReal.ofReal B = ENNReal.ofReal (max B 0) := by
    rcases le_total B 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos]
    · simp [h]
  refine ⟨2 * c⁻¹ * C0 ^ 2 * max B 0, ?_⟩
  intro g hg F hF hgF
  set Φ : Fin 2 → ℝ → ℝ≥0∞ := fun i σ =>
    (∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2) ^ (1 / 2 : ℝ) with hΦ
  have hΦm : ∀ i, Measurable (Φ i) := by
    intro i
    have hFc : Continuous F := hF.1.continuous
    have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ‖F p i‖ₑ ^ 2 := by
      have : Continuous fun p : ℝ × (ℝ × ℝ) => ‖F p i‖ₑ ^ 2 := by fun_prop
      exact this.measurable
    exact (hm.lintegral_prod_right' (ν := volume.restrict (UnforcedLeray.B0579.cell c))).pow_const _
  set M : Fin 2 → ℝ≥0∞ := fun i => ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) *
      ∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2 with hM
  have hΦsq : ∀ i σ, Φ i σ ^ 2 = ∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2 := by
    intro i σ
    simp only [hΦ]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hcomp : ∀ i j, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
          ∫⁻ x in UnforcedLeray.B0579.cell c,
            ‖fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) x
              (UnforcedLeray.B0579.dir j)‖ₑ ^ 2) ≤
        ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal (max B 0) * M i) := by
    intro i j
    calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (C0 ^ 2) *
          (ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
            (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel μ.re ν s σ) * Φ i σ) ^ 2) := by
          refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
          rw [mul_left_comm]
          gcongr
          exact hC0 c ν hc hν μ F hF s hs i j
      _ = ENNReal.ofReal (C0 ^ 2) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
            (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel μ.re ν s σ) * Φ i σ) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal B * ∫⁻ σ in Ioi (0 : ℝ),
            ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ i σ ^ 2) :=
          by gcongr; exact hB (Φ i) (hΦm i)
      _ = _ := by
          have hMi : ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ i σ ^ 2 = M i :=
            lintegral_congr fun σ => by rw [hΦsq]
          rw [hB', hMi]
  have hnorm := h5 c hc g F hF hgF
  calc _ ≤ _ := h6 c ν hc hν μ F hF
    _ ≤ ENNReal.ofReal c⁻¹ * ∑ i : Fin 2, ∑ j : Fin 2,
          (ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal (max B 0) * M i)) :=
        by gcongr with i _ j _; exact hcomp i j
    _ = ENNReal.ofReal (2 * c⁻¹ * C0 ^ 2 * max B 0) * ENNReal.ofReal (‖g‖ ^ 2) := by
        have e : ENNReal.ofReal (2 * c⁻¹ * C0 ^ 2 * max B 0) =
            2 * ENNReal.ofReal c⁻¹ * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (max B 0) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [e, hnorm]
        simp only [Fin.sum_univ_two, hM]
        ring
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]

end UnforcedLeray.Short.PartIIa.N01
