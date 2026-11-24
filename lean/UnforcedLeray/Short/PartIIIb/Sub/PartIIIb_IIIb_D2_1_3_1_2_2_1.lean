import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2

/-!
# Leaf 1 of `FWUAdjMoll`: `ρ ⋆ Φ` is a solenoidal phase test

Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
`Φ` is in the adjoint graph domain (so a.e. `P`-periodic, in `Y_2`, weakly solenoidal) and
`y`-compactly supported; `ρ ⋆ Φ = mollP ρ Φ`.  Smoothness comes from local integrability of `Φ`
(`MollLocInt`), periodicity and support are proved here, and the divergence is `⟪∇φ_x, Φ⟫ = 0`
for the periodised reflected kernel `φ_x` (`MollDivKernel`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

instance instHaarRS : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- **A0** (source 1351-1362): `Φ` in the adjoint graph domain, `y`-compactly supported, is locally
integrable on `ℝ × ℝ³` (it is a.e. `P`-periodic with finite `Y_2` norm, supported in `ℝ × B_R`;
`L²(cell) ⊂ L¹(cell)` on the bounded `y`-support, then translate the cell by `kP`). -/
def MollLocInt : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ →
      LocallyIntegrable Φ volume

/-- **D1** (source 1351-1362; periodisation of the reflected kernel): for every point `x` there is
a scalar phase test `φ` (the periodisation `(τ, y) ↦ ∑_k ρ(x - (τ + kP, y))`, a finite sum on each
compact set since `ρ` has compact support) and a constant `c` with
`div_y (ρ ⋆ Φ)(x) = c ⟪∇_y φ, Φ⟫` (`c = -P`: differentiate under the integral, move `∂_{y_j}` onto
the kernel, and fold `ℝ` into the cell `(0, P]` using the a.e. periodicity of `Φ`). -/
def MollDivKernel : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ →
      ∀ ρ : ContDiffBump (0 : ℝ × Space), ∀ x : ℝ × Space,
        ∃ (φ : ℝ × Space → ℂ) (c : ℂ), IsPhaseTest P φ ∧
          ∑ j : Fin 3, dy j (mollP ρ Φ) x j = c * pairF P (gradT φ) Φ

/-- `ρ ⋆ Φ` is smooth, given local integrability of `Φ`. -/
theorem mollP_contDiff (ρ : ContDiffBump (0 : ℝ × Space)) (Φ : ℝ × Space → CVec3)
    (hΦ : LocallyIntegrable Φ volume) : ContDiff ℝ ∞ (mollP ρ Φ) := by
  have h : mollP ρ Φ = MeasureTheory.convolution (ρ.normed volume) Φ
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp [mollP, MeasureTheory.convolution]
  rw [h]
  exact ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed hΦ

/-- The kernel vanishes outside the closed ball of radius `rOut`. -/
theorem normed_eq_zero_of_not_mem (ρ : ContDiffBump (0 : ℝ × Space)) {z : ℝ × Space}
    (hz : z ∉ Metric.closedBall (0 : ℝ × Space) ρ.rOut) : ρ.normed volume z = 0 := by
  by_contra hne
  have : z ∈ Function.support (ρ.normed volume) := hne
  rw [ρ.support_normed_eq] at this
  exact hz (Metric.ball_subset_closedBall this)

/-- `ρ ⋆ Φ` is `y`-compactly supported. -/
theorem mollP_ysupport (ρ : ContDiffBump (0 : ℝ × Space)) (Φ : ℝ × Space → CVec3)
    (hsupp : YCompactSupp Φ) : ∃ R, ∀ τ y, R < ‖y‖ → mollP ρ Φ (τ, y) = 0 := by
  obtain ⟨R, hR⟩ := hsupp
  refine ⟨R + ρ.rOut, fun τ y hy => ?_⟩
  unfold mollP
  have key : ∀ z : ℝ × Space, ρ.normed volume z • Φ ((τ, y) - z) = 0 := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℝ × Space) ρ.rOut
    · have hz2 : ‖z.2‖ ≤ ρ.rOut :=
        le_trans (norm_snd_le z) (mem_closedBall_zero_iff.mp hz)
      have h0 : Φ ((τ, y) - z) = 0 := by
        apply hR
        have h1 : ‖y‖ ≤ ‖y - z.2‖ + ‖z.2‖ := by
          have := norm_add_le (y - z.2) z.2
          simpa using this
        show R ≤ ‖y - z.2‖
        linarith
      rw [h0, smul_zero]
    · rw [normed_eq_zero_of_not_mem ρ hz, zero_smul]
  simp [key]

/-- `ρ ⋆ Φ` is `P`-periodic in `τ` (`Φ` a.e. periodic). -/
theorem mollP_periodic {P : ℝ} (ρ : ContDiffBump (0 : ℝ × Space)) (Φ : ℝ × Space → CVec3)
    (h : ∀ᵐ x : ℝ × Space, Φ (x.1 + P, x.2) = Φ x) (τ : ℝ) (y : Space) :
    mollP ρ Φ (τ + P, y) = mollP ρ Φ (τ, y) := by
  unfold mollP
  have hq : Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (τ, y) - z) volume volume :=
    (Measure.measurePreserving_sub_left volume ((τ, y) : ℝ × Space)).quasiMeasurePreserving
  have h2 := hq.ae h
  refine integral_congr_ae ?_
  filter_upwards [h2] with z hz
  have e : (τ + P, y) - z = (((τ, y) - z).1 + P, ((τ, y) - z).2) := by
    ext <;> simp <;> ring
  rw [e, hz]

theorem mollIsSolTestL_of (h1 : MollLocInt) (h2 : MollDivKernel) : MollIsSolTestL := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ hsupp ρ
  refine ⟨⟨mollP_contDiff ρ Φ (h1 P ν μ hP hP1 hν hμ Φ g hΦ hsupp),
    fun τ y => mollP_periodic ρ Φ hΦ.mem.periodic τ y, mollP_ysupport ρ Φ hsupp⟩, ?_⟩
  intro x
  obtain ⟨φ, c, hφ, hx⟩ := h2 P ν μ hP hP1 hν hμ Φ g hΦ hsupp ρ x
  rw [hx, hΦ.sol φ hφ, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
