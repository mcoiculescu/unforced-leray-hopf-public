import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Short.PartIIa.StatementsFree

/-!
# Part II-a, task `PartII-a:F04`: the maximal distributional domain (decomposition)

Source of record: `the November 2 reference manuscript`, lines 1409-1412 and
1470-1480.  The drift step (`T₀ w ∈ Y_r` once `νΔw ∈ Y_r`) is proved here
(`hasPhaseOp_drift_of`); the analytic content is the gluing of the window Laplacians of
`LocalWindowEstimate` into a global `a ∈ Y_r`, split into `GlobalLaplacianField` (a single field
`Λ` that is a window Laplacian on every window, periodic, `L^r` on a period) and
`LaplacianFieldToY` (such a field is a phase-space distributional Laplacian).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

/-- **Leaf `PartII-a:F04/1` (one global window Laplacian; lines 1470-1480).** Given the local
window estimate, a distributional solution `(μ + L₀)w = f` in `Y_r` has a single strongly
measurable field `Λ` on `ℝ × ℝ³` which is a weak Laplacian `νΔW` on every window
`|τ - τ₀| < 1` (the window Laplacians of `LocalWindowEstimate` agree a.e. on overlaps by the
uniqueness of the weak Laplacian on a window, and are glued over the countably many rational
centres), is `P`-periodic in `τ` a.e., and is `L^r` over one period (the window bound summed over
`≈ P + 2` windows, with the factor `∫₀^P` obtained from `B0425.lintegral_center_average`; no
inverse power of `P`). -/
def GlobalLaplacianField : Prop :=
  LocalWindowEstimate → ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ →
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∃ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ ∧ (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) ∧
          (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) ∧
          ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤

/-- **Leaf `PartII-a:F04/2` (from a global window Laplacian to `HasPhaseOp (νΔ)`; lines
1478-1480).** If `Λ` is as in `GlobalLaplacianField`, then `Λ` represents an element `a ∈ Y_r`
(periodic and `L^r` on a period) and `νΔw = a` against every phase test: periodize a phase test
`Φ` with a partition of unity `∑ₖ χ(· - kP/2)` subordinate to windows of length `2`, use
`IsWindowLaplacian` on each piece and sum. -/
def LaplacianFieldToY : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W → ∀ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ →
      (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) →
      (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) →
      ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ →
        ∃ a : Yq P r, HasPhaseOp (nuLapT ν) w a

/-- The drift step: `(μ + L₀ᵗ)` against `w` is `f`, and `νΔw = a`, give `T₀ w = f - μ w + a + w/2`
in distributions. -/
theorem hasPhaseOp_drift_of {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {ν : ℝ} {μ : ℂ}
    {f w a : Yq P r} (hf : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f)
    (ha : HasPhaseOp (nuLapT ν) w a) :
    HasPhaseOp driftT w (f - μ • w + a + (1 / 2 : ℂ) • w) := by
  intro Φ hΦ
  have h1 : phasePair P r (μ • Φ + L0T ν Φ) w = phasePair P r Φ f := hf Φ hΦ
  have h2 := ha Φ hΦ
  have hD : IsPhaseTest P (driftT Φ) := hΦ.driftT
  have hl : IsPhaseTest P (lapT Φ) := hΦ.lapT
  have hN : IsPhaseTest P (nuLapT ν Φ) := by
    have := hl.clm_comp (ν • ContinuousLinearMap.id ℝ CVec3)
    exact this
  have hH : IsPhaseTest P ((1 / 2 : ℝ) • Φ) := by
    have := hΦ.clm_comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ CVec3)
    exact this
  have hA : IsPhaseTest P (μ • Φ) := by
    have := hΦ.clm_comp ((μ • ContinuousLinearMap.id ℂ CVec3).restrictScalars ℝ)
    exact this
  have e : (μ • Φ + L0T ν Φ) = (μ • Φ) + ((driftT Φ - nuLapT ν Φ) - (1 / 2 : ℝ) • Φ) := by
    funext p; simp [L0T]
  rw [e, phasePair_add hA (hD.sub hN |>.sub hH), phasePair_sub (hD.sub hN) hH,
    phasePair_sub hD hN, phasePair_const_smul hΦ, phasePair_real_smul hΦ] at h1
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  rw [h2] at h1
  have : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [this] at h1
  linear_combination h1

/-- Reduction of the target to the local window estimate and the two gluing leaves. -/
theorem commonBodyMaximalDomain_of (hloc : LocalWindowEstimate) (h1 : GlobalLaplacianField)
    (h2 : LaplacianFieldToY) : CommonBodyMaximalDomain := by
  intro r _ hr1 hr3 P _ hP ν hν μ _ w f hf
  have hrt : r ≠ ⊤ := ne_top_of_lt hr3
  obtain ⟨W, hW⟩ := exists_isRep hrt w
  obtain ⟨Λ, hm, hwin, hper, hfin⟩ := h1 hloc r hr1 hrt P hP ν hν μ f w hf W hW
  obtain ⟨a, ha⟩ := h2 r hrt P ν w W hW Λ hm hwin hper hfin
  exact mem_D.2 ⟨⟨a, ha⟩, ⟨_, hasPhaseOp_drift_of hf ha⟩⟩

end UnforcedLeray.Short.PartIIa
