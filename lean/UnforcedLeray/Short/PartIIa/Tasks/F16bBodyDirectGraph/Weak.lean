import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph.Limit
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.DivPairing
import UnforcedLeray.Short.PartIIa.Tasks.F12bPhaseInnerEqPairing

/-!


For `w ∈ D_2` and a phase test `Φ`: from `HasPhaseOp driftT w (T0D w)` against the conjugate test
and `B = -𝒯₀ᵗ + 3/4` on tests.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.F16b

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.FreeStress

variable {P : ℝ} [hP : Fact (0 < P)]

theorem dτ_conjF {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    dτ (conjF Φ) = conjF (dτ Φ) := by
  funext p
  have h := conjM.hasFDerivAt.comp p
    ((hΦ.smooth.differentiable (by simp)) p).hasFDerivAt
  have h2 : fderiv ℝ (fun p => conjM (Φ p)) p = conjM ∘SL fderiv ℝ Φ p := h.fderiv
  simp only [dτ, conjF_eq]
  rw [h2]
  rfl

theorem radialT_conjF {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    radialT (conjF Φ) = conjF (radialT Φ) := by
  funext p
  have h1 : radialT (conjF Φ) p = ∑ j : Fin 3, (p.2 j) • conjF (dy j Φ) p := by
    simp only [radialT, dy_conjF hΦ]
  rw [h1]
  simp only [conjF_eq, radialT, map_sum, map_smul]

theorem driftT_conjF {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    driftT (conjF Φ) = conjF (driftT Φ) := by
  funext p
  have h1 : driftT (conjF Φ) p = -conjF (dτ Φ) p + (1 / 2 : ℝ) • conjF (radialT Φ) p +
      (3 / 2 : ℝ) • conjF Φ p := by
    simp only [driftT, dτ_conjF hΦ, radialT_conjF hΦ]
  rw [h1]
  simp only [driftT, conjF_eq, map_add, map_neg, map_smul]

/-- `B Φ = (3/4) Φ - 𝒯₀ᵗ Φ` on smooth fields. -/
theorem Bop_eq (Φ : ℝ × Space → CVec3) :
    Bop Φ = (3 / 4 : ℝ) • Φ - driftT Φ := by
  funext p
  have h := congrFun (B0005.driftT_eq_neg_T0op Φ) p
  simp only [Bop, Pi.sub_apply, Pi.smul_apply]
  have e1 : B0005.T0op Φ p = (3 / 2 : ℝ) • Φ p - driftT Φ p := by
    rw [h]; abel
  rw [e1, ← Complex.coe_smul (3 / 4 : ℝ), ← Complex.coe_smul (3 / 2 : ℝ)]
  push_cast
  module

theorem conjF_Bop {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    conjF (Bop Φ) = (3 / 4 : ℝ) • conjF Φ - driftT (conjF Φ) := by
  rw [Bop_eq, driftT_conjF hΦ]
  funext p
  simp only [conjF_eq, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply]

/-- **The weak identity.** -/
theorem weak_identity {ν : ℝ} (w : D P ν 2) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ⟪testElem P 2 (Bop Φ), (w : Yq P 2)⟫_ℂ =
      -⟪testElem P 2 Φ, T0D w - (3 / 4 : ℂ) • (w : Yq P 2)⟫_ℂ := by
  have hc : IsPhaseTest P (conjF Φ) := (phaseInnerEqPairing P Φ hΦ).1
  have hB : IsPhaseTest P (Bop Φ) := isPhaseTest_Bop hΦ
  rw [(phaseInnerEqPairing P _ hB).2, (phaseInnerEqPairing P Φ hΦ).2, conjF_Bop hΦ,
    phasePair_sub (hc.const_smul _ |> fun h => by simpa using h) hc.driftT,
    phasePair_real_smul hc, hasPhaseOp_T0D w _ hc, map_sub, map_smul, smul_eq_mul]
  push_cast
  ring

end UnforcedLeray.Short.PartIIa.F16b
