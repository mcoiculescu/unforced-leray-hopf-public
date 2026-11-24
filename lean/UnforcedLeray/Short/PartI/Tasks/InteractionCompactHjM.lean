import UnforcedLeray.Units.B0061
import UnforcedLeray.Units.B0064.ZeroMean

/-!
# Part I, task `PartI:S13b`: the interaction is compact on `H^j_M` and preserves `X_{j,M}`

Source of record: `the November 2 reference manuscript`, lines 853-860
(the Biot-Savart interaction `(∇^⊥Δ⁻¹f)·∇E₀` is compact on `H^j_M`, and both terms of the
generator have zero integral, so `X_{j,M}` is invariant).

Proof. The bounded gain `H^j_M → H^{j+1}_M` and the compactness of the operator on `H^j_M`
are the unit statement `UnforcedLeray.B0061.unit_statement` (B0061, `paper/main.tex:1222`).
The invariance clause holds because `∫ (Kf)·∇E₀ = 0` for every integrable `f`
(`UnforcedLeray.B0064.integral_perturbation_eq_zero`). Since `T₀ F` agrees a.e. with
`perturbation F`, the integral of `T₀ F` is zero, so `T₀ F ∈ X_{j,M}` by `mem_XjM_iff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:S13b`** (source lines 853-860): for `M > 1` and every `j`, the map
`f ↦ (Kf)·∇E₀` (`B0009.perturbation`) is bounded `H^j_M → H^{j+1}_M`; its restriction to
`H^j_M → H^j_M` is a compact operator; and it preserves `X_{j,M}`. -/
theorem interaction_isCompactOperator_HjM (j : ℕ) {M : ℝ} (hM : 1 < M) :
    (∃ T₁ : UnforcedLeray.B0008.HjM j M →L[ℂ] UnforcedLeray.B0008.HjM (j + 1) M,
      ∀ F : UnforcedLeray.B0008.HjM j M,
        ((T₁ F).value : ℂ → ℂ) =ᵐ[volume]
          UnforcedLeray.B0009.perturbation (F.value : ℂ → ℂ)) ∧
    (∃ T₀ : UnforcedLeray.B0008.HjM j M →L[ℂ] UnforcedLeray.B0008.HjM j M,
      IsCompactOperator T₀ ∧
      (∀ F : UnforcedLeray.B0008.HjM j M,
        ((T₀ F).value : ℂ → ℂ) =ᵐ[volume]
          UnforcedLeray.B0009.perturbation (F.value : ℂ → ℂ)) ∧
      ∀ F ∈ UnforcedLeray.B0008.XjM j M, T₀ F ∈ UnforcedLeray.B0008.XjM j M) := by
  obtain ⟨⟨T₁, hT₁⟩, ⟨T₀, hT₀, hC⟩⟩ := UnforcedLeray.B0061.unit_statement hM j
  refine ⟨⟨T₁, hT₁⟩, ⟨T₀, hC, hT₀, fun F _ => ?_⟩⟩
  rw [UnforcedLeray.B0008.mem_XjM_iff hM]
  have hint : ∫ y, ((T₀ F).value : ℂ → ℂ) y =
      ∫ y, UnforcedLeray.B0009.perturbation (F.value : ℂ → ℂ) y :=
    integral_congr_ae (hT₀ F)
  rw [hint]
  exact UnforcedLeray.B0064.integral_perturbation_eq_zero
    (UnforcedLeray.B0008.HjM.integrable_value hM F)

end UnforcedLeray.Short.PartI
