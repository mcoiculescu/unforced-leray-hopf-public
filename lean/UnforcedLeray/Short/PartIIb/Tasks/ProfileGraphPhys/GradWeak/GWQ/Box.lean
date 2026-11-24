import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Calc5
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: integrability against box-supported test functions
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem integrable_box_mul {f : Coord → ℂ}
    (hf : ∀ σ H R L : ℝ, 0 < σ →
      IntegrableOn f (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume)
    {ψ : Coord → ℝ} {a0 Q : ℝ} (ha0 : 0 < a0)
    (hc : ContinuousOn ψ (Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)))
    (hz : ∀ x, ψ x ≠ 0 → x ∈ Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)) :
    Integrable (fun x => f x * (ψ x : ℂ)) := by
  have hK : IsCompact (Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have h1 := hf a0 Q Q Q ha0
  have hcc : ContinuousOn (fun x => (ψ x : ℂ)) (Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have h2 : IntegrableOn (fun x => f x * (ψ x : ℂ))
      (Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)) volume := h1.mul_continuousOn hcc hK
  rw [← integrableOn_iff_integrable_of_support_subset (s := Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q))]
  · exact h2
  · intro x hx
    by_contra hn
    apply hx
    have : ψ x = 0 := by
      by_contra h
      exact hn (hz x h)
    simp [this]

theorem coord_box {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ a0 Q : ℝ, 0 < a0 ∧ ∀ x, φ x ≠ 0 → x ∈ Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q) := by
  obtain ⟨a0, Q, ha0, hQ, hs⟩ := coord_support_bounds hφ
  refine ⟨a0, Q, ha0, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hs x hx
  exact ⟨⟨h1, h2⟩, abs_le.1 h3, abs_le.1 h4⟩

end UnforcedLeray.Short.IIb.GWQ
