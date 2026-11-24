import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0223

/-- Component `i` of a smooth `ℂ²`-valued function is smooth. -/
theorem nzfpCompProj (i : Fin 2) (a : ℝ × ℝ → MeridC) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun x => a x i) :=
  ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp ha

/-- A component of a band-supported `ℂ²`-valued function is band-supported. -/
theorem nzfpCompBand (i : Fin 2) (a : ℝ × ℝ → MeridC)
    (hb : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, a x ≠ 0 → x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L) :
    NzBand2 (fun x => a x i) := by
  obtain ⟨s0, s1, L, h0, hL⟩ := hb
  unfold NzBand2
  refine ⟨s0, s1, L, h0, fun x hx => hL x (fun h => hx ?_)⟩
  simp [h]

theorem nzFpComp : UnforcedLeray.Short.PartIIa.NzFpComp := by
  unfold NzFpComp
  intro a ha hb
  exact ⟨nzfpCompProj 0 a ha, nzfpCompProj 1 a ha, nzfpCompBand 0 a hb, nzfpCompBand 1 a hb⟩

end UnforcedLeray.Short.PartIIa
