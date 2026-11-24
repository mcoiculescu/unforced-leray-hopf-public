import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H2
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H8

/-!
# Part III-a long assembly: `LongForwardEstimate` from the good frame and the amplitude Gronwall

Task PartIII-a:T21/long (SP 3017-3030, `eq:short-causal-long-forward`). Conditional on
`GoodFrameExists` (the frame of T21/c1, stability T21/c3, amplitude T21/c5) and on
`AmplitudeGronwall` (T21/c4). The constant is `C = (1+K⁺)G⁺(1+2K⁺+2K⁺²)` with `K⁺ = max K 0`,
`G⁺ = max K_G 0`, and `ν₀ = min ν₁ ν₂` where `ν₁` comes from the frame and `ν₂` from the Gronwall
budget. The constant `C` of the frame is replaced by `C' = max |C| 1 > 0` (`frameStable_mono`,
`frameAmp_mono`), so that the Gronwall budget applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem longForwardEstimate_of (hF : GoodFrameExists) (hG : AmplitudeGronwall) :
    LongForwardEstimate := by
  intro P hP m hm
  obtain ⟨K, C, h₀, b₀F, hh₀, hFr⟩ := hF P hP m hm
  have hC'pos : 0 < max |C| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC' : |C| ≤ max |C| 1 := le_max_left _ _
  obtain ⟨KG, b₀G, hGb⟩ := hG (max |C| 1) h₀ hh₀ hC'pos
  refine ⟨max b₀F b₀G, fun b hb => ?_⟩
  obtain ⟨ν₁, hν₁, hFb⟩ := hFr b ((le_max_left _ _).trans hb)
  obtain ⟨ν₂, hν₂, hGb'⟩ := hGb b ((le_max_right _ _).trans hb)
  refine ⟨(1 + max K 0) * max KG 0 * (1 + 2 * max K 0 + 2 * max K 0 * max K 0), min ν₁ ν₂,
    lt_min hν₁ hν₂, ?_⟩
  intro ν hν tr htr t s ht hts hb f hf hz w u hw
  have hνF : ν ∈ Ioc 0 ν₁ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hνG : ν ∈ Ioc 0 ν₂ := ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  obtain ⟨F, hSt, hAm⟩ := hFb ν hνF
  have hSt' := frameStable_mono P F hν.1 hCC' hSt
  have hAm' := frameAmp_mono P F hν.1 hCC' hAm
  have key := long_core (P := P) (K := K) (KG := KG) (Kp := max K 0) (Gp := max KG 0)
    (C' := max |C| 1) (h₀ := h₀) (tr := tr) (f := f) (w := w) (u := u) F hν.1 ht hts
    (by linarith) hb htr hw hz (le_max_right _ _) (le_max_left _ _) (le_max_right _ _)
    (le_max_left _ _) hSt' hAm' (hGb' ν hνG t s ht hts hb)
  have e : (1 + max K 0) * max KG 0 * (1 + 2 * max K 0 + 2 * max K 0 * max K 0) *
      Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν s)) *
        (clockTheta ν t / clockTheta ν s) ^ P.kappa.re =
      (1 + max K 0) * max KG 0 * (1 + 2 * max K 0 + 2 * max K 0 * max K 0) * clockN P ν t s := by
    unfold clockN
    ring
  rw [e]
  exact key

end UnforcedLeray.Short.IIIa
