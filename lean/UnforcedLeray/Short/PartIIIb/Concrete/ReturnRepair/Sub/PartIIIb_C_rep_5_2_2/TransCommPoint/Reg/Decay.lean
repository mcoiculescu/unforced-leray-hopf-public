import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Cont
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Reg.Struct
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3

/-!
# `StreamDecay` for `X₀ = sepX0`

Source `the November 2 reference manuscript` 4177-4179.  From the uniform half-plane
majorants `|ρ X₀(ρ,0,z)|, |ρ ∂_zX₀(ρ,0,z)| ≤ C (ρ - r_o)^{-3/2}` (`Int/Half2.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcr_streamDecay {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ : ℝ) :
    StreamDecay ν R (sepX0 ν μ T) τ := by
  intro r z hr
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  obtain ⟨Cb, hCb, hb⟩ := tcd_half hν hμ hr0 hP hT hM hr
  refine ⟨⟨fun ρ => Cb * (ρ - R * Real.sqrt (5 * ν / 6)) ^ (-(3 / 2 : ℝ)), ?_, ?_⟩, ?_⟩
  · exact (tcd_int_shift _ r (by linarith)).const_mul _
  · intro ρ hρ z' _
    have h := hb τ ρ z' (le_of_lt hρ)
    refine ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs]; exact h.1
    · rw [Real.norm_eq_abs]; exact h.2.2.1
  · have hlim : Tendsto (fun ρ : ℝ => Cb * (ρ - R * Real.sqrt (5 * ν / 6)) ^ (-(3 / 2 : ℝ)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun ρ : ℝ => ρ - R * Real.sqrt (5 * ν / 6)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp h1
      simpa using h2.const_mul Cb
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop r] with ρ hρ
    have h := hb τ ρ z hρ
    rw [Real.norm_eq_abs]
    exact h.2.1

end UnforcedLeray.Short.PartIIIb.Concrete

end
