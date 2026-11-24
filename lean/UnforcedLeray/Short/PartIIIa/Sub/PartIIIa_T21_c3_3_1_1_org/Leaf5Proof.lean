import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org
import UnforcedLeray.Short.PartIIb.Tasks.FreeCylinderBound
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Leaf (e): `FreeFlowAvailExists` from `freeCylinderBound_proof` (SP 2074-2118, 2937-2958)

The `Params` of `PartII-b` is built from the train `tr` itself (`c = ν⁻²`, `ε = e^{-1/ν}`,
`Σ = (ν b)⁻¹`, `d = d₋ = d₊ = 1`); `BgRegime` holds because `tr` is of the BUC class
(`PartI.trainStreamSmooth` for the smoothness of the stream).  The ages `s ≤ t₂` lie below
`Σ/ν` because `b ≤ θ(t₂) = (ν (1 + ν t₂))⁻¹`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
namespace UnforcedLeray.Short.IIIa
namespace ComplFreeRateSub

theorem freeFlowAvailExists_proof (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ b : ℝ) : FreeFlowAvailExists ν m tr t₁ t₂ b := by
  intro hm hν ht₁ h12 htr hb hbt hTC s hs f hf
  have hSig : 0 < (ν * b)⁻¹ := inv_pos.2 (mul_pos hν hb)
  obtain ⟨Cm, C, b', _, _, _, hF⟩ := UnforcedLeray.Short.IIb.freeCylinderBound_proof m hm _ hSig
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  let p : UnforcedLeray.Cons.C03.Concrete.Params :=
    { ν := ν, c := ν ^ (-2 : ℝ), ε := Real.exp (-1 / ν), ageCut := (ν * b)⁻¹,
      mode := fun _ => 0, ν_pos := hν, c_pos := hc, ε_pos := Real.exp_pos _,
      ageCut_pos := hSig, trainData := tr }
  have hBg : UnforcedLeray.Short.IIb.BgRegime p 1 1 1 :=
    { dm_pos := one_pos, dm_le := le_rfl, le_dp := le_rfl,
      eps_eq := rfl,
      c_eq := by
        show ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹
        rw [Real.rpow_neg hν.le]; norm_cast
      train_buc := htr,
      train_stream_smooth := UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc tr htr }
  have hθ : b ≤ (ν * (1 + ν * t₂))⁻¹ := hbt
  have ht2 : t₂ ≤ (ν * b)⁻¹ / ν := by
    have h1 : 0 < ν * (1 + ν * t₂) := by
      have : 0 ≤ t₂ := ht₁.trans h12
      positivity
    have h2 := mul_le_mul_of_nonneg_right hθ h1.le
    rw [inv_mul_cancel₀ h1.ne'] at h2
    have hνb : 0 < ν * b := mul_pos hν hb
    have key : t₂ * ν * (ν * b) ≤ 1 := by nlinarith [h2, hνb]
    rw [le_div_iff₀ hν]
    calc t₂ * ν = (t₂ * ν * (ν * b)) * (ν * b)⁻¹ := by field_simp
      _ ≤ 1 * (ν * b)⁻¹ := by gcongr
      _ = (ν * b)⁻¹ := one_mul _
  obtain ⟨ω, hω, -⟩ := hF p 1 1 1 hBg 1 zero_le_one hTC s s (ht₁.trans hs.1) le_rfl
    (hs.2.trans ht2) f (hf.memLp m)
  exact ⟨ω, hω⟩

end ComplFreeRateSub
end UnforcedLeray.Short.IIIa
