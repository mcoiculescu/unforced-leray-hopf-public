import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Lin.Helpers

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/3` (`StrPairLin`): linearity of the stress pairing on `StrG`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem strPairLin_proved : UnforcedLeray.Short.PartIIIb.Concrete.StrPairLin := by
  intro c mZ ρb γ ν ε hc hν hε hρ Φ hΦ
  obtain ⟨Y, K, hK, hB⟩ := strChartBound_proved c ε hc hε Φ hΦ
  have hI : ∀ T : StrG c mZ ρb γ ν,
      Integrable (fun x : ℝ × Space =>
        ∑ i : Fin 3, ∑ j : Fin 3, ((strPhys ε⁻¹ c (strSum T) x i j : ℝ) : ℂ) * dy j Φ x i)
        (volume.restrict (phaseCell (2 * ε * c))) := fun T =>
    (hB (strSum T) (strSum_measurable_lin T)
      (lintegral_rpow_two_lt_top_lin (memLp_region_strSum_lin hν hρ Y T))).1
  refine ⟨?_, ?_⟩
  · intro T T'
    unfold strPairVal
    rw [UnforcedLeray.Short.PartIIIb.NearInst.stressPairAE c ε hc hε _ _ (strSum_add_ae_lin hν hρ T T') Φ, strPhys_add_lin,
      stressPair_add_lin (hI T) (hI T')]
  · intro a T
    unfold strPairVal
    rw [UnforcedLeray.Short.PartIIIb.NearInst.stressPairAE c ε hc hε _ _ (strSum_smul_ae_lin hν hρ a T) Φ, strPhys_smul_lin,
      stressPair_smul_lin]
