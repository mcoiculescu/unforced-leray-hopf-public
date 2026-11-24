import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `IBPLin` (source 4268-4270): additivity of the phase pairing on continuous fields

Phase tests have bounded `y`-support, so `Φ·u` is continuous with bounded `y`-support and is
integrable on the phase slab `srwfSlab P`.  The pairing is then the slab integral
(`srwf_phaseInt_eq`), and additivity and subtractivity follow from `integral_add`/`integral_sub`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The integrand `Φ·w` of a phase test against a continuous field is slab integrable. -/
theorem ibpLin_integrable {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {w : ℝ × Space → CVec3} (hw : Continuous w) :
    Integrable (fun x => dotL (Φ x) (w x)) (UnforcedLeray.Short.IIb.srwfSlab P) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  refine UnforcedLeray.B0005.integrable_slab (𝒯 := P) ?_ (R := R) ?_
  · exact (dotL.continuous.comp hΦ.continuous).clm_apply hw
  · intro t y hy
    simp [hR t y hy]

/-- The phase pairing against a continuous field is the normalised slab integral. -/
theorem ibpLin_pairF_eq {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {w : ℝ × Space → CVec3} (hw : Continuous w) :
    pairF P Φ w = P⁻¹ • ∫ z, dotL (Φ z) (w z) ∂(UnforcedLeray.Short.IIb.srwfSlab P) := by
  unfold pairF
  exact UnforcedLeray.Short.IIb.srwf_phaseInt_eq (ibpLin_integrable hΦ hw)

theorem ibpLin_proved : IBPLin := by
  intro P Φ hΦ u v hu hv
  refine ⟨?_, ?_⟩
  · have hsum : Continuous (fun x => u x + v x) := hu.add hv
    rw [ibpLin_pairF_eq hΦ hsum, ibpLin_pairF_eq hΦ hu, ibpLin_pairF_eq hΦ hv]
    have key : ∫ z, dotL (Φ z) (u z + v z) ∂(UnforcedLeray.Short.IIb.srwfSlab P) =
        (∫ z, dotL (Φ z) (u z) ∂(UnforcedLeray.Short.IIb.srwfSlab P)) +
          ∫ z, dotL (Φ z) (v z) ∂(UnforcedLeray.Short.IIb.srwfSlab P) := by
      rw [← integral_add (ibpLin_integrable hΦ hu) (ibpLin_integrable hΦ hv)]
      congr 1
      funext z
      simp [map_add]
    rw [key, smul_add]
  · have hdif : Continuous (fun x => u x - v x) := hu.sub hv
    rw [ibpLin_pairF_eq hΦ hdif, ibpLin_pairF_eq hΦ hu, ibpLin_pairF_eq hΦ hv]
    have key : ∫ z, dotL (Φ z) (u z - v z) ∂(UnforcedLeray.Short.IIb.srwfSlab P) =
        (∫ z, dotL (Φ z) (u z) ∂(UnforcedLeray.Short.IIb.srwfSlab P)) -
          ∫ z, dotL (Φ z) (v z) ∂(UnforcedLeray.Short.IIb.srwfSlab P) := by
      rw [← integral_sub (ibpLin_integrable hΦ hu) (ibpLin_integrable hΦ hv)]
      congr 1
      funext z
      simp [map_sub]
    rw [key, smul_sub]

end UnforcedLeray.Short.PartIIIb.Concrete
