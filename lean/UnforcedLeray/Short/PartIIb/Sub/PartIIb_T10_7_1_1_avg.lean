import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# `PartII-b:T10/7/1/1` helper: joint-equivariance version of `Axi.ae_eq_avgLift`

Source: `the November 2 reference manuscript` 112-116, 1912-1921.
`Axi.ae_eq_avgLift` assumes slice-wise `IsAxisymmetricNoSwirl`; here only the joint a.e.
equivariance `GLEquivar` (rotations for each angle, one reflection) is available.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Axi

/-- Joint-equivariance version of `Axi.ae_eq_avgLift`: a measurable `𝒪`-equivariant field is a.e.
`A_r e_r + A_z e_3` with its angular averages. -/
theorem glAvgLift {W : ℝ × Space → Space} (hW : Measurable W) (hE : GLEquivar W) :
    W =ᵐ[volume] fun x => avgR W (x.1, mer x.2) • eR x.2 + avgZ W (x.1, mer x.2) • e3 := by
  have hvol : (volume : Measure (ℝ × Space)) = (volume : Measure ℝ).prod volume :=
    Measure.volume_eq_prod _ _
  obtain ⟨hrot, hrefl⟩ := hE
  rw [hvol] at hrefl ⊢
  have hrot : ∀ θ : ℝ, ∀ᵐ x ∂(volume : Measure ℝ).prod volume,
      W (x.1, rotZ θ x.2) = rotZ θ (W x) := fun θ => by rw [← hvol]; exact hrot θ
  have hR : ∀ θ : ℝ, ∀ᵐ x ∂(volume : Measure ℝ).prod volume,
      radC W (x.1, rotZ θ x.2) = radC W x := by
    intro θ
    filter_upwards [hrot θ] with x hx
    simp only [radC]
    rw [hx, eR_map (fixesAxis_rotZ θ), LinearIsometryEquiv.inner_map_map]
  have hZ : ∀ θ : ℝ, ∀ᵐ x ∂(volume : Measure ℝ).prod volume,
      axC W (x.1, rotZ θ x.2) = axC W x := by
    intro θ
    filter_upwards [hrot θ] with x hx
    simp only [axC]
    rw [hx, apply_two_map (fixesAxis_rotZ θ)]
  have hA : ∀ᵐ x ∂(volume : Measure ℝ).prod volume, aziC W x = 0 := by
    have hrotA : ∀ θ : ℝ, ∀ᵐ x ∂(volume : Measure ℝ).prod volume,
        aziC W (x.1, rotZ θ x.2) = aziC W x := by
      intro θ
      filter_upwards [hrot θ] with x hx
      simp only [aziC]
      rw [hx, eΦ_rotZ, LinearIsometryEquiv.inner_map_map]
    have havg := ae_eq_angAvg (measurable_aziC hW) hrotA
    have hmp : MeasurePreserving (Prod.map id reflY)
        ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
      (MeasurePreserving.id _).prod reflY.measurePreserving
    have havg' := hmp.quasiMeasurePreserving.ae havg
    filter_upwards [havg, havg', hrefl] with x h1 h2 h3
    change aziC W (x.1, reflY x.2) = angAvg (aziC W) (x.1, mer (reflY x.2)) at h2
    have h4 : aziC W (x.1, reflY x.2) = -aziC W x := by
      simp only [aziC]
      rw [h3, eΦ_reflY, inner_neg_right, LinearIsometryEquiv.inner_map_map]
    rw [mer_map fixesAxis_reflY, ← h1, h4] at h2
    linarith
  filter_upwards [ae_eq_angAvg (measurable_radC hW) hR, ae_eq_angAvg (measurable_axC hW) hZ,
    hA, Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis]
    with x h1 h2 h3 h4
  simp only [avgR, avgZ]
  rw [← h1, ← h2]
  conv_lhs => rw [eq_frame_decomp h4 (W x)]
  simp only [aziC] at h3
  rw [h3, zero_smul, add_zero]
  rfl

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.glAvgLift
