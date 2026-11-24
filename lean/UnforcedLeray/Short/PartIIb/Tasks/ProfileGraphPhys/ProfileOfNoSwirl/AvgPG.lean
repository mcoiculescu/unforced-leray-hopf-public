import UnforcedLeray.Lib.AxisymmetricB.Unitary

/-!
# Rotation averaging with per-group-element hypotheses

`Axi.ae_eq_avgLift` takes the joint hypothesis `∀ᵐ t, IsAxisymmetricNoSwirl (slice)`, which quantifies
over `𝒪` inside the a.e. statement.  The phase-space no-swirl hypothesis `PhaseNoSwirl` is given one
`g` at a time, with an a.e. statement over the product measure.  This file repeats the library
argument with the per-`g` hypothesis `∀ g, FixesAxis g → ∀ᵐ x ∂μ ⊗ dy, W(x₁, g x₂) = g(W x)`;
only the instances `g = rotZ θ` and `g = reflY` are used, so no countability in `g` is needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

variable {T : Type*} [MeasurableSpace T]

theorem ae_aziC_eq_zero_pg {μ : Measure T} [SFinite μ] {W : T × Space → Space}
    (hW : Measurable W)
    (hg : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      ∀ᵐ x ∂μ.prod volume, W (x.1, g x.2) = g (W x)) :
    ∀ᵐ x ∂μ.prod volume, aziC W x = 0 := by
  have hrot : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, aziC W (x.1, rotZ θ x.2) = aziC W x := by
    intro θ
    filter_upwards [hg (rotZ θ) (fixesAxis_rotZ θ)] with x hx
    simp only [aziC]
    rw [hx, eΦ_rotZ, LinearIsometryEquiv.inner_map_map]
  have havg := ae_eq_angAvg (measurable_aziC hW) hrot
  have hmp : MeasurePreserving (Prod.map id reflY) (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).prod reflY.measurePreserving
  have havg' := hmp.quasiMeasurePreserving.ae havg
  filter_upwards [havg, havg', hg reflY fixesAxis_reflY] with x h1 h2 h3
  change aziC W (x.1, reflY x.2) = angAvg (aziC W) (x.1, mer (reflY x.2)) at h2
  have h4 : aziC W (x.1, reflY x.2) = -aziC W x := by
    simp only [aziC]
    rw [h3, eΦ_reflY, inner_neg_right, LinearIsometryEquiv.inner_map_map]
  rw [mer_map fixesAxis_reflY, ← h1, h4] at h2
  linarith

theorem ae_eq_avgLift_pg {μ : Measure T} [SFinite μ] {W : T × Space → Space}
    (hW : Measurable W)
    (hg : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      ∀ᵐ x ∂μ.prod volume, W (x.1, g x.2) = g (W x)) :
    W =ᵐ[μ.prod volume] fun x => avgR W (x.1, mer x.2) • eR x.2 + avgZ W (x.1, mer x.2) • e3 := by
  have hR : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, radC W (x.1, rotZ θ x.2) = radC W x := by
    intro θ
    filter_upwards [hg (rotZ θ) (fixesAxis_rotZ θ)] with x hx
    simp only [radC]
    rw [hx, eR_map (fixesAxis_rotZ θ), LinearIsometryEquiv.inner_map_map]
  have hZ : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, axC W (x.1, rotZ θ x.2) = axC W x := by
    intro θ
    filter_upwards [hg (rotZ θ) (fixesAxis_rotZ θ)] with x hx
    simp only [axC]
    rw [hx, apply_two_map (fixesAxis_rotZ θ)]
  filter_upwards [ae_eq_angAvg (measurable_radC hW) hR, ae_eq_angAvg (measurable_axC hW) hZ,
    ae_aziC_eq_zero_pg hW hg, Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis]
    with x h1 h2 h3 h4
  simp only [avgR, avgZ]
  rw [← h1, ← h2]
  conv_lhs => rw [eq_frame_decomp h4 (W x)]
  simp only [aziC] at h3
  rw [h3, zero_smul, add_zero]
  rfl

end UnforcedLeray.Axi
