import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Lib.PhaseSpace.Charts

/-!
# Part II-a, task `PartII-a:F06/1/4`: the period integral of `Y_r` slice norms (`SliceIntegralYq`)

The period integral over `Ioc 0 P` of a function of `τ ∈ AddCircle P` equals `P` times its
Haar integral (`AddCircle.lintegral_preimage` with `volume = P • haarAddCircle`), and the
`Y_r` norms are `L^r` norms for the Haar measure (`lintegral_enorm_rpow_Yq`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

theorem sliceIntegralYq : SliceIntegralYq := by
  intro r hr hrt P hP μ f w
  -- period integral versus Haar integral on the circle
  have hslice : ∀ G : AddCircle P → ℝ≥0∞,
      ∫⁻ τ in Ioc 0 P, G (τ : AddCircle P) =
        ENNReal.ofReal P * ∫⁻ x, G x ∂AddCircle.haarAddCircle := by
    intro G
    have h1 := AddCircle.lintegral_preimage (T := P) 0 G
    rw [zero_add] at h1
    rw [h1, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul]
  have hfm : AEMeasurable (fun x : AddCircle P => ‖f x‖ₑ ^ r.toReal)
      AddCircle.haarAddCircle :=
    (((Lp.aestronglyMeasurable f).enorm).pow_const _)
  have hcne : ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have key := hslice (fun x => ‖f x‖ₑ ^ r.toReal +
    ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w x‖ₑ ^ r.toReal)
  rw [key, lintegral_add_left' hfm, lintegral_const_mul' _ _ hcne,
    lintegral_enorm_rpow_Yq f hrt, lintegral_enorm_rpow_Yq w hrt]

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.sliceIntegralYq
