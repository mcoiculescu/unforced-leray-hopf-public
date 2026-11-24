import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.SliceTaylor.Bounds

/-!
# Part II-a, task `PartII-a:F02/9`: uniform second-order bound on the slices of a phase test

Proves the Prop `SliceTaylor` of `Sub/F02.lean` from `adjointTaylor` (`AdjointTaylor.lean`),
the uniform slice bounds of `SliceTaylor/Bounds.lean` and the Re/Im splitting of `adjC`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- **Uniform second-order bound on the slices of a phase test** (task `PartII-a:F02/9`). -/
theorem sliceTaylor : UnforcedLeray.Short.PartIIa.SliceTaylor := by
  intro ν p P _ Φ hν hp1 hp hΦ
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨C₀, hC₀, hT⟩ := adjointTaylor ν R p hν hp1 hp
  obtain ⟨M, hM0, hM⟩ := SliceCalc.exists_uniform_bound hΦ
  refine ⟨2 * C₀ * M, mul_nonneg (mul_nonneg (by norm_num) hC₀) hM0, fun t s hs0 hs1 => ?_⟩
  have hpart : ∀ K : CVec3 →L[ℝ] Space, ‖K‖ ≤ 1 →
      eLpNorm (fun y => SliceCalc.Xk ν s K t Φ y) p volume ≤ ENNReal.ofReal (C₀ * M * s ^ 2) := by
    intro K hK
    have hu : ContDiff ℝ ∞ (fun z : Space => K (Φ (t, z))) :=
      K.contDiff.comp (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id))
    have hsupp : ∀ y : Space, R < ‖y‖ → (fun z : Space => K (Φ (t, z))) y = 0 :=
      fun y hy => by
        show K (Φ (t, y)) = 0
        rw [hR t y hy, map_zero]
    exact hT M _ hu hsupp (fun y => hM K hK t y) s hs0 hs1
  have hfun : (fun y : Space => adjC ν s (fun z => Φ (t, z)) y - Φ (t, y) -
      (s : ℂ) • F02.genT ν Φ (t, y)) =
      fun y => ofReV (SliceCalc.Xk ν s reV t Φ y) + ofImV (SliceCalc.Xk ν s imV t Φ y) :=
    funext fun y => SliceCalc.decomp_adjC ν s t hΦ.smooth y
  have hm1 : AEStronglyMeasurable (fun y => ofReV (SliceCalc.Xk ν s reV t Φ y)) volume :=
    (ofReV.continuous.measurable.comp
      (SliceCalc.measurable_Xk ν s reV t hΦ.smooth)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun y => ofImV (SliceCalc.Xk ν s imV t Φ y)) volume :=
    (ofImV.continuous.measurable.comp
      (SliceCalc.measurable_Xk ν s imV t hΦ.smooth)).aestronglyMeasurable
  have hnn : 0 ≤ C₀ * M * s ^ 2 := mul_nonneg (mul_nonneg hC₀ hM0) (sq_nonneg s)
  rw [hfun]
  calc eLpNorm (fun y => ofReV (SliceCalc.Xk ν s reV t Φ y) + ofImV (SliceCalc.Xk ν s imV t Φ y))
        p volume
      ≤ eLpNorm (fun y => ofReV (SliceCalc.Xk ν s reV t Φ y)) p volume +
          eLpNorm (fun y => ofImV (SliceCalc.Xk ν s imV t Φ y)) p volume :=
        eLpNorm_add_le hm1 hm2 hp1
    _ ≤ eLpNorm (SliceCalc.Xk ν s reV t Φ) p volume +
          eLpNorm (SliceCalc.Xk ν s imV t Φ) p volume :=
        add_le_add (SliceCalc.eLpNorm_clm_le ofReV norm_ofReV_le _ p)
          (SliceCalc.eLpNorm_clm_le ofImV norm_ofImV_le _ p)
    _ ≤ ENNReal.ofReal (C₀ * M * s ^ 2) + ENNReal.ofReal (C₀ * M * s ^ 2) :=
        add_le_add (hpart reV norm_reV_le) (hpart imV norm_imV_le)
    _ = ENNReal.ofReal (2 * C₀ * M * s ^ 2) := by
        rw [← ENNReal.ofReal_add hnn hnn]
        congr 1
        ring

end UnforcedLeray.Short.PartIIa
