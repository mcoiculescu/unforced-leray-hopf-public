import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Units.B0224.FiberHeat

/-!
# Periodic extension of an `L²(strip)` field (helper for `pepsC0SliceOrthCell`)

Source `the November 2 reference manuscript` 1650-1656, 1676.  Given a `ℂ²`-valued
field `v` that is `L²` on the strip `(0,c] × ℝ`, its `c`-periodic extension
`w(q,η) = v(reduceIoc q, η)` agrees with `v` on the strip and is `L²` on the centred cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem periodic_extension_L2 {c : ℝ} (hc : 0 < c) (v : ℝ × ℝ → Fin 2 → ℂ)
    (hv : MemLp (fun x => toMC (v x)) 2 (volume.restrict (stripSet c))) :
    ∃ w : ℝ × ℝ → Fin 2 → ℂ, (∀ q η, w (q + c, η) = w (q, η)) ∧
      (∀ᵐ x ∂(volume.restrict (stripSet c)), w x = v x) ∧
      MemLp (fun x => toMC (w x)) 2 (UnforcedLeray.Cyl.cellμ c) := by
  obtain ⟨G, hGsm, hGae⟩ := hv.aestronglyMeasurable
  have hGm : Measurable G := hGsm.measurable
  have hR : Measurable (fun x : ℝ × ℝ => (UnforcedLeray.B0220.reduceIoc c x.1, x.2)) :=
    ((UnforcedLeray.B0220.measurable_reduceIoc c).comp measurable_fst).prodMk measurable_snd
  refine ⟨fun x => (G (UnforcedLeray.B0220.reduceIoc c x.1, x.2)).ofLp, ?_, ?_, ?_⟩
  · intro q η
    show (G (UnforcedLeray.B0220.reduceIoc c (q + c), η)).ofLp
      = (G (UnforcedLeray.B0220.reduceIoc c q, η)).ofLp
    rw [UnforcedLeray.B0220.reduceIoc_add hc]
  · filter_upwards [hGae, ae_restrict_mem (UnforcedLeray.B0224.measurableSet_strip c)] with x hx hxs
    have hred : UnforcedLeray.B0220.reduceIoc c x.1 = x.1 :=
      UnforcedLeray.B0220.reduceIoc_of_mem hc hxs.1
    have hx' : G (x.1, x.2) = toMC (v x) := hx.symm
    show (G (UnforcedLeray.B0220.reduceIoc c x.1, x.2)).ofLp = v x
    rw [hred, hx']
    rfl
  · have hfin0 : ∫⁻ x in stripSet c, ENNReal.ofReal (‖toMC (v x)‖ ^ 2) < ∞ := by
      have hL := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
      have hnn : 0 ≤ᵐ[volume.restrict (stripSet c)] fun x => ‖toMC (v x)‖ ^ 2 :=
        Eventually.of_forall fun x => by positivity
      exact (hasFiniteIntegral_iff_ofReal hnn).1 hL.2
    have hfG : ∫⁻ x in stripSet c, ENNReal.ofReal (‖G x‖ ^ 2) < ∞ := by
      have heq : (fun x => ENNReal.ofReal (‖G x‖ ^ 2)) =ᵐ[volume.restrict (stripSet c)]
          (fun x => ENNReal.ofReal (‖toMC (v x)‖ ^ 2)) :=
        hGae.mono fun x hx => by simp only [hx]
      exact (lintegral_congr_ae heq).trans_lt hfin0
    have hper : UnforcedLeray.Cyl.IsPeriodic c
        (fun z : ℝ × ℝ => ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c z.1, z.2)‖ ^ 2)) := by
      intro z
      show ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c (z.1 + c), z.2)‖ ^ 2)
        = ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c z.1, z.2)‖ ^ 2)
      rw [UnforcedLeray.B0220.reduceIoc_add hc]
    have hcell_lint : ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c z.1, z.2)‖ ^ 2)
        = ∫⁻ z in stripSet c, ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c z.1, z.2)‖ ^ 2) :=
      (UnforcedLeray.B0224.lintegral_strip_eq_cell hc hper).symm
    have hstrip_eq : ∫⁻ z in stripSet c,
        ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c z.1, z.2)‖ ^ 2)
        = ∫⁻ z in stripSet c, ENNReal.ofReal (‖G z‖ ^ 2) :=
      setLIntegral_congr_fun (UnforcedLeray.B0224.measurableSet_strip c) fun z hz => by
        rw [UnforcedLeray.B0220.reduceIoc_of_mem hc hz.1]
    have hfinCell : ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ENNReal.ofReal (‖G (UnforcedLeray.B0220.reduceIoc c z.1, z.2)‖ ^ 2) < ∞ := by
      rw [hcell_lint, hstrip_eq]
      exact hfG
    have hfun : (fun x : ℝ × ℝ => toMC ((G (UnforcedLeray.B0220.reduceIoc c x.1, x.2)).ofLp))
        = fun x => G (UnforcedLeray.B0220.reduceIoc c x.1, x.2) :=
      funext fun x => by simp [toMC]
    show MemLp (fun x : ℝ × ℝ => toMC ((G (UnforcedLeray.B0220.reduceIoc c x.1, x.2)).ofLp)) 2
      (UnforcedLeray.Cyl.cellμ c)
    rw [hfun]
    have hnn : 0 ≤ᵐ[UnforcedLeray.Cyl.cellμ c]
        fun x : ℝ × ℝ => ‖G (UnforcedLeray.B0220.reduceIoc c x.1, x.2)‖ ^ 2 :=
      Eventually.of_forall fun x => by positivity
    refine (memLp_two_iff_integrable_sq_norm (hGm.comp hR).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact ((hGm.comp hR).norm.pow_const 2).aestronglyMeasurable
    · exact (hasFiniteIntegral_iff_ofReal hnn).2 hfinCell

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
