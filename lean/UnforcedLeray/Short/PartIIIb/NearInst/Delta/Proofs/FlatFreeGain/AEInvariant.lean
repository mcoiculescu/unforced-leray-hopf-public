import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.Props

/-!
# `FreeSolAEInvariant` (item `PartIII-b:C/near/delta/7/1`)

Source `the November 2 reference manuscript` 3426-3440: the causal energy class
only sees the source `F` through the integrable weak identity on `(0,∞) × cell`. Since the age
measure `ageμ c a` charges every set of positive Lebesgue measure in `(0,∞) × cell`, a.e. equality
for `ageμ c (-1/2)` implies a.e. equality for `volume.restrict ((0,∞) × cell)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- `volume` on `(0,∞) × cell` is absolutely continuous w.r.t. the age measure (`c > 0`). -/
theorem restrict_ac_ageμ {c : ℝ} (hc : 0 < c) (a : ℝ) :
    volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) ≪ ageμ c a := by
  have hset : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  have h1 : volume.restrict (Ioi (0 : ℝ)) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a) := by
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow a).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx a)).ne'
  have h2 : volume.restrict (UnforcedLeray.B0579.cell c) ≪ UnforcedLeray.Cyl.avgμ c := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [← hset]
    exact Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  have h3 := Measure.AbsolutelyContinuous.prod h1 h2
  rw [Measure.prod_restrict] at h3
  unfold ageμ
  exact h3

theorem freeSolAEInvariant : FreeSolAEInvariant := by
  intro c ν μ hc F F' b G hsol hae
  have hae' : ∀ᵐ p ∂ageμ c (-1 / 2), F p = F' p := hae
  have hcore : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      F p = F' p := (restrict_ac_ageμ hc (-1 / 2)).ae_le hae'
  have hfun : ∀ Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ,
      ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
        UnforcedLeray.Short.IIIa.flatIntegrand ν μ (fun _ _ _ => 0) F b Φ p =
          UnforcedLeray.Short.IIIa.flatIntegrand ν μ (fun _ _ _ => 0) F' b Φ p := by
    intro Φ
    filter_upwards [hcore] with p hp
    unfold UnforcedLeray.Short.IIIa.flatIntegrand
    rw [hp]
  refine { hsol with
    integrable := ?_
    weak := ?_ }
  · intro Φ hΦ
    exact (hsol.integrable Φ hΦ).congr_fun_ae (hfun Φ)
  · intro Φ hΦ
    exact (integral_congr_ae (hfun Φ)).symm.trans (hsol.weak Φ hΦ)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
