import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H5

/-!
# Helpers for `wardX0YoungL2_proved` (6): joint measurability of partial derivatives

Source of record: `the November 2 reference manuscript` (73 pages), 4171-4174.
A jointly measurable field differentiable in `y` on a measurable set has jointly measurable
partials there (limit of difference quotients).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

open scoped Classical in
theorem w10_meas_pd {X : ℝ → Space → Space} (hX : Measurable (fun x : ℝ × Space => X x.1 x.2))
    {U : Set Space} (hU : MeasurableSet U)
    (hd : ∀ τ y, y ∈ U → DifferentiableAt ℝ (X τ) y) (j : Fin 3) :
    Measurable (fun x : ℝ × Space => if x.2 ∈ U then physPd (X x.1) j x.2 else 0) := by
  classical
  set Gm : ℕ → ℝ × Space → Space := fun n x =>
    if x.2 ∈ U then (n : ℝ) • (X x.1 (x.2 + (n : ℝ)⁻¹ • coordinateVector j) - X x.1 x.2) else 0
    with hGm
  have hmeasU : MeasurableSet {x : ℝ × Space | x.2 ∈ U} := measurable_snd hU
  have hmeas : ∀ n, Measurable (Gm n) := by
    intro n
    refine Measurable.ite hmeasU ?_ measurable_const
    have hsub : Measurable (fun x : ℝ × Space =>
        X x.1 (x.2 + (n : ℝ)⁻¹ • coordinateVector j) - X x.1 x.2) :=
      (hX.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hX
    exact (measurable_const (a := (n : ℝ))).smul hsub
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun x => ?_)
  by_cases hx : x.2 ∈ U
  · simp only [hGm, hx, if_true]
    have hdif := hd x.1 x.2 hx
    have hγ : HasDerivAt (fun t : ℝ => X x.1 (x.2 + t • coordinateVector j))
        (fderiv ℝ (X x.1) x.2 (coordinateVector j)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => x.2 + t • coordinateVector j) (coordinateVector j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector j)).const_add x.2
      have h2 : HasFDerivAt (X x.1) (fderiv ℝ (X x.1) x.2) (x.2 + (0 : ℝ) • coordinateVector j) := by
        simpa using hdif.hasFDerivAt
      exact h2.comp_hasDerivAt 0 h1
    have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hγ)
    have hseq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop, ?_⟩
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [mem_compl_iff, mem_singleton_iff]
      exact (inv_pos.2 (by exact_mod_cast hn)).ne'
    have := hs.comp hseq
    refine (this.congr fun n => ?_).trans ?_
    · simp only [Function.comp, inv_inv, zero_add, zero_smul, add_zero]
    · simp [physPd]
  · simp only [hGm, hx, if_false]
    exact tendsto_const_nhds

end UnforcedLeray.Short.PartIIIb.Concrete
end
