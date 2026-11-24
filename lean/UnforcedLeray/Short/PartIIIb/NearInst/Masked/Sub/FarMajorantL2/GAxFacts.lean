import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Facts about the axisymmetric source profile `gAx` (source 2666-2668, 2675-2683)

* axisymmetry: `chartOf R c z τ` depends on `z` only through `hRad z` and `z 2`;
* periodicity: `τ ↦ τ + 2c/R` shifts the reduced phase `q` by `c`, which the floor reduction absorbs;
* measurability of `(τ, z) ↦ gAx R c f τ z` (`chartOf` is measurable, as in `T8_1.measurable_chartOf`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

@[fun_prop]
private lemma gax_coord (ab : Fin 3 × Fin 3) : Measurable fun T : Ten3 => T ab :=
  (measurable_pi_apply ab).comp (PiLp.continuous_ofLp 2 _).measurable

private lemma gax_chart_measurable (R c : ℝ) :
    Measurable fun s : ℝ × UnforcedLeray.Space => chartOf R c s.2 s.1 := by
  unfold chartOf hRad
  have hh : Measurable fun s : ℝ × UnforcedLeray.Space =>
      Real.sqrt (s.2 0 ^ 2 + s.2 1 ^ 2) := by fun_prop
  have hL : Measurable fun s : ℝ × UnforcedLeray.Space =>
      R * Real.log (Real.sqrt (s.2 0 ^ 2 + s.2 1 ^ 2) / R) + R * s.1 / 2 := by
    fun_prop
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · fun_prop
  · have hfl : Measurable fun s : ℝ × UnforcedLeray.Space =>
        ⌊(R * Real.log (Real.sqrt (s.2 0 ^ 2 + s.2 1 ^ 2) / R) + R * s.1 / 2) / c + 1 / 2⌋ :=
      Measurable.floor ((hL.div_const c).add_const _)
    exact hL.sub (measurable_const.mul ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hfl))
  · fun_prop

private lemma gax_nsSym_entry (a b : Fin 3) : Measurable fun T : Ten3 => nsSym T a b := by
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ] <;> fun_prop

private lemma gax_tensorNorm_meas :
    Measurable fun T : Ten3 => UnforcedLeray.Short.IIIa.tensorNorm (nsSym T) := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  refine Measurable.sqrt ?_
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => (gax_nsSym_entry i j).pow_const 2))

theorem gAxFacts_holds : GAxFacts := by
  intro R c f hR hc hf
  have hR0 : R ≠ 0 := hR.ne'
  have hc0 : c ≠ 0 := hc.ne'
  refine ⟨?_, ?_, ?_⟩
  · -- axisymmetry
    intro τ z z' h1 h2
    unfold gAx chartOf
    rw [h1, h2]
  · -- periodicity in `τ`
    intro τ z
    have hA : R * Real.log (hRad z / R) + R * (τ + 2 * c / R) / 2 =
        (R * Real.log (hRad z / R) + R * τ / 2) + c := by
      field_simp
      ring
    have hfl : ⌊(R * Real.log (hRad z / R) + R * τ / 2 + c) / c + 1 / 2⌋ =
        ⌊(R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2⌋ + 1 := by
      rw [← Int.floor_add_one]
      congr 1
      field_simp
      ring
    have hchart : chartOf R c z (τ + 2 * c / R) = chartOf R c z τ := by
      unfold chartOf
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      show R * Real.log (hRad z / R) + R * (τ + 2 * c / R) / 2 -
          c * ↑⌊(R * Real.log (hRad z / R) + R * (τ + 2 * c / R) / 2) / c + 1 / 2⌋ =
        R * Real.log (hRad z / R) + R * τ / 2 - c * ↑⌊(R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2⌋
      rw [hA, hfl]
      push_cast
      ring
    unfold gAx
    rw [hchart]
  · -- measurability
    have h1 : Measurable (fun s : ℝ × UnforcedLeray.Space => (chartOf R c s.2 s.1).1) :=
      measurable_fst.comp (gax_chart_measurable R c)
    have h2 : Measurable (fun s : ℝ × UnforcedLeray.Space => f (chartOf R c s.2 s.1)) :=
      hf.comp (gax_chart_measurable R c)
    have h3 : Measurable (fun s : ℝ × UnforcedLeray.Space =>
        UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f (chartOf R c s.2 s.1)))) :=
      gax_tensorNorm_meas.comp h2
    exact ENNReal.measurable_ofReal.comp (h1.mul h3)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
