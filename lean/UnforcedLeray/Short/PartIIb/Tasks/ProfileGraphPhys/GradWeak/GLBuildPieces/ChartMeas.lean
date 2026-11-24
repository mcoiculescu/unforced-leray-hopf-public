import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_3

/-!
# Part II-b, task `PartII-b:T10/7/1/1/3/5` (`GLBuildPieces/ChartMeas`): measurability of the chart profile

Source of record: `the November 2 reference manuscript` lines 1912-1921 (chart 1639-1668).

Target: `gl_chartMeas : UnforcedLeray.Short.IIb.GLChartMeas`.

Proof outline. The inverse chart `invChart ε` is measurable (`Real.log`, `Real.sqrt`, inverse,
products). The profile `chartProf ε A B` is `Measurable.ite` on the measurable set `{0 < x.1}` of
`(x.1)⁻¹ • !₂[A ∘ invChart, B ∘ invChart]`, and `sqrtS` multiplies by the measurable scalar `√x.1`.
So `sqrtS (chartProf ε A B)` is measurable and hence a.e. strongly measurable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace ChartMeasHelp

/-- The inverse chart is measurable. -/
theorem measurable_invChart (ε : ℝ) : Measurable (invChart ε) := by
  unfold invChart
  have hsq : Measurable fun x : Coord => Real.sqrt x.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_const.mul (measurable_fst.comp measurable_snd)).add
      (Real.measurable_log.comp measurable_fst)
  · exact measurable_const.mul hsq.inv
  · exact (measurable_snd.comp measurable_snd).mul hsq.inv

end ChartMeasHelp

/-- **(CB2)** Measurability of `sqrtS (chartProf ε A B)` for measurable `A, B`. -/
theorem gl_chartMeas : UnforcedLeray.Short.IIb.GLChartMeas := by
  intro ε A B μ hA hB
  apply Measurable.aestronglyMeasurable
  have hinv : Measurable (invChart ε) := ChartMeasHelp.measurable_invChart ε
  have hAi : Measurable fun x : Coord => A (invChart ε x) := hA.comp hinv
  have hBi : Measurable fun x : Coord => B (invChart ε x) := hB.comp hinv
  have hfun : Measurable fun x : Coord => (![A (invChart ε x), B (invChart ε x)] : Fin 2 → ℂ) := by
    refine measurable_pi_iff.2 (fun i => ?_)
    fin_cases i
    · exact hAi
    · exact hBi
  have hvec : Measurable fun x : Coord =>
      (!₂[A (invChart ε x), B (invChart ε x)] : CMerid) := (WithLp.measurable_toLp (2 : ENNReal) (Fin 2 → ℂ)).comp hfun
  have hsq : Measurable fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)
  have hinvC : Measurable fun x : Coord => ((x.1 : ℝ) : ℂ)⁻¹ :=
    (Complex.measurable_ofReal.comp measurable_fst).inv
  have hcp : Measurable (chartProf ε A B) := by
    unfold chartProf
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (hinvC.smul hvec) measurable_const
  have hs : Measurable (sqrtS (chartProf ε A B)) := by
    unfold sqrtS
    exact hsq.smul hcp
  exact hs

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_chartMeas
