import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!
# Part II-b, task `PartII-b:T15/2/1`: change of variable `s = e^t` for the age-weighted measure

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (drift
identity; its analytic input is the weak product rule in the measure `s^{-3/2} ds`). The statement
`ExpChartIntegral` is `Sub/T15_2.lean`, lines 78-88.

`E(t, z) = (e^t, z)` on `Coord = ℝ × (ℝ × ℝ)` is a measurable embedding. The one-dimensional map
`exp` carries `e^{(a+1)t} dt` to `s^a ds` on `(0, ∞)`, and `Cyl.avgμ c` is untouched. Hence the
pushforward of `e^{(a+1)t}` times `logMeas c` under `E` is `Axi.ageμ c a`. The three identities
then follow from `MeasurableEmbedding.lintegral_map` and `MeasurableEmbedding.integral_map`, which
need no integrability hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

/-! ## One-dimensional change of variable `s = e^t` -/

/-- The image of `e^{(a+1)t} dt` under `exp` is `s^a ds` restricted to `s > 0`. -/
theorem map_exp_withDensity (a : ℝ) :
    Measure.map Real.exp
        (volume.withDensity fun t : ℝ => ENNReal.ofReal (Real.exp ((a + 1) * t))) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s : ℝ => ENNReal.ofReal (s ^ a) := by
  ext S hS
  have hT : MeasurableSet (Real.exp ⁻¹' S) := Real.continuous_exp.measurable hS
  rw [Measure.map_apply Real.continuous_exp.measurable hS, withDensity_apply _ hT,
    withDensity_apply _ hS, Measure.restrict_restrict hS]
  have h1 := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    hT (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun s : ℝ => ENNReal.ofReal (s ^ a))
  rw [Set.image_preimage_eq_inter_range, Real.range_exp] at h1
  refine (lintegral_congr fun t => ?_).trans h1.symm
  show ENNReal.ofReal (Real.exp ((a + 1) * t)) =
    ENNReal.ofReal |Real.exp t| * ENNReal.ofReal ((Real.exp t) ^ a)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos t),
    Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_add,
    show (a + 1) * t = t + t * a by ring]

/-! ## The time change `E(t, z) = (e^t, z)` on the logarithmic chart -/

/-- The time change `E(t, z) = (e^t, z)` on `Coord` (tex 7493 analogue, `θ = e^t`). -/
abbrev expCoordE (x : Coord) : Coord := (Real.exp x.1, x.2)

theorem measurable_expCoordE : Measurable expCoordE := by
  unfold expCoordE; fun_prop

theorem range_expCoordE : range expCoordE = Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    rw [mem_prod]
    exact ⟨mem_Ioi.2 (Real.exp_pos x.1), mem_univ _⟩
  · intro hp
    rw [mem_prod] at hp
    refine mem_range.2 ⟨(Real.log p.1, p.2), ?_⟩
    exact Prod.ext (Real.exp_log (mem_Ioi.1 hp.1)) rfl

theorem measurableEmbedding_expCoordE : MeasurableEmbedding expCoordE := by
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun p : ℝ × (ℝ × ℝ) => (Real.log p.1, p.2)) measurable_expCoordE ?_ ?_ ?_
  · rw [range_expCoordE]
    exact measurableSet_Ioi.prod MeasurableSet.univ
  · fun_prop
  · intro x
    simp

/-! ## The pushforward of the weighted logarithmic measure is the age-weighted measure -/

/-- The pushforward of `e^{(a+1)t}` times `logMeas c` under `E` is `Axi.ageμ c a`. -/
theorem map_expCoordE_withDensity (c a : ℝ) :
    Measure.map expCoordE
        ((logMeas c).withDensity fun x : Coord => ENNReal.ofReal (Real.exp ((a + 1) * x.1))) =
      Axi.ageμ c a := by
  have hsf : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have hρ : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp ((a + 1) * t)) := by
    fun_prop
  have hprod : ((volume : Measure ℝ).withDensity fun t : ℝ =>
      ENNReal.ofReal (Real.exp ((a + 1) * t))).prod (Cyl.avgμ c) =
      (logMeas c).withDensity fun x : Coord => ENNReal.ofReal (Real.exp ((a + 1) * x.1)) :=
    prod_withDensity_left hρ
  have hexp : Measurable Real.exp := Real.continuous_exp.measurable
  have hE : expCoordE = Prod.map Real.exp id := rfl
  rw [← hprod, hE, ← Measure.map_prod_map _ _ hexp measurable_id, Measure.map_id,
    map_exp_withDensity a]
  rfl

/-! ## The three change-of-variable identities -/

/-- **Leaf `PartII-b:T15/2/1`** (change of variable `s = e^t`): the lower integral and the real
and complex Bochner integrals of `f` against `Axi.ageμ c a` equal those of the weighted
logarithmic integrand `e^{(a+1)t} f(e^t, y)` against `logMeas c`. -/
theorem expChartIntegral : ExpChartIntegral := by
  intro c a _hc
  have hmap := map_expCoordE_withDensity c a
  have hρ : Measurable fun x : Coord => ENNReal.ofReal (Real.exp ((a + 1) * x.1)) := by
    fun_prop
  have hR : Measurable fun x : Coord => (Real.exp ((a + 1) * x.1)).toNNReal :=
    Measurable.real_toNNReal (by fun_prop)
  have hden : (fun x : Coord => ENNReal.ofReal (Real.exp ((a + 1) * x.1))) =
      fun x : Coord => ((Real.exp ((a + 1) * x.1)).toNNReal : ℝ≥0∞) := rfl
  refine ⟨fun f _hf => ?_, fun f => ?_, fun f => ?_⟩
  · rw [← hmap, measurableEmbedding_expCoordE.lintegral_map]
    exact lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρ
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _
  · rw [← hmap, measurableEmbedding_expCoordE.integral_map, hden,
      integral_withDensity_eq_integral_smul hR]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, smul_eq_mul]
  · rw [← hmap, measurableEmbedding_expCoordE.integral_map, hden,
      integral_withDensity_eq_integral_smul hR]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Complex.real_smul

end UnforcedLeray.Short.IIb
