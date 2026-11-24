import UnforcedLeray.Units.B0449.TimeST
import UnforcedLeray.Lib.HeatR3B.SpaceTime
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# B0449, step 2: jointly measurable charts of a graph element

Blueprint unit B0449 (`eq:free-stress-5`), manuscript `paper/main.tex` lines 7635–7641 and
7681–7683. The manuscript fixes an observation point `(τ₀, y₀)` and sets
`W(t, z) = w(τ₀ + t, e^{-t/2}(y₀ + √ν z))`. We use `y₀ = 0`: the spatial part
`z ↦ e^{-t/2}√ν z` of the chart is then onto `ℝ³` for every `t`, so one chart per phase `τ₀`
covers the whole slab `{τ₀ + t} × ℝ³`, and only charts with different `τ₀` have to be glued
("these representatives agree on overlapping charts", tex 7682–7683).

`w ∈ Y_q` is a class of maps `ℝ/Pℤ → L^q(ℝ³)`. Space-time statements need a jointly measurable
representative: `jointRep f` (from the drafted `Infra/JointMeasurableRep`, which works for any
strongly measurable `L^q`-valued path), and the chart `chartJ f ν τ₀ (t, z) =
jointRep f (τ₀ + t, e^{-t/2}√ν z)`. For every `t`, its slice is the chart pullback of
B0447 a.e. in `z` (`chartJ_slice`, `chartJ_slice_lp`).

Also: the chart change between two phases (`chartJ_shift`), periodicity in the phase
(`chartJ_add_period`), and quasi-measure preservation of the chart change (`qmp_shift`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.BochnerTime

/-- The spatial scale `e^{-t/2}√ν` of the comoving chart at time `t` (tex 7640, `y₀ = 0`). -/
def sc (ν t : ℝ) : ℝ := Real.exp (-t / 2) * Real.sqrt ν

theorem sc_pos {ν : ℝ} (hν : 0 < ν) (t : ℝ) : 0 < sc ν t :=
  mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 hν)

theorem continuous_sc (ν : ℝ) : Continuous (sc ν) := by
  unfold sc; fun_prop

theorem chart_snd_zero (ν τ₀ t : ℝ) (z : Space) :
    (comovingChart ν τ₀ 0 t z).2 = sc ν t • z := by
  rw [chart_snd]; simp [sc]

/-- Scalings of `ℝ³` are quasi-measure-preserving. -/
theorem qmp_smul {b : ℝ} (hb : b ≠ 0) :
    Measure.QuasiMeasurePreserving (fun z : Space => b • z) volume volume :=
  ⟨measurable_const_smul b, by rw [map_smul_space hb]; exact Measure.smul_absolutelyContinuous⟩

/-- The chart change `(s, z) ↦ (s + d, e^{d/2} z)` of `ℝ × ℝ³` is quasi-measure-preserving. -/
theorem qmp_shift (d : ℝ) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × Space => (p.1 + d, Real.exp (d / 2) • p.2))
      volume volume := by
  have hne : Real.exp (d / 2) ≠ 0 := (Real.exp_pos _).ne'
  have e : (fun p : ℝ × Space => (p.1 + d, Real.exp (d / 2) • p.2)) =
      Prod.map (fun s : ℝ => s + d) (fun z : Space => Real.exp (d / 2) • z) := rfl
  rw [e]
  refine ⟨(measurable_add_const d).prodMap (measurable_const_smul _), ?_⟩
  rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (measurable_add_const d)
    (measurable_const_smul _), (measurePreserving_add_right volume d).map_eq, map_smul_space hne]
  exact Measure.AbsolutelyContinuous.rfl.prod Measure.smul_absolutelyContinuous

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem exists_jointRep (f : Yq P q) :
    ∃ G : AddCircle P × Space → CVec3, StronglyMeasurable G ∧
      ∀ τ, (fun y => G (τ, y)) =ᵐ[volume] (f τ : Space → CVec3) :=
  UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep (Lp.stronglyMeasurable f)

/-- A jointly strongly measurable representative of `f ∈ Y_q` on `ℝ/Pℤ × ℝ³`, whose slice at
**every** phase `τ` represents `f(τ) ∈ L^q(ℝ³)`. -/
def jointRep (f : Yq P q) : AddCircle P × Space → CVec3 :=
  Classical.choose (exists_jointRep f)

theorem stronglyMeasurable_jointRep (f : Yq P q) : StronglyMeasurable (jointRep f) :=
  (Classical.choose_spec (exists_jointRep f)).1

theorem jointRep_slice (f : Yq P q) (τ : AddCircle P) :
    (fun y => jointRep f (τ, y)) =ᵐ[volume] (f τ : Space → CVec3) :=
  (Classical.choose_spec (exists_jointRep f)).2 τ

/-- The chart `W(t, z) = w(τ₀ + t, e^{-t/2}√ν z)` (tex 7640 with `y₀ = 0`), built on the joint
representative. -/
def chartJ (f : Yq P q) (ν τ₀ : ℝ) (p : ℝ × Space) : CVec3 :=
  jointRep f (((τ₀ + p.1 : ℝ) : AddCircle P), sc ν p.1 • p.2)

omit [Fact (0 < P)] [Fact (1 ≤ q)] in
theorem measurable_chartMap (ν τ₀ : ℝ) :
    Measurable (fun p : ℝ × Space => (((τ₀ + p.1 : ℝ) : AddCircle P), sc ν p.1 • p.2)) := by
  refine Measurable.prodMk ?_ ?_
  · exact ((AddCircle.continuous_mk' P).comp (continuous_const.add continuous_fst)).measurable
  · exact (((continuous_sc ν).comp continuous_fst).smul continuous_snd).measurable

theorem stronglyMeasurable_chartJ (f : Yq P q) (ν τ₀ : ℝ) :
    StronglyMeasurable (chartJ f ν τ₀) :=
  (stronglyMeasurable_jointRep f).comp_measurable (measurable_chartMap ν τ₀)

/-- The slice of the joint chart is the chart pullback of B0447 (a.e. in `z`), for every `t`. -/
theorem chartJ_slice {ν : ℝ} (hν : 0 < ν) (f : Yq P q) (τ₀ t : ℝ) :
    (fun z => chartJ f ν τ₀ (t, z)) =ᵐ[volume] chartPullback f ν τ₀ 0 t := by
  have h := (qmp_smul (sc_pos hν t).ne').ae_eq_comp
    (jointRep_slice f ((τ₀ + t : ℝ) : AddCircle P))
  refine h.trans (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, chartPullback, chart_snd_zero]
  rfl

/-- The slice of the joint chart represents the `L^q`-valued chart `chartLp` of B0447. -/
theorem chartJ_slice_lp {ν : ℝ} (hν : 0 < ν) (f : Yq P q) (τ₀ t : ℝ) :
    (fun z => chartJ f ν τ₀ (t, z)) =ᵐ[volume] (B0447.chartLp f ν τ₀ 0 t : Space → CVec3) :=
  (chartJ_slice hν f τ₀ t).trans (B0447.coeFn_chartLp hν f τ₀ 0 t).symm

/-- **Chart change** (tex 7682–7683): the chart at phase `τ₀ + d` is the chart at `τ₀`
composed with `(s, z) ↦ (s + d, e^{d/2} z)`. -/
theorem chartJ_shift (f : Yq P q) (ν τ₀ d s : ℝ) (z : Space) :
    chartJ f ν (τ₀ + d) (s, z) = chartJ f ν τ₀ (s + d, Real.exp (d / 2) • z) := by
  simp only [chartJ]
  congr 2
  · congr 1; ring
  · rw [smul_smul]
    congr 1
    simp only [sc]
    rw [mul_comm (Real.exp (-(s + d) / 2)) (Real.sqrt ν), mul_assoc, ← Real.exp_add,
      mul_comm]
    congr 2
    ring

/-- The chart is `P`-periodic in the phase. -/
theorem chartJ_add_period (f : Yq P q) (ν τ₀ : ℝ) :
    chartJ f ν (τ₀ + P) = chartJ f ν τ₀ := by
  funext p
  simp only [chartJ]
  rw [show τ₀ + P + p.1 = (τ₀ + p.1) + P by ring, AddCircle.coe_add_period]

end UnforcedLeray.B0449
