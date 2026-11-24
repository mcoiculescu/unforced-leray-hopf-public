import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable.Periodic

/-!
# Part II-b, task `PartII-b:T12/3`: measurability of the causal Duhamel integral

Source of record: `the November 2 reference manuscript`, the Duhamel formula
`D G(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} G(t) dt/t` (SP 1924).

Statement: `DuhamelMeasurable` (for `1 < r < 3`, `a_r > 0`, `ν, c > 0`, `G ∈ H_r`,
`flatDuhamel ν μ G` is a.e. strongly measurable for `hMeas c r`).

Proof outline:
1. `G` has a strongly measurable `c`-periodic-in-`q` representative `G'` that agrees with `G`
   Lebesgue-a.e. on `{s > 0}` (`exists_periodic_rep`, in `DuhamelMeasurable/Periodic.lean`).
2. `flatDuhamel ν μ G = flatDuhamel ν μ G'` pointwise: by Fubini the slices agree a.e. in `t`
   and `w ↦ z - w` preserves Lebesgue measure.
3. `flatDuhamel ν μ G'` is strongly measurable: it is a parametric Bochner integral over `t` of a
   strongly measurable integrand, which is itself a parametric integral over `w`.
4. Conclude with `StronglyMeasurable.aestronglyMeasurable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The integrand of `flatDuhamel` as a function of `(x, t)` with `x = (s, z)`. -/
def duhamelBody (ν : ℝ) (μ : ℂ) (G : CProf) (p : Coord × ℝ) : CMerid :=
  (((p.2 / p.1.1 : ℝ) : ℂ) ^ μ * ((p.2⁻¹ : ℝ) : ℂ)) •
    flatHeat (ν * (p.1.1 - p.2)) (fun z => G (p.2, z)) p.1.2

/-- The set `{(x, t) | 0 < t < s}` of pairs with `t` in the integration range of `flatDuhamel`. -/
def duhamelS : Set (Coord × ℝ) := {p | p.2 ∈ Ioo (0 : ℝ) p.1.1}

theorem measurableSet_duhamelS : MeasurableSet duhamelS := by
  have h1 : MeasurableSet {p : Coord × ℝ | (0 : ℝ) < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h2 : MeasurableSet {p : Coord × ℝ | p.2 < p.1.1} :=
    measurableSet_lt measurable_snd (measurable_fst.comp measurable_fst)
  exact h1.inter h2

/-- `flatDuhamel` written as a Bochner integral over the whole line of the indicator integrand. -/
theorem flatDuhamel_eq_integral (ν : ℝ) (μ : ℂ) (G : CProf) (x : Coord) :
    flatDuhamel ν μ G x = ∫ t, duhamelS.indicator (duhamelBody ν μ G) (x, t) := by
  unfold flatDuhamel
  rw [← integral_indicator (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) x.1))]
  congr 1

/-- The integrand of `flatDuhamel` is strongly measurable in `(x, t)` when `G` is. -/
theorem stronglyMeasurable_duhamelBody (ν : ℝ) (μ : ℂ) {G : CProf}
    (hG : StronglyMeasurable G) : StronglyMeasurable (duhamelBody ν μ G) := by
  have hK : Measurable (fun q : (Coord × ℝ) × (ℝ × ℝ) =>
      flatHeatKernel (ν * (q.1.1.1 - q.1.2)) q.2) := by
    unfold flatHeatKernel
    fun_prop
  have hGm : Measurable (fun q : (Coord × ℝ) × (ℝ × ℝ) =>
      ((q.1.2, q.1.1.2 - q.2) : Coord)) := by
    fun_prop
  have hΘ : StronglyMeasurable (fun q : (Coord × ℝ) × (ℝ × ℝ) =>
      flatHeatKernel (ν * (q.1.1.1 - q.1.2)) q.2 • G (q.1.2, q.1.1.2 - q.2)) :=
    hK.stronglyMeasurable.smul (hG.comp_measurable hGm)
  have hΦ : StronglyMeasurable (fun p : Coord × ℝ =>
      flatHeat (ν * (p.1.1 - p.2)) (fun z => G (p.2, z)) p.1.2) :=
    hΘ.integral_prod_right'
  have hc : Measurable (fun p : Coord × ℝ =>
      (((p.2 / p.1.1 : ℝ) : ℂ)) ^ μ * ((p.2⁻¹ : ℝ) : ℂ)) :=
    ((Complex.measurable_ofReal.comp (measurable_snd.div (measurable_fst.comp measurable_fst))).pow_const μ).mul
      (Complex.measurable_ofReal.comp measurable_snd.inv)
  unfold duhamelBody
  exact hc.stronglyMeasurable.smul hΦ

/-- `flatDuhamel ν μ G` is strongly measurable when `G` is. -/
theorem flatDuhamel_stronglyMeasurable (ν : ℝ) (μ : ℂ) {G : CProf}
    (hG : StronglyMeasurable G) : StronglyMeasurable (flatDuhamel ν μ G) := by
  have h : flatDuhamel ν μ G = fun x => ∫ t, duhamelS.indicator (duhamelBody ν μ G) (x, t) :=
    funext (flatDuhamel_eq_integral ν μ G)
  rw [h]
  exact ((stronglyMeasurable_duhamelBody ν μ hG).indicator measurableSet_duhamelS).integral_prod_right'

/-- If `G` and `G'` agree a.e. on `{s > 0}`, then `flatDuhamel` does so pointwise, by Fubini and
the translation invariance of Lebesgue measure in `w`. -/
theorem flatDuhamel_congr_of_ae (ν : ℝ) (μ : ℂ) {G G' : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x) :
    flatDuhamel ν μ G = flatDuhamel ν μ G' := by
  have h' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      0 < z.1 → G z = G' z := h
  have hprod : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      0 < t → G (t, y) = G' (t, y) :=
    Measure.ae_ae_of_ae_prod h'
  funext x
  unfold flatDuhamel
  refine integral_congr_ae ?_
  have hprod' : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) x.1)),
      ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), 0 < t → G (t, y) = G' (t, y) :=
    ae_restrict_of_ae hprod
  have hmem : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) x.1)),
      t ∈ Ioo (0 : ℝ) x.1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hprod', hmem] with t ht hmem_t
  have hy : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), G (t, y) = G' (t, y) := by
    filter_upwards [ht] with y hy
    exact hy hmem_t.1
  have hflat : flatHeat (ν * (x.1 - t)) (fun z => G (t, z)) x.2 =
      flatHeat (ν * (x.1 - t)) (fun z => G' (t, z)) x.2 := by
    unfold flatHeat
    refine integral_congr_ae ?_
    filter_upwards [((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left x.2).quasiMeasurePreserving.ae
      hy] with w hw
    have hw' : G (t, x.2 - w) = G' (t, x.2 - w) := hw
    show flatHeatKernel (ν * (x.1 - t)) w • G (t, x.2 - w) =
      flatHeatKernel (ν * (x.1 - t)) w • G' (t, x.2 - w)
    rw [hw']
  rw [hflat]

/-- **Leaf `PartII-b:T12/3`** (SP 1924): for `G ∈ H_r` the Duhamel integral is (a.e.) strongly
measurable for the measure `hMeas c r`. -/
theorem duhamelMeasurable : DuhamelMeasurable := by
  unfold DuhamelMeasurable
  intro r _ _ μ _ ν c _ hc G hG
  obtain ⟨G', hG's, hGG'⟩ :=
    exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  rw [flatDuhamel_congr_of_ae ν μ hGG']
  exact (flatDuhamel_stronglyMeasurable ν μ hG's).aestronglyMeasurable

end UnforcedLeray.Short.IIb
