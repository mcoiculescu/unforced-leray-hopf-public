import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L2
import UnforcedLeray.Lib.Sobolev.Axis
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RbY
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ax
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.Pointwise

/-!
# A criterion for `AxiChartForm` (organizer task `PartIII-b:C/rep/8/2/pres/4/2/lp/2/org`)

Source `the November 2 reference manuscript`
2670-2674 (the cylinder chart `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2` read modulo `c`, `η = Rz/ρ`),
2681-2688 (the normalized phase/space integral read in the chart "after azimuthal integration").

A density `F(τ, y)` is read faithfully in the ring chart (`AxiChartForm R c F`) as soon as
* off the axis it equals a jointly measurable function `h(τ, y)` (the chart measure lives on
  `s > 0`, where the chart point is off the axis), and
* it is `2c/R`-periodic in `τ` (the chart reduces `q` modulo `c`, i.e. `τ` modulo `2c/R`), and
* off the axis it is invariant under the rotation about the axis carrying `y` to `(ϱ y, 0, y₂)`
  (axisymmetry; for a field without swirl this is `axiDens_azimuth`).

The identification `F(τ, y) = F(chartOf R c y τ)` then holds at every off-axis point
(`chartTauOf_proved`, `chartYOf_proved`), hence almost everywhere (`Sob.ae_offAxis`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace LpChartForm

/-- The chart reading map `p ↦ (chartTau R p, chartY R p)` is measurable on the whole chart. -/
theorem measurable_chartMap (R : ℝ) :
    Measurable fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p) := by
  refine Measurable.prodMk ?_ ?_
  · unfold NearInst.chartTau
    exact ((measurable_const.mul (measurable_fst.comp measurable_snd)).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  · unfold NearInst.chartY
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    have hq : Measurable fun p : Chart => Real.sqrt p.1 := measurable_fst.sqrt
    fin_cases i
    · exact measurable_const.div hq
    · exact measurable_const
    · exact (measurable_snd.comp measurable_snd).div hq

/-- The chart measure `s^{-5/2} ds dq/c dη` lives on `s > 0`. -/
theorem ae_pos (c : ℝ) : ∀ᵐ p ∂(ageμ c (-5 / 2)), 0 < p.1 := by
  have h0 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))), 0 < s :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  exact Measure.quasiMeasurePreserving_fst.ae h0

/-- **Chart measurability from an off-axis measurable representative**: if `F(τ, y) = h(τ, y)` off
the axis with `h` jointly measurable, the chart reading of `F` is a.e.-measurable for the chart
measure (source 2670-2674: for `s > 0` the chart point `(R/√s, 0, η/√s)` is off the axis). -/
theorem aemeasurable_ringRead {R c : ℝ} (hR : R ≠ 0) {F : ℝ → Space → ℝ}
    {h : ℝ × Space → ℝ} (hh : Measurable h) (hF : ∀ τ y, y ∉ axis → F τ y = h (τ, y)) :
    AEMeasurable (ringRead R F) (ageμ c (-5 / 2)) := by
  refine (hh.comp (measurable_chartMap R)).aemeasurable.congr ?_
  filter_upwards [ae_pos c] with p hp
  exact (hF _ _ (chartMap_mem_offAxis R hR hp)).symm

/-- **The chart reading at an off-axis point** (source 2670-2674): for a density that is
`2c/R`-periodic in `τ` and invariant under the rotation carrying `y` to `(ϱ y, 0, y₂)`, the
reading at the chart point of `(y, τ)` is `F(τ, y)` (`chartTauOf_proved`: the phase is read back
up to an integer multiple of `2c/R`; `chartYOf_proved`: the point is read back as `(ϱ y, 0, y₂)`). -/
theorem ringRead_chartOf {R c : ℝ} (hR : 0 < R) {F : ℝ → Space → ℝ}
    (hper : ∀ τ y, F (τ + 2 * c / R) y = F τ y)
    (hrot : ∀ τ y, y ∉ axis → F τ y = F τ (WithLp.toLp 2 ![ϱ y, 0, y 2]))
    (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    F τ y = ringRead R F (NearInst.chartOf R c y τ) := by
  have hpos : 0 < NearInst.hRad y := ϱ_pos hy
  set Q : Space := WithLp.toLp 2 ![ϱ y, 0, y 2] with hQ
  have hP : Function.Periodic (fun t => F t Q) (2 * c / R) := fun t => hper t Q
  set k : ℤ := ⌊(R * Real.log (NearInst.hRad y / R) + R * τ / 2) / c + 1 / 2⌋ with hk
  have e : F (τ - (k : ℝ) * (2 * c / R)) Q = F τ Q := hP.sub_int_mul_eq k
  have e2 : ringRead R F (NearInst.chartOf R c y τ) = F (τ - (k : ℝ) * (2 * c / R)) Q := by
    unfold ringRead
    rw [chartTauOf_proved R c y τ hR.ne', chartYOf_proved R c y τ hR hpos]
    rfl
  rw [e2, e]
  exact hrot τ y hy

/-- **Criterion for `AxiChartForm`** (source 2670-2674, 2681-2688): an off-axis measurable
representative, `2c/R`-periodicity in `τ`, and azimuthal invariance off the axis. -/
theorem axiChartForm_of {R c : ℝ} (hR : 0 < R) {F : ℝ → Space → ℝ} {h : ℝ × Space → ℝ}
    (hh : Measurable h) (hF : ∀ τ y, y ∉ axis → F τ y = h (τ, y))
    (hper : ∀ τ y, F (τ + 2 * c / R) y = F τ y)
    (hrot : ∀ τ y, y ∉ axis → F τ y = F τ (WithLp.toLp 2 ![ϱ y, 0, y 2])) :
    AxiChartForm R c F := by
  refine ⟨aemeasurable_ringRead hR.ne' hh hF, ?_⟩
  have hoff : ∀ᵐ x : ℝ × Space ∂volume, x.2 ∈ UnforcedLeray.Sob.offAxis := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae UnforcedLeray.Sob.ae_offAxis
  filter_upwards [hoff] with x hx
  have hx' : x.2 ∉ axis := fun hax => hx.elim (fun h0 => h0 hax.1) (fun h1 => h1 hax.2)
  exact ringRead_chartOf hR hper hrot x.1 hx'

/-- **Off-axis congruence**: `AxiChartForm` only sees a density off the axis (the chart measure
lives on `s > 0`, and the chart point of an off-axis `y` has `s = R²/ρ² > 0`). -/
theorem axiChartForm_congr {R c : ℝ} (hR : 0 < R) {F G : ℝ → Space → ℝ}
    (hFG : ∀ τ y, y ∉ axis → F τ y = G τ y) (hG : AxiChartForm R c G) : AxiChartForm R c F := by
  obtain ⟨hGm, hGae⟩ := hG
  have hread : ∀ p : Chart, 0 < p.1 → ringRead R F p = ringRead R G p := fun p hp =>
    hFG _ _ (chartMap_mem_offAxis R hR.ne' hp)
  refine ⟨hGm.congr ?_, ?_⟩
  · filter_upwards [ae_pos c] with p hp
    exact (hread p hp).symm
  have hoff : ∀ᵐ x : ℝ × Space ∂volume, x.2 ∈ UnforcedLeray.Sob.offAxis := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae UnforcedLeray.Sob.ae_offAxis
  filter_upwards [hGae, hoff] with x hx hxo
  have hx' : x.2 ∉ axis := fun hax => hxo.elim (fun h0 => h0 hax.1) (fun h1 => h1 hax.2)
  have hpos : 0 < (NearInst.chartOf R c x.2 x.1).1 := by
    show 0 < R ^ 2 / NearInst.hRad x.2 ^ 2
    exact div_pos (pow_pos hR 2) (pow_pos (ϱ_pos hx') 2)
  rw [hFG _ _ hx', hx, hread _ hpos]

/-- The change density against `0`: value, first and second derivative. -/
theorem coefChgDens_zero_eq (g : Space → Space) (y : Space) :
    coefChgDens g 0 y = ‖g y‖ + ‖fderiv ℝ g y‖ + ‖secondJet g y‖ := by
  unfold coefChgDens
  have e5 : fderiv ℝ (0 : Space → Space) y = 0 := by simp
  have e6 : fderiv ℝ g y - 0 = fderiv ℝ g y := by
    ext a : 1
    simp
  have e7 : secondJet g y - 0 = secondJet g y := by
    ext a b : 2
    simp
  simp only [Pi.zero_apply, sub_zero, e5, e6, secondJet_zero, e7]

/-- The rotated point `(ϱ y, 0, y₂)` of an off-axis point is off the axis. -/
theorem azimuth_not_mem_axis {y : Space} (hy : y ∉ axis) :
    (WithLp.toLp 2 ![ϱ y, 0, y 2] : Space) ∉ axis := by
  intro h
  have h0 : (WithLp.toLp 2 ![ϱ y, 0, y 2] : Space) 0 = 0 := h.1
  have h1 : ϱ y = 0 := by simpa using h0
  exact (ϱ_pos hy).ne' h1

/-- **Azimuthal invariance of the change density** (source 121-124, 2688): for a field that is
axisymmetric without swirl and `C²` off the axis, `coefChgDens g 0` takes the same value at `y`
and at `(ϱ y, 0, y₂)` (`axiDens_azimuth`; off the axis `secondJet = fderiv (fderiv ·)`). -/
theorem coefChgDens_azimuth {g : Space → Space} (hg : AxiNoSwirlPt g)
    (hC2 : ContDiffOn ℝ 2 g axisᶜ) {y : Space} (hy : y ∉ axis) :
    coefChgDens g 0 y = coefChgDens g 0 (WithLp.toLp 2 ![ϱ y, 0, y 2]) := by
  have hQ := azimuth_not_mem_axis hy
  obtain ⟨h0, h1, h2⟩ := axiDens_azimuth hg y
  have e1 : secondJet g y = fderiv ℝ (fderiv ℝ g) y :=
    secondJet_eq_fderiv (rby_fderiv_diff_of_contDiffOn hC2 hy)
  have e2 : secondJet g (WithLp.toLp 2 ![ϱ y, 0, y 2]) =
      fderiv ℝ (fderiv ℝ g) (WithLp.toLp 2 ![ϱ y, 0, y 2]) :=
    secondJet_eq_fderiv (rby_fderiv_diff_of_contDiffOn hC2 hQ)
  rw [coefChgDens_zero_eq, coefChgDens_zero_eq, e1, e2, h0, h1, h2]

/-- **`AxiChartForm` of the change density of an axisymmetric family** (source 2670-2674,
2681-2688, 121-124): for `f` jointly measurable, `C²` off the axis in `y`, `2c/R`-periodic in `τ`
and axisymmetric without swirl, the density `coefChgDens (f τ) 0 y` is read faithfully in the
ring chart.  Off the axis it is `‖f‖ + pwN1 f + pwN2 f` (`rby_coefChg_eq`), jointly measurable. -/
theorem axiChartForm_coefChgDens {R c : ℝ} (hR : 0 < R) {f : ℝ → Space → Space}
    (hf : Measurable fun x : ℝ × Space => f x.1 x.2)
    (hC2 : ∀ τ, ContDiffOn ℝ 2 (f τ) axisᶜ)
    (hper : ∀ τ, f (τ + 2 * c / R) = f τ)
    (hax : ∀ τ, AxiNoSwirlPt (f τ)) :
    AxiChartForm R c (fun τ y => coefChgDens (f τ) 0 y) := by
  have hdiff : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (f τ) y :=
    fun τ y hy => rby_diff_of_contDiffOn (hC2 τ) hy
  have hmP1 : Measurable fun x : ℝ × Space => pwN1 f x := by
    have hc : Continuous fun m : Fin 3 → Space => ‖jet1 m‖ :=
      (continuous_norm (E := Space →L[ℝ] Space)).comp continuous_jet1
    refine hc.measurable.comp (measurable_pi_lambda _ fun j => ?_)
    unfold pw1
    exact rby_meas_pw1 f hf hdiff (coordinateVector j)
  have hmP2 : Measurable fun x : ℝ × Space => pwN2 f x := by
    have hc : Continuous fun m : Fin 3 → Fin 3 → Space => ‖jet2 m‖ :=
      (continuous_norm (E := Space →L[ℝ] Space →L[ℝ] Space)).comp continuous_jet2
    refine hc.measurable.comp (measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun l => ?_)
    unfold pw2
    exact rby_meas_pw1 (gAux f l) (rby_meas_gAux f hf hdiff l)
      (fun τ y hy => rby_diff_gAux f hC2 τ l hy) (coordinateVector j)
  refine axiChartForm_of hR (h := fun x => ‖f x.1 x.2‖ + pwN1 f x + pwN2 f x)
    ((hf.norm.add hmP1).add hmP2) (fun τ y hy => rby_coefChg_eq f τ hy) ?_ ?_
  · intro τ y
    show coefChgDens (f (τ + 2 * c / R)) 0 y = coefChgDens (f τ) 0 y
    rw [hper τ]
  · intro τ y hy
    exact coefChgDens_azimuth (hax τ) (hC2 τ) hy

/-- **The change density of `f + g` against `f`** is that of `g` against `0` at a point where both
are `C²` (the equality case of `PwSplit.split_le`; source 5287-5289: `V - U_raw = E_εα`). -/
theorem coefChgDens_add_left_eq {f g : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) :
    coefChgDens (fun z => f z + g z) f y = coefChgDens g 0 y := by
  have e1 : fderiv ℝ (fun z => f z + g z) y - fderiv ℝ f y = fderiv ℝ g y := by
    rw [show (fun z => f z + g z) = f + g from rfl,
      ((PwSplit.da hf).hasFDerivAt.add (PwSplit.da hg).hasFDerivAt).fderiv]
    abel
  have e2 : ∀ j l, physPd2 (fun z => f z + g z) j l y - physPd2 f j l y = physPd2 g j l y := by
    intro j l
    rw [PwSplit.pd2_add hf hg j l]
    abel
  have e3 : secondJet (fun z => f z + g z) y - secondJet f y = secondJet g y := by
    unfold secondJet
    rw [jet2_sub]
    simp only [e2]
  unfold coefChgDens
  have e4 : f y + g y - f y = g y := by abel
  have e5 : fderiv ℝ (0 : Space → Space) y = 0 := by simp
  have e6 : secondJet g y - 0 = secondJet g y := by
    ext a b : 2
    simp
  simp only [Pi.zero_apply, sub_zero, e1, e3, e4, e5, secondJet_zero, e6]

/-- Finite linear combinations of fields axisymmetric without swirl are axisymmetric without
swirl (the isometries are linear). -/
theorem axiNoSwirlPt_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℝ) {f : ι → Space → Space}
    (hf : ∀ i, AxiNoSwirlPt (f i)) : AxiNoSwirlPt (fun y => ∑ i ∈ s, a i • f i y) := by
  intro g hg x
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hf i g hg x]

end LpChartForm

end UnforcedLeray.Short.PartIIIb.Concrete
