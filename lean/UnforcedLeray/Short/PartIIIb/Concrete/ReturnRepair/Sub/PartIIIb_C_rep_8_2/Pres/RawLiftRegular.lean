import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasDefs

/-!
# Regularity of the raw coefficient and the lifted pressure (task `PartIII-b:C/rep/8/2/pres/6/2/org`)

Source `the November 2 reference manuscript`
lines 1205-1225 (Proposition `sct:lift`: the lift is "smooth through the axis for positive time"),
4139-4141 (the fields are smooth), 5272-5282.

`RawLiftRegularAt` is not a consequence of `TrainSol` alone.  Its content splits into three source
facts, each a `Prop` below:

* `RawOffAxisSmooth`: `U_raw` is `C^∞` jointly in `(τ, y)` off the axis (the train velocity is `C^∞`
  by `IsTrain.smooth_v`; the raised stream `H = (1-K)ψ` is `C^∞` for `s > 0` by
  `PartI.TrainStreamSmooth`, which needs the train in the BUC class; the chart is smooth off the
  axis);
* `LiftOffAxisSmooth`: `p_lift = s·p(chart)` is `C^∞` jointly off the axis (`IsTrain.smooth_p`);
* `RawAxisContinuous`: the axis value of `Params.raw` (`axisExt`, the limit from off the axis,
  source 1205-1225 "smooth through the axis") is the continuous extension.

`rawLiftRegularAt_of` derives `RawLiftRegularAt` from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- `U_raw` is `C^∞` jointly in `(τ, y)` off the axis (source 1205-1225). -/
def RawOffAxisSmooth (Pl : PlanarData) (L : ReturnLevel) : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × Space => rawU Pl L x.1 x.2) {x : ℝ × Space | x.2 ∉ axis}

/-- The flat lifted pressure is `C^∞` jointly in `(τ, y)` off the axis (source 1217, 5272-5282). -/
def LiftOffAxisSmooth (L : ReturnLevel) : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × Space => liftP L x.1 x.2) {x : ℝ × Space | x.2 ∉ axis}

/-- The axis value of the raw coefficient is the continuous extension (source 1205-1225: the lift
is smooth through the axis; `Params.raw = axisExt`, `Cons/L2/BackgroundConcrete/Fields.lean:140`),
tested along the sequence `y + (n+1)⁻¹ e₀` which leaves the axis. -/
def RawAxisContinuous (Pl : PlanarData) (L : ReturnLevel) : Prop :=
  ∀ (τ : ℝ) (y : Space), y ∈ axis →
    Tendsto (fun n : ℕ => rawU Pl L τ (y + (((n : ℝ) + 1)⁻¹) • coordinateVector 0)) atTop
      (𝓝 (rawU Pl L τ y))

/-- `C^∞` jointly implies `C²` in the slice and `C¹` of the coordinate derivatives. -/
theorem slice_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × Space → E) (hF : ContDiffOn ℝ ∞ F {x : ℝ × Space | x.2 ∉ axis})
    (τ : ℝ) (y : Space) (hy : y ∉ axis) :
    ContDiffAt ℝ 2 (fun y' => F (τ, y')) y ∧
      ∀ j : Fin 3, ContDiffAt ℝ 1 (fun y' => fderiv ℝ (fun z => F (τ, z)) y' (coordinateVector j)) y := by
  have hopen : IsOpen {x : ℝ × Space | x.2 ∉ axis} :=
    (isOpen_compl_axis).preimage continuous_snd
  have hat : ContDiffAt ℝ ∞ F (τ, y) := hF.contDiffAt (hopen.mem_nhds hy)
  have hsl : ContDiffAt ℝ ∞ (fun y' : Space => F (τ, y')) y :=
    hat.comp y (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨hsl.of_le (by first | simp | norm_num | (norm_cast; exact le_top)), fun j => ?_⟩
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun z => F (τ, z))) y :=
    hsl.fderiv_right (m := 1) (by first | simp | norm_num | (norm_cast; exact le_top))
  exact h1.clm_apply contDiffAt_const

/-- Measurability of a field that is continuous off the axis and zero on it. -/
theorem measurable_of_contOn_axis_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : ℝ × Space → E)
    (hF : ContinuousOn F {x : ℝ × Space | x.2 ∉ axis}) (h0 : ∀ x : ℝ × Space, x.2 ∈ axis → F x = 0) :
    Measurable F := by
  have hcl : IsClosed {x : ℝ × Space | x.2 ∈ axis} := isClosed_axis.preimage continuous_snd
  have e : F = {x : ℝ × Space | x.2 ∈ axis}.piecewise (fun _ => (0 : E)) F := by
    funext x
    by_cases hx : x.2 ∈ axis
    · simp [Set.piecewise, hx, h0 x hx]
    · simp [Set.piecewise, hx]
  rw [e]
  exact ContinuousOn.measurable_piecewise continuousOn_const hF hcl.measurableSet

/-- **Measurability of `U_raw`** from off-axis smoothness and continuity at the axis. -/
theorem measurable_rawU_of (Pl : PlanarData) (L : ReturnLevel) (hS : RawOffAxisSmooth Pl L)
    (hAx : RawAxisContinuous Pl L) :
    Measurable (fun x : ℝ × Space => rawU Pl L x.1 x.2) := by
  set δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hδ
  have hδ0 : ∀ n, δ n ≠ 0 := fun n => (inv_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)).ne'
  let sh : ℕ → ℝ × Space → ℝ × Space := fun n x => (x.1, x.2 + δ n • coordinateVector 0)
  have hsh : ∀ n, Continuous (sh n) := fun n => by fun_prop
  let g : ℕ → ℝ × Space → Space := fun n x =>
    if (sh n x).2 ∈ axis then 0 else rawU Pl L (sh n x).1 (sh n x).2
  have hopen : IsOpen {x : ℝ × Space | x.2 ∉ axis} := (isOpen_compl_axis).preimage continuous_snd
  have hcont : ContinuousOn (fun x : ℝ × Space => rawU Pl L x.1 x.2) {x : ℝ × Space | x.2 ∉ axis} :=
    hS.continuousOn
  have hg : ∀ n, Measurable (g n) := fun n => by
    have hcl : IsClosed {x : ℝ × Space | (sh n x).2 ∈ axis} :=
      isClosed_axis.preimage (continuous_snd.comp (hsh n))
    have e : g n = {x : ℝ × Space | (sh n x).2 ∈ axis}.piecewise (fun _ => (0 : Space))
        (fun x => rawU Pl L (sh n x).1 (sh n x).2) := by
      funext x
      by_cases hx : (sh n x).2 ∈ axis <;> simp [g, Set.piecewise, hx]
    rw [e]
    refine ContinuousOn.measurable_piecewise continuousOn_const ?_ hcl.measurableSet
    exact hcont.comp (hsh n).continuousOn (fun x hx => hx)
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun x => ?_)
  by_cases hx : x.2 ∈ axis
  · refine (hAx x.1 x.2 hx).congr fun n => ?_
    have hna : (sh n x).2 ∉ axis := by
      intro h
      have h0 : (x.2 + δ n • coordinateVector 0) 0 = 0 := h.1
      have hx0 : x.2 0 = 0 := hx.1
      simp [coordinateVector, hx0] at h0
      exact hδ0 n h0
    exact (if_neg hna).symm
  · have hxo : x ∈ {x : ℝ × Space | x.2 ∉ axis} := hx
    have hc : ContinuousAt (fun x : ℝ × Space => rawU Pl L x.1 x.2) x :=
      hcont.continuousAt (hopen.mem_nhds hxo)
    have hlim : Tendsto (fun n => sh n x) atTop (𝓝 x) := by
      have h1 : Tendsto (fun n : ℕ => δ n) atTop (𝓝 0) := by simpa only [hδ, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h2 : Tendsto (fun n => x.2 + δ n • coordinateVector 0) atTop (𝓝 (x.2 + (0 : ℝ) • coordinateVector 0)) :=
        tendsto_const_nhds.add (h1.smul_const _)
      rw [zero_smul, add_zero] at h2
      exact (tendsto_const_nhds (x := x.1)).prodMk_nhds h2
    have h3 := hc.tendsto.comp hlim
    refine h3.congr' ?_
    have hev : ∀ᶠ n in atTop, sh n x ∈ {x : ℝ × Space | x.2 ∉ axis} := hlim.eventually (hopen.mem_nhds hxo)
    filter_upwards [hev] with n hn
    have : (sh n x).2 ∉ axis := hn
    simp [g, this]

/-- **The regularity of the raw coefficient and the lifted pressure** from the three source facts. -/
theorem rawLiftRegularAt_of (Pl : PlanarData) (L : ReturnLevel) (hS : RawOffAxisSmooth Pl L)
    (hP : LiftOffAxisSmooth L) (hAx : RawAxisContinuous Pl L) : RawLiftRegularAt Pl L := by
  refine ⟨measurable_rawU_of Pl L hS hAx, ?_, ?_, ?_⟩
  · refine measurable_of_contOn_axis_zero _ hP.continuousOn fun x hx => ?_
    have h0 : ϱ x.2 = 0 := by
      have := hx.1; have := hx.2
      simp only [ϱ]
      rw [Real.sqrt_eq_zero (by positivity)]
      nlinarith [sq_nonneg (x.2 0), sq_nonneg (x.2 1)]
    simp [liftP, age, h0]
  · intro τ y hy
    exact ⟨(slice_regular _ hS τ y hy).1, (slice_regular _ hP τ y hy).1⟩
  · intro τ y hy j
    exact ⟨(slice_regular _ hS τ y hy).2 j, (slice_regular _ hP τ y hy).2 j⟩

end UnforcedLeray.Short.PartIIIb.Concrete
