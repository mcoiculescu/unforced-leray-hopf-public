import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_3

/-!


Measurability of the chart coefficient of `wardH` (source 4161-4186, 4240-4258).

Route. `X = wardX` is jointly measurable (`wardX0` by T8_1, `outPrim` by T8_2, the cutoff
`χ_y` and its derivative are measurable since `χ_y` is smooth). Off the axis, `wardX τ` is
differentiable (it agrees with the regular field `X` of `WardXRegularAt`, and the axis is closed).
Then `wardH` is measurable off the axis by T8_3 (difference quotients). On the chart, the point
`chartY R p` has first coordinate `R / √p.1`, so it is off the axis when `p.1 > 0`; for `p.1 ≤ 0`
the prefactor `(√p.1)⁻¹` vanishes. Hence `coefOf R (wardH …) = coefOf R (wardHFix …)`, where
`wardHFix` is the everywhere-defined measurable version (value `0` on the axis).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace T8_4

lemma t84_coord (i : Fin 3) : Measurable fun y : Space => y i :=
  (measurable_pi_apply i).comp (PiLp.continuous_ofLp 2 _).measurable

lemma t84_vec2 {α : Type*} [MeasurableSpace α] {a b : α → ℝ} (ha : Measurable a)
    (hb : Measurable b) : Measurable fun x => (WithLp.toLp 2 ![a x, b x] : Merid) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact ha
  · exact hb

lemma t84_vec3 {α : Type*} [MeasurableSpace α] {a b c : α → ℝ} (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c) :
    Measurable fun x => (WithLp.toLp 2 ![a x, b x, c x] : Space) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Joint measurability of `wardX` (source 4171, 4180-4186). -/
lemma t84_ward_stream {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {g : Chart → Ten3} (hg : Measurable g) :
    Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 := by
  have hZ : Measurable fun p : ℝ × Space => wardX0 ν μ R c g p.1 p.2 :=
    wardX0_measurable_of_measurable ν μ R c g hg
  have hO : Measurable fun q : ℝ × ℝ × ℝ => outPrim (wardX0 ν μ R c g) q.1 q.2.1 q.2.2 :=
    outPrim_measurable hZ
  have hϱ : Measurable fun y : Space => ϱ y := by
    unfold ϱ
    exact Real.continuous_sqrt.measurable.comp
      (((t84_coord 0).pow_const 2).add ((t84_coord 1).pow_const 2))
  have hage : Measurable fun y : Space => age R y := by
    unfold age
    exact measurable_const.div (hϱ.pow_const 2)
  have hϱp : Measurable fun p : ℝ × Space => ϱ p.2 := hϱ.comp measurable_snd
  have hagep : Measurable fun p : ℝ × Space => ν * age R p.2 :=
    (hage.comp measurable_snd).const_mul ν
  have hχ : Measurable χy := hχy.smooth.continuous.measurable
  have hχd : Measurable (deriv χy) := measurable_deriv χy
  have hA : Measurable fun p : ℝ × Space => χy (ν * age R p.2) := hχ.comp hagep
  have hD : Measurable fun p : ℝ × Space => deriv χy (ν * age R p.2) := hχd.comp hagep
  have hF : Measurable fun p : ℝ × Space => outPrim (wardX0 ν μ R c g) p.1 (ϱ p.2) (p.2 2) :=
    hO.comp (measurable_fst.prodMk (hϱp.prodMk ((t84_coord 2).comp measurable_snd)))
  have hscal : Measurable fun p : ℝ × Space =>
      deriv χy (ν * age R p.2) * (-2 * ν * R ^ 2 / ϱ p.2 ^ 3) / ϱ p.2 *
        outPrim (wardX0 ν μ R c g) p.1 (ϱ p.2) (p.2 2) := by
    exact ((hD.mul (measurable_const.div (hϱp.pow_const 3))).div hϱp).mul hF
  have hsc : Measurable fun p : ℝ × Space =>
      wardStreamCut ν R χy (wardX0 ν μ R c g) p.1 p.2 := by
    unfold wardStreamCut
    exact (hA.smul hZ).add (hscal.smul measurable_const)
  exact hsc

/-- The everywhere-defined version of the Ward bracket `[U, X]`: the value of `wardH` off the
axis, and `0` on the axis (where `wardH` is not needed, source 4171-4173). -/
def wardHFix (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (g : Chart → Ten3) (τ : ℝ)
    (y : Space) : Space :=
  (if y ∈ axis then (0 : Space) else fderiv ℝ (wardX ν μ R c χy g τ) y (U τ y)) -
    (if y ∈ axis then (0 : Space) else fderiv ℝ (U τ) y (wardX ν μ R c χy g τ y))

lemma t84_wardHFix_meas {ν μ R c : ℝ} {χy : ℝ → ℝ} {U : ℝ → SpatialField}
    {g : Chart → Ten3} (hg : Measurable g) (hχy : IsYoungCutoff χy)
    (hU : ∀ τ, ContDiff ℝ 2 (U τ)) (hUm : Measurable fun p : ℝ × Space => U p.1 p.2)
    (hreg : WardXRegularAt ν μ R c χy g) :
    Measurable fun p : ℝ × Space => wardHFix ν μ R c χy U g p.1 p.2 := by
  have hWX : Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 :=
    t84_ward_stream hχy hg
  obtain ⟨X, hXc, hXeq, -, -, -⟩ := hreg
  have hdW : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y := by
    intro τ y hy
    have hev : X τ =ᶠ[𝓝 y] wardX ν μ R c χy g τ := by
      filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
      exact hXeq τ z hz
    exact ((hXc τ).differentiable (by norm_num) y).congr_of_eventuallyEq hev.symm
  have hdU : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (U τ) y :=
    fun τ y _ => (hU τ).differentiable (by norm_num) y
  have hA1 := measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g) (V := U) hWX hUm hdW
  have hA2 := measurable_fderiv_apply_offaxis (F := U) (V := wardX ν μ R c χy g) hUm hWX hdU
  unfold wardHFix
  exact hA1.sub hA2

lemma t84_wardH_eq {ν μ R c : ℝ} {χy : ℝ → ℝ} {U : ℝ → SpatialField} {g : Chart → Ten3}
    {τ : ℝ} {y : Space} (hy : y ∉ axis) :
    wardH ν μ R c χy U g τ y = wardHFix ν μ R c χy U g τ y := by
  simp only [wardH, wardHFix, ite_eq_right_iff.2 (fun h => absurd h hy), ite_false]

lemma t84_coefOf_eq {ν μ R c : ℝ} {χy : ℝ → ℝ} {U : ℝ → SpatialField} {g : Chart → Ten3}
    (hR : 0 < R) :
    coefOf R (wardH ν μ R c χy U g) = coefOf R (wardHFix ν μ R c χy U g) := by
  funext p
  by_cases hp : 0 < p.1
  · have hy : NearInst.chartY R p ∉ axis := by
      intro h
      have h' : NearInst.chartY R p 0 = 0 ∧ NearInst.chartY R p 1 = 0 := h
      have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
        simp [NearInst.chartY]
      have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hp).ne'
      exact hne (h1 ▸ h'.1)
    unfold coefOf
    rw [t84_wardH_eq hy]
  · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    simp [coefOf, hs]

lemma t84_coefOf_meas {ν μ R c : ℝ} {χy : ℝ → ℝ} {U : ℝ → SpatialField} {g : Chart → Ten3}
    (hg : Measurable g) (hχy : IsYoungCutoff χy)
    (hU : ∀ τ, ContDiff ℝ 2 (U τ)) (hUm : Measurable fun p : ℝ × Space => U p.1 p.2)
    (hreg : WardXRegularAt ν μ R c χy g) :
    Measurable (coefOf R (wardHFix ν μ R c χy U g)) := by
  have hFm := t84_wardHFix_meas hg hχy hU hUm hreg
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hτ : Measurable fun p : Chart => NearInst.chartTau R p := by
    unfold NearInst.chartTau
    exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have hY : Measurable fun p : Chart => NearInst.chartY R p := by
    unfold NearInst.chartY
    exact t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
      (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
      (measurable_const.div hsq) measurable_const
      ((measurable_snd.comp measurable_snd).div hsq)
  have hFmP : Measurable fun p : Chart =>
      wardHFix ν μ R c χy U g (NearInst.chartTau R p) (NearInst.chartY R p) :=
    hFm.comp (hτ.prodMk hY)
  have h0 : Measurable fun p : Chart =>
      wardHFix ν μ R c χy U g (NearInst.chartTau R p) (NearInst.chartY R p) 0 :=
    (t84_coord 0).comp hFmP
  have h2 : Measurable fun p : Chart =>
      wardHFix ν μ R c χy U g (NearInst.chartTau R p) (NearInst.chartY R p) 2 :=
    (t84_coord 2).comp hFmP
  have hv := t84_vec2 h0 h2
  unfold coefOf
  exact (measurable_inv.comp hsq).smul hv

end T8_4

open T8_4 in
/-- **`PartIII-b:IIIb-D2/3/1/8/4`** (`coefOf_wardH_measurable`): the chart coefficient of `wardH`
is measurable (source 4171-4174, 4240-4258). -/
theorem coefOf_wardH_measurable {ν μ R c : ℝ} (hR : 0 < R) {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {U : ℝ → SpatialField} (hU : ∀ τ, ContDiff ℝ 2 (U τ))
    (hUm : Measurable fun p : ℝ × Space => U p.1 p.2) {g : Chart → Ten3} (hg : Measurable g)
    (hreg : WardXRegularAt ν μ R c χy g) :
    Measurable (coefOf R (wardH ν μ R c χy U g)) := by
  rw [t84_coefOf_eq hR]
  exact t84_coefOf_meas hg hχy hU hUm hreg

end UnforcedLeray.Short.PartIIIb.Concrete
