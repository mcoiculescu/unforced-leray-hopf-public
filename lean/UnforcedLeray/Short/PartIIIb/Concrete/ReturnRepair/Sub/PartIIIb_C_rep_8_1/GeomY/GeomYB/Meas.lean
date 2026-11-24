import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYFormula
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.YTermsDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Measurable

/-!
# `PartIII-b:C/rep/8/1/1/2/5` (`geomYB`), leaf (4): measurability of `dYB` along the cell

Source `the November 2 reference manuscript`
lines 4171-4215 (`X = 𝒞_yX₀`, `Y = D_{μ+1}X`, `ward:cutoff-source`
`Y = 𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀`), 3611-3626 (`W_μ` a measurable parametric integral).

At a chart point `(s,(q,η))` the receiver `chartY R (s,(q,η)) = y₀` does not depend on `q` and the
phase `chartTau R (s,(q,η)) = 2q/R + log s` is affine in `q`; `mnYB` is phase free.  So it suffices
that `τ ↦ D_y(YB)(τ, y₀)` is a.e.-strongly measurable.  By the exact formula (`ActYFormulaAt`) for
almost every phase `YB = Y₁ - 𝒞_yW_μ` at every receiver off the axis, and both are measurable in
the phase at each fixed off-axis receiver:
* `Y₁ = D_{μ+1}X₁`: the phase derivative at a fixed receiver is measurable for every function
  (`measurable_deriv`); the spatial gradient and Laplacian are measurable by difference quotients
  (`measurable_fderiv_apply_offaxis`), `X₁` being jointly measurable and `C²` off the axis
  (`WardXRegularAt`);
* `𝒞_yW_μ`: `W_μ` is jointly measurable (`measurable_sepW_comp`), hence so are its outward primitive
  and its stream cutoff.
`D_y(YB)(τ, y₀)v` is then the a.e. limit of the difference quotients of `Y₁ - 𝒞_yW_μ` along the ray
`y₀ + t v` (`t ≥ 0`), which stays off the axis, by the a.e. differentiability `YTermsDiffAt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomYBMeas

/-- A directional derivative at a fixed point is a.e.-strongly measurable in the parameter when
the field agrees a.e. on the ray `y₀ + t v` (`t ≥ 0`) with a field measurable in the parameter at
each point of the ray, and is differentiable at `y₀` for almost every parameter. -/
theorem aesm_fderiv_apply {F G : ℝ → Space → Space} {y₀ v : Space}
    (hG : ∀ t : ℝ, 0 ≤ t → Measurable fun τ => G τ (y₀ + t • v))
    (hFG : ∀ᵐ τ : ℝ, ∀ t : ℝ, 0 ≤ t → F τ (y₀ + t • v) = G τ (y₀ + t • v))
    (hd : ∀ᵐ τ : ℝ, DifferentiableAt ℝ (F τ) y₀) :
    AEStronglyMeasurable (fun τ => fderiv ℝ (F τ) y₀ v) volume := by
  have h0 : Measurable fun τ => G τ y₀ := by
    have := hG 0 le_rfl
    simpa only [zero_smul, add_zero] using this
  have hq : ∀ n : ℕ, Measurable fun τ : ℝ =>
      ((n : ℝ) + 1) • (G τ (y₀ + ((n : ℝ) + 1)⁻¹ • v) - G τ y₀) := by
    intro n
    exact ((hG ((n : ℝ) + 1)⁻¹ (by positivity)).sub h0).const_smul ((n : ℝ) + 1)
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hq n).aestronglyMeasurable) ?_
  filter_upwards [hFG, hd] with τ hτ hdτ
  have e : ∀ n : ℕ, ((n : ℝ) + 1) • (G τ (y₀ + ((n : ℝ) + 1)⁻¹ • v) - G τ y₀) =
      ((n : ℝ) + 1) • (F τ (y₀ + ((n : ℝ) + 1)⁻¹ • v) - F τ y₀) := by
    intro n
    have h1 := hτ ((n : ℝ) + 1)⁻¹ (by positivity)
    have h2 := hτ 0 le_rfl
    simp only [zero_smul, add_zero] at h2
    rw [h1, h2]
  simp_rw [e]
  exact hdτ.hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) v hc

/-- A family of continuous linear maps of `Space` is a.e.-strongly measurable when its values on
the coordinate vectors are. -/
theorem aesm_clm_of_apply {μ : Measure ℝ} {Φ : ℝ → Space →L[ℝ] Space}
    (h : ∀ j : Fin 3, AEStronglyMeasurable (fun a => Φ a (coordinateVector j)) μ) :
    AEStronglyMeasurable Φ μ := by
  have e : ∀ L : Space →L[ℝ] Space, L = ∑ j : Fin 3,
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (L (coordinateVector j)) := by
    intro L
    ext1 v
    have hv : v = ∑ j : Fin 3, v j • (coordinateVector j : Space) := by
      have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
      simpa [coordinateVector] using this.symm
    conv_lhs => rw [hv]
    simp [map_sum, ContinuousLinearMap.sum_apply]
  have : Φ = fun a => ∑ j : Fin 3,
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (Φ a (coordinateVector j)) :=
    funext fun a => e (Φ a)
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum (f := fun (j : Fin 3) (a : ℝ) =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (Φ a (coordinateVector j))) _ fun j _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ Space Space
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable (h j)

/-- Joint measurability of the stream cutoff of a jointly measurable field (as `t84_ward_stream`). -/
theorem wardStreamCut_measurable {ν R : ℝ} {χy : ℝ → ℝ} (hχ : Continuous χy)
    {Z : ℝ → Space → Space} (hZ : Measurable fun p : ℝ × Space => Z p.1 p.2) :
    Measurable fun p : ℝ × Space => wardStreamCut ν R χy Z p.1 p.2 := by
  have hO : Measurable fun q : ℝ × ℝ × ℝ => outPrim Z q.1 q.2.1 q.2.2 :=
    outPrim_measurable hZ
  have hϱ : Measurable fun y : Space => ϱ y := by
    unfold ϱ
    exact Real.continuous_sqrt.measurable.comp
      (((T8_4.t84_coord 0).pow_const 2).add ((T8_4.t84_coord 1).pow_const 2))
  have hage : Measurable fun y : Space => age R y := by
    unfold age
    exact measurable_const.div (hϱ.pow_const 2)
  have hϱp : Measurable fun p : ℝ × Space => ϱ p.2 := hϱ.comp measurable_snd
  have hagep : Measurable fun p : ℝ × Space => ν * age R p.2 :=
    (hage.comp measurable_snd).const_mul ν
  have hA : Measurable fun p : ℝ × Space => χy (ν * age R p.2) := hχ.measurable.comp hagep
  have hD : Measurable fun p : ℝ × Space => deriv χy (ν * age R p.2) :=
    (measurable_deriv χy).comp hagep
  have hF : Measurable fun p : ℝ × Space => outPrim Z p.1 (ϱ p.2) (p.2 2) :=
    hO.comp (measurable_fst.prodMk (hϱp.prodMk ((T8_4.t84_coord 2).comp measurable_snd)))
  have hscal : Measurable fun p : ℝ × Space =>
      deriv χy (ν * age R p.2) * (-2 * ν * R ^ 2 / ϱ p.2 ^ 3) / ϱ p.2 *
        outPrim Z p.1 (ϱ p.2) (p.2 2) :=
    ((hD.mul (measurable_const.div (hϱp.pow_const 3))).div hϱp).mul hF
  unfold wardStreamCut
  exact (hA.smul hZ).add (hscal.smul measurable_const)

/-- A point with positive first coordinate is off the axis and has `ϱ > 0`. -/
theorem varrho_pos_of_fst {y : Space} (h : 0 < y 0) : 0 < ϱ y := by
  unfold ϱ
  apply Real.sqrt_pos.2
  have := sq_nonneg (y 1)
  have := pow_pos h 2
  linarith

theorem not_mem_axis_of_fst {y : Space} (h : 0 < y 0) : y ∉ axis := by
  intro hy
  have := hy.1
  linarith

theorem ray_fst_pos {y₀ : Space} (h : 0 < y₀ 0) (j : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    0 < (y₀ + t • (coordinateVector j : Space)) 0 := by
  have hc : 0 ≤ (coordinateVector j : Space) 0 := by
    have e : (coordinateVector j : Space) = EuclideanSpace.single j 1 := rfl
    rw [e, EuclideanSpace.single_apply]
    split_ifs <;> norm_num
  have e2 : (y₀ + t • (coordinateVector j : Space)) 0 = y₀ 0 + t * (coordinateVector j : Space) 0 := by
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [e2]
  have := mul_nonneg ht hc
  linarith

end GeomYBMeas

open GeomYBMeas

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `W_μ` of the old thin source is jointly measurable (`measurable_sepW_comp`). -/
theorem thinWardW_measurable (T : LStr Pl K L) :
    Measurable fun p : ℝ × Space => thinWardW Pl K L μ T p.1 p.2 := by
  have hg := XMeas.thinG_measurable Pl K L T
  have hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space =>
      oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T) s.1 s.2 j k :=
    fun j k => T8_1.measurable_oldPhys_entry L.ε⁻¹ (cOf L.ν) _ hg j k
  have h1 : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      (IIIa.sepW L.ν (μ : ℂ) (oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T)) q.2 q.1 i).re :=
    fun i => Complex.measurable_re.comp (T8_1.measurable_sepW_comp L.ν (μ : ℂ) _ i hT)
  unfold thinWardW
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp (measurable_pi_iff.2 h1)

/-- `𝒞_yW_μ` is measurable in the phase at every receiver. -/
theorem actYA_measurable_tau (hχ : Continuous K.χy) (T : LStr Pl K L) (y : Space) :
    Measurable fun τ : ℝ => actYA Pl K L μ T τ y := by
  have h : Measurable fun p : ℝ × Space =>
      wardStreamCut L.ν L.ε⁻¹ K.χy (thinWardW Pl K L μ T) p.1 p.2 :=
    wardStreamCut_measurable hχ (thinWardW_measurable Pl K L μ T)
  have hpt : Measurable fun τ : ℝ => ((τ, y) : ℝ × Space) :=
    measurable_id.prodMk measurable_const
  have e : (fun τ : ℝ => actYA Pl K L μ T τ y) =
      (fun p : ℝ × Space => wardStreamCut L.ν L.ε⁻¹ K.χy (thinWardW Pl K L μ T) p.1 p.2) ∘
        fun τ : ℝ => ((τ, y) : ℝ × Space) := rfl
  rw [e]
  exact h.comp hpt

end Regime

section WardY

variable {ν μ R c : ℝ} {χy : ℝ → ℝ} {g : Chart → Ten3}

/-- Off the axis a regular Ward field is differentiable. -/
theorem wardX_diff_offaxis (hreg : WardXRegularAt ν μ R c χy g) :
    ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y := by
  obtain ⟨X, hXC, hXeq, -, -, -⟩ := hreg
  intro τ y hy
  have hev : X τ =ᶠ[𝓝 y] wardX ν μ R c χy g τ := by
    filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
    exact hXeq τ z hz
  exact ((hXC τ).differentiable (by norm_num) y).congr_of_eventuallyEq hev.symm

/-- The radial part `y·∇X` at a fixed receiver off the axis is measurable in the phase. -/
theorem wardX_grad_measurable_tau (hχy : IsYoungCutoff χy) (hg : Measurable g)
    (hreg : WardXRegularAt ν μ R c χy g) {y : Space} (hy : y ∉ axis) :
    Measurable fun τ => fderiv ℝ (wardX ν μ R c χy g τ) y y := by
  have hWm : Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 :=
    T8_4.t84_ward_stream hχy hg
  have hm := measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g) (V := fun _ y => y)
    hWm measurable_snd (wardX_diff_offaxis hreg)
  have hpt : Measurable fun τ : ℝ => ((τ, y) : ℝ × Space) :=
    measurable_id.prodMk measurable_const
  have e : (fun τ => fderiv ℝ (wardX ν μ R c χy g τ) y y) =
      (fun p : ℝ × Space => if p.2 ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g p.1) p.2 p.2) ∘ fun τ : ℝ => ((τ, y) : ℝ × Space) := by
    funext τ
    exact (if_neg hy).symm
  rw [e]
  exact hm.comp hpt

/-- The second derivative `∂_j∂_jX` at a fixed receiver off the axis is measurable in the phase. -/
theorem wardX_pd2_measurable_tau (hχy : IsYoungCutoff χy) (hg : Measurable g)
    (hreg : WardXRegularAt ν μ R c χy g) {y : Space} (hy : y ∉ axis) (j : Fin 3) :
    Measurable fun τ => physPd2 (wardX ν μ R c χy g τ) j j y := by
  have hWm : Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 :=
    T8_4.t84_ward_stream hχy hg
  have hdW := wardX_diff_offaxis hreg
  obtain ⟨X, hXC, hXeq, -, -, -⟩ := hreg
  have hev : ∀ (τ : ℝ) (y : Space), y ∉ axis → X τ =ᶠ[𝓝 y] wardX ν μ R c χy g τ := by
    intro τ y hy
    filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
    exact hXeq τ z hz
  have hFd : Measurable fun q : ℝ × Space =>
      if q.2 ∈ axis then (0 : Space)
      else fderiv ℝ (wardX ν μ R c χy g q.1) q.2 (coordinateVector j) :=
    measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g)
      (V := fun _ _ => coordinateVector j) hWm measurable_const hdW
  have hev3 : ∀ (τ : ℝ) (y : Space), y ∉ axis →
      (fun y' : Space => if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j)) =ᶠ[𝓝 y]
        fun y' => fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j) := by
    intro τ y hy
    filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
    exact if_neg hz
  have hev2 : ∀ (τ : ℝ) (y : Space), y ∉ axis →
      (fun y' : Space => if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j)) =ᶠ[𝓝 y]
        fun y' => fderiv ℝ (X τ) y' (coordinateVector j) := by
    intro τ y hy
    filter_upwards [hev3 τ y hy, isClosed_axis.isOpen_compl.mem_nhds hy] with z hz hz'
    rw [hz, (hev τ z hz').fderiv_eq]
  have hd2 : ∀ (τ : ℝ) (y : Space), y ∉ axis →
      DifferentiableAt ℝ (fun y' : Space => if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j)) y := by
    intro τ y hy
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (hev2 τ y hy)
    exact (((hXC τ).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num) y
  have hm := measurable_fderiv_apply_offaxis
    (F := fun τ y' => if y' ∈ axis then (0 : Space)
      else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j))
    (V := fun _ _ => coordinateVector j) hFd measurable_const hd2
  have hpt : Measurable fun τ : ℝ => ((τ, y) : ℝ × Space) :=
    measurable_id.prodMk measurable_const
  have e : (fun τ => physPd2 (wardX ν μ R c χy g τ) j j y) =
      (fun p : ℝ × Space => if p.2 ∈ axis then (0 : Space)
        else fderiv ℝ (fun y' : Space => if y' ∈ axis then (0 : Space)
          else fderiv ℝ (wardX ν μ R c χy g p.1) y' (coordinateVector j)) p.2
          (coordinateVector j)) ∘ fun τ : ℝ => ((τ, y) : ℝ × Space) := by
    funext τ
    rw [Function.comp_apply, if_neg hy]
    unfold physPd2 physPd
    rw [(hev3 τ y hy).fderiv_eq]
  rw [e]
  exact hm.comp hpt

/-- `D_{μ+1}X` of a regular Ward field is measurable in the phase at every receiver off the axis:
the phase derivative at a fixed receiver by `measurable_deriv`, the spatial terms by difference
quotients (`measurable_fderiv_apply_offaxis`). -/
theorem wardY_measurable_tau (hχy : IsYoungCutoff χy) (hg : Measurable g)
    (hreg : WardXRegularAt ν μ R c χy g) {y : Space} (hy : y ∉ axis) :
    Measurable fun τ : ℝ => wardY ν μ R c χy g τ y := by
  have hWm : Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 :=
    T8_4.t84_ward_stream hχy hg
  have hpt : Measurable fun τ : ℝ => ((τ, y) : ℝ × Space) :=
    measurable_id.prodMk measurable_const
  have h1 : Measurable fun τ => deriv (fun t => wardX ν μ R c χy g t y) τ := measurable_deriv _
  have h2 : Measurable fun τ => (1 / 2 : ℝ) • fderiv ℝ (wardX ν μ R c χy g τ) y y :=
    (wardX_grad_measurable_tau hχy hg hreg hy).const_smul (1 / 2 : ℝ)
  have hsum : Measurable fun τ => ν • ∑ j : Fin 3, physPd2 (wardX ν μ R c χy g τ) j j y :=
    (Finset.measurable_sum _ fun j _ => wardX_pd2_measurable_tau hχy hg hreg hy j).const_smul ν
  have h4 : Measurable fun τ => ((μ + 1) - 1 / 2 : ℝ) • wardX ν μ R c χy g τ y :=
    (hWm.comp hpt).const_smul ((μ + 1) - 1 / 2 : ℝ)
  have hall := ((h1.sub h2).sub hsum).add h4
  exact hall

end WardY

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `Y₁ = D_{μ+1}X₁` is measurable in the phase at every receiver off the axis. -/
theorem actY_measurable_tau (hχy : IsYoungCutoff K.χy) (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0)
    (hμ : -(1 / 4) < μ) (T : LStr Pl K L) {y : Space} (hy : y ∉ axis) :
    Measurable fun τ : ℝ => actY Pl K L μ T τ y :=
  wardY_measurable_tau hχy (XMeas.thinG_measurable Pl K L T)
    (XMeas.thinG_wardXRegularAt Pl K L μ hχy hmZ hC0 hμ T) hy

/-- **Measurability of `dYB` along the cell** (leaf (4) of `geomYB`). -/
def MeasYBAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν),
    ∀ η : ℝ, AEStronglyMeasurable (fun q : ℝ => dYB Pl K L μ T
      (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))))
      (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2)))

/-- The phase map of a cell is quasi measure preserving. -/
theorem chartTau_qmp {R : ℝ} (hR : R ≠ 0) (s η : ℝ) :
    Measure.QuasiMeasurePreserving (fun q : ℝ => NearInst.chartTau R (s, (q, η))) volume volume := by
  have h2 : Measure.QuasiMeasurePreserving (fun q : ℝ => (2 / R) * q) volume volume := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [Real.map_volume_mul_left (div_ne_zero two_ne_zero hR)]
    exact Measure.smul_absolutelyContinuous
  have h3 := (measurePreserving_add_right volume (Real.log s)).quasiMeasurePreserving
  have e : (fun q : ℝ => NearInst.chartTau R (s, (q, η))) =
      (fun x : ℝ => x + Real.log s) ∘ fun q : ℝ => (2 / R) * q := by
    funext q
    simp only [NearInst.chartTau, Function.comp_apply]
    ring
  rw [e]
  exact h3.comp h2

/-- The receiver of a young chart point is off the axis: its first coordinate is `R/√s > 0`. -/
theorem chartY_fst_pos {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (η : ℝ) :
    0 < NearInst.chartY R (s, (0, η)) 0 := by
  have e : NearInst.chartY R (s, (0, η)) 0 = R / Real.sqrt s := by simp [NearInst.chartY]
  rw [e]
  exact div_pos hR (Real.sqrt_pos.2 hs)

/-- A function of `(τ, y)` read along a cell: if it is a.e.-strongly measurable in the phase at the
cell's receiver, it is a.e.-strongly measurable along the cell. -/
theorem cell_aesm_of_phase {E : Type*} [TopologicalSpace E] {R : ℝ} (hR : R ≠ 0) (c s η : ℝ)
    {F : ℝ → Space → E}
    (h : AEStronglyMeasurable (fun τ : ℝ => F τ (NearInst.chartY R (s, (0, η)))) volume) :
    AEStronglyMeasurable (fun q : ℝ => F (NearInst.chartTau R (s, (q, η)))
      (NearInst.chartY R (s, (q, η)))) (volume.restrict (Ico (-c / 2) (c / 2))) := by
  have hcomp := h.comp_quasiMeasurePreserving (chartTau_qmp hR s η)
  have e : (fun q : ℝ => F (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))) =
      (fun τ : ℝ => F τ (NearInst.chartY R (s, (0, η)))) ∘
        fun q : ℝ => NearInst.chartTau R (s, (q, η)) := by
    funext q
    have hY : NearInst.chartY R (s, (q, η)) = NearInst.chartY R (s, (0, η)) := by
      simp [NearInst.chartY]
    simp only [Function.comp_apply, hY]
  rw [e]
  exact hcomp.restrict

/-- **`D_y(YB)` at a young receiver is a.e.-strongly measurable in the phase** (source 4171-4215):
the a.e. limit of the difference quotients of `Y₁ - 𝒞_yW_μ` (`ActYFormulaAt`, `YTermsDiffAt`). -/
theorem actYB_fderiv_aesm (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) (hF : ActYFormulaAt Pl K L μ)
    (hD : YTermsDiffAt Pl K L μ) (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (T : LStr Pl K L)
    {s : ℝ} (hs : 0 < s) (η : ℝ) :
    AEStronglyMeasurable (fun τ : ℝ =>
      fderiv ℝ (actYB Pl K L μ T τ) (NearInst.chartY L.ε⁻¹ (s, (0, η)))) volume := by
  have hχy : IsYoungCutoff K.χy :=
    ⟨hL.chiY.smooth, hL.chiY.one, hL.chiY.zero, hL.chiY.range⟩
  have hμ : -(1 / 4) < μ := by have := hL.mu_pos; linarith
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  set y₀ : Space := NearInst.chartY L.ε⁻¹ (s, (0, η)) with hy₀def
  have hy₀ : 0 < y₀ 0 := chartY_fst_pos hR hs η
  -- the measurable version `G = Y₁ - 𝒞_yW_μ` along the rays from `y₀`
  have hG : ∀ j : Fin 3, ∀ t : ℝ, 0 ≤ t → Measurable fun τ =>
      actY Pl K L μ T τ (y₀ + t • (coordinateVector j : Space)) -
        actYA Pl K L μ T τ (y₀ + t • (coordinateVector j : Space)) := by
    intro j t ht
    exact (actY_measurable_tau Pl K L μ hχy hmZ hC0 hμ T
      (not_mem_axis_of_fst (ray_fst_pos hy₀ j ht))).sub
      (actYA_measurable_tau Pl K L μ hχy.smooth.continuous T _)
  have hFG : ∀ j : Fin 3, ∀ᵐ τ : ℝ, ∀ t : ℝ, 0 ≤ t →
      actYB Pl K L μ T τ (y₀ + t • (coordinateVector j : Space)) =
        actY Pl K L μ T τ (y₀ + t • (coordinateVector j : Space)) -
          actYA Pl K L μ T τ (y₀ + t • (coordinateVector j : Space)) := by
    intro j
    filter_upwards [hF T] with τ hτ t ht
    rw [hτ _ (varrho_pos_of_fst (ray_fst_pos hy₀ j ht))]
    abel
  have hd : ∀ᵐ τ : ℝ, DifferentiableAt ℝ (actYB Pl K L μ T τ) y₀ := by
    filter_upwards [hD hL T] with τ hτ
    exact (hτ y₀ (varrho_pos_of_fst hy₀)).2.1
  exact aesm_clm_of_apply fun j => aesm_fderiv_apply
    (G := fun τ y => actY Pl K L μ T τ y - actYA Pl K L μ T τ y) (hG j) (hFG j) hd

/-- **`MeasYBAt` from the exact formula and the a.e. differentiability** (source 4171-4215). -/
theorem measYBAt_of (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) (hF : ActYFormulaAt Pl K L μ)
    (hD : YTermsDiffAt Pl K L μ) : MeasYBAt Pl K L μ := by
  intro hL T s hs η
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  refine cell_aesm_of_phase hR.ne' (cOf L.ν) s η (F := dYB Pl K L μ T) ?_
  have hA := actYB_fderiv_aesm Pl K L μ hmZ hC0 hF hD hL T hs.1 η
  have e : (fun τ : ℝ => dYB Pl K L μ T τ (NearInst.chartY L.ε⁻¹ (s, (0, η)))) = fun τ =>
      fderiv ℝ (actYB Pl K L μ T τ) (NearInst.chartY L.ε⁻¹ (s, (0, η))) -
        fderiv ℝ (mnYB Pl K L μ T 0) (NearInst.chartY L.ε⁻¹ (s, (0, η))) := by
    funext τ
    rfl
  rw [e]
  exact hA.sub aestronglyMeasurable_const

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `MeasYBAt`. -/
def MeasYB : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeasYBAt D.Pl D.K (D.level n) (D.mu n z)

/-- **Leaf (4) of `geomYB`**: `dYB` is measurable along every young cell, from the exact formula
`actYFormula` and the differentiability `yTermsDiff` (source 4171-4215). -/
theorem measYB {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeasYB := by
  unfold MeasYB
  filter_upwards [actYFormula D hst, Sub8_1_1_2_3.yTermsDiff D hst] with n hF hD z hz
  exact measYBAt_of D.Pl D.K (D.level n) (D.mu n z) (by linarith [hst.mZ_gt]) hst.C0_pos
    (hF z hz) (hD z hz)

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
