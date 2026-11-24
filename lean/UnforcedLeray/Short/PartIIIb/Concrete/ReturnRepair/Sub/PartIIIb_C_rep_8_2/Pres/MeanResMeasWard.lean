import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasDefs

/-!
# Measurability of the Ward difference from its parts (task `PartIII-b:C/rep/8/2/pres/6/3`)

Source `the November 2 reference manuscript`
lines 1205-1225, 4139-4141, 4776-4791, 5272-5289.

The Ward residual is a sum of products of: the first and second derivatives of the exact profile
`U`, `p` (jointly `C^∞`), the first and second derivatives of `rawU`, `liftP` (`C²` off the axis,
jointly measurable), and the derivatives of the phase-independent mean fields `Xmean`, `Ymean`.
The derivative of an arbitrary function is measurable (`measurable_fderiv`), so the mean fields need
no regularity beyond what the statement gives; the off-axis derivatives of `U`, `p`, `rawU`,
`liftP` are measurable by the difference-quotient argument below (axis zeroed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Ward

/-- Off the axis, the directional derivative of a jointly measurable family `F τ` is measurable
(the axis is zeroed). Difference quotients converge to the derivative at points where `F τ` is
differentiable (source 4240-4258 usage). -/
theorem wardOff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] {F : ℝ → Space → G}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hd : ∀ (τ : ℝ) (y : Space), y ∉ axis → DifferentiableAt ℝ (F τ) y) (V : Space) :
    Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : G) else fderiv ℝ (F p.1) p.2 V := by
  have hS : MeasurableSet {p : ℝ × Space | p.2 ∈ axis} :=
    isClosed_axis.measurableSet.preimage measurable_snd
  have hq : ∀ n : ℕ, Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : G)
      else ((n : ℝ) + 1) • (F p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • V) - F p.1 p.2) := by
    intro n
    have hsum : Measurable fun p : ℝ × Space => p.2 + ((n : ℝ) + 1)⁻¹ • V :=
      measurable_snd.add_const _
    have hA : Measurable fun p : ℝ × Space => F p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • V) :=
      hF.comp (measurable_fst.prodMk hsum)
    exact Measurable.ite hS measurable_const ((hA.sub hF).const_smul _)
  refine measurable_of_tendsto_metrizable hq ?_
  rw [tendsto_pi_nhds]
  intro p
  by_cases hp : p.2 ∈ axis
  · simp only [if_pos hp]
    exact tendsto_const_nhds
  · simp only [if_neg hp]
    have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
    exact (hd p.1 p.2 hp).hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) V hc

/-- Off-axis second derivative `∂_j ∂_l F` of a jointly measurable family, `C²` off the axis. -/
theorem wardOff2 {F : ℝ → Space → Space}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (F τ) y) (j l : Fin 3) :
    Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : Space) else physPd2 (F p.1) j l p.2 := by
  have hG : Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : Space) else physPd (F p.1) l p.2 :=
    wardOff (F := F) hF (fun τ y hy => (hd τ y hy).differentiableAt (by norm_num))
      (coordinateVector l)
  have hGd : ∀ (τ : ℝ) (y : Space), y ∉ axis →
      DifferentiableAt ℝ (fun y' => if y' ∈ axis then (0 : Space) else physPd (F τ) l y') y := by
    intro τ y hy
    have heq : (fun y' => if y' ∈ axis then (0 : Space) else physPd (F τ) l y')
        =ᶠ[𝓝 y] fun y' => physPd (F τ) l y' := by
      filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with y' hy'
      have hy'' : y' ∉ axis := hy'
      simp only [if_neg hy'']
    have hdiff : DifferentiableAt ℝ (fun y' => physPd (F τ) l y') y := by
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ (F τ)) y :=
        (hd τ y hy).fderiv_right (m := 1) (by norm_num)
      exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)
    exact hdiff.congr_of_eventuallyEq heq
  have hM := wardOff (F := fun τ y' => if y' ∈ axis then (0 : Space) else physPd (F τ) l y')
    hG hGd (coordinateVector j)
  have hEq : (fun p : ℝ × Space => if p.2 ∈ axis then (0 : Space) else physPd2 (F p.1) j l p.2)
      = fun p : ℝ × Space => if p.2 ∈ axis then (0 : Space) else
        fderiv ℝ (fun y' => if y' ∈ axis then (0 : Space) else physPd (F p.1) l y') p.2
          (coordinateVector j) := by
    funext p
    by_cases hp : p.2 ∈ axis
    · simp [hp]
    · simp only [if_neg hp]
      have heq : (fun y' => if y' ∈ axis then (0 : Space) else physPd (F p.1) l y')
          =ᶠ[𝓝 p.2] fun y' => physPd (F p.1) l y' := by
        filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hp] with y' hy'
        have hy'' : y' ∉ axis := hy'
        simp only [if_neg hy'']
      rw [heq.fderiv_eq]
      rfl
  rw [hEq]
  exact hM

/-- Scalar version: off-axis derivative of a jointly measurable real family. -/
theorem wardOffS {F : ℝ → Space → ℝ}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hd : ∀ (τ : ℝ) (y : Space), y ∉ axis → DifferentiableAt ℝ (F τ) y) (j : Fin 3) :
    Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : ℝ) else fderiv ℝ (F p.1) p.2 (coordinateVector j) :=
  wardOff hF hd (coordinateVector j)

/-- Coordinates of a measurable `Space`-valued function are measurable. -/
theorem measurable_coordW {α : Type*} [MeasurableSpace α] {f : α → Space} (hf : Measurable f)
    (l : Fin 3) : Measurable fun a => f a l :=
  ((continuous_apply l).comp (PiLp.continuous_ofLp _ _)).measurable.comp hf

/-- The Ward residual of `(U, p)` against phase-independent mean fields `X = Xf`, `Y = Yf`,
zeroed on the axis, is measurable. -/
theorem wardEXY_meas (ν μ R : ℝ) {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (Xf Yf : Space → Space)
    (hUm : Measurable fun q : ℝ × Space => U q.1 q.2)
    (hUd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (U τ) y)
    (hpm : Measurable fun q : ℝ × Space => p q.1 q.2)
    (hpd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (p τ) y) :
    Measurable fun q : ℝ × Space =>
      if q.2 ∈ axis then (0 : Space) else wardEXY ν μ R U p (fun _ => Xf) (fun _ => Yf) q.1 q.2 := by
  have hS : MeasurableSet {q : ℝ × Space | q.2 ∈ axis} :=
    isClosed_axis.measurableSet.preimage measurable_snd
  obtain ⟨A1, hA1m, hA1e⟩ : ∃ A1 : Fin 3 → ℝ × Space → Space, (∀ j, Measurable (A1 j)) ∧
      ∀ j q, q.2 ∉ axis → A1 j q = physPd (U q.1) j q.2 :=
    ⟨fun j q => if q.2 ∈ axis then (0 : Space) else physPd (U q.1) j q.2,
      fun j => wardOff (F := U) hUm (fun τ y hy => (hUd τ y hy).differentiableAt (by norm_num))
        (coordinateVector j),
      fun j q hq => by simp [hq]⟩
  obtain ⟨A2, hA2m, hA2e⟩ : ∃ A2 : Fin 3 → Fin 3 → ℝ × Space → Space,
      (∀ j l, Measurable (A2 j l)) ∧
      ∀ j l q, q.2 ∉ axis → A2 j l q = physPd2 (U q.1) j l q.2 :=
    ⟨fun j l q => if q.2 ∈ axis then (0 : Space) else physPd2 (U q.1) j l q.2,
      fun j l => wardOff2 (F := U) hUm hUd j l,
      fun j l q hq => by simp [hq]⟩
  obtain ⟨P1, hP1m, hP1e⟩ : ∃ P1 : Fin 3 → ℝ × Space → ℝ, (∀ j, Measurable (P1 j)) ∧
      ∀ j q, q.2 ∉ axis → P1 j q = fderiv ℝ (p q.1) q.2 (coordinateVector j) :=
    ⟨fun j q => if q.2 ∈ axis then (0 : ℝ) else fderiv ℝ (p q.1) q.2 (coordinateVector j),
      fun j => wardOffS (F := p) hpm (fun τ y hy => (hpd τ y hy).differentiableAt (by norm_num)) j,
      fun j q hq => by simp [hq]⟩
  -- phase-independent mean fields: derivatives are measurable for any function
  have hXd1 : ∀ j : Fin 3, Measurable fun y : Space => physPd Xf j y := fun j =>
    measurable_fderiv_apply_const (𝕜 := ℝ) (f := Xf) (coordinateVector j)
  have hXd2 : ∀ j l : Fin 3, Measurable fun y : Space => physPd2 Xf j l y := fun j l =>
    measurable_fderiv_apply_const (𝕜 := ℝ) (f := fun y => physPd Xf l y) (coordinateVector j)
  have hYm : Measurable fun q : ℝ × Space => fderiv ℝ Yf q.2 (U q.1 q.2) := by
    have hA : Measurable fun q : ℝ × Space => fderiv ℝ Yf q.2 :=
      (measurable_fderiv (𝕜 := ℝ) (f := Yf)).comp measurable_snd
    exact (isBoundedBilinearMap_apply.continuous.measurable).comp (hA.prodMk hUm)
  have hB : Measurable fun q : ℝ × Space =>
      ∑ j : Fin 3, ∑ l : Fin 3, ((A1 j q) l • physPd2 Xf j l q.2 - (physPd Xf j q.2 l) • A2 j l q) :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
      ((measurable_coordW (hA1m j) l).smul ((hXd2 j l).comp measurable_snd)).sub
        ((measurable_coordW ((hXd1 j).comp measurable_snd) l).smul (hA2m j l))
  have hC : Measurable fun q : ℝ × Space =>
      ∑ j : Fin 3, ∑ l : Fin 3, (U q.1 q.2 j * U q.1 q.2 l) • physPd2 Xf j l q.2 :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ =>
      ((((measurable_coordW hUm j).mul (measurable_coordW hUm l))).smul
        ((hXd2 j l).comp measurable_snd))
  have hD : Measurable fun q : ℝ × Space =>
      (WithLp.toLp 2 fun i => ∑ j : Fin 3, (physPd Xf j q.2 i + physPd Xf i q.2 j) * P1 j q :
        Space) := by
    refine (PiLp.continuous_toLp _ _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_coordW ((hXd1 j).comp measurable_snd) i).add
        (measurable_coordW ((hXd1 i).comp measurable_snd) j)).mul (hP1m j)
  have hExpr : Measurable fun q : ℝ × Space =>
      (2 : ℝ) • fderiv ℝ Yf q.2 (U q.1 q.2)
        - (2 * ν) • (∑ j : Fin 3, ∑ l : Fin 3,
            ((A1 j q) l • physPd2 Xf j l q.2 - (physPd Xf j q.2 l) • A2 j l q))
        + (∑ j : Fin 3, ∑ l : Fin 3, (U q.1 q.2 j * U q.1 q.2 l) • physPd2 Xf j l q.2)
        - (WithLp.toLp 2 fun i => ∑ j : Fin 3,
            (physPd Xf j q.2 i + physPd Xf i q.2 j) * P1 j q : Space) :=
    ((((hYm.const_smul (2 : ℝ)).sub (hB.const_smul (2 * ν))).add hC).sub hD)
  have hfun : (fun q : ℝ × Space =>
        if q.2 ∈ axis then (0 : Space) else wardEXY ν μ R U p (fun _ => Xf) (fun _ => Yf) q.1 q.2)
      = fun q : ℝ × Space => if q.2 ∈ axis then (0 : Space) else
        ((2 : ℝ) • fderiv ℝ Yf q.2 (U q.1 q.2)
          - (2 * ν) • (∑ j : Fin 3, ∑ l : Fin 3,
              ((A1 j q) l • physPd2 Xf j l q.2 - (physPd Xf j q.2 l) • A2 j l q))
          + (∑ j : Fin 3, ∑ l : Fin 3, (U q.1 q.2 j * U q.1 q.2 l) • physPd2 Xf j l q.2)
          - (WithLp.toLp 2 fun i => ∑ j : Fin 3,
              (physPd Xf j q.2 i + physPd Xf i q.2 j) * P1 j q : Space)) := by
    funext q
    by_cases hq : q.2 ∈ axis
    · simp only [if_pos hq]
    · have hq' : q.2 ∉ axis := hq
      have e1 : ∀ j, A1 j q = physPd (U q.1) j q.2 := fun j => hA1e j q hq'
      have e2 : ∀ j l, A2 j l q = physPd2 (U q.1) j l q.2 := fun j l => hA2e j l q hq'
      have e3 : ∀ j, P1 j q = fderiv ℝ (p q.1) q.2 (coordinateVector j) := fun j => hP1e j q hq'
      simp only [if_neg hq', ↓reduceIte, wardEXY, physCdiff, physUUD2, physDXp, e1, e2, e3]
  rw [hfun]
  exact Measurable.ite hS measurable_const hExpr

end Ward

/-- **Measurability of the Ward difference from its parts** (source 4776-4791, 5272-5289): the
Ward residual of the exact profile minus the one of the raw coefficient and the lifted pressure is
jointly measurable on `ℝ × Space` once `Xmt` is measurable (`hX`), the raw coefficient is regular
(`hR`), and the exact profile is smooth (`hE`). -/
theorem wardDiffMeasAt_of_parts (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ P : ℝ)
    (hE : IsExactProfile L.ν P L.U L.pres) (hχ : IsStreamCutoff K.χy)
    (hX : XmtMeasAt Pl K L μ) (hR : RawLiftRegularAt Pl L) : WardDiffMeasAt Pl K L μ := by
  unfold WardDiffMeasAt
  intro T
  have hUs : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (L.U τ) := fun τ =>
    hE.smoothU.comp (contDiff_const.prodMk contDiff_id)
  have hPs : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (L.pres τ) := fun τ =>
    hE.smoothP.comp (contDiff_const.prodMk contDiff_id)
  have hUd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (L.U τ) y := fun τ y _ =>
    ((hUs τ).contDiffAt).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | norm_num)
  have hPd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (L.pres τ) y := fun τ y _ =>
    ((hPs τ).contDiffAt).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | norm_num)
  have hUm : Measurable fun q : ℝ × Space => L.U q.1 q.2 := hE.smoothU.continuous.measurable
  have hPm : Measurable fun q : ℝ × Space => L.pres q.1 q.2 := hE.smoothP.continuous.measurable
  have hRd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (rawU Pl L τ) y :=
    fun τ y hy => (hR.2.2.1 τ y hy).1
  have hLd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (liftP L τ) y :=
    fun τ y hy => (hR.2.2.1 τ y hy).2
  have hS : MeasurableSet {x : ℝ × Space | x.2 ∈ axis} :=
    isClosed_axis.measurableSet.preimage measurable_snd
  have hA := wardEXY_meas L.ν μ (L.ε⁻¹) (fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
    (fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) hUm hUd hPm hPd
  have hB := wardEXY_meas L.ν μ (L.ε⁻¹) (fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
    (fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) hR.1 hRd hR.2.1 hLd
  have h0 : Measurable fun _ : ℝ × Space => (0 : Space) := measurable_const
  have hG : Measurable fun x : ℝ × Space =>
      if x.2 ∈ axis then (0 : Space) else
        ((if x.2 ∈ axis then (0 : Space) else
            wardEXY L.ν μ (L.ε⁻¹) L.U L.pres
              (fun _ => fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
              (fun _ => fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) x.1 x.2)
          - (if x.2 ∈ axis then (0 : Space) else
            wardEXY L.ν μ (L.ε⁻¹) (rawU Pl L) (liftP L)
              (fun _ => fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
              (fun _ => fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) x.1 x.2)) :=
    Measurable.ite hS h0 (hA.sub hB)
  convert hG using 1
  funext x
  by_cases hx : x.2 ∈ axis
  · simp [hx]
  · simp only [if_neg hx]
    try rfl

end UnforcedLeray.Short.PartIIIb.Concrete
