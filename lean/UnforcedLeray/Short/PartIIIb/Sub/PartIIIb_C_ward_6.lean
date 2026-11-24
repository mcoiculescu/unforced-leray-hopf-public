import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.VelYH
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3

/-!
# `WardYMeas` and `WardHMeas` from the regularity of `X` (`PartIII-b:C/ward/6`, `C/ward/7`)

Source of record: `the November 2 reference manuscript` 4171-4174, 3611-3626,
4161-4186.

The coefficients of `Y = D_{μ+1}X` and `h = [U, X]` read `X = wardX` (the stream cut of
`X₀ = W_μ - W_{μ+1}`) through `∂_τX`, `D_yX`, `D_y²X` and `X` off the axis.  Measurability of these
follows from joint measurability of `X` (`T8_4.t84_ward_stream`) together with

* `WardXDiffOffAxis`: for each `τ`, `X(τ, ·)` is `C²` near every point off the axis
  (`X₀` is `C²` on the young region by `sep:resolvent`, 3611-3621, and the outward primitive is
  `C²` there, 4178-4186; `X = 0` near the axis);
* `WardXTauDiffOffAxis`: for each `y` off the axis, `X(·, y)` is differentiable (the instantaneous
  term of `∂_τW_μ` cancels in `X₀ = W_μ - W_{μ+1}`, `Kd(0) = 0`, `SepX0TauDeriv`; the outward
  primitive is differentiated under the integral).

Both hold for every `IsOldL2` datum (not only the canonical `chiOStr` representatives).
The difference-quotient measurability argument is `wardHMeas_of` / `wardYMeas_of` below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **(P1) `C²` of `X` in `y` off the axis, for old `L²` data** (source 4161-4186, 3611-3626):
`wardX ν μ R c χy g τ` is `C²` near every `y` off the axis, for all `τ`.  The proof for the
canonical representatives is `wardXRegular_of` (T9) from `Final.wardX0Smooth_of`,
`Final.wardX0Structure_of`, `wardX0Decay_unconditional`, `outPrimDerivR`, `outPrimDerivZ`, whose
only use of `T, g₁, g₂` is through `OldSourceReg` (an `IIIa.IsSepSource` with finite `Y₂` moment equal
to `oldPhys R c (g₁+g₂)` a.e.); for `IsOldL2 c ν g` the same data come from `g` itself
(`oldSourceReg_of` with `G := g`). -/
def WardXDiffOffAxis : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space), y ∉ axis →
      ContDiffAt ℝ 2 (wardX ν μ R c χy g τ) y

/-- **(P2) `τ`-differentiability of `X` off the axis, for old `L²` data** (source 4171-4174,
3611-3626): `t ↦ wardX ν μ R c χy g t y` is differentiable at every `τ`, for `y` off the axis.
`X₀ = W_μ - W_{μ+1}` is differentiable in `τ` with no instantaneous term (`Kd(0) = 0`,
`sepX0TauDeriv`), and the outward primitive `-∫_r^∞ ρ X₀,z dρ` is differentiated under the
integral (majorant: the far-field decay of `∂_τX₀`, `kdDh` in place of `Kd`). -/
def WardXTauDiffOffAxis : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space), y ∉ axis →
      DifferentiableAt ℝ (fun t => wardX ν μ R c χy g t y) τ

/-- **(L1) Source regularisation for old `L²` data** (source 4155-4171, 2666-2703, 3611-3621): the
analogue of `OldSourceReg` (`Sub/IIIb-D2_3_1_1.lean`) with the datum `g` itself in place of
`χ_o(T₁+T₂)`.  Proof: `oldSourceReg_of`'s argument with `G := g`: the leaves
`chartOfNullPullback`, `sepWCongrAE`, `oldCutMeasurable`, `oldCutMoment` (`IIIb-D2_3_1_1_1/L*`),
`T' := oldCutSrc R c (R√(5ν/6)) g`, `hchart` from `IsOldL2.old`, `IsOldL2.memLp` for the moment. -/
def OldL2SepReg : Prop :=
  ∀ (ν R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → IsOldL2 c ν g →
    ∃ (P : ℝ) (T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < P ∧
      IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T' ∧ SepMoment P T' ∧
      (∀ (μ : ℂ) (y : Space) (τ : ℝ),
        IIIa.sepW ν μ (oldPhys R c g) y τ = IIIa.sepW ν μ T' y τ) ∧
      ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 = T' x.1 x.2

/-- **(L2) Regularity, structure and decay of `X₀` for old `L²` data** (source 4161-4186,
3611-3621): on the young region `ϱ > R√(5ν/6)`, `X₀ = wardX0` is `C²` in `y`, divergence free,
axisymmetric swirl free, and satisfies `StreamDecay`, for every phase `τ`.  The canonical-datum
proofs are `Final.wardX0Smooth_of` (T1), `Final.wardX0Structure_of` (T2),
`wardX0Decay_unconditional` (T3a); each uses `T, g₁, g₂` only through `OldSourceReg`, i.e. through
the output of (L1), after which the arguments (`wardX0Smooth_of`, `wardX0Structure_of`,
`wardX0FarBound_of`, `wardX0Decay_of`) are verbatim. -/
def WardX0FactsOldL2 : Prop :=
  ∀ (ν μ R c : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g →
      (∀ τ, ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R)) ∧
      (∀ τ, ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (wardX0 ν μ R c g τ) j y j = 0) ∧
      AxiNoSwirlOn (youngOpen ν R) (wardX0 ν μ R c g) ∧
      (∀ τ, StreamDecay ν R (wardX0 ν μ R c g) τ)

namespace WardMeasAux

/-- Measurability of the `τ`-derivative off the axis (value `0` on the axis), from joint
measurability and differentiability in `τ`: the derivative is the limit of the difference
quotients. -/
lemma measurable_deriv_tau_offaxis {F : ℝ → Space → Space}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (fun t => F t y) τ) :
    Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : Space) else deriv (fun t => F t p.2) p.1 := by
  have hq : ∀ n : ℕ, Measurable fun p : ℝ × Space =>
      if p.2 ∈ axis then (0 : Space)
      else ((n : ℝ) + 1) • (F (p.1 + ((n : ℝ) + 1)⁻¹) p.2 - F p.1 p.2) := by
    intro n
    have hA : Measurable fun p : ℝ × Space => F (p.1 + ((n : ℝ) + 1)⁻¹) p.2 :=
      hF.comp ((measurable_fst.add_const _).prodMk measurable_snd)
    have hS : MeasurableSet {p : ℝ × Space | p.2 ∈ axis} :=
      isClosed_axis.measurableSet.preimage measurable_snd
    exact Measurable.ite hS measurable_const ((hA.sub hF).const_smul (((n : ℝ) + 1)))
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  refine measurable_of_tendsto_metrizable hq ?_
  rw [tendsto_pi_nhds]
  intro p
  by_cases hp : p.2 ∈ axis
  · simp only [if_pos hp]
    exact tendsto_const_nhds
  · simp only [if_neg hp]
    have h := (hd p.1 p.2 hp).hasDerivAt.hasFDerivAt.lim (1 : ℝ) hc
    simpa using h

/-- The chart coefficient reads `F` only off the axis. -/
lemma coefOf_eq_ite {R : ℝ} (hR : 0 < R) (F : ℝ → Space → Space) :
    coefOf R F = coefOf R (fun τ y => if y ∈ axis then (0 : Space) else F τ y) := by
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
    simp only [if_neg hy]
  · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    simp [coefOf, hs]

end WardMeasAux

open WardMeasAux in
/-- **`WardHMeas` from (P1)** (source 4171-4174, 4139-4141). -/
theorem wardHMeas_of (h1 : WardXDiffOffAxis) : WardHMeas := by
  intro ν μ R c γ P χy U p hχy hν hR hc hμ hU g hg
  have hWX : Measurable fun q : ℝ × Space => wardX ν μ R c χy g q.1 q.2 :=
    T8_4.t84_ward_stream hχy hg.measurable
  have hdW : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y :=
    fun τ y hy => (h1 ν μ R c χy hχy hν hR hc hμ g hg τ y hy).differentiableAt (by norm_num)
  have hUτ : ∀ τ, ContDiff ℝ 2 (U τ) := fun τ =>
    ((hU.smoothU.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp
      (contDiff_const.prodMk contDiff_id) : ContDiff ℝ 2 (fun y : Space => U τ y))
  have hUm : Measurable fun q : ℝ × Space => U q.1 q.2 := hU.smoothU.continuous.measurable
  have hdU : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (U τ) y :=
    fun τ y _ => (hUτ τ).differentiable (by norm_num) y
  have hA1 := measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g) (V := U)
    hWX hUm hdW
  have hA2 := measurable_fderiv_apply_offaxis (F := U) (V := wardX ν μ R c χy g)
    hUm hWX hdU
  have hFix : Measurable fun q : ℝ × Space =>
      T8_4.wardHFix ν μ R c χy U g q.1 q.2 := by
    unfold T8_4.wardHFix
    exact hA1.sub hA2
  rw [T8_4.t84_coefOf_eq hR]
  exact (vyh_measurable_coefOf R hFix).aestronglyMeasurable

open WardMeasAux in
/-- **`WardYMeas` from (P1) and (P2)** (source 4171-4174, 3611-3626). -/
theorem wardYMeas_of (h1 : WardXDiffOffAxis) (h2 : WardXTauDiffOffAxis) : WardYMeas := by
  intro ν μ R c γ χy hχy hν hR hc hμ g hg
  have hXm : Measurable fun q : ℝ × Space => wardX ν μ R c χy g q.1 q.2 :=
    T8_4.t84_ward_stream hχy hg.measurable
  have hC2 : ∀ τ y, y ∉ axis → ContDiffAt ℝ 2 (wardX ν μ R c χy g τ) y :=
    fun τ y hy => h1 ν μ R c χy hχy hν hR hc hμ g hg τ y hy
  have hdX : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y :=
    fun τ y hy => (hC2 τ y hy).differentiableAt (by norm_num)
  have hS : MeasurableSet {q : ℝ × Space | q.2 ∈ axis} :=
    isClosed_axis.measurableSet.preimage measurable_snd
  -- first derivatives in the coordinate directions
  have hFd : ∀ j : Fin 3, Measurable fun q : ℝ × Space =>
      if q.2 ∈ axis then (0 : Space)
      else fderiv ℝ (wardX ν μ R c χy g q.1) q.2 (coordinateVector j) := fun j =>
    measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g)
      (V := fun _ _ => coordinateVector j) hXm measurable_const hdX
  have hd2 : ∀ (j : Fin 3) (τ : ℝ) (y : Space), y ∉ axis →
      DifferentiableAt ℝ (fun y' : Space =>
        if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j)) y := by
    intro j τ y hy
    have hev : (fun y' : Space => if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j)) =ᶠ[𝓝 y]
        fun y' => fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j) := by
      filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
      exact if_neg hz
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    exact (((hC2 τ y hy).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hLap : ∀ j : Fin 3, Measurable fun q : ℝ × Space =>
      if q.2 ∈ axis then (0 : Space)
      else fderiv ℝ (fun y' : Space => if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g q.1) y' (coordinateVector j)) q.2
        (coordinateVector j) := fun j =>
    measurable_fderiv_apply_offaxis
      (F := fun τ y' => if y' ∈ axis then (0 : Space)
        else fderiv ℝ (wardX ν μ R c χy g τ) y' (coordinateVector j))
      (V := fun _ _ => coordinateVector j) (hFd j) measurable_const (hd2 j)
  have hB := measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g)
    (V := fun _ y => y) hXm measurable_snd hdX
  have hA := measurable_deriv_tau_offaxis (F := wardX ν μ R c χy g) hXm
    (fun τ y hy => h2 ν μ R c χy hχy hν hR hc hμ g hg τ y hy)
  have hD : Measurable fun q : ℝ × Space =>
      if q.2 ∈ axis then (0 : Space) else wardX ν μ R c χy g q.1 q.2 :=
    Measurable.ite hS measurable_const hXm
  have hsum : Measurable fun q : ℝ × Space =>
      ∑ j : Fin 3, (if q.2 ∈ axis then (0 : Space)
        else fderiv ℝ (fun y' : Space => if y' ∈ axis then (0 : Space)
          else fderiv ℝ (wardX ν μ R c χy g q.1) y' (coordinateVector j)) q.2
          (coordinateVector j)) :=
    Finset.measurable_sum _ fun j _ => hLap j
  have hY : Measurable fun q : ℝ × Space =>
      if q.2 ∈ axis then (0 : Space) else wardY ν μ R c χy g q.1 q.2 := by
    have hfun : (fun q : ℝ × Space =>
        if q.2 ∈ axis then (0 : Space) else wardY ν μ R c χy g q.1 q.2) =
        fun q => (if q.2 ∈ axis then (0 : Space)
            else deriv (fun t => wardX ν μ R c χy g t q.2) q.1) -
          (1 / 2 : ℝ) • (if q.2 ∈ axis then (0 : Space)
            else fderiv ℝ (wardX ν μ R c χy g q.1) q.2 q.2) -
          ν • (∑ j : Fin 3, (if q.2 ∈ axis then (0 : Space)
            else fderiv ℝ (fun y' : Space => if y' ∈ axis then (0 : Space)
              else fderiv ℝ (wardX ν μ R c χy g q.1) y' (coordinateVector j)) q.2
              (coordinateVector j))) +
          ((μ + 1) - 1 / 2) • (if q.2 ∈ axis then (0 : Space)
            else wardX ν μ R c χy g q.1 q.2) := by
      funext q
      by_cases hq : q.2 ∈ axis
      · simp [hq]
      · simp only [if_neg hq, wardY, physDmu, physLap, physPd2, physPd]
        have hev : ∀ j : Fin 3, (fun y' : Space => if y' ∈ axis then (0 : Space)
            else fderiv ℝ (wardX ν μ R c χy g q.1) y' (coordinateVector j)) =ᶠ[𝓝 q.2]
            fun y' => fderiv ℝ (wardX ν μ R c χy g q.1) y' (coordinateVector j) := by
          intro j
          filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hq] with z hz
          exact if_neg hz
        simp only [(hev _).fderiv_eq]
    rw [hfun]
    exact ((hA.sub (hB.const_smul (1 / 2 : ℝ))).sub (hsum.const_smul ν)).add
      (hD.const_smul ((μ + 1) - 1 / 2))
  rw [coefOf_eq_ite hR]
  exact (vyh_measurable_coefOf R hY).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
