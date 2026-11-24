import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.ZRegular
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.DPhaseMeas
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_2

/-!
# `PartIII-b:C/rep/8/1/1/2/4/4` (`measYA`): measurability of the phase part of `Y_A`

Source `the November 2 reference manuscript`
lines 5415-5432 (the normalized phase `L²` estimates of `Y_A = 𝒞_y W_μ`; measurability is
implicit), 4168-4186 (`W_μ` of the old source, outward primitive, stream cutoff).

* (joint measurability of the phase part) `zWAct = Re W_μ(oldPhys(thinG))` and
  `zWMid = Re W_μ(oldPhys(meanQ thinG))` are jointly measurable in `(τ, y)` (the separated kernel
  response of a measurable chart tensor, `T8_1.measurable_sepW_comp`), and `C²` in `y` on the open
  clear region at every phase (`ZRegYA.zWAct_cd`, `ZRegYA.zWMid_cd`); the derivative is the limit
  of measurable difference quotients (`DPhaseMeasAux.measurable_fderiv_apply_on`).
* (measurability along the cell) the receiver `chartY R (s,(q,η))` does not depend on `q`, the
  phase `chartTau R (s,(q,η)) = 2q/R + log s` is affine in `q`, and `mnYA` is phase free.
  `actYA = 𝒞_y zWAct` is jointly measurable (`outPrim_measurable`, measurable cutoff profile) and
  differentiable off the axis at every phase (`Sub8_1_1_2_3.cutW_diffAt` with the separated
  representative of `thinSepData`), so `τ ↦ D_y actYA(τ, y₀)` is measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace MeasYAAux

open GeomXAsm GeomXAsm.DPhaseMeasAux ZRegYA

/-- `Re W_μ` of a measurable source is jointly measurable in `(τ, y)`. -/
theorem measurable_sepWre (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 j k) :
    Measurable fun p : ℝ × Space => sepWre ν μ T p.1 p.2 := by
  have hcomp : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i).re :=
    fun i => Complex.measurable_re.comp (T8_1.measurable_sepW_comp ν (μ : ℂ) T i hT)
  unfold sepWre
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp (measurable_pi_iff.2 hcomp)

/-- The Ward stream cutoff of a jointly measurable field is jointly measurable (as
`T8_4.t84_ward_stream`). -/
theorem measurable_wardStreamCut {ν R : ℝ} {χy : ℝ → ℝ} (hχy : Continuous χy)
    {Z : ℝ → Space → Space} (hZ : Measurable fun p : ℝ × Space => Z p.1 p.2) :
    Measurable fun p : ℝ × Space => wardStreamCut ν R χy Z p.1 p.2 := by
  have hO : Measurable fun q : ℝ × ℝ × ℝ => outPrim Z q.1 q.2.1 q.2.2 := outPrim_measurable hZ
  have hcoord : ∀ i : Fin 3, Measurable fun y : Space => y i := fun i =>
    (measurable_pi_apply i).comp (PiLp.continuous_ofLp 2 _).measurable
  have hϱ : Measurable fun y : Space => ϱ y := UnforcedLeray.Axi.continuous_ϱ.measurable
  have hage : Measurable fun y : Space => age R y := by
    unfold age
    exact measurable_const.div (hϱ.pow_const 2)
  have hϱp : Measurable fun p : ℝ × Space => ϱ p.2 := hϱ.comp measurable_snd
  have hagep : Measurable fun p : ℝ × Space => ν * age R p.2 :=
    (hage.comp measurable_snd).const_mul ν
  have hA : Measurable fun p : ℝ × Space => χy (ν * age R p.2) := hχy.measurable.comp hagep
  have hD : Measurable fun p : ℝ × Space => deriv χy (ν * age R p.2) :=
    (measurable_deriv χy).comp hagep
  have hF : Measurable fun p : ℝ × Space => outPrim Z p.1 (ϱ p.2) (p.2 2) :=
    hO.comp (measurable_fst.prodMk (hϱp.prodMk ((hcoord 2).comp measurable_snd)))
  have hscal : Measurable fun p : ℝ × Space =>
      deriv χy (ν * age R p.2) * (-2 * ν * R ^ 2 / ϱ p.2 ^ 3) / ϱ p.2 *
        outPrim Z p.1 (ϱ p.2) (p.2 2) :=
    ((hD.mul (measurable_const.div (hϱp.pow_const 3))).div hϱp).mul hF
  unfold wardStreamCut
  exact (hA.smul hZ).add (hscal.smul measurable_const)

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

theorem measurable_zWAct (T : LStr Pl K L) :
    Measurable fun p : ℝ × Space => zWAct Pl K L μ T p.1 p.2 :=
  measurable_sepWre L.ν μ _ fun j k =>
    T8_1.measurable_oldPhys_entry _ _ _ (measurable_thinG Pl K L T) j k

theorem measurable_zWMid (T : LStr Pl K L) :
    Measurable fun p : ℝ × Space => zWMid Pl K L μ T p.1 p.2 :=
  measurable_sepWre L.ν μ _ fun j k =>
    T8_1.measurable_oldPhys_entry _ _ _ (measurable_meanQ _ (measurable_thinG Pl K L T)) j k

/-- Joint measurability of `1_clear · dPhaseW` (as `DPhaseMeasAux.dPhase_measurable`). -/
theorem dPhaseW_measurable (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hμ : -(1 / 4) < μ)
    (T : LStr Pl K L) :
    Measurable fun p : ℝ × Space =>
      (clearSet L.ε L.ν).indicator (fun y => dPhaseW Pl K L μ T p.1 y) p.2 := by
  classical
  have hS : IsOpen (clearSet L.ε L.ν) := GeomYAGen.isOpen_clearSet _ _
  have hA := measurable_zWAct Pl K L μ T
  have hM := measurable_zWMid Pl K L μ T
  have hdA : ∀ τ y, y ∈ clearSet L.ε L.ν → DifferentiableAt ℝ (zWAct Pl K L μ T τ) y := by
    intro τ y hy
    have h := zWAct_cd Pl K L μ hC0 hmZ hμ T τ
    exact (h.differentiableOn (by norm_num)).differentiableAt (hS.mem_nhds hy)
  have hdM : ∀ τ y, y ∈ clearSet L.ε L.ν → DifferentiableAt ℝ (zWMid Pl K L μ T τ) y := by
    intro τ y hy
    have h := zWMid_cd Pl K L μ hC0 hmZ hμ T τ
    exact (h.differentiableOn (by norm_num)).differentiableAt (hS.mem_nhds hy)
  have hj : ∀ j : Fin 3, Measurable fun p : ℝ × Space =>
      if p.2 ∈ clearSet L.ε L.ν then
        (fderiv ℝ (zWAct Pl K L μ T p.1) p.2 - fderiv ℝ (zWMid Pl K L μ T p.1) p.2)
          (coordinateVector j) else 0 := by
    intro j
    have := (measurable_fderiv_apply_on hS.measurableSet hA hdA (coordinateVector j)).sub
      (measurable_fderiv_apply_on hS.measurableSet hM hdM (coordinateVector j))
    convert this using 1
    funext p
    by_cases hp : p.2 ∈ clearSet L.ε L.ν <;> simp [hp]
  have hnorm : Measurable fun p : ℝ × Space =>
      ‖Gf (fun j => if p.2 ∈ clearSet L.ε L.ν then
        (fderiv ℝ (zWAct Pl K L μ T p.1) p.2 - fderiv ℝ (zWMid Pl K L μ T p.1) p.2)
          (coordinateVector j) else 0)‖ :=
    continuous_norm.measurable.comp (continuous_Gf.measurable.comp (measurable_pi_lambda _ hj))
  convert hnorm using 1
  funext p
  by_cases hp : p.2 ∈ clearSet L.ε L.ν
  · rw [Set.indicator_of_mem hp]
    simp only [if_pos hp]
    rw [Gf_coord]
    rfl
  · rw [Set.indicator_of_notMem hp]
    simp only [if_neg hp]
    have : Gf (fun _ => (0 : Space)) = 0 := by
      ext v : 1
      simp [Gf_apply]
    rw [this]
    simp

/-- `actYA` is jointly measurable. -/
theorem measurable_actYA (hχ : IsStreamCutoff K.χy) (T : LStr Pl K L) :
    Measurable fun p : ℝ × Space => actYA Pl K L μ T p.1 p.2 :=
  measurable_wardStreamCut hχ.smooth.continuous (measurable_zWAct Pl K L μ T)

/-- `actYA` is differentiable off the axis at every phase. -/
theorem actYA_diffAt (hχ : IsStreamCutoff K.χy) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (hμ : -(1 / 4) < μ) (T : LStr Pl K L) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (actYA Pl K L μ T τ) y := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  obtain ⟨S, hS1, hS2, hS3, hresp⟩ := Sub8_1_1_2_3.thinSepData Pl K L hC0 hmZ T
  have hP : 0 < 2 * L.ε * cOf L.ν := by have := cOf_pos hν; positivity
  have hW : thinWardW Pl K L μ T = sepWre L.ν μ S := by
    funext τ' y'
    simp only [thinWardW, sepWre, hresp]
  unfold actYA
  rw [hW]
  exact Sub8_1_1_2_3.cutW_diffAt hχ hν (inv_pos.2 hε) hμ hP hS1 hS2 hS3 τ hy

/-- At a fixed off-axis receiver, `τ ↦ D_y actYA(τ, y₀)` is measurable. -/
theorem measurable_fderiv_actYA (hχ : IsStreamCutoff K.χy) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (hμ : -(1 / 4) < μ) (T : LStr Pl K L) {y₀ : Space} (hy₀ : 0 < ϱ y₀) :
    Measurable fun τ : ℝ => fderiv ℝ (actYA Pl K L μ T τ) y₀ := by
  classical
  set S : Set Space := {y : Space | 0 < ϱ y} with hSdef
  have hSo : IsOpen S := isOpen_lt continuous_const UnforcedLeray.Axi.continuous_ϱ
  have hF := measurable_actYA Pl K L μ hχ T
  have hd : ∀ τ y, y ∈ S → DifferentiableAt ℝ (actYA Pl K L μ T τ) y :=
    fun τ y hy => actYA_diffAt Pl K L μ hχ hC0 hmZ hμ T τ hy
  have hj : ∀ j : Fin 3, Measurable fun τ : ℝ =>
      fderiv ℝ (actYA Pl K L μ T τ) y₀ (coordinateVector j) := by
    intro j
    have h := (measurable_fderiv_apply_on hSo.measurableSet hF hd (coordinateVector j)).comp
      (measurable_id.prodMk (measurable_const (a := y₀)))
    have hy₀S : y₀ ∈ S := hy₀
    convert h using 1
    funext τ
    simp [hy₀S]
  have hG : Measurable fun τ : ℝ =>
      Gf (fun j => fderiv ℝ (actYA Pl K L μ T τ) y₀ (coordinateVector j)) :=
    continuous_Gf.measurable.comp (measurable_pi_lambda _ hj)
  convert hG using 1
  funext τ
  rw [Gf_coord]

/-- `MeasYAAt` at one regime. -/
theorem measYAAt_of (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) : MeasYAAt Pl K L μ := by
  intro hLH T
  have hμ : -(1 / 4) < μ := by linarith [hLH.mu_pos]
  refine ⟨dPhaseW_measurable Pl K L μ hC0 hmZ hμ T, fun s hs η => ?_⟩
  have hs0 : 0 < s := hs.1
  set y₀ : Space := NearInst.chartY L.ε⁻¹ (s, (0, η)) with hy₀def
  have hy : ∀ q : ℝ, NearInst.chartY L.ε⁻¹ (s, (q, η)) = y₀ := fun q => rfl
  have hy₀ : 0 < ϱ y₀ := by
    rw [hy₀def, chartY_eq_hpt]
    have hρ : 0 < L.ε⁻¹ / Real.sqrt s := div_pos (inv_pos.2 L.ε_pos) (Real.sqrt_pos.2 hs0)
    rw [ZPrimKernel.ϱ_hpt hρ]
    exact hρ
  have hτ : Measurable fun q : ℝ => NearInst.chartTau L.ε⁻¹ (s, (q, η)) := by
    unfold NearInst.chartTau
    fun_prop
  have hm := (measurable_fderiv_actYA Pl K L μ hLH.chiY hC0 hmZ hμ T hy₀).comp hτ
  have hfun : (fun q : ℝ => dYA Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
      (NearInst.chartY L.ε⁻¹ (s, (q, η)))) = fun q : ℝ =>
      fderiv ℝ (actYA Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))) y₀ -
        fderiv ℝ (mnYA Pl K L μ T 0) y₀ := by
    funext q
    rw [hy q]
    rfl
  rw [hfun]
  exact (hm.sub measurable_const).aestronglyMeasurable

end Regime

end MeasYAAux

open MeasYAAux in
/-- **`PartIII-b:C/rep/8/1/1/2/4/4`** (`measYA`): at every level, under the standing hypotheses,
`(τ, y) ↦ 1_clear(y) dPhaseW(τ, y)` is measurable and `dYA` is a.e.-strongly measurable along
the cell at every young chart point (source 5415-5432, 4168-4186). -/
theorem measYA (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeasYA := by
  unfold SeqData.MeasYA
  exact Filter.Eventually.of_forall fun n z _ =>
    measYAAt_of D.Pl D.K (D.level n) (D.mu n z) hst.C0_pos (by linarith [hst.mZ_gt])

end UnforcedLeray.Short.PartIIIb.Concrete
