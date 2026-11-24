import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula.First

/-!
# Second derivatives along lines (`PartIII-b:C/rep/8/2/1/3/a`, helper 3)

`physPd2 G j l y` is the derivative at `t = 0` of `t ↦ physPd G l (y + t e_j)`; profile
derivatives along lines through the chart; `C¹` of `Dρ B`, `Dz B`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete

/-! ### `C¹` of the profile operators -/

theorem contDiffAt_dQ {B : ℝ × (ℝ × ℝ) → Merid} {x : ℝ × (ℝ × ℝ)} (hB : ContDiffAt ℝ 2 B x) :
    ContDiffAt ℝ 1 (UnforcedLeray.Axi.dQ B) x := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ B) x := hB.fderiv_right (by norm_num)
  exact h.clm_apply contDiffAt_const

theorem contDiffAt_dS {B : ℝ × (ℝ × ℝ) → Merid} {x : ℝ × (ℝ × ℝ)} (hB : ContDiffAt ℝ 2 B x) :
    ContDiffAt ℝ 1 (UnforcedLeray.Axi.dS B) x := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ B) x := hB.fderiv_right (by norm_num)
  exact h.clm_apply contDiffAt_const

theorem contDiffAt_dEta {B : ℝ × (ℝ × ℝ) → Merid} {x : ℝ × (ℝ × ℝ)} (hB : ContDiffAt ℝ 2 B x) :
    ContDiffAt ℝ 1 (UnforcedLeray.Axi.dEta B) x := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ B) x := hB.fderiv_right (by norm_num)
  exact h.clm_apply contDiffAt_const

theorem contDiffAt_Drho (ε : ℝ) {B : ℝ × (ℝ × ℝ) → Merid} {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.1)
    (hB : ContDiffAt ℝ 2 B x) : ContDiffAt ℝ 1 (Drho ε B) x := by
  have hsq : ContDiffAt ℝ 1 (fun x : ℝ × (ℝ × ℝ) => Real.sqrt x.1) x :=
    (Real.contDiffAt_sqrt hx.ne').comp x contDiff_fst.contDiffAt
  have h1 : ContDiffAt ℝ 1 (fun x : ℝ × (ℝ × ℝ) => x.1) x := contDiff_fst.contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun x : ℝ × (ℝ × ℝ) => x.2.2) x :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have := hsq.smul ((contDiffAt_dQ hB).sub
    ((contDiffAt_const (c := ε)).smul (((contDiffAt_const (c := (2:ℝ))).mul h1).smul
      (contDiffAt_dS hB) |>.add (h2.smul (contDiffAt_dEta hB)))))
  exact this

theorem contDiffAt_Dz {B : ℝ × (ℝ × ℝ) → Merid} {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.1)
    (hB : ContDiffAt ℝ 2 B x) : ContDiffAt ℝ 1 (Dz B) x := by
  have hsq : ContDiffAt ℝ 1 (fun x : ℝ × (ℝ × ℝ) => Real.sqrt x.1) x :=
    (Real.contDiffAt_sqrt hx.ne').comp x contDiff_fst.contDiffAt
  exact hsq.smul (contDiffAt_dEta hB)

/-! ### Lines -/

theorem hasDerivAt_line (y v : Space) :
    HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y

theorem physPd2_hasDerivAt {G : Space → Space} {y : Space} (hG : ContDiffAt ℝ 2 G y)
    (j l : Fin 3) :
    HasDerivAt (fun t : ℝ => physPd G l (y + t • coordinateVector j)) (physPd2 G j l y) 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΦ : HasFDerivAt (fun y' => physPd G l y')
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector l)).comp (fderiv ℝ (fderiv ℝ G) y)) y :=
    (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).hasFDerivAt.comp y hd.hasFDerivAt
  have hl := hasDerivAt_line y (coordinateVector j)
  have hΦ' : HasFDerivAt (fun y' => physPd G l y')
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector l)).comp (fderiv ℝ (fderiv ℝ G) y))
      ((fun t : ℝ => y + t • coordinateVector j) 0) := by simpa using hΦ
  have := hΦ'.comp_hasDerivAt (0:ℝ) hl
  have e : physPd2 G j l y = ((ContinuousLinearMap.apply ℝ Space (coordinateVector l)).comp
      (fderiv ℝ (fderiv ℝ G) y)) (coordinateVector j) := by
    change fderiv ℝ (fun y' => physPd G l y') y (coordinateVector j) = _
    rw [hΦ.fderiv]
  rw [e]
  exact this

theorem physPd2_eq_fderiv {G : Space → Space} {y : Space} (hG : ContDiffAt ℝ 2 G y)
    (j l : Fin 3) :
    physPd2 G j l y = fderiv ℝ (fderiv ℝ G) y (coordinateVector j) (coordinateVector l) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΦ : HasFDerivAt (fun y' => physPd G l y')
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector l)).comp (fderiv ℝ (fderiv ℝ G) y)) y :=
    (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).hasFDerivAt.comp y hd.hasFDerivAt
  change fderiv ℝ (fun y' => physPd G l y') y (coordinateVector j) = _
  rw [hΦ.fderiv]
  rfl

theorem physPd2_symm {G : Space → Space} {y : Space} (hG : ContDiffAt ℝ 2 G y) (j l : Fin 3) :
    physPd2 G j l y = physPd2 G l j y := by
  rw [physPd2_eq_fderiv hG, physPd2_eq_fderiv hG]
  exact (hG.isSymmSndFDerivAt (by simp)) _ _

/-- Profile derivative along a line through the chart. -/
theorem hasDerivAt_prof_line {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis)
    {F : ℝ × (ℝ × ℝ) → Merid} (hF : DifferentiableAt ℝ F (chart R τ y)) (v : Space) :
    HasDerivAt (fun t : ℝ => F (chart R τ (y + t • v)))
      (fderiv ℝ F (chart R τ y) (chartD R y v)) 0 := by
  have h1 : HasFDerivAt (chart R τ) (chartD R y) ((fun t : ℝ => y + t • v) 0) := by
    simpa using hasFDerivAt_chart hR.ne' τ hy
  have hc : HasDerivAt (fun t : ℝ => chart R τ (y + t • v)) (chartD R y v) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := chart R τ) (0:ℝ) h1 (hasDerivAt_line y v)
  have h2 : HasFDerivAt F (fderiv ℝ F (chart R τ y)) (chart R τ (y + (0:ℝ) • v)) := by
    simpa using hF.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℝ) hc

theorem fderiv_prof_e0 {R τ : ℝ} (hR : 0 < R) {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0)
    {F : ℝ × (ℝ × ℝ) → Merid} (hF : DifferentiableAt ℝ F (chart R τ y)) :
    fderiv ℝ F (chart R τ y) (chartD R y (coordinateVector 0)) = Drho R⁻¹ F (chart R τ y) := by
  have hy := not_axis_az hy0
  rw [← eR_az hy0 hy1, ← fderiv_comp_chart_apply hR.ne' hy hF, radial_chain hR hy hF]
  rfl

theorem fderiv_prof_e3 {R τ : ℝ} (hR : 0 < R) {y : Space} (hy0 : 0 < y 0)
    {F : ℝ × (ℝ × ℝ) → Merid} (hF : DifferentiableAt ℝ F (chart R τ y)) :
    fderiv ℝ F (chart R τ y) (chartD R y (coordinateVector 2)) = Dz F (chart R τ y) := by
  have hy := not_axis_az hy0
  have h2 : (coordinateVector 2 : Space) = e3 := rfl
  rw [h2, ← fderiv_comp_chart_apply hR.ne' hy hF, axial_chain hR hy hF]
  rfl

/-- The continuous linear form of `merSp`. -/
def merSpL : Merid →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).smulRight (coordinateVector 0) +
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).smulRight e3

theorem merSpL_apply (D : Merid) : merSpL D = merSp D := by
  rw [merSp_eq_local]
  simp [merSpL]

/-- Reading off a second derivative from the line through `y` in direction `e_j`. -/
theorem entry_of_line {G : Space → Space} {y : Space} (hG : ContDiffAt ℝ 2 G y) (j l : Fin 3)
    (hy0 : 0 < y 0) (hy1 : y 1 = 0) (hj : j = 0 ∨ j = 2) (g : Space → Space) (X : Space)
    (hg : ∀ y' : Space, 0 < y' 0 → y' 1 = 0 → physPd G l y' = g y')
    (hd : HasDerivAt (fun t : ℝ => g (y + t • coordinateVector j)) X 0) :
    physPd2 G j l y = X := by
  have h1 := physPd2_hasDerivAt hG j l
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), physPd G l (y + t • coordinateVector j) =
      g (y + t • coordinateVector j) := by
    have hpos : ∀ᶠ t in 𝓝 (0:ℝ), 0 < (y + t • coordinateVector j) 0 := by
      apply ContinuousAt.eventually_lt continuousAt_const
      · fun_prop
      · simpa using hy0
    filter_upwards [hpos] with t ht
    apply hg _ ht
    rcases hj with rfl | rfl <;> simp [hy1, coordinateVector_apply]
  exact h1.unique (hd.congr_of_eventuallyEq hev)

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux
