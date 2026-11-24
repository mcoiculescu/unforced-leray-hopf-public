import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3

/-!
# Smoothness of the framed profile (`PartIII-b:C/rep/8/2/1/3/a`, helper 1)

Source lines 5036-5045.  `G = frameL · (B ∘ chart)` is `C²` off the axis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete

theorem contDiffOn_chart (R τ : ℝ) (hR : 0 < R) {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (chart R τ) axisᶜ := by
  have hϱ : ContDiffOn ℝ k ϱ axisᶜ := contDiffOn_ϱ
  have hϱ2 : ∀ y ∈ (axisᶜ : Set Space), ϱ y ^ 2 ≠ 0 := fun y hy => pow_ne_zero 2 (ϱ_ne_zero hy)
  have hage : ContDiffOn ℝ k (age R) axisᶜ :=
    contDiffOn_const.div (hϱ.pow 2) hϱ2
  have hage0 : ∀ y ∈ (axisᶜ : Set Space), age R y ≠ 0 := fun y hy => (age_pos hR.ne' hy).ne'
  have hphase : ContDiffOn ℝ k (phase R τ) axisᶜ :=
    contDiffOn_const.sub (contDiffOn_const.mul (hage.log hage0))
  have h2 : ContDiff ℝ k (fun y : Space => y 2) := by fun_prop
  have htrans : ContDiffOn ℝ k (trans R) axisᶜ :=
    (contDiffOn_const.mul h2.contDiffOn).div hϱ fun y hy => ϱ_ne_zero hy
  exact hage.prodMk (hphase.prodMk htrans)

theorem mapsTo_chart (R τ : ℝ) (hR : 0 < R) :
    MapsTo (chart R τ) axisᶜ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  fun y hy => ⟨age_pos hR.ne' hy, trivial⟩

theorem contDiffOn_frame (R τ : ℝ) (hR : 0 < R) (B : ℝ × (ℝ × ℝ) → Merid)
    (hB : ContDiffOn ℝ 2 B (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) :
    ContDiffOn ℝ 2 (fun y' => frameL y' (B (chart R τ y'))) axisᶜ := by
  have hbm : ContDiffOn ℝ 2 (fun y => B (chart R τ y)) axisᶜ :=
    hB.comp (contDiffOn_chart R τ hR) (mapsTo_chart R τ hR)
  have hb0 : ContDiffOn ℝ 2 (fun y => B (chart R τ y) 0) axisᶜ :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbm
  have hb1 : ContDiffOn ℝ 2 (fun y => B (chart R τ y) 1) axisᶜ :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbm
  have := (hb0.smul contDiffOn_eR).add (hb1.smul (contDiffOn_const (c := e3)))
  refine this.congr fun y _ => ?_
  simp only [frameL_apply]
  rfl

theorem contDiffAt_frame (R τ : ℝ) (hR : 0 < R) (B : ℝ × (ℝ × ℝ) → Merid)
    (hB : ContDiffOn ℝ 2 B (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) {y : Space} (hy : y ∉ axis) :
    ContDiffAt ℝ 2 (fun y' => frameL y' (B (chart R τ y'))) y :=
  (contDiffOn_frame R τ hR B hB).contDiffAt (isOpen_compl_axis.mem_nhds hy)

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux
