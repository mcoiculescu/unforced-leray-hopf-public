import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Lib.Kernels.HeatTimePotential
import UnforcedLeray.Lib.HeatR3.FTC

/-!
# Utilities for the heat equation of `K_t` (`HeatLerayKHeat`, source 3598-3610)

Directional derivative operator `D a g = (y ↦ ∂_a g(y))`, commutation of `D`, `part2 f i j = D i (D j f)`,
`heatTail t = ∫_t^∞ G` is the library time potential, and the fundamental theorem of calculus
for `s ↦ ∫_s^∞ Φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Directional derivative as a function. -/
def Dd (a : Space) (g : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ g y a

lemma Dd_smooth {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (a : Space) : ContDiff ℝ ∞ (Dd a g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma Dd_comm {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Space) :
    Dd a (Dd b g) = Dd b (Dd a g) := by
  funext x
  have h1 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hs := (hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  change (fderiv ℝ (fun y => fderiv ℝ g y b) x) a = (fderiv ℝ (fun y => fderiv ℝ g y a) x) b
  rw [fderiv_clm_apply h1 (differentiableAt_const _), fderiv_clm_apply h1 (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hs a b

lemma Dd_sum {ι : Type*} (s : Finset ι) {g : ι → Space → ℝ} (hg : ∀ l, ContDiff ℝ ∞ (g l))
    (a : Space) :
    Dd a (fun y => ∑ l ∈ s, g l y) = fun y => ∑ l ∈ s, Dd a (g l) y := by
  funext y
  have hd : ∀ l ∈ s, DifferentiableAt ℝ (g l) y := fun l _ => (hg l).differentiable (by simp) y
  simp only [Dd]
  rw [fderiv_fun_sum hd]
  simp

lemma Dd_add {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a : Space) :
    Dd a (fun y => f y + g y) = fun y => Dd a f y + Dd a g y := by
  funext y
  simp only [Dd]
  rw [fderiv_fun_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
  rfl

lemma Dd_neg (g : Space → ℝ) (a : Space) : Dd a (fun y => - g y) = fun y => - Dd a g y := by
  funext y; simp only [Dd]; rw [fderiv_fun_neg]; rfl

/-- `part2 f i j = D_i D_j f`. -/
lemma part2_eq_Dd (f : Space → ℝ) (i j : Fin 3) :
    IIIa.part2 f i j = Dd (UnforcedLeray.coordinateVector i) (Dd (UnforcedLeray.coordinateVector j) f) := rfl

lemma part2_eq_iter {f : Space → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 3) (x : Space) :
    IIIa.part2 f i j x = iteratedFDeriv ℝ 2 f x ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector j] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [iteratedFDeriv_two_apply]
  unfold IIIa.part2
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  simp

lemma heatTail_eq_potential (t : ℝ) : IIIa.heatTail t = Kernels.heatTimePotential t := by
  funext x
  unfold IIIa.heatTail Kernels.heatTimePotential
  simp only [IIIa.heatG_eq_heatKernel]

lemma heatTail_smooth {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (IIIa.heatTail t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rw [heatTail_eq_potential]
  exact Kernels.contDiffAt_heatTimePotential ht.le (Or.inr ht)

lemma heatG_smooth (t : ℝ) : ContDiff ℝ ∞ (IIIa.heatG t) := by
  rw [IIIa.heatG_eq_heatKernel]
  exact Kernels.heatKernel_smooth t

/-- FTC for `s ↦ ∫_s^∞ Φ`. -/
lemma hasDerivAt_integral_Ioi {Φ : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hc : ContinuousOn Φ (Ioi 0))
    (hi : IntegrableOn Φ (Ioi (t / 2))) :
    HasDerivAt (fun s => ∫ a in Ioi s, Φ a) (-Φ t) t := by
  have hc2 : 0 < t / 2 := by positivity
  have hsplit : ∀ s ∈ Ioi (t / 2), ∫ a in Ioi s, Φ a =
      (∫ a in Ioi (t / 2), Φ a) - ∫ a in (t / 2)..s, Φ a := by
    intro s hs
    have hs' : t / 2 ≤ s := le_of_lt hs
    have hu : Ioc (t / 2) s ∪ Ioi s = Ioi (t / 2) := Ioc_union_Ioi_eq_Ioi hs'
    have h1 : IntegrableOn Φ (Ioc (t / 2) s) := hi.mono_set (fun a ha => ha.1)
    have h2 : IntegrableOn Φ (Ioi s) := hi.mono_set (Ioi_subset_Ioi hs')
    have := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2
    rw [hu] at this
    rw [this, intervalIntegral.integral_of_le hs']
    ring
  have hcont : ContinuousOn Φ (Ioi (t / 2)) := hc.mono (Ioi_subset_Ioi hc2.le)
  have hint : IntervalIntegrable Φ volume (t / 2) t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hi.mono_set (fun a ha => ha.1)
  have hmeas := hcont.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi t (by simp only [mem_Ioi]; linarith)
  have hca : ContinuousAt Φ t := hc.continuousAt (Ioi_mem_nhds ht)
  have hd := (intervalIntegral.integral_hasDerivAt_right hint hmeas hca).const_sub
    (∫ a in Ioi (t / 2), Φ a)
  refine HasDerivAt.congr_of_eventuallyEq hd ?_
  filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with s hs using hsplit s hs

end UnforcedLeray.Short.PartIIIb.Concrete
