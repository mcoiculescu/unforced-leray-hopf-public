import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.XKerA

/-!
# Compact-region bounds for smooth functions off the axis, and the ring map `y ↦ (ϱ y, 0, y₃)`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- The ring map `y ↦ (ϱ y, 0, y₃)`. -/
def ringMap (y : Space) : Space := !₂[ϱ y, 0, y 2]

namespace RingMapOff

theorem isOpen_offAxis : IsOpen {y : Space | 0 < ϱ y} := isOpen_lt continuous_const continuous_ϱ

end RingMapOff

theorem axis_compl_of_pos {y : Space} (hy : 0 < ϱ y) : y ∈ axisᶜ := by
  intro h
  have : ϱ y = 0 := by
    unfold ϱ; rw [h.1, h.2]; simp
  linarith

theorem contDiffOn_ϱ_pos : ContDiffOn ℝ 2 ϱ {y : Space | 0 < ϱ y} :=
  (contDiffOn_ϱ (k := 2)).mono (fun y hy => axis_compl_of_pos hy)

theorem contDiffOn_ringMap : ContDiffOn ℝ 2 ringMap {y : Space | 0 < ϱ y} := by
  unfold ringMap
  refine PiLp.contDiff_toLp.comp_contDiffOn ?_
  refine contDiffOn_pi.2 fun i => ?_
  fin_cases i
  · simpa using contDiffOn_ϱ_pos
  · simpa using contDiffOn_const
  · simpa using ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffOn)

/-- Bounds of the derivatives of orders `≤ 2` of a function smooth off the axis, on a compact region. -/
theorem region_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : ContDiffOn ℝ 2 f {y : Space | 0 < ϱ y}) {r₁ : ℝ} (hr : 0 < r₁) (Y : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Space, r₁ ≤ ϱ y → ‖y‖ ≤ Y → ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  set K : Set Space := {y | r₁ ≤ ϱ y} ∩ {y | ‖y‖ ≤ Y} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_ϱ).inter (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : Space)) (r := Y)).subset (fun y hy => by
        simpa using hy.2)
  have hKs : K ⊆ {y : Space | 0 < ϱ y} := fun y hy => lt_of_lt_of_le hr hy.1
  have hcont : ∀ i : ℕ, i ≤ 2 → ContinuousOn (fun y => iteratedFDeriv ℝ i f y) {y : Space | 0 < ϱ y} := by
    intro i hi
    have := hf.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast hi) RingMapOff.isOpen_offAxis.uniqueDiffOn
    exact this.congr (fun y hy => (iteratedFDerivWithin_of_isOpen i RingMapOff.isOpen_offAxis hy).symm)
  have hb : ∀ i : ℕ, i ≤ 2 → ∃ b : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ b := fun i hi =>
    hKc.exists_bound_of_continuousOn ((hcont i hi).mono hKs)
  obtain ⟨b0, h0⟩ := hb 0 (by norm_num)
  obtain ⟨b1, h1⟩ := hb 1 (by norm_num)
  obtain ⟨b2, h2⟩ := hb 2 (by norm_num)
  refine ⟨|b0| + |b1| + |b2|, by positivity, fun y hy1 hy2 i hi => ?_⟩
  have hyK : y ∈ K := ⟨hy1, hy2⟩
  interval_cases i
  · exact (h0 y hyK).trans (by nlinarith [le_abs_self b0, abs_nonneg b1, abs_nonneg b2])
  · exact (h1 y hyK).trans (by nlinarith [le_abs_self b1, abs_nonneg b0, abs_nonneg b2])
  · exact (h2 y hyK).trans (by nlinarith [le_abs_self b2, abs_nonneg b1, abs_nonneg b0])

/-- Chain-rule bound on open sets: the `n`-th derivative of `g ∘ f`, `n ≤ 2`. -/
theorem comp_bound_open {g : Space → ℝ} {f : Space → Space} {U s : Set Space} (hU : IsOpen U)
    (hs : IsOpen s) (hg : ContDiffOn ℝ 2 g U) (hf : ContDiffOn ℝ 2 f s) (hst : MapsTo f s U)
    {y : Space} (hy : y ∈ s) {C D : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f y)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f y‖ ≤ D ^ i) (n : ℕ) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (g ∘ f) y‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  have := norm_iteratedFDerivWithin_comp_le (n := n) (x := y) (N := 2) hg hf (by exact_mod_cast hn)
    hU.uniqueDiffOn hs.uniqueDiffOn hst hy (C := C) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hU (hst hy)]; exact hC i (hi.trans hn))
    (fun i h1 hi => by
      rw [iteratedFDerivWithin_of_isOpen i hs hy]; exact hD i h1 (hi.trans hn))
  rwa [iteratedFDerivWithin_of_isOpen n hs hy] at this

end UnforcedLeray.Short.PartIIIb.Concrete

end
