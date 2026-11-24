import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0StrongCont.CcDense
import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0StrongCont.DilWCc

/-!
# Helper for `PartIII-a:T21/c3/2/1/2/3/1`: strong continuity of the weighted dilation

Source: `the November 2 reference manuscript` lines 2914-2925 (the moving
complement is the zero extension of a field on the moving cell; its dependence on the age goes
through the dilation `J_a`, strongly continuous in `a` by the `ε/3` argument of SP 946-953).

* `dilR hM a`: the dilation `Planar.dilW hM` at `a > 0`, extended by `0` for `a ≤ 0`.
* `continuousAt_dilR_apply`: `a ↦ J_a f` is continuous at every `a₀ > 0` (density of
  compactly supported continuous functions `PartI.l2wCcDense`, continuity on them
  `PartI.dilWCcCont`, local operator bound `Planar.norm_dilW_le`).
* `continuousWithinAt_clm_apply`: a locally bounded, strongly continuous operator family applied
  to a continuous path is continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIIa.ComplMildYAux

/-- The dilation `J_a` on `L²_M`, extended by `0` for `a ≤ 0`. -/
def dilR {M : ℝ} (hM : 1 < M) (a : ℝ) : Planar.L2w M →L[ℂ] Planar.L2w M :=
  if h : 0 < a then Planar.dilW hM h else 0

theorem dilR_of_pos {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilR hM a = Planar.dilW hM ha := dif_pos ha

theorem norm_dilR_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    ‖dilR hM a‖ ≤ Planar.dilConst M a := by
  rw [dilR_of_pos hM ha]
  exact Planar.norm_dilW_le hM ha

/-- Strong continuity of `a ↦ J_a G` at `a₀ > 0` for compactly supported continuous `G`. -/
theorem continuousAt_dilR_cc {M : ℝ} (hM : 1 < M) (G : Planar.L2w M) (hG : PartI.IsCcRep G)
    {a₀ : ℝ} (ha₀ : 0 < a₀) : ContinuousAt (fun a => dilR hM a G) a₀ := by
  have h := PartI.dilWCcCont M hM G hG a₀ ha₀
  have hw : ContinuousWithinAt (fun a => dilR hM a G) (Ioi 0) a₀ := by
    rw [continuousWithinAt_iff_continuousAt_domRestrict _ (show a₀ ∈ Ioi (0 : ℝ) from ha₀)]
    have heq : (Ioi (0 : ℝ)).domRestrict (fun a => dilR hM a G) =
        fun a : Ioi (0 : ℝ) => Planar.dilW hM a.2 G := by
      funext a
      simp only [Set.domRestrict_apply, dilR_of_pos hM a.2]
    rw [heq]
    exact h
  exact hw.continuousAt (Ioi_mem_nhds ha₀)

/-- **Strong continuity of the dilation** on `L²_M`: `a ↦ J_a f` is continuous at `a₀ > 0`. -/
theorem continuousAt_dilR_apply {M : ℝ} (hM : 1 < M) (f : Planar.L2w M) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ContinuousAt (fun a => dilR hM a f) a₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set C : ℝ := Planar.dilConst M a₀ + 1 with hC
  have hC0 : 0 < C := by
    have := Planar.dilConst_nonneg M a₀
    rw [hC]; linarith
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    Metric.continuousAt_iff.1 (PartI.dilConst_continuousAt M a₀ ha₀) 1 one_pos
  have hδ : 0 < ε / (4 * C) := by positivity
  obtain ⟨G, hG, hGF⟩ := PartI.l2wCcDense M hM f (ε / (4 * C)) hδ
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ :=
    Metric.continuousAt_iff.1 (continuousAt_dilR_cc hM G hG ha₀) (ε / 2) (by positivity)
  refine ⟨min (min δ₁ δ₂) a₀, lt_min (lt_min hδ₁ hδ₂) ha₀, fun {a} ha => ?_⟩
  have ha1 : dist a a₀ < δ₁ := lt_of_lt_of_le ha ((min_le_left _ _).trans (min_le_left _ _))
  have ha2 : dist a a₀ < δ₂ := lt_of_lt_of_le ha ((min_le_left _ _).trans (min_le_right _ _))
  have ha3 : dist a a₀ < a₀ := lt_of_lt_of_le ha (min_le_right _ _)
  have ha0 : 0 < a := by
    rw [Real.dist_eq] at ha3
    have := neg_abs_le (a - a₀)
    linarith
  have hca : Planar.dilConst M a < C := by
    have := hδ₁' ha1
    rw [Real.dist_eq] at this
    have := le_abs_self (Planar.dilConst M a - Planar.dilConst M a₀)
    rw [hC]; linarith
  have hFG : ‖f - G‖ < ε / (4 * C) := by rw [norm_sub_rev]; exact hGF
  have hN : 0 ≤ ‖f - G‖ := norm_nonneg _
  have e1 : ‖dilR hM a (f - G)‖ ≤ C * ‖f - G‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((norm_dilR_le hM ha0).trans hca.le) hN)
  have e2 : ‖dilR hM a₀ (f - G)‖ ≤ C * ‖f - G‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((norm_dilR_le hM ha₀).trans (by rw [hC]; linarith)) hN)
  have e3 : C * ‖f - G‖ < ε / 4 := by
    calc C * ‖f - G‖ < C * (ε / (4 * C)) := mul_lt_mul_of_pos_left hFG hC0
      _ = ε / 4 := by field_simp
  have e4 : ‖dilR hM a G - dilR hM a₀ G‖ < ε / 2 := by
    have := hδ₂' ha2
    rwa [dist_eq_norm] at this
  have key : dilR hM a f - dilR hM a₀ f =
      dilR hM a (f - G) + (dilR hM a G - dilR hM a₀ G) - dilR hM a₀ (f - G) := by
    simp only [map_sub]; abel
  rw [dist_eq_norm, key]
  calc _ ≤ ‖dilR hM a (f - G) + (dilR hM a G - dilR hM a₀ G)‖ + ‖dilR hM a₀ (f - G)‖ :=
        norm_sub_le _ _
    _ ≤ ‖dilR hM a (f - G)‖ + ‖dilR hM a G - dilR hM a₀ G‖ + ‖dilR hM a₀ (f - G)‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- A locally bounded family of operators that is strongly continuous at the limit point,
applied to a continuous path, gives a continuous path. -/
theorem continuousWithinAt_clm_apply {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : X → E →L[ℂ] F} {g : X → E} {S : Set X} {x₀ : X} {C : ℝ}
    (hT : ∀ x ∈ S, ‖T x‖ ≤ C) (hTs : ContinuousWithinAt (fun x => T x (g x₀)) S x₀)
    (hg : ContinuousWithinAt g S x₀) :
    ContinuousWithinAt (fun x => T x (g x)) S x₀ := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun x => ‖g x - g x₀‖) (𝓝[S] x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hg
  have h2 : Tendsto (fun x => ‖T x (g x₀) - T x₀ (g x₀)‖) (𝓝[S] x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hTs
  have h3 : Tendsto (fun x => C * ‖g x - g x₀‖ + ‖T x (g x₀) - T x₀ (g x₀)‖) (𝓝[S] x₀)
      (𝓝 0) := by
    simpa using (h1.const_mul C).add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with x hx
  calc ‖T x (g x) - T x₀ (g x₀)‖
      = ‖T x (g x - g x₀) + (T x (g x₀) - T x₀ (g x₀))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖T x (g x - g x₀)‖ + ‖T x (g x₀) - T x₀ (g x₀)‖ := norm_add_le _ _
    _ ≤ C * ‖g x - g x₀‖ + ‖T x (g x₀) - T x₀ (g x₀)‖ := by
        gcongr
        exact (T x).le_of_opNorm_le (hT x hx) _

end UnforcedLeray.Short.IIIa.ComplMildYAux
