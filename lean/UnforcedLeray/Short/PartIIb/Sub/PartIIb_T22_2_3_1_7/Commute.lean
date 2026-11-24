import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_7.Basic

/-!


Source: `the November 2 reference manuscript` lines 2100-2105 (joint regularity of
the regular backward problem).  If `g, h` are spatially smooth with jointly continuous partials and
`h` is the time derivative of `g`, then `∂_j h` is the time derivative of `∂_j g`: the fundamental
theorem of calculus `g(s, x) = g(0, x) + ∫₀ˢ h(r, x) dr`, differentiation under the integral in `x`
(the bound comes from compactness of `[0, T] × [-1, 1]` along a line), and the fundamental theorem
again.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace UnforcedLeray.Short.IIb.BwdRoute.Joint

open CylPDE

/-- **Part (a)**: time and space derivatives commute inside the class `SpSmooth`. -/
def TimeSpaceCommute : Prop :=
  ∀ (T : ℝ) (g h : ℝ → Pl → ℝ), 0 < T → SpSmooth T g → SpSmooth T h → HasTimeDeriv T g h →
    ∀ j : Fin 2, HasTimeDeriv T (fun s => B0579.pd j (g s)) (fun s => B0579.pd j (h s))

/-- Continuity in time along a fixed point. -/
theorem contOn_time {T : ℝ} {F : ℝ → Pl → ℝ}
    (hF : ContinuousOn (fun z : ℝ × Pl => F z.1 z.2) (Icc 0 T ×ˢ univ)) (x : Pl) :
    ContinuousOn (fun r => F r x) (Icc 0 T) :=
  ContinuousOn.comp (g := fun z : ℝ × Pl => F z.1 z.2) (f := fun r : ℝ => ((r, x) : ℝ × Pl)) hF
    (by fun_prop) (fun r hr => ⟨hr, mem_univ _⟩)

/-- The fundamental theorem of calculus in time. -/
theorem time_ftc {T : ℝ} {g h : ℝ → Pl → ℝ} (hh : SpSmooth T h) (hgh : HasTimeDeriv T g h)
    {s : ℝ} (hs : s ∈ Icc 0 T) (y : Pl) : g s y = g 0 y + ∫ r in (0 : ℝ)..s, h r y := by
  have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hcont : ContinuousOn (fun r => g r y) (Icc 0 s) := fun r hr =>
    ((hgh r (hsub hr) y).continuousWithinAt).mono hsub
  have hderiv : ∀ r ∈ Ioo 0 s, HasDerivWithinAt (fun r => g r y) (h r y) (Ioi r) r := by
    intro r hr
    have hr' : r ∈ Ioo 0 T := ⟨hr.1, lt_of_lt_of_le hr.2 hs.2⟩
    exact ((hgh r (Ioo_subset_Icc_self hr') y).hasDerivAt
      (Icc_mem_nhds hr'.1 hr'.2)).hasDerivWithinAt
  have hint : IntervalIntegrable (fun r => h r y) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact (contOn_time (hh.cont []) y).mono hsub
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1 hcont hderiv hint
  linarith

/-- The derivative along a coordinate line. -/
theorem hasDerivAt_line {φ : Pl → ℝ} (hφ : Differentiable ℝ φ) (j : Fin 2) (x : Pl) (e : ℝ) :
    HasDerivAt (fun e : ℝ => φ (x + e • B0579.dir j)) (B0579.pd j φ (x + e • B0579.dir j)) e := by
  have h1 : HasDerivAt (fun e : ℝ => x + e • B0579.dir j) (B0579.dir j) e := by
    simpa using ((hasDerivAt_id e).smul_const (B0579.dir j)).const_add x
  exact (hφ _).hasFDerivAt.comp_hasDerivAt e h1

/-- Differentiation under the time integral along a coordinate line. -/
theorem hasDerivAt_line_integral {T : ℝ} {h : ℝ → Pl → ℝ} (hh : SpSmooth T h) {s : ℝ}
    (hs : s ∈ Icc 0 T) (j : Fin 2) (x : Pl) :
    HasDerivAt (fun e : ℝ => ∫ r in (0 : ℝ)..s, h r (x + e • B0579.dir j))
      (∫ r in (0 : ℝ)..s, B0579.pd j (h r) x) 0 := by
  have hsub : Ι (0 : ℝ) s ⊆ Icc 0 T := by
    rw [uIoc_of_le hs.1]
    exact fun r hr => ⟨hr.1.le, hr.2.trans hs.2⟩
  have hmeas : ∀ (F : ℝ → Pl → ℝ) (e : ℝ),
      ContinuousOn (fun z : ℝ × Pl => F z.1 z.2) (Icc 0 T ×ˢ univ) →
      AEStronglyMeasurable (fun r => F r (x + e • B0579.dir j)) (volume.restrict (Ι (0 : ℝ) s)) :=
    fun F e hF => ((contOn_time hF _).mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => B0579.pd j (h p.1) (x + p.2 • B0579.dir j))
      (Icc 0 T ×ˢ Icc (-1) 1) :=
    ContinuousOn.comp (g := fun z : ℝ × Pl => pdW [j] (h z.1) z.2)
      (f := fun p : ℝ × ℝ => ((p.1, x + p.2 • B0579.dir j) : ℝ × Pl)) (hh.cont [j])
      (by fun_prop) (fun p hp => ⟨hp.1, mem_univ _⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hΦ
  have hint : IntervalIntegrable (fun r => h r (x + (0 : ℝ) • B0579.dir j)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact (contOn_time (hh.cont []) _).mono (Icc_subset_Icc_right hs.2)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (a := 0) (b := s)
    (F := fun e r => h r (x + e • B0579.dir j))
    (F' := fun e r => B0579.pd j (h r) (x + e • B0579.dir j))
    (x₀ := 0) (s := Ioo (-1) 1) (bound := fun _ => C)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun e => hmeas h e (hh.cont []))
    hint
    (hmeas (fun r => B0579.pd j (h r)) 0 (hh.cont [j]))
    (Eventually.of_forall fun r hr e he => hC (r, e) ⟨hsub hr, Ioo_subset_Icc_self he⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun r hr e _ =>
      hasDerivAt_line ((hh.slice r (hsub hr)).differentiable (by simp)) j x e)
  have e0 : x + (0 : ℝ) • B0579.dir j = x := by simp
  simpa only [e0] using key.2

/-- The fundamental theorem of calculus for the partial. -/
theorem pd_ftc {T : ℝ} {g h : ℝ → Pl → ℝ} (hT : 0 < T) (hg : SpSmooth T g) (hh : SpSmooth T h)
    (hgh : HasTimeDeriv T g h) {s : ℝ} (hs : s ∈ Icc 0 T) (j : Fin 2) (x : Pl) :
    B0579.pd j (g s) x = B0579.pd j (g 0) x + ∫ r in (0 : ℝ)..s, B0579.pd j (h r) x := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have h1 := hasDerivAt_line ((hg.slice s hs).differentiable (by simp)) j x 0
  have h2 := hasDerivAt_line ((hg.slice 0 h0).differentiable (by simp)) j x 0
  have h3 := hasDerivAt_line_integral hh hs j x
  have e : (fun e : ℝ => g s (x + e • B0579.dir j)) =
      fun e => g 0 (x + e • B0579.dir j) + ∫ r in (0 : ℝ)..s, h r (x + e • B0579.dir j) := by
    funext e
    exact time_ftc hh hgh hs _
  rw [e] at h1
  have h4 := h1.unique (h2.fun_add h3)
  have e0 : x + (0 : ℝ) • B0579.dir j = x := by simp
  simpa only [e0] using h4

/-- **Part (a)** proved. -/
theorem timeSpaceCommute : TimeSpaceCommute := by
  intro T g h hT hg hh hgh j s hs x
  have hφ : ContinuousOn (fun r => B0579.pd j (h r) x) (Icc 0 T) :=
    contOn_time (F := fun r => B0579.pd j (h r)) (hh.cont [j]) x
  have : Fact (s ∈ Icc 0 T) := ⟨hs⟩
  have hint : IntervalIntegrable (fun r => B0579.pd j (h r) x) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact hφ.mono (Icc_subset_Icc_right hs.2)
  have hD : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, B0579.pd j (h r) x)
      (B0579.pd j (h s) x) (Icc 0 T) s :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hφ.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hφ s hs)
  exact (hD.const_add (B0579.pd j (g 0) x)).congr (fun r hr => pd_ftc hT hg hh hgh hr j x)
    (pd_ftc hT hg hh hgh hs j x)

end UnforcedLeray.Short.IIb.BwdRoute.Joint
