import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_7.Commute

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.  A tower `D` of
successive time derivatives inside `SpSmooth` has `D 0` jointly `C^∞` on `[0, T] × ℝ²` for `T > 0`:
the time partial is continuous and the slice is differentiable, so the mean value theorem gives the
full derivative at each point of the closed domain; its components `D 1`, `∂_q D 0`, `∂_η D 0` are
again heads of towers (`Tower.shift`, and `Tower.pd` through part (a)), and induction on the order
with `contDiffOn_succ_iff_fderivWithin` closes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.BwdRoute.Joint

open CylPDE

/-- **Part (c)**: the head of a tower is jointly smooth. -/
def MixedSmooth : Prop :=
  ∀ (T : ℝ) (D : ℕ → ℝ → Pl → ℝ), 0 < T → Tower T D →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => D 0 z.1 z.2) (Icc 0 T ×ˢ univ)

/-- A continuous time derivative and a differentiable slice give the full derivative within the
closed domain, by the mean value theorem in time. -/
theorem hasFDerivWithinAt_of_partials {T : ℝ} {F Ft : ℝ → Pl → ℝ} (hFt : HasTimeDeriv T F Ft)
    (hc : ContinuousOn (fun z : ℝ × Pl => Ft z.1 z.2) (Icc 0 T ×ˢ univ))
    {s0 : ℝ} (hs0 : s0 ∈ Icc 0 T) {x0 : Pl} {L : Pl →L[ℝ] ℝ} (hL : HasFDerivAt (F s0) L x0) :
    HasFDerivWithinAt (fun z : ℝ × Pl => F z.1 z.2)
      (Ft s0 x0 • ContinuousLinearMap.fst ℝ ℝ Pl + L.comp (ContinuousLinearMap.snd ℝ ℝ Pl))
      (Icc 0 T ×ˢ univ) (s0, x0) := by
  have h2 : HasFDerivWithinAt (fun z : ℝ × Pl => F s0 z.2)
      (L.comp (ContinuousLinearMap.snd ℝ ℝ Pl)) (Icc 0 T ×ˢ univ) (s0, x0) :=
    (HasFDerivAt.comp (s0, x0) hL hasFDerivAt_snd).hasFDerivWithinAt
  have h1 : HasFDerivWithinAt (fun z : ℝ × Pl => F z.1 z.2 - F s0 z.2)
      (Ft s0 x0 • ContinuousLinearMap.fst ℝ ℝ Pl) (Icc 0 T ×ˢ univ) (s0, x0) := by
    rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    have hcw := hc (s0, x0) ⟨hs0, mem_univ _⟩
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδ, hcw⟩ := hcw ε hε
    have hmem : ∀ᶠ z : ℝ × Pl in 𝓝[Icc 0 T ×ˢ univ] (s0, x0),
        z ∈ Icc 0 T ×ˢ (univ : Set Pl) ∧ dist z (s0, x0) < δ :=
      eventually_mem_nhdsWithin.and (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hδ))
    filter_upwards [hmem] with z hz
    obtain ⟨⟨hz1, -⟩, hzd⟩ := hz
    have hsubI : uIcc s0 z.1 ⊆ Icc 0 T := Set.uIcc_subset_Icc hs0 hz1
    have hφ : ∀ r ∈ uIcc s0 z.1, HasDerivWithinAt (fun r => F r z.2 - Ft s0 x0 * r)
        (Ft r z.2 - Ft s0 x0) (uIcc s0 z.1) r := by
      intro r hr
      have h3 := ((hFt r (hsubI hr) z.2).mono hsubI).fun_sub
        ((hasDerivWithinAt_id r (uIcc s0 z.1)).const_mul (Ft s0 x0))
      simpa using h3
    have hbound : ∀ r ∈ uIcc s0 z.1, ‖Ft r z.2 - Ft s0 x0‖ ≤ ε := by
      intro r hr
      have hr1 : dist r s0 ≤ dist z.1 s0 := by
        rw [Real.dist_eq, Real.dist_eq]
        exact Set.abs_sub_left_of_mem_uIcc hr
      have hzd' : max (dist z.1 s0) (dist z.2 x0) < δ := by
        have := hzd
        rwa [Prod.dist_eq] at this
      have hrdist : dist ((r, z.2) : ℝ × Pl) (s0, x0) < δ := by
        rw [Prod.dist_eq]
        exact lt_of_le_of_lt (max_le_max hr1 le_rfl) hzd'
      have h4 := hcw (x := (r, z.2)) ⟨hsubI hr, mem_univ _⟩ hrdist
      rw [Real.dist_eq] at h4
      exact h4.le
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbound (convex_uIcc s0 z.1)
      left_mem_uIcc right_mem_uIcc
    have hnorm : ‖z.1 - s0‖ ≤ ‖z - (s0, x0)‖ := by
      have := norm_fst_le (z - (s0, x0))
      simpa using this
    calc ‖F z.1 z.2 - F s0 z.2 - (F s0 x0 - F s0 x0)
            - (Ft s0 x0 • ContinuousLinearMap.fst ℝ ℝ Pl) (z - (s0, x0))‖
        = ‖F z.1 z.2 - Ft s0 x0 * z.1 - (F s0 z.2 - Ft s0 x0 * s0)‖ := by
          congr 1
          simp only [smul_apply, ContinuousLinearMap.coe_fst', Prod.fst_sub, smul_eq_mul]
          ring
      _ ≤ ε * ‖z.1 - s0‖ := hmv
      _ ≤ ε * ‖z - (s0, x0)‖ := mul_le_mul_of_nonneg_left hnorm hε.le
  have h := h1.fun_add h2
  simpa using h

/-- The partials expand the derivative of a slice. -/
theorem fderiv_eq_pd (φ : Pl → ℝ) (x v : Pl) :
    fderiv ℝ φ x v = v.1 * B0579.pd 0 φ x + v.2 * B0579.pd 1 φ x := by
  have hv : v = v.1 • B0579.dir 0 + v.2 • B0579.dir 1 := by
    ext <;> simp [B0579.dir]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul, B0579.pd]

/-- The candidate full derivative. -/
def jointD (F Ft : ℝ → Pl → ℝ) : ℝ × Pl → (ℝ × Pl →L[ℝ] ℝ) := fun z =>
  Ft z.1 z.2 • ContinuousLinearMap.fst ℝ ℝ Pl +
    B0579.pd 0 (F z.1) z.2 •
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Pl)) +
    B0579.pd 1 (F z.1) z.2 •
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Pl))

theorem hasFDerivWithinAt_jointD {T : ℝ} {F Ft : ℝ → Pl → ℝ} (hF : SpSmooth T F)
    (hFt : SpSmooth T Ft) (hd : HasTimeDeriv T F Ft) {z : ℝ × Pl}
    (hz : z ∈ Icc 0 T ×ˢ (univ : Set Pl)) :
    HasFDerivWithinAt (fun z : ℝ × Pl => F z.1 z.2) (jointD F Ft z) (Icc 0 T ×ˢ univ) z := by
  have hL : HasFDerivAt (F z.1) (fderiv ℝ (F z.1) z.2) z.2 :=
    ((hF.slice z.1 hz.1).differentiable (by simp) z.2).hasFDerivAt
  have h := hasFDerivWithinAt_of_partials hd (hFt.cont []) hz.1 hL
  have e : Ft z.1 z.2 • ContinuousLinearMap.fst ℝ ℝ Pl +
      (fderiv ℝ (F z.1) z.2).comp (ContinuousLinearMap.snd ℝ ℝ Pl) = jointD F Ft z := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [jointD, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', fderiv_eq_pd, smul_eq_mul]
    ring
  rw [← e]
  exact h

theorem Tower.shift {T : ℝ} {D : ℕ → ℝ → Pl → ℝ} (h : Tower T D) :
    Tower T (fun j => D (j + 1)) :=
  ⟨fun _ => h.sp _, fun _ => h.dt _⟩

theorem Tower.pd {T : ℝ} {D : ℕ → ℝ → Pl → ℝ} (hT : 0 < T) (h : Tower T D) (i : Fin 2) :
    Tower T (fun j s => B0579.pd i (D j s)) :=
  ⟨fun j => spSmooth_pd (h.sp j) i,
    fun j => timeSpaceCommute T (D j) (D (j + 1)) hT (h.sp j) (h.sp (j + 1)) (h.dt j) i⟩

/-- The induction on the order. -/
theorem tower_contDiffOn {T : ℝ} (hT : 0 < T) : ∀ (n : ℕ) (D : ℕ → ℝ → Pl → ℝ), Tower T D →
    ContDiffOn ℝ n (fun z : ℝ × Pl => D 0 z.1 z.2) (Icc 0 T ×ˢ univ) := by
  intro n
  induction n with
  | zero =>
    intro D hD
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hD.sp 0).cont []
  | succ n ih =>
    intro D hD
    have hS := uniqueDiffOn_dom hT
    have hderiv : ∀ z ∈ Icc 0 T ×ˢ (univ : Set Pl),
        HasFDerivWithinAt (fun z : ℝ × Pl => D 0 z.1 z.2) (jointD (D 0) (D 1) z)
          (Icc 0 T ×ˢ univ) z :=
      fun z hz => hasFDerivWithinAt_jointD (hD.sp 0) (hD.sp 1) (hD.dt 0) hz
    have hc1 := ih _ hD.shift
    have hc2 := ih _ (hD.pd hT 0)
    have hc3 := ih _ (hD.pd hT 1)
    have hcd : ContDiffOn ℝ n (jointD (D 0) (D 1)) (Icc 0 T ×ˢ univ) :=
      ((hc1.smul contDiffOn_const).add (hc2.smul contDiffOn_const)).add
        (hc3.smul contDiffOn_const)
    have hfw : ContDiffOn ℝ n
        (fderivWithin ℝ (fun z : ℝ × Pl => D 0 z.1 z.2) (Icc 0 T ×ˢ univ)) (Icc 0 T ×ˢ univ) :=
      hcd.congr fun z hz => (hderiv z hz).fderivWithin (hS z hz)
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderivWithin hS]
    exact ⟨fun z hz => (hderiv z hz).differentiableWithinAt, by simp, hfw⟩

/-- **Part (c)** proved. -/
theorem mixedSmooth : MixedSmooth := fun _ D hT hD =>
  contDiffOn_infty.2 fun n => tower_contDiffOn hT n D hD

end UnforcedLeray.Short.IIb.BwdRoute.Joint
