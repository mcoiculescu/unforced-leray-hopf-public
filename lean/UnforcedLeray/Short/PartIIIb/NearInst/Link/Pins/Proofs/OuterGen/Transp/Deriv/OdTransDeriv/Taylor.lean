import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

/-!
Generic helpers for the strong `r`-derivatives of `OD_TransDeriv` and `OD_DilDeriv`:
one-variable Taylor bound, slices of a jointly smooth family, a joint second-order bound on a
compact set, and an `L²` bound by a bounded indicator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst.OdHelp

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem taylor_bound (g g1 g2 : ℝ → E) (hg : ∀ s, HasDerivAt g (g1 s) s)
    (hg1 : ∀ s, HasDerivAt g1 (g2 s) s) (M r : ℝ) (hM : ∀ s ∈ uIcc 0 r, ‖g2 s‖ ≤ M) :
    ‖g r - g 0 - r • g1 0‖ ≤ M * r ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 left_mem_uIcc)
  have key : ∀ s, HasDerivAt (fun y : ℝ => g y - g 0 - y • g1 0) (g1 s - g1 0) s := by
    intro s
    have h1 := ((hg s).sub_const (g 0)).sub ((hasDerivAt_id' s).smul_const (g1 0))
    rw [one_smul] at h1
    exact h1
  have hgrad : ∀ s ∈ uIcc 0 r, ‖g1 s - g1 0‖ ≤ M * |r| := by
    intro s hs
    have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g1) (f' := g2)
      (s := uIcc 0 r) (C := M) (fun x _ => (hg1 x).hasDerivWithinAt) hM (convex_uIcc 0 r)
      left_mem_uIcc hs
    have h2 : ‖s - 0‖ ≤ |r| := by
      rw [sub_zero, Real.norm_eq_abs]
      rcases Set.mem_uIcc.1 hs with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        rw [abs_le] <;> constructor <;> cases abs_cases r <;> linarith [abs_nonneg r]
    calc ‖g1 s - g1 0‖ ≤ M * ‖s - 0‖ := h1
      _ ≤ M * |r| := mul_le_mul_of_nonneg_left h2 hM0
  have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => g y - g 0 - y • g1 0) (f' := fun s => g1 s - g1 0)
    (s := uIcc 0 r) (C := M * |r|) (fun x _ => (key x).hasDerivWithinAt) hgrad
    (convex_uIcc 0 r) right_mem_uIcc left_mem_uIcc
  have e : ‖g r - g 0 - r • g1 0‖ = ‖(fun y : ℝ => g y - g 0 - y • g1 0) r -
      (fun y : ℝ => g y - g 0 - y • g1 0) 0‖ := by
    simp
  rw [e, norm_sub_rev]
  refine h1.trans (le_of_eq ?_)
  rw [zero_sub, norm_neg, Real.norm_eq_abs, ← sq_abs r]
  ring

/-- Slices of a differentiable family `F (t, q)` in the first variable. -/
theorem hasDerivAt_slice {F : ℝ × (ℝ × Space) → E} (hF : Differentiable ℝ F) (s : ℝ)
    (q : ℝ × Space) :
    HasDerivAt (fun t : ℝ => F (t, q)) (fderiv ℝ F (s, q) (1, 0)) s := by
  have hline : HasDerivAt (fun t : ℝ => ((t, q) : ℝ × (ℝ × Space)))
      ((1 : ℝ), (0 : ℝ × Space)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s q)
  exact (hF (s, q)).hasFDerivAt.comp_hasDerivAt s hline

/-- A family vanishing for `|t| ≤ 1` has zero first `t`-derivative at `0`. -/
theorem fderiv_eq_zero_of_zero {G : ℝ × (ℝ × Space) → E} (hG : Differentiable ℝ G)
    (q : ℝ × Space) (h0 : ∀ s ∈ Icc (-1 : ℝ) 1, G (s, q) = 0) :
    fderiv ℝ G (0, q) (1, 0) = 0 := by
  have h1 := hasDerivAt_slice hG 0 q
  have h2 : HasDerivAt (fun t : ℝ => G (t, q)) (0 : E) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact h0 s hs
  exact h1.unique h2

/-- **Joint second-order bound.** For a `C²` family `G (t, q)` and a compact set `K` of
parameters `q`, the first `t`-derivative at `0` gives a uniform `O(t²)` remainder for `|t| ≤ 1`. -/
theorem joint_taylor {G : ℝ × (ℝ × Space) → E} (hG : ContDiff ℝ 2 G)
    (K : Set (ℝ × Space)) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, |r| ≤ 1 → ∀ q ∈ K,
      ‖G (r, q) - G (0, q) - r • fderiv ℝ G (0, q) (1, 0)‖ ≤ M * r ^ 2 := by
  have hD1 : ContDiff ℝ 1 (fun p : ℝ × (ℝ × Space) => fderiv ℝ G p (1, 0)) :=
    (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hD2c : Continuous (fun p : ℝ × (ℝ × Space) => fderiv ℝ (fun p' => fderiv ℝ G p' (1, 0)) p (1, 0)) :=
    (hD1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hT : IsCompact (Icc (-1 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hD2c.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun r hr q hq => ?_⟩
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hD1d : Differentiable ℝ (fun p : ℝ × (ℝ × Space) => fderiv ℝ G p (1, 0)) :=
    hD1.differentiable (by norm_num)
  have hr' : r ∈ Icc (-1 : ℝ) 1 := abs_le.1 hr
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine taylor_bound (fun t => G (t, q)) (fun t => fderiv ℝ G (t, q) (1, 0))
    (fun t => fderiv ℝ (fun p' => fderiv ℝ G p' (1, 0)) (t, q) (1, 0)) ?_ ?_ (max C 0) r ?_
  · intro s
    exact hasDerivAt_slice hGd s q
  · intro s
    exact hasDerivAt_slice hD1d s q
  · intro s hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0 hr' hs
    exact le_trans (hC (s, q) (mk_mem_prod hs' hq)) (le_max_left _ _)

end Taylor

section L2

/-- An `L²` element whose norm is pointwise bounded by a constant on a set of finite measure
has norm bounded by a fixed multiple of the constant. -/
theorem l2_indicator_bound {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (S : Set α) (hS : MeasurableSet S) (hfin : μ S < ⊤) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : Lp E 2 μ) (K : ℝ), 0 ≤ K →
      (∀ᵐ z ∂μ, ‖(f : α → E) z‖ ≤ S.indicator (fun _ => K) z) → ‖f‖ ≤ A * K := by
  refine ⟨(μ S ^ (1 / 2 : ℝ)).toReal, ENNReal.toReal_nonneg, fun f K hK h => ?_⟩
  rw [Lp.norm_def]
  have hmono := eLpNorm_mono_ae_real (p := 2) h
  have hind := eLpNorm_indicator_const (μ := μ) (c := K) hS (p := 2) (by norm_num) (by norm_num)
  have hne : ‖K‖ₑ * μ S ^ (1 / (2 : ENNReal).toReal) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin.ne
  calc (eLpNorm (f : α → E) 2 μ).toReal
      ≤ (eLpNorm (S.indicator (fun _ => K)) 2 μ).toReal := ENNReal.toReal_mono (by rw [hind]; exact hne) hmono
    _ = ‖K‖ * (μ S ^ (1 / 2 : ℝ)).toReal := by
        rw [hind, ENNReal.toReal_mul]
        simp
    _ = (μ S ^ (1 / 2 : ℝ)).toReal * K := by
        rw [Real.norm_eq_abs, abs_of_nonneg hK]
        ring

end L2

/-- The `t`-line through `(τ, x)` in the first (phase) variable. -/
theorem hasDerivAt_tauLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × Space → E} (hΦ : Differentiable ℝ Φ) (τ : ℝ) (x : Space) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Φ (τ + t, x)) (UnforcedLeray.PhaseSpace.dτ Φ (τ + s, x)) s := by
  have hline : HasDerivAt (fun t : ℝ => ((τ + t, x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    ((hasDerivAt_id' s).const_add τ).prodMk (hasDerivAt_const s x)
  exact (hΦ (τ + s, x)).hasFDerivAt.comp_hasDerivAt s hline

/-- A periodic function takes equal values at phases with equal images in the circle. -/
theorem periodic_lift_coe {E : Type*} [NormedAddCommGroup E] {P : ℝ} {f : ℝ → E}
    (hf : Function.Periodic f P) {a b : ℝ} (h : (a : AddCircle P) = (b : AddCircle P)) :
    f a = f b := by
  have h0 : ((b - a : ℝ) : AddCircle P) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).1 h0
  rw [zsmul_eq_mul] at hn
  have hb : b = a + (n : ℝ) * P := by linarith
  rw [hb]
  exact ((hf.int_mul n) a).symm


end UnforcedLeray.Short.PartIIIb.NearInst.OdHelp
