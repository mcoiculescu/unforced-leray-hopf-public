import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.Laplace

/-!
# Part II-a, task `PartII-a:F09/1/3/1/2`: phase-shift Taylor bound on the slices of a phase test

Source `the November 2 reference manuscript` lines 1403-1413 (`T(s)Φ(τ,y) = S(s)Φ(τ-s,·)`).
Proves `sliceShiftTaylor` for a phase test `Ψ`: the L^p norm of the first-order Taylor remainder of
`τ ↦ Ψ(τ, ·)` at a phase `t` is `O(s²)`, and the first difference is `O(s)`.

Strategy: a one-dimensional Taylor estimate, applied pointwise in `y` to `τ ↦ Ψ(τ, y)` with the
uniform bounds `‖∂_τΨ‖, ‖∂_τ²Ψ‖ ≤ M`; the remainder vanishes for `‖y‖` beyond the support radius, so
its L^p norm is at most `sup · vol(ball)^{1/p}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

namespace SliceShift

/-- A function with derivative bounded by `C` on `[a, x]` is `C`-Lipschitz there. -/
theorem lipschitz_of_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ x, HasDerivAt f (f' x) x) {C : ℝ} (hC : ∀ x, ‖f' x‖ ≤ C)
    (a x : ℝ) (hx : a ≤ x) : ‖f x - f a‖ ≤ C * (x - a) := by
  have hcont : ContinuousOn f (Icc a x) := fun y _ => (hf y).continuousAt.continuousWithinAt
  have hd : ∀ y ∈ Ico a x, HasDerivWithinAt f (f' y) (Ici y) y :=
    fun y _ => (hf y).hasDerivWithinAt
  exact norm_image_sub_le_of_norm_deriv_right_le_segment hcont hd (fun y _ => hC y) x ⟨hx, le_rfl⟩

/-- One-dimensional Taylor bound with uniform bounds on the first and second derivatives. -/
theorem taylor1d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' g'' : ℝ → E} {M : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hM2 : ∀ x, ‖g'' x‖ ≤ M) (hM1 : ∀ x, ‖g' x‖ ≤ M)
    (t s : ℝ) (hs : 0 ≤ s) :
    ‖g (t - s) - g t + s • g' t‖ ≤ M * s ^ 2 / 2 ∧ ‖g (t - s) - g t‖ ≤ M * s := by
  constructor
  · -- `F x = g (t - x) - g t + x • g' t` on `[0, s]`, with `F 0 = 0` and `‖F' x‖ ≤ M x`.
    set F : ℝ → E := fun x => g (t - x) - g t + x • g' t with hFdef
    set F' : ℝ → E := fun x => (-1 : ℝ) • g' (t - x) + (1 : ℝ) • g' t with hF'def
    have hF : ∀ x, HasDerivAt F (F' x) x := by
      intro x
      have h1 : HasDerivAt (fun x => g (t - x)) ((-1 : ℝ) • g' (t - x)) x := by
        exact (hg (t - x)).scomp x ((hasDerivAt_id' x).const_sub t)
      have h2 : HasDerivAt (fun x : ℝ => x • g' t) ((1 : ℝ) • g' t) x :=
        (hasDerivAt_id' x).smul_const (g' t)
      exact (h1.sub_const (g t)).add h2
    have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => M * (x * x) / 2) (M * x) x := by
      intro x
      exact (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).const_mul M |>.div_const 2).congr_deriv
        (by ring)
    have hbound : ∀ x ∈ Ico (0 : ℝ) s, ‖F' x‖ ≤ M * x := by
      intro x hx
      have hx0 : t - x ≤ t := by linarith [hx.1]
      have h := lipschitz_of_deriv hg' hM2 (t - x) t hx0
      have e : t - (t - x) = x := by ring
      rw [e] at h
      have e2 : F' x = g' t - g' (t - x) := by
        simp only [hF'def]
        module
      rw [e2]
      exact h
    have hFc : ContinuousOn F (Icc 0 s) := fun y _ => (hF y).continuousAt.continuousWithinAt
    have hFd : ∀ x ∈ Ico (0 : ℝ) s, HasDerivWithinAt F (F' x) (Ici x) x :=
      fun x _ => (hF x).hasDerivWithinAt
    have ha : ‖F 0‖ ≤ M * ((0 : ℝ) * 0) / 2 := by
      simp [hFdef]
    have key : ‖F s‖ ≤ M * (s * s) / 2 :=
      image_norm_le_of_norm_deriv_right_le_deriv_boundary hFc hFd ha hB hbound
        (⟨hs, le_rfl⟩ : s ∈ Icc (0 : ℝ) s)
    have e : M * (s * s) / 2 = M * s ^ 2 / 2 := by ring
    rw [e] at key
    exact key
  · have h := lipschitz_of_deriv hg hM1 (t - s) t (by linarith)
    have e : t - (t - s) = s := by ring
    rw [e, norm_sub_rev] at h
    exact h

/-- The derivative in the phase variable of a phase test, at fixed space point. -/
theorem hasDerivAt_phase {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ℝ} {Φ : ℝ × Space → F} (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    HasDerivAt (fun u : ℝ => Φ (u, y)) (PhaseSpace.dτ Φ (τ, y)) τ := by
  have hd : DifferentiableAt ℝ Φ (τ, y) :=
    (hΦ.smooth.differentiable (by simp)).differentiableAt
  have hc : HasDerivAt (fun u : ℝ => (u, y)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ y)
  exact hd.hasFDerivAt.comp_hasDerivAt τ hc

/-- An `L^p` bound for an element whose representative is bounded by `c` and supported in a ball. -/
theorem norm_le_of_ae_ball (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (X : Lp CVec3 p (volume : Measure Space)) (f : Space → CVec3)
    (hX : ⇑X =ᵐ[volume] f) (R c : ℝ) (hc : 0 ≤ c)
    (hbd : ∀ y, ‖f y‖ ≤ c) (hsupp : ∀ y, R < ‖y‖ → f y = 0) :
    ‖X‖ ≤ c * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (p.toReal)⁻¹ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hS : MeasurableSet (Metric.closedBall (0 : Space) R) := measurableSet_closedBall
  have hle : ∀ y, ‖f y‖ ≤ (Metric.closedBall (0 : Space) R).indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      exact hbd y
    · rw [Set.indicator_of_notMem hy, hsupp y ?_, norm_zero]
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      exact not_le.mp hy
  have h1 : eLpNorm X p volume ≤
      eLpNorm ((Metric.closedBall (0 : Space) R).indicator (fun _ => c)) p volume := by
    rw [eLpNorm_congr_ae hX]
    exact eLpNorm_mono_real hle
  rw [eLpNorm_indicator_const hS hp0 hp, Real.enorm_of_nonneg hc] at h1
  have hVtop : volume (Metric.closedBall (0 : Space) R) ≠ ⊤ := measure_closedBall_lt_top.ne
  have h2 : ENNReal.ofReal c * volume (Metric.closedBall (0 : Space) R) ^ (1 / p.toReal) =
      ENNReal.ofReal (c * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (p.toReal)⁻¹) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hVtop]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ← ENNReal.ofReal_mul hc, one_div]
  have h3 : eLpNorm X p volume ≤
      ENNReal.ofReal (c * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (p.toReal)⁻¹) :=
    h2 ▸ h1
  rw [Lp.norm_def]
  calc (eLpNorm X p volume).toReal
      ≤ (ENNReal.ofReal (c * (volume (Metric.closedBall (0 : Space) R)).toReal ^
          (p.toReal)⁻¹)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    _ = c * (volume (Metric.closedBall (0 : Space) R)).toReal ^ (p.toReal)⁻¹ :=
        ENNReal.toReal_ofReal (mul_nonneg hc (Real.rpow_nonneg ENNReal.toReal_nonneg _))

end SliceShift

open SliceShift in
/-- **Phase-shift Taylor bound on the slices of a phase test** (task `PartII-a:F09/1/3/1/2`). -/
theorem sliceShiftTaylor (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (P : ℝ) [Fact (0 < P)]
    (Ψ : ℝ × Space → CVec3) (hΨ : IsPhaseTest P Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, 0 < s → s ≤ 1 →
      ‖sliceMap (hΨ.isSliceTest p).2 (t - s) - sliceMap (hΨ.isSliceTest p).2 t +
          (s : ℂ) • sliceMap (hΨ.dτ.isSliceTest p).2 t‖ ≤ C * s ^ 2 ∧
      ‖sliceMap (hΨ.isSliceTest p).2 (t - s) - sliceMap (hΨ.isSliceTest p).2 t‖ ≤ C * s := by
  obtain ⟨M₁, hM₁, hb1⟩ := UnforcedLeray.Short.PartIIa.F02.exists_bound_of_phaseTest hΨ.dτ
  obtain ⟨M₂, hM₂, hb2⟩ := UnforcedLeray.Short.PartIIa.F02.exists_bound_of_phaseTest hΨ.dτ.dτ
  obtain ⟨R₀, hR₀⟩ := hΨ.bounded_support
  obtain ⟨R₁, hR₁⟩ := hΨ.dτ.bounded_support
  set M : ℝ := M₁ + M₂ with hMdef
  have hM : 0 ≤ M := add_nonneg hM₁ hM₂
  have hM1le : M₁ ≤ M := by rw [hMdef]; linarith
  have hM2le : M₂ ≤ M := by rw [hMdef]; linarith
  set R : ℝ := max R₀ R₁ with hRdef
  set V : ℝ := (volume (Metric.closedBall (0 : Space) R)).toReal ^ (p.toReal)⁻¹ with hVdef
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  refine ⟨M * V, mul_nonneg hM hV, fun t s hs0 hs1 => ?_⟩
  -- pointwise Taylor bounds in the phase variable, for each space point
  have hpt : ∀ y : Space,
      ‖Ψ (t - s, y) - Ψ (t, y) + (s : ℂ) • PhaseSpace.dτ Ψ (t, y)‖ ≤ M * s ^ 2 / 2 ∧
      ‖Ψ (t - s, y) - Ψ (t, y)‖ ≤ M * s := by
    intro y
    have h := taylor1d (g := fun u : ℝ => Ψ (u, y))
      (g' := fun u : ℝ => PhaseSpace.dτ Ψ (u, y))
      (g'' := fun u : ℝ => PhaseSpace.dτ (PhaseSpace.dτ Ψ) (u, y))
      (fun x => hasDerivAt_phase hΨ x y) (fun x => hasDerivAt_phase hΨ.dτ x y)
      (fun x => (hb2 (x, y)).trans hM2le)
      (fun x => (hb1 (x, y)).trans hM1le) t s hs0.le
    refine ⟨?_, h.2⟩
    have e : (s : ℂ) • PhaseSpace.dτ Ψ (t, y) = s • PhaseSpace.dτ Ψ (t, y) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    rw [e]
    exact h.1
  have hR₀' : ∀ τ : ℝ, ∀ y : Space, R < ‖y‖ → Ψ (τ, y) = 0 := fun τ y hy =>
    hR₀ τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  have hR₁' : ∀ τ : ℝ, ∀ y : Space, R < ‖y‖ → PhaseSpace.dτ Ψ (τ, y) = 0 := fun τ y hy =>
    hR₁ τ y (lt_of_le_of_lt (le_max_right _ _) hy)
  -- the two `Lp` elements, as functions on space
  have hcoe : ∀ τ : ℝ, ⇑(sliceMap (hΨ.isSliceTest p).2 τ) =ᵐ[volume] fun y => Ψ (τ, y) :=
    fun τ => MemLp.coeFn_toLp _
  have hcoe' : ∀ τ : ℝ, ⇑(sliceMap (hΨ.dτ.isSliceTest p).2 τ) =ᵐ[volume]
      fun y => PhaseSpace.dτ Ψ (τ, y) :=
    fun τ => MemLp.coeFn_toLp _
  have hX : ⇑(sliceMap (hΨ.isSliceTest p).2 (t - s) - sliceMap (hΨ.isSliceTest p).2 t +
      (s : ℂ) • sliceMap (hΨ.dτ.isSliceTest p).2 t) =ᵐ[volume]
      fun y => Ψ (t - s, y) - Ψ (t, y) + (s : ℂ) • PhaseSpace.dτ Ψ (t, y) := by
    filter_upwards [Lp.coeFn_add (sliceMap (hΨ.isSliceTest p).2 (t - s) -
        sliceMap (hΨ.isSliceTest p).2 t) ((s : ℂ) • sliceMap (hΨ.dτ.isSliceTest p).2 t),
      Lp.coeFn_sub (sliceMap (hΨ.isSliceTest p).2 (t - s)) (sliceMap (hΨ.isSliceTest p).2 t),
      Lp.coeFn_smul (s : ℂ) (sliceMap (hΨ.dτ.isSliceTest p).2 t),
      hcoe (t - s), hcoe t, hcoe' t] with y h1 h2 h3 h4 h5 h6
    simp only [h1, h2, h3, h4, h5, h6, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have hXsub : ⇑(sliceMap (hΨ.isSliceTest p).2 (t - s) - sliceMap (hΨ.isSliceTest p).2 t) =ᵐ[volume]
      fun y => Ψ (t - s, y) - Ψ (t, y) := by
    filter_upwards [Lp.coeFn_sub (sliceMap (hΨ.isSliceTest p).2 (t - s))
        (sliceMap (hΨ.isSliceTest p).2 t), hcoe (t - s), hcoe t] with y h1 h2 h3
    simp only [h1, h2, h3, Pi.sub_apply]
  have hbd1 : ∀ y : Space, ‖Ψ (t - s, y) - Ψ (t, y) + (s : ℂ) • PhaseSpace.dτ Ψ (t, y)‖ ≤
      M * s ^ 2 / 2 := fun y => (hpt y).1
  have hbd2 : ∀ y : Space, ‖Ψ (t - s, y) - Ψ (t, y)‖ ≤ M * s := fun y => (hpt y).2
  have hsupp1 : ∀ y : Space, R < ‖y‖ →
      Ψ (t - s, y) - Ψ (t, y) + (s : ℂ) • PhaseSpace.dτ Ψ (t, y) = 0 := by
    intro y hy
    simp [hR₀' (t - s) y hy, hR₀' t y hy, hR₁' t y hy]
  have hsupp2 : ∀ y : Space, R < ‖y‖ → Ψ (t - s, y) - Ψ (t, y) = 0 := by
    intro y hy
    simp [hR₀' (t - s) y hy, hR₀' t y hy]
  have hM2s : 0 ≤ M * s ^ 2 / 2 := by positivity
  have hMs : 0 ≤ M * s := by positivity
  refine ⟨?_, ?_⟩
  · have h := norm_le_of_ae_ball p hp _ _ hX R (M * s ^ 2 / 2) hM2s hbd1 hsupp1
    refine h.trans ?_
    rw [← hVdef]
    nlinarith [mul_nonneg (mul_nonneg hM hV) (sq_nonneg s)]
  · have h := norm_le_of_ae_ball p hp _ _ hXsub R (M * s) hMs hbd2 hsupp2
    refine h.trans ?_
    rw [← hVdef]
    nlinarith [mul_nonneg hM hV, hs0]

end UnforcedLeray.Short.PartIIa
