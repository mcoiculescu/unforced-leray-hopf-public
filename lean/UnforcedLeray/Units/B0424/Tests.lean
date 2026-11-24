import UnforcedLeray.Units.B0424.Calc

/-!
# B0424, part 3: the tests of the time change and of the local Laplacian

Blueprint unit B0424 (`eq:free-stress-13`, `-14`, `-15`), `paper/main.tex` lines 7479–7517.

* **(14) from (13)** (tex 7493–7499): a test `φ(θ, x)` of the heat operator in the variables
  `θ = e^t` becomes the test `Ξ(t, x) = χ(t) φ(e^t, x)` of (13) (`timeTest`), with
  `∂_tΞ = χ'φ(e^t, ·) + χ e^t (∂_θφ)(e^t, ·)` and `Δ_xΞ = χ (Δ_xφ)(e^t, ·)`
  (`tD_timeTest`, `sLap_timeTest`).
* **Back to the phase variables** (tex 7510–7512, "the distributional form of (11) supplies its
  derivatives"): a test `ψ(τ, y)` supported in the window `|τ - τ₀| < 1` becomes the test
  `φ(θ, x) = θ⁻¹ ψ(τ₀ + log θ, θ^{-1/2} x)` of the `(θ, x)` variables, extended by zero to
  `θ ≤ 0` (`lapTest`); it is smooth with compact support (`isSTTest_lapTest`) and
  `Δ_xφ(θ, x) = θ⁻¹ (θ^{-1/2})² (Δψ)(τ₀ + log θ, θ^{-1/2} x)` (`sLap_lapTest`).

Status: infrastructure for `Units/B0424.lean`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0424

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Parabolic

/-! ### Bounds for compactly supported functions -/

theorem exists_bound_real {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, M < |t| → χ t = 0 := by
  obtain ⟨M, hM⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := hM h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left M 0]

theorem exists_bound_space {φ : ℝ × Space → ℝ} (hφc : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t y, R < ‖y‖ → φ (t, y) = 0 := by
  obtain ⟨R, hR0, -, hR⟩ := B0005.exists_window_of_hasCompactSupport hφc
  exact ⟨R, hR0, hR⟩

/-! ### The test of the time change -/

/-- `Ξ(t, x) = χ(t) φ(e^t, x)` (tex 7493–7499). -/
def timeTest (χ : ℝ → ℝ) (φ : ℝ × Space → ℝ) : ℝ × Space → ℝ :=
  cmb χ Real.exp (fun _ => (1 : ℝ)) φ

theorem timeTest_apply (χ : ℝ → ℝ) (φ : ℝ × Space → ℝ) (p : ℝ × Space) :
    timeTest χ φ p = χ p.1 * φ (Real.exp p.1, p.2) := by
  simp [timeTest, cmb]

theorem isSTTest_timeTest {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {φ : PS 3 → ℝ} (hφ : IsSTTest φ) : IsSTTest (timeTest χ φ : PS 3 → ℝ) := by
  refine ⟨contDiff_cmb hφ.1 hχ Real.contDiff_exp contDiff_const, ?_⟩
  obtain ⟨M, hM0, hM⟩ := exists_bound_real hχc
  obtain ⟨R, -, hR⟩ := exists_bound_space hφ.2
  refine HasCompactSupport.intro (K := Icc (-M) M ×ˢ Metric.closedBall (0 : Space) R)
    (isCompact_Icc.prod (isCompact_closedBall _ _)) fun p hp => ?_
  rw [timeTest_apply]
  simp only [mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le]
    at hp
  rcases hp with h | h
  · have : M < |p.1| := by
      rcases h with h' | h'
      · rw [abs_of_neg (by linarith : p.1 < 0)]; linarith
      · exact h'.trans_le (le_abs_self _)
    rw [hM _ this, zero_mul]
  · rw [hR _ _ h, mul_zero]

theorem tD_timeTest {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {φ : PS 3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : ℝ × Space) :
    tD (timeTest χ φ : PS 3 → ℝ) p =
      deriv χ p.1 * φ (Real.exp p.1, p.2) +
        χ p.1 * (Real.exp p.1 * tD φ (Real.exp p.1, p.2)) := by
  have h1c : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have hd := ((contDiff_cmb hφ hχ Real.contDiff_exp h1c).differentiable (by simp)) p
  have hφd := (hφ.differentiable (by simp)) (Real.exp p.1, (fun _ => (1 : ℝ)) p.1 • p.2)
  show fderiv ℝ (cmb χ Real.exp (fun _ => (1 : ℝ)) φ) p ((1 : ℝ), (0 : Space)) = _
  rw [fderiv_cmb_time hd hφd ((hχ.differentiable (by simp)) p.1).hasDerivAt
    (Real.hasDerivAt_exp p.1) (hasDerivAt_const p.1 (1 : ℝ))]
  simp only [one_smul, zero_smul]
  rw [show ((Real.exp p.1, (0 : Space)) : ℝ × Space) = Real.exp p.1 • ((1 : ℝ), (0 : Space)) by
    simp, map_smul, smul_eq_mul]
  rfl

theorem sLap_timeTest {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {φ : PS 3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : ℝ × Space) :
    sLap (timeTest χ φ : PS 3 → ℝ) p = χ p.1 * sLap φ (Real.exp p.1, p.2) := by
  have h1c : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  rw [timeTest, sLap_cmb hφ hχ Real.contDiff_exp h1c]
  simp

/-! ### The test of the local Laplacian -/

/-- A compactly supported `ψ` with `tsupport ψ ⊆ (τ₀ - 1, τ₀ + 1) × ℝ³` vanishes at a positive
distance from the window's ends. -/
theorem window_margin {ψ : ℝ × Space → ℝ} (hψc : HasCompactSupport ψ) {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ y, ψ (τ, y) ≠ 0 → τ₀ - 1 + δ < τ ∧ τ < τ₀ + 1 - δ := by
  have hK : IsCompact (Prod.fst '' tsupport ψ) := hψc.isCompact.image continuous_fst
  have hKs : Prod.fst '' tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) := by
    rintro _ ⟨p, hp, rfl⟩; exact (hψw hp).1
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open isOpen_Ioo hKs
  refine ⟨δ, hδ, fun τ y hne => ?_⟩
  have hmem : τ ∈ Prod.fst '' tsupport ψ := ⟨(τ, y), subset_tsupport _ hne, rfl⟩
  have h1 : τ - δ ∈ Metric.cthickening δ (Prod.fst '' tsupport ψ) :=
    Metric.mem_cthickening_of_dist_le _ _ _ _ hmem (by rw [Real.dist_eq]; simp [abs_of_pos hδ])
  have h2 : τ + δ ∈ Metric.cthickening δ (Prod.fst '' tsupport ψ) :=
    Metric.mem_cthickening_of_dist_le _ _ _ _ hmem (by rw [Real.dist_eq]; simp [abs_of_pos hδ])
  have h1' := (hsub h1).1
  have h2' := (hsub h2).2
  constructor <;> linarith

/-- `φ(θ, x) = θ⁻¹ ψ(τ₀ + log θ, θ^{-1/2} x)` for `θ > 0`, extended by zero (tex 7510–7512),
written with `θ⁻¹ = e^{-log θ}` and `θ^{-1/2} = e^{-log θ / 2}`. -/
def lapTest (τ₀ : ℝ) (ψ : ℝ × Space → ℝ) (X : ℝ × Space) : ℝ :=
  if 0 < X.1 then
    Real.exp (-Real.log X.1) * ψ (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2)
  else 0

/-- The smooth expression of `lapTest` on `θ > 0`. -/
def lapCmb (τ₀ : ℝ) (ψ : ℝ × Space → ℝ) : ℝ × Space → ℝ :=
  cmb (fun θ => Real.exp (-Real.log θ)) (fun θ => τ₀ + Real.log θ)
    (fun θ => Real.exp (-Real.log θ / 2)) ψ

theorem lapTest_eq_lapCmb {τ₀ : ℝ} {ψ : ℝ × Space → ℝ} {X : ℝ × Space} (hX : 0 < X.1) :
    lapTest τ₀ ψ =ᶠ[𝓝 X] lapCmb τ₀ ψ := by
  have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [hopen.mem_nhds hX] with p hp
  simp only [lapTest, lapCmb, cmb, if_pos (show 0 < p.1 from hp)]

theorem lapTest_eq_zero {τ₀ : ℝ} {ψ : ℝ × Space → ℝ} {δ : ℝ}
    (hδ : ∀ τ y, ψ (τ, y) ≠ 0 → τ₀ - 1 + δ < τ ∧ τ < τ₀ + 1 - δ) {X : ℝ × Space}
    (hX : X.1 < Real.exp (-1 + δ)) : lapTest τ₀ ψ X = 0 := by
  unfold lapTest
  split_ifs with h
  · by_contra hne
    have hne' := right_ne_zero_of_mul hne
    have := (hδ _ _ hne').1
    have hlog : Real.log X.1 < -1 + δ := by
      rw [Real.log_lt_iff_lt_exp h]; exact hX
    linarith
  · rfl

theorem lapTest_eventually_zero {τ₀ : ℝ} {ψ : ℝ × Space → ℝ} {δ : ℝ}
    (hδ : ∀ τ y, ψ (τ, y) ≠ 0 → τ₀ - 1 + δ < τ ∧ τ < τ₀ + 1 - δ) {X : ℝ × Space}
    (hX : X.1 ≤ 0) : lapTest τ₀ ψ =ᶠ[𝓝 X] fun _ => 0 := by
  have hopen : IsOpen {p : ℝ × Space | p.1 < Real.exp (-1 + δ)} :=
    isOpen_lt continuous_fst continuous_const
  filter_upwards [hopen.mem_nhds (show X.1 < Real.exp (-1 + δ) from
    hX.trans_lt (Real.exp_pos _))] with p hp
  exact lapTest_eq_zero hδ hp

theorem contDiffAt_lapCmb {τ₀ : ℝ} {ψ : ℝ × Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) {X : ℝ × Space}
    (hX : 0 < X.1) : ContDiffAt ℝ ∞ (lapCmb τ₀ ψ) X := by
  have hlog : ContDiffAt ℝ ∞ (fun p : ℝ × Space => Real.log p.1) X :=
    (Real.contDiffAt_log.2 hX.ne').comp X contDiffAt_fst
  unfold lapCmb cmb
  refine (Real.contDiff_exp.contDiffAt.comp X hlog.neg).mul (hψ.contDiffAt.comp X ?_)
  exact (contDiffAt_const.add hlog).prodMk
    ((Real.contDiff_exp.contDiffAt.comp X (hlog.neg.div_const 2)).smul contDiffAt_snd)

theorem isSTTest_lapTest {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ) {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    IsSTTest (lapTest τ₀ ψ : PS 3 → ℝ) := by
  obtain ⟨δ, hδ0, hδ⟩ := window_margin hψ.2 hψw
  obtain ⟨R, hR0, hR⟩ := exists_bound_space hψ.2
  constructor
  · refine contDiff_iff_contDiffAt.2 fun X => ?_
    rcases lt_or_ge 0 X.1 with hX | hX
    · exact (contDiffAt_lapCmb hψ.1 hX).congr_of_eventuallyEq (lapTest_eq_lapCmb hX)
    · exact contDiffAt_const.congr_of_eventuallyEq (lapTest_eventually_zero hδ hX)
  · refine HasCompactSupport.intro
      (K := Icc (Real.exp (-1)) (Real.exp 1) ×ˢ Metric.closedBall (0 : Space) (R * Real.exp (1 / 2)))
      (isCompact_Icc.prod (isCompact_closedBall _ _)) fun X hX => ?_
    unfold lapTest
    split_ifs with h0
    · by_contra hne
      have hne' := right_ne_zero_of_mul hne
      obtain ⟨h1, h2⟩ := hδ _ _ hne'
      have hl1 : -1 < Real.log X.1 := by linarith
      have hl2 : Real.log X.1 < 1 := by linarith
      have hθ1 : Real.exp (-1) < X.1 := by
        have := Real.exp_lt_exp.2 hl1; rwa [Real.exp_log h0] at this
      have hθ2 : X.1 < Real.exp 1 := by
        have := Real.exp_lt_exp.2 hl2; rwa [Real.exp_log h0] at this
      have hx : R * Real.exp (1 / 2) < ‖X.2‖ := by
        simp only [mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right, not_and_or,
          not_le] at hX
        rcases hX with h | h
        · exfalso; rcases h with h' | h' <;> linarith
        · exact h
      apply hne
      rw [hR _ _ ?_, mul_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(1 / 2)) ≤ Real.exp (-Real.log X.1 / 2) :=
        Real.exp_le_exp.2 (by linarith)
      have hRe : R = Real.exp (-(1 / 2)) * (R * Real.exp (1 / 2)) := by
        rw [mul_left_comm, ← Real.exp_add]; simp
      calc R = Real.exp (-(1 / 2)) * (R * Real.exp (1 / 2)) := hRe
        _ < Real.exp (-(1 / 2)) * ‖X.2‖ := mul_lt_mul_of_pos_left hx (Real.exp_pos _)
        _ ≤ Real.exp (-Real.log X.1 / 2) * ‖X.2‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    · rfl

/-- `Δ_xφ(θ, x) = θ⁻¹ (θ^{-1/2})² Δψ(τ₀ + log θ, θ^{-1/2} x)` for `θ > 0`, and `0` for
`θ ≤ 0`. -/
theorem sLap_lapTest {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ) {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (X : ℝ × Space) :
    sLap (lapTest τ₀ ψ : PS 3 → ℝ) X =
      if 0 < X.1 then
        Real.exp (-Real.log X.1) * Real.exp (-Real.log X.1 / 2) ^ 2 *
          sLap ψ (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2)
      else 0 := by
  obtain ⟨δ, -, hδ⟩ := window_margin hψ.2 hψw
  split_ifs with hX
  · -- on `θ > 0`, `φ` agrees near `X` with the smooth expression `lapCmb`
    set c : ℝ → ℝ := fun θ => Real.exp (-Real.log θ)
    set m : ℝ → ℝ := fun θ => τ₀ + Real.log θ
    set b : ℝ → ℝ := fun θ => Real.exp (-Real.log θ / 2)
    have hopen : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
    have hcd : ∀ p : ℝ × Space, 0 < p.1 → DifferentiableAt ℝ (lapCmb τ₀ ψ) p := fun p hp =>
      (contDiffAt_lapCmb hψ.1 hp).differentiableAt (by simp)
    have hψd : ∀ Y, DifferentiableAt ℝ ψ Y := fun Y => (hψ.1.differentiable (by simp)) Y
    have hsDψ : ∀ j : Fin 3, ContDiff ℝ ∞ (sD j ψ) := fun j => contDiff_sD hψ.1 j
    -- first derivative near `X`
    have h1 : ∀ j : Fin 3, sD j (lapTest τ₀ ψ : PS 3 → ℝ) =ᶠ[𝓝 X]
        cmb (fun θ => c θ * b θ) m b (sD j ψ) := by
      intro j
      have hev := (lapTest_eq_lapCmb (τ₀ := τ₀) (ψ := ψ) hX).fderiv (𝕜 := ℝ)
      filter_upwards [hev, hopen.mem_nhds hX] with p hp hp0
      show fderiv ℝ (lapTest τ₀ ψ) p ((0 : ℝ), coordinateVector j) = _
      rw [hp]
      have := fderiv_cmb_space (c := c) (m := m) (b := b) (Ψ := ψ) (hcd p hp0) (hψd _)
        (coordinateVector j)
      rw [lapCmb, this]
      simp only [cmb]
      rw [← mul_assoc]
      rfl
    have hcb : ∀ j : Fin 3, DifferentiableAt ℝ (cmb (fun θ => c θ * b θ) m b (sD j ψ)) X := by
      intro j
      have hlog : ContDiffAt ℝ ∞ (fun p : ℝ × Space => Real.log p.1) X :=
        (Real.contDiffAt_log.2 hX.ne').comp X contDiffAt_fst
      have hca : ContDiffAt ℝ ∞ (cmb (fun θ => c θ * b θ) m b (sD j ψ)) X := by
        unfold cmb
        refine ((Real.contDiff_exp.contDiffAt.comp X hlog.neg).mul
          (Real.contDiff_exp.contDiffAt.comp X (hlog.neg.div_const 2))).mul
          ((hsDψ j).contDiffAt.comp X ?_)
        exact (contDiffAt_const.add hlog).prodMk
          ((Real.contDiff_exp.contDiffAt.comp X (hlog.neg.div_const 2)).smul contDiffAt_snd)
      exact hca.differentiableAt (by simp)
    simp only [sLap]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show fderiv ℝ (sD j (lapTest τ₀ ψ : PS 3 → ℝ)) X ((0 : ℝ), coordinateVector j) = _
    rw [(h1 j).fderiv_eq, fderiv_cmb_space (hcb j) (((hsDψ j).differentiable (by simp)) _)]
    simp only [c, b, m]
    rw [show sD2 j j ψ (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2) =
      fderiv ℝ (sD j ψ) (τ₀ + Real.log X.1, Real.exp (-Real.log X.1 / 2) • X.2)
        ((0 : ℝ), coordinateVector j) from rfl]
    ring
  · have hz := lapTest_eventually_zero (τ₀ := τ₀) (ψ := ψ) hδ (not_lt.1 hX)
    simp only [sLap]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : sD j (lapTest τ₀ ψ : PS 3 → ℝ) =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
      filter_upwards [hz.fderiv (𝕜 := ℝ)] with p hp
      show fderiv ℝ (lapTest τ₀ ψ) p ((0 : ℝ), coordinateVector j) = 0
      rw [hp]; simp
    show fderiv ℝ (sD j (lapTest τ₀ ψ : PS 3 → ℝ)) X ((0 : ℝ), coordinateVector j) = 0
    rw [h1.fderiv_eq]; simp

end UnforcedLeray.B0424
