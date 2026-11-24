import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph.Deriv
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.Laplace

/-!


For a phase test `Φ`, `h⁻¹ (e^{hB} Φ - Φ) → testElem (BΦ)` in `Y_2` as `h → 0`: pointwise
`∂_s (dilT s Φ) = dilT s (BΦ)` (`hasDerivAt_dilT`), uniform continuity of `s ↦ dilT s Ψ`
(compact support, periodicity) and `norm_testElem_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.F16b

open UnforcedLeray.PhaseSpace UnforcedLeray.FreeStress

variable {P : ℝ} [hP : Fact (0 < P)]

theorem dilT_zero (Φ : ℝ × Space → CVec3) : dilT 0 Φ = Φ := by
  funext p
  simp [dilT]

theorem dilT_eq_zero {Φ : ℝ × Space → CVec3} {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) {t : ℝ} (ht : |t| ≤ 1) (τ : ℝ) {y : Space}
    (hy : R * Real.exp (1 / 2) < ‖y‖) : dilT t Φ (τ, y) = 0 := by
  simp only [dilT]
  rw [hR _ _ ?_, smul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (t / 2) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.2 (by linarith [le_abs_self t])
  calc R = R * Real.exp (t / 2) * Real.exp (-(t / 2)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ R * Real.exp (1 / 2) * Real.exp (-(t / 2)) := by
        gcongr
    _ < ‖y‖ * Real.exp (-(t / 2)) := mul_lt_mul_of_pos_right hy (Real.exp_pos _)
    _ = Real.exp (-(t / 2)) * ‖y‖ := mul_comm _ _

theorem continuous_dilT_joint {Ψ : ℝ × Space → CVec3} (hΨ : Continuous Ψ) :
    Continuous (fun z : ℝ × (ℝ × Space) => dilT z.1 Ψ z.2) := by
  unfold dilT
  have h1 : Continuous (fun z : ℝ × (ℝ × Space) => (Real.exp (-(3 / 4) * z.1) : ℂ)) := by
    fun_prop
  have h2 : Continuous (fun z : ℝ × (ℝ × Space) =>
      ((z.2.1 + z.1, Real.exp (-(z.1 / 2)) • z.2.2) : ℝ × Space)) := by fun_prop
  exact h1.smul (hΨ.comp h2)

/-- Uniform continuity of `s ↦ dilT s Ψ` at `s = 0` for a phase test. -/
theorem dilT_uniform {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ p : ℝ × Space, ‖dilT s Ψ p - Ψ p‖ < ε := by
  obtain ⟨R, hR⟩ := hΨ.bounded_support
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR'1 : ∀ τ y, R' < ‖y‖ → Ψ (τ, y) = 0 := fun τ y hy =>
    hR τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  set R1 := R' * Real.exp (1 / 2) with hR1
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hF := continuous_dilT_joint hΨ.continuous
  have hevK : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ p ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R1,
      ‖dilT s Ψ p - Ψ p‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually (P := fun s p => ‖dilT s Ψ p - Ψ p‖ < ε) ?_
    intro p _
    have hc : Continuous (fun z : ℝ × (ℝ × Space) => ‖dilT z.1 Ψ z.2 - Ψ z.2‖) := by
      exact (hF.sub (hΨ.continuous.comp (continuous_snd))).norm
    have h0 : ‖dilT (0 : ℝ) Ψ p - Ψ p‖ < ε := by simp [dilT_zero, hε]
    exact (hc.continuousAt (x := (0, p))).eventually (gt_mem_nhds (a := _) h0) |>.mono fun z hz => hz
  have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), |s| ≤ 1 := by
    have : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ one_pos
    filter_upwards [this] with s hs
    simpa using (Metric.mem_ball.1 hs).le
  filter_upwards [hevK, hev1] with s hs h1 p
  obtain ⟨τ, y⟩ := p
  by_cases hy : R1 < ‖y‖
  · rw [dilT_eq_zero hR'0 hR'1 h1 τ hy, hR'1 τ y (lt_of_le_of_lt (by
      rw [hR1]; exact le_mul_of_one_le_right hR'0 (Real.one_le_exp (by norm_num))) hy)]
    simpa using hε
  · push_neg at hy
    set τ' := toIcoMod hP.out 0 τ with hτ'
    have hmem : (τ', y) ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R1 := by
      refine ⟨?_, by simpa using hy⟩
      have := toIcoMod_mem_Ico hP.out 0 τ
      exact ⟨this.1, by linarith [this.2]⟩
    have hp : Function.Periodic (fun x : ℝ => dilT s Ψ (x, y) - Ψ (x, y)) P := by
      intro x
      simp only
      rw [(isPhaseTest_dilT hΨ s).periodic, hΨ.periodic]
    have heq : dilT s Ψ (τ, y) - Ψ (τ, y) = dilT s Ψ (τ', y) - Ψ (τ', y) := by
      have := hp.sub_zsmul_eq (x := τ) (toIcoDiv hP.out 0 τ)
      rw [self_sub_toIcoDiv_zsmul] at this
      exact this.symm
    rw [heq]
    exact hs _ hmem

theorem hasDerivAt_dilT_test {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (p : ℝ × Space)
    (s : ℝ) : HasDerivAt (fun s : ℝ => dilT s Φ p) (dilT s (Bop Φ) p) s :=
  hasDerivAt_dilT (hΦ.smooth.differentiable (by simp)) p s

/-- Pointwise: `h⁻¹ (dilT h Φ - Φ) - BΦ` is small when `dilT s (BΦ) - BΦ` is. -/
theorem quotient_bound {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) {η : ℝ} {δ : ℝ}
    (hη : ∀ s : ℝ, |s| < δ → ∀ p, ‖dilT s (Bop Φ) p - Bop Φ p‖ ≤ η) {h : ℝ} (hh : h ≠ 0)
    (hδ : |h| < δ) (p : ℝ × Space) :
    ‖(h : ℂ)⁻¹ • (dilT h Φ p - Φ p) - Bop Φ p‖ ≤ η := by
  set Ψ := Bop Φ with hΨ
  have hcont : Continuous fun s : ℝ => dilT s Ψ p := by
    have := continuous_dilT_joint (isPhaseTest_Bop hΦ).continuous
    exact this.comp (continuous_id.prodMk continuous_const)
  have hftc : ∫ s in (0 : ℝ)..h, dilT s Ψ p = dilT h Φ p - Φ p := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := h)
      (f := fun s : ℝ => dilT s Φ p) (f' := fun s => dilT s Ψ p)
      (fun s _ => hasDerivAt_dilT_test hΦ p s) (hcont.intervalIntegrable _ _)
    rw [this, dilT_zero]
  have hI : ∫ s in (0 : ℝ)..h, (dilT s Ψ p - Ψ p) = (dilT h Φ p - Φ p) - h • Ψ p := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
      hftc, intervalIntegral.integral_const]
    simp
  have hbd : ‖∫ s in (0 : ℝ)..h, (dilT s Ψ p - Ψ p)‖ ≤ η * |h - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    refine hη s ?_ p
    rw [Set.mem_uIoc] at hs
    have : |s| ≤ |h| := by
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos h1, abs_of_pos (h1.trans_le h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_neg (h1.trans_le h2 |>.trans_le le_rfl |> fun _ => by linarith)]
        linarith
    exact this.trans_lt hδ
  have hrew : (h : ℂ)⁻¹ • (dilT h Φ p - Φ p) - Ψ p =
      (h : ℂ)⁻¹ • ∫ s in (0 : ℝ)..h, (dilT s Ψ p - Ψ p) := by
    rw [hI]
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have e : (h : ℂ)⁻¹ • (h • Ψ p) = Ψ p := by
      rw [← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hh', one_smul]
    rw [smul_sub ((h : ℂ)⁻¹) (dilT h Φ p - Φ p), e]
  rw [hrew, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < |h| := abs_pos.2 hh
  calc |h|⁻¹ * ‖∫ s in (0 : ℝ)..h, (dilT s Ψ p - Ψ p)‖ ≤ |h|⁻¹ * (η * |h - 0|) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hpos.le)
    _ = η := by rw [sub_zero]; field_simp

/-- **The derivative of `e^{tB}` on a phase test** (in `Y_2`). -/
theorem tendsto_dil_testElem {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (phaseDilation P h (testElem P 2 Φ) - testElem P 2 Φ))
      (𝓝[≠] 0) (𝓝 (testElem P 2 (Bop Φ))) := by
  have hΨ := isPhaseTest_Bop hΦ
  obtain ⟨RΦ, hRΦ⟩ := hΦ.bounded_support
  obtain ⟨RΨ, hRΨ⟩ := hΨ.bounded_support
  set R' := max (max RΦ RΨ) 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hRΦ' : ∀ τ y, R' < ‖y‖ → Φ (τ, y) = 0 := fun τ y hy =>
    hRΦ τ y (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hy)
  have hRΨ' : ∀ τ y, R' < ‖y‖ → Bop Φ (τ, y) = 0 := fun τ y hy =>
    hRΨ τ y (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hy)
  set R1 := R' * Real.exp (1 / 2) with hR1
  have hR'R1 : R' ≤ R1 := le_mul_of_one_le_right hR'0 (Real.one_le_exp (by norm_num))
  set C := (volume (Metric.closedBall (0 : Space) R1) ^ (2 : ℝ≥0∞).toReal⁻¹).toReal with hC
  have hCnn : 0 ≤ C := ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := ε / (2 * (C + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hev := dilT_uniform hΨ hη
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : Metric.ball (0 : ℝ) (min δ 1) ∈ 𝓝[≠] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (lt_min hδ0 one_pos))
  filter_upwards [hball, self_mem_nhdsWithin] with h hh hne
  have hne' : h ≠ 0 := hne
  have hhd : |h| < min δ 1 := by simpa using Metric.mem_ball.1 hh
  have hhδ : |h| < δ := hhd.trans_le (min_le_left _ _)
  have hh1 : |h| ≤ 1 := (hhd.trans_le (min_le_right _ _)).le
  set G : ℝ × Space → CVec3 :=
    (h : ℂ)⁻¹ • dilT h Φ + (-(h : ℂ)⁻¹) • Φ + (-1 : ℂ) • Bop Φ with hG
  have hGt : IsPhaseTest P G :=
    (((isPhaseTest_dilT hΦ h).const_smul _).add (hΦ.const_smul _)).add (hΨ.const_smul _)
  have hs1 := (isPhaseTest_dilT hΦ h).isSliceTest 2
  have hs2 := hΦ.isSliceTest 2
  have hs3 := hΨ.isSliceTest 2
  have hGe : testElem P 2 G = (h : ℂ)⁻¹ • (phaseDilation P h (testElem P 2 Φ) - testElem P 2 Φ)
      - testElem P 2 (Bop Φ) := by
    rw [phaseDilation_testElem hΦ, hG, testElem_add (hs1.const_smul _ |>.add (hs2.const_smul _))
      (hs3.const_smul _), testElem_add (hs1.const_smul _) (hs2.const_smul _),
      testElem_const_smul hs1, testElem_const_smul hs2, testElem_const_smul hs3]
    module
  have hGp : ∀ p : ℝ × Space, G p = (h : ℂ)⁻¹ • (dilT h Φ p - Φ p) - Bop Φ p := by
    intro p
    simp only [hG, Pi.add_apply, Pi.smul_apply]
    module
  rw [dist_eq_norm, ← hGe]
  have hbound : ‖testElem P 2 G‖ ≤ C * η := by
    refine F02.norm_testElem_le (hGt.isSliceTest 2) R1 η hη.le ?_ ?_
    · intro τ y hy
      have hy' : R' < ‖y‖ := lt_of_le_of_lt hR'R1 hy
      rw [hGp, dilT_eq_zero hR'0 hRΦ' hh1 τ hy, hRΦ' τ y hy', hRΨ' τ y hy']
      simp
    · intro τ y
      rw [hGp]
      exact quotient_bound hΦ (fun s hs p => (hδ (by simpa using hs) p).le) hne' hhδ _
  calc ‖testElem P 2 G‖ ≤ C * η := hbound
    _ ≤ (C + 1) * η := by nlinarith
    _ = ε / 2 := by rw [hηdef]; field_simp
    _ < ε := by linarith

end UnforcedLeray.Short.PartIIa.F16b
