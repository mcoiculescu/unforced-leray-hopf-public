import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MomentSplit
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split.DiffLocal

/-!
# Part III-a, task `PartIII-a:T17/1`: `SepSplit` (SP 3735-3745)

Linearity of the thin-source response at the receiver.  `thinSource ε F` is the sum of the
thin sources of the phase mean and the oscillation.  For `thinMoment c F < ∞` the phase integral of
`∫₀¹∫|T(τ + 2 log λ, z)| dz dλ` over one period is finite (Tonelli, the `τ`-integral over a period
of a `c`-periodic function removes the `λ`- and radial dependence; `Split/TonelliMain.lean`), so
for a.e. `τ` the order-`0` majorant is finite at the receiver, `sepW` is the product integral of
`sepDiffF` near `y` and is differentiable there (`Split/DiffLocal.lean`, extracted from the
differentiation under the integral of `sepWDiffUnder_of`).  Additivity of the integral and of
`fderiv` finishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem t17s_sepDom_lt_top (a : ℝ) (ha : 0 ≤ a) (D : ℝ) (hD : 0 < D) (g : ℝ → Space → ℝ≥0∞)
    (τ : ℝ) (y : Space)
    (h : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, g (τ + 2 * Real.log l) z < ⊤) :
    sepDom a 0 D g τ y < ⊤ := by
  set κ : ℝ≥0∞ := ENNReal.ofReal (D ^ (-4 : ℝ)) with hκ
  have hkd : ∀ x : Space, sepKd 0 D x ≤ κ := by
    intro x
    unfold sepKd
    split_ifs with hx
    · refine ENNReal.ofReal_le_ofReal ?_
      simpa using Real.rpow_le_rpow_of_nonpos hD hx (by norm_num : (-4 : ℝ) - ((0 : ℕ) : ℝ) ≤ 0)
    · exact zero_le
  calc sepDom a 0 D g τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, κ * ∫⁻ z : Space, g (τ + 2 * Real.log l) z := by
        unfold sepDom
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have h1 : ENNReal.ofReal (l ^ a) ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hl.1.le hl.2.le ha)
        calc ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, sepKd 0 D (y - l • z) * g (τ + 2 * Real.log l) z
            ≤ 1 * ∫⁻ z : Space, κ * g (τ + 2 * Real.log l) z := by
              gcongr with z
              exact hkd _
          _ = κ * ∫⁻ z : Space, g (τ + 2 * Real.log l) z := by
              rw [one_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = κ * ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, g (τ + 2 * Real.log l) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem t17s_isSepSource (ε c ρo : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j)
    (hper : ∀ x' Y q, G x' Y (q + c) = G x' Y q)
    (hsupp : ∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y q = 0) :
    IsSepSource (2 * ε * c) (ρo / ε) (thinSource ε G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hm : Measurable fun p : ℝ × Space => ((ε * p.2 0, ε * p.2 1), p.2 2,
        ε⁻¹ * Real.log (ε * Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2)) + p.1 / (2 * ε)) := by
      have h0 : Measurable fun p : ℝ × Space => p.2 0 := (t17s_meas_coord 0).comp measurable_snd
      have h1 : Measurable fun p : ℝ × Space => p.2 1 := (t17s_meas_coord 1).comp measurable_snd
      have h2 : Measurable fun p : ℝ × Space => p.2 2 := (t17s_meas_coord 2).comp measurable_snd
      refine ((measurable_const.mul h0).prodMk (measurable_const.mul h1)).prodMk (h2.prodMk ?_)
      refine (measurable_const.mul (Real.measurable_log.comp (measurable_const.mul
        (Measurable.sqrt ((h0.pow_const 2).add (h1.pow_const 2)))))).add
        (measurable_fst.div_const _)
    exact (hG i j).comp hm
  · intro τ z
    unfold thinSource
    have : ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + (τ + 2 * ε * c) / (2 * ε) =
        (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε)) + c := by
      field_simp
      ring
    rw [this, hper]
  · intro τ z hz
    unfold thinSource
    apply hsupp
    have h2 : Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2) = ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
      have : (ε * z 0) ^ 2 + (ε * z 1) ^ 2 = ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
    simp only
    rw [h2]
    rw [div_lt_iff₀ hε] at hz
    linarith

theorem t17s_one (hK : SepKernelBounds) (ν c ε ρo ρi : ℝ) (μ : ℂ) (hν : 0 < ν) (hc : 0 < c)
    (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j)
    (hper : ∀ x' Y q, G x' Y (q + c) = G x' Y q)
    (hsupp : ∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y q = 0)
    (hN : thinMoment c G ≠ ⊤) (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * ε * c))),
      (∀ᶠ y' in 𝓝 (ε⁻¹ • xo), Integrable (fun p => sepDiffF ν μ (thinSource ε G) τ p y') sepDiffRho ∧
        sepW ν μ (thinSource ε G) y' τ = ∫ p, sepDiffF ν μ (thinSource ε G) τ p y' ∂sepDiffRho) ∧
      DifferentiableAt ℝ (fun y' => sepW ν μ (thinSource ε G) y' τ) (ε⁻¹ • xo) := by
  filter_upwards [t17s_srcInt_ae ε c hε hc G hG hper hN] with τ hτ
  have hD : 0 < ρi / ε - ρo / ε := by
    have : 0 < ρi - ρo := by linarith
    rw [← sub_div]; positivity
  have hy : ρi / ε ≤ Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) := by
    have h2 : Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) =
        ε⁻¹ * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
      have : (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hε.le)]
    rw [h2, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  exact t17s_local hK ν hν μ (ρo / ε) (ρi / ε) (2 * ε * c) (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) (thinSource ε G)
    (t17s_isSepSource ε c ρo hε hc G hG hper hsupp) τ (ε⁻¹ • xo) hy
    (t17s_sepDom_lt_top (2 * μ.re + 2) (by linarith) _ hD _ τ _ hτ)

theorem t17s_thin_add (ε : ℝ) (c : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (z : Space) :
    thinSource ε F τ z = thinSource ε (meanLift (phaseMean c F)) τ z +
      thinSource ε (perpPart c F) τ z := by
  unfold thinSource meanLift perpPart
  simp

theorem sepSplit : UnforcedLeray.Short.IIIa.SepSplit := by
  intro ν c ε ρo ρi μ hν hc hε hρo hρ hμ F hmeas hper hsupp hN xo hxo
  have hK := sepKernelBounds
  obtain ⟨hm1, hm2⟩ := sepMomentSplit c hc F hmeas
  have hN1 : thinMoment c (meanLift (phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN hm1
  have hN2 : thinMoment c (perpPart c F) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hN) hm2
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => phaseMean c F w.1 w.2 i j :=
    phaseMean_measurable c F hmeas
  have hG1 : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ =>
      meanLift (phaseMean c F) w.1 w.2.1 w.2.2 i j := fun i j =>
    (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop)
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [phaseMean, hsupp x' Y _ h]
  have hG2 : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => perpPart c F w.1 w.2.1 w.2.2 i j := by
    intro i j
    exact (hmeas i j).sub ((hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop))
  have hp1 : ∀ x' Y q, meanLift (phaseMean c F) x' Y (q + c) = meanLift (phaseMean c F) x' Y q :=
    fun _ _ _ => rfl
  have hp2 : ∀ x' Y q, perpPart c F x' Y (q + c) = perpPart c F x' Y q := by
    intro x' Y q; simp [perpPart, hper]
  have hs1 : ∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → meanLift (phaseMean c F) x' Y q = 0 :=
    fun x' Y q h => hGs x' Y h
  have hs2 : ∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → perpPart c F x' Y q = 0 := by
    intro x' Y q h
    simp [perpPart, hsupp x' Y q h, hGs x' Y h]
  filter_upwards [t17s_one hK ν c ε ρo ρi μ hν hc hε hρo hρ hμ _ hG1 hp1 hs1 hN1 xo hxo,
    t17s_one hK ν c ε ρo ρi μ hν hc hε hρo hρ hμ _ hG2 hp2 hs2 hN2 xo hxo] with τ h1 h2
  obtain ⟨e1, d1⟩ := h1
  obtain ⟨e2, d2⟩ := h2
  have hTeq : ∀ p y', sepDiffF ν μ (thinSource ε F) τ p y' =
      sepDiffF ν μ (thinSource ε (meanLift (phaseMean c F))) τ p y' +
        sepDiffF ν μ (thinSource ε (perpPart c F)) τ p y' := by
    intro p y'
    funext i
    simp only [sepDiffF, Pi.add_apply, t17s_thin_add ε c F]
    simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
  have hev : (fun y' => sepW ν μ (thinSource ε F) y' τ) =ᶠ[𝓝 (ε⁻¹ • xo)]
      fun y' => sepW ν μ (thinSource ε (meanLift (phaseMean c F))) y' τ +
        sepW ν μ (thinSource ε (perpPart c F)) y' τ := by
    filter_upwards [e1, e2] with y' hy1 hy2
    have hint : Integrable (fun p => sepDiffF ν μ (thinSource ε F) τ p y') sepDiffRho := by
      have := hy1.1.add hy2.1
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp [hTeq]
    rw [sepDiffWEqIntegral ν μ _ τ y' hint, hy1.2, hy2.2]
    simp_rw [hTeq]
    exact integral_add hy1.1 hy2.1
  rw [hev.fderiv_eq]
  exact fderiv_add d1 d2

end UnforcedLeray.Short.IIIa

end
