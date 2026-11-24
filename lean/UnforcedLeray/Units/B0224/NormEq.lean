import UnforcedLeray.Units.B0224.Lower

/-!
# B0224 helper: `‖T_0(t)‖ = ‖T_0(t)^*‖ = e^{-t/4}`

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3376: "Both have norm
`e^{-t/4}` on `H`". Lower bound by the concentrating test functions
`F_δ(s, q, η) = 1_{(δ,2δ]}(s) s^{3/4} V(η)` of `Lower.lean`, with `δ → 0`; see that file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220

variable {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If the `η`-heat moves `V` by at most `κ‖V‖` at every heat time met on the support of `g`,
then `‖(H_θ - 1)(gV)‖²_H ≤ κ² ‖gV‖²_H`. -/
theorem lintegral_defect_le (hc : 0 < c) {θ : ℝ → ℝ} (hθ : Measurable θ) {g : ℝ → ℝ}
    (hg : Measurable g) (V : Lp E 2 (volume : Measure ℝ)) {κ : ℝ≥0∞} (hκ : κ ≠ ∞)
    (hsmall : ∀ s, 0 < s → g s ≠ 0 →
      ‖Heat.heatLp etaι continuous_etaι (θ s) V - V‖ₑ ≤ κ * ‖V‖ₑ) :
    ∫⁻ p, ‖fiberHeat c θ (prodFun g V) p - prodFun g V p‖ₑ ^ 2 ∂measureH c ≤
      κ ^ 2 * ∫⁻ p, ‖prodFun g V p‖ₑ ^ 2 ∂measureH c := by
  rw [lintegral_fiberHeat_prodFun_sub_sq hc hθ hg V,
    lintegral_prodFun_sq hc hg (Lp.stronglyMeasurable V), ← enorm_sq_Lp,
    ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hκ)]
  refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
  by_cases hg0 : g s = 0
  · simp [hg0]
  · have h := hsmall s hs hg0
    calc ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * (ENNReal.ofReal c * (‖g s‖ₑ ^ 2 *
          ‖Heat.heatLp etaι continuous_etaι (θ s) V - V‖ₑ ^ 2))
        ≤ ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * (ENNReal.ofReal c * (‖g s‖ₑ ^ 2 *
          (κ * ‖V‖ₑ) ^ 2)) := by gcongr
      _ = κ ^ 2 * (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * (ENNReal.ofReal c *
          (‖g s‖ₑ ^ 2 * ‖V‖ₑ ^ 2))) := by ring

/-- The age profile `g_δ(s) = 1_{(δ,2δ]}(s) s^{3/4}`, normalised so that `s^{-3/2} g_δ² = 1`. -/
def ageBump (δ : ℝ) : ℝ → ℝ := (Ioc δ (2 * δ)).indicator fun s => s ^ (3 / 4 : ℝ)

theorem measurable_ageBump (δ : ℝ) : Measurable (ageBump δ) :=
  (measurable_id.pow_const _).indicator measurableSet_Ioc

theorem weight_ageBump_sq {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ‖ageBump δ s‖ₑ ^ 2 =
      (Ioc δ (2 * δ)).indicator (fun _ => (1 : ℝ≥0∞)) s := by
  by_cases h : s ∈ Ioc δ (2 * δ)
  · rw [ageBump, indicator_of_mem h, indicator_of_mem h,
      Real.enorm_of_nonneg (Real.rpow_nonneg hs.le _), ← ENNReal.ofReal_pow
        (Real.rpow_nonneg hs.le _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      ← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
    norm_num
  · rw [ageBump, indicator_of_notMem h, indicator_of_notMem h]
    simp

theorem lintegral_prodFun_ageBump_sq (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ)
    (V : Lp E 2 (volume : Measure ℝ)) :
    ∫⁻ p, ‖prodFun (ageBump δ) V p‖ₑ ^ 2 ∂measureH c =
      ENNReal.ofReal c * ‖V‖ₑ ^ 2 * ENNReal.ofReal δ := by
  rw [lintegral_prodFun_sq hc (measurable_ageBump δ) (Lp.stronglyMeasurable V), ← enorm_sq_Lp]
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (ENNReal.ofReal c * (‖ageBump δ s‖ₑ ^ 2 * ‖V‖ₑ ^ 2))
      = ∫⁻ s in Ioi (0 : ℝ), (Ioc δ (2 * δ)).indicator
          (fun _ => ENNReal.ofReal c * ‖V‖ₑ ^ 2) s := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        have h := weight_ageBump_sq hδ (s := s) hs
        calc ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
              (ENNReal.ofReal c * (‖ageBump δ s‖ₑ ^ 2 * ‖V‖ₑ ^ 2))
            = (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ‖ageBump δ s‖ₑ ^ 2) *
                (ENNReal.ofReal c * ‖V‖ₑ ^ 2) := by ring
          _ = _ := by
            rw [h]
            by_cases hm : s ∈ Ioc δ (2 * δ)
            · rw [indicator_of_mem hm, indicator_of_mem hm, one_mul]
            · rw [indicator_of_notMem hm, indicator_of_notMem hm, zero_mul]
    _ = ENNReal.ofReal c * ‖V‖ₑ ^ 2 * ENNReal.ofReal δ := by
        rw [lintegral_indicator_const measurableSet_Ioc,
          Measure.restrict_apply measurableSet_Ioc,
          inter_eq_left.2 (show Ioc δ (2 * δ) ⊆ Ioi 0 from fun x hx => lt_trans hδ hx.1),
          Real.volume_Ioc, show 2 * δ - δ = δ by ring]

theorem eLpNorm_le_of_lintegral_le {μ : Measure Profile} {F G : Profile → E} {κ : ℝ≥0∞}
    (h : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂μ ≤ κ ^ 2 * ∫⁻ p, ‖G p‖ₑ ^ 2 ∂μ) :
    eLpNorm F 2 μ ≤ κ * eLpNorm G 2 μ := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq]
  calc (∫⁻ p, ‖F p‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ (κ ^ 2 * ∫⁻ p, ‖G p‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = κ * (∫⁻ p, ‖G p‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- **Lower bound** `e^{-t/4} ≤ ‖T_0(t)‖` (every `t`, `ν`; `E ≠ 0`). -/
theorem le_norm_T0 [Nontrivial E] (hc : 0 < c) (ν t : ℝ) :
    Real.exp (-t / 4) ≤ ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ := by
  set A : ℝ := Real.exp (-t / 4) with hA
  have hA0 : 0 < A := Real.exp_pos _
  suffices h : ∀ κ : ℝ, 0 < κ → (1 - κ) * A ≤ ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ by
    by_contra hlt
    rw [not_le] at hlt
    set B := ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖
    have hk := h ((A - B) / (2 * A)) (div_pos (by linarith) (by positivity))
    have he : (1 - (A - B) / (2 * A)) * A = (A + B) / 2 := by field_simp; ring
    linarith
  intro κ hκ
  -- a nonzero `V ∈ L²(ℝ; E)`
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hvol : (volume : Measure ℝ) (Icc 0 1) ≠ ∞ := measure_Icc_lt_top.ne
  obtain ⟨V, hVdef⟩ : ∃ V : Lp E 2 (volume : Measure ℝ),
      V = indicatorConstLp 2 measurableSet_Icc hvol e := ⟨_, rfl⟩
  have hVn : 0 < ‖V‖ := by
    rw [hVdef, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    simp [he]
  have hVe : ‖V‖ₑ ≠ 0 := by
    rw [← ofReal_norm]; exact (ENNReal.ofReal_pos.2 hVn).ne'
  have hVt : ‖V‖ₑ ≠ ∞ := enorm_ne_top
  -- strong continuity of the `η`-heat at time `0`
  have hcont := Heat.tendsto_heatLp_sub etaι continuous_etaι ENNReal.ofNat_ne_top V
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal κ * ‖V‖ₑ :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hκ).ne' hVe
  obtain ⟨θ0, hθ0, hball⟩ :=
    Metric.eventually_nhds_iff.1 ((ENNReal.tendsto_nhds_zero.1 hcont) _ hpos)
  -- the age scale `δ`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = |ν * (1 - Real.exp (-t))| + 1 := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = θ0 / (2 * Real.exp t * L) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hg : Measurable (ageBump δ) := measurable_ageBump δ
  have hg' : Measurable fun s => ageBump δ (Real.exp (-t) * s) :=
    hg.comp (measurable_id.const_mul _)
  have hK := stronglyMeasurable_prodFun hg (Lp.stronglyMeasurable V)
  have hK' := stronglyMeasurable_prodFun hg' (Lp.stronglyMeasurable V)
  -- the test function `F = g V ∈ H`
  have hnormF := lintegral_prodFun_ageBump_sq (c := c) hc hδ0 V
  have hfin : ENNReal.ofReal c * ‖V‖ₑ ^ 2 * ENNReal.ofReal δ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hVt))
      ENNReal.ofReal_ne_top
  have hFmem : MemLp (prodFun (ageBump δ) V) 2 (measureH c) := by
    refine ⟨hK.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_two_eq, hnormF]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin
  obtain ⟨F, hFdef⟩ : ∃ F : HSpace c E, F = hFmem.toLp _ := ⟨_, rfl⟩
  have hFpos : 0 < ‖F‖ := by
    rw [hFdef, Lp.norm_toLp, eLpNorm_two_eq, hnormF]
    refine ENNReal.toReal_pos ?_ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin).ne
    refine (ENNReal.rpow_pos ?_ hfin).ne'
    exact ENNReal.mul_pos (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc).ne'
      (pow_ne_zero 2 hVe)).ne' (ENNReal.ofReal_pos.2 hδ0).ne'
  have hFae : (F : Profile → E) =ᵐ[measureH c] prodFun (ageBump δ) V := by
    rw [hFdef]; exact MemLp.coeFn_toLp hFmem
  -- `D F = g' V`
  obtain ⟨G, hGdef⟩ : ∃ G : HSpace c E, G = dilH (Real.exp_pos (-t)) F := ⟨_, rfl⟩
  have hG : (G : Profile → E) =ᵐ[measureH c]
      prodFun (fun s => ageBump δ (Real.exp (-t) * s)) V := by
    rw [hGdef]
    refine (coeFn_dilH _ F).trans ?_
    rw [← dil_prodFun]
    exact dil_congr_ae (Real.exp_pos (-t)) (Lp.stronglyMeasurable F) hK hFae
  have hnormG : ‖G‖ = A * ‖F‖ := by
    rw [hGdef, norm_dilH_apply, exp_neg_rpow_quarter]
  -- the heat defect on `G` is at most `κ ‖G‖`
  have hsmall : ∀ s, 0 < s → ageBump δ (Real.exp (-t) * s) ≠ 0 →
      ‖Heat.heatLp etaι continuous_etaι (heatTime ν t s) V - V‖ₑ ≤ ENNReal.ofReal κ * ‖V‖ₑ := by
    intro s hs hgs
    have hmem : Real.exp (-t) * s ∈ Ioc δ (2 * δ) := by
      by_contra hn
      exact hgs (by simp only [ageBump, indicator_of_notMem hn])
    have hs2 : s ≤ 2 * δ * Real.exp t := by
      have h1 := hmem.2
      have h2 : s = Real.exp t * (Real.exp (-t) * s) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      rw [h2]
      nlinarith [Real.exp_pos t]
    apply hball
    rw [Real.dist_eq, sub_zero, heatTime]
    have hab : |ν * s * (1 - Real.exp (-t))| = |ν * (1 - Real.exp (-t))| * s := by
      rw [show ν * s * (1 - Real.exp (-t)) = ν * (1 - Real.exp (-t)) * s by ring, abs_mul,
        abs_of_pos hs]
    rw [hab]
    calc |ν * (1 - Real.exp (-t))| * s ≤ |ν * (1 - Real.exp (-t))| * (2 * δ * Real.exp t) :=
          mul_le_mul_of_nonneg_left hs2 (abs_nonneg _)
      _ < L * (2 * δ * Real.exp t) := by
          apply mul_lt_mul_of_pos_right (by rw [hL]; linarith) (by positivity)
      _ = θ0 := by rw [hδ]; field_simp
  have hdef := lintegral_defect_le hc (measurable_heatTime ν t) hg' V ENNReal.ofReal_ne_top hsmall
  have hHG : (heatH hc (measurable_heatTime ν t) G - G : HSpace c E) =ᵐ[measureH c]
      fun p => fiberHeat c (heatTime ν t) (prodFun (fun s => ageBump δ (Real.exp (-t) * s)) V) p -
        prodFun (fun s => ageBump δ (Real.exp (-t) * s)) V p := by
    filter_upwards [Lp.coeFn_sub (heatH hc (measurable_heatTime ν t) G) G,
      coeFn_heatH hc (measurable_heatTime ν t) G,
      fiberHeat_congr_ae hc (measurable_heatTime ν t) (Lp.stronglyMeasurable G) hK' hG, hG]
      with p h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
  have hGfin : eLpNorm (prodFun (fun s => ageBump δ (Real.exp (-t) * s)) V) 2 (measureH c) ≠ ∞ :=
    (eLpNorm_congr_ae hG).symm ▸ Lp.eLpNorm_ne_top G
  have hdefect : ‖heatH hc (measurable_heatTime ν t) G - G‖ ≤ κ * ‖G‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hHG, eLpNorm_congr_ae hG]
    have h := eLpNorm_le_of_lintegral_le hdef
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin) h).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ.le]
  -- conclusion
  have hT : T0 hc ν t F = heatH hc (measurable_heatTime ν t) G := by rw [hGdef]; rfl
  have hlow : (1 - κ) * A * ‖F‖ ≤ ‖T0 hc ν t F‖ := by
    rw [hT]
    have h1 := norm_sub_norm_le G (heatH hc (measurable_heatTime ν t) G)
    rw [norm_sub_rev] at h1
    nlinarith [hnormG, hdefect]
  have hup := (T0 hc ν t).le_opNorm F
  have : (1 - κ) * A * ‖F‖ ≤ ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ * ‖F‖ :=
    hlow.trans hup
  exact le_of_mul_le_mul_right this hFpos

/-- **`‖T_0(t)‖ = e^{-t/4}`** on `H` (tex line 3376). -/
theorem norm_T0 [Nontrivial E] (hc : 0 < c) (ν t : ℝ) :
    ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ = Real.exp (-t / 4) :=
  le_antisymm (norm_T0_le hc ν t) (le_norm_T0 hc ν t)

end UnforcedLeray.B0224
