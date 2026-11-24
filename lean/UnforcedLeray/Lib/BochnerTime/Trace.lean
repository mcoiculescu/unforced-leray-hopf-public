import UnforcedLeray.Lib.BochnerTime.Energy

/-!
# One-dimensional trace interpolation (INF14 target T3, blueprint unit B0236)


target T3. Manuscript `paper/main.tex` lines 4059–4065 (blueprint unit B0236): for a bounded
interval `I`, `H` in the interior of `I`, `1 < p < ∞` and the continuous representative of
`a ∈ W^{1,p}(I)`,
`|a(H)| ≤ C_I [‖a‖_{L^p(I)} + ‖a‖_{L^p(I)}^{1-1/p} ‖a'‖_{L^p(I)}^{1/p}]`.

Here `I = (a, b)`, `W^{1,p}(I)` is `HasWeakDerivTime a b f f'` together with
`MemLp f p` and `MemLp f' p` on `Ioo a b` (integrability on `Ioo a b` is implied by these), and
the continuous representative is `HasWeakDerivTime.rep` (unique on `Icc a b` by `eqOn_rep`).
The point `H` may be any point of `Icc a b`, and the constant
`traceConst (b - a) p = 2 (1 + (b - a)^{-1/p})` depends only on `|I|` and `p`, so the
statement is stronger than the manuscript's.

## Proof

For `0 < δ ≤ b - a` choose a subinterval `J = [c, c + δ] ⊆ [a, b]` containing `H`. The FTC
gives `|f(H)| ≤ |f(s)| + ∫_J |f'|` for `s ∈ J`; averaging over `J` and Hölder give
`|f(H)| ≤ δ^{-1/p} ‖f‖_p + δ^{1-1/p} ‖f'‖_p` (`abs_rep_le_of_le`). Choosing
`δ = min(b - a, ‖f‖_p/‖f'‖_p)` gives the claim; the case `‖f‖_p = 0` is a limit `δ → 0`.

The pairing part of T3 (B0445: `a_ε(s) = ∫ k_H · u(s)` has derivative `∫ k_H · ∂_s u`) is
`HasWeakDerivTime.map` with `L` the pairing functional.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.BochnerTime

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Increment bound on a subinterval.** For `[c, d] ⊆ [a, b]` and `s, t ∈ [c, d]`,
`‖ũ t - ũ s‖ ≤ ∫_c^d ‖u'‖`. -/
theorem HasWeakDerivTime.norm_rep_sub_le_of_subset {a b c d : ℝ} {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') (hac : a ≤ c) (hdb : d ≤ b) {s t : ℝ} (hs : s ∈ Icc c d)
    (ht : t ∈ Icc c d) : ‖h.rep t - h.rep s‖ ≤ ∫ r in c..d, ‖u' r‖ := by
  have hcd : c ≤ d := hs.1.trans hs.2
  have hs' : s ∈ Icc a b := ⟨hac.trans hs.1, hs.2.trans hdb⟩
  have ht' : t ∈ Icc a b := ⟨hac.trans ht.1, ht.2.trans hdb⟩
  rw [h.rep_sub_rep hs' ht', norm_integral_eq_norm_integral_uIoc, integral_of_le hcd]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hint' : IntegrableOn u' (Ioc a b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact h.int'
  have hint : IntegrableOn u' (Ioc c d) := hint'.mono_set (Ioc_subset_Ioc hac hdb)
  refine setIntegral_mono_set hint.norm (Eventually.of_forall fun _ => norm_nonneg _) ?_
  refine LE.le.eventuallyLE ?_
  rw [uIoc]
  exact Ioc_subset_Ioc (le_min hs.1 ht.1) (max_le hs.2 ht.2)

/-- **Hölder on a subinterval.** For `[c, d] ⊆ [a, b]`, `1 < p` and `g ∈ L^p(a, b)`,
`∫_c^d |g| ≤ (d - c)^{1 - 1/p} (∫_{(a,b)} |g|^p)^{1/p}`. -/
theorem integral_abs_le_of_memLp {p : ℝ} (hp : 1 < p) {a b c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) {g : ℝ → ℝ} (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Ioo a b))) :
    ∫ r in c..d, |g r| ≤ (d - c) ^ (1 - 1 / p) * (∫ r in Ioo a b, |g r| ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set q := Real.conjExponent p with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hμ : volume.restrict (Ioc c d) ≤ volume.restrict (Ioo a b) := by
    rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b))]
    exact Measure.restrict_mono (Ioc_subset_Ioc hac hdb) le_rfl
  have hgJ : MemLp g (ENNReal.ofReal p) (volume.restrict (Ioc c d)) := hg.mono_measure hμ
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal q) (volume.restrict (Ioc c d)) :=
    memLp_const 1
  have h1 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc c d)) hpq
    (f := fun r => |g r|) (g := fun _ => (1 : ℝ)) (ae_of_all _ fun r => abs_nonneg (g r))
    (ae_of_all _ fun _ => zero_le_one) hgJ.abs hconst
  simp only [mul_one, Real.one_rpow] at h1
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hcd, smul_eq_mul, mul_one] at h1
  have hq : 1 / q = 1 - 1 / p := by rw [one_div, one_div, hpq.one_sub_inv]
  rw [hq] at h1
  rw [intervalIntegral.integral_of_le hcd]
  refine h1.trans ?_
  rw [mul_comm]
  have hint : Integrable (fun r => |g r| ^ p) (volume.restrict (Ioo a b)) := by
    have := hg.integrable_norm_rpow (by simpa using hp0) ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using this
  have hmono : ∫ r in Ioc c d, |g r| ^ p ≤ ∫ r in Ioo a b, |g r| ^ p :=
    integral_mono_measure hμ (ae_of_all _ fun r => Real.rpow_nonneg (abs_nonneg _) _) hint
  have hnn : 0 ≤ ∫ r in Ioc c d, |g r| ^ p :=
    setIntegral_nonneg measurableSet_Ioc fun r _ => Real.rpow_nonneg (abs_nonneg _) _
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnn hmono (by positivity))
    (Real.rpow_nonneg (sub_nonneg.2 hcd) _)

/-- The real `L^p` norm as an integral: `‖g‖_p = (∫ |g|^p)^{1/p}` for `g ∈ L^p`, `0 < p < ∞`. -/
theorem toReal_eLpNorm_eq {p : ℝ} (hp : 0 < p) {μ : Measure ℝ} {g : ℝ → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    (eLpNorm g (ENNReal.ofReal p) μ).toReal = (∫ r, |g r| ^ p ∂μ) ^ (1 / p) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal_eq_iff.2]
  · simp [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le, one_div]
  · exact Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _

/-- **The trace bound at scale `δ`.** For `0 < δ ≤ b - a` and `H ∈ [a, b]`,
`|ũ(H)| ≤ δ^{-1/p} (∫|f|^p)^{1/p} + δ^{1-1/p} (∫|f'|^p)^{1/p}` (integrals over `Ioo a b`). -/
theorem HasWeakDerivTime.abs_rep_le_of_le {p : ℝ} (hp : 1 < p) {a b H δ : ℝ}
    (hH : H ∈ Icc a b) (hδ : 0 < δ) (hδL : δ ≤ b - a) {f f' : ℝ → ℝ}
    (h : HasWeakDerivTime a b f f')
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ioo a b)))
    (hf' : MemLp f' (ENNReal.ofReal p) (volume.restrict (Ioo a b))) :
    |h.rep H| ≤ δ ^ (-(1 / p)) * (∫ r in Ioo a b, |f r| ^ p) ^ (1 / p) +
      δ ^ (1 - 1 / p) * (∫ r in Ioo a b, |f' r| ^ p) ^ (1 / p) := by
  set A := (∫ r in Ioo a b, |f r| ^ p) ^ (1 / p) with hA_def
  set B := (∫ r in Ioo a b, |f' r| ^ p) ^ (1 / p) with hB_def
  set c := min (max a (H - δ)) (b - δ) with hc
  have hac : a ≤ c := le_min (le_max_left _ _) (by linarith)
  have hdb : c + δ ≤ b := by have := min_le_right (max a (H - δ)) (b - δ); linarith
  have hcH : c ≤ H := (min_le_left _ _).trans (max_le hH.1 (by linarith))
  have hHd : H ≤ c + δ := by
    rcases le_total (max a (H - δ)) (b - δ) with h1 | h1
    · rw [hc, min_eq_left h1]; linarith [le_max_right a (H - δ)]
    · rw [hc, min_eq_right h1]; linarith [hH.2]
  set d := c + δ with hd_def
  have hcd : c ≤ d := by linarith
  have hdc : d - c = δ := by rw [hd_def]; ring
  set Bc := ∫ r in c..d, ‖f' r‖ with hBc_def
  have hpt : ∀ s ∈ Icc c d, |h.rep H| - Bc ≤ |h.rep s| := by
    intro s hs
    have h1 := h.norm_rep_sub_le_of_subset hac hdb hs ⟨hcH, hHd⟩
    have h2 := abs_sub_abs_le_abs_sub (h.rep H) (h.rep s)
    rw [Real.norm_eq_abs] at h1
    linarith
  have hcont : ContinuousOn (fun s => |h.rep s|) (uIcc c d) := by
    rw [uIcc_of_le hcd]; exact (h.continuousOn_rep.mono (Icc_subset_Icc hac hdb)).abs
  have hmono := intervalIntegral.integral_mono_on hcd
    (by simp : IntervalIntegrable (fun _ => |h.rep H| - Bc) volume c d)
    hcont.intervalIntegrable hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, hdc] at hmono
  have heq : ∫ s in c..d, |h.rep s| = ∫ s in c..d, |f s| := by
    refine intervalIntegral.integral_congr_ae ?_
    have h1 := (ae_restrict_iff' measurableSet_Ioo).1 h.ae_eq_rep
    have h2 : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [h1, h2] with s hs hsb hmem
    rw [uIoc_of_le hcd] at hmem
    rw [hs ⟨lt_of_le_of_lt hac hmem.1, lt_of_le_of_ne (hmem.2.trans hdb) hsb⟩]
  have hHf := integral_abs_le_of_memLp hp hac hcd hdb hf
  have hHf' := integral_abs_le_of_memLp hp hac hcd hdb hf'
  rw [hdc] at hHf hHf'
  rw [← hA_def] at hHf
  rw [← hB_def] at hHf'
  have hBc : Bc = ∫ r in c..d, |f' r| := by simp only [hBc_def, Real.norm_eq_abs]
  rw [heq] at hmono
  have key : δ⁻¹ * δ ^ (1 - 1 / p) = δ ^ (-(1 / p)) := by
    rw [← Real.rpow_neg_one δ, ← Real.rpow_add hδ]; congr 1; ring
  have h3 : |h.rep H| - Bc ≤ δ⁻¹ * (δ ^ (1 - 1 / p) * A) := by
    rw [inv_mul_eq_div, le_div_iff₀ hδ]; linarith
  rw [← mul_assoc, key] at h3
  linarith

/-- The constant of `trace_interp`: `2 (1 + L^{-1/p})`, depending only on the length `L` of the
interval and on `p`. -/
noncomputable def traceConst (L p : ℝ) : ℝ := 2 * (1 + L ^ (-(1 / p)))

/-- An `rpow` identity used to balance the two terms of the trace bound. -/
theorem rpow_div_mul_self {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 < B) :
    (A / B) ^ r * B = A ^ r * B ^ (1 - r) := by
  rw [Real.div_rpow hA hB.le, Real.rpow_sub hB, Real.rpow_one, div_mul_eq_mul_div, mul_div_assoc]

/-- **One-dimensional trace interpolation** (T3; manuscript tex 4059–4065, blueprint B0236).
For `a < b`, `H ∈ [a, b]`, `1 < p` and `f` with weak derivative `f'` on `(a, b)`, both in
`L^p(a, b)`, the continuous representative satisfies
`|f(H)| ≤ C_{b-a,p} (‖f‖_p + ‖f‖_p^{1-1/p} ‖f'‖_p^{1/p})`. -/
theorem trace_interp {p : ℝ} (hp : 1 < p) {a b H : ℝ} (hab : a < b) (hH : H ∈ Icc a b)
    {f f' : ℝ → ℝ} (h : HasWeakDerivTime a b f f')
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ioo a b)))
    (hf' : MemLp f' (ENNReal.ofReal p) (volume.restrict (Ioo a b))) :
    |h.rep H| ≤ traceConst (b - a) p *
      ((eLpNorm f (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal +
        (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal ^ (1 - 1 / p) *
          (eLpNorm f' (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal ^ (1 / p)) := by
  have hp0 : 0 < p := by linarith
  rw [toReal_eLpNorm_eq hp0 hf, toReal_eLpNorm_eq hp0 hf']
  set A := (∫ r in Ioo a b, |f r| ^ p) ^ (1 / p) with hA_def
  set B := (∫ r in Ioo a b, |f' r| ^ p) ^ (1 / p) with hB_def
  set L := b - a with hL_def
  have hL : 0 < L := sub_pos.2 hab
  have hA0 : 0 ≤ A := Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioo
    fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have hB0 : 0 ≤ B := Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioo
    fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have hcore : ∀ δ, 0 < δ → δ ≤ L → |h.rep H| ≤ δ ^ (-(1 / p)) * A + δ ^ (1 - 1 / p) * B :=
    fun δ hδ hδL => h.abs_rep_le_of_le hp hH hδ hδL hf hf'
  have hLp : 0 ≤ L ^ (-(1 / p)) := Real.rpow_nonneg hL.le _
  have hX : 0 ≤ A ^ (1 - 1 / p) * B ^ (1 / p) :=
    mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)
  have hshift : ∀ δ : ℝ, 0 < δ → δ ^ (1 - 1 / p) = δ ^ (-(1 / p)) * δ := by
    intro δ hδ
    rw [show (1 : ℝ) - 1 / p = -(1 / p) + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
  unfold traceConst
  rcases le_or_gt (L * B) A with hcase | hcase
  · -- `δ = L`
    have h1 := hcore L hL le_rfl
    have h2 : L ^ (1 - 1 / p) * B ≤ L ^ (-(1 / p)) * A := by
      rw [hshift L hL, mul_assoc]
      exact mul_le_mul_of_nonneg_left hcase hLp
    nlinarith [mul_nonneg hLp hX, mul_nonneg hLp hA0]
  · rcases eq_or_lt_of_le hA0 with hAz | hApos
    · -- `A = 0`: let `δ → 0`
      have hBpos : 0 < B := by
        by_contra hB
        have : B = 0 := le_antisymm (not_lt.1 hB) hB0
        rw [this, mul_zero, ← hAz] at hcase
        exact lt_irrefl _ hcase
      have hq : 0 < 1 - 1 / p := by
        have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
        linarith
      have hT : Tendsto (fun δ : ℝ => δ ^ (1 - 1 / p) * B) (𝓝[>] 0) (𝓝 0) := by
        have hc : ContinuousAt (fun δ : ℝ => δ ^ (1 - 1 / p)) 0 :=
          Real.continuousAt_rpow_const 0 _ (Or.inr hq.le)
        have := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).mul_const B
        rwa [Real.zero_rpow hq.ne', zero_mul] at this
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), |h.rep H| ≤ δ ^ (1 - 1 / p) * B := by
        filter_upwards [Ioo_mem_nhdsGT hL] with δ hδ
        have := hcore δ hδ.1 hδ.2.le
        rwa [← hAz, mul_zero, zero_add] at this
      have h0 : |h.rep H| ≤ 0 := ge_of_tendsto hT hev
      have : 0 ≤ 2 * (1 + L ^ (-(1 / p))) * (A + A ^ (1 - 1 / p) * B ^ (1 / p)) := by positivity
      linarith
    · -- `δ = A / B < L`
      have hBpos : 0 < B := by
        by_contra hB
        have : B = 0 := le_antisymm (not_lt.1 hB) hB0
        rw [this, mul_zero] at hcase
        linarith
      set δ := A / B with hδ_def
      have hδ : 0 < δ := div_pos hApos hBpos
      have hδL : δ ≤ L := by rw [hδ_def, div_le_iff₀ hBpos]; linarith
      have h1 := hcore δ hδ hδL
      have hAδ : A = δ * B := by rw [hδ_def, div_mul_cancel₀ _ hBpos.ne']
      have hterm : δ ^ (1 - 1 / p) * B = A ^ (1 - 1 / p) * B ^ (1 / p) := by
        rw [hδ_def, rpow_div_mul_self hA0 hBpos, show (1 : ℝ) - (1 - 1 / p) = 1 / p by ring]
      have hterm' : δ ^ (-(1 / p)) * A = A ^ (1 - 1 / p) * B ^ (1 / p) := by
        rw [← hterm, hAδ, ← mul_assoc, ← hshift δ hδ]
      rw [hterm, hterm'] at h1
      nlinarith [mul_nonneg hLp hX, mul_nonneg hLp hA0]

end UnforcedLeray.BochnerTime
