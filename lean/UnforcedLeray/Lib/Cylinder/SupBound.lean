import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The one-dimensional `H¹ ⊂ L^∞` bound in `q` (INF13, target CY04, `sq_sup_q_le`)


§5 CY04 (`sq_sup_q_le`); blueprint unit B0183 (`paper/main.tex` lines 2826-2832:
"`H¹(ℝ/cℤ) ⊂ L^∞` with a polynomial `c` constant").

For a `C¹`, `c`-periodic `g : ℝ → ℂ` and every `q`,
`|g(q)|² ≤ 2 c⁻¹ ∫_{-c/2}^{c/2} |g|² + c ∫_{-c/2}^{c/2} |g'|²`
(`sq_norm_le_of_periodic`).  Proof: `|g|²` attains its minimum `≤ c⁻¹ ∫|g|²` at some `s₀` of
the period; `|g(q)|² - |g(s₀)|² = ∫_{s₀}^{q} 2 Re(ḡ g')` and `2|g||g'| ≤ c⁻¹|g|² + c|g'|²`.
The cylinder forms (`sq_norm_le_cyl`, `sq_sup_q_le`) apply it to the slices
`q ↦ f(q, η)`; they are the classical (`C¹`) form of the manuscript's `H¹` statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real

namespace UnforcedLeray.Cyl

/-- **`H¹(ℝ/cℤ) ⊂ L^∞`** (B0183): for a `C¹`, `c`-periodic `g` and every `q`,
`|g(q)|² ≤ 2 c⁻¹ ∫_{-c/2}^{c/2} |g|² + c ∫_{-c/2}^{c/2} |g'|²`. -/
theorem sq_norm_le_of_periodic {c : ℝ} (hc : 0 < c) {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : Function.Periodic g c) (q : ℝ) :
    ‖g q‖ ^ 2 ≤ 2 * c⁻¹ * (∫ s in (-c / 2)..(c / 2), ‖g s‖ ^ 2) +
      c * ∫ s in (-c / 2)..(c / 2), ‖deriv g s‖ ^ 2 := by
  have hle : -c / 2 ≤ c / 2 := by linarith
  have hgc : Continuous g := hg.continuous
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgd : ∀ s, HasDerivAt g (deriv g s) s := fun s =>
    ((hg.differentiable one_ne_zero) s).hasDerivAt
  set h : ℝ → ℝ := fun s => ‖g s‖ ^ 2 with hh
  set h' : ℝ → ℝ := fun s => 2 * inner ℝ (g s) (deriv g s) with hh'
  have hhd : ∀ s, HasDerivAt h (h' s) s := fun s => HasDerivAt.norm_sq (hgd s)
  have hhc : Continuous h := hgc.norm.pow 2
  have hh'c : Continuous h' := continuous_const.mul (hgc.inner hdc)
  -- reduce `q` to the centred period
  have hcp : 0 < c := hc
  set q' := toIcoMod hcp (-c / 2) q with hq'
  have hq'mem : q' ∈ Ico (-c / 2) (-c / 2 + c) := toIcoMod_mem_Ico hcp (-c / 2) q
  have hgq : g q = g q' := by
    rw [hq', ← self_sub_toIcoDiv_zsmul, hper.sub_zsmul_eq]
  have hq'I : q' ∈ Icc (-c / 2) (c / 2) := ⟨hq'mem.1, by linarith [hq'mem.2]⟩
  -- a minimum point of `h` on the period
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hle) hhc.continuousOn
  have hmean : h s₀ ≤ c⁻¹ * ∫ s in (-c / 2)..(c / 2), h s := by
    have h1 : ∫ s in (-c / 2)..(c / 2), h s₀ ≤ ∫ s in (-c / 2)..(c / 2), h s :=
      intervalIntegral.integral_mono_on hle intervalIntegrable_const
        (hhc.intervalIntegrable _ _) fun s hs => hmin hs
    have hcc : c / 2 - -c / 2 = c := by ring
    rw [intervalIntegral.integral_const, hcc, smul_eq_mul] at h1
    rw [le_inv_mul_iff₀ hc]
    exact h1
  -- the fundamental theorem of calculus between `s₀` and `q'`
  have hftc : h q' - h s₀ = ∫ s in s₀..q', h' s :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hhd s)
      (hh'c.intervalIntegrable _ _)).symm
  have hpt : ∀ s, ‖h' s‖ ≤ c⁻¹ * ‖g s‖ ^ 2 + c * ‖deriv g s‖ ^ 2 := by
    intro s
    have hin : |inner ℝ (g s) (deriv g s)| ≤ ‖g s‖ * ‖deriv g s‖ :=
      abs_real_inner_le_norm _ _
    have hab : 2 * (‖g s‖ * ‖deriv g s‖) ≤ c⁻¹ * ‖g s‖ ^ 2 + c * ‖deriv g s‖ ^ 2 := by
      have hsq : 0 ≤ c⁻¹ * (‖g s‖ - c * ‖deriv g s‖) ^ 2 := by positivity
      have hexp : c⁻¹ * (‖g s‖ - c * ‖deriv g s‖) ^ 2 =
          c⁻¹ * ‖g s‖ ^ 2 + c * ‖deriv g s‖ ^ 2 - 2 * (‖g s‖ * ‖deriv g s‖) := by
        field_simp
        ring
      linarith
    rw [hh', Real.norm_eq_abs, abs_mul, abs_two]
    linarith
  have hsub : uIoc s₀ q' ⊆ uIoc (-c / 2) (c / 2) := by
    rw [uIoc_of_le hle]
    intro x hx
    rw [mem_uIoc] at hx
    rcases hx with hx | hx
    · exact ⟨lt_of_le_of_lt hs₀.1 hx.1, hx.2.trans hq'I.2⟩
    · exact ⟨lt_of_le_of_lt hq'I.1 hx.1, hx.2.trans hs₀.2⟩
  have hbound : |∫ s in s₀..q', h' s| ≤ ∫ s in (-c / 2)..(c / 2), ‖h' s‖ := by
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
    refine (intervalIntegral.abs_integral_mono_interval hsub
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hh'c.norm.intervalIntegrable _ _)).trans_eq ?_
    exact abs_of_nonneg (intervalIntegral.integral_nonneg hle fun _ _ => norm_nonneg _)
  have hint : ∫ s in (-c / 2)..(c / 2), ‖h' s‖ ≤
      c⁻¹ * (∫ s in (-c / 2)..(c / 2), ‖g s‖ ^ 2) +
        c * ∫ s in (-c / 2)..(c / 2), ‖deriv g s‖ ^ 2 := by
    have i1 : IntervalIntegrable (fun s => ‖g s‖ ^ 2) volume (-c / 2) (c / 2) :=
      hhc.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s => ‖deriv g s‖ ^ 2) volume (-c / 2) (c / 2) :=
      (hdc.norm.pow 2).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _)]
    exact intervalIntegral.integral_mono_on hle (hh'c.norm.intervalIntegrable _ _)
      ((i1.const_mul _).add (i2.const_mul _)) fun s _ => hpt s
  have habs := le_abs_self (∫ s in s₀..q', h' s)
  calc ‖g q‖ ^ 2 = h q' := by rw [hgq]
    _ = h s₀ + ∫ s in s₀..q', h' s := by linarith
    _ ≤ c⁻¹ * (∫ s in (-c / 2)..(c / 2), ‖g s‖ ^ 2) +
          (c⁻¹ * (∫ s in (-c / 2)..(c / 2), ‖g s‖ ^ 2) +
            c * ∫ s in (-c / 2)..(c / 2), ‖deriv g s‖ ^ 2) := by
        have := hmean
        simp only [hh] at this
        linarith
    _ = _ := by ring

/-- The cylinder form of `sq_norm_le_of_periodic`: for a `C¹`, `c`-periodic `f` on the plane
and every `z = (q, η)`,
`|f(z)|² ≤ 2 c⁻¹ ∫_{-c/2}^{c/2} |f(q', η)|² dq' + c ∫_{-c/2}^{c/2} |∂_q f(q', η)|² dq'`. -/
theorem sq_norm_le_cyl {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) (z : Plane) :
    ‖f z‖ ^ 2 ≤ 2 * c⁻¹ * (∫ q in (-c / 2)..(c / 2), ‖f (q, z.2)‖ ^ 2) +
      c * ∫ q in (-c / 2)..(c / 2), ‖partialQ f (q, z.2)‖ ^ 2 := by
  have hg : ContDiff ℝ 1 (fun q : ℝ => f (q, z.2)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  have hp : Function.Periodic (fun q : ℝ => f (q, z.2)) c := fun q => hper (q, z.2)
  exact sq_norm_le_of_periodic hc hg hp z.1

/-- **CY04 `sq_sup_q_le`** (B0183, tex 2826-2832): for a `C¹`, `c`-periodic `f` and every
height `η`, `(sup_q |f(q,η)|)² ≤ 2 c⁻¹ ∫_{-c/2}^{c/2} |f(q,η)|² dq
+ c ∫_{-c/2}^{c/2} |∂_q f(q,η)|² dq`. -/
theorem sq_sup_q_le {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) (η : ℝ) :
    (⨆ q : ℝ, ‖f (q, η)‖) ^ 2 ≤ 2 * c⁻¹ * (∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2) +
      c * ∫ q in (-c / 2)..(c / 2), ‖partialQ f (q, η)‖ ^ 2 := by
  set B := 2 * c⁻¹ * (∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2) +
      c * ∫ q in (-c / 2)..(c / 2), ‖partialQ f (q, η)‖ ^ 2 with hB
  have hpt : ∀ q : ℝ, ‖f (q, η)‖ ^ 2 ≤ B := fun q => sq_norm_le_cyl hc hf hper (q, η)
  have hB0 : 0 ≤ B := le_trans (sq_nonneg _) (hpt 0)
  have hsup : (⨆ q : ℝ, ‖f (q, η)‖) ≤ Real.sqrt B :=
    ciSup_le fun q => Real.le_sqrt_of_sq_le (hpt q)
  have h0 : 0 ≤ ⨆ q : ℝ, ‖f (q, η)‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  calc (⨆ q : ℝ, ‖f (q, η)‖) ^ 2 ≤ Real.sqrt B ^ 2 := pow_le_pow_left₀ h0 hsup 2
    _ = B := Real.sq_sqrt hB0

end UnforcedLeray.Cyl
