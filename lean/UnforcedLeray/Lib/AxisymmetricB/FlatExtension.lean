import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.CompletePartialOrder

/-!
# AX07 (flat extension): fields flat at the axis extend by zero to `C^k` fields on `ℝ³`


§5 Layer 3, target AX07 (`contDiff_flat_extension`), §2.5 "(axis argument)". Blueprint unit
served: B0195 (`eq:st18-t00197`, tex 2969–2992), the clause at tex 2983–2986: "The
`q`-dependent pieces are flat to every finite order: their decay is
`exp(−κνtR²/(c²r²))`, and differentiation of `q = R log(r/R)` costs only powers of `r⁻¹`."

* `continuous_of_tendsto_axis`, `hasFDerivAt_zero_of_tendsto_axis`: a function vanishing on
  the axis, continuous (resp. differentiable) off it, whose values (resp. first derivatives)
  tend to `0` at the axis, is continuous (resp. has derivative `0` on the axis). The second
  is the mean value inequality along the segment from the axis point, which meets the axis
  only at its end (`add_smul_sub_not_mem_axis`).
* `contDiff_of_tendsto_axis` (induction on `k`): if `g = 0` on the axis, `g ∈ C^k` off the
  axis and `‖D^n g‖ → 0` at every axis point for `n ≤ k`, then `g ∈ C^k(ℝ³)`.
* `contDiff_flat_extension` (**AX07**): if `f ∈ C^k` off the axis and, near the axis
  (`ϱ < 1`), `‖D^n f‖ ≤ C_n ϱ^{-N_n} exp(−κ/ϱ²)` for `n ≤ k`, then the extension of `f` by `0`
  on the axis is `C^k` on `ℝ³`.

The hypotheses are only required near the axis and for the finitely many orders `n ≤ k`.
Junk values: the extension `extendByZeroOnAxis f` takes the value `0` on the axis by
definition; off the axis it is `f`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

universe u

namespace UnforcedLeray.Axi

/-- The segment from a point `y` off the axis to an axis point `y₀` meets the axis only at
`y₀`. -/
theorem add_smul_sub_not_mem_axis {y₀ y : Space} (hy₀ : y₀ ∈ axis) (hy : y ∉ axis) {t : ℝ}
    (ht : t ≠ 1) : y + t • (y₀ - y) ∉ axis := by
  intro h
  apply hy
  obtain ⟨h0, h1⟩ := h
  obtain ⟨a0, a1⟩ := hy₀
  have hne : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have e0 : (y + t • (y₀ - y)) 0 = y 0 + t * (y₀ 0 - y 0) := rfl
  have e1 : (y + t • (y₀ - y)) 1 = y 1 + t * (y₀ 1 - y 1) := rfl
  rw [e0, a0] at h0
  rw [e1, a1] at h1
  constructor
  · have : (1 - t) * y 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.1 this).resolve_left hne
  · have : (1 - t) * y 1 = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left hne

section General

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- Continuity across the axis. -/
theorem continuous_of_tendsto_axis {g : Space → F} (h0 : ∀ y ∈ axis, g y = 0)
    (hc : ContinuousOn g axisᶜ) (ht : ∀ y₀ ∈ axis, Tendsto g (𝓝[axisᶜ] y₀) (𝓝 0)) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ axis
  · rw [ContinuousAt, h0 y hy]
    have h1 : Tendsto g (𝓝[axis] y) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => (h0 z hz).symm)
    have h2 := h1.sup (ht y hy)
    rwa [← nhdsWithin_union, union_compl_self, nhdsWithin_univ] at h2
  · exact hc.continuousAt (isOpen_compl_axis.mem_nhds hy)

/-- The derivative on the axis vanishes when the derivative tends to `0` at the axis (mean value
inequality along the segment from the axis point). -/
theorem hasFDerivAt_zero_of_tendsto_axis {g : Space → F} (hcont : Continuous g)
    (h0 : ∀ y ∈ axis, g y = 0) (hd : DifferentiableOn ℝ g axisᶜ) {y₀ : Space}
    (ht : Tendsto (fun y => ‖fderiv ℝ g y‖) (𝓝[axisᶜ] y₀) (𝓝 0)) (hy₀ : y₀ ∈ axis) :
    HasFDerivAt g (0 : Space →L[ℝ] F) y₀ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hev : ∀ᶠ z in 𝓝[axisᶜ] y₀, ‖fderiv ℝ g z‖ ≤ ε :=
    ((tendsto_order.1 ht).2 ε hε).mono fun z hz => hz.le
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun y hy => ?_⟩
  simp only [h0 y₀ hy₀, sub_zero, zero_apply]
  by_cases hya : y ∈ axis
  · rw [h0 y hya, norm_zero]
    positivity
  · set φ : ℝ → F := fun t => g (y + t • (y₀ - y)) with hφ
    have hline : Continuous fun t : ℝ => y + t • (y₀ - y) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hφc : ContinuousOn φ (Icc 0 1) := (hcont.comp hline).continuousOn
    have hφd : ∀ t ∈ Ico (0 : ℝ) 1,
        HasDerivWithinAt φ (fderiv ℝ g (y + t • (y₀ - y)) (y₀ - y)) (Ici t) t := by
      intro t ht
      have hz : y + t • (y₀ - y) ∉ axis := add_smul_sub_not_mem_axis hy₀ hya (ne_of_lt ht.2)
      have hgd : HasFDerivAt g (fderiv ℝ g (y + t • (y₀ - y))) (y + t • (y₀ - y)) :=
        (hd.differentiableAt (isOpen_compl_axis.mem_nhds hz)).hasFDerivAt
      have hl : HasDerivAt (fun t : ℝ => y + t • (y₀ - y)) (y₀ - y) t := by
        simpa using ((hasDerivAt_id t).smul_const (y₀ - y)).const_add y
      exact (hgd.comp_hasDerivAt t hl).hasDerivWithinAt
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
        ‖fderiv ℝ g (y + t • (y₀ - y)) (y₀ - y)‖ ≤ ε * ‖y - y₀‖ := by
      intro t ht
      have hz : y + t • (y₀ - y) ∉ axis := add_smul_sub_not_mem_axis hy₀ hya (ne_of_lt ht.2)
      have hdist : dist (y + t • (y₀ - y)) y₀ < δ := by
        rw [dist_eq_norm]
        have e : y + t • (y₀ - y) - y₀ = (1 - t) • (y - y₀) := by
          rw [sub_smul, one_smul, smul_sub, smul_sub]
          abel
        rw [e, norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
        calc (1 - t) * ‖y - y₀‖ ≤ 1 * ‖y - y₀‖ :=
              mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
          _ = dist y y₀ := by rw [one_mul, dist_eq_norm]
          _ < δ := hy
      calc ‖fderiv ℝ g (y + t • (y₀ - y)) (y₀ - y)‖
          ≤ ‖fderiv ℝ g (y + t • (y₀ - y))‖ * ‖y₀ - y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * ‖y - y₀‖ := by
          rw [norm_sub_rev y₀ y]
          exact mul_le_mul_of_nonneg_right (hball hdist hz) (norm_nonneg _)
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd hbound 1
      ⟨zero_le_one, le_rfl⟩
    have e1 : φ 1 = 0 := by
      simp only [hφ, one_smul, add_sub_cancel]
      exact h0 y₀ hy₀
    have e0 : φ 0 = g y := by simp only [hφ, zero_smul, add_zero]
    rw [e1, e0, zero_sub, norm_neg, sub_zero, mul_one] at hmvt
    exact hmvt

end General

/-- **Smoothness across the axis.** If `g` vanishes on the axis, is `C^k` off it, and
`‖D^n g(y)‖ → 0` as `y → y₀` off the axis, for every axis point `y₀` and `n ≤ k`, then
`g ∈ C^k(ℝ³)`. -/
theorem contDiff_of_tendsto_axis : ∀ (k : ℕ) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : Space → F}, (∀ y ∈ axis, g y = 0) → ContDiffOn ℝ k g axisᶜ →
    (∀ n ≤ k, ∀ y₀ ∈ axis,
      Tendsto (fun y => ‖iteratedFDeriv ℝ n g y‖) (𝓝[axisᶜ] y₀) (𝓝 0)) →
    ContDiff ℝ k g := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g h0 hc ht
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_tendsto_axis h0 (hc.continuousOn) fun y₀ hy₀ => ?_
    have := ht 0 le_rfl y₀ hy₀
    simp only [norm_iteratedFDeriv_zero] at this
    exact tendsto_zero_iff_norm_tendsto_zero.2 this
  | succ k ih =>
    intro F _ _ g h0 hc ht
    have hcont : Continuous g := by
      refine continuous_of_tendsto_axis h0 hc.continuousOn fun y₀ hy₀ => ?_
      have := ht 0 (Nat.zero_le _) y₀ hy₀
      simp only [norm_iteratedFDeriv_zero] at this
      exact tendsto_zero_iff_norm_tendsto_zero.2 this
    have hdiff : DifferentiableOn ℝ g axisᶜ := hc.differentiableOn (by simp)
    have hfd0 : ∀ y₀ ∈ axis, HasFDerivAt g (0 : Space →L[ℝ] F) y₀ := by
      intro y₀ hy₀
      refine hasFDerivAt_zero_of_tendsto_axis hcont h0 hdiff ?_ hy₀
      have := ht 1 (by omega) y₀ hy₀
      simpa only [norm_iteratedFDeriv_one] using this
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fderiv ℝ g, ?_, fun x => ?_⟩
    · refine ih (g := fderiv ℝ g) (fun y hy => (hfd0 y hy).fderiv) ?_ ?_
      · exact hc.fderiv_of_isOpen isOpen_compl_axis (by rw [hcast])
      · intro n hn y₀ hy₀
        have := ht (n + 1) (by omega) y₀ hy₀
        simpa only [norm_iteratedFDeriv_fderiv] using this
    · by_cases hx : x ∈ axis
      · rw [(hfd0 x hx).fderiv]
        exact hfd0 x hx
      · exact (hdiff.differentiableAt (isOpen_compl_axis.mem_nhds hx)).hasFDerivAt

section Flat

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
/-- The extension of `f` by `0` on the axis. -/
def extendByZeroOnAxis (f : Space → F) (y : Space) : F := if y ∈ axis then 0 else f y

omit [NormedSpace ℝ F] in
theorem extendByZeroOnAxis_of_mem {f : Space → F} {y : Space} (hy : y ∈ axis) :
    extendByZeroOnAxis f y = 0 := by
  simp [extendByZeroOnAxis, hy]

omit [NormedSpace ℝ F] in
theorem extendByZeroOnAxis_of_not_mem {f : Space → F} {y : Space} (hy : y ∉ axis) :
    extendByZeroOnAxis f y = f y := by
  simp [extendByZeroOnAxis, hy]

/-- `t^{-N} exp(−κ/t²) ≤ (N+1)! κ^{-(N+1)} t^{N+2}` for `t, κ > 0`. -/
theorem inv_pow_mul_exp_le {t κ : ℝ} (ht : 0 < t) (hκ : 0 < κ) (N : ℕ) :
    (t ^ N)⁻¹ * Real.exp (-κ / t ^ 2) ≤ (N + 1).factorial / κ ^ (N + 1) * t ^ (N + 2) := by
  set x := κ / t ^ 2 with hx
  have hx0 : 0 < x := by positivity
  have hexp : x ^ (N + 1) / (N + 1).factorial ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp x hx0.le (N + 1)
  have hpos : 0 < x ^ (N + 1) / (N + 1).factorial := by positivity
  have hinv : Real.exp (-x) ≤ (N + 1).factorial / x ^ (N + 1) := by
    rw [Real.exp_neg]
    calc (Real.exp x)⁻¹ ≤ (x ^ (N + 1) / (N + 1).factorial)⁻¹ := inv_anti₀ hpos hexp
      _ = (N + 1).factorial / x ^ (N + 1) := by rw [inv_div]
  have e : -κ / t ^ 2 = -x := by rw [hx, neg_div]
  rw [e]
  calc (t ^ N)⁻¹ * Real.exp (-x) ≤ (t ^ N)⁻¹ * ((N + 1).factorial / x ^ (N + 1)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (N + 1).factorial / κ ^ (N + 1) * t ^ (N + 2) := by
        have htN : t ^ N ≠ 0 := pow_ne_zero _ ht.ne'
        have hκN : κ ^ (N + 1) ≠ 0 := pow_ne_zero _ hκ.ne'
        have hpow : (t ^ 2) ^ (N + 1) = t ^ N * t ^ (N + 2) := by
          rw [← pow_mul, ← pow_add]
          ring_nf
        rw [hx, div_pow, hpow, div_div_eq_mul_div]
        field_simp

/-- **AX07 `contDiff_flat_extension`** (B0195, tex 2983–2986: the `q`-dependent pieces are
flat to every finite order, with decay `exp(−κ/ϱ²)` and derivatives costing powers of
`ϱ⁻¹`). If `f ∈ C^k` off the axis and `‖D^n f(y)‖ ≤ C_n ϱ^{-N_n} exp(−κ/ϱ²)` for `n ≤ k` near
the axis (`ϱ < 1`), then the extension of `f` by `0` on the axis is `C^k` on `ℝ³`. -/
theorem contDiff_flat_extension {k : ℕ} {f : Space → F} (hf : ContDiffOn ℝ k f axisᶜ)
    {κ : ℝ} (hκ : 0 < κ) (C : ℕ → ℝ) (N : ℕ → ℕ)
    (hflat : ∀ n ≤ k, ∀ y : Space, y ∉ axis → ϱ y < 1 →
      ‖iteratedFDeriv ℝ n f y‖ ≤ C n / ϱ y ^ N n * Real.exp (-κ / ϱ y ^ 2)) :
    ContDiff ℝ k (extendByZeroOnAxis f) := by
  refine contDiff_of_tendsto_axis k (fun y hy => extendByZeroOnAxis_of_mem hy)
    (hf.congr fun y hy => extendByZeroOnAxis_of_not_mem hy) ?_
  intro n hn y₀ hy₀
  have hρ0 : ϱ y₀ = 0 := (mem_axis_iff y₀).1 hy₀
  set K : ℝ := |C n| * ((N n + 1).factorial / κ ^ (N n + 1)) with hK
  -- the bound tends to `0`
  have hlim : Tendsto (fun y => K * ϱ y ^ (N n + 2)) (𝓝[axisᶜ] y₀) (𝓝 0) := by
    have hc : Continuous fun y => K * ϱ y ^ (N n + 2) := continuous_const.mul
      (continuous_ϱ.pow _)
    have := hc.tendsto y₀
    rw [hρ0, zero_pow (by omega), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ y in 𝓝[axisᶜ] y₀, ϱ y < 1 := by
    have : ∀ᶠ y in 𝓝 y₀, ϱ y < 1 :=
      continuous_ϱ.continuousAt.eventually_lt continuousAt_const (by rw [hρ0]; exact one_pos)
    exact this.filter_mono nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hlim
  filter_upwards [hnear, self_mem_nhdsWithin] with y hy1 hy
  have hy' : y ∉ axis := hy
  have hρ := ϱ_pos hy'
  have heq : iteratedFDeriv ℝ n (extendByZeroOnAxis f) y = iteratedFDeriv ℝ n f y := by
    have h : extendByZeroOnAxis f =ᶠ[𝓝 y] f := by
      filter_upwards [isOpen_compl_axis.mem_nhds hy'] with z hz
      exact extendByZeroOnAxis_of_not_mem hz
    exact (h.iteratedFDeriv ℝ n).eq_of_nhds
  rw [heq]
  calc ‖iteratedFDeriv ℝ n f y‖ ≤ C n / ϱ y ^ N n * Real.exp (-κ / ϱ y ^ 2) :=
        hflat n hn y hy' hy1
    _ ≤ |C n| * ((ϱ y ^ N n)⁻¹ * Real.exp (-κ / ϱ y ^ 2)) := by
        rw [div_eq_mul_inv, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C n| * ((N n + 1).factorial / κ ^ (N n + 1) * ϱ y ^ (N n + 2)) :=
        mul_le_mul_of_nonneg_left (inv_pow_mul_exp_le hρ hκ (N n)) (abs_nonneg _)
    _ = K * ϱ y ^ (N n + 2) := by rw [hK]; ring

end Flat

end UnforcedLeray.Axi
