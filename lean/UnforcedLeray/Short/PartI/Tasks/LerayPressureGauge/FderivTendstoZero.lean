import UnforcedLeray.Short.PartI.Sub.T02_2

/-!


Source of record: `the November 2 reference manuscript`, line 447 (the Poisson
source `-tr((grad v)^2)` tends to `0` because `grad v` does).

Statement (`Short/PartI/Sub/T02_2.lean`): a `C^2` function `g` on the plane with bounded Hessian
that tends to `0` as `|z.2| -> infinity` has `||fderiv g z|| -> 0` as `|z.2| -> infinity`.

Proof outline.  Let `K := max M 1 > 0` bound the Hessian.  Fix `eps > 0` and put
`r := eps / (4 K)`, so `K r = eps / 4`.  Let `delta := eps r / 4`, and let `R0` be such that
`|g w| < delta` for `|w.2| >= R0`.  For a unit vector `e` and `z` with `|z.2| >= R0 + r`, the
points `z +- r e` lie in `{|w.2| >= R0}`, and second-order Taylor along the line `t -> z + t e`
gives `|g(z + r e) - g(z - r e) - 2 r (fderiv g z e)| <= 2 K r^2`.  Hence
`|fderiv g z e| <= delta / r + K r = eps / 2`.  The operator norm is the supremum over unit
vectors, so `||fderiv g z|| <= eps / 2 < eps`.
-/

set_option autoImplicit false

open Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The filter `comap (fun z => |z.2|) atTop` written in `epsilon`-`R` form. -/
lemma fdtz_tendsto_iff (f : Plane → ℝ) :
    Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) ↔
      ∀ ε > 0, ∃ R : ℝ, ∀ z : Plane, R ≤ |z.2| → |f z| < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have h' := h ε hε
    rw [Filter.eventually_comap, Filter.eventually_atTop] at h'
    obtain ⟨R, hR⟩ := h'
    exact ⟨R, fun z hz => by simpa [Real.dist_eq] using hR (|z.2|) hz z rfl⟩
  · intro h ε hε
    obtain ⟨R, hR⟩ := h ε hε
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨R, fun a ha z hz => ?_⟩
    subst hz
    simpa [Real.dist_eq] using hR z ha

/-- A linear functional on the plane whose values on unit vectors are at most `c` has norm at
most `c`. -/
lemma fdtz_opNorm_le_of_unit (L : Plane →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ e : Plane, ‖e‖ = 1 → ‖L e‖ ≤ c) : ‖L‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound L hc
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have he : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have h1 := h _ he
    rw [map_smul, norm_smul, norm_inv, norm_norm] at h1
    calc ‖L x‖ = ‖x‖ * (‖x‖⁻¹ * ‖L x‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      _ ≤ ‖x‖ * c := mul_le_mul_of_nonneg_left h1 hpos.le
      _ = c * ‖x‖ := mul_comm _ _

/-- Second-order Taylor estimate along a unit direction `x`: the second difference
`g(z + r x) - g(z - r x)` equals `2 r (fderiv g z x)` up to `2 K r^2`, where `K` bounds the
Hessian. -/
lemma fdtz_line (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (K : ℝ)
    (hK : ∀ y : Plane, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ K) (z x : Plane) (hx : ‖x‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    |g (z + r • x) - g (z + (-r) • x) - 2 * r * fderiv ℝ g z x| ≤ 2 * K * r ^ 2 := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ g) z)) (hK z)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ g) := hD.differentiable (by norm_num)
  -- the line `t ↦ z + t • x`
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • x) x t := by
    intro t
    have h := ((hasDerivAt_id' t).smul_const x).const_add z
    simpa using h
  -- derivative of `t ↦ g (z + t • x)`
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => g (z + s • x)) (fderiv ℝ g (z + t • x) x) t := by
    intro t
    exact (hgd (z + t • x)).hasFDerivAt.comp_hasDerivAt (x := t) (hline t)
  -- derivative of `t ↦ fderiv g (z + t • x)`
  have hc : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ g (z + s • x))
      (fderiv ℝ (fderiv ℝ g) (z + t • x) x) t := by
    intro t
    exact (hDd (z + t • x)).hasFDerivAt.comp_hasDerivAt (x := t) (hline t)
  -- derivative of `t ↦ fderiv g (z + t • x) x`
  have ha' : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ g (z + s • x) x)
      (fderiv ℝ (fderiv ℝ g) (z + t • x) x x) t := by
    intro t
    have h := (hc t).clm_apply (hasDerivAt_const t x)
    simpa using h
  -- the second derivative in the direction `x` is bounded by `K`
  have hb : ∀ t : ℝ, ‖fderiv ℝ (fderiv ℝ g) (z + t • x) x x‖ ≤ K := by
    intro t
    have h1 := (fderiv ℝ (fderiv ℝ g) (z + t • x)).le_opNorm x
    have h2 := ((fderiv ℝ (fderiv ℝ g) (z + t • x)) x).le_opNorm x
    have h3 := hK (z + t • x)
    simp only [hx, mul_one] at h1 h2
    linarith
  -- Lipschitz bound on the derivative along the line
  have hlip : ∀ t : ℝ, ‖fderiv ℝ g (z + t • x) x - fderiv ℝ g z x‖ ≤ K * |t| := by
    intro t
    have h0 : fderiv ℝ g z x = fderiv ℝ g (z + (0:ℝ) • x) x := by simp
    rw [h0]
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => fderiv ℝ g (z + s • x) x)
      (f' := fun s : ℝ => fderiv ℝ (fderiv ℝ g) (z + s • x) x x)
      (s := univ) (x := 0) (y := t) (C := K)
      (fun s _ => (ha' s).hasDerivWithinAt) (fun s _ => hb s) convex_univ
      (mem_univ _) (mem_univ _)
    simpa [Real.norm_eq_abs] using h
  -- the function `F s := g (z + s x) - s (fderiv g z x)` has derivative `a s - a 0`
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => g (z + s • x) - s * fderiv ℝ g z x)
      (fderiv ℝ g (z + t • x) x - fderiv ℝ g z x) t := by
    intro t
    exact ((hφ t).sub ((hasDerivAt_id' t).mul_const (fderiv ℝ g z x))).congr_deriv (by ring)
  -- one-sided estimate on `[0, r]`
  have hpos : ‖g (z + r • x) - r * fderiv ℝ g z x - g z‖ ≤ K * r * r := by
    have hbd : ∀ t ∈ Ico (0:ℝ) r, ‖fderiv ℝ g (z + t • x) x - fderiv ℝ g z x‖ ≤ K * r := by
      intro t ht
      have ht' : |t| ≤ r := by
        rw [abs_of_nonneg ht.1]
        exact ht.2.le
      exact (hlip t).trans (mul_le_mul_of_nonneg_left ht' hK0)
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s : ℝ => g (z + s • x) - s * fderiv ℝ g z x)
      (f' := fun t : ℝ => fderiv ℝ g (z + t • x) x - fderiv ℝ g z x)
      (a := 0) (b := r) (C := K * r)
      (fun t _ => (hF t).hasDerivWithinAt) hbd r ⟨hr.le, le_rfl⟩
    simp only [zero_smul, add_zero, zero_mul, sub_zero] at key
    exact key
  -- one-sided estimate on `[-r, 0]`
  have hneg : ‖g z - (g (z + (-r) • x) - (-r) * fderiv ℝ g z x)‖ ≤ K * r * (0 - -r) := by
    have hbd : ∀ t ∈ Ico (-r) 0, ‖fderiv ℝ g (z + t • x) x - fderiv ℝ g z x‖ ≤ K * r := by
      intro t ht
      have ht' : |t| ≤ r := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      exact (hlip t).trans (mul_le_mul_of_nonneg_left ht' hK0)
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s : ℝ => g (z + s • x) - s * fderiv ℝ g z x)
      (f' := fun t : ℝ => fderiv ℝ g (z + t • x) x - fderiv ℝ g z x)
      (a := -r) (b := 0) (C := K * r)
      (fun t _ => (hF t).hasDerivWithinAt) hbd 0 ⟨by linarith, le_rfl⟩
    simp only [zero_smul, add_zero, zero_mul, sub_zero] at key
    exact key
  have hsplit : g (z + r • x) - g (z + (-r) • x) - 2 * r * fderiv ℝ g z x
      = (g (z + r • x) - r * fderiv ℝ g z x - g z)
        + (g z - (g (z + (-r) • x) - (-r) * fderiv ℝ g z x)) := by
    ring
  rw [← Real.norm_eq_abs, hsplit]
  calc ‖(g (z + r • x) - r * fderiv ℝ g z x - g z)
        + (g z - (g (z + (-r) • x) - (-r) * fderiv ℝ g z x))‖
      ≤ ‖g (z + r • x) - r * fderiv ℝ g z x - g z‖
        + ‖g z - (g (z + (-r) • x) - (-r) * fderiv ℝ g z x)‖ := norm_add_le _ _
    _ ≤ K * r * r + K * r * (0 - -r) := add_le_add hpos hneg
    _ = 2 * K * r ^ 2 := by ring

/-- Unit-vector estimate: on the region `|z.2| >= R0 + r`, where `g` is below `eps r / 4`
on `|w.2| >= R0`, the derivative in a unit direction is at most `eps / 2`. -/
lemma fdtz_unit (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (K : ℝ)
    (hK : ∀ y : Plane, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ K) (ε : ℝ)
    (r : ℝ) (hr : 0 < r) (hKr : K * r = ε / 4)
    (R0 : ℝ) (hR0 : ∀ w : Plane, R0 ≤ |w.2| → |g w| < ε * r / 4)
    (z : Plane) (hz : R0 + r ≤ |z.2|) (e : Plane) (he : ‖e‖ = 1) :
    ‖fderiv ℝ g z e‖ ≤ ε / 2 := by
  have he2 : |e.2| ≤ 1 := by
    have h := norm_snd_le e
    rw [he, Real.norm_eq_abs] at h
    exact h
  have hreg : ∀ s : ℝ, |s| ≤ r → R0 ≤ |(z + s • e).2| := by
    intro s hs
    have h2 : |s * e.2| ≤ r := by
      rw [abs_mul]
      calc |s| * |e.2| ≤ |s| * 1 := mul_le_mul_of_nonneg_left he2 (abs_nonneg s)
        _ ≤ r := by linarith
    have h4 : z.2 = (z.2 + s * e.2) + -(s * e.2) := by ring
    have h3 : |z.2| ≤ |z.2 + s * e.2| + |s * e.2| := by
      calc |z.2| = |(z.2 + s * e.2) + -(s * e.2)| := by rw [← h4]
        _ ≤ |z.2 + s * e.2| + |-(s * e.2)| := abs_add_le _ _
        _ = |z.2 + s * e.2| + |s * e.2| := by rw [abs_neg]
    have h5 : (z + s • e).2 = z.2 + s * e.2 := by simp
    rw [h5]
    linarith
  have hP : |g (z + r • e)| < ε * r / 4 :=
    hR0 _ (hreg r (le_of_eq (abs_of_pos hr)))
  have hQ : |g (z + (-r) • e)| < ε * r / 4 :=
    hR0 _ (hreg (-r) (by rw [abs_neg]; exact le_of_eq (abs_of_pos hr)))
  have hL := fdtz_line g hg K hK z e he hr
  have hA := abs_le.mp hL
  have hP' := abs_lt.mp hP
  have hQ' := abs_lt.mp hQ
  have hKr2 : K * r ^ 2 = r * ε / 4 := by
    have h : K * r ^ 2 = (K * r) * r := by ring
    rw [h, hKr]
    ring
  have hup : 2 * fderiv ℝ g z e ≤ ε := by
    have h : r * (2 * fderiv ℝ g z e) ≤ r * ε := by
      linarith [hA.1, hA.2, hP'.1, hP'.2, hQ'.1, hQ'.2, hKr2]
    exact le_of_mul_le_mul_left h hr
  have hlo : -ε ≤ 2 * fderiv ℝ g z e := by
    have h : r * (-ε) ≤ r * (2 * fderiv ℝ g z e) := by
      linarith [hA.1, hA.2, hP'.1, hP'.2, hQ'.1, hQ'.2, hKr2]
    exact le_of_mul_le_mul_left h hr
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **Interpolation** (task `PartI:T02/2`): a `C^2` function with bounded Hessian that tends to
`0` as `|z.2| -> infinity` has gradient tending to `0` as `|z.2| -> infinity`. -/
theorem fderivTendstoZero : FderivTendstoZero := by
  unfold FderivTendstoZero
  intro g hg hbd hlim
  obtain ⟨M, hM⟩ := hbd
  have hK : ∀ y : Plane, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ max M 1 := by
    intro y
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := y) (n := 1)
    rw [norm_iteratedFDeriv_one] at h1
    rw [h1]
    exact le_trans (hM y) (le_max_left _ _)
  have hKpos : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKne : max M 1 ≠ 0 := hKpos.ne'
  refine (fdtz_tendsto_iff _).2 (fun ε hε => ?_)
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ε / (4 * max M 1) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hr_def]
    exact div_pos hε (by linarith)
  have hKr : max M 1 * r = ε / 4 := by
    rw [hr_def]
    field_simp
  obtain ⟨R0, hR0⟩ :=
    (fdtz_tendsto_iff g).1 hlim (ε * r / 4) (div_pos (mul_pos hε hr) (by norm_num))
  refine ⟨R0 + r, fun z hz => ?_⟩
  have hL := fdtz_opNorm_le_of_unit (fderiv ℝ g z) (ε / 2) (by linarith)
    (fun e he => fdtz_unit g hg (max M 1) hK ε r hr hKr R0 hR0 z hz e he)
  show |‖fderiv ℝ g z‖| < ε
  rw [abs_norm]
  linarith

end UnforcedLeray.Short.PartI
