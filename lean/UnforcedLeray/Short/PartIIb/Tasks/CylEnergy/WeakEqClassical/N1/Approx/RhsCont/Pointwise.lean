import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_3

/-!


Source: `the November 2 reference manuscript`
(SP 2074-2105). Fix `r ∈ (t₀,t₁)` and write `w = ω r`. For separated sums the integrand of
`cylTdInner` is a finite sum of pieces integrable by `IsFreeCylFlow.integrable`; the limit integrand
is the pointwise limit (from `CylTdConv` with `N = 0`) and is dominated by the integrable bound
`|ω F_{n₁}| + 2C|ω|`, so dominated convergence applies. No separate measurability of the train
velocity is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

theorem cylPt_integrable_jb_neg {m : ℝ} (hm : 1 < m) :
    Integrable (fun x : B0579.Plane => B0579.jb x ^ (-m)) volume := by
  have h1 : Integrable (fun t : ℝ => ((1 : ℝ) + ‖t‖ ^ 2) ^ (-m / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hm)
  have h2 : Integrable (fun z : ℝ × ℝ =>
      ((1 : ℝ) + ‖z.1‖ ^ 2) ^ (-m / 2) * ((1 : ℝ) + ‖z.2‖ ^ 2) ^ (-m / 2))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact h1.mul_prod h1
  refine Integrable.mono' h2 (B0579.continuous_jb_rpow _).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
  simp only [Real.norm_eq_abs, sq_abs]
  have hsplit : B0579.jb x ^ (-m) = B0579.jb x ^ (-m / 2) * B0579.jb x ^ (-m / 2) := by
    rw [B0579.jb_rpow_mul]
    congr 1
    ring
  rw [hsplit]
  have ha : B0579.jb x ^ (-m / 2) ≤ ((1 : ℝ) + x.1 ^ 2) ^ (-m / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by unfold B0579.jb; linarith [sq_nonneg x.2])
      (by linarith)
  have hb : B0579.jb x ^ (-m / 2) ≤ ((1 : ℝ) + x.2 ^ 2) ^ (-m / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by unfold B0579.jb; linarith [sq_nonneg x.1])
      (by linarith)
  exact mul_le_mul ha hb (Real.rpow_nonneg (B0579.jb_pos x).le _) (Real.rpow_nonneg (by positivity) _)

theorem cylPt_memLp_jb {m : ℝ} (hm : 1 < m) (c : ℝ) :
    MemLp (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2)) 2 (volume.restrict (B0579.cell c)) := by
  have hae : AEStronglyMeasurable (fun x : B0579.Plane => B0579.jb x ^ ((-m) / 2))
      (volume.restrict (B0579.cell c)) :=
    (B0579.continuous_jb_rpow _).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  refine (cylPt_integrable_jb_neg hm).restrict.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _), ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  congr 1
  push_cast
  ring

/-- A weight-`m` `L²` function is integrable on the cell (Hölder against `⟨x⟩^{-m}`), `m > 1`. -/
theorem cylPt_integrable_w {m c : ℝ} (hm : 1 < m) {w : B0579.Plane → ℝ}
    (hw : MemLp w 2 (B0579.cellMeasure c m)) : IntegrableOn w (B0579.cell c) := by
  have hA := (B0579.memLp_cellMeasure_iff c m).1 hw
  have h := hA.integrable_mul (cylPt_memLp_jb hm c)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  have hj : B0579.jb x ^ (m / 2) * B0579.jb x ^ ((-m) / 2) = 1 := by
    rw [B0579.jb_rpow_mul, ← Real.rpow_zero (B0579.jb x)]
    congr 1
    ring
  rw [B0579.bracket_rpow]
  linear_combination (w x) * hj

theorem cylPt_pd_sum {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, Differentiable ℝ (ψ k)) (j : Fin 2) :
    B0579.pd j (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd j (ψ k) y := by
  funext x
  simp only [B0579.pd]
  rw [fderiv_fun_sum (A := fun k y => a k * ψ k y) (fun k _ => (hψ k x).const_mul (a k))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_const_mul (hψ k x), ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem cylPt_lapP_sum {c : ℝ} {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, B0579.IsCylTest c (ψ k)) (x : B0579.Plane) :
    lapP (fun y => ∑ k, a k * ψ k y) x = ∑ k, a k * lapP (ψ k) x := by
  have D : ∀ k, Differentiable ℝ (ψ k) := fun k => (hψ k).differentiable
  have D0 : ∀ k, Differentiable ℝ (B0579.pd 0 (ψ k)) := fun k => ((hψ k).pd 0).differentiable
  have D1 : ∀ k, Differentiable ℝ (B0579.pd 1 (ψ k)) := fun k => ((hψ k).pd 1).differentiable
  have e0 : B0579.pd 0 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 0 (ψ k) y :=
    cylPt_pd_sum a ψ D 0
  have e1 : B0579.pd 1 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 1 (ψ k) y :=
    cylPt_pd_sum a ψ D 1
  have f00 : B0579.pd 0 (fun y => ∑ k, a k * B0579.pd 0 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 0 (B0579.pd 0 (ψ k)) y :=
    cylPt_pd_sum a (fun k => B0579.pd 0 (ψ k)) D0 0
  have f11 : B0579.pd 1 (fun y => ∑ k, a k * B0579.pd 1 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 1 (B0579.pd 1 (ψ k)) y :=
    cylPt_pd_sum a (fun k => B0579.pd 1 (ψ k)) D1 1
  simp only [lapP]
  rw [e0, e1, f00, f11]
  dsimp only
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cylPt_deriv_sum {n : ℕ} (χ : Fin n → ℝ → ℝ) (ψ : Fin n → B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) (hd : ∀ k, DifferentiableAt ℝ (χ k) r) (g : ℝ → B0579.Plane → ℝ)
    (hg : ∀ r' y, g r' y = ∑ k, χ k r' * ψ k y) :
    deriv (fun r' => g r' x) r = ∑ k, deriv (χ k) r * ψ k x := by
  have hfun : (fun r' => g r' x) = fun r' => ∑ k, χ k r' * ψ k x :=
    funext fun r' => hg r' x
  rw [hfun]
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum (A := fun k r' => χ k r' * ψ k x)
    (A' := fun k => deriv (χ k) r * ψ k x)
  intro k _
  exact (hd k).hasDerivAt.mul_const (ψ k x)

theorem cylPt_integrableOn_test {m c : ℝ} {g ψ : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => g x * ψ x) (B0579.cell c) := by
  have h := B0579.integrableOn_mul_neg c m (hg.toLp g) (B0579.testLp c (-m) hψ)
  refine Integrable.congr h ?_
  filter_upwards [(B0579.ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hg),
    B0579.coeFn_testLp c (-m) hψ] with x h1 h2
  simp only [h1, h2]

theorem cylPt_abs_le_of_close {a b c C : ℝ} (h1 : |a - b| ≤ C) (h2 : |c - b| ≤ C) :
    |a| ≤ |c| + 2 * C := by
  have h3 := abs_sub_abs_le_abs_sub a c
  have h4 := abs_sub_le a b c
  rw [abs_sub_comm b c] at h4
  linarith

/-- The integrand of the inner integral `cylTdInner` at age `r`, before multiplying by `ω r x`. -/
def cylPtIntegrand {ν c : ℝ} (tr : B0140.TrainSol ν c) (r : ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (x : B0579.Plane) : ℝ :=
  deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
    (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Short.IIb in
theorem cylTdRhsPointwise : UnforcedLeray.Short.IIb.CylTdRhsPointwise := by
  intro m ν c tr t₀ f ω t₁ φ φs M H r hr
  obtain ⟨hm, -, hfl, -, -, hsep, hconv, hM⟩ := H
  have hm1 : 1 < m := by linarith
  have hrI : r ∈ Icc t₀ t₁ := Ioo_subset_Icc_self hr
  have hwX : MemLp (ω r) 2 (B0579.cellMeasure c m) := hfl.memX r hr.1.le
  have hwI : IntegrableOn (ω r) (B0579.cell c) := cylPt_integrable_w hm1 hwX
  have hM0 : 0 ≤ M := le_trans (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hM r hrI 0)
  have hC : 0 < 1 + |ν| + M := by have := abs_nonneg ν; linarith
  -- pointwise closeness of the integrands, uniform in the plane
  have hKey : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x : B0579.Plane,
      |cylPtIntegrand tr r (φs n) x - cylPtIntegrand tr r φ x| ≤ (1 + |ν| + M) * ε := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hconv 0 ε hε
    refine ⟨n₀, fun n hn x => ?_⟩
    obtain ⟨hA, hB⟩ := hn₀ n hn
    have hA' := hA r hrI x
    have hB' := hB r hr x
    rw [Real.rpow_zero, mul_one] at hA' hB'
    have hp0 : |B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x| ≤ ε := by
      linarith [abs_nonneg (φs n r x - φ r x), abs_nonneg (B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x),
        abs_nonneg (lapP (φs n r) x - lapP (φ r) x)]
    have hp1 : |B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x| ≤ ε := by
      linarith [abs_nonneg (φs n r x - φ r x), abs_nonneg (B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x),
        abs_nonneg (lapP (φs n r) x - lapP (φ r) x)]
    have hl : |lapP (φs n r) x - lapP (φ r) x| ≤ ε := by
      linarith [abs_nonneg (φs n r x - φ r x), abs_nonneg (B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x),
        abs_nonneg (B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x)]
    have hsplit : cylPtIntegrand tr r (φs n) x - cylPtIntegrand tr r φ x =
        (deriv (fun r' => φs n r' x) r - deriv (fun r' => φ r' x) r) +
          ν * (lapP (φs n r) x - lapP (φ r) x) +
          (tr.v r x 0 * (B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x) +
            tr.v r x 1 * (B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x)) := by
      unfold cylPtIntegrand
      ring
    rw [hsplit]
    have hv := hM r hrI x
    have t2 : |ν * (lapP (φs n r) x - lapP (φ r) x)| ≤ |ν| * ε := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
    have t3 : |tr.v r x 0 * (B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x) +
        tr.v r x 1 * (B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x)| ≤
        |tr.v r x 0| * ε + |tr.v r x 1| * ε := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hp0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hp1 (abs_nonneg _))
    have t5 : |tr.v r x 0| * ε + |tr.v r x 1| * ε ≤ M * ε := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hv hε.le
    have t6 : (1 + |ν| + M) * ε = ε + |ν| * ε + M * ε := by ring
    rw [t6]
    have t7 := abs_add_three (deriv (fun r' => φs n r' x) r - deriv (fun r' => φ r' x) r)
      (ν * (lapP (φs n r) x - lapP (φ r) x))
      (tr.v r x 0 * (B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x) +
        tr.v r x 1 * (B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x))
    linarith
  -- pointwise convergence of the integrands
  have hlim : ∀ x, Tendsto (fun n => cylPtIntegrand tr r (φs n) x) atTop
      (𝓝 (cylPtIntegrand tr r φ x)) := by
    intro x
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨n₀, hn₀⟩ := hKey (δ / (2 * (1 + |ν| + M))) (div_pos hδ (by linarith))
    refine ⟨n₀, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hn₀ n hn x
    have h2 : (1 + |ν| + M) * (δ / (2 * (1 + |ν| + M))) = δ / 2 := by
      field_simp
    linarith
  -- each inner integrand is integrable against `ω r` (separated sums, `IsFreeCylFlow.integrable`)
  have hGint : ∀ n, IntegrableOn (fun x => ω r x * cylPtIntegrand tr r (φs n) x) (B0579.cell c) := by
    intro n
    obtain ⟨N, χ, ψ, hχ, hψ, hsum⟩ := hsep n
    have hd : ∀ k, DifferentiableAt ℝ (χ k) r := fun k =>
      ((hχ k).differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hr.1 hr.2)
    have hdv : ∀ x, deriv (fun r' => φs n r' x) r = ∑ k, deriv (χ k) r * ψ k x :=
      fun x => cylPt_deriv_sum χ ψ r x hd (φs n) hsum
    have hlap : ∀ x, lapP (φs n r) x = ∑ k, χ k r * lapP (ψ k) x := fun x => by
      have hfun : φs n r = fun y => ∑ k, χ k r * ψ k y := funext fun y => hsum r y
      rw [hfun]
      exact cylPt_lapP_sum (fun k => χ k r) ψ hψ x
    have hpd : ∀ j x, B0579.pd j (φs n r) x = ∑ k, χ k r * B0579.pd j (ψ k) x := fun j x => by
      have hfun : φs n r = fun y => ∑ k, χ k r * ψ k y := funext fun y => hsum r y
      rw [hfun, cylPt_pd_sum (fun k => χ k r) ψ (fun k => (hψ k).differentiable) j]
    have hint : (fun x => ω r x * cylPtIntegrand tr r (φs n) x) = fun x =>
        ∑ k, (deriv (χ k) r * (ω r x * ψ k x) + χ k r * cylFreeIntegrand tr (ω r) r (ψ k) x) := by
      funext x
      unfold cylPtIntegrand cylFreeIntegrand
      rw [hdv x, hlap x, hpd 0 x, hpd 1 x]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hint]
    exact integrable_finset_sum _ fun k _ =>
      ((cylPt_integrableOn_test hwX (hψ k)).const_mul _).add
        ((hfl.integrable (ψ k) (hψ k) r hr.1.le).const_mul _)
  -- dominated convergence in the cell integral
  obtain ⟨n₁, hn₁⟩ := hKey 1 one_pos
  show Tendsto (fun n => ∫ x in B0579.cell c, ω r x * cylPtIntegrand tr r (φs n) x) atTop
    (𝓝 (∫ x in B0579.cell c, ω r x * cylPtIntegrand tr r φ x))
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => |ω r x * cylPtIntegrand tr r (φs n₁) x| + 2 * (1 + |ν| + M) * |ω r x|) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun n => (hGint n).aestronglyMeasurable
  · refine Filter.eventually_atTop.2 ⟨n₁, fun n hn => Filter.Eventually.of_forall fun x => ?_⟩
    have hb := cylPt_abs_le_of_close (hn₁ n hn x) (hn₁ n₁ le_rfl x)
    rw [Real.norm_eq_abs]
    calc |ω r x * cylPtIntegrand tr r (φs n) x|
        = |ω r x| * |cylPtIntegrand tr r (φs n) x| := abs_mul _ _
      _ ≤ |ω r x| * (|cylPtIntegrand tr r (φs n₁) x| + 2 * ((1 + |ν| + M) * 1)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |ω r x * cylPtIntegrand tr r (φs n₁) x| + 2 * (1 + |ν| + M) * |ω r x| := by
          rw [abs_mul]
          ring
  · exact (Integrable.abs (hGint n₁)).add (Integrable.const_mul (Integrable.abs hwI) _)
  · exact Filter.Eventually.of_forall fun x => (hlim x).const_mul (ω r x)
