import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_3_3
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Part II-b, task `PartII-b:G4/2/3/3/3`: termwise differentiation of the periodization

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

For `c ≥ 1` the periodization `perC c G` is a `ℤ`-indexed sum of translates `G(· + (kc,0))`.
Mathlib's `contDiff_tsum` and `iteratedFDeriv_tsum` need bounds uniform on all of `ℝ²`, which fail
(the translates are not uniformly small in `x₁`). So the argument localizes to the open strips
`S_n = {|x₁| < n}`, where the bounds `e^{-κ(x₁+kc)²} ≤ e^{κn²} e^{-(κ/2)k²}` are uniform and
summable (`perDeriv_gauss_strip_le`). On each strip we prove, by induction, that the tsum is
`C^n` together with the termwise identity for iterated derivatives, using
`hasFDerivAt_tsum_of_isPreconnected` (local version of the derivative of a series).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The Gaussian `m ↦ e^{-a m²}` is summable over `ℤ` for `a > 0`. -/
lemma perDeriv_gauss_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun m : ℤ => Real.exp (-(a * (m : ℝ) ^ 2))) := by
  have hT : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 hT 0
  refine h.congr fun m => ?_
  simp only [pow_zero, one_mul]
  congr 1
  field_simp <;> ring

/-- `(x₁ + kc)² ≥ k²/2 - n²` when `|x₁| ≤ n`, `c ≥ 1`, `n ≥ 0`. -/
lemma perDeriv_sq_shift_strip_ge (c n x₁ : ℝ) (k : ℤ) (hc : 1 ≤ c) (hn : 0 ≤ n) (hx : |x₁| ≤ n) :
    (k : ℝ) ^ 2 / 2 - n ^ 2 ≤ (x₁ + (k : ℝ) * c) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hkc : |(k : ℝ)| ≤ |(k : ℝ) * c| := by
    rw [abs_mul, abs_of_pos hc0]
    nlinarith [abs_nonneg (k : ℝ)]
  have htri : |(k : ℝ) * c| ≤ |x₁ + (k : ℝ) * c| + |x₁| := by
    have h := abs_sub (x₁ + (k : ℝ) * c) x₁
    have e : x₁ + (k : ℝ) * c - x₁ = (k : ℝ) * c := by ring
    rw [e] at h
    exact h
  have hA : |(k : ℝ)| - n ≤ |x₁ + (k : ℝ) * c| := by linarith
  have hsq : (x₁ + (k : ℝ) * c) ^ 2 = |x₁ + (k : ℝ) * c| ^ 2 := (sq_abs _).symm
  have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  rw [hsq, hk2]
  rcases le_total n |(k : ℝ)| with h | h
  · have h0 : 0 ≤ |(k : ℝ)| - n := by linarith
    nlinarith [sq_nonneg (|(k : ℝ)| - 2 * n), mul_le_mul hA hA h0 (abs_nonneg _)]
  · nlinarith [sq_nonneg |x₁ + (k : ℝ) * c|, abs_nonneg (k : ℝ)]

/-- Uniform strip bound for the Gaussian lattice terms. -/
lemma perDeriv_gauss_strip_le (κ c n x₁ : ℝ) (k : ℤ) (hκ : 0 < κ) (hc : 1 ≤ c) (hn : 0 ≤ n)
    (hx : |x₁| ≤ n) :
    Real.exp (-(κ * (x₁ + (k : ℝ) * c) ^ 2)) ≤
      Real.exp (κ * n ^ 2) * Real.exp (-((κ / 2) * (k : ℝ) ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := perDeriv_sq_shift_strip_ge c n x₁ k hc hn hx
  have h2 := mul_le_mul_of_nonneg_left h hκ.le
  nlinarith

/-- The open strip `{|x₁| < n}`. -/
def perDerivStrip (n : ℕ) : Set (ℝ × ℝ) := Prod.fst ⁻¹' Metric.ball (0 : ℝ) (n : ℝ)

lemma mem_perDerivStrip (n : ℕ) (x : ℝ × ℝ) : x ∈ perDerivStrip n ↔ |x.1| < n := by
  simp [perDerivStrip, Metric.mem_ball, Real.dist_eq]

lemma perDerivStrip_isOpen (n : ℕ) : IsOpen (perDerivStrip n) :=
  Metric.isOpen_ball.preimage continuous_fst

lemma perDerivStrip_convex (n : ℕ) : Convex ℝ (perDerivStrip n) :=
  (convex_ball (0 : ℝ) (n : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)

/-- Smoothness of a locally uniformly summable series on an open convex set, for all finite orders. -/
theorem perDeriv_contDiffOn_aux (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hUc : Convex ℝ U) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : ℤ → ℝ × ℝ → F) (v : ℕ → ℤ → ℝ),
      (∀ i, ContDiff ℝ ∞ (f i)) → (∀ k : ℕ, Summable (v k)) →
      (∀ (k : ℕ) (i : ℤ) (x : ℝ × ℝ), x ∈ U → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) →
      ContDiffOn ℝ n (fun y => ∑' i, f i y) U := by
  induction n with
  | zero =>
    intro F _ _ _ f v hf hv hb
    refine contDiffOn_zero.2 (continuousOn_tsum (fun i => (hf i).continuous.continuousOn) (hv 0) ?_)
    intro i y hy
    have h := hb 0 i y hy
    rwa [norm_iteratedFDeriv_zero] at h
  | succ n ih =>
    intro F _ _ _ f v hf hv hb
    have hb0 : ∀ i (y : ℝ × ℝ), y ∈ U → ‖f i y‖ ≤ v 0 i := by
      intro i y hy
      have h := hb 0 i y hy
      rwa [norm_iteratedFDeriv_zero] at h
    have hbd1 : ∀ i (y : ℝ × ℝ), y ∈ U → ‖fderiv ℝ (f i) y‖ ≤ v 1 i := by
      intro i y hy
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := f i) (x := y)
      simp only [norm_iteratedFDeriv_zero, zero_add] at h
      rw [h]
      exact hb 1 i y hy
    have hdiffS : ∀ y ∈ U, HasFDerivAt (fun z => ∑' i, f i z) (∑' i, fderiv ℝ (f i) y) y := by
      intro y hy
      refine hasFDerivAt_tsum_of_isPreconnected (f := f) (f' := fun i z => fderiv ℝ (f i) z)
        (hv 1) hU hUc.isPreconnected (fun i z _ => ((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt)
        (fun i z hz => hbd1 i z hz) hy (Summable.of_norm_bounded (hv 0) (fun i => hb0 i y hy)) hy
    have hfd : ∀ y ∈ U, fderiv ℝ (fun z => ∑' i, f i z) y = ∑' i, fderiv ℝ (f i) y :=
      fun y hy => (hdiffS y hy).fderiv
    have hfam : ∀ i, ContDiff ℝ ∞ (fderiv ℝ (f i)) := fun i =>
      (hf i).fderiv_right (m := ∞) (by simp)
    have hbk : ∀ (k : ℕ) (i : ℤ) (x : ℝ × ℝ), x ∈ U →
        ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (f i) y) x‖ ≤ v (k + 1) i := by
      intro k i x hx
      rw [norm_iteratedFDeriv_fderiv]
      exact hb (k + 1) i x hx
    have hcong := ih (ℝ × ℝ →L[ℝ] F) (fun i => fderiv ℝ (f i)) (fun k => v (k + 1)) hfam
      (fun k => hv (k + 1)) hbk
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun y hy => (hdiffS y hy).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hcong.congr (fun y hy => hfd y hy)

/-- Smoothness on an open convex set (all orders). -/
theorem perDeriv_contDiffOn (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hUc : Convex ℝ U)
    (f : ℤ → ℝ × ℝ → ℂ) (v : ℕ → ℤ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hv : ∀ k : ℕ, Summable (v k))
    (hb : ∀ (k : ℕ) (i : ℤ) (x : ℝ × ℝ), x ∈ U → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, f i y) U :=
  contDiffOn_infty.2 fun n => perDeriv_contDiffOn_aux U hU hUc n ℂ f v hf hv hb

/-- Local termwise identity for iterated derivatives of a series on an open convex set. -/
theorem perDeriv_iteratedFDeriv_tsum (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hUc : Convex ℝ U)
    (f : ℤ → ℝ × ℝ → ℂ) (v : ℕ → ℤ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hv : ∀ k : ℕ, Summable (v k))
    (hb : ∀ (k : ℕ) (i : ℤ) (x : ℝ × ℝ), x ∈ U → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ∀ (j : ℕ) (x : ℝ × ℝ), x ∈ U →
      iteratedFDeriv ℝ j (fun y => ∑' i, f i y) x = ∑' i, iteratedFDeriv ℝ j (f i) x := by
  intro j
  induction j with
  | zero =>
    intro x _
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) ℂ).symm.toContinuousLinearEquiv.map_tsum
  | succ j ih =>
    intro x hx
    have hEq : iteratedFDeriv ℝ j (fun y => ∑' i, f i y) =ᶠ[𝓝 x]
        fun y => ∑' i, iteratedFDeriv ℝ j (f i) y :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    have hjlt : ∀ i : ℤ, Differentiable ℝ (iteratedFDeriv ℝ j (f i)) := fun i =>
      (hf i).differentiable_iteratedFDeriv (WithTop.coe_lt_coe.2 (ENat.coe_lt_top j))
    have hdiff : HasFDerivAt (fun y => ∑' i, iteratedFDeriv ℝ j (f i) y)
        (∑' i, fderiv ℝ (iteratedFDeriv ℝ j (f i)) x) x := by
      refine hasFDerivAt_tsum_of_isPreconnected (f := fun i => iteratedFDeriv ℝ j (f i))
        (f' := fun i z => fderiv ℝ (iteratedFDeriv ℝ j (f i)) z) (hv (j + 1)) hU hUc.isPreconnected
        (fun i z _ => (hjlt i z).hasFDerivAt) ?_ hx ?_ hx
      · intro i z hz
        rw [norm_fderiv_iteratedFDeriv]
        exact hb (j + 1) i z hz
      · exact Summable.of_norm_bounded (hv j) (fun i => hb j i x hx)
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [hEq.fderiv_eq, hdiff.fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => ℝ × ℝ) ℂ).symm.toContinuousLinearEquiv.map_tsum

/-- The `c`-periodization, written as a `ℤ`-indexed sum of translates. -/
theorem perDerivTsum_aux_shift (G : ℝ × ℝ → ℂ) (j : ℕ) (a : ℝ) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ j (fun y : ℝ × ℝ => G (y.1 + a, y.2)) z =
      iteratedFDeriv ℝ j G (z.1 + a, z.2) := by
  have h1 : (fun y : ℝ × ℝ => G (y.1 + a, y.2)) = fun y => G (y + (a, 0)) := by
    funext y
    congr 1
    ext <;> simp
  rw [h1, iteratedFDeriv_comp_add_right]
  congr 1
  ext <;> simp

theorem perDerivTsum : UnforcedLeray.Short.IIb.PerDerivTsum := by
  intro G hG hbd c hc
  choose C κ hκ hCb using hbd
  have hC0 : ∀ j, 0 ≤ C j := by
    intro j
    have h := hCb j 0
    have hp : 0 < Real.exp (-(κ j * (((0 : ℝ × ℝ).1) ^ 2 + ((0 : ℝ × ℝ).2) ^ 2))) := Real.exp_pos _
    have hn := norm_nonneg (iteratedFDeriv ℝ j G 0)
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  -- smoothness of the translates
  have hfsm : ∀ (k : ℤ), ContDiff ℝ ∞ (fun y : ℝ × ℝ => G (y.1 + (k : ℝ) * c, y.2)) := by
    intro k
    exact hG.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  -- the uniform strip bound for the translates
  have hstrip : ∀ (n j : ℕ) (k : ℤ) (x : ℝ × ℝ), x ∈ perDerivStrip n →
      ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ => G (y.1 + (k : ℝ) * c, y.2)) x‖ ≤
        C j * Real.exp (κ j * (n : ℝ) ^ 2) * Real.exp (-((κ j / 2) * (k : ℝ) ^ 2)) := by
    intro n j k x hx
    have hxn : |x.1| ≤ (n : ℝ) := le_of_lt ((mem_perDerivStrip n x).1 hx)
    rw [perDerivTsum_aux_shift G j _ x]
    have h1 : ‖iteratedFDeriv ℝ j G (x.1 + (k : ℝ) * c, x.2)‖ ≤
        C j * Real.exp (-(κ j * ((x.1 + (k : ℝ) * c) ^ 2 + x.2 ^ 2))) := hCb j _
    have h2 : Real.exp (-(κ j * ((x.1 + (k : ℝ) * c) ^ 2 + x.2 ^ 2))) ≤
        Real.exp (-(κ j * (x.1 + (k : ℝ) * c) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (hκ j).le (sq_nonneg x.2)
      nlinarith
    have h3 := perDeriv_gauss_strip_le (κ j) c n x.1 k (hκ j) hc (Nat.cast_nonneg n) hxn
    have hCj := hC0 j
    calc _ ≤ C j * Real.exp (-(κ j * ((x.1 + (k : ℝ) * c) ^ 2 + x.2 ^ 2))) := h1
      _ ≤ C j * Real.exp (-(κ j * (x.1 + (k : ℝ) * c) ^ 2)) := mul_le_mul_of_nonneg_left h2 hCj
      _ ≤ C j * (Real.exp (κ j * (n : ℝ) ^ 2) * Real.exp (-((κ j / 2) * (k : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 hCj
      _ = C j * Real.exp (κ j * (n : ℝ) ^ 2) * Real.exp (-((κ j / 2) * (k : ℝ) ^ 2)) := by ring
  -- summable bounds on the strip
  have hvsum : ∀ (n j : ℕ), Summable (fun k : ℤ =>
      C j * Real.exp (κ j * (n : ℝ) ^ 2) * Real.exp (-((κ j / 2) * (k : ℝ) ^ 2))) := by
    intro n j
    exact (perDeriv_gauss_summable (κ j / 2) (by linarith [hκ j])).mul_left _
  -- the claim on each strip
  have claim : ∀ (n j : ℕ) (x : ℝ × ℝ), x ∈ perDerivStrip n →
      Summable (fun k : ℤ => ‖iteratedFDeriv ℝ j G (x.1 + (k : ℝ) * c, x.2)‖) ∧
      ‖iteratedFDeriv ℝ j (perC c G) x‖ ≤
        ∑' k : ℤ, ‖iteratedFDeriv ℝ j G (x.1 + (k : ℝ) * c, x.2)‖ := by
    intro n j x hx
    have hsumG : ∀ k : ℤ, iteratedFDeriv ℝ j (fun z : ℝ × ℝ => G (z.1 + (k : ℝ) * c, z.2)) x =
        iteratedFDeriv ℝ j G (x.1 + (k : ℝ) * c, x.2) := fun k => perDerivTsum_aux_shift G j _ x
    have hsum : Summable (fun k : ℤ =>
        ‖iteratedFDeriv ℝ j (fun z : ℝ × ℝ => G (z.1 + (k : ℝ) * c, z.2)) x‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hstrip n j k x hx) (hvsum n j)
    have hid : iteratedFDeriv ℝ j (perC c G) x = ∑' k : ℤ,
        iteratedFDeriv ℝ j (fun z : ℝ × ℝ => G (z.1 + (k : ℝ) * c, z.2)) x :=
      perDeriv_iteratedFDeriv_tsum (perDerivStrip n) (perDerivStrip_isOpen n)
        (perDerivStrip_convex n) (fun k z => G (z.1 + (k : ℝ) * c, z.2))
        (fun j' k' => C j' * Real.exp (κ j' * (n : ℝ) ^ 2) * Real.exp (-((κ j' / 2) * (k' : ℝ) ^ 2)))
        hfsm (fun j' => hvsum n j') (fun j' k y hy => hstrip n j' k y hy) j x hx
    refine ⟨?_, ?_⟩
    · simpa only [hsumG] using hsum
    · rw [hid]
      have h := norm_tsum_le_tsum_norm hsum
      simp only [hsumG] at h ⊢
      exact h
  have hcontd : ContDiff ℝ ∞ (perC c G) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x.1|
    have hx : x ∈ perDerivStrip n := (mem_perDerivStrip n x).2 hn
    have hon := perDeriv_contDiffOn (perDerivStrip n) (perDerivStrip_isOpen n)
      (perDerivStrip_convex n) (fun k z => G (z.1 + (k : ℝ) * c, z.2))
      (fun j' k' => C j' * Real.exp (κ j' * (n : ℝ) ^ 2) * Real.exp (-((κ j' / 2) * (k' : ℝ) ^ 2)))
      hfsm (fun j' => hvsum n j') (fun j' k y hy => hstrip n j' k y hy)
    exact hon.contDiffAt ((perDerivStrip_isOpen n).mem_nhds hx)
  refine ⟨hcontd, fun j x => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt |x.1|
  exact claim n j x ((mem_perDerivStrip n x).2 hn)

end UnforcedLeray.Short.IIb
