import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.PairBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.FlowNormBound

/-!


Source: `the November 2 reference manuscript`
(SP 2074-2105). Fix `r ∈ (t₀,t₁)`. Write `G_φ(r,x)` for the inner integrand without the factor `ω r x`
(`cylBdG`). Then:
* `CylTdConv` with `N = 0`, `ε = 1` gives `n₀` such that for `n ≥ n₀` both `φs n` and `φs n₀` are
  within `1 + |ν| + |M|` of the limit `φ` in `G`, hence `|G_{φs n} - G_{φs n₀}| ≤ 2(1+|ν|+|M|)`;
* `φs n₀` is a separated sum, so `G_{φs n₀}(r,x)` is bounded on `(t₀,t₁) × cell` (`CylSepSum`,
  `ContDiffOn` derivatives of `χ_k`, compact band support of `IsCylTest` test functions, `M`);
* the pairing estimate `CylPairBound` and the flow bound `CylFlowNormBound` finish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- The inner integrand of `cylTdInner` at age `r`, without the factor `ω r x`. -/
def cylBdG {ν c : ℝ} (tr : B0140.TrainSol ν c) (φ : ℝ → B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) : ℝ :=
  deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
    (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x)

/-- Linearity of the first planar derivative for finite sums of test functions. -/
theorem cylBd_pd_sum {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, Differentiable ℝ (ψ k)) (j : Fin 2) :
    B0579.pd j (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd j (ψ k) y := by
  funext x
  simp only [B0579.pd]
  rw [fderiv_fun_sum (A := fun k y => a k * ψ k y) (fun k _ => (hψ k x).const_mul (a k))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_const_mul (hψ k x), ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Linearity of the planar Laplacian for finite sums of test functions. -/
theorem cylBd_lapP_sum {c : ℝ} {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, B0579.IsCylTest c (ψ k)) (x : B0579.Plane) :
    lapP (fun y => ∑ k, a k * ψ k y) x = ∑ k, a k * lapP (ψ k) x := by
  have D : ∀ k, Differentiable ℝ (ψ k) := fun k => (hψ k).differentiable
  have D0 : ∀ k, Differentiable ℝ (B0579.pd 0 (ψ k)) := fun k => ((hψ k).pd 0).differentiable
  have D1 : ∀ k, Differentiable ℝ (B0579.pd 1 (ψ k)) := fun k => ((hψ k).pd 1).differentiable
  have e0 : B0579.pd 0 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 0 (ψ k) y :=
    cylBd_pd_sum a ψ D 0
  have e1 : B0579.pd 1 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 1 (ψ k) y :=
    cylBd_pd_sum a ψ D 1
  have f00 : B0579.pd 0 (fun y => ∑ k, a k * B0579.pd 0 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 0 (B0579.pd 0 (ψ k)) y :=
    cylBd_pd_sum a (fun k => B0579.pd 0 (ψ k)) D0 0
  have f11 : B0579.pd 1 (fun y => ∑ k, a k * B0579.pd 1 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 1 (B0579.pd 1 (ψ k)) y :=
    cylBd_pd_sum a (fun k => B0579.pd 1 (ψ k)) D1 1
  simp only [lapP]
  rw [e0, e1, f00, f11]
  dsimp only
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A test function on the cylinder is bounded on the cell (continuity on a compact box, and
the band `|η| ≤ R` outside of which it vanishes). -/
theorem cylBd_band_bdd {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ B0579.cell c, |φ x| ≤ C := by
  obtain ⟨R, hR⟩ := hφ.band
  have hKc : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R|) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  by_cases hxR : |x.2| ≤ |R|
  · have hxK : x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R| :=
      ⟨⟨hx.1.1, hx.1.2.le⟩, abs_le.1 hxR⟩
    have h := hC x hxK
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have hlt : R < |x.2| := lt_of_le_of_lt (le_abs_self R) (not_le.1 hxR)
    rw [hR x hlt]
    simp

/-- A `C¹` function on a compact interval has bounded value and (interior) derivative. -/
theorem cylBd_deriv_bdd {χ : ℝ → ℝ} {a b : ℝ} (hχ : ContDiffOn ℝ 1 χ (Icc a b)) :
    ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧ (∀ r ∈ Icc a b, |χ r| ≤ X) ∧
      (∀ r ∈ Ioo a b, |deriv χ r| ≤ Y) := by
  obtain ⟨X, hX⟩ := isCompact_Icc.exists_bound_of_continuousOn hχ.continuousOn
  have hX' : ∀ r ∈ Icc a b, |χ r| ≤ max X 0 := fun r hr => by
    have h := hX r hr
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  by_cases hab : a < b
  · obtain ⟨Y, hY⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hχ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
    refine ⟨max X 0, max Y 0, le_max_right _ _, le_max_right _ _, hX', fun r hr => ?_⟩
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)]
    have h := hY r (Ioo_subset_Icc_self hr)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · exact ⟨max X 0, 0, le_max_right _ _, le_rfl, hX', fun r hr => absurd (hr.1.trans hr.2) hab⟩

/-- Pointwise bound of one term of a separated sum. -/
theorem cylBd_term_le {Y X D ν M dc ch ps lp q0 q1 v0 v1 : ℝ} (hY0 : 0 ≤ Y) (hX0 : 0 ≤ X)
    (hD0 : 0 ≤ D) (hM0 : 0 ≤ M) (hdc : |dc| ≤ Y) (hch : |ch| ≤ X) (hps : |ps| ≤ D)
    (hlp : |lp| ≤ D) (hq0 : |q0| ≤ D) (hq1 : |q1| ≤ D) (hv : |v0| + |v1| ≤ M) :
    |dc * ps + ν * (ch * lp) + ch * (v0 * q0 + v1 * q1)| ≤ Y * D + |ν| * (X * D) + X * D * M := by
  have h1 : |dc * ps| ≤ Y * D := by
    rw [abs_mul]
    exact mul_le_mul hdc hps (abs_nonneg _) hY0
  have h2 : |ν * (ch * lp)| ≤ |ν| * (X * D) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hch hlp (abs_nonneg _) hX0) (abs_nonneg _)
  have hq : |v0 * q0 + v1 * q1| ≤ D * M := by
    calc |v0 * q0 + v1 * q1| ≤ |v0 * q0| + |v1 * q1| := abs_add_le _ _
      _ = |v0| * |q0| + |v1| * |q1| := by rw [abs_mul, abs_mul]
      _ ≤ |v0| * D + |v1| * D := by
          gcongr
      _ = (|v0| + |v1|) * D := by ring
      _ ≤ M * D := mul_le_mul_of_nonneg_right hv hD0
      _ = D * M := by ring
  have h3 : |ch * (v0 * q0 + v1 * q1)| ≤ X * D * M := by
    rw [abs_mul]
    calc |ch| * |v0 * q0 + v1 * q1| ≤ X * (D * M) := mul_le_mul hch hq (abs_nonneg _) hX0
      _ = X * D * M := by ring
  calc |dc * ps + ν * (ch * lp) + ch * (v0 * q0 + v1 * q1)|
      ≤ |dc * ps + ν * (ch * lp)| + |ch * (v0 * q0 + v1 * q1)| := abs_add_le _ _
    _ ≤ (|dc * ps| + |ν * (ch * lp)|) + |ch * (v0 * q0 + v1 * q1)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ Y * D + |ν| * (X * D) + X * D * M := by linarith

/-- Bound of the inner integrand for a separated sum, at a point of `(t₀,t₁) × cell`. -/
theorem cylBd_sep_bound {ν c : ℝ} (tr : B0140.TrainSol ν c) {t₀ t₁ M' : ℝ} {p : ℕ}
    (hM' : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M')
    (χ : Fin p → ℝ → ℝ) (ψ : Fin p → B0579.Plane → ℝ)
    (hχ : ∀ k, ContDiffOn ℝ 1 (χ k) (Icc t₀ t₁)) (hψ : ∀ k, B0579.IsCylTest c (ψ k))
    (X Y D : Fin p → ℝ) (hX0 : ∀ k, 0 ≤ X k) (hY0 : ∀ k, 0 ≤ Y k) (hD0 : ∀ k, 0 ≤ D k)
    (hM0 : 0 ≤ M')
    (hXb : ∀ k, ∀ r ∈ Icc t₀ t₁, |χ k r| ≤ X k)
    (hYb : ∀ k, ∀ r ∈ Ioo t₀ t₁, |deriv (χ k) r| ≤ Y k)
    (hDb : ∀ k, ∀ x ∈ B0579.cell c, |ψ k x| ≤ D k ∧ |B0579.pd 0 (ψ k) x| ≤ D k ∧
      |B0579.pd 1 (ψ k) x| ≤ D k ∧ |lapP (ψ k) x| ≤ D k)
    (φ : ℝ → B0579.Plane → ℝ) (hφ : ∀ r x, φ r x = ∑ k, χ k r * ψ k x)
    {r : ℝ} (hr : r ∈ Ioo t₀ t₁) {x : B0579.Plane} (hx : x ∈ B0579.cell c) :
    |cylBdG tr φ r x| ≤ ∑ k, (Y k * D k + |ν| * (X k * D k) + X k * D k * M') := by
  have hr' : r ∈ Icc t₀ t₁ := Ioo_subset_Icc_self hr
  have hdiff : ∀ k, DifferentiableAt ℝ (χ k) r := fun k =>
    ((hχ k).differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds hr.1 hr.2)
  have hderiv : deriv (fun r' => φ r' x) r = ∑ k, deriv (χ k) r * ψ k x := by
    have hfun : (fun r' => φ r' x) = fun r' => ∑ k, χ k r' * ψ k x :=
      funext fun r' => hφ r' x
    rw [hfun]
    apply HasDerivAt.deriv
    refine HasDerivAt.fun_sum (A := fun k r' => χ k r' * ψ k x)
      (A' := fun k => deriv (χ k) r * ψ k x) ?_
    intro k _
    exact (hdiff k).hasDerivAt.mul_const (ψ k x)
  have hφr : φ r = fun y => ∑ k, χ k r * ψ k y := funext fun y => hφ r y
  have hpd : ∀ j : Fin 2, B0579.pd j (φ r) x = ∑ k, χ k r * B0579.pd j (ψ k) x := by
    intro j
    rw [hφr]
    have e := cylBd_pd_sum (fun k => χ k r) ψ (fun k => (hψ k).differentiable) j
    exact congrFun e x
  have hlap : lapP (φ r) x = ∑ k, χ k r * lapP (ψ k) x := by
    rw [hφr]
    exact cylBd_lapP_sum (fun k => χ k r) ψ hψ x
  have hid : cylBdG tr φ r x = ∑ k, (deriv (χ k) r * ψ k x + ν * (χ k r * lapP (ψ k) x) +
      χ k r * (tr.v r x 0 * B0579.pd 0 (ψ k) x + tr.v r x 1 * B0579.pd 1 (ψ k) x)) := by
    unfold cylBdG
    rw [hderiv, hlap, hpd 0, hpd 1]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hid]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hDb k x hx
  exact cylBd_term_le (hY0 k) (hX0 k) (hD0 k) hM0 (hYb k r hr) (hXb k r hr') h1 h4 h2 h3
    (hM' r hr' x)

/-- Two inner integrands with close test functions are close (`|·| ≤ 1 + |ν| + M`). -/
theorem cylBd_close {ν c : ℝ} (tr : B0140.TrainSol ν c) (φ u : ℝ → B0579.Plane → ℝ) {M : ℝ}
    {r : ℝ} {x : B0579.Plane} (hv : |tr.v r x 0| + |tr.v r x 1| ≤ M)
    (h1 : |B0579.pd 0 (u r) x - B0579.pd 0 (φ r) x| ≤ 1)
    (h2 : |B0579.pd 1 (u r) x - B0579.pd 1 (φ r) x| ≤ 1)
    (h3 : |lapP (u r) x - lapP (φ r) x| ≤ 1)
    (h4 : |deriv (fun r' => u r' x) r - deriv (fun r' => φ r' x) r| ≤ 1) :
    |cylBdG tr u r x - cylBdG tr φ r x| ≤ 1 + |ν| + M := by
  have e : cylBdG tr u r x - cylBdG tr φ r x =
      (deriv (fun r' => u r' x) r - deriv (fun r' => φ r' x) r) +
        ν * (lapP (u r) x - lapP (φ r) x) +
        (tr.v r x 0 * (B0579.pd 0 (u r) x - B0579.pd 0 (φ r) x) +
          tr.v r x 1 * (B0579.pd 1 (u r) x - B0579.pd 1 (φ r) x)) := by
    unfold cylBdG
    ring
  rw [e]
  have t1 : |ν * (lapP (u r) x - lapP (φ r) x)| ≤ |ν| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h3
  have t2 : |tr.v r x 0 * (B0579.pd 0 (u r) x - B0579.pd 0 (φ r) x) +
      tr.v r x 1 * (B0579.pd 1 (u r) x - B0579.pd 1 (φ r) x)| ≤ M := by
    calc _ ≤ |tr.v r x 0 * (B0579.pd 0 (u r) x - B0579.pd 0 (φ r) x)| +
          |tr.v r x 1 * (B0579.pd 1 (u r) x - B0579.pd 1 (φ r) x)| := abs_add_le _ _
      _ = |tr.v r x 0| * |B0579.pd 0 (u r) x - B0579.pd 0 (φ r) x| +
          |tr.v r x 1| * |B0579.pd 1 (u r) x - B0579.pd 1 (φ r) x| := by
          rw [abs_mul, abs_mul]
      _ ≤ |tr.v r x 0| * 1 + |tr.v r x 1| * 1 := by
          gcongr
      _ ≤ M := by linarith
  calc _ ≤ |deriv (fun r' => u r' x) r - deriv (fun r' => φ r' x) r| + |ν * (lapP (u r) x - lapP (φ r) x)|
        + |tr.v r x 0 * (B0579.pd 0 (u r) x - B0579.pd 0 (φ r) x) +
          tr.v r x 1 * (B0579.pd 1 (u r) x - B0579.pd 1 (φ r) x)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 1 + |ν| + M := by linarith

/-- Integral bound with the pairing constant. A non-integrable product integrates to `0`. -/
theorem cylBd_int_bound {m c K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (ω g : B0579.Plane → ℝ) (A : ℝ), MemLp ω 2 (B0579.cellMeasure c m) →
      AEStronglyMeasurable g (volume.restrict (B0579.cell c)) →
      (∀ x ∈ B0579.cell c, |g x| ≤ A) →
      |∫ x in B0579.cell c, ω x * g x| ≤ K * A * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal)
    (w g : B0579.Plane → ℝ) {A : ℝ} (hA : 0 ≤ A) (hw : MemLp w 2 (B0579.cellMeasure c m))
    (hg : ∀ x ∈ B0579.cell c, |g x| ≤ A) :
    |∫ x in B0579.cell c, w x * g x| ≤ K * A * (eLpNorm w 2 (B0579.cellMeasure c m)).toReal := by
  by_cases hmeas : AEStronglyMeasurable (fun x => w x * g x) (volume.restrict (B0579.cell c))
  · have hwm : AEStronglyMeasurable w (volume.restrict (B0579.cell c)) :=
      hw.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m)
    have hg'm : AEStronglyMeasurable (fun x => w x * g x * (w x)⁻¹)
        (volume.restrict (B0579.cell c)) :=
      hmeas.mul (hwm.aemeasurable.inv.aestronglyMeasurable)
    have hbound : ∀ x ∈ B0579.cell c, |w x * g x * (w x)⁻¹| ≤ A := by
      intro x hx
      by_cases h0 : w x = 0
      · simp [h0, hA]
      · have e : w x * g x * (w x)⁻¹ = g x := by field_simp
        rw [e]
        exact hg x hx
    have hfun : (fun x => w x * (w x * g x * (w x)⁻¹)) = fun x => w x * g x := by
      funext x
      by_cases h0 : w x = 0
      · simp [h0]
      · field_simp
    have key := hK w (fun x => w x * g x * (w x)⁻¹) A hw hg'm hbound
    rw [hfun] at key
    exact key
  · have hint : ∫ x in B0579.cell c, w x * g x = 0 :=
      integral_undef (fun h => hmeas h.aestronglyMeasurable)
    rw [hint, abs_zero]
    exact mul_nonneg (mul_nonneg hK0 hA) ENNReal.toReal_nonneg

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Short.IIb in
theorem cylTdRhsBound : UnforcedLeray.Short.IIb.CylTdRhsBound := by
  intro m ν c tr t₀ f ω t₁ φ φs M H
  have H' := H
  unfold CylRhsHyp at H'
  obtain ⟨hm, hc, hfl, ht, hφ, hsep, hconv, hM⟩ := H'
  obtain ⟨K, hK0, hK⟩ := cylPairBound m hm c hc
  obtain ⟨Bf, hBf⟩ := cylFlowNormBound m hm ν c tr t₀ f ω hfl t₁ ht
  obtain ⟨n₀, hn₀⟩ := hconv 0 1 one_pos
  obtain ⟨p, χ, ψ, hχ, hψ, hsum⟩ := hsep n₀
  have hXYD : ∀ k : Fin p, ∃ X Y D : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ D ∧
      (∀ r ∈ Icc t₀ t₁, |χ k r| ≤ X) ∧ (∀ r ∈ Ioo t₀ t₁, |deriv (χ k) r| ≤ Y) ∧
      (∀ x ∈ B0579.cell c, |ψ k x| ≤ D ∧ |B0579.pd 0 (ψ k) x| ≤ D ∧
        |B0579.pd 1 (ψ k) x| ≤ D ∧ |lapP (ψ k) x| ≤ D) := by
    intro k
    obtain ⟨X, Y, hX, hY, hXb, hYb⟩ := cylBd_deriv_bdd (hχ k)
    obtain ⟨D1, hD1, hb1⟩ := cylBd_band_bdd (hψ k)
    obtain ⟨D2, hD2, hb2⟩ := cylBd_band_bdd ((hψ k).pd 0)
    obtain ⟨D3, hD3, hb3⟩ := cylBd_band_bdd ((hψ k).pd 1)
    obtain ⟨D4, hD4, hb4⟩ := cylBd_band_bdd (((hψ k).pd 0).pd 0)
    obtain ⟨D5, hD5, hb5⟩ := cylBd_band_bdd (((hψ k).pd 1).pd 1)
    refine ⟨X, Y, D1 + D2 + D3 + D4 + D5, hX, hY, by linarith, hXb, hYb,
      fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩
    · linarith [hb1 x hx]
    · linarith [hb2 x hx]
    · linarith [hb3 x hx]
    · unfold lapP
      have h4 := hb4 x hx
      have h5 := hb5 x hx
      have := abs_add_le (B0579.pd 0 (B0579.pd 0 (ψ k)) x) (B0579.pd 1 (B0579.pd 1 (ψ k)) x)
      linarith
  choose X Y D hX hY hD hXb hYb hDb using hXYD
  have hMabs : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ |M| :=
    fun r hr x => (hM r hr x).trans (le_abs_self M)
  have hclosed : ∀ n', n₀ ≤ n' → ∀ r ∈ Ioo t₀ t₁, ∀ x ∈ B0579.cell c,
      |cylBdG tr (φs n') r x - cylBdG tr φ r x| ≤ 1 + |ν| + |M| := by
    intro n' hn' r hr x _
    obtain ⟨hv, hd⟩ := hn₀ n' hn'
    have h := hv r (Ioo_subset_Icc_self hr) x
    have h' := hd r hr x
    simp only [Real.rpow_zero, mul_one] at h h'
    apply cylBd_close tr φ (φs n') (hMabs r (Ioo_subset_Icc_self hr) x)
    · linarith [abs_nonneg (φs n' r x - φ r x),
        abs_nonneg (B0579.pd 1 (φs n' r) x - B0579.pd 1 (φ r) x),
        abs_nonneg (lapP (φs n' r) x - lapP (φ r) x)]
    · linarith [abs_nonneg (φs n' r x - φ r x),
        abs_nonneg (B0579.pd 0 (φs n' r) x - B0579.pd 0 (φ r) x),
        abs_nonneg (lapP (φs n' r) x - lapP (φ r) x)]
    · linarith [abs_nonneg (φs n' r x - φ r x),
        abs_nonneg (B0579.pd 0 (φs n' r) x - B0579.pd 0 (φ r) x),
        abs_nonneg (B0579.pd 1 (φs n' r) x - B0579.pd 1 (φ r) x)]
    · exact h'
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = ∑ k, (Y k * D k + |ν| * (X k * D k) + X k * D k * |M|) :=
    ⟨_, rfl⟩
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]
    refine Finset.sum_nonneg fun k _ => ?_
    have := hX k
    have := hY k
    have := hD k
    have := abs_nonneg ν
    have := abs_nonneg M
    positivity
  refine ⟨K * (A0 + 2 * (1 + |ν| + |M|)) * Bf, n₀, fun n hn r hr => ?_⟩
  have hr' : r ∈ Icc t₀ t₁ := Ioo_subset_Icc_self hr
  have hpt : ∀ x ∈ B0579.cell c, |cylBdG tr (φs n) r x| ≤ A0 + 2 * (1 + |ν| + |M|) := by
    intro x hx
    have hs := cylBd_sep_bound tr hMabs χ ψ hχ hψ X Y D hX hY hD (abs_nonneg M) hXb hYb hDb
      (φs n₀) hsum hr hx
    rw [← hA0] at hs
    have hc1 := hclosed n hn r hr x hx
    have hc2 := hclosed n₀ le_rfl r hr x hx
    have t1 := abs_sub_abs_le_abs_sub (cylBdG tr (φs n) r x) (cylBdG tr (φs n₀) r x)
    have t2 := abs_sub_le (cylBdG tr (φs n) r x) (cylBdG tr φ r x) (cylBdG tr (φs n₀) r x)
    have t3 : |cylBdG tr φ r x - cylBdG tr (φs n₀) r x| =
        |cylBdG tr (φs n₀) r x - cylBdG tr φ r x| := abs_sub_comm _ _
    linarith
  have hA : 0 ≤ A0 + 2 * (1 + |ν| + |M|) := by
    have := abs_nonneg ν
    have := abs_nonneg M
    linarith
  have hint : |cylTdInner tr ω (φs n) r| ≤
      K * (A0 + 2 * (1 + |ν| + |M|)) * (eLpNorm (ω r) 2 (B0579.cellMeasure c m)).toReal :=
    cylBd_int_bound hK0 hK (ω r) (cylBdG tr (φs n) r) hA (hfl.memX r hr'.1) hpt
  exact hint.trans (mul_le_mul_of_nonneg_left (hBf r hr') (mul_nonneg hK0 hA))

