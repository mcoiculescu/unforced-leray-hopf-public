import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound.Young

/-!
# `L²` bound of `h = [U, X]` on the young support (`PartIII-b:C/ward/10`; source 4194-4195,
4306-4311, 2683-2689)

Source of record: `the November 2 reference manuscript` (73 pages).

"Since `U, DU` are bounded, `h ∈ Y₂`" (4194-4195).  Pointwise, `Df(y)v = Σ_k v_k∂_kf(y)` gives
`|[U, X]| ≤ |U||∂X| + |X||∂U| ≤ M(Σ_k|∂_kX| + 3|X|)` on the young receiver region `ϱ ≥ R√ν`
(only the sup clause of `WardBgBoundL` enters); `h = 0` near the chart points with `νs > 1`
(`wardYoungPointwise`, 4306-4311).  The young chart readings of `X`, `∂_kX` are in
`L²(s^{-3/2}dς)` with bound `C‖g‖_{L²(s^{-1/2}dς)}` (`WardXYoungL2`, from `sep:young`
3633-3648 and the stream-cutoff majorant 3687-3713), and on `νs ≤ 1` the gained body measure is at
most `πe^{2|γ|/ν}s^{-3/2}dς` (Lemma A, `wyl_eLpNorm_body_le`).

* `whb_pointwise`: the pointwise bound of the bracket;
* `wardHBoundL_of`: `WardHBoundL` from `WardXYoungL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **The bracket on the young support** (source 4194-4195): if `|U| ≤ M` and `|∂_jU| ≤ M` at `y`,
then `|DX(y)U - DU(y)X| ≤ M(Σ_k|∂_kX(y)| + 3|X(y)|)`. -/
theorem whb_pointwise {M : ℝ} {u : Space → Space} {X : Space → Space} {y : Space}
    (hU : ‖u y‖ ≤ M) (hdU : ∀ j : Fin 3, ‖physPd u j y‖ ≤ M) :
    ‖fderiv ℝ X y (u y) - fderiv ℝ u y (X y)‖ ≤
      M * (∑ k : Fin 3, ‖physPd X k y‖ + 3 * ‖X y‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hU
  have h1 : ‖fderiv ℝ X y (u y)‖ ≤ M * ∑ k : Fin 3, ‖physPd X k y‖ := by
    refine (wyl_fderiv_apply_norm_le X y (u y)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_right ((wyl_abs_apply_le _ k).trans hU) (norm_nonneg _)
  have h2 : ‖fderiv ℝ u y (X y)‖ ≤ M * (3 * ‖X y‖) := by
    refine (wyl_fderiv_apply_norm_le u y (X y)).trans ?_
    have h3 : ∀ k : Fin 3, |X y k| * ‖physPd u k y‖ ≤ ‖X y‖ * M := fun k =>
      mul_le_mul (wyl_abs_apply_le _ k) (hdU k) (norm_nonneg _) (norm_nonneg _)
    calc ∑ k : Fin 3, |X y k| * ‖physPd u k y‖ ≤ ∑ _k : Fin 3, ‖X y‖ * M :=
          Finset.sum_le_sum fun k _ => h3 k
      _ = M * (3 * ‖X y‖) := by simp [Finset.sum_const]; ring
  calc ‖fderiv ℝ X y (u y) - fderiv ℝ u y (X y)‖
      ≤ ‖fderiv ℝ X y (u y)‖ + ‖fderiv ℝ u y (X y)‖ := norm_sub_le _ _
    _ ≤ M * ∑ k : Fin 3, ‖physPd X k y‖ + M * (3 * ‖X y‖) := add_le_add h1 h2
    _ = M * (∑ k : Fin 3, ‖physPd X k y‖ + 3 * ‖X y‖) := by ring

/-- The bound `M` of `WardBgBoundL` is nonnegative (`|U| ≤ M` at the point `(R√ν, 0, 0)`). -/
theorem whb_M_nonneg {R ν c M : ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hR : 0 < R)
    (hbg : WardBgBoundL R ν c U p M) : 0 ≤ M := by
  set y₀ : Space := WithLp.toLp 2 ![R * Real.sqrt ν, 0, 0]
  have hy : R * Real.sqrt ν ≤ ϱ y₀ := by
    have h0 : y₀ 0 = R * Real.sqrt ν := by simp [y₀]
    have h1 : y₀ 1 = 0 := by simp [y₀]
    unfold ϱ
    rw [h0, h1, show (R * Real.sqrt ν) ^ 2 + (0 : ℝ) ^ 2 = (R * Real.sqrt ν) ^ 2 by ring,
      Real.sqrt_sq (mul_nonneg hR.le (Real.sqrt_nonneg _))]
  exact (norm_nonneg _).trans (hbg.1 0 y₀ hy).1

/-- **`WardHBoundL` from `WardXYoungL2`** (source 4194-4195, 4306-4311, 2683-2689). -/
theorem wardHBoundL_of (hB : WardXYoungL2) : WardHBoundL := by
  intro ν μ R c γ M χy U p hχy hν hR hc hμ hbg
  obtain ⟨C, hC⟩ := hB ν μ R c χy hχy hν hR hc hμ
  have hM := whb_M_nonneg hR hbg
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set KA : ℝ := Real.sqrt (Real.pi * Real.exp (2 * |γ| / ν)) with hKA
  set K₀ : ℝ := |M| * (∑ _k : Fin 3, C' + |(3 : ℝ)| * C') with hK₀
  refine ⟨KA * K₀, fun g hg => ?_⟩
  obtain ⟨hX, hdX⟩ := hC g hg
  set N := eLpNorm g 2 (ageμ c (-1 / 2)) with hN
  set X := wardX ν μ R c χy g with hXdef
  -- the bookkeeping of the bound
  have b0 := wyl_bd_of_young hX
  have b1 : ∀ k : Fin 3, WylBd (ageμ c (-3 / 2)) N
      (wardYoungRead ν R fun τ => physPd (X τ) k) C' := fun k => wyl_bd_of_young (hdX k)
  have bs := WylBd.sum (Finset.univ : Finset (Fin 3)) (K := fun _ => C') (fun _ => hC'0)
    (fun k _ => b1 k)
  have bB := (bs.add (b0.const_mul 3) (Finset.sum_nonneg fun _ _ => hC'0)
    (mul_nonneg (abs_nonneg _) hC'0)).const_mul M
  set B : Chart → ℝ := fun q => M * ((∑ k : Fin 3, wardYoungRead ν R
      (fun τ => physPd (X τ) k) q) + 3 * wardYoungRead ν R X q) with hBdef
  have hB0 : ∀ q, 0 ≤ B q := fun q =>
    mul_nonneg hM (add_nonneg (Finset.sum_nonneg fun k _ => wyl_youngRead_nonneg _ _ _ q)
      (mul_nonneg (by norm_num) (wyl_youngRead_nonneg _ _ _ q)))
  -- pointwise domination of the chart coefficient
  have hpt : ∀ q, ‖coefOf R (wardH ν μ R c χy U g) q‖ ≤ B q := by
    refine wyl_coefOf_le (ν := ν) hB0 (fun q hq => ?_) (fun q hs hq => ?_)
    · have hev := (wyl_X_zero_nhds (μ := μ) (c := c) hν hR hχy g hq).self_of_nhds
        (NearInst.chartTau R q)
      unfold wardH
      rw [hev.fderiv_eq, hev.self_of_nhds]
      simp
    · have hy := wyl_young_ϱ hν hR hs hq
      obtain ⟨hU, hdU, -⟩ := hbg.1 (NearInst.chartTau R q) _ hy
      have key := whb_pointwise (X := X (NearInst.chartTau R q)) hU hdU
      have hi : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      simp only [hBdef, wyl_youngRead_of_young _ hq]
      calc (Real.sqrt q.1)⁻¹ *
            ‖wardH ν μ R c χy U g (NearInst.chartTau R q) (NearInst.chartY R q)‖
          ≤ (Real.sqrt q.1)⁻¹ * (M * (∑ k : Fin 3, ‖physPd (X (NearInst.chartTau R q)) k
              (NearInst.chartY R q)‖ + 3 * ‖X (NearInst.chartTau R q) (NearInst.chartY R q)‖)) :=
            mul_le_mul_of_nonneg_left key hi
        _ = M * (∑ k : Fin 3, (Real.sqrt q.1)⁻¹ * ‖physPd (X (NearInst.chartTau R q)) k
              (NearInst.chartY R q)‖ +
            3 * ((Real.sqrt q.1)⁻¹ * ‖X (NearInst.chartTau R q) (NearInst.chartY R q)‖)) := by
            rw [← Finset.mul_sum]; ring
  -- the coefficient vanishes off the young region
  have hzero : ∀ q : Chart, 1 < ν * q.1 → coefOf R (wardH ν μ R c χy U g) q = 0 :=
    fun q hq => (wardYoungPointwise (μ := μ) (c := c) U hν hR hχy g q hq).2
  calc eLpNorm (coefOf R (wardH ν μ R c χy U g)) 2 (bodyMeasure c γ ν)
      ≤ ENNReal.ofReal KA * eLpNorm (coefOf R (wardH ν μ R c χy U g)) 2 (ageμ c (-3 / 2)) :=
        wyl_eLpNorm_body_le c γ hν hzero
    _ ≤ ENNReal.ofReal KA * eLpNorm B 2 (ageμ c (-3 / 2)) :=
        mul_le_mul' le_rfl (eLpNorm_mono_real hpt)
    _ ≤ ENNReal.ofReal KA * (ENNReal.ofReal K₀ * N) := mul_le_mul' le_rfl bB.2
    _ = ENNReal.ofReal (KA * K₀) * N := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end UnforcedLeray.Short.PartIIIb.Concrete
