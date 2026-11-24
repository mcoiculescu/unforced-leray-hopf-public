import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.WtCore
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.XNormDuality

/-!
# `PartIII-a:T21/2/2/2/2/1/3`: the `L²(wt(r) dx)` difference quotient of `φ` (SP 3060-3073)

For `r ≥ 0` the weight `wt(r, x) = a(r)⁻³ (1+P/a)^{-m}` is bounded on the cell by a constant
times the density `⟨x⟩^{-2m}` of `X_{-m,c}` (`wtRatio_le`), so the `L²(wt(r) dx)`-norm of a
function is at most a constant times its `X_{-m,c}`-norm. The difference quotient converges in
`X_{-m,c}` by `AdjXDiff` (with `w = []`), and `φ(r)`, `∂_rφ(r)` lie in `X_{-m,c}` by `memX`
and `AdjHigherCont`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The weight is dominated by the density of `X_{-m,c}` on the cell, with constant `K`
(`wtRatio_le` at `A = a(r)`, `1 ≤ a(r)`). -/
theorem wt_le_dens_L2 (ν c m r : ℝ) (hc : 0 < c) (ha1 : 1 ≤ clockA ν r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ B0579.cell c,
      wtPhys ν c m r x ≤ K * B0579.jb x ^ (-m) := by
  have ha : 0 < clockA ν r := by linarith
  have hpow0 : 0 ≤ (4 / (Real.pi ^ 2 * clockA ν r)) ^ (-m) :=
    Real.rpow_nonneg (div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) ha.le)) _
  refine ⟨(clockA ν r ^ 3)⁻¹ * (1 + (4 / (Real.pi ^ 2 * clockA ν r)) ^ (-m)),
    mul_nonneg (inv_nonneg.mpr (pow_nonneg ha.le 3)) (by linarith), ?_⟩
  intro x hx
  have hR := wtRatio_le c m hc ha1 le_rfl hx
  unfold wtRatio at hR
  have hjb : 0 < B0579.jb x := B0579.jb_pos x
  have hjbm : 0 ≤ B0579.jb x ^ (-m) := Real.rpow_nonneg hjb.le _
  have hsplit : wtF0 c m (clockA ν r) x
      = wtF0 c m (clockA ν r) x * B0579.jb x ^ m * B0579.jb x ^ (-m) := by
    rw [mul_assoc, ← Real.rpow_add hjb, add_neg_cancel, Real.rpow_zero, mul_one]
  have hF : wtF0 c m (clockA ν r) x
      ≤ (1 + (4 / (Real.pi ^ 2 * clockA ν r)) ^ (-m)) * B0579.jb x ^ (-m) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hR hjbm
  have hwt : wtPhys ν c m r x = (clockA ν r ^ 3)⁻¹ * wtF0 c m (clockA ν r) x := by
    unfold wtPhys
    rw [wtF0_eq_periodicWeight c m (clockA ν r) hc ha x]
  rw [hwt]
  calc (clockA ν r ^ 3)⁻¹ * wtF0 c m (clockA ν r) x
      ≤ (clockA ν r ^ 3)⁻¹ * ((1 + (4 / (Real.pi ^ 2 * clockA ν r)) ^ (-m)) * B0579.jb x ^ (-m)) :=
        mul_le_mul_of_nonneg_left hF (inv_nonneg.mpr (pow_nonneg ha.le 3))
    _ = (clockA ν r ^ 3)⁻¹ * (1 + (4 / (Real.pi ^ 2 * clockA ν r)) ^ (-m)) *
          B0579.jb x ^ (-m) := by ring

/-- Integration against the density of `X_{-m,c}` as an integral over the cell. -/
theorem cellMeasure_lintegral_eq (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m)) =
      ∫⁻ x in B0579.cell c, (B0579.density (-m) x : ℝ≥0∞) * ‖F x‖ₑ ^ 2 := by
  unfold B0579.cellMeasure
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable _
    ((B0579.measurable_density (-m)).coe_nnreal_ennreal)
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top) _

theorem physE0L2Diff (m : ℝ) : UnforcedLeray.Short.IIIa.E0.PhysE0L2Diff m := by
  intro ν hν tr t s ht hts g φ hφ hX r hr
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr0 : 0 < r := lt_of_le_of_lt ht hr.1
  have ha1 : 1 ≤ clockA ν r := by unfold clockA; nlinarith
  obtain ⟨K, hK0, hK⟩ := wt_le_dens_L2 ν (ν ^ (-2 : ℝ)) m r hc ha1
  have hKtop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hkey : ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ENNReal.ofReal (wtPhys ν (ν ^ (-2 : ℝ)) m r x)
        ≤ ENNReal.ofReal K * (B0579.density (-m) x : ℝ≥0∞) := by
    intro x hx
    have h2 : ENNReal.ofReal (B0579.jb x ^ (-m)) = (B0579.density (-m) x : ℝ≥0∞) := by
      rw [← B0579.coe_density, ENNReal.ofReal_coe_nnreal]
    rw [← h2, ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal (hK x hx)
  have hmeas : MeasurableSet (B0579.cell (ν ^ (-2 : ℝ))) := by
    unfold B0579.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hgen : ∀ f : ℝ × ℝ → ℂ,
      ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
          ENNReal.ofReal (wtPhys ν (ν ^ (-2 : ℝ)) m r x) * ‖f x‖ₑ ^ 2
        ≤ ENNReal.ofReal K * (xNorm (ν ^ (-2 : ℝ)) (-m) f) ^ 2 := by
    intro f
    rw [XND.xNorm_sq, cellMeasure_lintegral_eq, ← lintegral_const_mul' _ _ hKtop]
    apply setLIntegral_mono' hmeas
    intro x hx
    rw [← mul_assoc]
    exact mul_le_mul' (hkey x hx) le_rfl
  refine ⟨?_, ?_, ?_⟩
  · have hX0 := hX ν hν tr t s ht hts g φ hφ r hr [] (by simp)
    have hT0 := (((ENNReal.continuous_pow 2).tendsto 0).comp hX0)
    have hT : Tendsto (fun r' => ENNReal.ofReal K * (xNorm (ν ^ (-2 : ℝ)) (-m)
        (fun x => (r' - r)⁻¹ • (φ r' x - φ r x) - adjDt t s φ r x)) ^ 2)
        (𝓝[≠] r) (𝓝 (ENNReal.ofReal K * 0 ^ 2)) :=
      ENNReal.Tendsto.const_mul hT0 (Or.inr hKtop)
    rw [show ENNReal.ofReal K * (0 : ℝ≥0∞) ^ 2 = 0 by simp] at hT
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
      (fun _ => zero_le)
      (fun r' => hgen _)
  · have hmem : MemLp (φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      hφ.memX r (Ioo_subset_Icc_self hr)
    have hfin : xNorm (ν ^ (-2 : ℝ)) (-m) (φ r) < ⊤ := hmem.eLpNorm_lt_top
    exact lt_of_le_of_lt (hgen (φ r))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hfin))
  · have hA : MemLp (adjDt t s φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      ((hφ.higherCont r (Ioo_subset_Ico_self hr) []).2 (by simp)).1
    have hfin : xNorm (ν ^ (-2 : ℝ)) (-m) (adjDt t s φ r) < ⊤ := hA.eLpNorm_lt_top
    exact lt_of_le_of_lt (hgen (adjDt t s φ r))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hfin))

end UnforcedLeray.Short.IIIa.E0
