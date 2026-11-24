import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.L2Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff.Proof

/-!
# `PartIII-a:T21/2/2/3/5/3/1`, leaf `PhysE1L2Diff` (SP 3060-3073)

The `L²(physW(r) dx)` difference quotient of `∂_kφ`. For `r > 0` the fixed-cell weight
`physW(r) = a(r)³ wtPhys(r)` is bounded on the cell by a constant times the density `⟨x⟩^{-2m}` of
`X_{-m,c}` (`E0.wt_le_dens_L2`), so the `L²(physW(r) dx)`-norm of a function is at most a constant
times its `X_{-m,c}`-norm. The difference quotient of `∂_kφ` converges in `X_{-m,c}` by `adjXDiff`
(`w = [k]`), and `∂_kφ(r)`, `∂_k∂_rφ(r)` lie in `X_{-m,c}` by `IsAdjointFlow.memH1` and
`AdjHigherCont` (the proof of `E0.physE0L2Diff` with `w = [k]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff NNReal

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-- The fixed-cell weight is dominated by the density of `X_{-m,c}` on the cell. -/
theorem physW_le_dens (ν c m r : ℝ) (hc : 0 < c) (ha1 : 1 ≤ clockA ν r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ B0579.cell c, physW ν c m r x ≤ K * B0579.jb x ^ (-m) := by
  obtain ⟨K, hK0, hK⟩ := E0.wt_le_dens_L2 ν c m r hc ha1
  have ha : 0 < clockA ν r := by linarith
  refine ⟨clockA ν r ^ 3 * K, by positivity, fun x hx => ?_⟩
  have e : physW ν c m r x = clockA ν r ^ 3 * E0.wtPhys ν c m r x := by
    unfold physW E0.wtPhys
    have h3 : clockA ν r ^ 3 ≠ 0 := pow_ne_zero 3 ha.ne'
    rw [← mul_assoc, mul_inv_cancel₀ h3, one_mul]
  rw [e, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK x hx) (by positivity)

/-- **`PhysE1L2Diff`** (SP 3060-3073). -/
theorem physE1L2Diff (m : ℝ) : PhysE1L2Diff m := by
  intro ν hν tr t s ht hts g φ hφ r hr k
  have hX := adjXDiff m
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr0 : 0 < r := lt_of_le_of_lt ht hr.1
  have ha1 : 1 ≤ clockA ν r := by unfold clockA; nlinarith
  obtain ⟨K, hK0, hK⟩ := physW_le_dens ν (ν ^ (-2 : ℝ)) m r hc ha1
  have hKtop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hkey : ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ENNReal.ofReal (physW ν (ν ^ (-2 : ℝ)) m r x)
        ≤ ENNReal.ofReal K * (B0579.density (-m) x : ℝ≥0∞) := by
    intro x hx
    have h2 : ENNReal.ofReal (B0579.jb x ^ (-m)) = (B0579.density (-m) x : ℝ≥0∞) := by
      rw [← B0579.coe_density, ENNReal.ofReal_coe_nnreal]
    rw [← h2, ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal (hK x hx)
  have hmeas : MeasurableSet (B0579.cell (ν ^ (-2 : ℝ))) := B0579.measurableSet_cell _
  have hgen : ∀ f : ℝ × ℝ → ℂ,
      ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
          ENNReal.ofReal (physW ν (ν ^ (-2 : ℝ)) m r x) * ‖f x‖ₑ ^ 2
        ≤ ENNReal.ofReal K * (xNorm (ν ^ (-2 : ℝ)) (-m) f) ^ 2 := by
    intro f
    rw [XND.xNorm_sq, E0.cellMeasure_lintegral_eq, ← lintegral_const_mul' _ _ hKtop]
    apply setLIntegral_mono' hmeas
    intro x hx
    rw [← mul_assoc]
    exact mul_le_mul' (hkey x hx) le_rfl
  refine ⟨?_, ?_, ?_⟩
  · have hX0 := hX ν hν tr t s ht hts g φ hφ r hr [k] (by simp)
    have hT0 := (((ENNReal.continuous_pow 2).tendsto 0).comp hX0)
    have hT : Tendsto (fun r' => ENNReal.ofReal K * (xNorm (ν ^ (-2 : ℝ)) (-m)
        (fun x => (r' - r)⁻¹ • (pdCx k (φ r') x - pdCx k (φ r) x) -
          pdCx k (adjDt t s φ r) x)) ^ 2)
        (𝓝[≠] r) (𝓝 (ENNReal.ofReal K * 0 ^ 2)) :=
      ENNReal.Tendsto.const_mul hT0 (Or.inr hKtop)
    rw [show ENNReal.ofReal K * (0 : ℝ≥0∞) ^ 2 = 0 by simp] at hT
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
      (fun _ => zero_le)
      (fun r' => hgen _)
  · have hmem : MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      hφ.memH1 r (Ioo_subset_Ico_self hr) k
    have hfin : xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (φ r)) < ⊤ := hmem.eLpNorm_lt_top
    exact lt_of_le_of_lt (hgen (pdCx k (φ r)))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hfin))
  · have hA : MemLp (pdCx k (adjDt t s φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      ((hφ.higherCont r (Ioo_subset_Ico_self hr) [k]).2 (by simp)).1
    have hfin : xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (adjDt t s φ r)) < ⊤ := hA.eLpNorm_lt_top
    exact lt_of_le_of_lt (hgen (pdCx k (adjDt t s φ r)))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hfin))

end UnforcedLeray.Short.IIIa.AdjE1
