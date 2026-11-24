import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F07Surjective

/-!
# Part II-a, task `PartII-a:F16/a`: the body inverse is bounded on `Y_2`

Source `shorter-proof-2026-11-02.tex` lines 1553-1554, 1585-1586. For `μ` in a compact `K` with
`Re μ + 1/4 > 0`, `R f := (μ+L)^{-1}(𝐏 f)` is a bounded linear map of `Y_2`, the inverse of
`bodyOp` on `D_2` composed with the Leray projection. The norm bound comes from the common
graph bound (`PartII-a:F06`) at `r = 2`, the factor `1 + (1+|μ|)/a` being bounded on `K`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Injectivity of `μ + L` on `D_2` (from the graph bound at `r = 2`). -/
theorem bodyOp_injective_F16a (P : ℝ) [Fact (0 < P)] (hP1 : P ≤ 1) (ν : ℝ) (hν : 0 < ν)
    (μ : ℂ) (hμ : 0 < μ.re + gammaR 2) : Function.Injective (bodyOp P ν 2 μ) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨C, hC0, hC⟩ := commonBodyGraphBound 2 ENNReal.one_lt_two (by norm_num)
  obtain ⟨g, -, hg⟩ := hC P hP1 ν hν μ hμ w
  rw [hw, norm_zero, mul_zero] at hg
  have h0 : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ := by positivity
  have hw0 : graphNormD w ≤ 0 := by linarith
  have hn : ‖(w : Yq P 2)‖ ≤ 0 := by
    have h2 := norm_nonneg (nuLapD w)
    have h3' := norm_nonneg (T0D w)
    unfold graphNormD at hw0
    linarith
  exact Subtype.ext (norm_le_zero_iff.1 hn)

/-- `μ + L : D_2 → Y_2` is bijective for `Re μ + 1/4 > 0`. -/
theorem bodyOp_bijective_F16a (P : ℝ) [Fact (0 < P)] (hP1 : P ≤ 1) (ν : ℝ) (hν : 0 < ν)
    (μ : ℂ) (hμ : 0 < μ.re + gammaR 2) : Function.Bijective (bodyOp P ν 2 μ) :=
  ⟨bodyOp_injective_F16a P hP1 ν hν μ hμ,
    commonBodySurjective 2 ENNReal.one_lt_two (by norm_num) P hP1 ν hν μ hμ⟩

/-- **`PartII-a:F16/a`**: the body inverse `R_μ = (μ+L)^{-1} 𝐏` exists as a bounded operator
of `Y_2`, uniformly in `P ≤ 1`, `ν > 0` and `μ` in a compact `K ⊂ {Re μ > -1/4}`. -/
theorem bodyInverseBounded : BodyInverseBounded := by
  intro K hK hKpos
  have hKpos' : ∀ μ ∈ K, 0 < μ.re + gammaR 2 := fun μ hμ => by
    rw [gammaR_two]; exact hKpos μ hμ
  obtain ⟨CG, hCG0, hCG⟩ := commonBodyGraphBound 2 ENNReal.one_lt_two (by norm_num)
  have hcont : ContinuousOn (fun μ : ℂ => 1 + (1 + ‖μ‖) / (μ.re + gammaR 2)) K := by
    refine continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_)
    · exact (continuous_const.add continuous_norm).continuousOn
    · exact (Complex.continuous_re.add continuous_const).continuousOn
    · intro μ hμ; exact (hKpos' μ hμ).ne'
  obtain ⟨F0, hF0⟩ := hK.exists_bound_of_continuousOn hcont
  set F := max F0 0 with hFdef
  have hF : ∀ μ ∈ K, 1 + (1 + ‖μ‖) / (μ.re + gammaR 2) ≤ F := fun μ hμ =>
    (Real.le_norm_self _).trans ((hF0 μ hμ).trans (le_max_left _ _))
  have hF0' : 0 ≤ F := le_max_right _ _
  have hLC0 : 0 ≤ ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ := norm_nonneg _
  refine ⟨CG * F * ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖,
    mul_nonneg (mul_nonneg hCG0 hF0') hLC0, ?_⟩
  intro P _ hP1 ν hν μ hμ
  have hμ' := hKpos' μ hμ
  have hbij := bodyOp_bijective_F16a P hP1 ν hν μ hμ'
  let Ebij : D P ν 2 ≃ₗ[ℂ] Yq P 2 := LinearEquiv.ofBijective (bodyOp P ν 2 μ) hbij
  let Lm : Yq P 2 →ₗ[ℂ] Yq P 2 :=
    (D P ν 2).subtype.comp (Ebij.symm.toLinearMap.comp
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).toLinearMap)
  have hbound : ∀ x : Yq P 2,
      ‖Lm x‖ ≤ (CG * F * ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖) * ‖x‖ := by
    intro x
    set y := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x with hy
    set w : D P ν 2 := Ebij.symm y with hw
    have hbw : bodyOp P ν 2 μ w = y := Ebij.apply_symm_apply y
    obtain ⟨g, -, hg⟩ := hCG P hP1 ν hν μ hμ' w
    rw [hbw] at hg
    have hsum : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ := by positivity
    have hwn : ‖(w : Yq P 2)‖ ≤ graphNormD w := by
      unfold graphNormD
      have := norm_nonneg (nuLapD w)
      have := norm_nonneg (T0D w)
      linarith
    have hyb : ‖y‖ ≤ ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖x‖ := by
      calc ‖y‖ = ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x‖ := rfl
        _ ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖x‖ :=
            mul_le_mul_of_nonneg_right (norm_lerayY_le _ _) (norm_nonneg _)
    have hfac : 1 + (1 + ‖μ‖) / (μ.re + gammaR 2) ≤ F := hF μ hμ
    have hA : CG * (1 + (1 + ‖μ‖) / (μ.re + gammaR 2)) * ‖y‖ ≤ CG * F * ‖y‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hCG0) (norm_nonneg y)
    have hB : CG * F * ‖y‖ ≤ CG * F * (‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left hyb (mul_nonneg hCG0 hF0')
    calc ‖Lm x‖ = ‖(w : Yq P 2)‖ := rfl
      _ ≤ graphNormD w := hwn
      _ ≤ CG * (1 + (1 + ‖μ‖) / (μ.re + gammaR 2)) * ‖y‖ := by linarith
      _ ≤ CG * F * ‖y‖ := hA
      _ ≤ CG * F * (‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖x‖) := hB
      _ = (CG * F * ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖) * ‖x‖ := by ring
  let Rc : Yq P 2 →L[ℂ] Yq P 2 :=
    Lm.mkContinuous (CG * F * ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖) hbound
  refine ⟨Rc, ?_, ?_⟩
  · intro f
    refine ⟨Ebij.symm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f), rfl, ?_⟩
    exact Ebij.apply_symm_apply _
  · exact ContinuousLinearMap.opNorm_le_bound Rc
      (mul_nonneg (mul_nonneg hCG0 hF0') hLC0) (fun x => hbound x)

end UnforcedLeray.Short.PartIIa
