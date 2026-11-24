import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16
import UnforcedLeray.Units.B0414.PhaseOrthogonal

/-!


Source `the November 2 reference manuscript` lines 1586-1587 (`D R_μ^*`),
1359-1361, 1426-1440.  With `u = R^* v`:

* leaf `AdjointSolvesPhaseEq`: `u` solves the adjoint equation `(μ̄ + L₀) u = 𝐏 v` against phase
  tests (`HasPhaseOp (fun Φ => μ̄ Φ + L₀ Φ) u (𝐏 v)`);
* leaf `NuLapFibrewise`: `νΔu = a` against phase tests implies the fibrewise `𝓢'` identity for
  a.e. phase.

`CommonBodyAdjoint` (task `F09`, proved) puts `u` in `D_2` with `‖νΔu‖ ≤ C (1 + (1+|μ|)/a) ‖𝐏v‖`;
compactness of `K` bounds the constant.  Everything but the two leaves is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology SchwartzMap
open scoped ENNReal NNReal Laplacian

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Leaf A**: the Hilbert adjoint of a body inverse solves the adjoint equation, against phase
tests, with datum `𝐏 v`. -/
def AdjointSolvesPhaseEq : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ R : Yq P 2 →L[ℂ] Yq P 2, IsBodyInverse P ν μ R → ∀ v : Yq P 2,
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) ((ContinuousLinearMap.adjoint R) v)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v)

/-- **Leaf B**: `νΔu = a` against phase tests is the fibrewise tempered-distribution identity,
for a.e. phase. -/
def NuLapFibrewise : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (u a : Yq P 2), HasPhaseOp (nuLapT ν) u a →
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      (ν : ℂ) • Δ (((u τ : Lp CVec3 2 (volume : Measure Space))) : 𝓢'(Space, CVec3)) =
        (((a τ : Lp CVec3 2 (volume : Measure Space))) : 𝓢'(Space, CVec3))

/-- **The adjoint graph bound from the two leaves.** -/
theorem bodyAdjointGraph_of (hadj : CommonBodyAdjoint) (hA : AdjointSolvesPhaseEq)
    (hB : NuLapFibrewise) : BodyAdjointGraph := by
  intro K hK hKpos
  have hKpos' : ∀ μ ∈ K, 0 < μ.re + 1 / 4 := hKpos
  obtain ⟨C, hC0, hC⟩ := hadj
  have hcont : ContinuousOn (fun μ : ℂ => 1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) K := by
    refine continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_)
    · exact (continuous_const.add continuous_norm).continuousOn
    · exact (Complex.continuous_re.add continuous_const).continuousOn
    · intro μ hμ; exact (hKpos' μ hμ).ne'
  obtain ⟨F0, hF0⟩ := hK.exists_bound_of_continuousOn hcont
  set F := max F0 0 with hFdef
  have hF : ∀ μ ∈ K, 1 + (1 + ‖μ‖) / (μ.re + 1 / 4) ≤ F := fun μ hμ =>
    (Real.le_norm_self _).trans ((hF0 μ hμ).trans (le_max_left _ _))
  have hF0' : 0 ≤ F := le_max_right _ _
  refine ⟨C * F, mul_nonneg hC0 hF0', ?_⟩
  intro P _ hP1 ν hν μ hμ R hR v
  have hμ' := hKpos' μ hμ
  set u := (ContinuousLinearMap.adjoint R) v with hu
  set f := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v with hf
  have hsol := hA P ν hν μ hμ' R hR v
  obtain ⟨-, hmax⟩ := hC P hP1 ν hν μ hμ' f
  obtain ⟨hw, g, -, hbd⟩ := hmax u hsol
  have hfn : ‖f‖ ≤ ‖v‖ :=
    calc ‖f‖ ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right B0414.norm_lerayY_two_le (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hsum : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hnl : ‖nuLapD (⟨u, hw⟩ : D P ν 2)‖ ≤ graphNormD (⟨u, hw⟩ : D P ν 2) := by
    unfold graphNormD
    linarith [norm_nonneg (u : Yq P 2), norm_nonneg (T0D (⟨u, hw⟩ : D P ν 2))]
  have hb1 : C * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ‖f‖ ≤ C * F * ‖v‖ := by
    have := mul_le_mul_of_nonneg_left (hF μ hμ) hC0
    calc C * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ‖f‖
        ≤ C * F * ‖f‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ C * F * ‖v‖ := mul_le_mul_of_nonneg_left hfn (mul_nonneg hC0 hF0')
  refine ⟨-(nuLapD (⟨u, hw⟩ : D P ν 2)), ?_, ?_⟩
  · have hB' := hB P ν u (nuLapD (⟨u, hw⟩ : D P ν 2)) (hasPhaseOp_nuLapD ⟨u, hw⟩)
    filter_upwards [hB', Lp.coeFn_neg (nuLapD (⟨u, hw⟩ : D P ν 2))] with τ h1 h2
    have h2' : ((-(nuLapD (⟨u, hw⟩ : D P ν 2)) : Yq P 2) τ : Lp CVec3 2 (volume : Measure Space)) =
        -((nuLapD (⟨u, hw⟩ : D P ν 2) : Yq P 2) τ : Lp CVec3 2 (volume : Measure Space)) := h2
    rw [h2', neg_smul, h1]
    rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_neg]
  · rw [norm_neg]
    have hgn : graphNormD (⟨u, hw⟩ : D P ν 2) ≤ C * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ‖f‖ := by
      linarith [hbd, hsum]
    exact hnl.trans (hgn.trans hb1)

end UnforcedLeray.Short.PartIIa
