import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph.Abstract
import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph.Weak
import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Dense

/-!
# Part II-a, task `PartII-a:F16/b`: the direct graph bound `B R_μ` on `Y_2`

Source `shorter-proof-2026-11-02.tex` lines 1548-1552 (the group `e^{tB}` with generator
`B = 𝒯 - 3/4`) and 1585-1586.

The direct graph bound follows from the generator identity
`bodyDirectGraph_of_generator`: for `w ∈ D_2` the difference quotients of the phase-dilation
group converge to `𝒯 w - (3/4) w`. That identity is `phaseDilation_generator_D2`, proved from
the helpers in `Tasks/F16bBodyDirectGraph/`:

* `Tests`: `e^{tB}` on phase tests, `phaseDilation_testElem`;
* `Deriv`, `Limit`: the classical generator `Bop = 𝒯₀ - 3/4`, its commutation with `dilT`, and
  `h⁻¹ (e^{hB} Φ - Φ) → Bop Φ` in `Y_2` (`tendsto_dil_testElem`);
* `Weak`: the weak identity `⟪BΦ, w⟫ = -⟪Φ, 𝒯₀w - (3/4) w⟫` for `w ∈ D_2`;
* `Abstract`: a unitary group, a dense invariant family of tests and a weakly differentiable
  vector have a strongly differentiable orbit (`generator_of_weak`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **The generator identity on `D_2`** (source 1548-1552): the strong derivative of the
phase-dilation group at `w ∈ D_2` is `𝒯₀ w - (3/4) w`. -/
theorem phaseDilation_generator_D2 (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : D P ν 2) :
    Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ •
        (FreeStress.phaseDilation P t (w : Yq P 2) - (w : Yq P 2)))
      (𝓝[≠] 0) (𝓝 (T0D w - (3 / 4 : ℂ) • (w : Yq P 2))) := by
  refine F16b.generator_of_weak (fun t => FreeStress.phaseDilation P t)
    (FreeStress.phaseDilation_add P) (FreeStress.phaseDilation_zero P)
    (ι := {Φ : ℝ × Space → CVec3 // IsPhaseTest P Φ})
    (fun Φ => testElem P 2 Φ.1) (fun Φ => testElem P 2 (F16b.Bop Φ.1)) ?_ ?_ ?_ _ _ ?_
  · intro g
    obtain ⟨G, hG, hlim⟩ := phaseTestsDenseY2 P g
    exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨⟨G n, hG n⟩, rfl⟩)
  · intro Φ t
    refine ⟨⟨F16b.dilT t Φ.1, F16b.isPhaseTest_dilT Φ.2 t⟩, ?_, ?_⟩
    · exact (F16b.phaseDilation_testElem Φ.2 t).symm
    · show testElem P 2 (F16b.Bop (F16b.dilT t Φ.1)) =
        FreeStress.phaseDilation P t (testElem P 2 (F16b.Bop Φ.1))
      rw [F16b.Bop_dilT (Φ.2.smooth.differentiable (by simp)) t,
        ← F16b.phaseDilation_testElem (F16b.isPhaseTest_Bop Φ.2) t]
  · intro Φ
    exact F16b.tendsto_dil_testElem Φ.2
  · intro Φ
    exact F16b.weak_identity w Φ.2

/-- **Reduction of `PartII-a:F16/b`.** The direct graph bound follows from the strong derivative
of the phase-dilation group on `D_2` (generator `𝒯 - 3/4`, source 1548-1552). -/
theorem bodyDirectGraph_of_generator
    (hgen : ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ w : D P ν 2,
      Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ •
          (FreeStress.phaseDilation P t (w : Yq P 2) - (w : Yq P 2)))
        (𝓝[≠] 0) (𝓝 (T0D w - (3 / 4 : ℂ) • (w : Yq P 2)))) :
    BodyDirectGraph := by
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
  refine ⟨(7 / 4) * (CG * F * ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖),
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCG0 hF0') hLC0), ?_⟩
  intro P _ hP1 ν hν μ hμ R hR v
  have hμ' := hKpos' μ hμ
  obtain ⟨w, hwR, hwy⟩ := hR v
  -- the graph bound for `w = R v`
  obtain ⟨g, -, hg⟩ := hCG P hP1 ν hν μ hμ' w
  set y := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v with hy
  rw [hwy] at hg
  have hsum : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ := by positivity
  have hwn : ‖(w : Yq P 2)‖ ≤ graphNormD w := by
    unfold graphNormD
    have := norm_nonneg (nuLapD w)
    have := norm_nonneg (T0D w)
    linarith
  have hT : ‖T0D w‖ ≤ graphNormD w := by
    unfold graphNormD
    linarith [norm_nonneg (w : Yq P 2), norm_nonneg (nuLapD w)]
  have hyb : ‖y‖ ≤ ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖ := by
    calc ‖y‖ = ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v‖ := rfl
      _ ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_lerayY_le _ _) (norm_nonneg _)
  have hfac : 1 + (1 + ‖μ‖) / (μ.re + gammaR 2) ≤ F := hF μ hμ
  have hA : CG * (1 + (1 + ‖μ‖) / (μ.re + gammaR 2)) * ‖y‖ ≤ CG * F * ‖y‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hCG0) (norm_nonneg y)
  have hB : CG * F * ‖y‖ ≤ CG * F * (‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖) :=
    mul_le_mul_of_nonneg_left hyb (mul_nonneg hCG0 hF0')
  have hgraph : graphNormD w ≤
      CG * F * (‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖) := by
    linarith
  -- the limit `𝒯 w - (3/4) w` and its norm
  refine ⟨T0D w - (3 / 4 : ℂ) • (w : Yq P 2), ?_, ?_⟩
  · rw [← hwR]; exact hgen P ν hν w
  · have h34 : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by norm_num
    calc ‖T0D w - (3 / 4 : ℂ) • (w : Yq P 2)‖
        ≤ ‖T0D w‖ + ‖(3 / 4 : ℂ) • (w : Yq P 2)‖ := norm_sub_le _ _
      _ = ‖T0D w‖ + (3 / 4) * ‖(w : Yq P 2)‖ := by rw [norm_smul, h34]
      _ ≤ graphNormD w + (3 / 4) * graphNormD w :=
          add_le_add hT (mul_le_mul_of_nonneg_left hwn (by norm_num))
      _ = (7 / 4) * graphNormD w := by ring
      _ ≤ (7 / 4) * (CG * F * (‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hgraph (by norm_num)
      _ = (7 / 4) * (CG * F * ‖lerayC 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖) * ‖v‖ := by
          ring

/-- **`PartII-a:F16/b`: the direct graph bound.** -/
theorem bodyDirectGraph : BodyDirectGraph :=
  bodyDirectGraph_of_generator fun P _ ν _ w => phaseDilation_generator_D2 P ν w

end UnforcedLeray.Short.PartIIa
