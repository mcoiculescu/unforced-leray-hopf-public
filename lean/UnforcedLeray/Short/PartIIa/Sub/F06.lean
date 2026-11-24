import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F05HomogeneousUniqueness
import UnforcedLeray.Units.B0431
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04

/-!
# Part II-a, task `PartII-a:F06`: the graph bound, reduced to the quantitative drift/diffusion step

Source of record: `the November 2 reference manuscript`, lines 1353-1355 and
the proof 1363-1480.

The only missing analytic input is `BodyLaplacianBound` (source 1431-1480: local window estimate,
averaged over the window centres with no inverse period factor): a distributional solution
`(μ + L₀) w = f` has `νΔw = a ∈ Y_r` with `‖a‖ ≤ C (‖f‖ + (1+|μ|) ‖w‖)`.
Everything else (norm bound `‖w‖ ≤ ‖f‖/a_r` from F01/F02/F05, the drift from the equation, the
gradient from B0431) is proved here: `commonBodyGraphBound_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Quantitative body diffusion bound** (source 1431-1480): for `1 < r < 3` there is `C ≥ 0`
independent of `P ≤ 1`, `ν > 0`, `μ` such that every distributional `Y_r` solution of
`(μ + L₀) w = f` has `νΔw = a` in `Y_r` with `‖a‖ ≤ C (‖f‖ + (1+|μ|)‖w‖)`. -/
def BodyLaplacianBound : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f →
        ∃ a : Yq P r, HasPhaseOp (nuLapT ν) w a ∧ ‖a‖ ≤ C * (‖f‖ + (1 + ‖μ‖) * ‖w‖)

theorem hasPhaseOp_body_of_D {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {ν : ℝ} {μ : ℂ}
    (w : D P ν r) :
    HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w : Yq P r) (bodyOp P ν r μ w) := by
  intro Φ hΦ
  have hL := hasPhaseOp_L0D w
  have hA : IsPhaseTest P (μ • Φ) := by
    have := hΦ.clm_comp ((μ • ContinuousLinearMap.id ℂ CVec3).restrictScalars ℝ)
    exact this
  have hB : IsPhaseTest P (L0T ν Φ) := by
    have e : L0T ν Φ = (driftT Φ - nuLapT ν Φ) - (1 / 2 : ℝ) • Φ := by
      funext p; simp [L0T]
    rw [e]
    have hH : IsPhaseTest P ((1 / 2 : ℝ) • Φ) := by
      have := hΦ.clm_comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ CVec3)
      exact this
    exact (hΦ.driftT.sub (isPhaseTest_nuLapT hΦ ν)).sub hH
  have e1 : bodyOp P ν r μ w = μ • (w : Yq P r) + L0D w := rfl
  show phasePair P r (μ • Φ + L0T ν Φ) (w : Yq P r) = _
  rw [e1, phasePair_add hA hB,
    hL Φ hΦ, phasePair_const_smul hΦ, map_add, map_smul, smul_eq_mul]

/-- The body graph bound, from the quantitative diffusion bound. -/
theorem commonBodyGraphBound_of (h : BodyLaplacianBound) : CommonBodyGraphBound := by
  intro r _ h1 h3
  obtain ⟨C, hC0, hC⟩ := h r h1 h3
  have hrt : r ≠ ⊤ := ne_top_of_lt h3
  refine ⟨(1 + 3 * B0431.gradConstD) * (7 / 2 + 6 * C), by
    have := B0431.gradConstD_nonneg; positivity, ?_⟩
  intro P _ hP ν hν μ hμ w
  set a : ℝ := μ.re + gammaR r with ha
  set f : Yq P r := bodyOp P ν r μ w with hf
  have hw : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w : Yq P r) f :=
    hasPhaseOp_body_of_D w
  -- norm bound from the resolvent and uniqueness
  obtain ⟨Rm, hRm, hRf⟩ := bodyResolvent_exists r h1 h3 P ν hν μ hμ
  have hsol := bodyResolvent_solves r h1 h3 P ν hν μ hμ Rm hRf f
  have hz : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) ((w : Yq P r) - Rm f) 0 := by
    intro Φ hΦ
    rw [map_sub, hw Φ hΦ, hsol Φ hΦ, sub_self, map_zero]
  have hwR : (w : Yq P r) = Rm f := sub_eq_zero.1 (bodyOp_uniqueness r h1 h3 P ν hν μ hμ _ hz)
  have hwn : ‖(w : Yq P r)‖ ≤ a⁻¹ * ‖f‖ := by
    rw [hwR]; exact (Rm.le_opNorm f).trans (mul_le_mul_of_nonneg_right hRm (norm_nonneg _))
  have ha0 : 0 < a := hμ
  -- diffusion
  obtain ⟨Λ, hΛ, hΛn⟩ := hC P hP ν hν μ f w hw
  have hΛeq : nuLapD w = Λ := nuLapD_eq hΛ
  have hdr := hasPhaseOp_drift_of hw hΛ
  have hTeq : T0D w = f - μ • (w : Yq P r) + Λ + (1 / 2 : ℂ) • (w : Yq P r) := T0D_eq hdr
  set K : ℝ := ‖f‖ with hK
  set S : ℝ := 1 + (1 + ‖μ‖) / a with hS
  set X : ℝ := K * S with hX
  have hK0 : 0 ≤ K := norm_nonneg _
  have hS1 : 1 ≤ S := by
    have : 0 ≤ (1 + ‖μ‖) / a := by positivity
    linarith
  have hX0 : 0 ≤ X := by positivity
  have hKX : K ≤ X := by nlinarith
  have hwX : ‖(w : Yq P r)‖ ≤ X := by
    have h1' : ‖(w : Yq P r)‖ ≤ a⁻¹ * K := hwn
    have : a⁻¹ * K ≤ (1 + ‖μ‖) / a * K := by
      rw [div_eq_inv_mul]
      have : a⁻¹ * 1 ≤ a⁻¹ * (1 + ‖μ‖) := by
        gcongr; linarith [norm_nonneg μ]
      nlinarith [mul_le_mul_of_nonneg_right this hK0]
    have h2 : (1 + ‖μ‖) / a * K ≤ X := by
      rw [hX, hS]; nlinarith
    linarith
  have hμw : ‖μ‖ * ‖(w : Yq P r)‖ ≤ X := by
    have : ‖μ‖ * ‖(w : Yq P r)‖ ≤ ‖μ‖ * (a⁻¹ * K) := by gcongr
    have h2 : ‖μ‖ * (a⁻¹ * K) ≤ (1 + ‖μ‖) / a * K := by
      rw [div_eq_inv_mul]
      nlinarith [mul_nonneg (inv_nonneg.2 ha0.le) hK0, norm_nonneg μ]
    have h3' : (1 + ‖μ‖) / a * K ≤ X := by rw [hX, hS]; nlinarith
    linarith
  have hΛX' : ‖Λ‖ ≤ 3 * C * X := by
    have hs : K + (1 + ‖μ‖) * ‖(w : Yq P r)‖ ≤ 3 * X := by
      have : (1 + ‖μ‖) * ‖(w : Yq P r)‖ = ‖(w : Yq P r)‖ + ‖μ‖ * ‖(w : Yq P r)‖ := by ring
      linarith
    calc ‖Λ‖ ≤ C * (K + (1 + ‖μ‖) * ‖(w : Yq P r)‖) := hΛn
      _ ≤ C * (3 * X) := mul_le_mul_of_nonneg_left hs hC0
      _ = 3 * C * X := by ring
  have hTn : ‖T0D w‖ ≤ X + X + 3 * C * X + X / 2 := by
    rw [hTeq]
    have e1 := norm_add_le (f - μ • (w : Yq P r) + Λ) ((1 / 2 : ℂ) • (w : Yq P r))
    have e2 := norm_add_le (f - μ • (w : Yq P r)) Λ
    have e3 := norm_sub_le f (μ • (w : Yq P r))
    have e4 : ‖μ • (w : Yq P r)‖ = ‖μ‖ * ‖(w : Yq P r)‖ := norm_smul _ _
    have e5 : ‖(1 / 2 : ℂ) • (w : Yq P r)‖ ≤ ‖(w : Yq P r)‖ / 2 := by
      rw [norm_smul]; simp [div_eq_inv_mul]
    linarith
  have hG : graphNormD w ≤ (7 / 2 + 6 * C) * X := by
    unfold graphNormD
    rw [hΛeq]
    linarith
  -- gradient
  obtain ⟨g, hg, -, -, hgs⟩ := B0431.exists_grad_graph (P := P) (q := r) h1 hrt hν w
  refine ⟨g, hg, ?_⟩
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hgd : Real.sqrt ν * ∑ j, ‖g j‖ ≤ 3 * B0431.gradConstD * graphNormD w := by
    calc Real.sqrt ν * ∑ j, ‖g j‖
        ≤ Real.sqrt ν * (3 * (B0431.gradConstD * (Real.sqrt ν)⁻¹ * graphNormD w)) :=
          mul_le_mul_of_nonneg_left hgs hsq.le
      _ = 3 * B0431.gradConstD * graphNormD w := by field_simp
  have hgc := B0431.gradConstD_nonneg
  have hG0 : 0 ≤ graphNormD w := by
    unfold graphNormD
    exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  calc graphNormD w + Real.sqrt ν * ∑ j, ‖g j‖
      ≤ graphNormD w + 3 * B0431.gradConstD * graphNormD w := by linarith
    _ = (1 + 3 * B0431.gradConstD) * graphNormD w := by ring
    _ ≤ (1 + 3 * B0431.gradConstD) * ((7 / 2 + 6 * C) * X) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = (1 + 3 * B0431.gradConstD) * (7 / 2 + 6 * C) * (1 + (1 + ‖μ‖) / a) * K := by
      rw [hX, hS]; ring
    _ = (1 + 3 * B0431.gradConstD) * (7 / 2 + 6 * C) * (1 + (1 + ‖μ‖) / (μ.re + gammaR r)) *
        ‖bodyOp P ν r μ w‖ := rfl

end UnforcedLeray.Short.PartIIa
