import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09
import UnforcedLeray.Units.B0431

/-!
# Part II-a, task `PartII-a:F09/3`: the adjoint graph bound, reduced to two leaves

Source `the November 2 reference manuscript`
lines 1426-1442 (adjoint equation `(μ̄ - 𝒯 - νΔ + 1) w = f`, time reversal of the body problem,
Hilbert identity of 1491-1496).

For `w ∈ D_2` the weak adjoint equation `HasPhaseOp (μ̄ + L₀) w f` is the identity
`f = μ̄ w - T₀w - νΔw + w` (proved here: `adjoint_equation_of_D`, since
`L₀Φ = -driftT Φ - νΔΦ + Φ` on tests).  The two analytic leaves are
`AdjointLaplacianBound` (the time-reversed local window estimate, 1431-1442) and
`AdjointEnergyD2` (the Hilbert identity for the adjoint combination on `D_2`, 1491-1496).
`adjointGraphBound_of` assembles `AdjointGraphBound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Time-reversed diffusion bound** (source 1426-1442 and 1431-1480 with the window rescaled by
`e^{+t/2}`): every distributional `Y_2` solution of the adjoint equation `(μ̄ + L₀)ᵗ w = f` has
`νΔw = a ∈ Y_2` with `‖a‖ ≤ C(‖f‖ + (1+|μ|)‖w‖)`, `C` independent of `P ≤ 1`, `ν`, `μ`. -/
def AdjointLaplacianBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, ∀ f w : Yq P 2,
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
        ∃ a : Yq P 2, HasPhaseOp (nuLapT ν) w a ∧ ‖a‖ ≤ C * (‖f‖ + (1 + ‖μ‖) * ‖w‖)

/-- **Hilbert identity for the adjoint combination on `D_2`** (source 1491-1496, time reversed:
`Re⟨T₀w, w⟩ = (3/4)‖w‖²`, `Re⟨-νΔw, w⟩ = ν‖∇w‖²`, so
`Re⟨-T₀w - νΔw + w, w⟩ = (1/4)‖w‖² + ν‖∇w‖²`), from the core density `D2CoreDense`
(`Sub/F14_1.lean`, lines 1424-1445) and `freeEnergyIdentity`-type slab identities
(`Tasks/F13EnergyIdentity.lean`). -/
def AdjointEnergyD2 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ w : D P ν 2, ∃ g : Fin 3 → Yq P 2,
    HasGrad (w : Yq P 2) g ∧
      (inner ℂ (-(T0D w) - nuLapD w + (w : Yq P 2)) (w : Yq P 2)).re =
        1 / 4 * ‖(w : Yq P 2)‖ ^ 2 + ν * ∑ j, ‖g j‖ ^ 2

/-- On phase tests, `L₀Φ = -driftT Φ - νΔΦ + Φ`. -/
theorem L0_eq_adjoint (ν : ℝ) (Φ : ℝ × Space → CVec3) :
    L0 ν Φ = -(driftT Φ) - nuLapT ν Φ + Φ := by
  funext p
  simp only [L0, T0, driftT, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
  module

/-- The weak adjoint equation of an element of `D_2` is the identity
`μ̄ w - T₀w - νΔw + w`. -/
theorem adjoint_equation_of_D {P : ℝ} [Fact (0 < P)] {ν : ℝ} (μ : ℂ) (w : D P ν 2) :
    HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) (w : Yq P 2)
      ((starRingEnd ℂ) μ • (w : Yq P 2) - T0D w - nuLapD w + (w : Yq P 2)) := by
  intro Φ hΦ
  have hd := hΦ.driftT
  have hn := isPhaseTest_nuLapT hΦ ν
  have hc : IsPhaseTest P ((starRingEnd ℂ) μ • Φ) := hΦ.const_smul _
  have e : (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) Φ =
      (starRingEnd ℂ) μ • Φ + (-(driftT Φ) - nuLapT ν Φ + Φ) := by
    simp only [L0_eq_adjoint]
  rw [e, phasePair_add hc ((hd.neg.sub hn).add hΦ), phasePair_add (hd.neg.sub hn) hΦ,
    phasePair_sub hd.neg hn, phasePair_neg hd, phasePair_const_smul hΦ,
    hasPhaseOp_T0D w Φ hΦ, hasPhaseOp_nuLapD w Φ hΦ]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  ring

theorem adjointGraphBound_of (h1 : AdjointLaplacianBound) (h2 : AdjointEnergyD2) :
    AdjointGraphBound := by
  obtain ⟨C, hC0, hC⟩ := h1
  refine ⟨(1 + 3 * B0431.gradConstD) * (4 + 6 * C), by
    have := B0431.gradConstD_nonneg; positivity, ?_⟩
  intro P _ hP ν hν μ hμ f w hwf hw
  obtain ⟨w', rfl⟩ : ∃ w' : D P ν 2, (w' : Yq P 2) = w := ⟨⟨w, hw⟩, rfl⟩
  set w : Yq P 2 := (w' : Yq P 2) with hwdef
  set a : ℝ := μ.re + 1 / 4 with ha
  have ha0 : 0 < a := hμ
  have hf : f = (starRingEnd ℂ) μ • w - T0D w' - nuLapD w' + w :=
    hasPhaseOp_unique hwf (adjoint_equation_of_D μ w')
  -- norm bound from the Hilbert identity
  obtain ⟨g0, -, hE⟩ := h2 P ν hν w'
  have hwn : ‖w‖ ≤ a⁻¹ * ‖f‖ := by
    have hre : (inner ℂ f w).re = a * ‖w‖ ^ 2 + ν * ∑ j, ‖g0 j‖ ^ 2 := by
      have e1 : f = (starRingEnd ℂ) μ • w + (-(T0D w') - nuLapD w' + w) := by
        rw [hf]; abel
      have e2 : (inner ℂ w w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; simp
      have e3 : (inner ℂ (-(T0D w') - nuLapD w' + w) w).re =
          1 / 4 * ‖w‖ ^ 2 + ν * ∑ j, ‖g0 j‖ ^ 2 := hE
      rw [e1, inner_add_left, inner_smul_left, Complex.add_re, e3, e2, Complex.conj_conj]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ha]
      ring
    have hle : (inner ℂ f w).re ≤ ‖f‖ * ‖w‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hg0 : 0 ≤ ν * ∑ j, ‖g0 j‖ ^ 2 :=
      mul_nonneg hν.le (Finset.sum_nonneg fun _ _ => by positivity)
    have h3 : a * ‖w‖ ^ 2 ≤ ‖f‖ * ‖w‖ := by linarith
    rcases (norm_nonneg w).eq_or_lt with h0 | h0
    · have h00 : ‖w‖ = 0 := h0.symm
      rw [h00]
      exact mul_nonneg (inv_nonneg.2 ha0.le) (norm_nonneg _)
    · have h4 : (‖w‖ * a) * ‖w‖ ≤ ‖f‖ * ‖w‖ := by
        have : (‖w‖ * a) * ‖w‖ = a * ‖w‖ ^ 2 := by ring
        rw [this]; exact h3
      rw [inv_mul_eq_div, le_div_iff₀ ha0]
      exact le_of_mul_le_mul_right h4 h0
  -- diffusion
  obtain ⟨Λ, hΛ, hΛn⟩ := hC P hP ν hν μ f w hwf
  have hΛeq : nuLapD w' = Λ := nuLapD_eq hΛ
  set K : ℝ := ‖f‖ with hK
  set S : ℝ := 1 + (1 + ‖μ‖) / a with hS
  set X : ℝ := K * S with hX
  have hK0 : 0 ≤ K := norm_nonneg _
  have hS1 : 1 ≤ S := by
    have : 0 ≤ (1 + ‖μ‖) / a := by positivity
    linarith
  have hX0 : 0 ≤ X := by positivity
  have hKX : K ≤ X := by nlinarith
  have hwX : ‖w‖ ≤ X := by
    have : a⁻¹ * K ≤ (1 + ‖μ‖) / a * K := by
      rw [div_eq_inv_mul]
      have : a⁻¹ * 1 ≤ a⁻¹ * (1 + ‖μ‖) := by
        gcongr; linarith [norm_nonneg μ]
      nlinarith [mul_le_mul_of_nonneg_right this hK0]
    have h2' : (1 + ‖μ‖) / a * K ≤ X := by
      rw [hX, hS]; nlinarith
    linarith
  have hμw : ‖μ‖ * ‖w‖ ≤ X := by
    have : ‖μ‖ * ‖w‖ ≤ ‖μ‖ * (a⁻¹ * K) := by gcongr
    have h2' : ‖μ‖ * (a⁻¹ * K) ≤ (1 + ‖μ‖) / a * K := by
      rw [div_eq_inv_mul]
      nlinarith [mul_nonneg (inv_nonneg.2 ha0.le) hK0, norm_nonneg μ]
    have h3' : (1 + ‖μ‖) / a * K ≤ X := by rw [hX, hS]; nlinarith
    linarith
  have hΛX : ‖Λ‖ ≤ 3 * C * X := by
    have hs : K + (1 + ‖μ‖) * ‖w‖ ≤ 3 * X := by
      have : (1 + ‖μ‖) * ‖w‖ = ‖w‖ + ‖μ‖ * ‖w‖ := by ring
      linarith
    calc ‖Λ‖ ≤ C * (K + (1 + ‖μ‖) * ‖w‖) := hΛn
      _ ≤ C * (3 * X) := mul_le_mul_of_nonneg_left hs hC0
      _ = 3 * C * X := by ring
  have hTeq : T0D w' = (starRingEnd ℂ) μ • w - Λ + w - f := by
    rw [hf, hΛeq]; abel
  have hTn : ‖T0D w'‖ ≤ X + 3 * C * X + X + X := by
    rw [hTeq]
    have e1 := norm_sub_le ((starRingEnd ℂ) μ • w - Λ + w) f
    have e2 := norm_add_le ((starRingEnd ℂ) μ • w - Λ) w
    have e3 := norm_sub_le ((starRingEnd ℂ) μ • w) Λ
    have e4 : ‖(starRingEnd ℂ) μ • w‖ = ‖μ‖ * ‖w‖ := by
      rw [norm_smul]; simp
    linarith
  have hG : graphNormD w' ≤ (4 + 6 * C) * X := by
    unfold graphNormD
    rw [hΛeq]
    linarith
  -- gradient
  change ∃ g : Fin 3 → Yq P 2, HasGrad w g ∧ graphNormD w' + Real.sqrt ν * ∑ j, ‖g j‖ ≤ _
  obtain ⟨g, hg, -, -, hgs⟩ := B0431.exists_grad_graph (P := P) (q := 2)
    ENNReal.one_lt_two ENNReal.ofNat_ne_top hν w'
  refine ⟨g, hg, ?_⟩
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hgd : Real.sqrt ν * ∑ j, ‖g j‖ ≤ 3 * B0431.gradConstD * graphNormD w' := by
    calc Real.sqrt ν * ∑ j, ‖g j‖
        ≤ Real.sqrt ν * (3 * (B0431.gradConstD * (Real.sqrt ν)⁻¹ * graphNormD w')) :=
          mul_le_mul_of_nonneg_left hgs hsq.le
      _ = 3 * B0431.gradConstD * graphNormD w' := by field_simp
  have hgc := B0431.gradConstD_nonneg
  have hG0 : 0 ≤ graphNormD w' := by
    unfold graphNormD
    exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  calc graphNormD w' + Real.sqrt ν * ∑ j, ‖g j‖
      ≤ graphNormD w' + 3 * B0431.gradConstD * graphNormD w' := by linarith
    _ = (1 + 3 * B0431.gradConstD) * graphNormD w' := by ring
    _ ≤ (1 + 3 * B0431.gradConstD) * ((4 + 6 * C) * X) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = (1 + 3 * B0431.gradConstD) * (4 + 6 * C) * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ‖f‖ := by
      rw [hX, hS]; ring

end UnforcedLeray.Short.PartIIa
