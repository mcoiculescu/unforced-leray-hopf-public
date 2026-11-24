import UnforcedLeray.Loc.L13PhysicalRemainder.Background
import UnforcedLeray.Loc.L09CompactDatum.Defect

/-!
# Step L13, helpers: the heat profile of `u_dss` is solenoidal

Support for `Loc/L13PhysicalRemainder.lean` (step L13 `PhysicalRemainderStep`,
`paper/main.tex` lines 152, 159–167; blueprint units B0707, B1028).

For an exact background, `H_h[u_dss](τ, y) = e^{τ/2} ∫ K_s(z) u_dss(e^{τ/2}y - z) dz`
(`s = he^τ`) is distributionally solenoidal: for a scalar test `θ`,
`∫ H·∇θ = e^{τ/2} ∫_z K_s(z) ∫_y u_dss(e^{τ/2}y - z)·∇θ(y) dy dz` (Fubini) and the inner
integral vanishes because `u_dss` is solenoidal (test `θ(e^{-τ/2}(· + z))`). Fubini is
justified by `|u_dss| ≤ C|x|⁻¹`: split `u_dss` into its part on the unit ball (integrable) and
its bounded part. With `U_* = H_h[u_dss] + r_heat` this gives the solenoidality of `r_heat`.
The integrability lemma `integrable_of_rpow_bound` is from

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L13

/-- `∑ᵢ |∂ᵢθ|`. -/
def gradAbs (θ : Space → ℝ) (x : Space) : ℝ := ∑ i : Fin 3, |spatialTestDerivative i θ x|

theorem continuous_spatialTestDerivative {θ : Space → ℝ} (hθ : IsSpatialTest θ) (i : Fin 3) :
    Continuous (spatialTestDerivative i θ) :=
  (hθ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

theorem integrable_gradAbs {θ : Space → ℝ} (hθ : IsSpatialTest θ) : Integrable (gradAbs θ) := by
  unfold gradAbs
  refine integrable_finset_sum _ (fun i _ => ?_)
  have hc := continuous_spatialTestDerivative hθ i
  exact (hc.integrable_of_hasCompactSupport (hθ.compact.fderiv_apply (𝕜 := ℝ) _)).abs

theorem abs_sum_mul_le (v : Space) (θ : Space → ℝ) (x : Space) :
    |∑ i : Fin 3, v i * spatialTestDerivative i θ x| ≤ ‖v‖ * gradAbs θ x := by
  unfold gradAbs
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  gcongr
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

/-- The inner integral vanishes: `∫ u(cy - z)·∇θ(y) dy = 0` for solenoidal `u`. -/
theorem integral_divergence_shift_eq_zero {u : SpatialField} (hsol : IsSolenoidal u)
    {θ : Space → ℝ} (hθ : IsSpatialTest θ) {c : ℝ} (hc : 0 < c) (z : Space) :
    ∫ y, ∑ i : Fin 3, (u (c • y - z)) i * spatialTestDerivative i θ y = 0 := by
  set θ' : Space → ℝ := fun x => θ (c⁻¹ • (x + z)) with hθ'def
  have hθ' : IsSpatialTest θ' := by
    refine ⟨hθ.smooth.comp ((contDiff_id.add contDiff_const).const_smul c⁻¹), ?_⟩
    exact hθ.compact.comp_homeomorph
      ((Homeomorph.addRight z).trans (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc.ne')))
  have hder : ∀ i x, spatialTestDerivative i θ' x =
      c⁻¹ * spatialTestDerivative i θ (c⁻¹ • (x + z)) := by
    intro i x
    have h1 : HasFDerivAt (fun x : Space => c⁻¹ • (x + z))
        (c⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
      ((hasFDerivAt_id x).add_const z).const_smul c⁻¹
    have hd := ((hθ.smooth.differentiable (by simp)) (c⁻¹ • (x + z))).hasFDerivAt.comp x h1
    simp only [spatialTestDerivative, hθ'def]
    rw [show (fun x => θ (c⁻¹ • (x + z))) = θ ∘ (fun x : Space => c⁻¹ • (x + z)) from rfl,
      hd.fderiv]
    simp [map_smul]
  have h0 := hsol.identity θ' hθ'
  have hF : ∀ y : Space, ∑ i : Fin 3, (u (c • y - z)) i * spatialTestDerivative i θ' (c • y - z) =
      c⁻¹ * ∑ i : Fin 3, (u (c • y - z)) i * spatialTestDerivative i θ y := by
    intro y
    have hy : c⁻¹ • (c • y - z + z) = y := by
      rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    simp only [hder, hy]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have e1 := integral_sub_right_eq_self (μ := (volume : Measure Space))
    (fun x => ∑ i : Fin 3, (u x) i * spatialTestDerivative i θ' x) z
  have e2 := MeasureTheory.Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun x => ∑ i : Fin 3, (u (x - z)) i * spatialTestDerivative i θ' (x - z)) c (hR := hc.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at e2
  rw [e1, h0, mul_zero] at e2
  have e3 : (∫ y, c⁻¹ * ∑ i : Fin 3, (u (c • y - z)) i * spatialTestDerivative i θ y) = 0 := by
    rw [← e2]
    exact integral_congr_ae (Eventually.of_forall fun y => (hF y).symm)
  rw [integral_const_mul] at e3
  exact (mul_eq_zero.mp e3).resolve_left (inv_ne_zero hc.ne')

/-- The Fubini integrand `K_s(z) u(cy - z)·∇θ(y)` is integrable on `ℝ³ × ℝ³` when `u` is
continuous off `0` with `|u(x)||x| ≤ C`. -/
theorem integrable_heatDivergence {u : SpatialField} (hcont : ContinuousOn u {0}ᶜ) {C : ℝ}
    (hC : ∀ x : Space, x ≠ 0 → ‖u x‖ * ‖x‖ ≤ C) {θ : Space → ℝ} (hθ : IsSpatialTest θ)
    {c s : ℝ} (hs : 0 < s) :
    Integrable (fun p : Space × Space => Heat.kernel s p.2 *
      ∑ i : Fin 3, (u (c • p.1 - p.2)) i * spatialTestDerivative i θ p.1)
      ((volume : Measure Space).prod volume) := by
  have hC0 : 0 ≤ C := by
    have h := hC (EuclideanSpace.single 0 1) (by simp)
    exact le_trans (by positivity) h
  have hum : Measurable u := measurable_of_continuousOn_compl_singleton 0 hcont
  have hK : Continuous (Heat.kernel s) := (Heat.Gaussian.kernel_smooth (4 * s)).continuous
  have hKmax : ∀ z, Heat.kernel s z ≤ Heat.Gaussian.normalization (4 * s) :=
    fun z => Heat.Gaussian.kernel_le_normalization (by positivity) z
  have hK0 : ∀ z, 0 ≤ Heat.kernel s z := fun z => Heat.kernel_nonneg hs z
  set Km := Heat.Gaussian.normalization (4 * s)
  -- the part of `u` on the unit ball
  set u₁ : SpatialField := (Metric.ball (0 : Space) 1).indicator u with hu₁def
  have hu₁ : Integrable u₁ := by
    refine UnforcedLeray.L09.integrable_of_rpow_bound
      (hum.aestronglyMeasurable.indicator Metric.isOpen_ball.measurableSet)
      (α := 1) (C := C) (R := 1) (by norm_num) (fun x hx => ?_) (fun x hx => ?_)
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hpos]
      by_cases hb : x ∈ Metric.ball (0 : Space) 1
      · rw [hu₁def, Set.indicator_of_mem hb]
        exact hC x hx
      · rw [hu₁def, Set.indicator_of_notMem hb]
        simpa using hC0
    · rw [hu₁def, Set.indicator_of_notMem]
      simp only [Metric.mem_ball, dist_zero_right, not_lt]
      exact hx.le
  have hsplit : ∀ x, ‖u x‖ ≤ ‖u₁ x‖ + C := by
    intro x
    by_cases hb : x ∈ Metric.ball (0 : Space) 1
    · rw [hu₁def, Set.indicator_of_mem hb]
      linarith
    · have hx1 : 1 ≤ ‖x‖ := by simpa using hb
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx1
        linarith
      have h1 := hC x hx0
      have h2 : ‖u x‖ ≤ C := by nlinarith [norm_nonneg (u x)]
      linarith [norm_nonneg (u₁ x)]
  -- measurability
  have hmeas : AEStronglyMeasurable (fun p : Space × Space => Heat.kernel s p.2 *
      ∑ i : Fin 3, (u (c • p.1 - p.2)) i * spatialTestDerivative i θ p.1)
      ((volume : Measure Space).prod volume) := by
    have h1 : Measurable (fun p : Space × Space => u (c • p.1 - p.2)) :=
      hum.comp ((measurable_fst.const_smul c).sub measurable_snd)
    refine (Measurable.mul (hK.measurable.comp measurable_snd) ?_).aestronglyMeasurable
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((measurable_pi_apply i).comp ((PiLp.continuous_ofLp 2 _).measurable.comp h1)).mul
      ((continuous_spatialTestDerivative hθ i).measurable.comp measurable_fst)
  -- the dominating functions
  have hG := integrable_gradAbs hθ
  have hG0 : ∀ x, 0 ≤ gradAbs θ x := fun x => Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hD₂ : Integrable (fun p : Space × Space => (C * gradAbs θ p.1) * Heat.kernel s p.2)
      ((volume : Measure Space).prod volume) :=
    (hG.const_mul C).mul_prod (Heat.kernel_integrable hs)
  have hD₁ : Integrable (fun p : Space × Space => gradAbs θ p.1 * ‖u₁ (c • p.1 - p.2)‖)
      ((volume : Measure Space).prod volume) := by
    have hm : AEStronglyMeasurable (fun p : Space × Space => gradAbs θ p.1 *
        ‖u₁ (c • p.1 - p.2)‖) ((volume : Measure Space).prod volume) := by
      have hu₁m : Measurable u₁ := hum.indicator Metric.isOpen_ball.measurableSet
      have hcg : Continuous (gradAbs θ) :=
        continuous_finsetSum _ (fun i _ => (continuous_spatialTestDerivative hθ i).abs)
      exact ((hcg.measurable.comp measurable_fst).mul
        (hu₁m.comp ((measurable_fst.const_smul c).sub measurable_snd)).norm).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · exact (hu₁.norm.comp_sub_left (c • y)).const_mul (gradAbs θ y)
    · have he : (fun y => ∫ z, ‖gradAbs θ y * ‖u₁ (c • y - z)‖‖) =
          fun y => gradAbs θ y * ∫ z, ‖u₁ z‖ := by
        funext y
        have hn : ∀ z, ‖gradAbs θ y * ‖u₁ (c • y - z)‖‖ = gradAbs θ y * ‖u₁ (c • y - z)‖ :=
          fun z => by rw [Real.norm_of_nonneg (mul_nonneg (hG0 y) (norm_nonneg _))]
        simp only [hn]
        rw [integral_const_mul, integral_sub_left_eq_self (fun z => ‖u₁ z‖) volume (c • y)]
      rw [he]
      exact hG.mul_const _
  refine ((hD₁.const_mul Km).add hD₂).mono' hmeas (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 p.2)]
  have hb := abs_sum_mul_le (u (c • p.1 - p.2)) θ p.1
  calc Heat.kernel s p.2 * |∑ i : Fin 3, (u (c • p.1 - p.2)) i * spatialTestDerivative i θ p.1|
      ≤ Heat.kernel s p.2 * (‖u (c • p.1 - p.2)‖ * gradAbs θ p.1) :=
        mul_le_mul_of_nonneg_left hb (hK0 _)
    _ ≤ Heat.kernel s p.2 * ((‖u₁ (c • p.1 - p.2)‖ + C) * gradAbs θ p.1) := by
        gcongr
        · exact hK0 _
        · exact hG0 _
        · exact hsplit _
    _ = Heat.kernel s p.2 * (gradAbs θ p.1 * ‖u₁ (c • p.1 - p.2)‖) +
          C * gradAbs θ p.1 * Heat.kernel s p.2 := by ring
    _ ≤ Km * (gradAbs θ p.1 * ‖u₁ (c • p.1 - p.2)‖) + C * gradAbs θ p.1 * Heat.kernel s p.2 := by
        gcongr
        · exact mul_nonneg (hG0 _) (norm_nonneg _)
        · exact hKmax _

/-- **`H_h[u_dss](τ)` is solenoidal** for every exact background and every phase. -/
theorem heatProfile_isSolenoidal {B : BackgroundCore} (hB : IsExactBackground B) (τ : ℝ) :
    IsSolenoidal (heatProfile B.h B.udss τ) := by
  have hcont : ContinuousOn B.udss {0}ᶜ := hB.udss_smooth.continuousOn
  obtain ⟨C, hC⟩ := hB.udss_bounds 0 (by norm_num)
  have hC' : ∀ x : Space, x ≠ 0 → ‖B.udss x‖ * ‖x‖ ≤ C := by
    intro x hx
    simpa [norm_iteratedFDeriv_zero] using hC x hx
  set c := Real.exp (τ / 2) with hcdef
  set s := B.h * Real.exp τ with hsdef
  have hc : 0 < c := Real.exp_pos _
  have hs : 0 < s := mul_pos hB.h_pos (Real.exp_pos τ)
  -- the pairing as a fibre integral
  have hrepr : ∀ θ : Space → ℝ, ∀ y : Space,
      ∑ i : Fin 3, (heatProfile B.h B.udss τ y) i * spatialTestDerivative i θ y =
        c * ∫ z, Heat.kernel s z *
          ∑ i : Fin 3, (B.udss (c • y - z)) i * spatialTestDerivative i θ y := by
    intro θ y
    have hint := hB.heat_integrable hs (c • y)
    have hcoord : ∀ i : Fin 3, (∫ z, Heat.kernel s z • B.udss (c • y - z)) i =
        ∫ z, Heat.kernel s z * (B.udss (c • y - z)) i := by
      intro i
      have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hint
      simpa using this.symm
    have hcomp : ∀ i : Fin 3, Integrable (fun z => Heat.kernel s z * (B.udss (c • y - z)) i) := by
      intro i
      have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integrable_comp hint
      simpa using this
    have hcomp' : ∀ i : Fin 3, Integrable (fun z => Heat.kernel s z *
        ((B.udss (c • y - z)) i * spatialTestDerivative i θ y)) := by
      intro i
      simpa [mul_assoc] using (hcomp i).mul_const (spatialTestDerivative i θ y)
    rw [heatProfile_apply, ← hcdef, ← hsdef]
    simp only [PiLp.smul_apply, smul_eq_mul, hcoord]
    have hterm : ∀ i : Fin 3, c * (∫ z, Heat.kernel s z * (B.udss (c • y - z)) i) *
        spatialTestDerivative i θ y = c * ∫ z, Heat.kernel s z *
          ((B.udss (c • y - z)) i * spatialTestDerivative i θ y) := by
      intro i
      rw [mul_assoc, ← integral_mul_const]
      congr 2
      funext z
      ring
    simp only [hterm]
    rw [← Finset.mul_sum, ← integral_finset_sum _ (fun i _ => hcomp' i)]
    congr 2
    funext z
    rw [Finset.mul_sum]
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have hΦ := integrable_heatDivergence hcont hC' hθ (c := c) hs
    have h1 := hΦ.integral_prod_left
    simp only [hrepr θ]
    exact h1.const_mul c
  · have hΦ := integrable_heatDivergence hcont hC' hθ (c := c) hs
    simp only [hrepr θ]
    rw [integral_const_mul]
    have hswap := integral_integral_swap (μ := (volume : Measure Space))
      (ν := (volume : Measure Space))
      (f := fun y z => Heat.kernel s z *
        ∑ i : Fin 3, (B.udss (c • y - z)) i * spatialTestDerivative i θ y) hΦ
    rw [hswap]
    have hz : ∀ z, (∫ y, Heat.kernel s z *
        ∑ i : Fin 3, (B.udss (c • y - z)) i * spatialTestDerivative i θ y) = 0 := by
      intro z
      rw [integral_const_mul, integral_divergence_shift_eq_zero hB.udss_solenoidal hθ hc z,
        mul_zero]
    simp only [hz, integral_zero, mul_zero]

/-- `r_heat(τ)` is solenoidal at every phase. -/
theorem rheat_solenoidal {D : BackgroundData} (hD : IsUnstableBackground D) (τ : ℝ) :
    (D.rheat τ).value ∈ Leray.solenoidalSubspace :=
  rheat_solenoidal_of hD (heatProfile_isSolenoidal hD.1 τ)

end UnforcedLeray.Blueprint.L13
