import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.Leaves
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8`: H1-H6 from their sub-leaves

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836.
Statements: `HeatExists/Leaves.lean`.

* `adjHeatS0Young_of`, `adjHeatGradYoung_of`: the Young bounds from the weighted periodic Young
  inequality and the Gaussian moments;
* `adjHeatS0StrongZero_of`: strong continuity at `0` from the uniform bound (H1), convergence
  on tests and density of tests (three-epsilon argument on the bounded operators `kerCLM`);
* `adjHeatSemigroup_of`: the two semigroup laws;
* `adjHeatS0Weak_of`: the weak heat equation from the dual identity and the time identity of
  the smoothed tests;
* `adjHeatRespDual_of`: the dual identity of the response from H1, H2 (integrability on the
  cell, through `adjPairing`) and the dual identities of `G` and `∂_j G`;
* `adjHeatDuhamelWeak_of`: the tested Duhamel identity of the response from its dual identity
  and the Duhamel identity of the smoothed tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- (H1) from the periodic Young inequality and the Gaussian moment. -/
theorem adjHeatS0Young_of (m : ℝ) (hm : 0 ≤ m) (hY : AdjKerYoungMoment)
    (hH : AdjHeatMoment) : AdjHeatS0Young m := by
  intro ν c hν hc
  obtain ⟨A, hA, hmom⟩ := hH ν m hν hm
  refine ⟨(2 * (1 + c ^ 2 / 4)) ^ (m / 2) * A,
    mul_nonneg (Real.rpow_nonneg (by positivity) _) hA, fun τ hτ => ?_⟩
  exact hY c m hc hm _ (continuous_adjHeatKer ν τ) A hA (hmom τ hτ)

/-- (H2) from the periodic Young inequality and the gradient moment. -/
theorem adjHeatGradYoung_of (m : ℝ) (hm : 0 ≤ m) (hY : AdjKerYoungMoment)
    (hG : AdjHeatGradMoment) : AdjHeatGradYoung m := by
  intro ν c hν hc
  obtain ⟨A, hA, hmom⟩ := hG ν m hν hm
  refine ⟨(2 * (1 + c ^ 2 / 4)) ^ (m / 2) * A,
    mul_nonneg (Real.rpow_nonneg (by positivity) _) hA, fun τ hτ j => ?_⟩
  have hτA : 0 ≤ A * τ ^ (-(1 / 2 : ℝ)) := mul_nonneg hA (Real.rpow_nonneg hτ.1.le _)
  have h := hY c m hc hm _ (continuous_adjHeatGradKer ν τ j) _ hτA (hmom τ hτ j)
  rwa [← mul_assoc] at h

/-- (H3) from (H1), convergence on tests and density of tests. -/
theorem adjHeatS0StrongZero_of (m : ℝ) (h1 : AdjHeatS0Young m) (hT : AdjHeatS0TestLimit m)
    (hD : AdjCylTestDense m) : AdjHeatS0StrongZero m := by
  intro ν c hν hc w
  obtain ⟨M₀, hM₀, hY⟩ := h1 ν c hν hc
  set μ := B0579.cellMeasure c (-m) with hμ
  let T : ℝ → AdjX c m →L[ℂ] AdjX c m := fun τ =>
    if h : τ ∈ Ioc (0 : ℝ) 1 then kerCLM hc (continuous_adjHeatKer ν τ) hM₀ (hY τ h) else 0
  have hTeq : ∀ τ ∈ Ioc (0 : ℝ) 1, ∀ v : AdjX c m,
      ‖T τ v - v‖ = (eLpNorm (fun x => adjS0Fun ν c τ (⇑v) x - v x) 2 μ).toReal := by
    intro τ hτ v
    simp only [T, hτ, ↓reduceDIte]
    exact norm_kerCLM_sub hc _ hM₀ (hY τ hτ) v
  have hTnorm : ∀ τ ∈ Ioc (0 : ℝ) 1, ‖T τ‖ ≤ M₀ := by
    intro τ hτ
    simp only [T, hτ, ↓reduceDIte]
    exact norm_kerCLM_le hc _ hM₀ (hY τ hτ)
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT (by norm_num)
  have key : Tendsto (fun τ => ‖T τ w - w‖) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hK : 0 < M₀ + 1 := by linarith
    obtain ⟨v, hv, hvw⟩ := (hD c hc).exists_dist_lt w
      (show 0 < ε / (2 * (M₀ + 1)) by positivity)
    obtain ⟨g, hg, hvg⟩ := hv
    have hconv : Tendsto (fun τ => (eLpNorm (fun x => adjS0Fun ν c τ g x - g x) 2 μ).toReal)
        (𝓝[>] 0) (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hT ν c hν hc g hg)
      rw [ENNReal.toReal_zero] at h
      exact h
    have hev2 := (Metric.tendsto_nhds.1 hconv) (ε / 2) (by positivity)
    filter_upwards [hev, hev2] with τ hτ hτ2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hτ2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    have hvv : ‖T τ v - v‖ = (eLpNorm (fun x => adjS0Fun ν c τ g x - g x) 2 μ).toReal := by
      rw [hTeq τ hτ v]
      congr 1
      rw [show adjS0Fun ν c τ (⇑v) = adjS0Fun ν c τ g from adjKerOp_congr_ae hc _ hvg]
      refine eLpNorm_congr_ae ?_
      filter_upwards [hvg] with x hx
      rw [hx]
    have hwv : ‖w - v‖ < ε / (2 * (M₀ + 1)) := by rwa [dist_eq_norm] at hvw
    have e : T τ w - w = T τ (w - v) + (T τ v - v) + (v - w) := by
      rw [map_sub]
      abel
    calc ‖T τ w - w‖ = ‖T τ (w - v) + (T τ v - v) + (v - w)‖ := by rw [e]
      _ ≤ ‖T τ (w - v)‖ + ‖T τ v - v‖ + ‖v - w‖ := norm_add₃_le
      _ ≤ M₀ * ‖w - v‖ + ‖T τ v - v‖ + ‖w - v‖ := by
          have h1 : ‖T τ (w - v)‖ ≤ M₀ * ‖w - v‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hTnorm τ hτ) (norm_nonneg _))
          rw [norm_sub_rev v w]
          linarith
      _ = (M₀ + 1) * ‖w - v‖ + ‖T τ v - v‖ := by ring
      _ < (M₀ + 1) * (ε / (2 * (M₀ + 1))) + ε / 2 := by
          rw [hvv]
          exact add_lt_add (mul_lt_mul_of_pos_left hwv hK) hτ2
      _ = ε := by
          field_simp
          ring
  have hlim : Tendsto (fun τ => ENNReal.ofReal ‖T τ w - w‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal key
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  rw [hTeq τ hτ w, ENNReal.ofReal_toReal]
  exact ((memLp_adjKerOp hc (continuous_adjHeatKer ν τ) (hY τ hτ) w).sub
    (Lp.memLp w)).eLpNorm_ne_top

/-- (H4) from the two semigroup laws. -/
theorem adjHeatSemigroup_of (m : ℝ) (h1 : AdjHeatSemigroupS0 m) (h2 : AdjHeatSemigroupGrad m) :
    AdjHeatSemigroup m :=
  ⟨h1, h2⟩

/-- (H5) from the dual identity and the time identity of the smoothed tests. -/
theorem adjHeatS0Weak_of (m : ℝ) (hD : AdjHeatS0Dual m) (hT : AdjHeatS0Time m) :
    AdjHeatS0Weak m := by
  intro ν c hν hc w ψ hψ τ hτ
  rw [hD ν c hν hc τ hτ w ψ hψ, hT ν c hν hc w ψ hψ τ hτ]
  congr 1
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
  rw [Set.uIoc_of_le hτ.1.le] at hr
  rw [hD ν c hν hc r ⟨hr.1, hr.2.trans hτ.2⟩ w (lapP ψ) (Exist.cylTest_lapP hψ)]

/-- A kernel image is integrable on the cell against a test (`adjPairing`, through `kerCLM`). -/
theorem integrableOn_adjKerOp_mul {c m M : ℝ} {k : ℝ × ℝ → ℝ} (hc : 0 < c) (hk : Continuous k)
    (hM : 0 ≤ M) (hY : KerYoung c m k M) (w : AdjX c m) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => adjKerOp c k (⇑w) x * (ψ x : ℂ)) (B0579.cell c) := by
  refine ((adjPairing c m hc ψ hψ).1 (kerCLM hc hk hM hY w)).congr ?_
  filter_upwards [(B0579.ac_cellMeasure c (-m)).ae_le (coeFn_kerCLM hc hk hM hY w)] with x hx
  rw [hx]

/-- (H6.1) from (H1), (H2) and the dual identities of `G` and `∂_j G`. -/
theorem adjHeatRespDual_of (m : ℝ) (h1 : AdjHeatS0Young m) (h2 : AdjHeatGradYoung m)
    (hS : AdjHeatS0Dual m) (hG : AdjHeatGradDual m) : AdjHeatRespDual m := by
  intro ν c hν hc θ hθ y ψ hψ
  obtain ⟨M₀, hM₀, hY0⟩ := h1 ν c hν hc
  obtain ⟨C₁, hC₁, hY1⟩ := h2 ν c hν hc
  have hCθ : 0 ≤ C₁ * θ ^ (-(1 / 2 : ℝ)) := mul_nonneg hC₁ (Real.rpow_nonneg hθ.1.le _)
  have i0 := integrableOn_adjKerOp_mul hc (continuous_adjHeatGradKer ν θ 0) hCθ
    (hY1 θ hθ 0) (y.1 0) hψ
  have i1 := integrableOn_adjKerOp_mul hc (continuous_adjHeatGradKer ν θ 1) hCθ
    (hY1 θ hθ 1) (y.1 1) hψ
  have i2 := integrableOn_adjKerOp_mul hc (continuous_adjHeatKer ν θ) hM₀ (hY0 θ hθ) y.2 hψ
  have g0 := hG ν c hν hc θ hθ 0 (y.1 0) ψ hψ
  have g1 := hG ν c hν hc θ hθ 1 (y.1 1) ψ hψ
  have s2 : ∫ x in B0579.cell c, adjKerOp c (adjHeatKer ν θ) (⇑y.2) x * (ψ x : ℂ) =
      ∫ x in B0579.cell c, y.2 x * (Exist.cylHeatSmooth c (ν * θ) ψ x : ℂ) :=
    hS ν c hν hc θ hθ y.2 ψ hψ
  set A0 := fun x => adjKerOp c (adjHeatGradKer ν θ 0) (⇑(y.1 0)) x * (ψ x : ℂ) with hA0
  set A1 := fun x => adjKerOp c (adjHeatGradKer ν θ 1) (⇑(y.1 1)) x * (ψ x : ℂ) with hA1
  set B := fun x => adjKerOp c (adjHeatKer ν θ) (⇑y.2) x * (ψ x : ℂ) with hB
  have hsplit : (fun x => adjSFun ν c θ (fun j => ⇑(y.1 j)) (⇑y.2) x * (ψ x : ℂ)) =
      fun x => (-(A0 x) - A1 x) + B x := by
    funext x
    simp only [hA0, hA1, hB, adjSFun, adjDivFun_eq, Fin.sum_univ_two, adjS0Fun_eq_adjKerOp]
    ring
  have e1 : ∫ x in B0579.cell c, ((-(A0 x) - A1 x) + B x) =
      (∫ x in B0579.cell c, (-(A0 x) - A1 x)) + ∫ x in B0579.cell c, B x :=
    integral_add (i0.neg.sub i1) i2
  have e2 : ∫ x in B0579.cell c, (-(A0 x) - A1 x) =
      (∫ x in B0579.cell c, -(A0 x)) - ∫ x in B0579.cell c, A1 x :=
    integral_sub i0.neg i1
  have e3 : ∫ x in B0579.cell c, -(A0 x) = -∫ x in B0579.cell c, A0 x := integral_neg _
  unfold adjRespPair
  rw [hsplit, e1, e2, e3, g0, g1, s2]
  unfold adjFluxPair
  ring

/-- (H6) from the dual identity of the response and the Duhamel identity of the smoothed
tests. -/
theorem adjHeatDuhamelWeak_of (m : ℝ) (hD : AdjHeatRespDual m) (hT : AdjHeatRespTime m) :
    AdjHeatDuhamelWeak m := by
  intro ν c hν hc F a b hab hb hF ψ hψ τ hτ
  have hlap := Exist.cylTest_lapP hψ
  have hinner : ∀ r ∈ Icc a τ,
      ∫ σ in a..r, adjRespPair ν c (r - σ) (F σ) (lapP ψ) =
        ∫ σ in a..r, adjFluxPair (F σ) (Exist.cylHeatSmooth c (ν * (r - σ)) (lapP ψ)) := by
    intro r hr
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [UnforcedLeray.Infra.VolterraEvolution.ae_ne_real r] with σ hσr hσ
    rw [Set.uIoc_of_le hr.1] at hσ
    have hlt : σ < r := lt_of_le_of_ne hσ.2 hσr
    exact hD ν c hν hc (r - σ) ⟨by linarith, by linarith [hσ.1, hr.2, hτ.2]⟩ (F σ)
      (lapP ψ) hlap
  have houter : ∫ r in a..τ, adjRespPair ν c (τ - r) (F r) ψ =
      ∫ r in a..τ, adjFluxPair (F r) (Exist.cylHeatSmooth c (ν * (τ - r)) ψ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [UnforcedLeray.Infra.VolterraEvolution.ae_ne_real τ] with r hrτ hr
    rw [Set.uIoc_of_le hτ.1] at hr
    have hlt : r < τ := lt_of_le_of_ne hr.2 hrτ
    exact hD ν c hν hc (τ - r) ⟨by linarith, by linarith [hr.1, hτ.2]⟩ (F r) ψ hψ
  rw [houter, hT ν c hν hc F a b hab hb hF ψ hψ τ hτ]
  congr 1
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [Set.uIcc_of_le hτ.1] at hr
  rw [hinner r hr]

end UnforcedLeray.Short.IIIa
