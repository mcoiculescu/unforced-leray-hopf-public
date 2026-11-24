import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen2Bound.PairB.Common

/-!


Source of record: `the November 2 reference manuscript`,
lines 1809-1835. Mirrors `Gen1Bound` one derivative order higher.

`genDiff2Term3 ν v = (ν s) S v` and `genDiff2Term4 ν v = (ν s) η² ∂_η² v` with
`v = flatAdjointRep ν μ h`. On `s > 0`:
* `S v = causal₀(S h) + causal₁(ν s Δ h)` (one age differentiation under the integral);
* `∂_η² v = causal₀(∂_η² h)`, and the two moments are commuted through the heat semigroup by
  `η e^{θΔ} = e^{θΔ}(η - 2θ ∂_η)` (`etaMul_causalAdjointRep`) twice, which is the identity
  `η² e^{θΔ} = e^{θΔ}(η² - 4θ η ∂_η - 2θ + 4θ² ∂_η²)` of the source.
Each causal integral is bounded by the inverse coercivity gap times the `L²` norm of its source,
which is dominated by `flatProjMomentNorm c h` (`Gen2Aux`); the heat time is at most `ν H₁`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226
open FlatAdjointElemAux Gen2Aux

namespace PairBProof

/-- The causal representative of `S v` on `s > 0`. -/
def F3 (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  causalAdjointRep ν μ (thetaWeight 0) (opS h) +
    causalAdjointRep ν μ (thetaWeight (0 + 1)) (nuSMul ν 1 (laplaceQEta h))

theorem term3_L2B {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    L2B c (genDiff2Term3 ν (flatAdjointRep ν μ h))
      (ν * H1 * (γs⁻¹ * (1 * flatProjMomentNorm c h) +
        γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h))) := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have hμ : 0 < μ.re + 1 / 4 := hγs.trans_le hμγ
  have iS : Inner c σ H1 h 1 (opS h) :=
    (isDer_Sh hh).inner zero_le_one (by norm_num) (by norm_num)
  have iG : Inner c σ H1 h (ν * H1 * (1 + 1)) (nuSMul ν 1 (laplaceQEta h)) :=
    ((isDer_h hh).lap.inner (by norm_num) (by norm_num) (by norm_num)).nuS hν hσ hσH1
  have hF : L2B c (F3 ν μ h) (γs⁻¹ * (1 * flatProjMomentNorm c h) +
      γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h)) :=
    (iS.causal hh hc hγs hμγ zero_le_one 0).add
      (iG.causal hh hc hγs hμγ (by positivity) (0 + 1))
  refine hF.outer hν hH1 (fun p hp => ?_) (fun p hp => ?_)
  · simp [F3, iS.causal_zero hσ hσH1 _ hp, iG.causal_zero hσ hσH1 _ hp]
  · show (ν * p.1) • opS (flatAdjointRep ν μ h) p = (ν * p.1) • F3 ν μ h p
    rw [← causalAdjointRep_thetaWeight_zero,
      opS_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hp]
    rfl

/-- The causal representative of `η² ∂_η² v` on `s > 0`. -/
def F4 (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  (causalAdjointRep ν μ (thetaWeight 0) (etaMul (etaMul (pdEta (pdEta h)))) -
      (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
        (nuSMul ν 1 (pdEta (etaMul (pdEta (pdEta h)))))) -
    (2 : ℝ) • (causalAdjointRep ν μ (thetaWeight (0 + 1))
        (etaMul (nuSMul ν 1 (pdEta (pdEta (pdEta h))))) -
      (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1 + 1))
        (nuSMul ν 1 (pdEta (nuSMul ν 1 (pdEta (pdEta (pdEta h)))))))

theorem term4_L2B {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    L2B c (genDiff2Term4 ν (flatAdjointRep ν μ h))
      (ν * H1 * ((γs⁻¹ * (1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h))) +
        |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * 1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (ν * H1 * 1) * flatProjMomentNorm c h))))) := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have hμ : 0 < μ.re + 1 / 4 := hγs.trans_le hμγ
  have hY : 0 ≤ ν * H1 := (mul_pos hν hH1).le
  -- derivative chains
  have d2 : IsDer c σ H1 h 0 (0 + 1 + 1) 1 (pdEta (pdEta h)) := (isDer_h hh).dEta.dEta
  have d3 : IsDer c σ H1 h 0 (0 + 1 + 1 + 1) 1 (pdEta (pdEta (pdEta h))) := d2.dEta
  have d4 : IsDer c σ H1 h 0 (0 + 1 + 1 + 1 + 1) 1 (pdEta (pdEta (pdEta (pdEta h)))) := d3.dEta
  have i2 : Inner c σ H1 h 1 (pdEta (pdEta h)) := d2.inner zero_le_one (by norm_num) (by norm_num)
  have i3 : Inner c σ H1 h 1 (pdEta (pdEta (pdEta h))) :=
    d3.inner zero_le_one (by norm_num) (by norm_num)
  have i2e : Inner c σ H1 h 1 (etaMul (pdEta (pdEta h))) :=
    d2.inner_eta zero_le_one (by norm_num) (by norm_num)
  have i3e : Inner c σ H1 h 1 (etaMul (pdEta (pdEta (pdEta h)))) :=
    d3.inner_eta zero_le_one (by norm_num) (by norm_num)
  -- the four sources
  have iA1 : Inner c σ H1 h 1 (etaMul (etaMul (pdEta (pdEta h)))) :=
    d2.inner_eta2 zero_le_one (by norm_num) (by norm_num)
  have iD : Inner c σ H1 h (1 + 1) (pdEta (etaMul (pdEta (pdEta h)))) :=
    (i2.add i3e).congr (pdEta_etaMul_eq d2.smooth).symm
  have iA2 : Inner c σ H1 h (ν * H1 * (1 + 1)) (nuSMul ν 1 (pdEta (etaMul (pdEta (pdEta h))))) :=
    iD.nuS hν hσ hσH1
  have iN3 : Inner c σ H1 h (ν * H1 * 1) (nuSMul ν 1 (pdEta (pdEta (pdEta h)))) :=
    i3.nuS hν hσ hσH1
  have iA3 : Inner c σ H1 h (ν * H1 * 1) (etaMul (nuSMul ν 1 (pdEta (pdEta (pdEta h))))) :=
    d3.inner_eta_nuSMul zero_le_one (by norm_num) (by norm_num) hν hσ hσH1
  have hcomm : pdEta (nuSMul ν 1 (pdEta (pdEta (pdEta h)))) =
      nuSMul ν 1 (pdEta (pdEta (pdEta (pdEta h)))) :=
    pdEta_nuSMul_one ν (d3.smooth.differentiable (by simp))
  have iN4 : Inner c σ H1 h (ν * H1 * 1) (pdEta (nuSMul ν 1 (pdEta (pdEta (pdEta h))))) :=
    ((d4.inner zero_le_one (by norm_num) (by norm_num)).nuS hν hσ hσH1).congr hcomm.symm
  have iA4 : Inner c σ H1 h (ν * H1 * (ν * H1 * 1))
      (nuSMul ν 1 (pdEta (nuSMul ν 1 (pdEta (pdEta (pdEta h)))))) :=
    iN4.nuS hν hσ hσH1
  -- the `L²` bound of the representative
  have hF : L2B c (F4 ν μ h)
      ((γs⁻¹ * (1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h))) +
        |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * 1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (ν * H1 * 1) * flatProjMomentNorm c h)))) :=
    ((iA1.causal hh hc hγs hμγ zero_le_one 0).sub
        ((iA2.causal hh hc hγs hμγ (by positivity) (0 + 1)).smul 2)).sub
      (((iA3.causal hh hc hγs hμγ (by positivity) (0 + 1)).sub
        ((iA4.causal hh hc hγs hμγ (by positivity) (0 + 1 + 1)).smul 2)).smul 2)
  refine hF.outer hν hH1 (fun p hp => ?_) (fun p hp => ?_)
  · simp [F4, iA1.causal_zero hσ hσH1 _ hp, iA2.causal_zero hσ hσH1 _ hp,
      iA3.causal_zero hσ hσH1 _ hp, iA4.causal_zero hσ hσH1 _ hp]
  · -- `∂_η² v = causal₀(∂_η² h)` on `s > 0`
    have hev : pdEta (flatAdjointRep ν μ h) =ᶠ[𝓝 p]
        causalAdjointRep ν μ (thetaWeight 0) (pdEta h) := by
      filter_upwards [pos_mem_nhds hp] with q hq
      rw [← causalAdjointRep_thetaWeight_zero]
      exact pdEta_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hq
    have hEE : pdEta (pdEta (flatAdjointRep ν μ h)) p =
        causalAdjointRep ν μ (thetaWeight 0) (pdEta (pdEta h)) p := by
      rw [pdEta_congr_nhds hev]
      exact pdEta_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_pdEta hh) hp
    -- moment commutations
    have e1 : (p.2.2 : ℝ) • causalAdjointRep ν μ (thetaWeight 0) (pdEta (pdEta h)) p =
        causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta (pdEta h))) p -
          (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
            (nuSMul ν 1 (pdEta (pdEta (pdEta h)))) p :=
      etaMul_causalAdjointRep hν hσ hσH1 hμ 0 d2.smooth d2.support_s (i2.bdd hh zero_le_one)
        (i3.bdd hh zero_le_one) (i2e.bdd hh zero_le_one) hp
    have e2 : (p.2.2 : ℝ) • causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta (pdEta h))) p =
        causalAdjointRep ν μ (thetaWeight 0) (etaMul (etaMul (pdEta (pdEta h)))) p -
          (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
            (nuSMul ν 1 (pdEta (etaMul (pdEta (pdEta h))))) p :=
      etaMul_causalAdjointRep hν hσ hσH1 hμ 0 i2e.smooth i2e.support_s
        (i2e.bdd hh zero_le_one) (iD.bdd hh (by norm_num)) (iA1.bdd hh zero_le_one) hp
    have e3 : (p.2.2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
          (nuSMul ν 1 (pdEta (pdEta (pdEta h)))) p =
        causalAdjointRep ν μ (thetaWeight (0 + 1))
            (etaMul (nuSMul ν 1 (pdEta (pdEta (pdEta h))))) p -
          (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1 + 1))
            (nuSMul ν 1 (pdEta (nuSMul ν 1 (pdEta (pdEta (pdEta h)))))) p :=
      etaMul_causalAdjointRep hν hσ hσH1 hμ (0 + 1) iN3.smooth iN3.support_s
        (iN3.bdd hh (by positivity)) (iN4.bdd hh (by positivity)) (iA3.bdd hh (by positivity)) hp
    show (ν * p.1) • ((p.2.2 ^ 2 : ℝ) • pdEta (pdEta (flatAdjointRep ν μ h)) p) =
      (ν * p.1) • F4 ν μ h p
    rw [hEE, pow_two, mul_smul p.2.2 p.2.2, e1, smul_sub, smul_comm (p.2.2 : ℝ) (2 : ℝ), e2, e3]
    rfl

end PairBProof

open PairBProof

/-- **Pair B (`PartII-a:N04/2/2/3`)**: `L²` membership and polynomial `GammaBox` bound for
`genDiff2Term3` and `genDiff2Term4` applied to `flatAdjointRep ν μ h`. -/
theorem flatAdjointGen2PairB : UnforcedLeray.Short.PartIIa.N04_2_2_3.PairB := by
  refine ⟨7, 23, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  obtain ⟨ht3, b3⟩ := term3_L2B hc hν hσ hσH1 hγs hμγ hh
  obtain ⟨ht4, b4⟩ := term4_L2B hc hν hσ hσH1 hγs hμγ hh
  refine ⟨ht3, ht4, ?_⟩
  obtain ⟨hG1, hγG, -, hYG⟩ := gammaBox_facts hc hν hσ hσH1 hL1 hM0 hγs
  have hF0 : 0 ≤ flatProjMomentNorm c h := flatProjMomentNorm_nonneg c h
  have hY0 : 0 ≤ ν * H1 := (mul_pos hν (hσ.trans_le hσH1)).le
  have key := poly_le hG1 hY0 hYG (inv_nonneg.2 hγs.le) hγG hF0
    (a := 5) (b := 14) (d := 4) (by norm_num) (by norm_num) (by norm_num)
  have e : 4 * (ν * H1 * (γs⁻¹ * (1 * flatProjMomentNorm c h) +
        γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h))) +
      ν * H1 * ((γs⁻¹ * (1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h))) +
        |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * 1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (ν * H1 * 1) * flatProjMomentNorm c h)))) =
      ν * H1 * γs⁻¹ * flatProjMomentNorm c h * (5 + 14 * (ν * H1) + 4 * (ν * H1) ^ 2) := by
    rw [abs_two]
    ring
  have hsum : (5 : ℝ) + 14 + 4 = 23 := by norm_num
  rw [hsum] at key
  linarith

end UnforcedLeray.Short.PartIIa
