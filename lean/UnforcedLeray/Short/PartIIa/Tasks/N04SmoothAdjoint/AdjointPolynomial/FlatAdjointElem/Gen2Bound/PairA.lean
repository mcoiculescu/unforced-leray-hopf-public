import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen2Bound.PairB.Common

/-!


Source of record: `the November 2 reference manuscript`,
lines 1809-1835. Mirrors `Gen1Bound` one derivative order higher.

`genDiff2Term1 ν v = (ν s) S² v` and `genDiff2Term2 ν v = (ν s) S(η ∂_η v)` with
`v = flatAdjointRep ν μ h`. On `s > 0`, one age differentiation under the causal integral gives
`S causal_k(w) = causal_k(S w) + causal_{k+1}(ν s Δ w)` (`opS_causalAdjointRep`), so
* `S v = causal₀(S h) + causal₁(ν s Δ h)` and, differentiating once more (two age
  differentiations), `S² v = causal₀(S² h) + causal₁(ν s Δ S h) + causal₁(S(ν s Δ h)) +
  causal₂(ν s Δ(ν s Δ h))`;
* `S(η ∂_η v) = η S ∂_η v = η (causal₀(S ∂_η h) + causal₁(ν s Δ ∂_η h))`, and the moment is
  commuted through the heat semigroup by `η e^{θΔ} = e^{θΔ}(η - 2θ ∂_η)`.
Every source is dominated by `flatProjMomentNorm c h` (`Gen2Aux`, shared with pair B); the heat
time is at most `ν H₁` and `S² h = s ∂_s(S h)` costs a factor `H₁`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226
open FlatAdjointElemAux Gen2Aux

namespace PairAProof

/-- The causal representative of `S² v` on `s > 0`. -/
def F1 (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  (causalAdjointRep ν μ (thetaWeight 0) (opS (opS h)) +
      causalAdjointRep ν μ (thetaWeight (0 + 1)) (nuSMul ν 1 (laplaceQEta (opS h)))) +
    (causalAdjointRep ν μ (thetaWeight (0 + 1)) (opS (nuSMul ν 1 (laplaceQEta h))) +
      causalAdjointRep ν μ (thetaWeight (0 + 1 + 1))
        (nuSMul ν 1 (laplaceQEta (nuSMul ν 1 (laplaceQEta h)))))

theorem term1_L2B {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    L2B c (genDiff2Term1 ν (flatAdjointRep ν μ h))
      (ν * H1 * ((γs⁻¹ * (H1 * flatProjMomentNorm c h) +
          γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h)) +
        (γs⁻¹ * ((ν * H1 * (1 + 1) + ν * H1 * (1 + 1)) * flatProjMomentNorm c h) +
          γs⁻¹ * (ν * H1 * (ν * H1 * (1 + 1 + (1 + 1))) * flatProjMomentNorm c h)))) := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have hμ : 0 < μ.re + 1 / 4 := hγs.trans_le hμγ
  -- sources
  have iSS : Inner c σ H1 h H1 (opS (opS h)) :=
    { smooth := contDiff_opS (contDiff_opS hh.smooth)
      periodic := periodic_opS (periodic_opS hh.periodic)
      support_s := support_s_opS (support_s_opS hh.support_s)
      bound := fun q => by
        have h1 := norm_opS_le_of_support hσ hσH1 (support_s_opS hh.support_s) q
        have h2 := (isDer_Sh hh).dS.le_Bsum zero_le_one (by norm_num) (by norm_num) q
        calc ‖opS (opS h) q‖ ≤ H1 * ‖pdS (opS h) q‖ := h1
          _ ≤ H1 * (1 * Bsum h q) := mul_le_mul_of_nonneg_left h2 hH1.le
          _ = H1 * Bsum h q := by ring }
  have iA : Inner c σ H1 h (ν * H1 * (1 + 1)) (nuSMul ν 1 (laplaceQEta (opS h))) :=
    ((isDer_Sh hh).lap.inner (by norm_num) (by norm_num) (by norm_num)).nuS hν hσ hσH1
  have iG : Inner c σ H1 h (ν * H1 * (1 + 1)) (nuSMul ν 1 (laplaceQEta h)) :=
    ((isDer_h hh).lap.inner (by norm_num) (by norm_num) (by norm_num)).nuS hν hσ hσH1
  have eB : opS (nuSMul ν 1 (laplaceQEta h)) =
      nuSMul ν 1 (laplaceQEta h) + nuSMul ν 1 (laplaceQEta (opS h)) := by
    rw [opS_nuSMul_one_eq ν (contDiff_laplaceQEta hh.smooth), opS_laplaceQEta_comm hh.smooth]
    rfl
  have iB : Inner c σ H1 h (ν * H1 * (1 + 1) + ν * H1 * (1 + 1))
      (opS (nuSMul ν 1 (laplaceQEta h))) :=
    (iG.add iA).congr eB.symm
  have eC : laplaceQEta (nuSMul ν 1 (laplaceQEta h)) =
      nuSMul ν 1 (laplaceQEta (laplaceQEta h)) :=
    laplaceQEta_nuSMul_one ν (contDiff_laplaceQEta hh.smooth)
  have iLG : Inner c σ H1 h (ν * H1 * (1 + 1 + (1 + 1))) (laplaceQEta (nuSMul ν 1 (laplaceQEta h))) :=
    (((isDer_h hh).lap.lap.inner (by norm_num) (by norm_num) (by norm_num)).nuS hν hσ
      hσH1).congr eC.symm
  have iC : Inner c σ H1 h (ν * H1 * (ν * H1 * (1 + 1 + (1 + 1))))
      (nuSMul ν 1 (laplaceQEta (nuSMul ν 1 (laplaceQEta h)))) :=
    iLG.nuS hν hσ hσH1
  -- differentiability data
  have hdS : IsDiffProfile σ H1 (opS h) :=
    (isDer_Sh hh).isDiffProfile hh hσ hσH1 zero_le_one (by norm_num) (by norm_num)
  have hdG : IsDiffProfile σ H1 (nuSMul ν 1 (laplaceQEta h)) :=
    Gen2Aux.IsDiffProfile.nuSMul_one hν hσ hσH1
      ((isDer_h hh).lap.isDiffProfile hh hσ hσH1 (by norm_num) (by norm_num) (by norm_num))
  have hF : L2B c (F1 ν μ h)
      ((γs⁻¹ * (H1 * flatProjMomentNorm c h) +
          γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h)) +
        (γs⁻¹ * ((ν * H1 * (1 + 1) + ν * H1 * (1 + 1)) * flatProjMomentNorm c h) +
          γs⁻¹ * (ν * H1 * (ν * H1 * (1 + 1 + (1 + 1))) * flatProjMomentNorm c h))) :=
    ((iSS.causal hh hc hγs hμγ hH1.le 0).add
        (iA.causal hh hc hγs hμγ (by positivity) (0 + 1))).add
      ((iB.causal hh hc hγs hμγ (by positivity) (0 + 1)).add
        (iC.causal hh hc hγs hμγ (by positivity) (0 + 1 + 1)))
  refine hF.outer hν hH1 (fun p hp => ?_) (fun p hp => ?_)
  · simp [F1, iSS.causal_zero hσ hσH1 _ hp, iA.causal_zero hσ hσH1 _ hp,
      iB.causal_zero hσ hσH1 _ hp, iC.causal_zero hσ hσH1 _ hp]
  · have hev : opS (flatAdjointRep ν μ h) =ᶠ[𝓝 p]
        causalAdjointRep ν μ (thetaWeight 0) (opS h) +
          causalAdjointRep ν μ (thetaWeight (0 + 1)) (nuSMul ν 1 (laplaceQEta h)) := by
      filter_upwards [pos_mem_nhds hp] with q hq
      rw [← causalAdjointRep_thetaWeight_zero]
      exact opS_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hq
    show (ν * p.1) • opS (opS (flatAdjointRep ν μ h)) p = (ν * p.1) • F1 ν μ h p
    rw [opS_congr_nhds hev,
      opS_add_apply (differentiableAt_causalAdjointRep hν hσ hσH1 hμ 0 hdS hp)
        (differentiableAt_causalAdjointRep hν hσ hσH1 hμ (0 + 1) hdG hp),
      opS_causalAdjointRep hν hσ hσH1 hμ 0 hdS hp,
      opS_causalAdjointRep hν hσ hσH1 hμ (0 + 1) hdG hp]
    rfl

/-- The causal representative of `S(η ∂_η v)` on `s > 0`. -/
def F2 (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) : Profile → MeridC :=
  (causalAdjointRep ν μ (thetaWeight 0) (etaMul (opS (pdEta h))) -
      (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
        (nuSMul ν 1 (pdEta (opS (pdEta h))))) +
    (causalAdjointRep ν μ (thetaWeight (0 + 1))
        (etaMul (nuSMul ν 1 (laplaceQEta (pdEta h)))) -
      (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1 + 1))
        (nuSMul ν 1 (pdEta (nuSMul ν 1 (laplaceQEta (pdEta h))))))

theorem term2_L2B {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4) {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    L2B c (genDiff2Term2 ν (flatAdjointRep ν μ h))
      (ν * H1 * ((γs⁻¹ * (1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * 1 * flatProjMomentNorm c h))) +
        (γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (ν * H1 * (1 + 1)) * flatProjMomentNorm c h))))) := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have hμ : 0 < μ.re + 1 / 4 := hγs.trans_le hμγ
  -- derivative chains
  have hw1 : IsDer c σ H1 h 1 (0 + 1) 1 (opS (pdEta h)) := by
    rw [opS_pdEta_comm hh.smooth]
    exact (isDer_Sh hh).dEta
  have hX : IsDer c σ H1 h 0 (0 + 1 + 2) (1 + 1) (laplaceQEta (pdEta h)) := (isDer_h hh).dEta.lap
  -- sources
  have iW1 : Inner c σ H1 h 1 (opS (pdEta h)) := hw1.inner zero_le_one (by norm_num) (by norm_num)
  have iPW1 : Inner c σ H1 h 1 (pdEta (opS (pdEta h))) :=
    hw1.dEta.inner zero_le_one (by norm_num) (by norm_num)
  have a1 : Inner c σ H1 h 1 (etaMul (opS (pdEta h))) :=
    hw1.inner_eta zero_le_one (by norm_num) (by norm_num)
  have a2 : Inner c σ H1 h (ν * H1 * 1) (nuSMul ν 1 (pdEta (opS (pdEta h)))) :=
    iPW1.nuS hν hσ hσH1
  have iW2 : Inner c σ H1 h (ν * H1 * (1 + 1)) (nuSMul ν 1 (laplaceQEta (pdEta h))) :=
    (hX.inner (by norm_num) (by norm_num) (by norm_num)).nuS hν hσ hσH1
  have a3 : Inner c σ H1 h (ν * H1 * (1 + 1)) (etaMul (nuSMul ν 1 (laplaceQEta (pdEta h)))) :=
    hX.inner_eta_nuSMul (by norm_num) (by norm_num) (by norm_num) hν hσ hσH1
  have iPW2 : Inner c σ H1 h (ν * H1 * (1 + 1)) (pdEta (nuSMul ν 1 (laplaceQEta (pdEta h)))) :=
    ((hX.dEta.inner (by norm_num) (by norm_num) (by norm_num)).nuS hν hσ hσH1).congr
      (pdEta_nuSMul_one ν (hX.smooth.differentiable (by simp))).symm
  have a4 : Inner c σ H1 h (ν * H1 * (ν * H1 * (1 + 1)))
      (nuSMul ν 1 (pdEta (nuSMul ν 1 (laplaceQEta (pdEta h))))) :=
    iPW2.nuS hν hσ hσH1
  have hF : L2B c (F2 ν μ h)
      ((γs⁻¹ * (1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * 1 * flatProjMomentNorm c h))) +
        (γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (ν * H1 * (1 + 1)) * flatProjMomentNorm c h)))) :=
    ((a1.causal hh hc hγs hμγ zero_le_one 0).sub
        ((a2.causal hh hc hγs hμγ (by positivity) (0 + 1)).smul 2)).add
      ((a3.causal hh hc hγs hμγ (by positivity) (0 + 1)).sub
        ((a4.causal hh hc hγs hμγ (by positivity) (0 + 1 + 1)).smul 2))
  refine hF.outer hν hH1 (fun p hp => ?_) (fun p hp => ?_)
  · simp [F2, a1.causal_zero hσ hσH1 _ hp, a2.causal_zero hσ hσH1 _ hp,
      a3.causal_zero hσ hσH1 _ hp, a4.causal_zero hσ hσH1 _ hp]
  · have hev : pdEta (flatAdjointRep ν μ h) =ᶠ[𝓝 p]
        causalAdjointRep ν μ (thetaWeight 0) (pdEta h) := by
      filter_upwards [pos_mem_nhds hp] with q hq
      rw [← causalAdjointRep_thetaWeight_zero]
      exact pdEta_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hq
    have hdiff : DifferentiableAt ℝ (pdEta (flatAdjointRep ν μ h)) p :=
      hev.differentiableAt_iff.2
        (differentiableAt_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_pdEta hh) hp)
    have hSE : opS (pdEta (flatAdjointRep ν μ h)) p =
        causalAdjointRep ν μ (thetaWeight 0) (opS (pdEta h)) p +
          causalAdjointRep ν μ (thetaWeight (0 + 1)) (nuSMul ν 1 (laplaceQEta (pdEta h))) p := by
      rw [opS_congr_nhds hev]
      exact opS_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_pdEta hh) hp
    have e1 : (p.2.2 : ℝ) • causalAdjointRep ν μ (thetaWeight 0) (opS (pdEta h)) p =
        causalAdjointRep ν μ (thetaWeight 0) (etaMul (opS (pdEta h))) p -
          (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
            (nuSMul ν 1 (pdEta (opS (pdEta h)))) p :=
      etaMul_causalAdjointRep hν hσ hσH1 hμ 0 hw1.smooth hw1.support_s
        (iW1.bdd hh zero_le_one) (iPW1.bdd hh zero_le_one) (a1.bdd hh zero_le_one) hp
    have e2 : (p.2.2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1))
          (nuSMul ν 1 (laplaceQEta (pdEta h))) p =
        causalAdjointRep ν μ (thetaWeight (0 + 1))
            (etaMul (nuSMul ν 1 (laplaceQEta (pdEta h)))) p -
          (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (0 + 1 + 1))
            (nuSMul ν 1 (pdEta (nuSMul ν 1 (laplaceQEta (pdEta h))))) p :=
      etaMul_causalAdjointRep hν hσ hσH1 hμ (0 + 1) iW2.smooth iW2.support_s
        (iW2.bdd hh (by positivity)) (iPW2.bdd hh (by positivity)) (a3.bdd hh (by positivity)) hp
    have hEta : opS (fun q => q.2.2 • pdEta (flatAdjointRep ν μ h) q) p =
        (p.2.2 : ℝ) • opS (pdEta (flatAdjointRep ν μ h)) p :=
      opS_etaMul_eq hdiff
    show (ν * p.1) • opS (fun q => q.2.2 • pdEta (flatAdjointRep ν μ h) q) p =
      (ν * p.1) • F2 ν μ h p
    rw [hEta, hSE, smul_add, e1, e2]
    rfl

/-- Polynomial domination with an extra `H₁` term. -/
theorem poly_le_H {G Y g F H : ℝ} (hG1 : 1 ≤ G) (hY0 : 0 ≤ Y) (hY : Y ≤ G ^ 2) (hg0 : 0 ≤ g)
    (hg : g ≤ G) (hF : 0 ≤ F) (hH0 : 0 ≤ H) (hH : H ≤ G) {a e b d : ℝ} (ha : 0 ≤ a)
    (he : 0 ≤ e) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Y * g * F * (a + e * H + b * Y + d * Y ^ 2) ≤ (a + e + b + d) * G ^ 7 * F := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG1
  have h1 : Y * g ≤ G ^ 3 := by
    calc Y * g ≤ G ^ 2 * G := mul_le_mul hY hg hg0 (by positivity)
      _ = G ^ 3 := by ring
  have hG4 : 1 ≤ G ^ 4 := one_le_pow₀ hG1
  have hGG4 : G ≤ G ^ 4 := by
    calc G = G ^ 1 := (pow_one G).symm
      _ ≤ G ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
  have hY4 : Y ≤ G ^ 4 := hY.trans (pow_le_pow_right₀ hG1 (by norm_num))
  have hYY : Y ^ 2 ≤ G ^ 4 := by
    calc Y ^ 2 ≤ (G ^ 2) ^ 2 := pow_le_pow_left₀ hY0 hY 2
      _ = G ^ 4 := by ring
  have h2 : a + e * H + b * Y + d * Y ^ 2 ≤ (a + e + b + d) * G ^ 4 := by
    have e1 : a ≤ a * G ^ 4 := le_mul_of_one_le_right ha hG4
    have e2 : e * H ≤ e * G ^ 4 := mul_le_mul_of_nonneg_left (hH.trans hGG4) he
    have e3 : b * Y ≤ b * G ^ 4 := mul_le_mul_of_nonneg_left hY4 hb
    have e4 : d * Y ^ 2 ≤ d * G ^ 4 := mul_le_mul_of_nonneg_left hYY hd
    nlinarith
  have hP : 0 ≤ a + e * H + b * Y + d * Y ^ 2 := by positivity
  calc Y * g * F * (a + e * H + b * Y + d * Y ^ 2) =
        (Y * g) * (a + e * H + b * Y + d * Y ^ 2) * F := by ring
    _ ≤ G ^ 3 * ((a + e + b + d) * G ^ 4) * F := by gcongr
    _ = (a + e + b + d) * G ^ 7 * F := by ring

end PairAProof

open PairAProof

/-- **Pair A (`PartII-a:N04/2/2/3`)**: `L²` membership and polynomial `GammaBox` bound for
`genDiff2Term1` (two age derivatives) and `genDiff2Term2` (one age and one transverse
derivative with a moment) applied to `flatAdjointRep ν μ h`. -/
theorem flatAdjointGen2PairA : UnforcedLeray.Short.PartIIa.N04_2_2_3.PairA := by
  refine ⟨7, 80, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  obtain ⟨ht1, b1⟩ := term1_L2B hc hν hσ hσH1 hγs hμγ hh
  obtain ⟨ht2, b2⟩ := term2_L2B hc hν hσ hσH1 hγs hμγ hh
  refine ⟨ht1, ht2, ?_⟩
  obtain ⟨hG1, hγG, hHG, hYG⟩ := gammaBox_facts hc hν hσ hσH1 hL1 hM0 hγs
  have hF0 : 0 ≤ flatProjMomentNorm c h := flatProjMomentNorm_nonneg c h
  have hH0 : 0 ≤ H1 := (hσ.trans_le hσH1).le
  have hY0 : 0 ≤ ν * H1 := mul_nonneg hν.le hH0
  have key := poly_le_H hG1 hY0 hYG (inv_nonneg.2 hγs.le) hγG hF0 hH0 hHG
    (a := 4) (e := 4) (b := 40) (d := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e : 4 * (ν * H1 * ((γs⁻¹ * (H1 * flatProjMomentNorm c h) +
          γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h)) +
        (γs⁻¹ * ((ν * H1 * (1 + 1) + ν * H1 * (1 + 1)) * flatProjMomentNorm c h) +
          γs⁻¹ * (ν * H1 * (ν * H1 * (1 + 1 + (1 + 1))) * flatProjMomentNorm c h)))) +
      4 * (ν * H1 * ((γs⁻¹ * (1 * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * 1 * flatProjMomentNorm c h))) +
        (γs⁻¹ * (ν * H1 * (1 + 1) * flatProjMomentNorm c h) +
          |(2 : ℝ)| * (γs⁻¹ * (ν * H1 * (ν * H1 * (1 + 1)) * flatProjMomentNorm c h))))) =
      ν * H1 * γs⁻¹ * flatProjMomentNorm c h *
        (4 + 4 * H1 + 40 * (ν * H1) + 32 * (ν * H1) ^ 2) := by
    rw [abs_two]
    ring
  have hsum : (4 : ℝ) + 4 + 40 + 32 = 80 := by norm_num
  rw [hsum] at key
  linarith

end UnforcedLeray.Short.PartIIa
