import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_2
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense
import UnforcedLeray.Short.PartIIa.Sub.N01.PhaseLift
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.OuterSGenPair.Defs

/-!
# `PartII-a:N04/3/3/2/1` (`OuterCore.lean`): `OuterPhaseTestCoreDense`

Source of record: `the November 2 reference manuscript`, lines 1456–1480 and
3340–3363.

Proves `outerPhaseTestCoreDense : OuterPhaseTestCoreDense`: for `ν, ε, P > 0` and
`0 < μ.re + 1 / 4`, any `Z : X SpaceC P` orthogonal to all `(μ - phaseGen ν ε) ψ` for smooth
`P`-periodic bounded-support phase tests `ψ` (`IsPhaseTest P ψ`) vanishes.

## Proof outline
1. Via the unit-scale phase lift `U : X SpaceC P →ₗᵢ[ℂ] Yq P 2` (`N01.phaseLiftExists 1 P`),
   `U Ψ = √P • testElem P 2 ψ` for every phase test `ψ`, and `phaseGen ν ε ψ = -L0 (ν * ε²) ψ`,
   transferring orthogonality of `Z` to orthogonality of `U Z` against
   `μ • testElem P 2 ψ + L0 (ν * ε²) ψ` on all phase tests `ψ`.
2. Radial cutoff graph approximation (`schwartz_triple_mem_closure`) extends orthogonality of `U Z`
   to all Schwartz-type phase functions `IsPhaseSchwartz P 2 Ψs`.
3. Applying this to the truncated inverse integral `truncRes (ν * ε²) μ n f` (`truncResSchwartz_of`,
   `truncResEquation_of`) and sending `n → ∞` via `fwdRemainderBound` (`0 < μ.re + 1 / 4`) gives
   `⟪testElem P 2 f, U Z⟫ = 0` for every phase test `f`.
4. Density of phase tests in `Yq P 2` (`phaseTestsDenseY2`) yields `U Z = 0`, hence `Z = 0` by
   isometry of `U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

namespace OuterCoreAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0223

private theorem inner_eq_zero_of_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u : ℕ → E} {v w : E}
    (hu : Tendsto u atTop (𝓝 v)) (h0 : ∀ k, inner ℂ (u k) w = 0) :
    inner ℂ v w = 0 := by
  have hlim : Tendsto (fun k => ‖u k - v‖ * ‖w‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_iff_norm_sub_tendsto_zero.1 hu).mul_const ‖w‖
  have hle : ∀ k, ‖inner ℂ v w‖ ≤ ‖u k - v‖ * ‖w‖ := fun k => by
    calc ‖inner ℂ v w‖ = ‖inner ℂ (v - u k) w‖ := by rw [inner_sub_left, h0 k, sub_zero]
      _ ≤ ‖v - u k‖ * ‖w‖ := norm_inner_le_norm _ _
      _ = ‖u k - v‖ * ‖w‖ := by rw [norm_sub_rev]
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)

private theorem isPhaseTest_phaseGen {P : ℝ} (ν ε : ℝ) {ψ : ℝ × Space → CVec3}
    (hψ : IsPhaseTest P ψ) : IsPhaseTest P (phaseGen ν ε ψ) := by
  have h : phaseGen ν ε ψ =
      (ν * ε ^ 2) • lapT ψ + (1 / 2 : ℝ) • radialT ψ + (1 / 2 : ℝ) • ψ - dτ ψ := by
    funext q
    rfl
  rw [h]
  exact (((hψ.lapT.const_smul (ν * ε ^ 2)).add (hψ.radialT.const_smul (1 / 2 : ℝ))).add
    (hψ.const_smul (1 / 2 : ℝ))).sub hψ.dτ

private theorem phaseGen_eq_neg (ν ε : ℝ) (ψ : ℝ × Space → CVec3) :
    phaseGen ν ε ψ = -(B0005.T0op ψ - nuLapT (ν * ε ^ 2) ψ - (1 / 2 : ℂ) • ψ) := by
  funext p
  simp only [phaseGen, B0005.T0op, nuLapT, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply,
    smul_half_complex]
  abel

private theorem ae_haar_of_ae_pspace {P : ℝ} [Fact (0 < P)]
    {g : ℝ × Space → CVec3} {Ψ : X SpaceC P}
    (hΨ : (Ψ : PSpace P → SpaceC) =ᵐ[volume]
      fun z => g ((toCell P z).2, (toCell P z).1)) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ᵐ y ∂(volume : Measure Space),
      (Ψ : PSpace P → SpaceC) (y, τ) = g ((toCell P (y, τ)).2, y) := by
  have hP : (0 : ℝ) < P := Fact.out
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × Space → Space × AddCircle P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure Space))
      (volume : Measure (PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hΨ_prod : ∀ᵐ w ∂((volume : Measure (AddCircle P)).prod (volume : Measure Space)),
      (Ψ : PSpace P → SpaceC) (w.2, w.1) = g ((toCell P (w.2, w.1)).2, w.2) := by
    filter_upwards [hsw.quasiMeasurePreserving.ae hΨ] with w hw
    exact hw
  have hμ : (volume : Measure (AddCircle P)).prod (volume : Measure Space) =
      ENNReal.ofReal P • ((AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.prod_smul_left]
  rw [hμ] at hΨ_prod
  exact Measure.ae_ae_of_ae_prod
    ((Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP).ne').1 hΨ_prod)

private theorem testElem_two_ae {P : ℝ} [Fact (0 < P)] {g : ℝ × Space → CVec3}
    (hg : IsPhaseTest P g) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      (testElem P 2 g : AddCircle P → Lp CVec3 2 (volume : Measure Space)) τ =
        sliceMap (hg.isSliceTest 2).2
          ((AddCircle.measurableEquivIoc P 0 τ : Ioc (0 : ℝ) (0 + P)) : ℝ) := by
  have hsG : IsSliceTest P 2 g := hg.isSliceTest 2
  rw [testElem_of hsG]
  filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
    (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsG)] with τ hcsτ
  rw [hcsτ]
  set t : ℝ := ((AddCircle.measurableEquivIoc P 0 τ : Ioc (0 : ℝ) (0 + P)) : ℝ)
  have ht : (t : AddCircle P) = τ := AddCircle.coe_equivIoc
  rw [← ht, circleSlice_coe]

private theorem phaseLift_one_eq_testElem {P : ℝ} [Fact (0 < P)]
    {U : X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : N01.IsPhaseLift 1 P U)
    {g : ℝ × Space → CVec3} (hg : IsPhaseTest P g)
    {Ψ : X SpaceC P}
    (hΨ : (Ψ : PSpace P → SpaceC) =ᵐ[volume]
      fun z => g ((toCell P z).2, (toCell P z).1)) :
    U Ψ = ((Real.sqrt P : ℝ) : ℂ) • testElem P 2 g := by
  have hsG : IsSliceTest P 2 g := hg.isSliceTest 2
  apply Lp.ext
  filter_upwards [hU Ψ, ae_haar_of_ae_pspace hΨ,
    Lp.coeFn_smul (((Real.sqrt P : ℝ) : ℂ)) (testElem P 2 g),
    testElem_two_ae hg] with τ hUτ hΨτ hsmτ hteτ
  rw [hsmτ, Pi.smul_apply, hteτ]
  set t : ℝ := ((AddCircle.measurableEquivIoc P 0 τ : Ioc (0 : ℝ) (0 + P)) : ℝ)
  apply Lp.ext
  filter_upwards [hUτ, hΨτ,
    Lp.coeFn_smul (((Real.sqrt P : ℝ) : ℂ)) (sliceMap hsG.2 t),
    MemLp.coeFn_toLp (hsG.2.memLp t)] with y hy1 hy2 hy3 hy4
  have htc : (toCell P (y, τ)).2 = t := rfl
  rw [hy1, one_smul, Real.one_rpow, mul_one, hy2, htc, hy3, Pi.smul_apply]
  unfold sliceMap
  rw [hy4]

private def bodyCombo {P : ℝ} [Fact (0 < P)] (μ : ℂ) (x : Yq P 2 × Yq P 2 × Yq P 2) : Yq P 2 :=
  μ • x.1 + (x.2.1 - x.2.2 - (1 / 2 : ℂ) • x.1)

private theorem continuous_bodyCombo {P : ℝ} [Fact (0 < P)] (μ : ℂ) :
    Continuous (bodyCombo (P := P) μ) :=
  (continuous_fst.const_smul μ).add
    (((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)).sub
      (continuous_fst.const_smul (1 / 2 : ℂ)))

private theorem bodyCombo_phaseTest_eq {P : ℝ} [Fact (0 < P)] (ν ε : ℝ) (μ : ℂ)
    {ψ : ℝ × Space → CVec3} (hψ : IsPhaseTest P ψ) :
    bodyCombo μ (testElem P 2 ψ, testElem P 2 (B0005.T0op ψ),
        testElem P 2 (nuLapT (ν * ε ^ 2) ψ)) =
      μ • testElem P 2 ψ - testElem P 2 (phaseGen ν ε ψ) := by
  have hs0 : IsSliceTest P 2 ψ := hψ.isSliceTest 2
  have hsT : IsSliceTest P 2 (B0005.T0op ψ) := isSliceTest_T0op hs0 (hψ.driftT.isSliceTest 2)
  have hsL : IsSliceTest P 2 (nuLapT (ν * ε ^ 2) ψ) :=
    isSliceTest_nuLapT (hψ.lapT.isSliceTest 2) (ν * ε ^ 2)
  rw [phaseGen_eq_neg,
    testElem_neg (isSliceTest_sub' (isSliceTest_sub' hsT hsL) (hs0.const_smul _)),
    testElem_sub' (isSliceTest_sub' hsT hsL) (hs0.const_smul _),
    testElem_sub' hsT hsL, testElem_const_smul hs0, sub_neg_eq_add]
  rfl

private theorem inner_schwartz_eq_zero {P : ℝ} [Fact (0 < P)] (ν' : ℝ) (μ : ℂ) (W : Yq P 2)
    (hpt : ∀ G : ℝ × Space → CVec3, IsPhaseTest P G →
      inner ℂ (bodyCombo μ (testElem P 2 G, testElem P 2 (B0005.T0op G),
        testElem P 2 (nuLapT ν' G))) W = 0)
    {Ψs : ℝ × Space → CVec3} (hΨs : IsPhaseSchwartz P 2 Ψs) :
    inner ℂ (bodyCombo μ (testElem P 2 Ψs, testElem P 2 (B0005.T0op Ψs),
      testElem P 2 (nuLapT ν' Ψs))) W = 0 := by
  obtain ⟨seq, hseq_mem, hseq_lim⟩ :=
    mem_closure_iff_seq_limit.1 (schwartz_triple_mem_closure ν' hΨs)
  refine inner_eq_zero_of_tendsto ((continuous_bodyCombo μ).continuousAt.tendsto.comp hseq_lim)
    fun k => ?_
  obtain ⟨G, hG, hGk⟩ := hseq_mem k
  rw [Function.comp_apply, hGk]
  exact hpt G hG

private theorem bodyCombo_truncRes_eq {P : ℝ} [Fact (0 < P)] {ν' : ℝ} (hν' : 0 < ν') (μ : ℂ)
    {f : ℝ × Space → CVec3} (hf : IsPhaseTest P f) {M : ℝ} (hM : 0 ≤ M) :
    bodyCombo μ (testElem P 2 (truncRes ν' μ M f),
        testElem P 2 (B0005.T0op (truncRes ν' μ M f)),
        testElem P 2 (nuLapT ν' (truncRes ν' μ M f))) =
      testElem P 2 f - testElem P 2 (fwdIntegrand ν' μ f M) := by
  have hP : 0 < P := Fact.out
  have hs : IsPhaseSchwartz P 2 (truncRes ν' μ M f) :=
    truncResSchwartz_of fwdIntegrandRegular fwdIntegrandDecay P ν' hP hν' μ f hf M hM
  have h1 : IsSliceTest P 2 (truncRes ν' μ M f) := hs.sliceTest
  have hT' : IsSliceTest P 2 (B0005.T0op (truncRes ν' μ M f)) :=
    isSliceTest_T0op hs.sliceTest hs.sliceTest_driftT
  have hL' : IsSliceTest P 2 (nuLapT ν' (truncRes ν' μ M f)) :=
    isSliceTest_nuLapT hs.sliceTest_lapT ν'
  have hrem : IsSliceTest P 2 (fwdIntegrand ν' μ f M) :=
    (fwdRemainderBound P ν' hν' μ f hf M hM).1
  have hfun : μ • truncRes ν' μ M f +
      (B0005.T0op (truncRes ν' μ M f) - nuLapT ν' (truncRes ν' μ M f) -
        (1 / 2 : ℂ) • truncRes ν' μ M f) =
      f - fwdIntegrand ν' μ f M := by
    funext p
    have h := truncResEquation_of fwdIntegrandRegular fwdIntegrandDeriv fwdIntegrandCont
      P ν' hP hν' μ f hf M hM p
    simp only [L0, T0] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, B0005.T0op, nuLapT, smul_half_complex]
    exact h
  rw [bodyCombo, ← testElem_const_smul h1 μ, ← testElem_const_smul h1 (1 / 2 : ℂ),
    ← testElem_sub' hT' hL',
    ← testElem_sub' (isSliceTest_sub' hT' hL') (h1.const_smul (1 / 2 : ℂ)),
    ← testElem_add (h1.const_smul μ)
      (isSliceTest_sub' (isSliceTest_sub' hT' hL') (h1.const_smul (1 / 2 : ℂ))),
    hfun, testElem_sub' (hf.isSliceTest 2) hrem]

end OuterCoreAux

/-- **`PartII-a:N04/3/3/2/1`**: smooth `P`-periodic bounded-support phase tests are a core for
the outer generator on `X SpaceC P` (`Re μ > -1/4`). -/
theorem outerPhaseTestCoreDense : OuterPhaseTestCoreDense := by
  intro ν ε hν hε P _ μ hγ Z horth
  open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 OuterCoreAux in
  have hP : (0 : ℝ) < P := Fact.out
  set ν' : ℝ := ν * ε ^ 2
  have hν' : 0 < ν' := by positivity
  obtain ⟨U, hU⟩ := N01.phaseLiftExists 1 P zero_lt_one
  have hpt : ∀ ψ : ℝ × Space → CVec3, IsPhaseTest P ψ →
      inner ℂ (bodyCombo μ (testElem P 2 ψ, testElem P 2 (B0005.T0op ψ),
        testElem P 2 (nuLapT ν' ψ))) (U Z) = 0 := by
    intro ψ hψ
    have hψ' : IsPhaseTest P (phaseGen ν ε ψ) := isPhaseTest_phaseGen ν ε hψ
    obtain ⟨Ψ, hΨ⟩ := OuterSGen.exists_rep ψ hψ.continuous hψ.periodic hψ.bounded_support
    obtain ⟨Ψ', hΨ'⟩ := OuterSGen.exists_rep (phaseGen ν ε ψ)
      hψ'.continuous hψ'.periodic hψ'.bounded_support
    have h0 : inner ℂ (U (μ • Ψ - Ψ')) (U Z) = 0 := by
      rw [U.inner_map_map]
      exact horth ψ hψ Ψ Ψ' hΨ hΨ'
    have hUsub : U (μ • Ψ - Ψ') =
        ((Real.sqrt P : ℝ) : ℂ) •
          bodyCombo μ (testElem P 2 ψ, testElem P 2 (B0005.T0op ψ),
            testElem P 2 (nuLapT ν' ψ)) := by
      rw [bodyCombo_phaseTest_eq ν ε μ hψ, map_sub, map_smul,
        phaseLift_one_eq_testElem hU hψ hΨ, phaseLift_one_eq_testElem hU hψ' hΨ',
        smul_sub, smul_comm μ]
    rw [hUsub, inner_smul_left] at h0
    have hc_ne : starRingEnd ℂ ((Real.sqrt P : ℝ) : ℂ) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hP).ne')
    exact (mul_eq_zero.1 h0).resolve_left hc_ne
  have htest_zero : ∀ f : ℝ × Space → CVec3, IsPhaseTest P f →
      inner ℂ (testElem P 2 f) (U Z) = 0 := by
    intro f hf
    have hn_zero : ∀ n : ℕ,
        inner ℂ (testElem P 2 f - testElem P 2 (fwdIntegrand ν' μ f (n : ℝ))) (U Z) = 0 := by
      intro n
      have hM : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hs : IsPhaseSchwartz P 2 (truncRes ν' μ (n : ℝ) f) :=
        truncResSchwartz_of fwdIntegrandRegular fwdIntegrandDecay P ν' hP hν' μ f hf (n : ℝ) hM
      rw [← bodyCombo_truncRes_eq hν' μ hf hM]
      exact inner_schwartz_eq_zero ν' μ (U Z) hpt hs
    have hrem_tendsto : Tendsto
        (fun n : ℕ => testElem P 2 f - testElem P 2 (fwdIntegrand ν' μ f (n : ℝ)))
        atTop (𝓝 (testElem P 2 f)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hexp : Tendsto (fun n : ℕ =>
          Real.exp (-(μ.re + 1 / 4) * (n : ℝ)) * ‖testElem P 2 f‖) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => -(μ.re + 1 / 4) * (n : ℝ)) atTop atBot :=
          (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.2 hγ))
        simpa only [zero_mul, Function.comp_def] using
          (Real.tendsto_exp_atBot.comp h1).mul_const ‖testElem P 2 f‖
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
        (fun _ => norm_nonneg _) fun n => ?_
      have hsub_eq : (testElem P 2 f - testElem P 2 (fwdIntegrand ν' μ f (n : ℝ))) -
          testElem P 2 f = -testElem P 2 (fwdIntegrand ν' μ f (n : ℝ)) := by abel
      rw [hsub_eq, norm_neg]
      exact (fwdRemainderBound P ν' hν' μ f hf (n : ℝ) (Nat.cast_nonneg n)).2
    exact OuterCoreAux.inner_eq_zero_of_tendsto hrem_tendsto hn_zero
  obtain ⟨G, hG, hG_lim⟩ := phaseTestsDenseY2 P (U Z)
  have hUZ0 : inner ℂ (U Z) (U Z) = 0 :=
    OuterCoreAux.inner_eq_zero_of_tendsto hG_lim fun n => htest_zero (G n) (hG n)
  exact U.injective ((inner_self_eq_zero.1 hUZ0).trans U.map_zero.symm)

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.outerPhaseTestCoreDense
