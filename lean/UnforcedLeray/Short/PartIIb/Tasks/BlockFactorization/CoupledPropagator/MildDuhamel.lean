import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.MildDuhamel.AcCont
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.MildDuhamel.PropCont
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# `PartII-b:F2/2/1` (`MildDuhamel.lean`): Mild Volterra/Duhamel evolution family on `Xmc p.c m`

Source of record: `the November 2 reference manuscript` (SP), lines 2076–2083,
2147–2155.

Proves `mildDuhamelEvolutionStep_proof : UnforcedLeray.Short.IIb.MildDuhamelEvolutionStep` using:
1. Strong time-continuity `ContinuousOn (fun r => Ac r w) (Icc 0 p.H)` (`MildDuhamel/AcCont.lean`),
2. Right-grid Bochner integrability and final-time continuity of Duhamel integrals
   (`MildDuhamel/PropCont.lean`, built on `PartIIbF4Aux.integrableOn_propagator_apply`),
3. Real Dyson-series summation (`UnforcedLeray.Short.IIb.RCDuhamel.exists_isDysonSum`) applied to
   the rescaled propagator `Sc' t s = e^{-K₀(t-s)} • Sc t s` (`‖Sc' t s‖ ≤ 1`),
4. Uniform convergence of the continuous Dyson iterates for `strongCont`, and Gronwall uniqueness
   (`B0104.gronwall_family`) on `[r, p.H]` for `comp_cocycle`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal Nat

namespace UnforcedLeray.Short.IIb.MildDuhamelAux

open UnforcedLeray.Cons.C03.Concrete

theorem exists_mildDuhamelPropagator
    {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    (hAge : p.ageCut = Sig) {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (hTCM : TrainCloseM m p.train Sig δ)
    {K₀ : ℝ} {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)} (hK₀ : 0 < K₀)
    (hSc : IsFreeCylPropagator m p Sc)
    (hSc_bd : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s)))
    {M_A : ℝ} {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)} (hMA : 0 ≤ M_A)
    (hAc : ∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s) ∧ ‖Ac s‖ ≤ M_A) :
    ∃ U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m),
      IsMildDuhamelPropagator m p K₀ M_A Sc Ac U := by
  have hH_nn : 0 ≤ p.H := by
    rw [Params.H, hAge]
    exact div_nonneg hSig.le p.ν_pos.le
  have hAc_cont : ∀ w : Xmc p.c m, ContinuousOn (fun r => Ac r w) (Icc 0 p.H) :=
    continuousOn_Ac_apply hm hSig hbg hν1 hAge hδ0 hTCM (fun s hs => (hAc s hs).1)
  -- 1. Rescaled free propagator `Sc' t s = e^{-K₀(t-s)} • Sc t s` with `‖Sc' t s‖ ≤ 1`
  let Sc' : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m) :=
    fun t s => Real.exp (-K₀ * (t - s)) • Sc t s
  have hSc'_id : ∀ r ∈ Icc 0 p.H, Sc' r r = ContinuousLinearMap.id ℝ (Xmc p.c m) := by
    intro r hr
    dsimp [Sc']
    rw [sub_self, mul_zero, Real.exp_zero, one_smul, hSc.id_self r hr]
  have hSc'_coc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ p.H →
      (Sc' c b).comp (Sc' b a) = Sc' c a := by
    intro a b c ha hab hbc hc
    ext1 y
    simp only [Sc', ContinuousLinearMap.comp_apply, smul_apply,
      map_smul, smul_smul, ← Real.exp_add]
    have hexp : -K₀ * (b - a) + -K₀ * (c - b) = -K₀ * (c - a) := by ring
    rw [hexp, ← ContinuousLinearMap.comp_apply, hSc.comp_cocycle a b c ha hab hbc hc]
  have hSc'_cont : ∀ a ∈ Icc 0 p.H, ∀ y : Xmc p.c m,
      ContinuousOn (fun b => Sc' b a y) (Icc a p.H) := by
    intro a ha y
    have hscalar : ContinuousOn (fun b : ℝ => Real.exp (-K₀ * (b - a))) (Icc a p.H) :=
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
    exact hscalar.smul (hSc.strongCont a ha y)
  have hSc'_bd : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ p.H → ‖Sc' b a‖ ≤ 1 := by
    intro a b ha hab hb
    dsimp [Sc']
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-K₀ * (b - a)) * ‖Sc b a‖
        ≤ Real.exp (-K₀ * (b - a)) * Real.exp (K₀ * (b - a)) :=
          mul_le_mul_of_nonneg_left (hSc_bd a b ha hab hb) (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          have h0 : -K₀ * (b - a) + K₀ * (b - a) = 0 := by ring
          rw [h0, Real.exp_zero]
  -- 2. Clamped window extensions for `RCDuhamel` (`ι = Unit`, `B = p.H`, `M = 1`, `K = M_A`)
  let F : Unit → ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m) :=
    RCDuhamel.extW 0 p.H (fun _ => Sc')
  let A : Unit → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m) :=
    RCDuhamel.extA 0 p.H (fun _ => Ac)
  have hF_bd : ∀ (u : Unit) t s, s ≤ t → t ≤ s + p.H → ‖F u t s‖ ≤ 1 := by
    intro _ t s hst _
    exact hSc'_bd _ _ (RCDuhamel.le_clampW 0 p.H s) (RCDuhamel.clampW_mono hst)
      (RCDuhamel.clampW_le hH_nn t)
  have hA_bd : ∀ (u : Unit) r, ‖A u r‖ ≤ M_A :=
    RCDuhamel.extA_norm_le hMA (fun _ r hr => (hAc r hr).2)
  have hclamp_idem : ∀ y : ℝ,
      RCDuhamel.clampW 0 p.H (RCDuhamel.clampW 0 p.H y) = RCDuhamel.clampW 0 p.H y :=
    fun y => RCDuhamel.clampW_of_mem (RCDuhamel.le_clampW 0 p.H y) (RCDuhamel.clampW_le hH_nn y)
  -- 3. Continuity and clamping invariance of every Dyson iterate `dysonTerm F A k`
  have hIter : ∀ k : ℕ,
      (∀ s ∈ Icc 0 p.H, ∀ x : Xmc p.c m,
        ContinuousOn (fun t => RCDuhamel.dysonTerm F A k () t s x) (Icc s p.H)) ∧
      (∀ s t : ℝ, s ≤ t → ∀ x : Xmc p.c m,
        RCDuhamel.dysonTerm F A k () t s x =
          RCDuhamel.dysonTerm F A k ()
            (RCDuhamel.clampW 0 p.H t) (RCDuhamel.clampW 0 p.H s) x) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro s hs x
        refine (hSc'_cont s hs x).congr fun t ht => ?_
        simp only [RCDuhamel.dysonTerm, F, RCDuhamel.extW,
          RCDuhamel.clampW_of_mem hs.1 hs.2,
          RCDuhamel.clampW_of_mem (hs.1.trans ht.1) ht.2]
      · intro s t _hst x
        simp only [RCDuhamel.dysonTerm, F, RCDuhamel.extW, hclamp_idem]
    | succ k ih =>
      obtain ⟨ih_cont, ih_clamp⟩ := ih
      have h_eq_ind : ∀ s t : ℝ, s ≤ t → ∀ x : Xmc p.c m, ∀ r ∈ Icc s t,
          F () t r (A () r (RCDuhamel.dysonTerm F A k () r s x)) =
            (Icc 0 p.H).indicator
              (fun r => Sc' (RCDuhamel.clampW 0 p.H t) r
                (Ac r (RCDuhamel.dysonTerm F A k () r (RCDuhamel.clampW 0 p.H s) x))) r := by
        intro s t _hst x r hr_st
        by_cases hr : r ∈ Icc 0 p.H
        · simp only [F, A, RCDuhamel.extW, RCDuhamel.extA, Set.indicator_of_mem hr,
            RCDuhamel.clampW_of_mem hr.1 hr.2]
          rw [ih_clamp s r hr_st.1 x, RCDuhamel.clampW_of_mem hr.1 hr.2]
        · simp only [A, RCDuhamel.extA, Set.indicator_of_notMem hr,
            zero_apply, map_zero]
      have h_clamp_eq : ∀ s t : ℝ, s ≤ t → ∀ x : Xmc p.c m,
          RCDuhamel.dysonTerm F A (k + 1) () t s x =
            ∫ r in RCDuhamel.clampW 0 p.H s..RCDuhamel.clampW 0 p.H t,
              Sc' (RCDuhamel.clampW 0 p.H t) r
                (Ac r (RCDuhamel.dysonTerm F A k () r (RCDuhamel.clampW 0 p.H s) x)) := by
        intro s t hst x
        show (∫ r in s..t, F () t r (A () r (RCDuhamel.dysonTerm F A k () r s x))) = _
        have hcongr :
            (∫ r in s..t, F () t r (A () r (RCDuhamel.dysonTerm F A k () r s x))) =
              ∫ r in s..t, (Icc 0 p.H).indicator
                (fun r => Sc' (RCDuhamel.clampW 0 p.H t) r
                  (Ac r (RCDuhamel.dysonTerm F A k () r (RCDuhamel.clampW 0 p.H s) x))) r := by
          refine intervalIntegral.integral_congr fun r hr => ?_
          rw [uIcc_of_le hst] at hr
          exact h_eq_ind s t hst x r hr
        rw [hcongr, RCDuhamel.integral_indicator_Icc_eq hH_nn hst]
      refine ⟨?_, ?_⟩
      · intro s hs x
        have hg_cont : ContinuousOn
            (fun r => Ac r (RCDuhamel.dysonTerm F A k () r s x)) (Icc s p.H) :=
          continuousOn_op_apply_of_norm_le hs hAc_cont (fun r hr => (hAc r hr).2)
            (ih_cont s hs x)
        have hint_cont := continuousOn_propagator_intervalIntegral hs zero_le_one
          hSc'_id hSc'_coc hSc'_cont hSc'_bd hg_cont
        refine hint_cont.congr fun t ht => ?_
        rw [h_clamp_eq s t ht.1 x,
          RCDuhamel.clampW_of_mem hs.1 hs.2,
          RCDuhamel.clampW_of_mem (hs.1.trans ht.1) ht.2]
      · intro s t hst x
        rw [h_clamp_eq s t hst x,
          h_clamp_eq (RCDuhamel.clampW 0 p.H s) (RCDuhamel.clampW 0 p.H t)
            (RCDuhamel.clampW_mono hst) x]
        simp only [hclamp_idem]
  -- 4. `DysonDefined p.H F A`
  have hDysonDef : RCDuhamel.DysonDefined p.H F A := by
    intro k u s t hst _hts x
    cases u
    set s' : ℝ := RCDuhamel.clampW 0 p.H s
    set t' : ℝ := RCDuhamel.clampW 0 p.H t
    have hs'_mem : s' ∈ Icc 0 p.H :=
      ⟨RCDuhamel.le_clampW 0 p.H s, RCDuhamel.clampW_le hH_nn s⟩
    have ht'_mem : t' ∈ Icc s' p.H :=
      ⟨RCDuhamel.clampW_mono hst, RCDuhamel.clampW_le hH_nn t⟩
    have hg_cont : ContinuousOn
        (fun r => Ac r (RCDuhamel.dysonTerm F A k () r s' x)) (Icc s' p.H) :=
      continuousOn_op_apply_of_norm_le hs'_mem hAc_cont (fun r hr => (hAc r hr).2)
        ((hIter k).1 s' hs'_mem x)
    have hg_ii : IntervalIntegrable
        (fun r => Ac r (RCDuhamel.dysonTerm F A k () r s' x)) volume s' t' :=
      (hg_cont.mono (Icc_subset_Icc_right ht'_mem.2)).intervalIntegrable_of_Icc ht'_mem.1
    have hwin_ii : IntervalIntegrable
        (fun r => Sc' t' r (Ac r (RCDuhamel.dysonTerm F A k () r s' x))) volume s' t' :=
      intervalIntegrable_propagator_apply hs'_mem.1 ht'_mem.1 le_rfl ht'_mem.2 zero_le_one
        hSc'_id hSc'_coc hSc'_cont hSc'_bd hg_ii
    have hind_ii := RCDuhamel.intervalIntegrable_indicator_Icc (a := 0) (b := p.H) hst hwin_ii
    refine hind_ii.congr fun r hr => ?_
    rw [uIoc_of_le hst] at hr
    by_cases hr_0H : r ∈ Icc 0 p.H
    · simp only [F, A, RCDuhamel.extW, RCDuhamel.extA, Set.indicator_of_mem hr_0H,
        RCDuhamel.clampW_of_mem hr_0H.1 hr_0H.2, s', t']
      rw [(hIter k).2 s r hr.1.le x, RCDuhamel.clampW_of_mem hr_0H.1 hr_0H.2]
    · simp only [A, RCDuhamel.extA, Set.indicator_of_notMem hr_0H,
        zero_apply, map_zero]
  -- 5. Sum Dyson series and rescale back `U t s = e^{K₀(t-s)} • U_ext () t s`
  obtain ⟨U_ext, hDyson⟩ := RCDuhamel.exists_isDysonSum hF_bd hA_bd hDysonDef
  have hEvo := hDyson.isDuhamelEvolution hF_bd hA_bd hDysonDef
  let U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m) :=
    fun t s => Real.exp (K₀ * (t - s)) • U_ext () t s
  -- 6. Verify all fields of `IsMildDuhamelPropagator`
  have hU_norm : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
      ‖U t s‖ ≤ Real.exp ((K₀ + M_A) * (t - s)) := by
    intro s t hs hst ht
    have hts : t ≤ s + p.H := by linarith
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
    dsimp [U]
    rw [smul_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 := hDyson.norm_apply_le hF_bd hA_bd (p := ()) hst hts x
    calc Real.exp (K₀ * (t - s)) * ‖U_ext () t s x‖
        ≤ Real.exp (K₀ * (t - s)) * (1 * Real.exp (1 * M_A * (t - s)) * ‖x‖) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = (Real.exp (K₀ * (t - s)) * Real.exp (M_A * (t - s))) * ‖x‖ := by
          rw [one_mul, one_mul]; ring
      _ = Real.exp ((K₀ + M_A) * (t - s)) * ‖x‖ := by
          rw [← Real.exp_add]
          congr 2
          ring
  have h_integrand_rescale : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
      ∀ f : Xmc p.c m, ∀ r ∈ Icc s t,
        Sc t r (Ac r (U r s f)) =
          Real.exp (K₀ * (t - s)) • F () t r (A () r (U_ext () r s f)) := by
    intro s t hs _hst ht f r hr
    have hr_0H : r ∈ Icc 0 p.H := ⟨hs.trans hr.1, hr.2.trans ht⟩
    have ht_0H : t ∈ Icc 0 p.H := ⟨hr_0H.1.trans hr.2, ht⟩
    simp only [F, A, RCDuhamel.extW, RCDuhamel.extA, Set.indicator_of_mem hr_0H,
      RCDuhamel.clampW_of_mem hr_0H.1 hr_0H.2, RCDuhamel.clampW_of_mem ht_0H.1 ht_0H.2,
      Sc', U, smul_apply, map_smul, smul_smul, ← Real.exp_add]
    have hexp : K₀ * (t - s) + -K₀ * (t - r) = K₀ * (r - s) := by ring
    rw [hexp]
  have hU_int : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
      IntervalIntegrable (fun r => Sc t r (Ac r (U r s f))) volume s t := by
    intro s t hs hst ht f
    have hts : t ≤ s + p.H := by linarith
    have hii := (hEvo.integrable () s t hst hts f).smul (Real.exp (K₀ * (t - s)))
    refine hii.congr fun r hr => ?_
    rw [uIoc_of_le hst] at hr
    exact (h_integrand_rescale s t hs hst ht f r ⟨hr.1.le, hr.2⟩).symm
  have hU_duhamel : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
      U t s f = Sc t s f + ∫ r in s..t, Sc t r (Ac r (U r s f)) := by
    intro s t hs hst ht f
    have hts : t ≤ s + p.H := by linarith
    have hd := congrArg (fun z : Xmc p.c m => Real.exp (K₀ * (t - s)) • z)
      (hEvo.duhamel () s t hst hts f)
    dsimp [U]
    rw [smul_apply, hd, smul_add,
      ← intervalIntegral.integral_smul]
    have h1 : Real.exp (K₀ * (t - s)) • F () t s f = Sc t s f := by
      simp only [F, RCDuhamel.extW,
        RCDuhamel.clampW_of_mem hs (hst.trans ht),
        RCDuhamel.clampW_of_mem (hs.trans hst) ht,
        Sc', smul_apply, smul_smul, ← Real.exp_add]
      have h0 : K₀ * (t - s) + -K₀ * (t - s) = 0 := by ring
      rw [h0, Real.exp_zero, one_smul]
    rw [h1]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hst] at hr
    exact (h_integrand_rescale s t hs hst ht f r hr).symm
  have hU_id : ∀ s ∈ Icc 0 p.H, U s s = ContinuousLinearMap.id ℝ (Xmc p.c m) := by
    intro s hs
    ext1 f
    rw [hU_duhamel s s hs.1 le_rfl hs.2 f, intervalIntegral.integral_same, add_zero,
      hSc.id_self s hs]
  have hU_cont : ∀ s ∈ Icc 0 p.H, ∀ f : Xmc p.c m,
      ContinuousOn (fun t => U t s f) (Icc s p.H) := by
    intro s hs f
    let maj : ℕ → ℝ := fun k => 1 * ((1 * M_A * p.H) ^ k / (k ! : ℝ)) * ‖f‖
    have hmaj_sum : Summable maj := (RCDuhamel.hasSum_majorant 1 M_A p.H ‖f‖).summable
    have hmaj_bd : ∀ (k : ℕ) (t : ℝ), t ∈ Icc s p.H →
        ‖RCDuhamel.dysonTerm F A k () t s f‖ ≤ maj k := by
      intro k t ht
      have hts : t ≤ s + p.H := by linarith [hs.1, ht.2]
      refine (RCDuhamel.norm_dysonTerm_le hF_bd hA_bd k () t s ht.1 hts f).trans ?_
      dsimp [maj]
      have hpow : (1 * M_A * (t - s)) ^ k ≤ (1 * M_A * p.H) ^ k :=
        pow_le_pow_left₀ (by linarith [sub_nonneg.2 ht.1, mul_nonneg hMA (sub_nonneg.2 ht.1)])
          (by nlinarith [hs.1, ht.2, hMA]) k
      have hdiv : (1 * M_A * (t - s)) ^ k / (k ! : ℝ) ≤ (1 * M_A * p.H) ^ k / (k ! : ℝ) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv zero_le_one) (norm_nonneg _)
    have htsum_cont : ContinuousOn
        (fun t => ∑' k : ℕ, RCDuhamel.dysonTerm F A k () t s f) (Icc s p.H) :=
      continuousOn_tsum (fun k => (hIter k).1 s hs f) hmaj_sum hmaj_bd
    have hUext_cont : ContinuousOn (fun t => U_ext () t s f) (Icc s p.H) := by
      refine htsum_cont.congr fun t ht => ?_
      exact (hDyson () t s ht.1 (by linarith [hs.1, ht.2]) f).tsum_eq.symm
    have hscalar : ContinuousOn (fun t : ℝ => Real.exp (K₀ * (t - s))) (Icc s p.H) :=
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
    exact hscalar.smul hUext_cont
  have hU_coc : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ p.H →
      (U t r).comp (U r s) = U t s := by
    intro s r t hs hsr hrt ht
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    let v₁ : ℝ → Xmc p.c m := fun τ => U τ r (U r s f)
    let v₂ : ℝ → Xmc p.c m := fun τ => U τ s f
    have hv₂_eq : ∀ τ : ℝ, r ≤ τ → τ ≤ p.H →
        IntervalIntegrable (fun θ => Sc τ θ (Ac θ (v₂ θ))) volume r τ ∧
        v₂ τ = Sc τ r (U r s f) + ∫ θ in r..τ, Sc τ θ (Ac θ (v₂ θ)) := by
      intro τ hrτ hτH
      have h_sτ := hU_int s τ hs (hsr.trans hrτ) hτH f
      have h_rτ : IntervalIntegrable (fun θ => Sc τ θ (Ac θ (v₂ θ))) volume r τ := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrτ]
        exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (hsr.trans hrτ)).1 h_sτ).mono_set
          (Ioc_subset_Ioc_left hsr)
      have h_sr_r := hU_int s r hs hsr (hrτ.trans hτH) f
      have h_sr_comp : IntervalIntegrable
          (fun θ => Sc τ r (Sc r θ (Ac θ (v₂ θ)))) volume s r := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hsr] at h_sr_r ⊢
        exact (Sc τ r).integrable_comp h_sr_r
      have h_sr_τ : IntervalIntegrable (fun θ => Sc τ θ (Ac θ (v₂ θ))) volume s r := by
        refine h_sr_comp.congr fun θ hθ => ?_
        rw [uIoc_of_le hsr] at hθ
        rw [← ContinuousLinearMap.comp_apply,
          hSc.comp_cocycle θ r τ (hs.trans hθ.1.le) hθ.2 hrτ hτH]
      have h_adj : (∫ θ in s..τ, Sc τ θ (Ac θ (v₂ θ))) =
          (∫ θ in s..r, Sc τ θ (Ac θ (v₂ θ))) + (∫ θ in r..τ, Sc τ θ (Ac θ (v₂ θ))) :=
        (intervalIntegral.integral_add_adjacent_intervals h_sr_τ h_rτ).symm
      have h_Sc_Urs : Sc τ r (U r s f) =
          Sc τ s f + ∫ θ in s..r, Sc τ θ (Ac θ (v₂ θ)) := by
        rw [hU_duhamel s r hs hsr (hrτ.trans hτH) f, map_add,
          ← (Sc τ r).intervalIntegral_comp_comm (hU_int s r hs hsr (hrτ.trans hτH) f),
          ← ContinuousLinearMap.comp_apply,
          hSc.comp_cocycle s r τ hs hsr hrτ hτH]
        congr 1
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le hsr] at hθ
        rw [← ContinuousLinearMap.comp_apply,
          hSc.comp_cocycle θ r τ (hs.trans hθ.1) hθ.2 hrτ hτH]
      refine ⟨h_rτ, ?_⟩
      dsimp [v₂]
      rw [hU_duhamel s τ hs (hsr.trans hrτ) hτH f, h_adj, h_Sc_Urs, add_assoc]
    set M_Sc : ℝ := Real.exp (K₀ * p.H)
    set C_U : ℝ := Real.exp ((K₀ + M_A) * p.H)
    have hM_Sc_pos : 0 < M_Sc := Real.exp_pos _
    have hC_U_pos : 0 < C_U := Real.exp_pos _
    have hU_bd_all : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ p.H → ‖U b a‖ ≤ C_U := by
      intro a b ha hab hb
      refine (hU_norm a b ha hab hb).trans (Real.exp_le_exp.2 ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hSc_bd_all : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ p.H → ‖Sc b a‖ ≤ M_Sc := by
      intro a b ha hab hb
      refine (hSc_bd a b ha hab hb).trans (Real.exp_le_exp.2 ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) hK₀.le
    have G := UnforcedLeray.B0104.gronwall_family (I := Unit)
      (fun _ τ => ‖v₁ τ - v₂ τ‖) (s := r) (B := p.H - r)
      (a := 0) (L := M_Sc * M_A) (C := C_U * ‖U r s f‖ + C_U * ‖f‖)
      le_rfl (by positivity)
      (fun _ τ h1 h2 => by
        have hτH : τ ≤ p.H := by linarith
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact ((U τ r).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hU_bd_all r τ (hs.trans hsr) h1 hτH) (norm_nonneg _))
        · exact ((U τ s).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hU_bd_all s τ hs (hsr.trans h1) hτH) (norm_nonneg _)))
      (fun g hg τ h1 h2 _ hφ _ => by
        have hτH : τ ≤ p.H := by linarith
        have hv1_int : IntervalIntegrable (fun θ => Sc τ θ (Ac θ (v₁ θ))) volume r τ :=
          hU_int r τ (hs.trans hsr) h1 hτH (U r s f)
        have hv1_eq : v₁ τ = Sc τ r (U r s f) + ∫ θ in r..τ, Sc τ θ (Ac θ (v₁ θ)) :=
          hU_duhamel r τ (hs.trans hsr) h1 hτH (U r s f)
        obtain ⟨hv2_int, hv2_eq⟩ := hv₂_eq τ h1 hτH
        change ‖v₁ τ - v₂ τ‖ ≤ 0 + (M_Sc * M_A) * ∫ θ in r..τ, g θ
        rw [hv1_eq, hv2_eq, add_sub_add_left_eq_sub,
          ← intervalIntegral.integral_sub hv1_int hv2_int,
          zero_add, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.norm_integral_le_of_norm_le h1
          (Filter.Eventually.of_forall fun θ hθ => ?_)
          ((hg.const_mul _).intervalIntegrable _ _)
        have hθ_0H : θ ∈ Icc 0 p.H := ⟨(hs.trans hsr).trans hθ.1.le, hθ.2.trans hτH⟩
        rw [← map_sub, ← map_sub]
        calc ‖Sc τ θ (Ac θ (v₁ θ - v₂ θ))‖
            ≤ ‖Sc τ θ‖ * (‖Ac θ‖ * ‖v₁ θ - v₂ θ‖) :=
              ((Sc τ θ).le_opNorm _).trans
                (mul_le_mul_of_nonneg_left ((Ac θ).le_opNorm _) (norm_nonneg _))
          _ ≤ M_Sc * (M_A * ‖v₁ θ - v₂ θ‖) :=
              mul_le_mul (hSc_bd_all θ τ hθ_0H.1 hθ.2 hτH)
                (mul_le_mul_of_nonneg_right ((hAc θ hθ_0H).2) (norm_nonneg _))
                (by positivity) hM_Sc_pos.le
          _ = (M_Sc * M_A) * ‖v₁ θ - v₂ θ‖ := by ring
          _ ≤ (M_Sc * M_A) * g θ :=
              mul_le_mul_of_nonneg_left (hφ () θ hθ.1.le hθ.2) (by positivity))
      () t hrt (by linarith)
    have h0 : ‖v₁ t - v₂ t‖ ≤ 0 := by simpa using G
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  exact ⟨U, {
    id_self := hU_id
    comp_cocycle := hU_coc
    strongCont := hU_cont
    duhamel_integrable := hU_int
    duhamel_eq := hU_duhamel
    norm_le := hU_norm
  }⟩

end UnforcedLeray.Short.IIb.MildDuhamelAux

/-- **Main theorem (`PartII-b:F2/2/1`, `MildDuhamelEvolutionStep`, SP 2076–2083, 2147–2155)**:
existence of the mild Volterra/Duhamel propagator `U` on `Xmc p.c m`. -/
theorem mildDuhamelEvolutionStep_proof : UnforcedLeray.Short.IIb.MildDuhamelEvolutionStep := by
  intro m hm Sig hSig p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM K₀ Sc hK₀ hSc hSc_bd M_A Ac hMA hAc
  exact UnforcedLeray.Short.IIb.MildDuhamelAux.exists_mildDuhamelPropagator
    hm hSig hbg hν1 hAge hδ0 hδ1 hTCM hK₀ hSc hSc_bd hMA hAc
