import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_1_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_R06
import UnforcedLeray.Short.PartI.Sub.PartI_T22_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap

/-!
# Fixed-parameter weighted mixed-derivative decay of `meanStress` (`PartII-b:S2/wtd/mean` helper)

Source of record: `the November 2 reference manuscript` (SP), lines 429–446 and
516–551.

Deduces fixed-threshold (`ν₀` depending only on `ρ > 1/2`), all-weight, all-order exponential decay
for `(1 + η ^ 2) ^ k * |∂_η^b ∂_t^ℓ (meanStress tr) t η|` from:
- `weightedTrainFluctAgeJetFixed_of PartI.trainFluctAgeJetFixed fluctDoubledWeightPoly_proof`
  (weighted age-spatial jets of the stream fluctuation `ψ - S` at a single threshold `ν_fl`),
- `PartI_T22.isStreamPair_ψ_fluct_v_fluct`, `psiEtaSwap_proof`, `psiQSwap_proof`, and
  `PartIIa.sliceJetBound_of PartIIa.profileDict` (expressing `hfluct c (tr.v)₀ = -∂_η(ψ - S)` and
  `hfluct c (tr.v)₁ = ∂_q(ψ - S)` so every velocity-fluctuation slice derivative is bounded by an
  `ageJet` of `ψ - S`), and
- `PartIIa.meanStressDerivForm_of`, `PartIIa.leib_inst_c`, and `PartIIa.avg_bound`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.WeightedTrainMeanAux

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short

/-- Component `0` velocity-fluctuation slice derivatives are bounded by stream-fluctuation age-jets
of spatial order `i + 1`. -/
theorem velFluct0_slice_le_streamJet {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (i r : ℕ) {t : ℝ} (ht : 0 < t) (q η : ℝ) :
    |iteratedDeriv i (fun e => iteratedDeriv r
        (fun s => PartI.hfluct c (fun w => tr.v s w 0) (q, e)) t) η| ≤
      ‖PartI.ageJet r (i + 1)
          (fun s z => tr.ψ s z - PartI.hmean c (tr.ψ s) z.2) t (q, η)‖ := by
  let ψ_fluct : ℝ → Plane → ℝ := fun s z => tr.ψ s z - PartI.hmean c (tr.ψ s) z.2
  let v_fluct : ℝ → Plane → UnforcedLeray.Train.Vec := fun s => PartI.hfluct c (tr.v s)
  have hsp : IIb.IsStreamPair ψ_fluct v_fluct :=
    PartI.PartI_T22.isStreamPair_ψ_fluct_v_fluct hν hc tr
  have hprof := PartIIa.contDiffOn_trainProfile_of (F := ψ_fluct) hsp.1
  have hSJ := PartIIa.sliceJetBound_of PartIIa.profileDict
  have hpt : ∀ e : ℝ,
      iteratedDeriv r (fun s => PartI.hfluct c (fun w => tr.v s w 0) (q, e)) t =
        -deriv (fun t' : ℝ => iteratedDeriv r (fun s => ψ_fluct s (q, t')) t) e := by
    intro e
    have hev : (fun s => PartI.hfluct c (fun w => tr.v s w 0) (q, e)) =ᶠ[𝓝 t]
        (fun s => v_fluct s (q, e) 0) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact PartIIa.fvs_hfluct_apply c (tr.v s)
        (PartIIa.fvs_slice_continuous tr (le_of_lt hs)) 0 (q, e)
    rw [hev.iteratedDeriv_eq r]
    have hap := IIb.psi_iteratedDeriv_apply (fun x => v_fluct x.1 x.2) hsp.2.1 0 r ht (q, e)
    dsimp only at hap
    rw [hap]
    have hsw := (_root_.psiEtaSwap_proof ψ_fluct v_fluct hsp r t ht q e).deriv
    linarith
  have hfun : (fun e => iteratedDeriv r
      (fun s => PartI.hfluct c (fun w => tr.v s w 0) (q, e)) t) =
      fun e => -deriv (fun t' : ℝ => iteratedDeriv r (fun s => ψ_fluct s (q, t')) t) e :=
    funext hpt
  rw [hfun, iteratedDeriv_fun_neg, ← congrFun (iteratedDeriv_succ' (n := i)
    (f := fun t' : ℝ => iteratedDeriv r (fun s => ψ_fluct s (q, t')) t)) η, abs_neg]
  have hslice := hSJ ψ_fluct hprof (i + 1) 0 r q η t ht
  simpa only [iteratedDeriv_zero, Nat.add_zero] using hslice

/-- Component `1` velocity-fluctuation slice derivatives are bounded by stream-fluctuation age-jets
of spatial order `i + 1`. -/
theorem velFluct1_slice_le_streamJet {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (i r : ℕ) {t : ℝ} (ht : 0 < t) (q η : ℝ) :
    |iteratedDeriv i (fun e => iteratedDeriv r
        (fun s => PartI.hfluct c (fun w => tr.v s w 1) (q, e)) t) η| ≤
      ‖PartI.ageJet r (i + 1)
          (fun s z => tr.ψ s z - PartI.hmean c (tr.ψ s) z.2) t (q, η)‖ := by
  let ψ_fluct : ℝ → Plane → ℝ := fun s z => tr.ψ s z - PartI.hmean c (tr.ψ s) z.2
  let v_fluct : ℝ → Plane → UnforcedLeray.Train.Vec := fun s => PartI.hfluct c (tr.v s)
  have hsp : IIb.IsStreamPair ψ_fluct v_fluct :=
    PartI.PartI_T22.isStreamPair_ψ_fluct_v_fluct hν hc tr
  have hprof := PartIIa.contDiffOn_trainProfile_of (F := ψ_fluct) hsp.1
  have hSJ := PartIIa.sliceJetBound_of PartIIa.profileDict
  have hpt : ∀ e : ℝ,
      iteratedDeriv r (fun s => PartI.hfluct c (fun w => tr.v s w 1) (q, e)) t =
        iteratedDeriv 1 (fun q' : ℝ => iteratedDeriv r (fun s => ψ_fluct s (q', e)) t) q := by
    intro e
    have hev : (fun s => PartI.hfluct c (fun w => tr.v s w 1) (q, e)) =ᶠ[𝓝 t]
        (fun s => v_fluct s (q, e) 1) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact PartIIa.fvs_hfluct_apply c (tr.v s)
        (PartIIa.fvs_slice_continuous tr (le_of_lt hs)) 1 (q, e)
    rw [hev.iteratedDeriv_eq r]
    have hap := IIb.psi_iteratedDeriv_apply (fun x => v_fluct x.1 x.2) hsp.2.1 1 r ht (q, e)
    dsimp only at hap
    rw [hap, iteratedDeriv_one]
    exact ((_root_.psiQSwap_proof ψ_fluct v_fluct hsp r t ht q e).deriv).symm
  have hfun : (fun e => iteratedDeriv r
      (fun s => PartI.hfluct c (fun w => tr.v s w 1) (q, e)) t) =
      fun e => iteratedDeriv 1 (fun q' : ℝ => iteratedDeriv r (fun s => ψ_fluct s (q', e)) t) q :=
    funext hpt
  rw [hfun]
  exact hSJ ψ_fluct hprof i 1 r q η t ht

/-- Fixed-threshold all-weight, all-order mixed-derivative exponential decay of `meanStress`:
for every `ρ > 1/2`, there exists a single threshold `ν_st > 0` such that for every `0 < ν ≤ ν_st`,
every BUC train `tr`, and every `(k, b, ℓ)`, `(1 + η ^ 2) ^ k * |∂_η^b ∂_t^ℓ (meanStress tr) t η|`
decays as `polyP C M ν c * exp (-(κ * ν * t / c ^ 2))`. -/
theorem meanStress_weighted_jet_fixed (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ ν_st : ℝ, 0 < ν_st ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν_st →
      ∀ tr : B0140.TrainSol ν (PartI.trainPeriod ρ ν), PartI.IsBUCTrain tr →
        let c := PartI.trainPeriod ρ ν
        ∀ k b ℓ : ℕ, ∃ C : ℝ, ∃ M : ℕ, ∃ κ : ℝ, 0 < C ∧ 0 < κ ∧
          ∀ t : ℝ, 0 < t → ∀ η : ℝ,
            (1 + η ^ 2) ^ k *
              |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanStress tr r e) t) η| ≤
                PartI.polyP C M ν c * Real.exp (-(κ * ν * t / c ^ 2)) := by
  have hWFl := PartIIIb.Concrete.weightedTrainFluctAgeJetFixed_of
    PartI.trainFluctAgeJetFixed IIb.fluctDoubledWeightPoly_proof
  obtain ⟨ν_fl, hν_fl, hFlAll⟩ := hWFl ρ hρ
  refine ⟨min ν_fl (1 / 2), lt_min hν_fl (by norm_num), ?_⟩
  intro ν hν hν_le tr htr c k b ℓ
  have hν_fl_le : ν ≤ ν_fl := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := by linarith
  have hc1 : 1 ≤ c := by
    dsimp [c, PartI.trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  let hSm := PartIIa.meanStressSmooth_of PartI.hmeanContDiff
  let hMix := PartIIa.hmeanMixedDeriv_of PartIIa.ageDerivSmooth
    (PartIIa.hmeanAgeIter_of PartI.hmeanDerivS PartIIa.ageDerivSmooth) PartIIa.hmeanEtaDeriv
  let hDF := PartIIa.meanStressDerivForm_of PartI.trainMeanEquations_proof
    PartIIa.hmeanMulFluct hMix hSm
  let hL := PartIIa.mixedLeibniz_of PartIIa.ageDerivSmooth
  let ψ_fluct : ℝ → Plane → ℝ := fun r z => tr.ψ r z - PartI.hmean c (tr.ψ r) z.2
  have hFl := hFlAll ν hν hν_fl_le tr htr
  choose C_pt κ_pt hκ_pt hBd_pt using fun (m' r j' : ℕ) => hFl m' r j'
  let S_idx : Finset (ℕ × ℕ) := Finset.product (Finset.range (ℓ + 1)) (Finset.range (b + 2))
  have hS_ne : S_idx.Nonempty := ⟨(0, 0), by simp [S_idx]⟩
  set C_w : ℝ := max (∑ p ∈ S_idx, max (C_pt (2 * k) p.1 p.2) 0) 1
  have hCw_pos : 0 < C_w := lt_max_of_lt_right one_pos
  set κ_w : ℝ := S_idx.inf' hS_ne (fun p => κ_pt (2 * k) p.1 p.2)
  have hκw_pos : 0 < κ_w := (Finset.lt_inf'_iff hS_ne).2 fun p _ => hκ_pt (2 * k) p.1 p.2
  set C_0 : ℝ := max (∑ p ∈ S_idx, max (C_pt 0 p.1 p.2) 0) 1
  have hC0_pos : 0 < C_0 := lt_max_of_lt_right one_pos
  have hRect_w : ∀ r j' : ℕ, r ≤ ℓ → j' ≤ b + 1 → ∀ t : ℝ, 0 < t → ∀ z : Plane,
      (1 + |z.2|) ^ (2 * k) * ‖PartI.ageJet r j' ψ_fluct t z‖ ≤
        C_w * Real.exp (-(κ_w * t)) := by
    intro r j' hr hj' t ht z
    have hmem : (r, j') ∈ S_idx :=
      Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
    have hpt_bd := hBd_pt (2 * k) r j' t ht z
    have hC_nn : 0 ≤ max (C_pt (2 * k) r j') 0 := le_max_right _ _
    have hC_le_sum : max (C_pt (2 * k) r j') 0 ≤ ∑ p ∈ S_idx, max (C_pt (2 * k) p.1 p.2) 0 :=
      Finset.single_le_sum (f := fun p : ℕ × ℕ => max (C_pt (2 * k) p.1 p.2) 0)
        (fun _ _ => le_max_right _ _) hmem
    have hC_le : C_pt (2 * k) r j' ≤ C_w :=
      (le_max_left _ 0).trans (hC_le_sum.trans (le_max_left _ 1))
    have hκ_le : κ_w ≤ κ_pt (2 * k) r j' := Finset.inf'_le _ hmem
    have hexp_le : Real.exp (-(κ_pt (2 * k) r j' * t)) ≤ Real.exp (-(κ_w * t)) := by
      apply Real.exp_le_exp.2
      nlinarith
    calc (1 + |z.2|) ^ (2 * k) * ‖PartI.ageJet r j' ψ_fluct t z‖
        ≤ C_pt (2 * k) r j' * Real.exp (-(κ_pt (2 * k) r j' * t)) := hpt_bd
      _ ≤ C_w * Real.exp (-(κ_pt (2 * k) r j' * t)) :=
          mul_le_mul_of_nonneg_right hC_le (Real.exp_nonneg _)
      _ ≤ C_w * Real.exp (-(κ_w * t)) :=
          mul_le_mul_of_nonneg_left hexp_le hCw_pos.le
  have hRect_0 : ∀ r j' : ℕ, r ≤ ℓ → j' ≤ b + 1 → ∀ t : ℝ, 0 < t → ∀ z : Plane,
      ‖PartI.ageJet r j' ψ_fluct t z‖ ≤ C_0 := by
    intro r j' hr hj' t ht z
    have hmem : (r, j') ∈ S_idx :=
      Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
    have hpt_bd := hBd_pt 0 r j' t ht z
    rw [pow_zero, one_mul] at hpt_bd
    have hC_le_sum : max (C_pt 0 r j') 0 ≤ ∑ p ∈ S_idx, max (C_pt 0 p.1 p.2) 0 :=
      Finset.single_le_sum (f := fun p : ℕ × ℕ => max (C_pt 0 p.1 p.2) 0)
        (fun _ _ => le_max_right _ _) hmem
    have hC_le : C_pt 0 r j' ≤ C_0 :=
      (le_max_left _ 0).trans (hC_le_sum.trans (le_max_left _ 1))
    have hexp_le1 : Real.exp (-(κ_pt 0 r j' * t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (hκ_pt 0 r j').le ht.le))
    calc ‖PartI.ageJet r j' ψ_fluct t z‖
        ≤ C_pt 0 r j' * Real.exp (-(κ_pt 0 r j' * t)) := hpt_bd
      _ ≤ C_0 * Real.exp (-(κ_pt 0 r j' * t)) :=
          mul_le_mul_of_nonneg_right hC_le (Real.exp_nonneg _)
      _ ≤ C_0 * 1 := mul_le_mul_of_nonneg_left hexp_le1 hC0_pos.le
      _ = C_0 := mul_one _
  set C_sum : ℝ := ∑ p ∈ PartIIa.meanPairs b ℓ, |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)|
  set C_out : ℝ := max (C_sum * (C_w * C_0)) 1
  refine ⟨C_out, 0, κ_w, lt_max_of_lt_right one_pos, hκw_pos, fun t ht η => ?_⟩
  rw [hDF ν c hν hc0 tr htr b ℓ t η ht]
  have hjap_le : (1 + η ^ 2) ^ k ≤ (1 + |η|) ^ (2 * k) := by
    have h1 : 1 + η ^ 2 ≤ (1 + |η|) ^ 2 := by
      have := abs_nonneg η
      have := sq_abs η
      nlinarith
    calc (1 + η ^ 2) ^ k ≤ ((1 + |η|) ^ 2) ^ k := pow_le_pow_left₀ (by positivity) h1 k
      _ = (1 + |η|) ^ (2 * k) := (pow_mul (1 + |η|) 2 k).symm
  have hpt : ∀ q ∈ Ioc (-c / 2) (c / 2),
      (1 + η ^ 2) ^ k * |iteratedDeriv b (fun e => iteratedDeriv ℓ
        (fun r => PartIIa.fluctProd tr r (q, e)) t) η| ≤
        (C_sum * (C_w * C_0)) * Real.exp (-(κ_w * t)) := by
    intro q _
    rw [PartIIa.leib_inst_c hL hSm ν c hν hc0 tr htr q t η ht b ℓ]
    calc (1 + η ^ 2) ^ k *
          |∑ p ∈ PartIIa.meanPairs b ℓ, ((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)) *
            (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η *
              iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η)|
        ≤ (1 + η ^ 2) ^ k *
            ∑ p ∈ PartIIa.meanPairs b ℓ, |((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)) *
              (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                  (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η *
                iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                  (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ = ∑ p ∈ PartIIa.meanPairs b ℓ, (1 + η ^ 2) ^ k *
            |((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)) *
              (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                  (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η *
                iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                  (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η)| :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ PartIIa.meanPairs b ℓ,
            |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
              ((C_w * C_0) * Real.exp (-(κ_w * t))) := by
          refine Finset.sum_le_sum fun p (hp : p ∈ PartIIa.meanPairs b ℓ) => ?_
          have hp_mem : p.1 < b + 1 ∧ p.2 < ℓ + 1 := by
            simpa [PartIIa.meanPairs] using hp
          have hp1 : p.1 ≤ b := Nat.lt_succ_iff.1 hp_mem.1
          have hp2 : p.2 ≤ ℓ := Nat.lt_succ_iff.1 hp_mem.2
          have hv0 := velFluct0_slice_le_streamJet hν hc0 tr p.1 p.2 ht q η
          have hv1 := velFluct1_slice_le_streamJet hν hc0 tr (b - p.1) (ℓ - p.2) ht q η
          have h0_w : (1 + η ^ 2) ^ k *
              |iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η| ≤
              C_w * Real.exp (-(κ_w * t)) := by
            calc (1 + η ^ 2) ^ k *
                  |iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                    (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η|
                ≤ (1 + |η|) ^ (2 * k) *
                    ‖PartI.ageJet p.2 (p.1 + 1) ψ_fluct t (q, η)‖ :=
                  mul_le_mul hjap_le hv0 (abs_nonneg _) (by positivity)
              _ ≤ C_w * Real.exp (-(κ_w * t)) :=
                  hRect_w p.2 (p.1 + 1) hp2 (by omega) t ht (q, η)
          have h1_0 : |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
              (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η| ≤ C_0 :=
            hv1.trans (hRect_0 (ℓ - p.2) ((b - p.1) + 1) (Nat.sub_le ℓ p.2) (by omega) t ht (q, η))
          rw [abs_mul ((b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)),
            abs_mul (iteratedDeriv p.1 _ η)]
          calc (1 + η ^ 2) ^ k *
                (|(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
                  (|iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                      (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η| *
                    |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                      (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η|))
              = |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
                  (((1 + η ^ 2) ^ k *
                    |iteratedDeriv p.1 (fun e => iteratedDeriv p.2
                      (fun r => PartI.hfluct c (fun w => tr.v r w 0) (q, e)) t) η|) *
                    |iteratedDeriv (b - p.1) (fun e => iteratedDeriv (ℓ - p.2)
                      (fun r => PartI.hfluct c (fun w => tr.v r w 1) (q, e)) t) η|) := by ring
            _ ≤ |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
                  ((C_w * Real.exp (-(κ_w * t))) * C_0) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul h0_w h1_0 (abs_nonneg _) (by positivity)) (abs_nonneg _)
            _ = |(b.choose p.1 : ℝ) * (ℓ.choose p.2 : ℝ)| *
                  ((C_w * C_0) * Real.exp (-(κ_w * t))) := by ring
      _ = (C_sum * (C_w * C_0)) * Real.exp (-(κ_w * t)) := by
          dsimp [C_sum]
          rw [← Finset.sum_mul]
          ring
  have havg := PartIIa.avg_bound (c := c) (η := η) hc0 (by positivity : 0 ≤ (1 + η ^ 2) ^ k)
    (fun q η' => iteratedDeriv b (fun e => iteratedDeriv ℓ
      (fun r => PartIIa.fluctProd tr r (q, e)) t) η') hpt
  have hexp_scale : Real.exp (-(κ_w * t)) ≤ Real.exp (-(κ_w * ν * t / c ^ 2)) := by
    apply Real.exp_le_exp.2
    have hc2_ge1 : 1 ≤ c ^ 2 := by nlinarith
    have h1 : κ_w * ν * t / c ^ 2 ≤ κ_w * ν * t / 1 :=
      div_le_div_of_nonneg_left (by positivity) one_pos hc2_ge1
    have h2 : κ_w * ν * t ≤ κ_w * 1 * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hν1 hκw_pos.le) ht.le
    linarith
  calc (1 + η ^ 2) ^ k *
        |PartI.hmean c (fun z => iteratedDeriv b
          (fun e => iteratedDeriv ℓ (fun r => PartIIa.fluctProd tr r (z.1, e)) t) z.2) η|
      ≤ (C_sum * (C_w * C_0)) * Real.exp (-(κ_w * t)) := havg
    _ ≤ C_out * Real.exp (-(κ_w * ν * t / c ^ 2)) :=
        mul_le_mul (le_max_left _ 1) hexp_scale (Real.exp_nonneg _) (lt_max_of_lt_right one_pos).le
    _ = PartI.polyP C_out 0 ν c * Real.exp (-(κ_w * ν * t / c ^ 2)) := by
        unfold PartI.polyP
        simp

end UnforcedLeray.Short.IIb.WeightedTrainMeanAux
