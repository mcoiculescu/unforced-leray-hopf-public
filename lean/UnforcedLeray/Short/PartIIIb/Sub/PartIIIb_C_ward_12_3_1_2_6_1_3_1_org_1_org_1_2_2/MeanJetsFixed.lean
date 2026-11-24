import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.A
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.B.Jets
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanStreamDeriv
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed

/-!
# `MeanJetsFixed` from `TrainJetsBoundedFixed` (SP 397-404, SP 427-435)

Source `the November 2 reference manuscript` 397-404 and 427-435.  Two generalisations
to every order `N` of the accepted order-`3` proofs: `velJointJetsFixed3_of` (A.lean) and
`meanStreamGradJets` (B.lean, with `JB 3` replaced by `JB (N+1)`); then the transfer
`S = Φ ∘ ι` with `ι(s,η) = (s,(0,η))`, `‖ι‖ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartIIIb.Concrete.PO

/-- Joint jets of `v` of orders `≤ N` are bounded on `s > 0` (from the age jets, every order). -/
private theorem velJets_of_age (N : ℕ) {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hMex : ∀ ℓ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.v s z‖ ≤ M) :
    ∃ C : ℝ, ∀ l : ℕ, l ≤ N → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖ ≤ C := by
  choose M hM using hMex
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)
  choose K hK0 hK using vjA_joint
  refine ⟨∑ l ∈ Finset.range (N + 1), K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)|, ?_⟩
  intro l hl y hy
  have hl' : l ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  calc ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖
      ≤ K l * ∑ ℓ ∈ Finset.range (l + 1),
          ‖UnforcedLeray.Short.PartI.ageJet ℓ (l - ℓ) tr.v y.1 y.2‖ :=
        hK l tr.v hsm y hy
    _ ≤ K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ =>
          (hM ℓ (l - ℓ) y.1 hy y.2).trans (le_abs_self _)) (hK0 l)
    _ ≤ ∑ l ∈ Finset.range (N + 1), K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)| :=
        Finset.single_le_sum (f := fun l => K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)|)
          (fun l' _ => mul_nonneg (hK0 l') (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hl'

/-- The mean stream `Φ(s,q,η) = S(s,η)` has jets of orders `1..N+1` bounded on `s > 0`, and is
smooth there, when the joint jets of `v` of orders `≤ N+1` are bounded (B.lean with `3 ↦ N+1`). -/
private theorem meanStreamGradJetsN (N : ℕ) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) (C : ℝ)
    (hC : ∀ l : ℕ, l ≤ N + 1 → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖ ≤ C) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) DD ∧
    ∃ C' : ℝ, ∀ l : ℕ, 1 ≤ l → l ≤ N + 1 → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l
        (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ C' := by
  have hvs : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) DD :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hvJB : JB (N + 1) (fun x : ℝ × Plane => tr.v x.1 x.2) := ⟨hvs, C, hC⟩
  have hV : ∀ i : Fin 2, JB (N + 1) (fun x : ℝ × Plane => tr.v x.1 x.2 i) := fun i =>
    hvJB.clm (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  have hVU : JB (N + 1) (fun x : ℝ × Plane => tr.v x.1 x.2 0) := hV 0
  have hVG : JB (N + 1) (fun x : ℝ × Plane => tr.v x.1 x.2 0 * tr.v x.1 x.2 1) :=
    (hV 0).mul (hV 1)
  -- horizontal averages
  set U : ℝ × Plane → ℝ := fun x => UnforcedLeray.Short.PartI.hmean c (fun z => tr.v x.1 z 0) x.2.2
    with hUdef
  set G : ℝ × Plane → ℝ := fun x =>
    UnforcedLeray.Short.PartI.hmean c (fun z => tr.v x.1 z 0 * tr.v x.1 z 1) x.2.2 with hGdef
  have hU : JB (N + 1) U := by
    obtain ⟨K, hK⟩ := hVU.2
    obtain ⟨h1, h2⟩ := hmean_jets hc (fun s z => tr.v s z 0) (N + 1) K hVU.1 hK
    exact ⟨h1, K, h2⟩
  have hG : JB (N + 1) G := by
    obtain ⟨K, hK⟩ := hVG.2
    obtain ⟨h1, h2⟩ := hmean_jets hc (fun s z => tr.v s z 0 * tr.v s z 1) (N + 1) K hVG.1 hK
    exact ⟨h1, K, h2⟩
  -- the coefficient functions
  set e : ℝ × Plane := (0, (0, 1)) with he
  set fstL : (ℝ × Plane) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Plane with hfst
  set sndL : (ℝ × Plane) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane) with hsnd
  have hUη : JB N (fun y => fderiv ℝ U y e) :=
    (JB.fderiv (N := N) hU).clm (ContinuousLinearMap.apply ℝ ℝ e)
  have hA : JB N (fun y => G y - ν • fderiv ℝ U y e) :=
    (hG.mono (Nat.le_succ N)).sub (hUη.const_smul ν)
  have hR : JB N (fun y => (ContinuousLinearMap.toSpanSingleton ℝ fstL)
        (G y - ν • fderiv ℝ U y e) - (ContinuousLinearMap.toSpanSingleton ℝ sndL) (U y)) :=
    (hA.clm (ContinuousLinearMap.toSpanSingleton ℝ fstL)).sub
      ((hU.mono (Nat.le_succ N)).clm (ContinuousLinearMap.toSpanSingleton ℝ sndL))
  obtain ⟨-, K, hK⟩ := hR
  refine ⟨?_, K, fun l hl1 hl3 y hy => ?_⟩
  · -- smoothness of `Φ` on `s > 0`
    have hSsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (Ioi 0 ×ˢ univ) := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc tr hbuc
    exact hSsm.comp ((contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn)
      (fun x hx => ⟨hx.1, mem_univ _⟩)
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hfd : ∀ y : ℝ × Plane, 0 < y.1 → fderiv ℝ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y =
      (ContinuousLinearMap.toSpanSingleton ℝ fstL) (G y - ν • fderiv ℝ U y e) -
        (ContinuousLinearMap.toSpanSingleton ℝ sndL) (U y) := by
    intro y hy
    -- the derivative of `Φ`
    have hSsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (Ioi 0 ×ˢ univ) := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc tr hbuc
    have hopen2 : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hSd : DifferentiableAt ℝ
        (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) (y.1, y.2.2) :=
      (hSsm.contDiffAt (hopen2.mem_nhds (show ((y.1, y.2.2) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hy, mem_univ _⟩))).differentiableAt (by simp)
    have hUd : DifferentiableAt ℝ U y :=
      (contDiffAt_of_DD hU.1 hy).differentiableAt (by simp)
    have hPd : HasFDerivAt (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ))
        (fstL.prod sndL) y := (fstL.prod sndL).hasFDerivAt
    have hΦ := hSd.hasFDerivAt.comp y hPd
    -- partial derivatives of `S`
    have hs1 : fderiv ℝ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (y.1, y.2.2) (1, 0) = UnforcedLeray.Short.PartI.meanStress tr y.1 y.2.2 -
          ν * fderiv ℝ U y e := by
      have hline : HasDerivAt (fun r : ℝ => ((r, y.2.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
        (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2.2)
      have h1 := (hSd.hasFDerivAt.comp_hasDerivAt y.1 hline).deriv
      have h2 := UnforcedLeray.Short.PartI.trainMeanStreamDeriv ν c hν hc tr hbuc y.1 hy y.2.2
      have hline2 : HasDerivAt (fun t : ℝ => ((y.1, (y.2.1, t)) : ℝ × Plane)) e y.2.2 :=
        (hasDerivAt_const y.2.2 y.1).prodMk ((hasDerivAt_const y.2.2 y.2.1).prodMk (hasDerivAt_id _))
      have h3 := (hUd.hasFDerivAt.comp_hasDerivAt y.2.2 hline2).deriv
      have h3' : deriv (fun t : ℝ => U (y.1, (y.2.1, t))) y.2.2 = deriv (fun t : ℝ =>
          UnforcedLeray.Short.PartI.hmean c (fun z => tr.v y.1 z 0) t) y.2.2 := rfl
      rw [← h1]
      show deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r y.2.2) y.1 = _
      rw [h2, ← h3, ← h3']
      rfl
    have hs2 : fderiv ℝ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (y.1, y.2.2) (0, 1) = - U y := by
      have hline : HasDerivAt (fun t : ℝ => ((y.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2.2 :=
        (hasDerivAt_const y.2.2 y.1).prodMk (hasDerivAt_id _)
      have h1 := (hSd.hasFDerivAt.comp_hasDerivAt y.2.2 hline).deriv
      have h2 := UnforcedLeray.Short.PartI.trainMeanV1 ν c hν hc tr y.1 hy y.2.2
      rw [← h1]
      show deriv (fun t => UnforcedLeray.Short.PartI.meanStream tr y.1 t) y.2.2 = _
      have : U y = UnforcedLeray.Short.PartI.hmean c (fun z => tr.v y.1 z 0) y.2.2 := rfl
      rw [this, h2]; ring
    rw [show fderiv ℝ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y = fderiv ℝ ((fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) ∘ fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) y from rfl, hΦ.fderiv]
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : ((w.1, w.2.2) : ℝ × ℝ) = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show (fstL w, sndL w) = ((w.1, w.2.2) : ℝ × ℝ) from rfl, hw, map_add, map_smul, map_smul,
      hs1, hs2]
    simp only [smul_eq_mul, hfst, hsnd, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.coe_snd', Function.comp_apply]
    show _ = _
    have hG' : G y = UnforcedLeray.Short.PartI.meanStress tr y.1 y.2.2 := rfl
    rw [hG']
    ring
  have hyD : y ∈ DD := ⟨hy, mem_univ _⟩
  have hev : fderiv ℝ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
      =ᶠ[𝓝 y] (fun z => (ContinuousLinearMap.toSpanSingleton ℝ fstL)
        (G z - ν • fderiv ℝ U z e) - (ContinuousLinearMap.toSpanSingleton ℝ sndL) (U z)) := by
    filter_upwards [isOpen_DD.mem_nhds hyD] with z hz
    exact hfd z hz.1
  rw [← norm_iteratedFDeriv_fderiv, (Filter.EventuallyEq.iteratedFDeriv ℝ hev n).eq_of_nhds]
  exact hK n (by omega) y hy

/-- The coordinate embedding `ι(s,η) = (s,(0,η))` of norm at most one. -/
private theorem iota_norm_le_one (ι : ℝ × ℝ →L[ℝ] ℝ × Plane)
    (hι : ∀ x : ℝ × ℝ, ι x = (x.1, ((0 : ℝ), x.2))) : ‖ι‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound ι zero_le_one (fun x => ?_)
  rw [one_mul]
  have h2 : ‖((0 : ℝ), x.2)‖ ≤ ‖x‖ := by
    rw [Prod.norm_def, Prod.norm_def]
    exact max_le_max (by simp) le_rfl
  calc ‖ι x‖ = max ‖x.1‖ ‖((0 : ℝ), x.2)‖ := by rw [hι, Prod.norm_def]
    _ ≤ ‖x‖ := max_le (norm_fst_le x) h2

/-- Transfer of a derivative bound along `ι(s,η) = (s,(0,η))`. -/
private theorem iota_transfer (Φ : ℝ × Plane → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ DD) (l : ℕ) (C' : ℝ)
    (hΦb : ∀ y : ℝ × Plane, 0 < y.1 → ‖iteratedFDeriv ℝ l Φ y‖ ≤ C') (y : ℝ × ℝ) (hy : 0 < y.1) :
    ‖iteratedFDeriv ℝ l (fun x : ℝ × ℝ => Φ (x.1, ((0 : ℝ), x.2))) y‖ ≤ C' := by
  set ι : ℝ × ℝ →L[ℝ] ℝ × Plane :=
    ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ContinuousLinearMap.prod (0 : (ℝ × ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)) with hιdef
  have hι : ∀ x : ℝ × ℝ, ι x = (x.1, ((0 : ℝ), x.2)) := fun x => rfl
  have hιn : ‖ι‖ ≤ 1 := iota_norm_le_one ι hι
  have hmaps : ∀ x : ℝ × ℝ, 0 < x.1 → ι x ∈ DD := fun x hx => ⟨by rw [hι]; exact hx, mem_univ _⟩
  have hopenP : IsOpen (ι ⁻¹' DD) := isOpen_DD.preimage ι.continuous
  have hyP : y ∈ ι ⁻¹' DD := hmaps y hy
  have hfun : (fun x : ℝ × ℝ => Φ (x.1, ((0 : ℝ), x.2))) = Φ ∘ ι := funext fun x => rfl
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right ι hΦ isOpen_DD.uniqueDiffOn
    hopenP.uniqueDiffOn (x := y) (hmaps y hy) (i := l) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen l hopenP hyP, iteratedFDerivWithin_of_isOpen l isOpen_DD (hmaps y hy)] at hcomp
  rw [hfun, hcomp]
  have hP : ‖(iteratedFDeriv ℝ l Φ (ι y)).compContinuousLinearMap (fun _ : Fin l => ι)‖
      ≤ ‖iteratedFDeriv ℝ l Φ (ι y)‖ * ∏ _i : Fin l, ‖ι‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  have hprod : ∏ _i : Fin l, ‖ι‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hιn)
  have hb : ‖iteratedFDeriv ℝ l Φ (ι y)‖ ≤ C' := hΦb (ι y) (by rw [hι]; exact hy)
  calc ‖(iteratedFDeriv ℝ l Φ (ι y)).compContinuousLinearMap (fun _ : Fin l => ι)‖
      ≤ ‖iteratedFDeriv ℝ l Φ (ι y)‖ * ∏ _i : Fin l, ‖ι‖ := hP
    _ ≤ ‖iteratedFDeriv ℝ l Φ (ι y)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ C' := by rw [mul_one]; exact hb

/-- **Target** `meanJetsFixed_of`: the all-order form of `MeanStreamGradJets` at fixed parameters
(SP 397-404, SP 427-435), from `PartI.TrainJetsBoundedFixed`. -/
theorem meanJetsFixed_of (h : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed) :
    MeanJetsFixed := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, H⟩ := h ρ hρ
  refine ⟨ν₀, hν₀, fun ν c hν hνν₀ hc tr hbuc i hi => ?_⟩
  subst hc
  obtain ⟨N, rfl⟩ : ∃ N, i = N + 1 := ⟨i - 1, by omega⟩
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod ρ ν := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    exact Real.rpow_pos_of_pos hν _
  have hMex : ∀ ℓ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.v s z‖ ≤ M :=
    fun ℓ j => H ν hν hνν₀ tr hbuc ℓ j
  obtain ⟨C, hC⟩ := velJets_of_age (N + 1) tr hbuc hMex
  obtain ⟨hΦs, C', hC'⟩ := meanStreamGradJetsN N ν _ hν hcpos tr hbuc C
    (fun l hl => hC l hl)
  refine ⟨C', fun y hy => ?_⟩
  exact iota_transfer (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
    hΦs (N + 1) C' (fun y' hy' => hC' (N + 1) (by omega) (by omega) y' hy') y hy

end UnforcedLeray.Short.PartIIIb.Concrete
