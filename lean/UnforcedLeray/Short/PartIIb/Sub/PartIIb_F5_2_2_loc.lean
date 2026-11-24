import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.P0SliceLiftH1.Needed
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice
import UnforcedLeray.Short.PartIIb.Tasks.HardyL1

/-!
# Part II-b, `ORG:F5-2-2-3-P0-loc`: local-in-age `H¹` integrability bridge for `CylBodySourceProjection` (R11)

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239 and
2269–2282 (`g = -P_0(v_c · ∇b_0 + b_0 · ∇v_c)`, display `short-bg:source`).

`P0SliceLiftH1` (`Sub/PartII-b_F5_2_2.lean:370`) omitted the local-in-age `L¹` integrability
hypothesis `hLoc : ∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s < ⊤`, which is
recorded in `P0SliceLiftH1Needed.P0SliceLiftH1Loc` (`P0SliceLiftH1/Needed.lean:36`). In parent
`CylBodySourceProjection` (`Sub/PartII-b_F5_2.lean:863`), `hLoc` follows from the standing
local-in-age train bound `hTrp` (`trainSliceNorm22_3 p.c m p.train s ≤ ENNReal.ofReal C` on
`Icc a b`), `sliceH1Norm_flatBv_le`, `FlatGraphD2Slice`, and `hardyL1_proof`. Per R11, we prove
`cylBodySourceProjection_of_leaves_loc` beside `Sub/PartII-b_F5_2_2.lean` without modifying
existing definitions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete CylProjectionSub

/-- Local-in-age `L¹` integrability of `sliceH1Norm c (flatBv ...) (flatBvQ ...) (flatBvEta ...)`
on every compact interval `[a, b] ⊂ (0, ∞)` for `0 ≤ m`, from `InHr c bgp` of
`b0', sqrtS b0q, sqrtS b0η, mulS (D2 i j)`, `hardyL1_proof`, and a local bound on
`trainSliceNorm22_3 c m tr`. -/
private theorem loc_lintegral_sliceH1Norm_lt_top_m {ν c m : ℝ} (hm : 0 ≤ m)
    (tr : B0140.TrainSol ν c) (hc : 0 < c)
    (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf)
    (hb0'_hr : InHr c bgp b0') (hbq_hr : InHr c bgp (sqrtS b0q))
    (hbη_hr : InHr c bgp (sqrtS b0η)) (hD2_hr : ∀ i j, InHr c bgp (mulS (D2 i j)))
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    (hTr_loc : ∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ s ∈ Icc a b,
      trainSliceNorm22_3 c m tr s ≤ ENNReal.ofReal C) :
    ∀ a b : ℝ, 0 < a →
      ∫⁻ s in Icc a b,
        sliceH1Norm c (flatBv tr b0' b0q b0η)
          (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
          (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s < ⊤ := by
  intro a b ha
  by_cases hab : a ≤ b
  · let T : ℝ := max b 1
    have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_right b 1)
    have hsub : Icc a b ⊆ Ioc 0 T := fun s hs =>
      ⟨lt_of_lt_of_le ha hs.1, hs.2.trans (le_max_left b 1)⟩
    obtain ⟨C, hC_bd⟩ := hTr_loc a b ha
    let K : ℝ≥0∞ := ENNReal.ofReal 16 * (ENNReal.ofReal C * ENNReal.ofReal (c ^ (4 / 11 : ℝ)))
    have hK_lt : K < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    have hm0 := measurable_sliceLpNorm c hsm0
    have hmq := measurable_sliceLpNorm c hsmq
    have hmη := measurable_sliceLpNorm c hsmη
    have hmD2 : ∀ i j, Measurable (sliceLpNorm c (D2 i j)) :=
      fun i j => measurable_sliceLpNorm c (hsmD2 i j)
    have hmSum := measurable_sliceD2Sum c hm0 hmq hmη hmD2
    have hs0_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0') < ⊤ :=
      (sLpNorm_D0_le T _ hm0).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sliceLpNorm_le_hNorm c T hsm0).trans_lt hb0'_hr.finite))
    have hsq_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0q) < ⊤ :=
      (sLpNorm_D1_le T _ hmq).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sqrtS_sliceLpNorm_le c T hsmq).trans_lt hbq_hr.finite))
    have hsη_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0η) < ⊤ :=
      (sLpNorm_D1_le T _ hmη).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sqrtS_sliceLpNorm_le c T hsmη).trans_lt hbη_hr.finite))
    have hsD2_lt : ∀ i j, sLpNorm (13 / 8) T (sliceLpNorm c (D2 i j)) < ⊤ := fun i j => by
      rw [sLpNorm_D2_eq T _ (hmD2 i j)]
      exact (sLpNorm_mulS_sliceLpNorm_le c T (hsmD2 i j)).trans_lt (hD2_hr i j).finite
    have hsSum_lt : sLpNorm (13 / 8) T (sliceD2Sum c b0' b0q b0η D2) < ⊤ := by
      refine (sLpNorm_sliceD2Sum_le (13 / 8) T c hm0 hmq hmη hmD2).trans_lt ?_
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
        ⟨hs0_lt, hsq_lt⟩, hsη_lt⟩, ?_⟩
      exact ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr fun j _ => hsD2_lt i j
    have hHardy := hardyL1_proof T hT (sliceD2Sum c b0' b0q b0η D2) hmSum
    change ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s ≤
      ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * T ^ (1 / 22 : ℝ)) *
        sLpNorm (13 / 8) T (sliceD2Sum c b0' b0q b0η D2) at hHardy
    have hIoc_lt : ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s < ⊤ :=
      hHardy.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsSum_lt)
    have hIcc_le : ∫⁻ s in Icc a b,
          sliceH1Norm c (flatBv tr b0' b0q b0η)
            (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
            (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s ≤
        K * ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s := by
      calc ∫⁻ s in Icc a b,
              sliceH1Norm c (flatBv tr b0' b0q b0η)
                (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
                (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s
          ≤ ∫⁻ s in Icc a b, K * sliceD2Sum c b0' b0q b0η D2 s := by
            refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
            have hs0 : 0 ≤ s := (lt_of_lt_of_le ha hs.1).le
            refine (sliceH1Norm_flatBv_le hc hm tr hsm0 hsmq hsmη hsmD2 hs0).trans ?_
            dsimp only [K]
            gcongr
            exact hC_bd s hs
        _ = K * ∫⁻ s in Icc a b, sliceD2Sum c b0' b0q b0η D2 s :=
            lintegral_const_mul' K _ hK_lt.ne
        _ ≤ K * ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s :=
            mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
    exact hIcc_le.trans_lt (ENNReal.mul_lt_top hK_lt hIoc_lt)
  · rw [Icc_eq_empty hab, Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top

/-- **Conditional proof of `CylBodySourceProjection`** (`PartII-b:F5/2/2`, SP 2213–2239) from
`FlatBvWeakLeibniz`, `FlatBvSliceGoodAe`, and `P0SliceLiftH1Needed.P0SliceLiftH1Loc` (`K_L = 2`),
discharging `hLoc` via `loc_lintegral_sliceH1Norm_lt_top_m`. -/
theorem cylBodySourceProjection_of_leaves_loc
    (hLeib : FlatBvWeakLeibniz)
    (hGood : FlatBvSliceGoodAe)
    (hLift : P0SliceLiftH1Needed.P0SliceLiftH1Loc) :
    UnforcedLeray.Short.IIb.CylBodySourceProjection := by
  apply cylBodySourceProjection_of_leray
  refine ⟨2, by norm_num,
    fun m hm p T hcp _hTp hTrp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 => ?_⟩
  have hTr_ae : ∀ᵐ s ∂volume, 0 < s → trainSliceNorm22_3 p.c m p.train s < ⊤ :=
    Eventually.of_forall fun s hs => by
      obtain ⟨C, hC⟩ := hTrp s s hs
      exact (hC s ⟨le_rfl, le_rfl⟩).trans_lt ENNReal.ofReal_lt_top
  have hLoc := loc_lintegral_sliceH1Norm_lt_top_m (by linarith : (0 : ℝ) ≤ m) p.train hcp
    b0' b0q b0η D2 hb0'H hbqH hbηH hD2H hsm0 hsmq hsmη hsmD2 hTrp
  obtain ⟨hwU_q, hwU_η⟩ :=
    hLeib p.train hcp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hgood_ae :=
    hGood m hm p.train hcp hTr_ae b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 hwU_q hwU_η
  obtain ⟨g, gq, gη, hsm_g, hsm_gq, hsm_gη, hgper, hgwq, hgwη, hgsrc,
      hH1_le, hcurl_dichot, hcurl_ae⟩ :=
    hLift m hm p.train hcp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 hwU_q hwU_η hLoc hgood_ae
  set Uq := flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0)
  set Uη := flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1)
  refine ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc,
    measurable_sliceH1Norm_cp p.c hsm_g hsm_gq hsm_gη,
    measurable_sliceXmNorm_cp p.c m (measurable_profCurl_cp hsm_gq hsm_gη),
    fun s hs => ⟨hH1_le s hs.1, ?_⟩, ?_⟩
  · have h1le2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    rcases hcurl_dichot s hs.1 with hzero | hae_eq
    · rw [sliceXmNorm_zero_of_eq_zero p.c m (fun z => (hzero z).1) (fun z => (hzero z).2)]
      exact zero_le
    · rw [sliceXmNorm_eq_of_ae_neg_cell p.c m hae_eq]
      calc sliceXmNorm p.c m (profCurl Uq Uη) s
          = 1 * sliceXmNorm p.c m (profCurl Uq Uη) s := (one_mul _).symm
        _ ≤ ENNReal.ofReal 2 * sliceXmNorm p.c m (profCurl Uq Uη) s :=
            mul_le_mul_of_nonneg_right h1le2 zero_le
  · filter_upwards [hgood_ae, hcurl_ae] with s hgs hcs hs
    obtain ⟨_, _, _, hintU, hcircU⟩ := hgs hs.1
    exact integrableOn_and_integral_zero_of_ae_neg_cell p.c (hcs hs.1) hintU hcircU

end UnforcedLeray.Short.IIb

end
