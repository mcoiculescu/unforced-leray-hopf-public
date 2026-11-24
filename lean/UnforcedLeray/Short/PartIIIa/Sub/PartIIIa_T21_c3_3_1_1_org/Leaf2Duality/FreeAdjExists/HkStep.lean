import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.Weak
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.StaticMollEnergy
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellWeakDerivOfMollBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellInterp
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CompactJetBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollKerProps
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.SmoothCellJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollConvJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollRateJetAbs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.VelMulCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollDual
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.MollRateTested
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.CellIBP
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.XMulTestInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.EnergyDerivAbs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.EnergyContAbs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.XDerivOfTested
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TestedOfXDeriv
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel.Bridge

/-!
# Spatial Sobolev bootstrap up to the end age for the free backward adjoint

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958,
3044-3050, and 3060-3073.

Proves `freeHkAllOrders`: for any `0 < ν` (`c = ν⁻²`) and `PartI.IsBUCTrain tr`, any weak free
adjoint `φ` (`IsFreeAdjointWeak`, `FreeTestedDeriv`) lies in `C([t, s); H^k_{-m,c})` (`AdjHkOn`)
for every `k : ℕ`. Because the free adjoint has no Biot-Savart term (`χ = 0`), only spatial
derivatives of `tr.v` enter (`SliceVel`), which `PartI.IsBUCTrain.deriv_bound` supplies for all
`0 < ν` without requiring `ν ≤ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

/-- Uniform `SliceVel` bounds on `[0, S]` for any `PartI.IsBUCTrain` and any `c > 0`. -/
theorem freeSliceVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {S : ℝ} (hS : 0 ≤ S) :
    ∃ Av : ℕ → ℝ, ∀ r ∈ Icc (0 : ℝ) S, SliceVel c (tr.v r) Av := by
  choose Av hAv using fun i => hbuc.deriv_bound hS i
  refine ⟨Av, fun r hr => ⟨?_, tr.isTrain.periodic_v r hr.1, tr.isTrain.solenoidal r hr.1,
    fun i x => hAv i r hr x⟩⟩
  exact slice_contDiff (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) tr.isTrain.smooth_v hr.1

/-- `IsCellJet` of every order for the zero field. -/
theorem isCellJet_zero (c m : ℝ) (k : ℕ) :
    IsCellJet c m k (fun _ => 0) (fun _ _ => 0) where
  base := rfl
  periodic _ _ _ := rfl
  memX _ _ := MemLp.zero
  deriv _ _ _ := ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩

/-- Static mollified energy inequality for the free adjoint (`χ = 0`), valid for every `0 < ν`
(no `ν ≤ 1` hypothesis). -/
theorem freeStaticMollEnergy (m : ℝ) {ν : ℝ} (hν : 0 < ν) (k : ℕ) (Av : ℕ → ℝ) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧
      ∀ (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)), SliceVel (ν ^ (-2 : ℝ)) v Av →
        ∀ (φ : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (M : ℝ),
          IsCellJet (ν ^ (-2 : ℝ)) m k φ D →
          (∀ w : List (Fin 2), w.length ≤ k →
            xNorm (ν ^ (-2 : ℝ)) (-m) (D w) ≤ ENNReal.ofReal M) →
          ∀ n j : ℕ, j ≤ k + 1 →
            -energyRate (ν ^ (-2 : ℝ)) m j (cellMoll n φ) (mollRate ν v n φ (fun _ => 0)) +
                β * cellEnergy (ν ^ (-2 : ℝ)) m (j + 1) (cellMoll n φ) ≤
              C * (cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n φ) + M ^ 2) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hT : StTransWord :=
    stTransWord_of cellMollSmooth cellConvDeriv stCellIbp stReynolds
      (stTransComm_of stAdjComm stVelWords)
      (stFriedJet_of cellConvDeriv (stFriedZero_of cellConvBound stMolMoment stFriedPointwise)
        (stFriedDeriv_of cellConvDeriv cellMollSmooth cellMollWeakDeriv cellPeriodicLocInt
          stAdjComm ktWeakLeibniz) stVelWords)
  obtain ⟨Cm, hCm0, hCm⟩ := cellMollBound c m hc
  obtain ⟨CT, hCT0, hCT⟩ := hT c m k Av hc
  set t : ℝ := CT / ν with ht
  have hCTt : CT = ν * t := by rw [ht]; field_simp
  set K₁ : ℝ := 16 * ν * |m| ^ 2 + 1 + CT + ν * t ^ 2 + Cm ^ 2 * |(0 : ℝ)| ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have h1 : 0 ≤ 16 * ν * |m| ^ 2 + 1 := by positivity
    have h2 : 0 ≤ ν * t ^ 2 + Cm ^ 2 * |(0 : ℝ)| ^ 2 := by positivity
    rw [hK₁]
    linarith
  refine ⟨ν + ((wordsLE (k + 1)).card : ℝ) * K₁, ν, ?_, hν, ?_⟩
  · have : 0 ≤ ((wordsLE (k + 1)).card : ℝ) * K₁ := mul_nonneg (Nat.cast_nonneg _) hK₁0
    linarith
  intro v hv φ D M hJ hDM n j hj
  let χ : ℝ × ℝ → ℂ := fun _ => 0
  let Dχ : List (Fin 2) → ℝ × ℝ → ℂ := fun _ _ => 0
  have hJχ : IsCellJet c m (k + 1) χ Dχ := isCellJet_zero c m (k + 1)
  have hφp := st_jet_periodic hJ
  have hφm := st_jet_memX hJ
  have hχp := st_jet_periodic hJχ
  have hχm := st_jet_memX hJχ
  obtain ⟨hGs, hGp, hGm⟩ := cellMollSmooth c m n φ hc hφp hφm
  obtain ⟨hXs, -, hXm⟩ := cellMollSmooth c m n χ hc hχp hχm
  obtain ⟨hTs, -, hTm⟩ := st_trans_reg cellMollSmooth cellConvDeriv hc hv hφp hφm n
  have hM' : ∀ w : List (Fin 2), w.length ≤ k → xNorm c (-m) (D w) ≤ ENNReal.ofReal |M| :=
    fun w hw => (hDM w hw).trans (ENNReal.ofReal_le_ofReal (le_abs_self M))
  have hTW : ∀ w : List (Fin 2), w.length ≤ k + 1 →
      2 * ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)) ≤
        CT * (cellEnergy c m w.length (cellMoll n φ) + |M| ^ 2) +
          CT * |M| * ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal :=
    hCT v hv φ D |M| (abs_nonneg M) hJ hM' n
  have hword : ∀ w ∈ wordsLE j,
      -(2 * ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (mollRate ν v n φ χ))) ≤
        -ν * ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal ^ 2 +
          K₁ * (cellEnergy c m j (cellMoll n φ) + M ^ 2) := by
    intro w hwW
    have hwj : w.length ≤ j := mem_wordsLE.1 hwW
    have hwk : w.length ≤ k + 1 := hwj.trans hj
    have hFs : ContDiff ℝ ∞ (adjSpatial w (cellMoll n φ)) := st_contDiff_adjSpatial hGs w
    have hFp := st_adjSpatial_periodic hGp w
    have hFm : MemLp (adjSpatial w (cellMoll n φ)) 2 (B0579.cellMeasure c (-m)) := hGm w
    have hLs : ContDiff ℝ ∞ (stLap (cellMoll n φ)) := st_contDiff_stLap hGs
    have hνLs : ContDiff ℝ ∞ (fun x => (ν : ℂ) * stLap (cellMoll n φ) x) :=
      contDiff_const.mul hLs
    have hBs : ContDiff ℝ ∞ (fun x => (ν : ℂ) * stLap (cellMoll n φ) x + stTrans v n φ x) :=
      hνLs.add hTs
    have hsplit : adjSpatial w (mollRate ν v n φ χ) = fun x =>
        -((ν : ℂ) * adjSpatial w (stLap (cellMoll n φ)) x + adjSpatial w (stTrans v n φ) x -
          adjSpatial w (cellMoll n χ) x) := by
      rw [mollRate_eq_st, st_adjSpatial_neg _ w, st_adjSpatial_sub hBs hXs w,
        st_adjSpatial_add hνLs hTs w, st_adjSpatial_const_mul _ hLs w]
    have hLw : MemLp (adjSpatial w (stLap (cellMoll n φ))) 2 (B0579.cellMeasure c (-m)) := by
      rw [st_adjSpatial_stLap stAdjComm hGs w]
      exact (hGm (0 :: 0 :: w)).add (hGm (1 :: 1 :: w))
    have hTw : MemLp (adjSpatial w (stTrans v n φ)) 2 (B0579.cellMeasure c (-m)) := hTm w
    have hXw : MemLp (adjSpatial w (cellMoll n χ)) 2 (B0579.cellMeasure c (-m)) := hXm w
    have hνLw : MemLp (fun x => (ν : ℂ) * adjSpatial w (stLap (cellMoll n φ)) x) 2
        (B0579.cellMeasure c (-m)) := hLw.const_mul _
    have hBw : MemLp (fun x => (ν : ℂ) * adjSpatial w (stLap (cellMoll n φ)) x +
        adjSpatial w (stTrans v n φ) x) 2 (B0579.cellMeasure c (-m)) := hνLw.add hTw
    have hipx : ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (mollRate ν v n φ χ)) =
        -(ν * ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stLap (cellMoll n φ))) +
          ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)) -
          ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ))) := by
      rw [hsplit, st_ipX_neg_right, st_ipX_sub_right hFm hBw hXw,
        st_ipX_add_right hFm hνLw hTw, st_ipX_real_mul_right]
    have hIL : ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stLap (cellMoll n φ))) =
        ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (0 :: 0 :: w) (cellMoll n φ)) +
          ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (1 :: 1 :: w) (cellMoll n φ)) := by
      rw [st_adjSpatial_stLap stAdjComm hGs w]
      exact st_ipX_add_right hFm (hGm (0 :: 0 :: w)) (hGm (1 :: 1 :: w))
    have hdiff : ∀ l : Fin 2,
        ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (l :: l :: w) (cellMoll n φ)) ≤
          -(xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal ^ 2 +
            2 * |m| * (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal *
              (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal := by
      intro l
      have hH : MemLp (adjSpatial (l :: w) (cellMoll n φ)) 2 (B0579.cellMeasure c (-m)) :=
        hGm (l :: w)
      have h : |ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (l :: l :: w) (cellMoll n φ)) +
          ipX c m (adjSpatial (l :: w) (cellMoll n φ)) (adjSpatial (l :: w) (cellMoll n φ))| ≤
          2 * |m| * (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal *
            (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal :=
        stCellIbp c m l (adjSpatial w (cellMoll n φ)) (adjSpatial (l :: w) (cellMoll n φ))
          hc hFs (st_contDiff_adjSpatial hGs (l :: w)) hFp (st_adjSpatial_periodic hGp (l :: w))
          hFm hH hH (hGm (l :: l :: w))
      have hself := st_ipX_self hH
      have h2 := (abs_le.mp h).2
      linarith
    have hXnorm : (xNorm c (-m) (adjSpatial w (cellMoll n χ))).toReal ≤
        Cm * (|(0 : ℝ)| * |M|) := by
      rw [st_adjSpatial_cellMoll_jet cellMollWeakDeriv hc hJχ n w hwk]
      have h1 := hCm n (Dχ w) (hJχ.periodic w hwk) (hJχ.memX w hwk)
      have h2 : xNorm c (-m) (Dχ w) = 0 := by unfold xNorm Dχ; simp
      rw [h2, mul_zero] at h1
      have h3 : (xNorm c (-m) (cellMoll n (Dχ w))).toReal ≤ 0 :=
        ENNReal.toReal_le_of_le_ofReal le_rfl (by simpa using h1)
      have h4 : 0 ≤ Cm * (|(0 : ℝ)| * |M|) := by positivity
      linarith
    have hX : -ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ)) ≤
        (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal * (Cm * (|(0 : ℝ)| * |M|)) := by
      have h1 := st_abs_ipX_le hFm hXw
      have h2 := mul_le_mul_of_nonneg_left hXnorm
        (ENNReal.toReal_nonneg (a := xNorm c (-m) (adjSpatial w (cellMoll n φ))))
      have h3 := neg_abs_le (ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ)))
      linarith
    have hY := st_word_young (ν := ν) (a := |m|) (CT := CT) (Cm := Cm) (b := |(0 : ℝ)|) (M := |M|)
      (t := t) (e := (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal)
      (d0 := (xNorm c (-m) (adjSpatial (0 :: w) (cellMoll n φ))).toReal)
      (d1 := (xNorm c (-m) (adjSpatial (1 :: w) (cellMoll n φ))).toReal)
      (I0 := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (0 :: 0 :: w) (cellMoll n φ)))
      (I1 := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (1 :: 1 :: w) (cellMoll n φ)))
      (IT := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)))
      (IX := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ)))
      (Nw := cellEnergy c m w.length (cellMoll n φ)) (Nj := cellEnergy c m j (cellMoll n φ))
      hν hCTt hCT0 hCm0 (abs_nonneg m) (abs_nonneg (0 : ℝ)) ENNReal.toReal_nonneg (abs_nonneg M)
      (hdiff 0) (hdiff 1) (by simpa [Fin.sum_univ_two] using hTW w hwk) hX
      (sq_toReal_le_cellEnergy c m (cellMoll n φ) hwj) (st_cellEnergy_mono c m hwj _)
    rw [hipx, hIL]
    simp only [Fin.sum_univ_two]
    rw [sq_abs M] at hY
    linarith
  have hsum := Finset.sum_le_sum hword
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hE : cellEnergy c m (j + 1) (cellMoll n φ) =
      (xNorm c (-m) (cellMoll n φ)).toReal ^ 2 + ∑ w ∈ wordsLE j, ∑ l : Fin 2,
        (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal ^ 2 := by
    unfold cellEnergy
    rw [st_sum_wordsLE_succ]
    rfl
  have hN0 : (xNorm c (-m) (cellMoll n φ)).toReal ^ 2 ≤ cellEnergy c m j (cellMoll n φ) :=
    sq_toReal_le_cellEnergy c m (cellMoll n φ) (w := []) (Nat.zero_le j)
  have hcard : ((wordsLE j).card : ℝ) ≤ ((wordsLE (k + 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (st_wordsLE_mono hj)
  have hNj0 := cellEnergy_nonneg c m j (cellMoll n φ)
  have hKM : 0 ≤ K₁ * (cellEnergy c m j (cellMoll n φ) + M ^ 2) :=
    mul_nonneg hK₁0 (add_nonneg hNj0 (sq_nonneg M))
  have hc1 := mul_le_mul_of_nonneg_right hcard hKM
  have hc2 := mul_le_mul_of_nonneg_left hN0 hν.le
  have hc3 : ν * cellEnergy c m j (cellMoll n φ) ≤
      ν * (cellEnergy c m j (cellMoll n φ) + M ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg M]) hν.le
  unfold energyRate
  rw [hE, ← Finset.sum_neg_distrib]
  nlinarith

/-- `v_l(r) φ(r)` is periodic, lies in `X_{-m,c}`, and varies continuously in `X_{-m,c}` on
`(a, b)` for any `PartI.IsBUCTrain` and `IsFreeAdjointWeak`. -/
theorem freeVelXFam {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s a b : ℝ} (ht : 0 ≤ t) (hts : t < s)
    (hta : t ≤ a) (hbs : b < s) {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν c m tr t s g φ) (l : Fin 2) :
    XFam c m a b (fun r y => ((tr.v r y l : ℝ) : ℂ) * φ r y) := by
  obtain ⟨C, hC0, hCb⟩ := buc_vel_bound hbuc (ht.trans hts.le)
  have hsm : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hyr : ∀ ρ : ℝ, 0 ≤ ρ → Continuous (fun y : ℝ × ℝ => tr.v ρ y l) := by
    intro ρ hρ
    have hcont : Continuous (fun y : ℝ × ℝ => tr.v ρ y) :=
      hsm.comp_continuous (f := fun y : ℝ × ℝ => (ρ, y)) (by fun_prop)
        (fun _ => ⟨hρ, mem_univ _⟩)
    exact (continuous_apply l).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).comp hcont)
  have hsub : Ioo a b ⊆ Icc t s := fun x hx => ⟨hta.trans hx.1.le, hx.2.le.trans hbs.le⟩
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have hr0 : 0 ≤ r := ht.trans (hta.trans hr.1.le)
    have hrs : r ∈ Icc t s := hsub hr
    have hrI : r ∈ Ico t s := ⟨hta.trans hr.1.le, hr.2.trans hbs⟩
    refine ⟨fun x => ?_, ?_⟩
    · dsimp only
      rw [tr.isTrain.periodic_v r hr0 x, hφ.periodic r hrI x]
    · have hmeas : AEStronglyMeasurable (fun y : ℝ × ℝ => ((tr.v r y l : ℝ) : ℂ) * φ r y)
          (B0579.cellMeasure c (-m)) :=
        (Complex.continuous_ofReal.comp (hyr r hr0)).aestronglyMeasurable.mul (hφ.memX r hrs).1
      refine MemLp.of_le ((hφ.memX r hrs).const_mul ((C : ℝ) : ℂ)) hmeas
        (Eventually.of_forall fun y => ?_)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hCb r ⟨hr0, hrs.2⟩ y l) (norm_nonneg _)
  · have hr0 : 0 ≤ r := ht.trans (hta.trans hr.1.le)
    have hrI : r ∈ Icc t s := hsub hr
    have hFc : Continuous (fun w : EuclideanSpace ℝ (Fin 2) => ((w l : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply l).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)))
    have htc : ∀ y : ℝ × ℝ, Tendsto (fun r' => ((tr.v r' y l : ℝ) : ℂ)) (𝓝[Ioo a b] r)
        (𝓝 ((tr.v r y l : ℝ) : ℂ)) := by
      intro y
      have h1 : ContinuousWithinAt (fun r' : ℝ => ((r', y) : ℝ × (ℝ × ℝ))) (Ioo a b) r :=
        continuousWithinAt_id.prodMk continuousWithinAt_const
      have h2 : ContinuousWithinAt (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici 0 ×ˢ univ) (r, y) :=
        hsm.continuousWithinAt ⟨hr0, mem_univ _⟩
      have h3 : ContinuousWithinAt (fun r' : ℝ => tr.v r' y) (Ioo a b) r :=
        ContinuousWithinAt.comp (f := fun r' : ℝ => ((r', y) : ℝ × (ℝ × ℝ))) (x := r) h2 h1
          (fun x hx => ⟨ht.trans (hta.trans hx.1.le), mem_univ _⟩)
      exact hFc.continuousAt.comp_continuousWithinAt h3
    have hvb : ∀ ρ ∈ Ioo a b, ∀ y : ℝ × ℝ, |tr.v ρ y l| ≤ C := fun ρ hρ y =>
      hCb ρ ⟨ht.trans (hta.trans hρ.1.le), hρ.2.le.trans hbs.le⟩ y l
    have hBt : Tendsto (fun r' => eLpNorm (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y)
        2 (B0579.cellMeasure c (-m))) (𝓝[Ioo a b] r) (𝓝 0) := by
      refine eLpNorm_mul_tendsto_zero (φ := φ r) (K := 2 * C) (hφ.memX r hrI) ?_ ?_ ?_
      · exact eventually_nhdsWithin_of_forall fun r' hr' =>
          (Complex.continuous_ofReal.comp ((hyr r' (ht.trans (hta.trans hr'.1.le))).sub
            (hyr r hr0))).aestronglyMeasurable
      · refine eventually_nhdsWithin_of_forall fun r' hr' => Eventually.of_forall fun y => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        have h1 := abs_le.1 (hvb r' hr' y)
        have h2 := abs_le.1 (hvb r hr y)
        exact ⟨by linarith, by linarith⟩
      · refine Eventually.of_forall fun y => ?_
        have := (htc y).sub_const ((tr.v r y l : ℝ) : ℂ)
        simp only [sub_self] at this
        simpa [Complex.ofReal_sub] using this
    have hsc : Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Ioo a b] r) (𝓝 0) :=
      (hφ.strongCont r hrI).mono_left (nhdsWithin_mono r hsub)
    have hAt : Tendsto (fun r' => ‖((C : ℝ) : ℂ)‖ₑ * xNorm c (-m) (φ r' - φ r))
        (𝓝[Ioo a b] r) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hsc (Or.inr (enorm_ne_top (x := ((C : ℝ) : ℂ))))
      simpa using this
    have hsum : Tendsto (fun r' =>
        ‖((C : ℝ) : ℂ)‖ₑ * xNorm c (-m) (φ r' - φ r) +
          eLpNorm (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y) 2
            (B0579.cellMeasure c (-m))) (𝓝[Ioo a b] r) (𝓝 0) := by
      simpa using hAt.add hBt
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (eventually_nhdsWithin_of_forall fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _))
      (eventually_nhdsWithin_of_forall fun r' hr' => ?_)
    have hr'I : r' ∈ Icc t s := hsub hr'
    have hdec : (fun y => ((tr.v r' y l : ℝ) : ℂ) * φ r' y) -
        (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) =
        (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y)) +
          (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y) := by
      funext y; simp only [Pi.sub_apply, Pi.add_apply]; push_cast; ring
    have hAm : AEStronglyMeasurable (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y))
        (B0579.cellMeasure c (-m)) :=
      (Complex.continuous_ofReal.comp (hyr r' (ht.trans (hta.trans hr'.1.le)))).aestronglyMeasurable.mul
        ((hφ.memX r' hr'I).1.sub (hφ.memX r hrI).1)
    have hBm : AEStronglyMeasurable (fun y => ((tr.v r' y l - tr.v r y l : ℝ) : ℂ) * φ r y)
        (B0579.cellMeasure c (-m)) :=
      (Complex.continuous_ofReal.comp ((hyr r' (ht.trans (hta.trans hr'.1.le))).sub
        (hyr r hr0))).aestronglyMeasurable.mul (hφ.memX r hrI).1
    have hAbound : eLpNorm (fun y => ((tr.v r' y l : ℝ) : ℂ) * (φ r' y - φ r y)) 2
        (B0579.cellMeasure c (-m)) ≤ ‖((C : ℝ) : ℂ)‖ₑ * xNorm c (-m) (φ r' - φ r) := by
      unfold xNorm
      rw [← eLpNorm_const_smul ((C : ℝ) : ℂ) (φ r' - φ r) 2]
      refine eLpNorm_mono_ae (Eventually.of_forall fun y => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hvb r' hr' y) (norm_nonneg _)
    rw [xNorm, hdec]
    exact (eLpNorm_add_le hAm hBm (by norm_num)).trans (add_le_add hAbound le_rfl)

/-- Tested identity for `mollRate` with `χ = 0` against a cylinder test `ψ` (`0 < c`). -/
theorem freeMollRateTested {ν c m : ℝ} (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    {r : ℝ} {φ : ℝ × ℝ → ℂ} (hφp : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x)
    (hφm : MemLp φ 2 (B0579.cellMeasure c (-m)))
    (hVp : ∀ (l : Fin 2) (x : ℝ × ℝ),
      ((tr.v r (x.1 + c, x.2) l : ℝ) : ℂ) * φ (x.1 + c, x.2) = ((tr.v r x l : ℝ) : ℂ) * φ x)
    (hVm : ∀ l : Fin 2, MemLp (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y) 2 (B0579.cellMeasure c (-m)))
    (n : ℕ) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c, mollRate ν (tr.v r) n φ (fun _ => 0) x * (ψ x : ℂ) =
      -∫ x in B0579.cell c, freeAdjIntegrand tr φ r (mollR n ψ) x := by
  have hDual := mollDual cellPeriodicLocInt cellConvDeriv
  have hG := cellMollSmooth c m n φ hc hφp hφm
  have hdu := hDual c m n hc ψ hψ
  have hψ' : B0579.IsCylTest c (mollR n ψ) := hdu.1
  have hpd : ∀ l : Fin 2, B0579.pd l (mollR n ψ) = mollR n (B0579.pd l ψ) := hdu.2.1
  have hpdpd : ∀ l : Fin 2,
      B0579.pd l (B0579.pd l (mollR n ψ)) = mollR n (B0579.pd l (B0579.pd l ψ)) := by
    intro l
    rw [hpd l]
    exact (hDual c m n hc (B0579.pd l ψ) (hψ.pd l)).2.1 l
  have hpart3 : ∀ h : ℝ × ℝ → ℝ, B0579.IsCylTest c h →
      ∫ x in B0579.cell c, cellMoll n φ x * (h x : ℂ) =
        ∫ x in B0579.cell c, φ x * (mollR n h x : ℂ) :=
    fun h hh => ((hDual c m n hc h hh).2.2 φ hφp hφm).2
  have hKV : ∀ (l : Fin 2) (x : ℝ × ℝ),
      cellConv (B0579.pd l (molKer n)) (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y) x =
        pdCx l (cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y)) x := by
    intro l x
    have e := (cellConvDeriv c m (molKer n) (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y) hc
      (molKer_props_mrt n).1 (molKer_props_mrt n).2.1 (hVp l) (hVm l)).2.2 [l]
    simp only [adjSpatial, pdWordR] at e
    exact congrFun e.symm x
  have hI00 : IntegrableOn (fun x => adjSpatial [0, 0] (cellMoll n φ) x * (ψ x : ℂ))
      (B0579.cell c) :=
    xMulTestInt c m (adjSpatial [0, 0] (cellMoll n φ)) ψ hc (hG.2.2 [0, 0]) hψ
  have hI11 : IntegrableOn (fun x => adjSpatial [1, 1] (cellMoll n φ) x * (ψ x : ℂ))
      (B0579.cell c) :=
    xMulTestInt c m (adjSpatial [1, 1] (cellMoll n φ)) ψ hc (hG.2.2 [1, 1]) hψ
  have hMl0 := cellMollSmooth c m n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y) hc (hVp 0) (hVm 0)
  have hMl1 := cellMollSmooth c m n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y) hc (hVp 1) (hVm 1)
  have hIK0 : IntegrableOn
      (fun x => pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ))
      (B0579.cell c) :=
    xMulTestInt c m (adjSpatial [0] (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)))
      ψ hc (hMl0.2.2 [0]) hψ
  have hIK1 : IntegrableOn
      (fun x => pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ))
      (B0579.cell c) :=
    xMulTestInt c m (adjSpatial [1] (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)))
      ψ hc (hMl1.2.2 [1]) hψ
  have hIC : IntegrableOn (fun x => cellMoll n (fun _ => (0 : ℂ)) x * (ψ x : ℂ)) (B0579.cell c) :=
    ((hDual c m n hc ψ hψ).2.2 (fun _ => 0) (fun _ => rfl) MemLp.zero).1
  have hV0 : IntegrableOn (fun x => ((tr.v r x 0 : ℝ) : ℂ) * φ x * (B0579.pd 0 (mollR n ψ) x : ℂ))
      (B0579.cell c) :=
    xMulTestInt c m (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y) (B0579.pd 0 (mollR n ψ))
      hc (hVm 0) (hψ'.pd 0)
  have hV1 : IntegrableOn (fun x => ((tr.v r x 1 : ℝ) : ℂ) * φ x * (B0579.pd 1 (mollR n ψ) x : ℂ))
      (B0579.cell c) :=
    xMulTestInt c m (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y) (B0579.pd 1 (mollR n ψ))
      hc (hVm 1) (hψ'.pd 1)
  have hsplit : ∀ x : ℝ × ℝ,
      mollRate ν (tr.v r) n φ (fun _ => 0) x * (ψ x : ℂ) =
        -((ν : ℂ) * (adjSpatial [0, 0] (cellMoll n φ) x * (ψ x : ℂ) +
            adjSpatial [1, 1] (cellMoll n φ) x * (ψ x : ℂ)) +
          (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ) +
            pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ)) -
          cellMoll n (fun _ => (0 : ℂ)) x * (ψ x : ℂ)) := by
    intro x
    unfold mollRate
    simp only [Fin.sum_univ_two]
    rw [hKV 0 x, hKV 1 x]
    ring
  have hF : ∫ x in B0579.cell c,
      (adjSpatial [0, 0] (cellMoll n φ) x * (ψ x : ℂ) +
        adjSpatial [1, 1] (cellMoll n φ) x * (ψ x : ℂ)) =
      ∫ x in B0579.cell c, φ x * (lapP (mollR n ψ) x : ℂ) := by
    rw [integral_add hI00 hI11,
      ibp_pdpd_mrt cellIBP c hc (cellMoll n φ) hG.1 hG.2.1 ψ hψ 0,
      ibp_pdpd_mrt cellIBP c hc (cellMoll n φ) hG.1 hG.2.1 ψ hψ 1,
      hpart3 _ ((hψ.pd 0).pd 0), hpart3 _ ((hψ.pd 1).pd 1)]
    have hpt : ∀ x : ℝ × ℝ, φ x * (lapP (mollR n ψ) x : ℂ) =
        φ x * (mollR n (B0579.pd 0 (B0579.pd 0 ψ)) x : ℂ) +
          φ x * (mollR n (B0579.pd 1 (B0579.pd 1 ψ)) x : ℂ) := by
      intro x
      unfold lapP
      rw [hpdpd 0, hpdpd 1]
      push_cast
      ring
    have hA0 : IntegrableOn (fun x => φ x * (mollR n (B0579.pd 0 (B0579.pd 0 ψ)) x : ℂ))
        (B0579.cell c) :=
      xMulTestInt c m φ (mollR n (B0579.pd 0 (B0579.pd 0 ψ))) hc hφm
        ((hDual c m n hc (B0579.pd 0 (B0579.pd 0 ψ)) ((hψ.pd 0).pd 0)).1)
    have hA1 : IntegrableOn (fun x => φ x * (mollR n (B0579.pd 1 (B0579.pd 1 ψ)) x : ℂ))
        (B0579.cell c) :=
      xMulTestInt c m φ (mollR n (B0579.pd 1 (B0579.pd 1 ψ))) hc hφm
        ((hDual c m n hc (B0579.pd 1 (B0579.pd 1 ψ)) ((hψ.pd 1).pd 1)).1)
    simp only [hpt]
    rw [integral_add hA0 hA1]
  have hl : ∀ l : Fin 2,
      ∫ x in B0579.cell c,
          pdCx l (cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ) =
        -∫ x in B0579.cell c,
          ((tr.v r x l : ℝ) : ℂ) * φ x * (B0579.pd l (mollR n ψ) x : ℂ) := by
    intro l
    have hMl := cellMollSmooth c m n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y) hc (hVp l) (hVm l)
    have h1 := cellIBP c (cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y)) ψ hc
      hMl.1 hMl.2.1 hψ l
    have h2 := (hDual c m n hc (B0579.pd l ψ) (hψ.pd l)).2.2
      (fun y => ((tr.v r y l : ℝ) : ℂ) * φ y) (hVp l) (hVm l)
    rw [h2.2] at h1
    simp only [hpd l]
    rw [h1, neg_neg]
  have hQ : ∫ x in B0579.cell c,
      (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ) +
        pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ)) =
      -∫ x in B0579.cell c,
        φ x * ((tr.v r x 0 * B0579.pd 0 (mollR n ψ) x +
          tr.v r x 1 * B0579.pd 1 (mollR n ψ) x : ℝ) : ℂ) := by
    rw [integral_add hIK0 hIK1, hl 0, hl 1, ← neg_add, ← integral_add hV0 hV1]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun _ => by push_cast; ring)
  have hC : ∫ x in B0579.cell c, cellMoll n (fun _ => (0 : ℂ)) x * (ψ x : ℂ) = 0 := by
    rw [((hDual c m n hc ψ hψ).2.2 (fun _ => 0) (fun _ => rfl) MemLp.zero).2]
    simp
  have hI2 : IntegrableOn (fun x => (ν : ℂ) * (adjSpatial [0, 0] (cellMoll n φ) x * (ψ x : ℂ) +
        adjSpatial [1, 1] (cellMoll n φ) x * (ψ x : ℂ))) (B0579.cell c) :=
    Integrable.const_mul (hI00.add hI11) (ν : ℂ)
  have hI3 : IntegrableOn (fun x =>
      pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ) +
        pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ))
      (B0579.cell c) := hIK0.add hIK1
  have hLHS : ∫ x in B0579.cell c, mollRate ν (tr.v r) n φ (fun _ => 0) x * (ψ x : ℂ) =
      -((ν : ℂ) * (∫ x in B0579.cell c,
          (adjSpatial [0, 0] (cellMoll n φ) x * (ψ x : ℂ) +
            adjSpatial [1, 1] (cellMoll n φ) x * (ψ x : ℂ))) +
        (∫ x in B0579.cell c,
          (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ) +
            pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ))) -
        ∫ x in B0579.cell c, cellMoll n (fun _ => (0 : ℂ)) x * (ψ x : ℂ)) := by
    have hI4 : IntegrableOn (fun x =>
        (ν : ℂ) * (adjSpatial [0, 0] (cellMoll n φ) x * (ψ x : ℂ) +
          adjSpatial [1, 1] (cellMoll n φ) x * (ψ x : ℂ)) +
        (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ) +
          pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ y)) x * (ψ x : ℂ)))
        (B0579.cell c) := hI2.add hI3
    simp only [hsplit]
    rw [integral_neg, integral_sub hI4 hIC, integral_add hI2 hI3, integral_const_mul]
  have hRHS : ∫ x in B0579.cell c, freeAdjIntegrand tr φ r (mollR n ψ) x =
      (ν : ℂ) * (∫ x in B0579.cell c, φ x * (lapP (mollR n ψ) x : ℂ)) -
        ∫ x in B0579.cell c, φ x * ((tr.v r x 0 * B0579.pd 0 (mollR n ψ) x +
          tr.v r x 1 * B0579.pd 1 (mollR n ψ) x : ℝ) : ℂ) := by
    have hIL : IntegrableOn (fun x => (ν : ℂ) * (φ x * (lapP (mollR n ψ) x : ℂ))) (B0579.cell c) :=
      (xMulTestInt c m φ (lapP (mollR n ψ)) hc hφm (isCylTest_lapP hψ')).const_mul (ν : ℂ)
    have hIV : IntegrableOn (fun x => φ x * ((tr.v r x 0 * B0579.pd 0 (mollR n ψ) x +
        tr.v r x 1 * B0579.pd 1 (mollR n ψ) x : ℝ) : ℂ)) (B0579.cell c) := by
      refine (hV0.add hV1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
      simp only [Pi.add_apply]; push_cast; ring
    have hpt : ∀ x : ℝ × ℝ, freeAdjIntegrand tr φ r (mollR n ψ) x =
        (ν : ℂ) * (φ x * (lapP (mollR n ψ) x : ℂ)) -
          φ x * ((tr.v r x 0 * B0579.pd 0 (mollR n ψ) x +
            tr.v r x 1 * B0579.pd 1 (mollR n ψ) x : ℝ) : ℂ) := by
      intro x; unfold freeAdjIntegrand UnforcedLeray.Short.IIb.lapP lapP; push_cast; ring
    simp_rw [hpt]
    rw [integral_sub hIL hIV, integral_const_mul]
  rw [hLHS, hRHS, hF, hQ, hC]
  ring

/-- Age differentiability of the mollified energies for `IsFreeAdjointWeak` (`χ = 0`). -/
theorem freeMollRateDeriv (m : ℝ) {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ)
    (hTD : FreeTestedDeriv tr t s φ) {a b : ℝ} (hta : t ≤ a) (hbs : b < s) (n j : ℕ) :
    ContinuousOn (fun r => cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r))) (Icc a b) ∧
      ∀ r ∈ Ioo a b,
        HasDerivAt (fun r' => cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r')))
          (energyRate (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r))
            (mollRate ν (tr.v r) n (φ r) (fun _ => 0))) r := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hIcc : ∀ r ∈ Icc a b, r ∈ Icc t s := fun r hr => ⟨hta.trans hr.1, hr.2.trans hbs.le⟩
  have hIco : ∀ r ∈ Icc a b, r ∈ Ico t s := fun r hr => ⟨hta.trans hr.1, hr.2.trans_lt hbs⟩
  have hIoo : ∀ r ∈ Ioo a b, r ∈ Icc a b := fun r hr => ⟨hr.1.le, hr.2.le⟩
  have hφX : XFam c m a b φ :=
    ⟨fun r hr => ⟨hφ.periodic r (hIco r (hIoo r hr)), hφ.memX r (hIcc r (hIoo r hr))⟩,
      fun r hr => (hφ.strongCont r (hIcc r (hIoo r hr))).mono_left
        (nhdsWithin_mono _ (fun x hx => hIcc x (hIoo x hx)))⟩
  have hVX : ∀ l : Fin 2, XFam c m a b (fun r y => ((tr.v r y l : ℝ) : ℂ) * φ r y) :=
    fun l => freeVelXFam tr hbuc ht hts hta hbs hφ l
  have h0X : XFam c m a b (fun _ _ => (0 : ℂ)) :=
    ⟨fun _ _ => ⟨fun _ => rfl, MemLp.zero⟩, fun _ _ => by
      have hz : ∀ r' : ℝ, xNorm c (-m) ((fun _ => (0 : ℂ)) - (fun _ => (0 : ℂ))) = 0 :=
        fun _ => by unfold xNorm; simp
      exact (tendsto_const_nhds (x := (0 : ℝ≥0∞))).congr fun r' => (hz r').symm⟩
  have hJ := mollConvJet smoothCellJet cellConvDeriv cellConvBound cellPeriodicLocInt
  have hR := mollRateJetAbs hJ cellConvDeriv
  have hDual := mollDual cellPeriodicLocInt cellConvDeriv
  obtain ⟨hKs, hKc, hKb⟩ := mollKerProps n
  have hFjet : AdjHkAll c m (Ioo a b) (fun r => cellMoll n (φ r))
      (fun r w => adjSpatial w (cellMoll n (φ r))) :=
    hJ c m (molKer n) φ a b hc hKs hKc hKb hφX
  have hRjet : AdjHkAll c m (Ioo a b)
      (fun r => mollRate ν (tr.v r) n (φ r) (fun _ => 0))
      (fun r w => adjSpatial w (mollRate ν (tr.v r) n (φ r) (fun _ => 0))) :=
    hR c m ν n a b φ (fun _ _ => 0) (fun l r y => ((tr.v r y l : ℝ) : ℂ) * φ r y) hc hφX hVX h0X
  have hmemF : ∀ r ∈ Ioo a b, ∀ w : List (Fin 2),
      MemLp (adjSpatial w (cellMoll n (φ r))) 2 (B0579.cellMeasure c (-m)) :=
    fun r hr w => (hFjet.1 r hr w.length).memX w le_rfl
  have hmemR : ∀ r ∈ Ioo a b, ∀ w : List (Fin 2),
      MemLp (adjSpatial w (mollRate ν (tr.v r) n (φ r) (fun _ => 0))) 2
        (B0579.cellMeasure c (-m)) :=
    fun r hr w => (hRjet.1 r hr w.length).memX w le_rfl
  have htest : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ r ∈ Ioo a b,
      HasDerivAt (fun r' => ∫ x in B0579.cell c, cellMoll n (φ r') x * (ψ x : ℂ))
        (∫ x in B0579.cell c, mollRate ν (tr.v r) n (φ r) (fun _ => 0) x * (ψ x : ℂ)) r := by
    intro ψ hψ r hr
    obtain ⟨hψ', -, hdual⟩ := hDual c m n hc ψ hψ
    have hrI : r ∈ Ioo t s := ⟨hta.trans_lt hr.1, hr.2.trans hbs⟩
    have hderiv := ((hTD (mollR n ψ) hψ').2 r ⟨hrI.1.le, hrI.2.le⟩).hasDerivAt
      (Icc_mem_nhds hrI.1 hrI.2)
    have h1 : HasDerivAt (fun r' => ∫ x in B0579.cell c, cellMoll n (φ r') x * (ψ x : ℂ))
        (-∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r (mollR n ψ) x) r := by
      refine hderiv.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hrI.1 hrI.2] with q hq
      exact (hdual (φ q) (hφ.periodic q ⟨hq.1.le, hq.2⟩) (hφ.memX q ⟨hq.1.le, hq.2.le⟩)).2
    have h2 := freeMollRateTested (m := m) hc tr (hφ.periodic r (hIco r (hIoo r hr)))
      (hφ.memX r (hIcc r (hIoo r hr))) (fun l => (hVX l).1 r hr |>.1)
      (fun l => (hVX l).1 r hr |>.2) n hψ
    rw [h2]
    exact h1
  have hHas : HasXDerivOn c m (Ioo a b) (fun r => cellMoll n (φ r))
      (fun r => mollRate ν (tr.v r) n (φ r) (fun _ => 0)) :=
    xDerivOfTested c m a b _ _ hc (fun r hr => hmemF r hr [])
      (fun r hr => hmemR r hr []) (fun r hr => hRjet.2 [] r hr) htest
  have hHasW := (xDerivUpgrade_of xDerivOfTested testedOfXDeriv) c m a b _ _ _ _ hc hFjet hRjet hHas
  refine ⟨(energyContAbs cellConvBound cellConvDeriv cellPeriodicLocInt mollKerProps)
    c m j n a b φ hc (fun r hr => ⟨hφ.periodic r (hIco r hr), hφ.memX r (hIcc r hr)⟩)
    (fun r hr => (hφ.strongCont r (hIcc r hr)).mono_left
      (nhdsWithin_mono _ (fun x hx => hIcc x hx))), fun r hr => ?_⟩
  exact energyDerivAbs c m j _ _ a b hc (fun r hr w => ⟨hmemF r hr w, hmemR r hr w⟩) hHasW r hr

/-- One gain of spatial regularity on `[a, b']` (`b' < b < s`) for `IsFreeAdjointWeak`. -/
theorem freeHkGainJet {m ν : ℝ} (hν : 0 < ν)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ)
    (hTD : FreeTestedDeriv tr t s φ) (k : ℕ) {a b b' : ℝ} (hta : t ≤ a)
    (hbs : b < s) (hb' : b' < b) {D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} {M : ℝ}
    (hDj : ∀ r ∈ Icc a b, IsCellJet (ν ^ (-2 : ℝ)) m k (φ r) (D r))
    (hDM : ∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k →
      xNorm (ν ^ (-2 : ℝ)) (-m) (D r w) ≤ ENNReal.ofReal M) :
    ∃ M' : ℝ, ∀ r ∈ Icc a b',
      IsCellJet (ν ^ (-2 : ℝ)) m (k + 1) (φ r) (jetExt (ν ^ (-2 : ℝ)) m k (D r)) ∧
      ∀ w : List (Fin 2), w.length ≤ k + 1 →
        xNorm (ν ^ (-2 : ℝ)) (-m) (jetExt (ν ^ (-2 : ℝ)) m k (D r) w) ≤ ENNReal.ofReal M' := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨Av, hAv⟩ := freeSliceVel tr hbuc (ht.trans hts.le)
  obtain ⟨C, β, hC0, hβ, hSt⟩ := freeStaticMollEnergy m hν k Av
  obtain ⟨K, hK0, hK⟩ := adjointEnergyChain C hC0
  obtain ⟨Cm, hCm0, hCm⟩ := cellMollBound c m hc
  set Mp := max M 0
  have hMp0 : 0 ≤ Mp := le_max_right _ _
  have hDMp : ∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k →
      xNorm c (-m) (D r w) ≤ ENNReal.ofReal Mp :=
    fun r hr w hw => (hDM r hr w hw).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set β' := min β 1
  have hβ'0 : 0 < β' := lt_min hβ one_pos
  have hβ'β : β' ≤ β := min_le_left _ _
  set δ := min (b - b') 1
  have hδ0 : 0 < δ := lt_min (sub_pos.2 hb') one_pos
  set E0 := ((wordsLE k).card : ℝ) * (Cm * Mp) ^ 2 + M ^ 2 with hE0
  have hE00 : 0 ≤ E0 := by positivity
  set Bnd := K * (β' * δ)⁻¹ * E0
  have hM₁ : ∀ r₀ ∈ Icc a b', ∀ w : List (Fin 2), w.length = k → ∀ j : Fin 2,
      ∃ G : ℝ × ℝ → ℂ,
        (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) ∧
        MemLp G 2 (B0579.cellMeasure c (-m)) ∧
        HasWeakCellDerivC c j (D r₀ w) G ∧
        xNorm c (-m) G ≤ ENNReal.ofReal (2 * Real.sqrt Bnd) := by
    intro r₀ hr₀ w hw j
    have hr₀ab : r₀ ∈ Icc a b := ⟨hr₀.1, hr₀.2.trans hb'.le⟩
    have hper : ∀ r ∈ Icc a b, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x :=
      fun r hr x => hφ.periodic r ⟨hta.trans hr.1, hr.2.trans_lt hbs⟩ x
    have hmem : ∀ r ∈ Icc a b, MemLp (φ r) 2 (B0579.cellMeasure c (-m)) :=
      fun r hr => hφ.memX r ⟨hta.trans hr.1, (hr.2.trans_lt hbs).le⟩
    have hN : ∀ n : ℕ, cellEnergy c m (k + 1) (cellMoll n (φ r₀)) ≤ Bnd := by
      intro n
      set b₁ := min b (r₀ + 1)
      have hr₀b₁ : r₀ < b₁ := lt_min (hr₀.2.trans_lt hb') (lt_add_one r₀)
      have hb₁b : b₁ ≤ b := min_le_left _ _
      set Δ := b₁ - r₀ with hΔ
      have hΔ0 : 0 < Δ := sub_pos.2 hr₀b₁
      have hΔ1 : Δ ≤ 1 := by
        have : b₁ ≤ r₀ + 1 := min_le_right _ _
        linarith
      have hδΔ : δ ≤ Δ := by
        rcases le_total b (r₀ + 1) with h | h
        · have h1 : b₁ = b := min_eq_left h
          have h2 : δ ≤ b - b' := min_le_left _ _
          linarith [hr₀.2]
        · have h1 : b₁ = r₀ + 1 := min_eq_right h
          have h2 : δ ≤ 1 := min_le_right _ _
          linarith
      have hmaps : MapsTo (fun ζ : ℝ => b₁ - ζ) (Icc 0 Δ) (Icc a b) :=
        fun ζ hζ => ⟨by linarith [hζ.2, hr₀.1], by linarith [hζ.1]⟩
      have hsubIoo : ∀ ζ ∈ Ioo 0 Δ, b₁ - ζ ∈ Ioo a b :=
        fun ζ hζ => ⟨by linarith [hζ.2, hr₀.1], by linarith [hζ.1]⟩
      have hcont : ContinuousOn (fun ζ : ℝ => b₁ - ζ) (Icc 0 Δ) :=
        (continuous_const.sub continuous_id).continuousOn
      obtain ⟨hc0, hd0⟩ := freeMollRateDeriv m hν tr hbuc ht hts hφ hTD hta hbs n k
      obtain ⟨hc1, hd1⟩ := freeMollRateDeriv m hν tr hbuc ht hts hφ hTD hta hbs n (k + 1)
      have hD0 : ∀ ζ ∈ Ioo 0 Δ, ∃ d : ℝ,
          HasDerivAt (fun ζ => cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2) d ζ ∧
          d + β' * cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) ≤
            C * (cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2) := by
        intro ζ hζ
        have hrζ : b₁ - ζ ∈ Ioo a b := hsubIoo ζ hζ
        have hrζs : b₁ - ζ ∈ Icc (0 : ℝ) s :=
          ⟨ht.trans (hta.trans hrζ.1.le), hrζ.2.le.trans hbs.le⟩
        have hrζab : b₁ - ζ ∈ Icc a b := ⟨hrζ.1.le, hrζ.2.le⟩
        have hd := hd0 (b₁ - ζ) hrζ
        have hineq := hSt (tr.v (b₁ - ζ)) (hAv (b₁ - ζ) hrζs) (φ (b₁ - ζ)) (D (b₁ - ζ)) M
          (hDj _ hrζab) (hDM _ hrζab) n k (Nat.le_succ k)
        refine ⟨-energyRate c m k (cellMoll n (φ (b₁ - ζ)))
            (mollRate ν (tr.v (b₁ - ζ)) n (φ (b₁ - ζ)) (fun _ => 0)),
          (HasDerivAt.comp_const_sub b₁ ζ hd).add_const _, ?_⟩
        have h1 : β' * cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) ≤
            β * cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) :=
          mul_le_mul_of_nonneg_right hβ'β (cellEnergy_nonneg _ _ _ _)
        linarith
      have hD1 : ∀ ζ ∈ Ioo 0 Δ, ∃ d : ℝ,
          HasDerivAt (fun ζ => cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ)))) d ζ ∧
          d + β' * cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))) ≤
            C * (cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) +
              (cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2)) := by
        intro ζ hζ
        have hrζ : b₁ - ζ ∈ Ioo a b := hsubIoo ζ hζ
        have hrζs : b₁ - ζ ∈ Icc (0 : ℝ) s :=
          ⟨ht.trans (hta.trans hrζ.1.le), hrζ.2.le.trans hbs.le⟩
        have hrζab : b₁ - ζ ∈ Icc a b := ⟨hrζ.1.le, hrζ.2.le⟩
        have hd := hd1 (b₁ - ζ) hrζ
        have hineq := hSt (tr.v (b₁ - ζ)) (hAv (b₁ - ζ) hrζs) (φ (b₁ - ζ)) (D (b₁ - ζ)) M
          (hDj _ hrζab) (hDM _ hrζab) n (k + 1) le_rfl
        refine ⟨-energyRate c m (k + 1) (cellMoll n (φ (b₁ - ζ)))
            (mollRate ν (tr.v (b₁ - ζ)) n (φ (b₁ - ζ)) (fun _ => 0)),
          HasDerivAt.comp_const_sub b₁ ζ hd, ?_⟩
        have h1 : β' * cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))) ≤
            β * cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))) :=
          mul_le_mul_of_nonneg_right hβ'β (cellEnergy_nonneg _ _ _ _)
        have h2 : C * (cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) + M ^ 2) ≤
            C * (cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) +
              (cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith [cellEnergy_nonneg c m k (cellMoll n (φ (b₁ - ζ)))])
            hC0
        linarith
      have hchain := (hK β' Δ hβ'0 (min_le_right _ _) hΔ0 hΔ1
        (fun ζ => cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2)
        (fun ζ => cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))))
        (fun ζ => cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))))
        ((hc0.comp hcont hmaps).add continuousOn_const)
        ((hc1.comp hcont hmaps).mono Ioc_subset_Icc_self)
        (fun _ _ => add_nonneg (cellEnergy_nonneg _ _ _ _) (sq_nonneg _))
        (fun _ _ => cellEnergy_nonneg _ _ _ _)
        (fun _ _ => cellEnergy_nonneg _ _ _ _) hD0 hD1).2
      have e1 : b₁ - Δ = r₀ := by simp only [hΔ]; ring
      simp only [e1, sub_zero] at hchain
      have hb₁ab : b₁ ∈ Icc a b := ⟨hr₀.1.trans hr₀b₁.le, hb₁b⟩
      have hEk : cellEnergy c m k (cellMoll n (φ b₁)) + M ^ 2 ≤ E0 := by
        have := cellEnergy_jet_le cellMollWeakDeriv hc (hDj b₁ hb₁ab) hCm0 hMp0 hCm (hDMp b₁ hb₁ab) n
        simp only [hE0]
        linarith
      have hinv : (β' * Δ)⁻¹ ≤ (β' * δ)⁻¹ :=
        inv_anti₀ (mul_pos hβ'0 hδ0) (mul_le_mul_of_nonneg_left hδΔ hβ'0.le)
      exact hchain.trans (mul_le_mul (mul_le_mul_of_nonneg_left hinv hK0) hEk
        (add_nonneg (cellEnergy_nonneg _ _ _ _) (sq_nonneg _))
        (mul_nonneg hK0 (inv_nonneg.2 (mul_pos hβ'0 hδ0).le)))
    have hJ := hDj r₀ hr₀ab
    have hjw : ∀ n : ℕ,
        xNorm c (-m) (pdCx j (cellMoll n (D r₀ w))) ≤ ENNReal.ofReal (Real.sqrt Bnd) := by
      intro n
      have e : pdCx j (cellMoll n (D r₀ w)) = adjSpatial (j :: w) (cellMoll n (φ r₀)) := by
        show pdCx j (cellMoll n (D r₀ w)) = pdCx j (adjSpatial w (cellMoll n (φ r₀)))
        rw [adjSpatial_cellMoll_jet cellMollWeakDeriv hc hJ n w hw.le]
      rw [e]
      have hmemw : MemLp (adjSpatial (j :: w) (cellMoll n (φ r₀))) 2 (B0579.cellMeasure c (-m)) :=
        (cellMollSmooth c m n (φ r₀) hc (hper r₀ hr₀ab) (hmem r₀ hr₀ab)).2.2 (j :: w)
      have hsq : (xNorm c (-m) (adjSpatial (j :: w) (cellMoll n (φ r₀)))).toReal ^ 2 ≤ Bnd :=
        (sq_toReal_le_cellEnergy c m _ (by simp [hw])).trans (hN n)
      rw [← ENNReal.ofReal_toReal (xNorm_ne_top hmemw)]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.abs_le_sqrt hsq))
    exact cellWeakDerivOfMollBound c m j (D r₀ w) (Real.sqrt Bnd) hc
      (hJ.periodic w hw.le) (hJ.memX w hw.le) hjw
  refine ⟨max M (2 * Real.sqrt Bnd), fun r hr => ?_⟩
  have hrab : r ∈ Icc a b := ⟨hr.1, hr.2.trans hb'.le⟩
  have hex : ∀ w : List (Fin 2), w.length = k → ∀ j : Fin 2, ∃ G : ℝ × ℝ → ℂ,
      (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) ∧
        MemLp G 2 (B0579.cellMeasure c (-m)) ∧
        HasWeakCellDerivC c j (D r w) G := fun w hw j => by
    obtain ⟨G, h1, h2, h3, -⟩ := hM₁ r hr w hw j
    exact ⟨G, h1, h2, h3⟩
  refine ⟨isCellJet_jetExt (hDj r hrab) hex, fun w hw => ?_⟩
  rcases Nat.lt_or_ge w.length (k + 1) with h | h
  · rw [jetExt_of_le c m k (D r) w (by omega)]
    exact (hDM r hrab w (by omega)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · cases w with
    | nil => simp at h
    | cons j w =>
      have hwk : w.length = k := by simp at hw h; omega
      rw [jetExt_cons_of_length c m k (D r) j hwk]
      obtain ⟨G, -, -, hGd, hGb⟩ := hM₁ r hr w hwk j
      have hspec := cellWeakD_spec (hex w hwk j)
      have hae := weakCellAeUnique c j (D r w) _ _ hspec.2.2 hGd
      have hae' : cellWeakD c m j (D r w) =ᵐ[B0579.cellMeasure c (-m)] G :=
        (B0579.cellMeasure_ac _ _).ae_le hae
      rw [show xNorm c (-m) (cellWeakD c m j (D r w)) = xNorm c (-m) G from eLpNorm_congr_ae hae']
      exact hGb.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- Bootstrap step `C([t, s); H^k_{-m,c}) → C([t, s); H^{k+1}_{-m,c})` for `IsFreeAdjointWeak`. -/
theorem freeHkStepEnd {m ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ)
    (hTD : FreeTestedDeriv tr t s φ) (k : ℕ)
    (hk : AdjHkOn (ν ^ (-2 : ℝ)) m k (Ico t s) φ) :
    AdjHkOn (ν ^ (-2 : ℝ)) m (k + 1) (Ico t s) φ := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨D, hDj, hDc⟩ := hk
  have loc : ∀ r₀ ∈ Ico t s, ∃ a b'' : ℝ, a ≤ r₀ ∧ r₀ < b'' ∧ Icc a b'' ∈ 𝓝[Ico t s] r₀ ∧
      ∃ M₁ M₂ : ℝ, ∀ r ∈ Icc a b'',
        IsCellJet c m (k + 1) (φ r) (jetExt c m k (D r)) ∧
        IsCellJet c m (k + 1 + 1) (φ r) (jetExt c m (k + 1) (jetExt c m k (D r))) ∧
        (∀ w : List (Fin 2), w.length ≤ k + 1 →
          xNorm c (-m) (jetExt c m k (D r) w) ≤ ENNReal.ofReal M₁) ∧
        (∀ w : List (Fin 2), w.length ≤ k + 1 + 1 →
          xNorm c (-m) (jetExt c m (k + 1) (jetExt c m k (D r)) w) ≤ ENNReal.ofReal M₂) := by
    intro r₀ hr₀
    set b := (r₀ + s) / 2
    have hrb : r₀ < b := by simp only [b]; linarith [hr₀.2]
    have hbs : b < s := by simp only [b]; linarith [hr₀.2]
    have hsub : Icc t b ⊆ Ico t s := fun x hx => ⟨hx.1, hx.2.trans_lt hbs⟩
    set b' := (r₀ + b) / 2 with hb'
    set b'' := (r₀ + b') / 2 with hb''
    have hr₀b'' : r₀ < b'' := by simp only [hb'', hb']; linarith
    have hb''b' : b'' < b' := by simp only [hb'', hb']; linarith
    have hb'b : b' < b := by simp only [hb']; linarith
    obtain ⟨M, hM⟩ := compactJetBound c m k (Ico t s) (Icc t b) φ D hDj hDc isCompact_Icc hsub
    obtain ⟨M₁, hM₁⟩ := freeHkGainJet hν hbuc ht hts hφ hTD k le_rfl hbs hb'b
      (fun r hr => hDj r (hsub hr)) hM
    obtain ⟨M₂, hM₂⟩ := freeHkGainJet hν hbuc ht hts hφ hTD (k + 1) le_rfl (hb'b.trans hbs) hb''b'
      (fun r hr => (hM₁ r hr).1) (fun r hr => (hM₁ r hr).2)
    refine ⟨t, b'', hr₀.1, hr₀b'', ?_, M₁, M₂, fun r hr => ?_⟩
    · have h1 : Iio b'' ∈ 𝓝[Ico t s] r₀ := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr₀b'')
      filter_upwards [self_mem_nhdsWithin, h1] with x hx1 hx2
      exact ⟨hx1.1, le_of_lt hx2⟩
    · have hr' : r ∈ Icc t b' := ⟨hr.1, hr.2.trans hb''b'.le⟩
      exact ⟨(hM₁ r hr').1, (hM₂ r hr).1, (hM₁ r hr').2, (hM₂ r hr).2⟩
  refine ⟨fun r => jetExt c m k (D r), fun r hr => ?_, fun w hw r₀ hr₀ => ?_⟩
  · obtain ⟨a, b'', har, hrb, -, M₁, M₂, hL⟩ := loc r hr
    exact (hL r ⟨har, hrb.le⟩).1
  · rcases Nat.lt_or_ge w.length (k + 1) with h | h
    · have e : ∀ r, jetExt c m k (D r) w = D r w := fun r => jetExt_of_le c m k (D r) w (by omega)
      simp only [e]
      exact hDc w (by omega) r₀ hr₀
    · cases w with
      | nil => simp at h
      | cons j w =>
        have hwk : w.length = k := by simp at hw h; omega
        obtain ⟨a, b'', har, hrb, hnhds, M₁, M₂, hL⟩ := loc r₀ hr₀
        have hr₀mem : r₀ ∈ Icc a b'' := ⟨har, hrb.le⟩
        obtain ⟨J1₀, J2₀, B1₀, B2₀⟩ := hL r₀ hr₀mem
        have hBfin : ENNReal.ofReal (2 * |m|) * (2 * ENNReal.ofReal M₁) +
            2 * ENNReal.ofReal M₂ ≠ ⊤ :=
          ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),
            ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
        refine tendsto_of_sq_le_mul hBfin (hDc w (by omega) r₀ hr₀) ?_
        filter_upwards [hnhds] with r hr
        obtain ⟨J1, J2, B1, B2⟩ := hL r hr
        have eD : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ},
            jetExt c m k E w = E w := fun {E} => jetExt_of_le c m k E w (by omega)
        have eD1 : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ},
            jetExt c m (k + 1) (jetExt c m k E) (j :: w) = jetExt c m k E (j :: w) :=
          fun {E} => jetExt_of_le c m (k + 1) (jetExt c m k E) (j :: w) (by simp [hwk])
        have hlw : w.length ≤ k + 1 := by omega
        have hljw : (j :: w).length ≤ k + 1 := by simp [hwk]
        have hljjw : (j :: j :: w).length ≤ k + 1 + 1 := by simp [hwk]
        have hperf : ∀ x : ℝ × ℝ, (D r w - D r₀ w) (x.1 + c, x.2) = (D r w - D r₀ w) x := by
          intro x
          have h1 := J1.periodic w hlw x
          have h2 := J1₀.periodic w hlw x
          rw [eD] at h1 h2
          simp only [Pi.sub_apply, h1, h2]
        have hperg : ∀ x : ℝ × ℝ, (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w))
            (x.1 + c, x.2) = (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w)) x := by
          intro x
          simp only [Pi.sub_apply, J1.periodic (j :: w) hljw x, J1₀.periodic (j :: w) hljw x]
        have hperh : ∀ x : ℝ × ℝ,
            (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
              jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) (x.1 + c, x.2) =
            (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
              jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) x := by
          intro x
          simp only [Pi.sub_apply, J2.periodic (j :: j :: w) hljjw x,
            J2₀.periodic (j :: j :: w) hljjw x]
        have hmf : MemLp (D r w - D r₀ w) 2 (B0579.cellMeasure c (-m)) := by
          have h1 := J1.memX w hlw
          have h2 := J1₀.memX w hlw
          rw [eD] at h1 h2
          exact h1.sub h2
        have hmg1 := J1.memX (j :: w) hljw
        have hmg2 := J1₀.memX (j :: w) hljw
        have hmh1 := J2.memX (j :: j :: w) hljjw
        have hmh2 := J2₀.memX (j :: j :: w) hljjw
        have hdf : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ}, IsCellJet c m (k + 1) (φ r) (jetExt c m k E) →
            HasWeakCellDerivC c j (E w) (jetExt c m k E (j :: w)) := by
          intro E hE
          have := hE.deriv j w (by omega)
          rwa [eD] at this
        have hdf₀ : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ},
            IsCellJet c m (k + 1) (φ r₀) (jetExt c m k E) →
            HasWeakCellDerivC c j (E w) (jetExt c m k E (j :: w)) := by
          intro E hE
          have := hE.deriv j w (by omega)
          rwa [eD] at this
        have hdg : HasWeakCellDerivC c j (jetExt c m k (D r) (j :: w))
            (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w)) := by
          have := J2.deriv j (j :: w) (by simp [hwk])
          rwa [eD1] at this
        have hdg₀ : HasWeakCellDerivC c j (jetExt c m k (D r₀) (j :: w))
            (jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) := by
          have := J2₀.deriv j (j :: w) (by simp [hwk])
          rwa [eD1] at this
        have key := cellInterp c m j (D r w - D r₀ w)
          (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w))
          (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
            jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w))
          hc hperf hperg hperh hmf (hmg1.sub hmg2) (hmh1.sub hmh2)
          (hasWeakCellDerivC_sub (hdf J1) (hdf₀ J1₀)) (hasWeakCellDerivC_sub hdg hdg₀)
        refine key.trans ?_
        have hgb : xNorm c (-m) (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w)) ≤
            2 * ENNReal.ofReal M₁ :=
          (xNorm_sub_le hmg1 hmg2).trans
            (by rw [two_mul]; exact add_le_add (B1 _ hljw) (B1₀ _ hljw))
        have hhb : xNorm c (-m) (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
            jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) ≤ 2 * ENNReal.ofReal M₂ :=
          (xNorm_sub_le hmh1 hmh2).trans
            (by rw [two_mul]; exact add_le_add (B2 _ hljjw) (B2₀ _ hljjw))
        gcongr

/-- **All-order spatial regularity up to the end age**: `φ ∈ C([t, s); H^k_{-m,c})` for every `k`. -/
theorem freeHkAllOrders {m ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ)
    (hTD : FreeTestedDeriv tr t s φ) (k : ℕ) :
    AdjHkOn (ν ^ (-2 : ℝ)) m k (Ico t s) φ := by
  induction k with
  | zero => exact adjHkOn_zero_Ico_of_freeWeak hφ
  | succ k ih => exact freeHkStepEnd hν tr hbuc ht hts hφ hTD k ih

end UnforcedLeray.Short.IIIa.ComplFreeRateSub
