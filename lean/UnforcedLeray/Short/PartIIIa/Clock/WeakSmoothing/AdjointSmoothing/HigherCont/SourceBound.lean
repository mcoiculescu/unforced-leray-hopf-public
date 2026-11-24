import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_4
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Comm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StAdjComm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Static.StVelWords
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutE1DerivUnder
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.LadDtRegular

/-!
# `PartIII-a:T21/2/7/2/4/2`: effective source bound for `ψ = ∂^w φ`

Source of record: `the November 2 reference manuscript`
(SP), lines 3067-3071.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace SourceBoundAux

lemma ladDt_adjSpatial {t s ρ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hρ : ρ ∈ Ioo t s) :
    ∀ w : List (Fin 2), ladDt (fun r => adjSpatial w (φ r)) ρ = adjSpatial w (ladDt φ ρ)
  | [] => rfl
  | j :: w => by
    funext x
    have hd := CutE1DU.hasDerivAt_pdCx_r (ψ := fun r => adjSpatial w (φ r))
      (HigherContAux.jointSmooth_adjSpatial hj w) hρ j x
    have heq := ladDt_eq_of_hasDerivAt hd
    show ladDt (fun r => pdCx j (adjSpatial w (φ r))) ρ x = pdCx j (adjSpatial w (ladDt φ ρ)) x
    rw [heq, ladDt_adjSpatial hj hρ w]

lemma ladLapCx_eq_stLap (G : ℝ × ℝ → ℂ) : ladLapCx G = stLap G := rfl

lemma ladTransport_eq_stGrad {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ)
    (G : ℝ × ℝ → ℂ) : ladTransport tr ρ G = stGrad (stVel (tr.v ρ)) G := by
  funext x
  simp [ladTransport, stGrad, stVel, Fin.sum_univ_two]

lemma contDiff_coefWord_tr {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (u : List (Fin 2)) (l : Fin 2) :
    ContDiff ℝ ∞ (stCoefWord u (stVel (tr.v ρ)) l) := by
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
  have hvl : ContDiff ℝ ∞ (stVel (tr.v ρ) l) :=
    (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  change ContDiff ℝ ∞ (pdWordR u (stVel (tr.v ρ) l))
  induction u with
  | nil => exact hvl
  | cons j u ih => exact st_pd_contDiff ih j

lemma abs_coefWord_tr_le {ν c m b : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {CJ : ℝ}
    (hCJ : ∀ j : ℕ, j ≤ 6 → ∀ ρ ∈ Icc (0 : ℝ) b, ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) ^ (⌈max 0 ((m + 2) / 2)⌉₊) * ‖iteratedFDeriv ℝ j (tr.v ρ) x‖ ≤ CJ)
    {ρ : ℝ} (hρb : ρ ∈ Icc (0 : ℝ) b) {u : List (Fin 2)} (hu : u.length ≤ 2)
    (l : Fin 2) (x : ℝ × ℝ) :
    |stCoefWord u (stVel (tr.v ρ)) l x| ≤ |CJ| := by
  have hρ0 : 0 ≤ ρ := hρb.1
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
  have hvl : ContDiff ℝ ∞ (stVel (tr.v ρ) l) :=
    (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have h1 : |pdWordR u (stVel (tr.v ρ) l) x| ≤ ‖iteratedFDeriv ℝ u.length (stVel (tr.v ρ) l) x‖ :=
    sv_abs_pdWordR_le hvl u x
  have hproj : ‖iteratedFDeriv ℝ u.length (stVel (tr.v ρ) l) x‖ ≤
      ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ := by
    let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj l
    have hL : ‖L‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
      rw [one_mul]
      exact PiLp.norm_apply_le y l
    have hn : ContDiffAt ℝ ∞ (tr.v ρ) x := hv.contDiffAt
    have hle : (u.length : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
    have h := L.norm_iteratedFDeriv_comp_left hn hle
    calc ‖iteratedFDeriv ℝ u.length (stVel (tr.v ρ) l) x‖
        = ‖iteratedFDeriv ℝ u.length (L ∘ tr.v ρ) x‖ := rfl
      _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ := h
      _ ≤ 1 * ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ :=
          mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ := one_mul _
  set kw : ℕ := ⌈max 0 ((m + 2) / 2)⌉₊
  have hw1 : 1 ≤ (1 + x.2 ^ 2) ^ kw := one_le_pow₀ (by nlinarith [sq_nonneg x.2])
  have hu6 : u.length ≤ 6 := by omega
  have hbd := (hCJ u.length hu6 ρ hρb x).trans (le_abs_self CJ)
  calc |stCoefWord u (stVel (tr.v ρ)) l x|
      ≤ ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ := h1.trans hproj
    _ = 1 * ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ := (one_mul _).symm
    _ ≤ (1 + x.2 ^ 2) ^ kw * ‖iteratedFDeriv ℝ u.length (tr.v ρ) x‖ :=
        mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
    _ ≤ |CJ| := hbd

lemma ladChi_adjSpatial_eq {ν c t s ρ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hρ : ρ ∈ Ioo t s) (w : List (Fin 2)) (x : ℝ × ℝ) :
    ladChi tr (fun r => adjSpatial w (φ r)) ρ x =
      adjSpatial w (ladChi tr φ ρ) x - HigherContAux.adjTransComm tr ρ w (φ ρ) x := by
  have hρIco : ρ ∈ Ico t s := Ioo_subset_Ico_self hρ
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  have hslice : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj hρIco
  have hdt : ContDiff ℝ ∞ (ladDt φ ρ) := LadDtReg.contDiff_ladDt_of hj hρ
  have hlap : ContDiff ℝ ∞ (ladLapCx (φ ρ)) := st_contDiff_stLap hslice
  have htr : ContDiff ℝ ∞ (ladTransport tr ρ (φ ρ)) := by
    rw [ladTransport_eq_stGrad]
    exact st_contDiff_stGrad' (contDiff_coefWord_tr tr hρ0 []) hslice
  have hchi_eq : ladChi tr φ ρ = fun y =>
      (ladDt φ ρ y + (ν : ℂ) * ladLapCx (φ ρ) y) + ladTransport tr ρ (φ ρ) y := rfl
  have hνlap : ContDiff ℝ ∞ (fun y => (ν : ℂ) * ladLapCx (φ ρ) y) :=
    (contDiff_const (c := (ν : ℂ))).mul hlap
  have h1 := congrFun (st_adjSpatial_add (hdt.add hνlap) htr w) x
  have h2 := congrFun (st_adjSpatial_add hdt hνlap w) x
  have h3 := congrFun (st_adjSpatial_const_mul (ν : ℂ) hlap w) x
  have h4 := congrFun (ladDt_adjSpatial hj hρ w) x
  have h5 := congrFun (st_adjSpatial_stLap stAdjComm hslice w) x
  change ladDt (fun r => adjSpatial w (φ r)) ρ x +
      (ν : ℂ) * ladLapCx (adjSpatial w (φ ρ)) x +
      ladTransport tr ρ (adjSpatial w (φ ρ)) x =
    adjSpatial w (ladChi tr φ ρ) x -
      (adjSpatial w (ladTransport tr ρ (φ ρ)) x - ladTransport tr ρ (adjSpatial w (φ ρ)) x)
  rw [hchi_eq, h1, h2, h3, ← h4]
  change _ = _ + (ν : ℂ) * adjSpatial w (stLap (φ ρ)) x + _ - _
  rw [h5]
  change _ = _ + (ν : ℂ) * ladLapCx (adjSpatial w (φ ρ)) x + _ - _
  ring

end SourceBoundAux

open SourceBoundAux in
/-- **(i-a) Effective source bound for `ψ = ∂^w φ`**
(`PartIII-a:T21/2/7/2/4/2`, SP lines 3067-3071). -/
theorem adjHigherSourceBound (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjHigherSourceBound m := by
  have _ := hm
  intro ν _hν _hν1 tr _hb hJ t s ht _hts φ hj _hper k hk hcont b hbI Mχ hMχ w hw
  let c : ℝ := ν ^ (-2 : ℝ)
  have hb0 : 0 ≤ b := ht.trans hbI.1.le
  obtain ⟨CJ, hCJ⟩ := hJ b hb0
  have hex_u : ∀ u : List (Fin 2), ∃ Mu : ℝ, 0 ≤ Mu ∧ ∀ ρ ∈ Ioo t b,
      u.length ≤ k → xNorm c (-m) (adjSpatial u (φ ρ)) ≤ ENNReal.ofReal Mu := by
    intro u
    by_cases hu : u.length ≤ k
    · obtain ⟨M₀, hM₀⟩ := HigherContAux.exists_xNorm_bdd_on_Ioo hbI
        (fun r hr => (hcont r hr u hu).1) (fun r hr => (hcont r hr u hu).2)
      refine ⟨max M₀ 0, le_max_right _ _, fun ρ hρ _ => ?_⟩
      exact (hM₀ ρ hρ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact ⟨0, le_rfl, fun _ _ h => absurd h hu⟩
  choose Mu hMu0 hMu using hex_u
  set Mφ : ℝ := ∑ u ∈ wordsLE w.length, Mu u
  have hMφ0 : 0 ≤ Mφ := Finset.sum_nonneg fun u _ => hMu0 u
  set Mcomm : ℝ := 2 ^ k * (2 * |CJ|) * Mφ
  have hMcomm0 : 0 ≤ Mcomm := by positivity
  refine ⟨max Mχ 0 + Mcomm, fun ρ hρ => ?_⟩
  have hρs : ρ ∈ Ioo t s := ⟨hρ.1, hρ.2.trans hbI.2⟩
  have hρIco : ρ ∈ Ico t s := Ioo_subset_Ico_self hρs
  have hρb : ρ ∈ Icc (0 : ℝ) b := ⟨ht.trans hρ.1.le, hρ.2.le⟩
  have hρ0 : 0 ≤ ρ := hρb.1
  have hslice : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj hρIco
  have hcs : ∀ (u : List (Fin 2)) (l : Fin 2), ContDiff ℝ ∞ (stCoefWord u (stVel (tr.v ρ)) l) :=
    fun u l => contDiff_coefWord_tr tr hρ0 u l
  have hexp : adjSpatial w (stGrad (stVel (tr.v ρ)) (φ ρ)) = fun x =>
      ((stSplits w).map fun p =>
        stGrad (stCoefWord p.1 (stVel (tr.v ρ))) (adjSpatial p.2 (φ ρ)) x).sum :=
    st_word_leibniz stGrad (stVel (tr.v ρ)) (fun u => adjSpatial u (φ ρ)) w.length
      (fun u u' _ => st_contDiff_stGrad' (hcs u) (st_contDiff_adjSpatial hslice u'))
      (fun j u u' _ => st_pdCx_stGrad stAdjComm (hcs u) (st_contDiff_adjSpatial hslice u') j)
      w le_rfl
  obtain ⟨T, hT, hT1⟩ := st_splits_cons_head w
  have hc0 : stCoefWord [] (stVel (tr.v ρ)) = stVel (tr.v ρ) := rfl
  have hcomm_eq : HigherContAux.adjTransComm tr ρ w (φ ρ) = fun x =>
      (T.map fun p =>
        stGrad (stCoefWord p.1 (stVel (tr.v ρ))) (adjSpatial p.2 (φ ρ)) x).sum := by
    funext x
    unfold HigherContAux.adjTransComm
    rw [ladTransport_eq_stGrad, ladTransport_eq_stGrad, hexp]
    simp only [hT, List.map_cons, List.sum_cons, hc0]
    ring
  have hterm : ∀ p ∈ T,
      MemLp (stGrad (stCoefWord p.1 (stVel (tr.v ρ))) (adjSpatial p.2 (φ ρ))) 2
        (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (stGrad (stCoefWord p.1 (stVel (tr.v ρ))) (adjSpatial p.2 (φ ρ)))).toReal ≤
        |CJ| * (2 * Mφ) := by
    intro p hp
    have hpS : p ∈ stSplits w := by rw [hT]; exact List.mem_cons_of_mem _ hp
    have hlen := st_splits_length p hpS
    have hp1 := hT1 p hp
    have hp1_le : p.1.length ≤ 2 := by omega
    have hAp : ∀ (l : Fin 2) (x : ℝ × ℝ),
        |stCoefWord p.1 (stVel (tr.v ρ)) l x| ≤ |CJ| :=
      fun l x => abs_coefWord_tr_le tr hCJ hρb hp1_le l x
    have hGm : ∀ l : Fin 2, MemLp (pdCx l (adjSpatial p.2 (φ ρ))) 2 (B0579.cellMeasure c (-m)) :=
      fun l => (hcont ρ hρIco (l :: p.2) (by simp; omega)).1
    obtain ⟨hm, hb⟩ := st_stGrad_bound (abs_nonneg CJ) (fun l => (hcs p.1 l).continuous) hAp
      (H := adjSpatial p.2 (φ ρ)) hGm
    refine ⟨hm, hb.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg CJ))⟩
    have hle : ∀ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: p.2) (φ ρ))).toReal ≤ Mφ := by
      intro l
      have hlw : (l :: p.2).length ≤ w.length := by simp; omega
      have hlk : (l :: p.2).length ≤ k := hlw.trans hw
      have hmem : (l :: p.2) ∈ wordsLE w.length := mem_wordsLE.2 hlw
      have h1 : (xNorm c (-m) (adjSpatial (l :: p.2) (φ ρ))).toReal ≤ Mu (l :: p.2) := by
        rw [← ENNReal.toReal_ofReal (hMu0 (l :: p.2))]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMu (l :: p.2) ρ hρ hlk)
      exact h1.trans (Finset.single_le_sum (f := Mu) (fun u _ => hMu0 u) hmem)
    have h0 := hle 0
    have h1 := hle 1
    rw [Fin.sum_univ_two]
    show (xNorm c (-m) (adjSpatial (0 :: p.2) (φ ρ))).toReal +
        (xNorm c (-m) (adjSpatial (1 :: p.2) (φ ρ))).toReal ≤ 2 * Mφ
    linarith
  obtain ⟨hm_sum, hb_sum⟩ := st_list_sum_memLp_le T
    (fun p => stGrad (stCoefWord p.1 (stVel (tr.v ρ))) (adjSpatial p.2 (φ ρ)))
    (fun _ => |CJ| * (2 * Mφ)) hterm
  have hcomm_mem : MemLp (HigherContAux.adjTransComm tr ρ w (φ ρ)) 2
      (B0579.cellMeasure c (-m)) := by
    rwa [hcomm_eq]
  have hcomm_bd : eLpNorm (HigherContAux.adjTransComm tr ρ w (φ ρ)) 2
      (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal Mcomm := by
    have hTlen : T.length + 1 = 2 ^ w.length := by
      have := st_splits_card w
      rw [hT, List.length_cons] at this
      exact this
    have hTk : (T.length : ℝ) ≤ 2 ^ k := by
      have h1 : T.length ≤ 2 ^ w.length := by omega
      have h2 : 2 ^ w.length ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hw
      exact_mod_cast h1.trans h2
    have htoReal : (xNorm c (-m) (HigherContAux.adjTransComm tr ρ w (φ ρ))).toReal ≤ Mcomm := by
      rw [hcomm_eq]
      refine hb_sum.trans ?_
      rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      calc (T.length : ℝ) * (|CJ| * (2 * Mφ))
          ≤ 2 ^ k * (|CJ| * (2 * Mφ)) :=
            mul_le_mul_of_nonneg_right hTk (mul_nonneg (abs_nonneg _) (mul_nonneg zero_le_two hMφ0))
        _ = Mcomm := by unfold Mcomm; ring
    have hne : xNorm c (-m) (HigherContAux.adjTransComm tr ρ w (φ ρ)) ≠ ⊤ :=
      hcomm_mem.eLpNorm_lt_top.ne
    change xNorm c (-m) (HigherContAux.adjTransComm tr ρ w (φ ρ)) ≤ ENNReal.ofReal Mcomm
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal htoReal
  obtain ⟨hm_chi, hb_chi⟩ := hMχ ρ hρ w hw
  have hchi_eq : ladChi tr (fun r => adjSpatial w (φ r)) ρ =
      adjSpatial w (ladChi tr φ ρ) - HigherContAux.adjTransComm tr ρ w (φ ρ) :=
    funext fun x => ladChi_adjSpatial_eq tr ht hj hρs w x
  rw [hchi_eq]
  refine ⟨hm_chi.sub hcomm_mem, ?_⟩
  calc eLpNorm (adjSpatial w (ladChi tr φ ρ) - HigherContAux.adjTransComm tr ρ w (φ ρ)) 2
        (B0579.cellMeasure c (-m))
      ≤ eLpNorm (adjSpatial w (ladChi tr φ ρ)) 2 (B0579.cellMeasure c (-m)) +
          eLpNorm (HigherContAux.adjTransComm tr ρ w (φ ρ)) 2 (B0579.cellMeasure c (-m)) :=
        eLpNorm_sub_le hm_chi.1 hcomm_mem.1 (by norm_num)
    _ ≤ ENNReal.ofReal (max Mχ 0) + ENNReal.ofReal Mcomm :=
        add_le_add (hb_chi.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) hcomm_bd
    _ = ENNReal.ofReal (max Mχ 0 + Mcomm) :=
        (ENNReal.ofReal_add (le_max_right _ _) hMcomm0).symm

end UnforcedLeray.Short.IIIa
