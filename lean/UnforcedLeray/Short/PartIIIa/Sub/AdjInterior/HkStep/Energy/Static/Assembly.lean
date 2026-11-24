import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: `StaticMollEnergy` from its leaves

Source of record: `the November 2 reference manuscript` lines 3060-3071 (the
differentiated weighted energy: the diffusion gives `-2ν‖∇∂^wG‖²` up to the diffusion-weight error
`C_m`, the transport and compact terms have coefficient `C_b`; then `β = ν`), 3044-3050.

For a word `w`, `|w| ≤ j ≤ k + 1`, `F = ∂^w G`, `G = ρ_n ⋆ φ`:
`-2 Re⟨F, ∂^w mollRate⟩ = 2ν Re⟨F, ΔF⟩ + 2 Re⟨F, ∂^w T⟩ - 2 Re⟨F, ρ_n ⋆ Dχ w⟩`
(`mollRate_eq_st`, linearity of `adjSpatial` and `ipX`, `st_adjSpatial_stLap`); the diffusion term by
`StCellIbp`, the transport term by `StTransWord`, the compact term by Cauchy-Schwarz and
`CellMollBound`; Young's inequality (`st_word_young`) leaves `-ν Σ_l ‖∂_l F‖² + K (N_j + M²)`, and
the sum over the words is `-ν (N_{j+1} - N_0) + |W_j| K (N_j + M²)` (`st_sum_wordsLE_succ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The real arithmetic of one word (Young's inequality three times). -/
theorem st_word_young {ν a CT Cm b M t e d0 d1 I0 I1 IT IX Nw Nj : ℝ}
    (hν : 0 < ν) (hCT : CT = ν * t) (hCT0 : 0 ≤ CT) (hCm0 : 0 ≤ Cm) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hM : 0 ≤ M)
    (h0 : I0 ≤ -d0 ^ 2 + 2 * a * e * d0) (h1 : I1 ≤ -d1 ^ 2 + 2 * a * e * d1)
    (hT : 2 * IT ≤ CT * (Nw + M ^ 2) + CT * M * (d0 + d1))
    (hX : -IX ≤ e * (Cm * (b * M)))
    (heN : e ^ 2 ≤ Nj) (hwN : Nw ≤ Nj) :
    2 * ν * (I0 + I1) + 2 * IT - 2 * IX ≤
      -ν * (d0 ^ 2 + d1 ^ 2) +
        (16 * ν * a ^ 2 + 1 + CT + ν * t ^ 2 + Cm ^ 2 * b ^ 2) * (Nj + M ^ 2) := by
  have y0 : 4 * ν * a * e * d0 ≤ ν / 2 * d0 ^ 2 + 8 * ν * a ^ 2 * e ^ 2 := by
    nlinarith [mul_nonneg hν.le (sq_nonneg (d0 - 4 * a * e))]
  have y1 : 4 * ν * a * e * d1 ≤ ν / 2 * d1 ^ 2 + 8 * ν * a ^ 2 * e ^ 2 := by
    nlinarith [mul_nonneg hν.le (sq_nonneg (d1 - 4 * a * e))]
  have z0 : CT * M * d0 ≤ ν / 2 * d0 ^ 2 + ν * t ^ 2 / 2 * M ^ 2 := by
    rw [hCT]; nlinarith [mul_nonneg hν.le (sq_nonneg (d0 - t * M))]
  have z1 : CT * M * d1 ≤ ν / 2 * d1 ^ 2 + ν * t ^ 2 / 2 * M ^ 2 := by
    rw [hCT]; nlinarith [mul_nonneg hν.le (sq_nonneg (d1 - t * M))]
  have x0 : 2 * e * (Cm * (b * M)) ≤ e ^ 2 + Cm ^ 2 * b ^ 2 * M ^ 2 := by
    nlinarith [sq_nonneg (e - Cm * (b * M))]
  have hNj0 : 0 ≤ Nj := (sq_nonneg e).trans heN
  have hc1 : 0 ≤ 16 * ν * a ^ 2 + 1 := by positivity
  have hc2 : 0 ≤ ν * t ^ 2 + Cm ^ 2 * b ^ 2 := by positivity
  have k1 : (16 * ν * a ^ 2 + 1) * e ^ 2 ≤ (16 * ν * a ^ 2 + 1) * Nj :=
    mul_le_mul_of_nonneg_left heN hc1
  have k2 : CT * Nw ≤ CT * Nj := mul_le_mul_of_nonneg_left hwN hCT0
  have k3 : 0 ≤ (ν * t ^ 2 + Cm ^ 2 * b ^ 2) * Nj := mul_nonneg hc2 hNj0
  have k4 : 0 ≤ (16 * ν * a ^ 2 + 1) * M ^ 2 := mul_nonneg hc1 (sq_nonneg M)
  have hA : 2 * ν * (I0 + I1) ≤ 2 * ν * (-d0 ^ 2 + 2 * a * e * d0 + (-d1 ^ 2 + 2 * a * e * d1)) :=
    mul_le_mul_of_nonneg_left (add_le_add h0 h1) (by positivity)
  nlinarith

/-- **`StaticMollEnergy` from its leaves** (SP 3060-3071). -/
theorem staticMollEnergy_of (m : ℝ) (hS : CellMollSmooth) (hB : CellMollBound)
    (hW : CellMollWeakDeriv) (hCD : CellConvDeriv) (hComm : StAdjComm) (hIbp : StCellIbp)
    (hT : StTransWord) : StaticMollEnergy m := by
  intro ν hν hν1 k Av Cχ
  set c : ℝ := ν ^ (-2 : ℝ) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨Cm, hCm0, hCm⟩ := hB c m hc
  obtain ⟨CT, hCT0, hCT⟩ := hT c m k Av hc
  set t : ℝ := CT / ν with ht
  have hCTt : CT = ν * t := by rw [ht]; field_simp
  set K₁ : ℝ := 16 * ν * |m| ^ 2 + 1 + CT + ν * t ^ 2 + Cm ^ 2 * |Cχ| ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have h1 : 0 ≤ 16 * ν * |m| ^ 2 + 1 := by positivity
    have h2 : 0 ≤ ν * t ^ 2 + Cm ^ 2 * |Cχ| ^ 2 := by positivity
    rw [hK₁]
    linarith
  refine ⟨ν + ((wordsLE (k + 1)).card : ℝ) * K₁, ν, ?_, hν, ?_⟩
  · have : 0 ≤ ((wordsLE (k + 1)).card : ℝ) * K₁ := mul_nonneg (Nat.cast_nonneg _) hK₁0
    linarith
  intro v hv φ χ D Dχ M hJ hDM hJχ hDχ n j hj
  have hφp := st_jet_periodic hJ
  have hφm := st_jet_memX hJ
  have hχp := st_jet_periodic hJχ
  have hχm := st_jet_memX hJχ
  obtain ⟨hGs, hGp, hGm⟩ := hS c m n φ hc hφp hφm
  obtain ⟨hXs, -, hXm⟩ := hS c m n χ hc hχp hχm
  obtain ⟨hTs, -, hTm⟩ := st_trans_reg hS hCD hc hv hφp hφm n
  have hM' : ∀ w : List (Fin 2), w.length ≤ k → xNorm c (-m) (D w) ≤ ENNReal.ofReal |M| :=
    fun w hw => (hDM w hw).trans (ENNReal.ofReal_le_ofReal (le_abs_self M))
  have hTW : ∀ w : List (Fin 2), w.length ≤ k + 1 →
      2 * ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)) ≤
        CT * (cellEnergy c m w.length (cellMoll n φ) + |M| ^ 2) +
          CT * |M| * ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal :=
    hCT v hv φ D |M| (abs_nonneg M) hJ hM' n
  -- the bound for one word
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
    -- the splitting of the rate
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
      rw [st_adjSpatial_stLap hComm hGs w]
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
    -- the diffusion
    have hIL : ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stLap (cellMoll n φ))) =
        ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (0 :: 0 :: w) (cellMoll n φ)) +
          ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (1 :: 1 :: w) (cellMoll n φ)) := by
      rw [st_adjSpatial_stLap hComm hGs w]
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
        hIbp c m l (adjSpatial w (cellMoll n φ)) (adjSpatial (l :: w) (cellMoll n φ)) hc hFs
          (st_contDiff_adjSpatial hGs (l :: w)) hFp (st_adjSpatial_periodic hGp (l :: w)) hFm hH
          hH (hGm (l :: l :: w))
      have hself := st_ipX_self hH
      have h2 := (abs_le.mp h).2
      linarith
    -- the compact term
    have hXnorm : (xNorm c (-m) (adjSpatial w (cellMoll n χ))).toReal ≤ Cm * (|Cχ| * |M|) := by
      rw [st_adjSpatial_cellMoll_jet hW hc hJχ n w hwk]
      have h1 := hCm n (Dχ w) (hJχ.periodic w hwk) (hJχ.memX w hwk)
      have h2 : xNorm c (-m) (Dχ w) ≤ ENNReal.ofReal (|Cχ| * |M|) :=
        (hDχ w hwk).trans (ENNReal.ofReal_le_ofReal (by rw [← abs_mul]; exact le_abs_self _))
      have h3 : xNorm c (-m) (cellMoll n (Dχ w)) ≤ ENNReal.ofReal (Cm * (|Cχ| * |M|)) := by
        calc xNorm c (-m) (cellMoll n (Dχ w))
            ≤ ENNReal.ofReal Cm * xNorm c (-m) (Dχ w) := h1
          _ ≤ ENNReal.ofReal Cm * ENNReal.ofReal (|Cχ| * |M|) := by gcongr
          _ = ENNReal.ofReal (Cm * (|Cχ| * |M|)) := (ENNReal.ofReal_mul hCm0).symm
      exact ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg hCm0 (mul_nonneg (abs_nonneg _) (abs_nonneg _))) h3
    have hX : -ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ)) ≤
        (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal * (Cm * (|Cχ| * |M|)) := by
      have h1 := st_abs_ipX_le hFm hXw
      have h2 := mul_le_mul_of_nonneg_left hXnorm
        (ENNReal.toReal_nonneg (a := xNorm c (-m) (adjSpatial w (cellMoll n φ))))
      have h3 := neg_abs_le (ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ)))
      linarith
    -- Young's inequality
    have hY := st_word_young (ν := ν) (a := |m|) (CT := CT) (Cm := Cm) (b := |Cχ|) (M := |M|)
      (t := t) (e := (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal)
      (d0 := (xNorm c (-m) (adjSpatial (0 :: w) (cellMoll n φ))).toReal)
      (d1 := (xNorm c (-m) (adjSpatial (1 :: w) (cellMoll n φ))).toReal)
      (I0 := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (0 :: 0 :: w) (cellMoll n φ)))
      (I1 := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial (1 :: 1 :: w) (cellMoll n φ)))
      (IT := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)))
      (IX := ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (cellMoll n χ)))
      (Nw := cellEnergy c m w.length (cellMoll n φ)) (Nj := cellEnergy c m j (cellMoll n φ))
      hν hCTt hCT0 hCm0 (abs_nonneg m) (abs_nonneg Cχ) ENNReal.toReal_nonneg (abs_nonneg M)
      (hdiff 0) (hdiff 1) (by simpa [Fin.sum_univ_two] using hTW w hwk) hX
      (sq_toReal_le_cellEnergy c m (cellMoll n φ) hwj) (st_cellEnergy_mono c m hwj _)
    rw [hipx, hIL]
    simp only [Fin.sum_univ_two]
    rw [sq_abs M] at hY
    linarith
  -- the sum over the words
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

end UnforcedLeray.Short.IIIa
