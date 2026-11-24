import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: the transport term word by word (`StTransWord`)

Source of record: `the November 2 reference manuscript` lines 3060-3071
("Reynolds cancellation"; the transport terms have coefficient `C_b`).

For `G = ρ_n ⋆ φ`, `F = ∂^wG`, `|w| ≤ k + 1`: `T = v·∇G + R` (`R = stFriedRem v n φ`), so
`Re⟨F, ∂^w T⟩ = Re⟨F, ∂^w(v·∇G) - v·∇F⟩ + Re⟨F, v·∇F⟩ + Re⟨F, ∂^w R⟩`; the first term by
`StTransComm` (order `|w|`), the second by `StReynolds`, the third by `StFriedJet` for `|w| ≤ k`
and, for `w = l :: u` with `|u| = k`, by `StCellIbp` moving `∂_l` onto `F`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem st_contDiff_stGrad {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (stGrad (stVel v) H) := by
  have h : ∀ l : Fin 2, ContDiff ℝ ∞ (fun x => ((stVel v l x : ℝ) : ℂ) * pdCx l H x) :=
    fun l => (Complex.ofRealCLM.contDiff.comp (st_vel_contDiff hv l)).mul (st_contDiff_pdCx hH l)
  unfold stGrad
  simp only [Fin.sum_univ_two]
  exact (h 0).add (h 1)

theorem st_stGrad_periodic {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) {H : ℝ × ℝ → ℂ} (hH : ∀ x : ℝ × ℝ, H (x.1 + c, x.2) = H x)
    (x : ℝ × ℝ) : stGrad (stVel v) H (x.1 + c, x.2) = stGrad (stVel v) H x := by
  unfold stGrad
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [st_vel_periodic hv l x, st_pdCx_periodic hH l x]

theorem st_stGrad_memLp {c m : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) {H : ℝ × ℝ → ℂ}
    (hH : ∀ l : Fin 2, MemLp (pdCx l H) 2 (B0579.cellMeasure c (-m))) :
    MemLp (stGrad (stVel v) H) 2 (B0579.cellMeasure c (-m)) := by
  have h : ∀ l : Fin 2, MemLp (fun x => ((stVel v l x : ℝ) : ℂ) * pdCx l H x) 2
      (B0579.cellMeasure c (-m)) := fun l => st_velMul_memLp hv (hH l) l
  unfold stGrad
  simp only [Fin.sum_univ_two]
  exact (h 0).add (h 1)

/-- `e Σ_{u ∈ W_i} e_u ≤ |W_i| N_i` for `|w| = i`. -/
theorem st_mul_sum_le (c m : ℝ) (G : ℝ × ℝ → ℂ) (w : List (Fin 2)) :
    (xNorm c (-m) (adjSpatial w G)).toReal *
        ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal ≤
      ((wordsLE w.length).card : ℝ) * cellEnergy c m w.length G := by
  rw [Finset.mul_sum]
  have h : ∀ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial w G)).toReal *
      (xNorm c (-m) (adjSpatial u G)).toReal ≤ cellEnergy c m w.length G := by
    intro u hu
    have h1 := sq_toReal_le_cellEnergy c m G (le_refl w.length) (w := w)
    have h2 := sq_toReal_le_cellEnergy c m G (mem_wordsLE.1 hu)
    nlinarith [sq_nonneg ((xNorm c (-m) (adjSpatial w G)).toReal -
      (xNorm c (-m) (adjSpatial u G)).toReal)]
  calc ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial w G)).toReal *
        (xNorm c (-m) (adjSpatial u G)).toReal
      ≤ ∑ _u ∈ wordsLE w.length, cellEnergy c m w.length G := Finset.sum_le_sum h
    _ = ((wordsLE w.length).card : ℝ) * cellEnergy c m w.length G := by
        rw [Finset.sum_const, nsmul_eq_mul]


/-! ## Real arithmetic -/

theorem st_ar_comm {IC e X CC T0 Wl W N : ℝ} (h1 : |IC| ≤ e * X) (hX : X ≤ CC * T0)
    (h3 : e * T0 ≤ Wl * N) (h4 : Wl ≤ W) (he : 0 ≤ e) (hCC : 0 ≤ CC) (hN : 0 ≤ N) :
    2 * IC ≤ 2 * CC * W * N := by
  have a1 : IC ≤ e * X := (abs_le.mp h1).2
  have a2 : e * X ≤ e * (CC * T0) := mul_le_mul_of_nonneg_left hX he
  have a3 : e * (CC * T0) = CC * (e * T0) := by ring
  have a4 : CC * (e * T0) ≤ CC * (Wl * N) := mul_le_mul_of_nonneg_left h3 hCC
  have a5 : Wl * N ≤ W * N := mul_le_mul_of_nonneg_right h4 hN
  have a6 : CC * (Wl * N) ≤ CC * (W * N) := mul_le_mul_of_nonneg_left a5 hCC
  have a7 : CC * (W * N) = CC * W * N := by ring
  linarith

theorem st_ar_frA {IR e R CF M N S a : ℝ} (h1 : |IR| ≤ e * R) (hR : R ≤ CF * M) (he : 0 ≤ e)
    (he2 : e ^ 2 ≤ N) (hCF : 0 ≤ CF) (hM : 0 ≤ M) (hS : 0 ≤ S) (ha : 0 ≤ a) :
    2 * IR ≤ (1 + 2 * a * CF) * N + (CF ^ 2 + 2 * a * CF) * M ^ 2 + 2 * CF * M * S := by
  have a1 : IR ≤ e * R := (abs_le.mp h1).2
  have a2 : e * R ≤ e * (CF * M) := mul_le_mul_of_nonneg_left hR he
  have a3 : 2 * (e * (CF * M)) ≤ e ^ 2 + CF ^ 2 * M ^ 2 := by
    nlinarith [sq_nonneg (e - CF * M)]
  have hN : 0 ≤ N := (sq_nonneg e).trans he2
  have a4 : 0 ≤ 2 * a * CF * N := by positivity
  have a5 : 0 ≤ 2 * a * CF * M ^ 2 := by positivity
  have a6 : 0 ≤ 2 * CF * M * S := by positivity
  nlinarith

theorem st_ar_frB {I J e d R CF M N S a : ℝ} (h3 : I + J ≤ 2 * a * e * R) (h4 : -(d * R) ≤ J)
    (hd : d ≤ S) (hR0 : 0 ≤ R) (hR : R ≤ CF * M) (he : 0 ≤ e) (he2 : e ^ 2 ≤ N) (hCF : 0 ≤ CF)
    (hM : 0 ≤ M) (hS : 0 ≤ S) (ha : 0 ≤ a) :
    2 * I ≤ (1 + 2 * a * CF) * N + (CF ^ 2 + 2 * a * CF) * M ^ 2 + 2 * CF * M * S := by
  have a1 : d * R ≤ S * R := mul_le_mul_of_nonneg_right hd hR0
  have a2 : I ≤ (2 * a * e + S) * R := by nlinarith
  have a3 : (2 * a * e + S) * R ≤ (2 * a * e + S) * (CF * M) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have a4 : 2 * e * M ≤ e ^ 2 + M ^ 2 := by nlinarith [sq_nonneg (e - M)]
  have a5 : 2 * a * CF * (2 * e * M) ≤ 2 * a * CF * (e ^ 2 + M ^ 2) :=
    mul_le_mul_of_nonneg_left a4 (by positivity)
  have hN : 0 ≤ N := (sq_nonneg e).trans he2
  have a6 : 2 * a * CF * e ^ 2 ≤ 2 * a * CF * N := mul_le_mul_of_nonneg_left he2 (by positivity)
  have a7 : 0 ≤ CF ^ 2 * M ^ 2 := by positivity
  nlinarith

theorem st_ar_final {IC IB IR CC W a A CF N M S : ℝ} (hIC : 2 * IC ≤ 2 * CC * W * N)
    (hIB : 2 * IB ≤ 4 * a * A * N)
    (hIR : 2 * IR ≤ (1 + 2 * a * CF) * N + (CF ^ 2 + 2 * a * CF) * M ^ 2 + 2 * CF * M * S)
    (hCC : 0 ≤ CC) (hW : 0 ≤ W) (ha : 0 ≤ a) (hA : 0 ≤ A) (hCF : 0 ≤ CF) (hN : 0 ≤ N)
    (hM : 0 ≤ M) (hS : 0 ≤ S) :
    2 * (IC + IB + IR) ≤
      (2 * CC * W + 4 * a * A + 1 + 2 * a * CF + CF ^ 2 + 2 * CF) * (N + M ^ 2) +
        (2 * CC * W + 4 * a * A + 1 + 2 * a * CF + CF ^ 2 + 2 * CF) * M * S := by
  have b1 : 0 ≤ (2 * CC * W + 4 * a * A + 1) * M ^ 2 := by positivity
  have b2 : 0 ≤ (CF ^ 2 + 2 * CF) * N := by positivity
  have b3 : 0 ≤ (2 * CC * W + 4 * a * A + 1 + 2 * a * CF + CF ^ 2) * (M * S) := by positivity
  have b4 : 0 ≤ 2 * CF * M ^ 2 := by positivity
  nlinarith

/-- **`StTransWord` from its leaves** (SP 3060-3071). -/
theorem stTransWord_of (hS : CellMollSmooth) (hCD : CellConvDeriv) (hIbp : StCellIbp)
    (hR : StReynolds) (hC : StTransComm) (hF : StFriedJet) : StTransWord := by
  intro c m k Av hc
  obtain ⟨CC, hCC0, hCC⟩ := hC c m (k + 1) Av
  obtain ⟨CF, hCF0, hCF⟩ := hF c m k Av hc
  have hW0 : 0 ≤ ((wordsLE (k + 1)).card : ℝ) := Nat.cast_nonneg _
  refine ⟨2 * CC * ((wordsLE (k + 1)).card : ℝ) + 4 * |m| * |Av 0| + 1 + 2 * |m| * CF +
    CF ^ 2 + 2 * CF, by positivity, ?_⟩
  intro v hv φ D M hM hJ hDM n w hw
  have hφp := st_jet_periodic hJ
  have hφm := st_jet_memX hJ
  obtain ⟨hGs, hGp, hGm⟩ := hS c m n φ hc hφp hφm
  obtain ⟨hTs, hTp, hTm⟩ := st_trans_reg hS hCD hc hv hφp hφm n
  have hVs : ContDiff ℝ ∞ (stGrad (stVel v) (cellMoll n φ)) := st_contDiff_stGrad hv hGs
  have hRs : ContDiff ℝ ∞ (stFriedRem v n φ) := hTs.sub hVs
  have hRp : ∀ x : ℝ × ℝ, stFriedRem v n φ (x.1 + c, x.2) = stFriedRem v n φ x := by
    intro x
    show stTrans v n φ (x.1 + c, x.2) - stGrad (stVel v) (cellMoll n φ) (x.1 + c, x.2) =
      stTrans v n φ x - stGrad (stVel v) (cellMoll n φ) x
    rw [hTp x, st_stGrad_periodic hv hGp x]
  -- the splitting `T = v·∇G + R`
  have hTeq : stTrans v n φ =
      fun x => stGrad (stVel v) (cellMoll n φ) x + stFriedRem v n φ x := by
    funext x
    simp only [stFriedRem]
    ring
  have hTw : adjSpatial w (stTrans v n φ) = fun x =>
      adjSpatial w (stGrad (stVel v) (cellMoll n φ)) x + adjSpatial w (stFriedRem v n φ) x := by
    rw [hTeq]
    exact st_adjSpatial_add hVs hRs w
  -- memberships
  have hFs : ContDiff ℝ ∞ (adjSpatial w (cellMoll n φ)) := st_contDiff_adjSpatial hGs w
  have hFp := st_adjSpatial_periodic hGp w
  have hFm : MemLp (adjSpatial w (cellMoll n φ)) 2 (B0579.cellMeasure c (-m)) := hGm w
  have hFall : ∀ u : List (Fin 2), MemLp (adjSpatial u (adjSpatial w (cellMoll n φ))) 2
      (B0579.cellMeasure c (-m)) := fun u => by
    rw [← st_adjSpatial_append]
    exact hGm (u ++ w)
  have hBm : MemLp (stGrad (stVel v) (adjSpatial w (cellMoll n φ))) 2
      (B0579.cellMeasure c (-m)) := st_stGrad_memLp hv fun l => hGm (l :: w)
  obtain ⟨hCwm, hCwb⟩ := hCC v hv (cellMoll n φ) hGs hGm w hw
  have hAm : MemLp (adjSpatial w (stGrad (stVel v) (cellMoll n φ))) 2
      (B0579.cellMeasure c (-m)) := by
    have h := hCwm.add hBm
    have e : ((fun x => adjSpatial w (stGrad (stVel v) (cellMoll n φ)) x -
        stGrad (stVel v) (adjSpatial w (cellMoll n φ)) x) +
        stGrad (stVel v) (adjSpatial w (cellMoll n φ))) =
        adjSpatial w (stGrad (stVel v) (cellMoll n φ)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rwa [e] at h
  have hRw : MemLp (adjSpatial w (stFriedRem v n φ)) 2 (B0579.cellMeasure c (-m)) := by
    have e : adjSpatial w (stFriedRem v n φ) = fun x =>
        adjSpatial w (stTrans v n φ) x - adjSpatial w (stGrad (stVel v) (cellMoll n φ)) x :=
      st_adjSpatial_sub hTs hVs w
    rw [e]
    exact (hTm w).sub hAm
  -- the three terms
  have hI : ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stTrans v n φ)) =
      ipX c m (adjSpatial w (cellMoll n φ)) (fun x =>
          adjSpatial w (stGrad (stVel v) (cellMoll n φ)) x -
            stGrad (stVel v) (adjSpatial w (cellMoll n φ)) x) +
        ipX c m (adjSpatial w (cellMoll n φ)) (stGrad (stVel v) (adjSpatial w (cellMoll n φ))) +
        ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stFriedRem v n φ)) := by
    rw [hTw, st_ipX_add_right hFm hAm hRw]
    congr 1
    rw [← st_ipX_add_right hFm hCwm hBm]
    congr 1
    funext x
    ring
  have he0 : 0 ≤ (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hN0 : 0 ≤ cellEnergy c m w.length (cellMoll n φ) := cellEnergy_nonneg _ _ _ _
  have he2 : (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal ^ 2 ≤
      cellEnergy c m w.length (cellMoll n φ) :=
    sq_toReal_le_cellEnergy c m (cellMoll n φ) (le_refl w.length)
  -- the commutator
  have hcomm := st_ar_comm (st_abs_ipX_le hFm hCwm) hCwb (st_mul_sum_le c m (cellMoll n φ) w)
    (by exact_mod_cast Finset.card_le_card (st_wordsLE_mono hw) :
      ((wordsLE w.length).card : ℝ) ≤ ((wordsLE (k + 1)).card : ℝ)) he0 hCC0 hN0
  -- Reynolds
  have hrey : 2 * ipX c m (adjSpatial w (cellMoll n φ))
      (stGrad (stVel v) (adjSpatial w (cellMoll n φ))) ≤
        4 * |m| * |Av 0| * cellEnergy c m w.length (cellMoll n φ) := by
    have h1 := hR c m v Av (adjSpatial w (cellMoll n φ)) hc hv hFs hFp hFall
    have h2 := (abs_le.mp h1).2
    have h4 : 2 * |m| * Av 0 * (xNorm c (-m) (adjSpatial w (cellMoll n φ))).toReal ^ 2 ≤
        2 * |m| * |Av 0| * cellEnergy c m w.length (cellMoll n φ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) he2 (sq_nonneg _)
        (by positivity)
    linarith
  -- the Friedrichs remainder
  have hfr : 2 * ipX c m (adjSpatial w (cellMoll n φ)) (adjSpatial w (stFriedRem v n φ)) ≤
      (1 + 2 * |m| * CF) * cellEnergy c m w.length (cellMoll n φ) +
        (CF ^ 2 + 2 * |m| * CF) * M ^ 2 +
        2 * CF * M * ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: w) (cellMoll n φ))).toReal := by
    rcases Nat.lt_or_ge w.length (k + 1) with hlt | hge
    · -- `|w| ≤ k`
      obtain ⟨-, hRb⟩ := hCF v hv φ D M hM hJ hDM n w (by omega)
      exact st_ar_frA (st_abs_ipX_le hFm hRw) hRb he0 he2 hCF0 hM hS0 (abs_nonneg m)
    · -- `|w| = k + 1`: move one derivative onto `F`
      have hlen : w.length = k + 1 := le_antisymm hw hge
      obtain ⟨l₀, u, rfl⟩ : ∃ (l₀ : Fin 2) (u : List (Fin 2)), w = l₀ :: u := by
        cases w with
        | nil => simp at hlen
        | cons l₀ u => exact ⟨l₀, u, rfl⟩
      have hu : u.length = k := by simpa using hlen
      obtain ⟨hHm, hHb⟩ := hCF v hv φ D M hM hJ hDM n u hu.le
      have hHs : ContDiff ℝ ∞ (adjSpatial u (stFriedRem v n φ)) := st_contDiff_adjSpatial hRs u
      have hHp := st_adjSpatial_periodic hRp u
      have h1 : |ipX c m (adjSpatial (l₀ :: u) (cellMoll n φ))
            (adjSpatial (l₀ :: u) (stFriedRem v n φ)) +
          ipX c m (adjSpatial (l₀ :: l₀ :: u) (cellMoll n φ)) (adjSpatial u (stFriedRem v n φ))| ≤
          2 * |m| * (xNorm c (-m) (adjSpatial (l₀ :: u) (cellMoll n φ))).toReal *
            (xNorm c (-m) (adjSpatial u (stFriedRem v n φ))).toReal :=
        hIbp c m l₀ _ _ hc hFs hHs hFp hHp hFm hHm (hGm (l₀ :: l₀ :: u)) hRw
      have h2 := (abs_le.mp (st_abs_ipX_le (hGm (l₀ :: l₀ :: u)) hHm)).1
      have hd : (xNorm c (-m) (adjSpatial (l₀ :: l₀ :: u) (cellMoll n φ))).toReal ≤
          ∑ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: l₀ :: u) (cellMoll n φ))).toReal :=
        Finset.single_le_sum (f := fun l : Fin 2 =>
          (xNorm c (-m) (adjSpatial (l :: l₀ :: u) (cellMoll n φ))).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ l₀)
      exact st_ar_frB (abs_le.mp h1).2 (by linarith) hd ENNReal.toReal_nonneg hHb he0 he2 hCF0 hM
        hS0 (abs_nonneg m)
  rw [hI]
  exact st_ar_final hcomm hrey hfr hCC0 hW0 (abs_nonneg m) (abs_nonneg _) hCF0 hN0 hM hS0

end UnforcedLeray.Short.IIIa
