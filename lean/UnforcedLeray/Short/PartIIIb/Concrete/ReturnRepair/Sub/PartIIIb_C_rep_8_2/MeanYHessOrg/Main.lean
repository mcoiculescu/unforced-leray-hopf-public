import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Props

/-!
# `PartIII-b:C/rep/8/2/2/2/org`: the Hessian of `Y^mt` from the jets of `X^mt`

Source `the November 2 reference manuscript`
5380-5387 (`Y^mt = D_{μ+1}X^mt = (-½y·∇ - νΔ + μ + ½)X^mt`), 5400-5413 (kernel degree `-5`, ratio
`≤ 1/√1.2`, every `s∂_s`/`y·∇` costs a factor `r` and the degree is kept), 5438-5448.

At the receiver `y = (R/√s, 0, η/√s)`, `w = εy = (s^{-1/2}, 0, εη/√s)`, `r = s^{-1/2}`,
`|w|² = (1 + ε²η²)/s ≥ r²`.  With `‖D^mX_1(w)‖ ≤ C r^{-2-m}|w|^{-2}N` (`XmtJetOff`, `m ≤ 3`;
`XmtJetOff4`, `m = 4`) and `X_ε = ε²X_1(ε·)`:
* `‖D²X_ε‖ ≤ ε⁴Cs³N`;
* `‖D³X_ε‖‖y‖ ≤ ε⁴ C r^{-5}|w|^{-2}|w|N ≤ ε⁴Cs³N` (the factor `|y| = |w|/ε` is absorbed by the
  decay `|w|^{-2}` of the kernel off the ray);
* `ν‖D⁴X_ε‖ ≤ νε⁶Cr^{-6}|w|^{-2}N ≤ ε⁴Cs³N` (`νs ≤ 1`, `ε ≤ 1`).
`MeanYHessAt` follows from `MeanYHessCalc.Yf_iter2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanYHessCalc

theorem cyl_pow {q : ℝ} (hq : 0 < q) (m : ℕ) : (1 / q) ^ (-(2 : ℝ) - (m : ℝ)) = q ^ (2 + m) := by
  have : (-(2 : ℝ) - (m : ℝ)) = -((2 + m : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div, inv_pow, inv_inv]

end MeanYHessCalc

/-- **The Hessian bound for `Y^mt` at one level** (source 5445-5447, 5380-5387). -/
theorem meanYHessAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy)
    (hfin : ∀ T : LStr Pl K L, OldThinFinite (cOf L.ν) L.ν (thinRep T))
    (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    {Kt : ℝ} (hKt : ∀ u : Vec3, ‖(WithLp.toLp 2 u : Space)‖ ≤ Kt * ‖u‖) (hKt0 : 0 ≤ Kt)
    {CJ : ℝ}
    (hJ : ∀ (c ν μ : ℝ), LHyp c ν 1 μ K.χo K.χy → ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ∀ w : Vec3, ν ≤ cylR w ^ 2 → ∀ m : ℕ, m ≤ 3 →
        ‖iteratedFDeriv ℝ m (Xmt c ν 1 μ K.χo K.χy M) w‖ ≤
          CJ * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν K.χo M)
    {C4 : ℝ}
    (hJ4 : ∀ (c ν μ : ℝ), LHyp c ν 1 μ K.χo K.χy → ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ∀ w : Vec3, ν ≤ cylR w ^ 2 → ∀ m : ℕ, m = 4 →
        ‖iteratedFDeriv ℝ m (Xmt c ν 1 μ K.χo K.χy M) w‖ ≤
          C4 * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν K.χo M) :
    MeanYHessAt Pl K L μ (Kt * (3 * |CJ| + 3 * |C4|)) 0 := by
  intro T p hp0 hp1 j l
  obtain ⟨s, q, η⟩ := p
  have hs0 : 0 < s := hp0
  have hs1 : s ≤ 1 / L.ν := hp1
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hL1 : LHyp (cOf L.ν) L.ν 1 μ K.χo K.χy :=
    ⟨hL.c_pos, hL.nu_pos, hL.nu_le, one_pos, hL.mu_pos, hL.mu_lt, hL.chiO, hL.chiY⟩
  set M : Chart → Mat3 := thinRep T with hM
  have hX1 : ContDiff ℝ 4 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) :=
    (xmtSmooth _ _ _ _ _ _ hL1 M (hfin T)).of_le (by norm_num)
  have hXe : ContDiff ℝ 4 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) :=
    (xmtSmooth _ _ _ _ _ _ hL M (hfin T)).of_le (by norm_num)
  have hGeq : JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε =
      Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M := by
    funext y'; simp only [JetClockCore.Xsc]; rw [Scale.Xmt_smul hε]
  set v : Vec3 := WithLp.ofLp (NearInst.chartY L.ε⁻¹ (s, (q, η))) with hv
  have hvdef : v = ![L.ε⁻¹ / Real.sqrt s, 0, η / Real.sqrt s] := by
    ext i; fin_cases i <;> simp [hv, NearInst.chartY]
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hεne : L.ε ≠ 0 := hε.ne'
  have hw : L.ε • v = ![1 / Real.sqrt s, 0, L.ε * η / Real.sqrt s] := by
    rw [hvdef]
    ext i; fin_cases i <;> simp <;> field_simp
  have hcyl : cylR (L.ε • v) = 1 / Real.sqrt s := by
    rw [hw]; unfold cylR; simp
  have hcyl2 : cylR (L.ε • v) ^ 2 = s⁻¹ := by
    rw [hcyl, div_pow, Real.sq_sqrt hs0.le]; simp
  have heuc : s⁻¹ ≤ eucSq (L.ε • v) := by
    rw [hw]; unfold eucSq
    simp [Fin.sum_univ_three, div_pow, Real.sq_sqrt hs0.le]
    have : 0 ≤ (L.ε * η) ^ 2 / s := by positivity
    linarith
  have hrange : L.ν ≤ cylR (L.ε • v) ^ 2 := by
    rw [hcyl2]
    rw [le_inv_comm₀ hν hs0]
    simpa [one_div] using hs1
  have hνs : L.ν * s ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hs1 hν.le
    rwa [mul_one_div_cancel hν.ne'] at this
  set N : ℝ := oldN0cut (cOf L.ν) L.ν K.χo M with hNdef
  have hN0 : 0 ≤ N := oldN0cut_nonneg _ _ hν K.hχo M
  set w : Vec3 := L.ε • v with hwdef
  set E : ℝ := (eucSq w)⁻¹ with hEdef
  have hesq : 0 < eucSq w := lt_of_lt_of_le (inv_pos.2 hs0) heuc
  have hE0 : 0 ≤ E := inv_nonneg.2 hesq.le
  have hEs : E ≤ s := by
    have := inv_anti₀ (inv_pos.2 hs0) heuc
    simpa using this
  set σ : ℝ := Real.sqrt (eucSq w) with hσdef
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hesq
  have hσ2 : σ ^ 2 = eucSq w := Real.sq_sqrt hesq.le
  have hσq : (Real.sqrt s)⁻¹ ≤ σ := by
    rw [hσdef]
    apply Real.le_sqrt_of_sq_le
    rw [inv_pow, Real.sq_sqrt hs0.le]; exact heuc
  have hEσ : E * σ ≤ Real.sqrt s := by
    have h1 : E * σ = σ⁻¹ := by
      rw [hEdef, ← hσ2]; field_simp
    rw [h1]
    calc σ⁻¹ ≤ ((Real.sqrt s)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hsq) hσq
      _ = _ := inv_inv _
  have hwσ : ‖w‖ ≤ σ := by
    refine (pi_norm_le_iff_of_nonneg hσ0.le).2 fun i => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    unfold eucSq
    exact Finset.single_le_sum (f := fun i => w i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  have hwv : ‖w‖ = L.ε * ‖v‖ := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  -- the jets of `X_1` at `w`
  have hj : ∀ m : ℕ, m ≤ 3 → ‖iteratedFDeriv ℝ m (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) w‖ ≤
      |CJ| * Real.sqrt s ^ (2 + m) * E * N := by
    intro m hm
    have := hJ _ _ _ hL1 M (hfin T) w hrange m hm
    rw [hcyl, MeanYHessCalc.cyl_pow hsq] at this
    refine this.trans ?_
    gcongr
    exact le_abs_self _
  have hj4 : ‖iteratedFDeriv ℝ 4 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) w‖ ≤
      |C4| * Real.sqrt s ^ (2 + 4) * E * N := by
    have := hJ4 _ _ _ hL1 M (hfin T) w hrange 4 rfl
    rw [hcyl, MeanYHessCalc.cyl_pow hsq] at this
    refine this.trans ?_
    gcongr
    exact le_abs_self _
  have hq2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hε0 := hε.le
  -- derivative bounds of `G = X_ε` at `v`
  have hG2 : ‖iteratedFDeriv ℝ 2 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) v‖ ≤
      L.ε ^ 4 * (|CJ| * s ^ 3 * N) := by
    rw [← hGeq]
    refine (MeanYHessCalc.iter_Xsc hX1 hε0 2 (by norm_num) v).trans ?_
    have h := hj 2 (by norm_num)
    calc L.ε ^ (2 + 2) * ‖iteratedFDeriv ℝ 2 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) (L.ε • v)‖
        ≤ L.ε ^ (2 + 2) * (|CJ| * Real.sqrt s ^ (2 + 2) * E * N) := by gcongr
      _ ≤ L.ε ^ 4 * (|CJ| * Real.sqrt s ^ (2 + 2) * s * N) := by gcongr
      _ = L.ε ^ 4 * (|CJ| * s ^ 3 * N) := by
        have : Real.sqrt s ^ (2 + 2) = s ^ 2 := by
          rw [show 2 + 2 = 2 * 2 from rfl, pow_mul, hq2]
        rw [this]; ring
  have hG3 : ‖iteratedFDeriv ℝ 3 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) v‖ * ‖v‖ ≤
      L.ε ^ 4 * (|CJ| * s ^ 3 * N) := by
    rw [← hGeq]
    have h1 := MeanYHessCalc.iter_Xsc hX1 hε0 3 (by norm_num) v
    have h := hj 3 (by norm_num)
    have hv' : ‖v‖ = ‖w‖ / L.ε := by rw [hwv]; field_simp
    have hnn : 0 ≤ ‖v‖ := norm_nonneg _
    calc _ ≤ (L.ε ^ (2 + 3) * (|CJ| * Real.sqrt s ^ (2 + 3) * E * N)) * ‖v‖ := by
          gcongr
          exact h1.trans (by gcongr)
      _ = L.ε ^ 4 * (|CJ| * Real.sqrt s ^ (2 + 3) * N * (E * ‖w‖)) := by
          rw [hv']; field_simp; ring
      _ ≤ L.ε ^ 4 * (|CJ| * Real.sqrt s ^ (2 + 3) * N * (Real.sqrt s)) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left hwσ hE0).trans hEσ
      _ = L.ε ^ 4 * (|CJ| * s ^ 3 * N) := by
          have : Real.sqrt s ^ (2 + 3) * Real.sqrt s = s ^ 3 := by
            rw [← pow_succ, show 2 + 3 + 1 = 2 * 3 from rfl, pow_mul, hq2]
          calc _ = L.ε ^ 4 * (|CJ| * N * (Real.sqrt s ^ (2 + 3) * Real.sqrt s)) := by ring
            _ = _ := by rw [this]; ring
  have hG4 : L.ν * ‖iteratedFDeriv ℝ 4 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) v‖ ≤
      L.ε ^ 4 * (|C4| * s ^ 3 * N) := by
    rw [← hGeq]
    have h1 := MeanYHessCalc.iter_Xsc hX1 hε0 4 (by norm_num) v
    have hε2 : L.ε ^ 2 ≤ 1 := pow_le_one₀ hε0 hε1
    have hq6 : Real.sqrt s ^ (2 + 4) = s ^ 3 := by
      rw [show 2 + 4 = 2 * 3 from rfl, pow_mul, hq2]
    calc L.ν * ‖iteratedFDeriv ℝ 4 (JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε) v‖
        ≤ L.ν * (L.ε ^ (2 + 4) * (|C4| * Real.sqrt s ^ (2 + 4) * E * N)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ ≤ L.ν * (L.ε ^ (2 + 4) * (|C4| * s ^ 3 * s * N)) := by
          rw [hq6]; gcongr
      _ = (L.ν * s) * (L.ε ^ 2) * (L.ε ^ 4 * (|C4| * s ^ 3 * N)) := by ring
      _ ≤ 1 * 1 * (L.ε ^ 4 * (|C4| * s ^ 3 * N)) := by gcongr
      _ = _ := by ring
  -- the second derivative of `Y`
  have hYeq : Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy M (NearInst.chartTau L.ε⁻¹ (s, (q, η))) =
      fun y' : Space => WithLp.toLp 2 (JetClockCore.Yf
        (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) L.ν μ (WithLp.ofLp y')) := rfl
  have hY2 := MeanYHessCalc.Yf_iter2 hXe L.ν μ v
  have hpd := MeanXHessP.physPd2_bound hKt hKt0
    (G := JetClockCore.Yf (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) L.ν μ)
    (MeanYHessCalc.Yf_contDiff hXe L.ν μ) j l (NearInst.chartY L.ε⁻¹ (s, (q, η)))
  have hfd : ‖fderiv ℝ (fderiv ℝ (JetClockCore.Yf (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) L.ν μ))
      v‖ = ‖iteratedFDeriv ℝ 2 (JetClockCore.Yf (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) L.ν μ) v‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv (n := 1)]
  have hμ1 : |μ + 1 / 2| ≤ 1 := by
    rw [abs_of_pos (by linarith [hL.mu_pos])]; linarith [hL.mu_lt]
  have hνabs : |L.ν| = L.ν := abs_of_pos hν
  have hCJ := abs_nonneg CJ
  have hC4 := abs_nonneg C4
  have hYb : ‖iteratedFDeriv ℝ 2 (JetClockCore.Yf (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) L.ν μ) v‖ ≤
      L.ε ^ 4 * ((3 * |CJ| + 3 * |C4|) * s ^ 3 * N) := by
    refine hY2.trans ?_
    rw [hνabs]
    have a2 := mul_le_mul_of_nonneg_left hG2 (by norm_num : (0:ℝ) ≤ 2)
    have a3 := mul_le_mul_of_nonneg_left hG4 (by norm_num : (0:ℝ) ≤ 3)
    have a5 : |μ + 1 / 2| * ‖iteratedFDeriv ℝ 2 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) v‖ ≤
        L.ε ^ 4 * (|CJ| * s ^ 3 * N) :=
      (mul_le_mul hμ1 hG2 (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
    have : L.ν * (3 * ‖iteratedFDeriv ℝ 4 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) v‖) =
        3 * (L.ν * ‖iteratedFDeriv ℝ 4 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) v‖) := by ring
    rw [this]
    have hX0 : 0 ≤ L.ε ^ 4 * (|CJ| * s ^ 3 * N) := by positivity
    have hR : L.ε ^ 4 * ((3 * |CJ| + 3 * |C4|) * s ^ 3 * N) =
        3 * (L.ε ^ 4 * (|CJ| * s ^ 3 * N)) + 3 * (L.ε ^ 4 * (|C4| * s ^ 3 * N)) := by ring
    rw [hR]
    linarith [hG3, a2, a3, a5]
  have hreal : ‖physPd2 (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy M
        (NearInst.chartTau L.ε⁻¹ (s, (q, η)))) j l (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖ ≤
      Kt * (3 * |CJ| + 3 * |C4|) * L.ε ^ 4 * s ^ 3 * N := by
    rw [hYeq]
    refine hpd.trans ?_
    rw [hfd]
    calc Kt * _ ≤ Kt * (L.ε ^ 4 * ((3 * |CJ| + 3 * |C4|) * s ^ 3 * N)) :=
          mul_le_mul_of_nonneg_left hYb hKt0
      _ = _ := by ring
  have hN1 : ENNReal.ofReal N ≤ oldN1 Pl K L T :=
    n0cutLeN1 (cOf L.ν) L.ν K.χo hc hν K.hχo M (hfin T)
  rw [← ofReal_norm]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal (Kt * (3 * |CJ| + 3 * |C4|) * L.ε ^ 4 * s ^ 3 * N) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Kt * (3 * |CJ| + 3 * |C4|) * L.ε ^ 4 * s ^ 3) * ENNReal.ofReal N :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (Kt * (3 * |CJ| + 3 * |C4|) * L.ν⁻¹ ^ 0 * L.ε ^ 4 * s ^ (3 : ℝ)) *
        oldN1 Pl K L T := by
        have h3 : s ^ (3 : ℝ) = s ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast s 3
        rw [h3, pow_zero, mul_one]
        gcongr

/-- **`meanYHess` from the fourth-derivative bound** (source 5445-5447, 5380-5387): the Hessian
bound of `Y^mt` at the young receivers, given `XmtJetOff4`. -/
theorem meanYHess_of (D : SeqData) {dm dp : ℝ} (hJ4 : XmtJetOff4 D.K.χo D.K.χy) :
    D.MeanYHessSeq dm dp := by
  intro hst
  obtain ⟨CJ, hCJ⟩ := xmtJetOff_of (newtonVCutBound D.K.χo) (scXJetOff D.K.χy)
  obtain ⟨C4, hC4⟩ := hJ4
  obtain ⟨Kt, hKt0, hKt⟩ := MeanXHessP.exists_toLp_bound
  obtain ⟨CN, kN, hCN⟩ := sourceLN0 D.K.mZ (gRate D.Pl) hst.mZ_gt hst.gamma_pos
  have hle := retNu_retEps_eventually_le_one (Pl := D.Pl) (σ₀ := D.σ₀) hst.omega_ne
    hst.gamma_pos D.coeff_ne
  refine ⟨Kt * (3 * |CJ| + 3 * |C4|), 0, ?_⟩
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY, hle] with n hn hle' z hz
  have h := hn z hz
  exact meanYHessAt_of D.Pl D.K (D.level n) (D.mu n z) h
    (fun T => (hCN (cOf (D.level n).ν) (D.level n).ν ((D.level n).ρb D.Pl D.K) h.c_pos
      h.nu_pos h.nu_le T).1) hle'.1 hle'.2 hKt hKt0
    (fun c ν μ hL M hM w hw m hm => hCJ c ν μ hL M hM w hw m hm)
    (fun c ν μ hL M hM w hw m hm => hC4 c ν μ hL M hM w hw m hm)

end UnforcedLeray.Short.PartIIIb.Concrete
end
