import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.XJetOff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_5

/-!
# `PartIII-b:C/rep/8/2/2/1`: the Hessian bound `MeanXHess` of the mean Newton field

Source `the November 2 reference manuscript`
5438-5448, 5380-5387, 5400-5413.

At `ε = 1` the stream-cut mean field has `‖D²X^mt_1(w)‖ ≤ C r^{-4}|w|^{-2}N₀^χ` for `ν ≤ r²`
(`xmtJetOff_of`: `newtonVCutBound` and `scXJetOff`, `m = 2`).  By `X^mt_ε = ε²X^mt_1(ε·)`
(`Scale.Xmt_smul`), `D²X^mt_ε(y) = ε⁴D²X^mt_1(εy)`; at the receiver
`y = (R/√s, 0, η/√s)`, `R = ε⁻¹`, one has `w = εy`, `r = s^{-1/2}`, `|w| ≥ r`, so
`r^{-4}|w|^{-2} ≤ s³`.  `N₀^χ ≤ N₁(χ_oT)` is `n0cutLeN1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanXHessP

/-- The derivative of a `WithLp` conjugate: `D(toLp ∘ G ∘ ofLp)(y) u = toLp (DG(ofLp y)(ofLp u))`. -/
theorem lift_fderiv {G : Vec3 → Vec3} (y : Space) (hG : DifferentiableAt ℝ G (WithLp.ofLp y))
    (u : Space) :
    fderiv ℝ (fun y' : Space => WithLp.toLp 2 (G (WithLp.ofLp y'))) y u =
      WithLp.toLp 2 (fderiv ℝ G (WithLp.ofLp y) (WithLp.ofLp u)) := by
  have e1 := hG.hasFDerivAt.comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 y)
  have e2 := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (G (WithLp.ofLp y))).comp y e1
  have : fderiv ℝ (fun y' : Space => WithLp.toLp 2 (G (WithLp.ofLp y'))) y =
      _ := e2.fderiv
  rw [this]
  rfl

/-- `toLp` is bounded on `Vec3`. -/
theorem exists_toLp_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Vec3, ‖(WithLp.toLp 2 u : Space)‖ ≤ K * ‖u‖ := by
  let e : Vec3 ≃L[ℝ] Space := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  refine ⟨‖(e : Vec3 →L[ℝ] Space)‖, norm_nonneg _, fun u => ?_⟩
  exact (e : Vec3 →L[ℝ] Space).le_opNorm u

theorem norm_ofLp_coord (j : Fin 3) : ‖WithLp.ofLp (coordinateVector j : Space)‖ ≤ 1 := by
  have : WithLp.ofLp (coordinateVector j : Space) = Pi.single j 1 := by
    ext k
    simp [coordinateVector, EuclideanSpace.single_apply, Pi.single_apply]
  rw [this]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by
    by_cases h : k = j <;> simp [Pi.single_apply, h]

theorem physPd2_bound {K : ℝ} (hK : ∀ u : Vec3, ‖(WithLp.toLp 2 u : Space)‖ ≤ K * ‖u‖)
    (hK0 : 0 ≤ K) {G : Vec3 → Vec3} (hG : ContDiff ℝ 2 G) (j l : Fin 3) (y : Space) :
    ‖physPd2 (fun y' : Space => WithLp.toLp 2 (G (WithLp.ofLp y'))) j l y‖ ≤
      K * ‖fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y)‖ := by
  set F : Space → Space := fun y' => WithLp.toLp 2 (G (WithLp.ofLp y')) with hF
  have hD : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDG : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set u0 : Vec3 := WithLp.ofLp (coordinateVector l : Space) with hu0
  set H : Vec3 → Vec3 := fun v => fderiv ℝ G v u0 with hH
  have hpd : (fun y' : Space => physPd F l y') =
      fun y' => WithLp.toLp 2 (H (WithLp.ofLp y')) := by
    funext y'
    simp only [physPd, hF, hH]
    exact lift_fderiv y' (hD _) _
  have hHd : DifferentiableAt ℝ H (WithLp.ofLp y) :=
    (hDG _).clm_apply (differentiableAt_const u0)
  have hHder : ∀ w : Vec3, fderiv ℝ H (WithLp.ofLp y) w = fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y) w u0 := by
    intro w
    have := ((hDG _).hasFDerivAt.clm_apply (hasFDerivAt_const u0 (WithLp.ofLp y)))
    have e : fderiv ℝ H (WithLp.ofLp y) = _ := this.fderiv
    rw [e]
    simp
  have key : physPd2 F j l y =
      WithLp.toLp 2 (fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y) (WithLp.ofLp (coordinateVector j : Space)) u0) := by
    unfold physPd2
    rw [hpd]
    unfold physPd
    rw [lift_fderiv y hHd, hHder]
  rw [key]
  refine (hK _).trans ?_
  have h1 : ‖fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y) (WithLp.ofLp (coordinateVector j : Space)) u0‖ ≤
      ‖fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y)‖ := by
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y) (WithLp.ofLp (coordinateVector j : Space))‖ *
          ‖u0‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y)‖ * ‖WithLp.ofLp (coordinateVector j : Space)‖) * ‖u0‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (‖fderiv ℝ (fderiv ℝ G) (WithLp.ofLp y)‖ * 1) * 1 := by
          gcongr
          · exact norm_ofLp_coord j
          · exact norm_ofLp_coord l
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left h1 hK0

end MeanXHessP

/-- **The Hessian bound at one level** (source 5445-5447). -/
theorem meanXHessAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy)
    (hfin : ∀ T : LStr Pl K L, OldThinFinite (cOf L.ν) L.ν (thinRep T))
    {Kt : ℝ} (hKt : ∀ u : Vec3, ‖(WithLp.toLp 2 u : Space)‖ ≤ Kt * ‖u‖) (hKt0 : 0 ≤ Kt)
    {CJ : ℝ}
    (hJ : ∀ (c ν μ : ℝ), LHyp c ν 1 μ K.χo K.χy → ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ∀ w : Vec3, ν ≤ cylR w ^ 2 → ∀ m : ℕ, m ≤ 3 →
        ‖iteratedFDeriv ℝ m (Xmt c ν 1 μ K.χo K.χy M) w‖ ≤
          CJ * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν K.χo M) :
    MeanXHessAt Pl K L μ (Kt * |CJ|) 0 := by
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
  have hX1 : ContDiff ℝ 3 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) :=
    (xmtSmooth _ _ _ _ _ _ hL1 M (hfin T)).of_le (by norm_num)
  have hXe : ContDiff ℝ 2 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M) :=
    (xmtSmooth _ _ _ _ _ _ hL M (hfin T)).of_le (by norm_num)
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
  have hjet := hJ _ _ _ hL1 M (hfin T) (L.ε • v) hrange 2 (by norm_num)
  have hN0 : 0 ≤ oldN0cut (cOf L.ν) L.ν K.χo M := oldN0cut_nonneg _ _ hν K.hχo M
  have hpow : cylR (L.ε • v) ^ (-(2 : ℝ) - ((2 : ℕ) : ℝ)) = s ^ 2 := by
    rw [hcyl]
    have : (-(2 : ℝ) - ((2 : ℕ) : ℝ)) = -(4 : ℕ) := by norm_num
    rw [this, Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow, one_pow,
      show Real.sqrt s ^ 4 = s ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hs0.le]]
    simp
  have hinv : (eucSq (L.ε • v))⁻¹ ≤ s := by
    have := inv_anti₀ (inv_pos.2 hs0) heuc
    simpa using this
  have hit : ‖iteratedFDeriv ℝ 2 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) (L.ε • v)‖ ≤
      |CJ| * s ^ 3 * oldN0cut (cOf L.ν) L.ν K.χo M := by
    refine hjet.trans ?_
    rw [hpow]
    have h1 : CJ * s ^ 2 * (eucSq (L.ε • v))⁻¹ ≤ |CJ| * s ^ 2 * s := by
      calc CJ * s ^ 2 * (eucSq (L.ε • v))⁻¹ ≤ |CJ| * s ^ 2 * (eucSq (L.ε • v))⁻¹ := by
            gcongr
            · exact inv_nonneg.2 (le_trans (inv_nonneg.2 hs0.le) heuc)
            · exact le_abs_self _
        _ ≤ |CJ| * s ^ 2 * s := by gcongr
    calc _ ≤ |CJ| * s ^ 2 * s * oldN0cut (cOf L.ν) L.ν K.χo M := by gcongr
      _ = _ := by ring
  have hXmean : Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy M (NearInst.chartTau L.ε⁻¹ (s, (q, η))) =
      fun y' : Space => WithLp.toLp 2 (JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε
        (WithLp.ofLp y')) := by
    funext y'
    simp only [Xmean, JetClockCore.Xsc]
    rw [Scale.Xmt_smul hε]
  have hsc := scD2 (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε v hX1 hε
  have hpd := MeanXHessP.physPd2_bound hKt hKt0
    (G := JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε)
    (by
      have : JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε =
          Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy M := by
        funext y'; simp only [JetClockCore.Xsc]; rw [Scale.Xmt_smul hε]
      rw [this]; exact hXe) j l (NearInst.chartY L.ε⁻¹ (s, (q, η)))
  have hreal : ‖physPd2 (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy M
        (NearInst.chartTau L.ε⁻¹ (s, (q, η)))) j l (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖ ≤
      Kt * |CJ| * L.ε ^ 4 * s ^ 3 * oldN0cut (cOf L.ν) L.ν K.χo M := by
    rw [hXmean]
    refine hpd.trans ?_
    have h2 : ‖fderiv ℝ (fderiv ℝ (JetClockCore.Xsc (Xmt (cOf L.ν) L.ν 1 μ K.χo K.χy M) L.ε)) v‖ ≤
        L.ε ^ 4 * (|CJ| * s ^ 3 * oldN0cut (cOf L.ν) L.ν K.χo M) :=
      hsc.trans (mul_le_mul_of_nonneg_left hit (by positivity))
    calc Kt * _ ≤ Kt * (L.ε ^ 4 * (|CJ| * s ^ 3 * oldN0cut (cOf L.ν) L.ν K.χo M)) :=
          mul_le_mul_of_nonneg_left h2 hKt0
      _ = _ := by ring
  have hN1 : ENNReal.ofReal (oldN0cut (cOf L.ν) L.ν K.χo M) ≤ oldN1 Pl K L T :=
    n0cutLeN1 (cOf L.ν) L.ν K.χo hc hν K.hχo M (hfin T)
  rw [← ofReal_norm]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal (Kt * |CJ| * L.ε ^ 4 * s ^ 3 *
        oldN0cut (cOf L.ν) L.ν K.χo M) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Kt * |CJ| * L.ε ^ 4 * s ^ 3) *
        ENNReal.ofReal (oldN0cut (cOf L.ν) L.ν K.χo M) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (Kt * |CJ| * L.ν⁻¹ ^ 0 * L.ε ^ 4 * s ^ (3 : ℝ)) * oldN1 Pl K L T := by
        have h3 : s ^ (3 : ℝ) = s ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast s 3
        rw [h3, pow_zero, mul_one]
        gcongr

/-- **`meanXHess`** (source 5445-5447): the Hessian bound of the mean Newton field at the young
receivers. -/
theorem meanXHess (D : SeqData) {dm dp : ℝ} : D.MeanXHessSeq dm dp := by
  intro hst
  obtain ⟨CJ, hCJ⟩ := xmtJetOff_of (newtonVCutBound D.K.χo) (scXJetOff D.K.χy)
  obtain ⟨Kt, hKt0, hKt⟩ := MeanXHessP.exists_toLp_bound
  obtain ⟨CN, kN, hCN⟩ := sourceLN0 D.K.mZ (gRate D.Pl) hst.mZ_gt hst.gamma_pos
  refine ⟨Kt * |CJ|, 0, ?_⟩
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY] with n hn z hz
  have h := hn z hz
  exact meanXHessAt_of D.Pl D.K (D.level n) (D.mu n z) h
    (fun T => (hCN (cOf (D.level n).ν) (D.level n).ν ((D.level n).ρb D.Pl D.K) h.c_pos
      h.nu_pos h.nu_le T).1) hKt hKt0
    (fun c ν μ hL M hM w hw m hm => hCJ c ν μ hL M hM w hw m hm)

end UnforcedLeray.Short.PartIIIb.Concrete
end
