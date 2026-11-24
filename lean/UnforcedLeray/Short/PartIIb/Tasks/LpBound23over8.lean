import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.WeakDq
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.PhysPoly
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.FlatPoly

/-!
# Part II-b, task `PartII-b:T17`: uniform polynomial `L^r` endpoint bound at `r = 23/8`

Source of record: `the November 2 reference manuscript`, lines 1992-1996:
"At exponent `r = 23/8`, `(bg:profile-graph)` and the local coordinate identities give a uniform
polynomial bound for the same operator."

Proves `compRate_zero` for general `1 < r < 3` with gap `(3/r - 1)/2` and rate exponent `θ = 0`,
and specializes to `r = bgr = 23/8` (`gap = 1/46`) to obtain `lp_endpoint_bound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dqOf_eq_add (ε : ℝ) (b Sb Qb Eb : CProf) (x : Coord) :
    dqOf ε b Sb Qb Eb x =
      Qb x + (ε : ℂ) • ((2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x) := by
  ext i
  simp [dqOf]
  ring

theorem sqrt_inv_bound {s Γ : ℝ} (hs : 0 < s) (hsinv : s⁻¹ ≤ Γ) (hΓ1 : 1 ≤ Γ) :
    1 ≤ Real.sqrt s * Γ := by
  have h1 : 1 ≤ s * s⁻¹ := by rw [mul_inv_cancel₀ hs.ne']
  have h2 : s * s⁻¹ ≤ s * Γ ^ 2 := by
    have : s⁻¹ ≤ Γ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hs.le
  have hsq := Real.sqrt_le_sqrt (h1.trans h2)
  rw [Real.sqrt_one, Real.sqrt_mul hs.le, Real.sqrt_sq (by linarith)] at hsq
  exact hsq

theorem norm_sqrtS (P : CProf) (x : Coord) :
    ‖sqrtS P x‖ = Real.sqrt x.1 * ‖P x‖ := by
  simp [sqrtS, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_le_gamma_mul_norm_sqrtS {σ H₁ L₁ Γ : ℝ} (hσ : 0 < σ) (hσΓ : σ⁻¹ ≤ Γ) (hΓ1 : 1 ≤ Γ)
    (P : CProf) {x : Coord} (hx : x ∈ obsBox σ H₁ L₁) :
    ‖P x‖ ≤ Γ * ‖sqrtS P x‖ := by
  have hx1 : σ ≤ x.1 := hx.1.1
  have hs : 0 < x.1 := lt_of_lt_of_le hσ hx1
  have hsinv : x.1⁻¹ ≤ Γ := (inv_anti₀ hσ hx1).trans hσΓ
  have h1 := sqrt_inv_bound hs hsinv hΓ1
  calc ‖P x‖ = 1 * ‖P x‖ := (one_mul _).symm
    _ ≤ (Real.sqrt x.1 * Γ) * ‖P x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = Γ * (Real.sqrt x.1 * ‖P x‖) := by ring
    _ = Γ * ‖sqrtS P x‖ := by rw [norm_sqrtS]

theorem obsOp_coeff_bound {σ H₁ L₁ Γ : ℝ} (B : ObsOp σ H₁ L₁ Γ) (x : Coord) :
    ‖B.Aq x‖ ≤ Γ ∧ ‖B.Aeta x‖ ≤ Γ ∧ ‖B.A0 x‖ ≤ Γ := by
  have hb := B.bounded 0 (by decide) x
  simpa only [norm_iteratedFDeriv_zero] using hb

theorem obsOp_apply_eq_zero_of_notMem {σ H₁ L₁ Γ : ℝ} (B : ObsOp σ H₁ L₁ Γ)
    (d gq gη : CProf) {x : Coord} (hx : x ∉ obsBox σ H₁ L₁) :
    B.apply d gq gη x = 0 := by
  obtain ⟨h1, h2, h3⟩ := B.supp x hx
  simp [ObsOp.apply, h1, h2, h3]

theorem norm_dqOf_le {σ H₁ L₁ Γ ε : ℝ} (hL₁ : L₁ ≤ Γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (b Sb Qb Eb : CProf) {x : Coord} (hx : x ∈ obsBox σ H₁ L₁) :
    ‖dqOf ε b Sb Qb Eb x‖ ≤ ‖Qb x‖ + 2 * ‖Sb x‖ + Γ * ‖Eb x‖ + ‖b x‖ := by
  have hη : |x.2.2| ≤ Γ := (abs_le.mpr hx.2.2).trans hL₁
  rw [dqOf_eq_add]
  have h1 : ‖(2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x‖ ≤
      2 * ‖Sb x‖ + |x.2.2| * ‖Eb x‖ + ‖b x‖ := by
    calc ‖(2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x‖
        ≤ ‖(2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x‖ + ‖b x‖ := norm_add_le _ _
      _ ≤ ‖(2 : ℂ) • Sb x‖ + ‖(x.2.2 : ℂ) • Eb x‖ + ‖b x‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ = 2 * ‖Sb x‖ + |x.2.2| * ‖Eb x‖ + ‖b x‖ := by
          simp [norm_smul, Real.norm_eq_abs]
  calc ‖Qb x + (ε : ℂ) • ((2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x)‖
      ≤ ‖Qb x‖ + ‖(ε : ℂ) • ((2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x)‖ := norm_add_le _ _
    _ = ‖Qb x‖ + ε * ‖(2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε0.le]
    _ ≤ ‖Qb x‖ + 1 * (2 * ‖Sb x‖ + |x.2.2| * ‖Eb x‖ + ‖b x‖) := by
        gcongr
    _ ≤ ‖Qb x‖ + (2 * ‖Sb x‖ + Γ * ‖Eb x‖ + ‖b x‖) := by
        rw [one_mul]
        gcongr
    _ = ‖Qb x‖ + 2 * ‖Sb x‖ + Γ * ‖Eb x‖ + ‖b x‖ := by ring

theorem obsOp_pointwise_bound {σ H₁ L₁ Γ ε : ℝ} (hσ : 0 < σ) (hσΓ : σ⁻¹ ≤ Γ)
    (hL₁ : L₁ ≤ Γ) (hΓ1 : 1 ≤ Γ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (B : ObsOp σ H₁ L₁ Γ) (bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 : CProf) (x : Coord) :
    ‖B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0) x‖ ≤
      2 * Γ ^ 3 *
        ((‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) +
          (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖)) := by
  have hRHS_nonneg : 0 ≤ 2 * Γ ^ 3 *
      ((‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) +
        (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖)) := by positivity
  by_cases hx : x ∈ obsBox σ H₁ L₁
  · obtain ⟨hAq, hAeta, hA0⟩ := obsOp_coeff_bound B x
    set gq := dqOf ε bε Sbε Qbε Ebε - Qb0
    set gη := Ebε - Eb0
    set d := bε - b0
    have hB : ‖B.apply d gq gη x‖ ≤ Γ * (‖gq x‖ + ‖gη x‖ + ‖d x‖) := by
      unfold ObsOp.apply
      calc ‖B.Aq x (gq x) + B.Aeta x (gη x) + B.A0 x (d x)‖
          ≤ ‖B.Aq x (gq x) + B.Aeta x (gη x)‖ + ‖B.A0 x (d x)‖ := norm_add_le _ _
        _ ≤ ‖B.Aq x (gq x)‖ + ‖B.Aeta x (gη x)‖ + ‖B.A0 x (d x)‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖B.Aq x‖ * ‖gq x‖ + ‖B.Aeta x‖ * ‖gη x‖ + ‖B.A0 x‖ * ‖d x‖ :=
            add_le_add (add_le_add (ContinuousLinearMap.le_opNorm _ _)
              (ContinuousLinearMap.le_opNorm _ _)) (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ Γ * ‖gq x‖ + Γ * ‖gη x‖ + Γ * ‖d x‖ := by gcongr
        _ = Γ * (‖gq x‖ + ‖gη x‖ + ‖d x‖) := by ring
    have hgq : ‖gq x‖ ≤ ‖dqOf ε bε Sbε Qbε Ebε x‖ + ‖Qb0 x‖ := norm_sub_le _ _
    have hgη : ‖gη x‖ ≤ ‖Ebε x‖ + ‖Eb0 x‖ := norm_sub_le _ _
    have hd : ‖d x‖ ≤ ‖bε x‖ + ‖b0 x‖ := norm_sub_le _ _
    have hdq := norm_dqOf_le hL₁ hε0 hε1 bε Sbε Qbε Ebε hx
    have hQε := norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 Qbε hx
    have hEε := norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 Ebε hx
    have hQ0 := norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 Qb0 hx
    have hE0 := norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 Eb0 hx
    have hsum : ‖gq x‖ + ‖gη x‖ + ‖d x‖ ≤
        2 * Γ ^ 2 *
          ((‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) +
            (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖)) := by
      have h1Γ : 1 ≤ Γ ^ 2 := by nlinarith
      have hΓ2 : Γ ≤ Γ ^ 2 := by nlinarith
      nlinarith [norm_nonneg (bε x), norm_nonneg (Sbε x), norm_nonneg (sqrtS Qbε x),
        norm_nonneg (sqrtS Ebε x), norm_nonneg (b0 x), norm_nonneg (Sb0 x),
        norm_nonneg (sqrtS Qb0 x), norm_nonneg (sqrtS Eb0 x),
        mul_le_mul_of_nonneg_left hEε (by positivity : (0 : ℝ) ≤ Γ)]
    calc ‖B.apply d gq gη x‖ ≤ Γ * (‖gq x‖ + ‖gη x‖ + ‖d x‖) := hB
      _ ≤ Γ * (2 * Γ ^ 2 *
          ((‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) +
            (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖))) :=
          mul_le_mul_of_nonneg_left hsum (by linarith)
      _ = 2 * Γ ^ 3 *
          ((‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) +
            (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖)) := by ring
  · rw [obsOp_apply_eq_zero_of_notMem B _ _ _ hx, norm_zero]
    exact hRHS_nonneg

theorem eLpNorm_add4_norm_le {μ : Measure Coord} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {P1 P2 P3 P4 : CProf}
    (h1 : AEStronglyMeasurable P1 μ) (h2 : AEStronglyMeasurable P2 μ)
    (h3 : AEStronglyMeasurable P3 μ) (h4 : AEStronglyMeasurable P4 μ) :
    eLpNorm (fun x => ‖P1 x‖ + ‖P2 x‖ + ‖P3 x‖ + ‖P4 x‖) p μ ≤
      eLpNorm P1 p μ + eLpNorm P2 p μ + eLpNorm P3 p μ + eLpNorm P4 p μ := by
  have m1 := h1.norm
  have m2 := h2.norm
  have m3 := h3.norm
  have m4 := h4.norm
  have m12 := m1.add m2
  have m123 := m12.add m3
  calc eLpNorm (fun x => ‖P1 x‖ + ‖P2 x‖ + ‖P3 x‖ + ‖P4 x‖) p μ
      ≤ eLpNorm (fun x => ‖P1 x‖ + ‖P2 x‖ + ‖P3 x‖) p μ + eLpNorm (fun x => ‖P4 x‖) p μ :=
        eLpNorm_add_le m123 m4 hp
    _ ≤ (eLpNorm (fun x => ‖P1 x‖ + ‖P2 x‖) p μ + eLpNorm (fun x => ‖P3 x‖) p μ) +
          eLpNorm (fun x => ‖P4 x‖) p μ :=
        add_le_add (eLpNorm_add_le m12 m3 hp) le_rfl
    _ ≤ (eLpNorm (fun x => ‖P1 x‖) p μ + eLpNorm (fun x => ‖P2 x‖) p μ +
          eLpNorm (fun x => ‖P3 x‖) p μ) + eLpNorm (fun x => ‖P4 x‖) p μ :=
        add_le_add (add_le_add (eLpNorm_add_le m1 m2 hp) le_rfl) le_rfl
    _ = eLpNorm P1 p μ + eLpNorm P2 p μ + eLpNorm P3 p μ + eLpNorm P4 p μ := by
        simp only [eLpNorm_norm]

theorem graph_sum_le_of_graphBound {c r ν Γ Cg : ℝ} (hν : 0 < ν) (hνΓ : ν⁻¹ ≤ Γ) (hΓ1 : 1 ≤ Γ)
    {F b Sb Qb Eb : CProf}
    (hg : hNorm c r b + hNorm c r Sb +
        ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) ≤
      ENNReal.ofReal Cg * hNorm c r F) :
    hNorm c r b + hNorm c r Sb + hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb) ≤
      ENNReal.ofReal Γ * (ENNReal.ofReal Cg * hNorm c r F) := by
  have h1 : 1 ≤ Real.sqrt ν * Γ := sqrt_inv_bound hν hνΓ hΓ1
  have hΓ_ge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Γ := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hΓ1
  have hQE : hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb) ≤
      ENNReal.ofReal Γ *
        (ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) := by
    calc hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)
        = ENNReal.ofReal 1 * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) := by simp
      _ ≤ ENNReal.ofReal (Γ * Real.sqrt ν) *
            (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) := by
          gcongr
          linarith
      _ = ENNReal.ofReal Γ *
            (ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) := by
          rw [ENNReal.ofReal_mul (by linarith), mul_assoc]
  have hbS : hNorm c r b + hNorm c r Sb ≤ ENNReal.ofReal Γ * (hNorm c r b + hNorm c r Sb) :=
    le_mul_of_one_le_left zero_le hΓ_ge
  calc hNorm c r b + hNorm c r Sb + hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)
      = (hNorm c r b + hNorm c r Sb) + (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) := by
        rw [add_assoc]
    _ ≤ ENNReal.ofReal Γ * (hNorm c r b + hNorm c r Sb) +
          ENNReal.ofReal Γ *
            (ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) :=
        add_le_add hbS hQE
    _ = ENNReal.ofReal Γ *
          (hNorm c r b + hNorm c r Sb +
            ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) := by
        rw [← mul_add]
    _ ≤ ENNReal.ofReal Γ * (ENNReal.ofReal Cg * hNorm c r F) := by gcongr

/-- Uniform polynomial bound (`θ = 0`) for `B(b_ε - b_0)` in `H_r` for any `1 < r < 3`. -/
theorem compRate_zero (r : ℝ) (hr1 : 1 < r) (hr3 : r < 3) :
    CompRate r ((3 / r - 1) / 2) 0 := by
  obtain ⟨Cp, hCp, hphys⟩ := phys_graph_poly r hr1 hr3
  obtain ⟨Cf, hCf, hflat⟩ := flat_graph_poly r hr1 hr3
  refine ⟨6, 2 * (Cp + Cf), by positivity, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ
    B ε hε0 hε1 hP F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
  obtain ⟨Sbε, Qbε, Ebε, hSε, hQε, hEε, mSε, mQε, mEε, hgε⟩ :=
    hphys Γ ν c ε μ hΓ1 hμΓ hgap hν hc hε0 hε1 hP F bε hF hbε_resp
  obtain ⟨Sb0, Qb0, Eb0, hS0, hQ0, hE0, mS0, mQ0, mE0, hg0⟩ :=
    hflat Γ ν c μ hΓ1 hμΓ hgap hν hc F b0 hF hb0_resp hb0_class
  have hDbε : HasWeakVec vQ0 dZero bε (dqOf ε bε Sbε Qbε Ebε) :=
    hasWeakVec_dqOf ε hSε hQε hEε
  refine ⟨dqOf ε bε Sbε Qbε Ebε - Qb0, Ebε - Eb0,
    flatCls_hasWeakVec_sub hDbε hQ0, flatCls_hasWeakVec_sub hEε hE0, ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr1.le
  set fε : Coord → ℝ := fun x => ‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖
  set f0 : Coord → ℝ := fun x => ‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖
  have mfε : AEStronglyMeasurable fε (hMeas c r) :=
    ((hbε_in.meas.norm.add mSε.norm).add mQε.norm).add mEε.norm
  have mf0 : AEStronglyMeasurable f0 (hMeas c r) :=
    ((hb0_class.inHr.meas.norm.add mS0.norm).add mQ0.norm).add mE0.norm
  have hmono : hNorm c r (B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0)) ≤
      eLpNorm ((2 * Γ ^ 3) • (fε + f0)) (ENNReal.ofReal r) (hMeas c r) := by
    apply eLpNorm_mono_real
    intro x
    simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul, fε, f0] using
      obsOp_pointwise_bound hσ hσΓ hL₁ hΓ1 hε0 hε1 B bε Sbε Qbε Ebε b0 Sb0 Qb0 Eb0 x
  have h2Γ3 : 0 ≤ 2 * Γ ^ 3 := by positivity
  have hsmul : eLpNorm ((2 * Γ ^ 3) • (fε + f0)) (ENNReal.ofReal r) (hMeas c r) ≤
      ENNReal.ofReal (2 * Γ ^ 3) *
        (eLpNorm fε (ENNReal.ofReal r) (hMeas c r) +
          eLpNorm f0 (ENNReal.ofReal r) (hMeas c r)) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal h2Γ3]
    gcongr
    exact eLpNorm_add_le mfε mf0 hp1
  have h4ε : eLpNorm fε (ENNReal.ofReal r) (hMeas c r) ≤
      ENNReal.ofReal Γ * (ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c r F) :=
    (eLpNorm_add4_norm_le hp1 hbε_in.meas mSε mQε mEε).trans
      (graph_sum_le_of_graphBound hν hνΓ hΓ1 hgε)
  have h40 : eLpNorm f0 (ENNReal.ofReal r) (hMeas c r) ≤
      ENNReal.ofReal Γ * (ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c r F) :=
    (eLpNorm_add4_norm_le hp1 hb0_class.inHr.meas mS0 mQ0 mE0).trans
      (graph_sum_le_of_graphBound hν hνΓ hΓ1 hg0)
  have hCp0 : 0 ≤ Cp * Γ ^ 2 := by positivity
  have hCf0 : 0 ≤ Cf * Γ ^ 2 := by positivity
  have hΓ0 : 0 ≤ Γ := by linarith
  calc hNorm c r (B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0))
      ≤ ENNReal.ofReal (2 * Γ ^ 3) *
          (eLpNorm fε (ENNReal.ofReal r) (hMeas c r) +
            eLpNorm f0 (ENNReal.ofReal r) (hMeas c r)) := hmono.trans hsmul
    _ ≤ ENNReal.ofReal (2 * Γ ^ 3) *
          (ENNReal.ofReal Γ * (ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c r F) +
            ENNReal.ofReal Γ * (ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c r F)) := by
        gcongr
    _ = ENNReal.ofReal (2 * (Cp + Cf) * Γ ^ 6 * ε ^ (0 : ℝ)) * hNorm c r F := by
        rw [Real.rpow_zero, mul_one, ← mul_assoc (ENNReal.ofReal Γ),
          ← ENNReal.ofReal_mul hΓ0, ← mul_assoc (ENNReal.ofReal Γ),
          ← ENNReal.ofReal_mul hΓ0, ← add_mul,
          ← ENNReal.ofReal_add (mul_nonneg hΓ0 hCp0) (mul_nonneg hΓ0 hCf0),
          ← mul_assoc, ← ENNReal.ofReal_mul h2Γ3]
        congr 2
        ring

/-- **`PartII-b:T17` (`lp_endpoint_bound`)** (SP 1992-1996): uniform polynomial `H_{23/8}` bound
for `B(T_ε - T_0)` at `r = bgr = 23/8`, shift gap `1/46`, rate exponent `θ = 0`. -/
theorem lp_endpoint_bound : UnforcedLeray.Short.IIb.CompRate UnforcedLeray.Short.IIb.bgr (1 / 46) 0 := by
  have hr1 : (1 : ℝ) < bgr := by norm_num [bgr]
  have hr3 : bgr < (3 : ℝ) := by norm_num [bgr]
  have hgap : (3 / bgr - 1) / 2 = (1 / 46 : ℝ) := by norm_num [bgr]
  rw [← hgap]
  exact compRate_zero bgr hr1 hr3

end UnforcedLeray.Short.IIb

end
