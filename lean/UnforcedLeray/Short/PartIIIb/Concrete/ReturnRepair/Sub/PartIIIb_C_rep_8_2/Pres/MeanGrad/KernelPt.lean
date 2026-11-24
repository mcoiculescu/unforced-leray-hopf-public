import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.XJetOff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanSupport
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.Scale

/-!
# The pointwise kernel bound `MeanJetKernelPt` (`PartIII-b:C/rep/8/2/pres/5/4`)

Source of record: `shorter-proof-2026-11-02.tex` lines 5380-5387, 5400-5413, 4161-4166, 5267-5268.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem kp_meanJetDens_zero {X Y : Space → Space} {y : Space}
    (hX : X =ᶠ[𝓝 y] fun _ => 0) (hY : Y =ᶠ[𝓝 y] fun _ => 0) :
    meanJetDens X Y y = 0 := by
  unfold meanJetDens
  rw [ms_fderiv_eq_zero hY]
  simp [ms_physPd_zero hX, ms_physPd2_zero hX]

/-- Young support: the mean jet density vanishes for `1/ν < s`. -/
theorem kp_zero_case (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) (hν : 0 < ν)
    (hε : 0 < ε) (hχ : IsStreamCutoff χy) (τ : ℝ) (p : Chart) (hp : 1 / ν < p.1) :
    meanJetDens (Xmean c ν ε μ χo χy M τ) (Ymean c ν ε μ χo χy M τ)
        (NearInst.chartY ε⁻¹ p) = 0 := by
  have hs : 0 < p.1 := lt_trans (one_div_pos.2 hν) hp
  have hεne : ε ≠ 0 := hε.ne'
  set y0 : Space := NearInst.chartY ε⁻¹ p with hy0
  have hdef : WithLp.ofLp y0 = ![ε⁻¹ / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] := by
    simp [hy0, NearInst.chartY]
  have hc : cylR (WithLp.ofLp y0) = ε⁻¹ / Real.sqrt p.1 := by
    rw [hdef]
    unfold cylR
    have hnn : 0 ≤ ε⁻¹ / Real.sqrt p.1 :=
      div_nonneg (inv_nonneg.2 hε.le) (Real.sqrt_nonneg _)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (ε⁻¹ / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (ε⁻¹ / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq hnn
  have hcyl : (ε * cylR (WithLp.ofLp y0)) ^ 2 < ν := by
    rw [hc]
    have h1 : ε * (ε⁻¹ / Real.sqrt p.1) = (Real.sqrt p.1)⁻¹ := by
      field_simp
    rw [h1, inv_pow, Real.sq_sqrt hs.le]
    exact inv_lt_of_inv_lt₀ hν (by simpa [one_div] using hp)
  have hev : ∀ᶠ y' in 𝓝 y0, (ε * cylR (WithLp.ofLp y')) ^ 2 < ν := by
    have hc' : ContinuousAt (fun y' : Space => (ε * cylR (WithLp.ofLp y')) ^ 2) y0 := by
      apply Continuous.continuousAt
      unfold cylR
      fun_prop
    exact hc'.eventually_lt continuousAt_const hcyl
  have hX : ∀ τ' : ℝ, (Xmean c ν ε μ χo χy M τ') =ᶠ[𝓝 y0] fun _ => 0 := by
    intro τ'
    filter_upwards [hev] with y' hy'
    show WithLp.toLp 2 (Xmt c ν ε μ χo χy M (WithLp.ofLp y')) = 0
    rw [young_xmt_zero_open M hε hχ hy']
    simp
  have hY : ∀ τ' : ℝ, (Ymean c ν ε μ χo χy M τ') =ᶠ[𝓝 y0] fun _ => 0 := by
    intro τ'
    filter_upwards [hev] with y' hy'
    show WithLp.toLp 2 (YmtFun c ν ε μ χo χy M (WithLp.ofLp y')) = 0
    rw [ms_ymt_zero_of_open M hε hχ _ hy']
    simp
  exact kp_meanJetDens_zero (hX τ) (hY τ)

/-- `(t⁻¹)^(-(2+n)) = t^(n+2)` for `t > 0`. -/
theorem kp_pow (t : ℝ) (ht : 0 < t) (n : ℕ) :
    (t⁻¹) ^ (-(2 : ℝ) - (n : ℝ)) = t ^ (n + 2) := by
  rw [Real.inv_rpow ht.le, show (-(2 : ℝ) - (n : ℝ)) = -((n + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg ht.le, Real.rpow_natCast, inv_inv]

/-- Core inequality: for `0 ≤ v ≤ 1`, `ν t ≤ 1`. -/
theorem kp_core (t v ν : ℝ) (ht : 0 < t) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hν : 0 < ν)
    (hν1 : ν ≤ 1) (hνt : ν * t ≤ 1) :
    t ^ 5 * v ^ 2 + t ^ 6 * v ^ 2 + t ^ 5 * v + ν * t ^ 7 * v ^ 2 ≤ 4 * ν⁻¹ * t ^ 5 * v := by
  have ht5 : 0 ≤ t ^ 5 := pow_nonneg ht.le 5
  have hA : 0 ≤ t ^ 5 * v := mul_nonneg ht5 hv0
  have hνv : ν * v ≤ 1 := by nlinarith [mul_nonneg hν.le hv0]
  have hv2 : v ^ 2 ≤ v := by nlinarith
  have h1 : ν * (t ^ 5 * v ^ 2) ≤ t ^ 5 * v := by
    calc ν * (t ^ 5 * v ^ 2) = (t ^ 5 * v) * (ν * v) := by ring
      _ ≤ (t ^ 5 * v) * 1 := mul_le_mul_of_nonneg_left hνv hA
      _ = t ^ 5 * v := mul_one _
  have h2 : ν * (t ^ 6 * v ^ 2) ≤ t ^ 5 * v := by
    have hB : 0 ≤ t ^ 5 * v ^ 2 := mul_nonneg ht5 (sq_nonneg v)
    calc ν * (t ^ 6 * v ^ 2) = (ν * t) * (t ^ 5 * v ^ 2) := by ring
      _ ≤ 1 * (t ^ 5 * v ^ 2) := mul_le_mul_of_nonneg_right hνt hB
      _ = t ^ 5 * v ^ 2 := one_mul _
      _ ≤ t ^ 5 * v := mul_le_mul_of_nonneg_left hv2 ht5
  have h3 : ν * (t ^ 5 * v) ≤ t ^ 5 * v := mul_le_of_le_one_left hA hν1
  have h4 : ν * (ν * t ^ 7 * v ^ 2) ≤ t ^ 5 * v := by
    have hB : 0 ≤ t ^ 5 * v ^ 2 := mul_nonneg ht5 (sq_nonneg v)
    have hY : 0 ≤ (ν * t) * (t ^ 5 * v ^ 2) := mul_nonneg (mul_nonneg hν.le ht.le) hB
    calc ν * (ν * t ^ 7 * v ^ 2) = (ν * t) * ((ν * t) * (t ^ 5 * v ^ 2)) := by ring
      _ ≤ 1 * ((ν * t) * (t ^ 5 * v ^ 2)) := mul_le_mul_of_nonneg_right hνt hY
      _ = (ν * t) * (t ^ 5 * v ^ 2) := one_mul _
      _ ≤ 1 * (t ^ 5 * v ^ 2) := mul_le_mul_of_nonneg_right hνt hB
      _ = t ^ 5 * v ^ 2 := one_mul _
      _ ≤ t ^ 5 * v := mul_le_mul_of_nonneg_left hv2 ht5
  have hsum : (t ^ 5 * v ^ 2 + t ^ 6 * v ^ 2 + t ^ 5 * v + ν * t ^ 7 * v ^ 2) * ν
      = ν * (t ^ 5 * v ^ 2) + ν * (t ^ 6 * v ^ 2) + ν * (t ^ 5 * v) + ν * (ν * t ^ 7 * v ^ 2) := by
    ring
  have key : (t ^ 5 * v ^ 2 + t ^ 6 * v ^ 2 + t ^ 5 * v + ν * t ^ 7 * v ^ 2) * ν
      ≤ 4 * (t ^ 5 * v) := by
    linarith [hsum, h1, h2, h3, h4]
  have hr : 4 * ν⁻¹ * t ^ 5 * v = (4 * (t ^ 5 * v)) / ν := by ring
  rw [hr, le_div_iff₀ hν]
  exact key

/-- The final algebra of the young range. -/
theorem kp_final (t u ν ε K N : ℝ) (ht : 0 < t) (hu1 : 1 ≤ u) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hνt : ν * t ≤ 1) (hε : 0 < ε) (hK : 0 ≤ K) (hN : 0 ≤ N) :
    100 * ε ^ 3 * (K * (t ^ 3 * ((t⁻¹ * u) ^ 2)⁻¹ * N)
        + (1 + t⁻¹ * u) * (K * (t ^ 4 * ((t⁻¹ * u) ^ 2)⁻¹ * N))
        + ν * (K * (t ^ 5 * ((t⁻¹ * u) ^ 2)⁻¹ * N)))
      ≤ 400 * K * ν⁻¹ ^ 1 * (ε ^ 3 * t ^ 5 * u⁻¹) * N := by
  have hu0 : 0 < u := by linarith
  have huv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0.ne'
  have hv0 : 0 ≤ u⁻¹ := inv_nonneg.2 hu0.le
  have hv1 : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
  have htne : t ≠ 0 := ht.ne'
  have hue : u ≠ 0 := hu0.ne'
  have hE : ((t⁻¹ * u) ^ 2)⁻¹ = t ^ 2 * (u⁻¹) ^ 2 := by
    field_simp
  have hT2 : (1 + t⁻¹ * u) * (t ^ 4 * (t ^ 2 * (u⁻¹) ^ 2))
      = t ^ 6 * (u⁻¹) ^ 2 + t ^ 5 * u⁻¹ := by
    have h : t⁻¹ * u * (t ^ 6 * (u⁻¹) ^ 2) = t ^ 5 * u⁻¹ := by
      calc t⁻¹ * u * (t ^ 6 * (u⁻¹) ^ 2) = t ^ 5 * (u * u⁻¹) * u⁻¹ := by
            field_simp
        _ = t ^ 5 * u⁻¹ := by rw [huv, mul_one]
    linear_combination h
  have hsumeq : K * (t ^ 3 * ((t⁻¹ * u) ^ 2)⁻¹ * N)
        + (1 + t⁻¹ * u) * (K * (t ^ 4 * ((t⁻¹ * u) ^ 2)⁻¹ * N))
        + ν * (K * (t ^ 5 * ((t⁻¹ * u) ^ 2)⁻¹ * N))
      = K * N * (t ^ 5 * (u⁻¹) ^ 2 + t ^ 6 * (u⁻¹) ^ 2 + t ^ 5 * u⁻¹
          + ν * t ^ 7 * (u⁻¹) ^ 2) := by
    rw [hE]
    linear_combination (K * N) * hT2
  have hQ := kp_core t (u⁻¹) ν ht hv0 hv1 hν hν1 hνt
  have hKN : 0 ≤ K * N := mul_nonneg hK hN
  have h100 : 0 ≤ 100 * ε ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hε.le 3)
  rw [hsumeq]
  calc 100 * ε ^ 3 * (K * N * (t ^ 5 * (u⁻¹) ^ 2 + t ^ 6 * (u⁻¹) ^ 2 + t ^ 5 * u⁻¹
          + ν * t ^ 7 * (u⁻¹) ^ 2))
      ≤ 100 * ε ^ 3 * (K * N * (4 * ν⁻¹ * t ^ 5 * u⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hKN) h100
    _ = 400 * K * ν⁻¹ ^ 1 * (ε ^ 3 * t ^ 5 * u⁻¹) * N := by ring

/-- **The pointwise kernel bound** (`PartIII-b:C/rep/8/2/pres/5/4`). -/
theorem meanJetKernelPt (χo χy : ℝ → ℝ) : MeanJetKernelPt χo χy := by
  obtain ⟨C0, hC0⟩ := xmtJetOff_of (newtonVCutBound χo) (scXJetOff χy)
  refine ⟨400 * |C0|, 1, ?_⟩
  intro c ν ε μ hL hε1 M hM τ p hp
  have hν : 0 < ν := hL.nu_pos
  have hε : 0 < ε := hL.eps_pos
  have hN : 0 ≤ oldN0cut c ν χo M := oldN0cut_nonneg c ν hν hL.chiO M
  by_cases hcond : 1 / ν < p.1
  · have hz := kp_zero_case c ν ε μ χo χy M hν hε hL.chiY τ p hcond
    have hyW : youngJetWeight ν ε p = 0 := by
      unfold youngJetWeight
      rw [if_neg (fun h => absurd h.2 (not_le.2 hcond))]
    rw [hz, hyW]
    simp
  · push_neg at hcond
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.sqrt p.1 := ⟨_, rfl⟩
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.sqrt (1 + (ε * p.2.2) ^ 2) := ⟨_, rfl⟩
    have ht : 0 < t := by rw [htdef]; exact Real.sqrt_pos.2 hp
    have ht2 : t ^ 2 = p.1 := by rw [htdef]; exact Real.sq_sqrt hp.le
    have hu0 : 0 ≤ u := by rw [hudef]; exact Real.sqrt_nonneg _
    have hu2 : u ^ 2 = 1 + (ε * p.2.2) ^ 2 := by
      rw [hudef]; exact Real.sq_sqrt (by positivity)
    have hu1 : 1 ≤ u := by nlinarith [sq_nonneg (ε * p.2.2)]
    have hεne : ε ≠ 0 := hε.ne'
    have htne : t ≠ 0 := ht.ne'
    have hνs : ν * p.1 ≤ 1 := by
      have h := (le_div_iff₀ hν).1 hcond
      linarith [mul_comm ν p.1]
    have hνt : ν * t ≤ 1 := by
      have h1 : (ν * t) ^ 2 ≤ 1 := by
        have e : (ν * t) ^ 2 = ν ^ 2 * p.1 := by rw [← ht2]; ring
        rw [e]
        nlinarith [mul_nonneg (mul_nonneg hν.le (sub_nonneg.2 hL.nu_le)) hp.le]
      nlinarith [mul_nonneg hν.le ht.le]
    set y0 : Space := NearInst.chartY ε⁻¹ p with hy0
    have hdef : WithLp.ofLp y0 = ![ε⁻¹ / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] := by
      simp [hy0, NearInst.chartY]
    have hw : ε • WithLp.ofLp y0 = ![t⁻¹, 0, ε * p.2.2 * t⁻¹] := by
      rw [hdef, htdef]
      funext i
      fin_cases i <;> simp <;> field_simp
    have hcylw : cylR (ε • WithLp.ofLp y0) = t⁻¹ := by
      rw [hw]
      unfold cylR
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show (t⁻¹) ^ 2 + (0 : ℝ) ^ 2 = (t⁻¹) ^ 2 by ring]
      exact Real.sqrt_sq (inv_nonneg.2 ht.le)
    have heucw : eucSq (ε • WithLp.ofLp y0) = (t⁻¹ * u) ^ 2 := by
      rw [hw, mul_pow, hu2]
      unfold eucSq
      simp [Fin.sum_univ_three]
      ring
    have hνcyl : ν ≤ cylR (ε • WithLp.ofLp y0) ^ 2 := by
      rw [hcylw, inv_pow, ht2]
      rw [le_inv_comm₀ hν hp, ← one_div]
      exact hcond
    have hL1 : LHyp c ν 1 μ χo χy :=
      ⟨hL.c_pos, hL.nu_pos, hL.nu_le, one_pos, hL.mu_pos, hL.mu_lt, hL.chiO, hL.chiY⟩
    have b1 := hC0 c ν μ hL1 M hM _ hνcyl 1 (by norm_num)
    have b2 := hC0 c ν μ hL1 M hM _ hνcyl 2 (by norm_num)
    have b3 := hC0 c ν μ hL1 M hM _ hνcyl 3 (by norm_num)
    have e1 : (t⁻¹) ^ (-(2 : ℝ) - ((1 : ℕ) : ℝ)) = t ^ 3 := by
      rw [kp_pow t ht 1] <;> norm_num
    have e2 : (t⁻¹) ^ (-(2 : ℝ) - ((2 : ℕ) : ℝ)) = t ^ 4 := by
      rw [kp_pow t ht 2] <;> norm_num
    have e3 : (t⁻¹) ^ (-(2 : ℝ) - ((3 : ℕ) : ℝ)) = t ^ 5 := by
      rw [kp_pow t ht 3] <;> norm_num
    rw [hcylw, heucw, e1] at b1
    rw [hcylw, heucw, e2] at b2
    rw [hcylw, heucw, e3] at b3
    have hX1 : ContDiff ℝ 3 (Xmt c ν 1 μ χo χy M) :=
      (xmtSmooth c ν 1 μ χo χy hL1 M hM).of_le (by norm_num)
    have hscale := meanJetScaleBound (Xmt c ν 1 μ χo χy M) ε ν μ hX1 hε hε1 hν.le
      hL.mu_pos.le hL.mu_lt.le y0
    rw [heucw, Real.sqrt_sq (mul_nonneg (inv_nonneg.2 ht.le) hu0)] at hscale
    have hXeq : Xmean c ν ε μ χo χy M τ
        = fun y' => WithLp.toLp 2 (JetClockCore.Xsc (Xmt c ν 1 μ χo χy M) ε (WithLp.ofLp y')) := by
      funext y'
      simp only [Xmean, Scale.Xmt_smul hε, JetClockCore.Xsc]
    have hYeq : Ymean c ν ε μ χo χy M τ
        = fun y' => WithLp.toLp 2 (JetClockCore.Yf (JetClockCore.Xsc (Xmt c ν 1 μ χo χy M) ε) ν μ
            (WithLp.ofLp y')) := by
      funext y'
      simp only [Ymean, YmtFun, JetClockCore.Yf, Scale.Xmt_smul hε]
      rfl
    have hpow5 : p.1 ^ (5 / 2 : ℝ) = t ^ 5 := by
      rw [htdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num
    have hpowu : (1 + (ε * p.2.2) ^ 2) ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
      rw [hudef, Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
    rw [hXeq, hYeq, youngJetWeight, if_pos ⟨hp, hcond⟩, hpow5, hpowu]
    have hX0 : 0 ≤ t ^ 3 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M :=
      mul_nonneg (mul_nonneg (pow_nonneg ht.le 3) (inv_nonneg.2 (sq_nonneg _))) hN
    have hX2 : 0 ≤ t ^ 4 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M :=
      mul_nonneg (mul_nonneg (pow_nonneg ht.le 4) (inv_nonneg.2 (sq_nonneg _))) hN
    have hX3 : 0 ≤ t ^ 5 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M :=
      mul_nonneg (mul_nonneg (pow_nonneg ht.le 5) (inv_nonneg.2 (sq_nonneg _))) hN
    have hb1' := mul_le_mul_of_nonneg_right (le_abs_self C0) hX0
    have hb2' := mul_le_mul_of_nonneg_right (le_abs_self C0) hX2
    have hb3' := mul_le_mul_of_nonneg_right (le_abs_self C0) hX3
    have hd1 : ‖iteratedFDeriv ℝ 1 (Xmt c ν 1 μ χo χy M) (ε • WithLp.ofLp y0)‖
        ≤ |C0| * (t ^ 3 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M) := by
      linarith [b1, hb1']
    have hd2 : ‖iteratedFDeriv ℝ 2 (Xmt c ν 1 μ χo χy M) (ε • WithLp.ofLp y0)‖
        ≤ |C0| * (t ^ 4 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M) := by
      linarith [b2, hb2']
    have hd3 : ‖iteratedFDeriv ℝ 3 (Xmt c ν 1 μ χo χy M) (ε • WithLp.ofLp y0)‖
        ≤ |C0| * (t ^ 5 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M) := by
      linarith [b3, hb3']
    have hcoef : 0 ≤ 1 + t⁻¹ * u := by
      have := mul_nonneg (inv_nonneg.2 ht.le) hu0
      linarith
    have hm2 := mul_le_mul_of_nonneg_left hd2 hcoef
    have hm3 := mul_le_mul_of_nonneg_left hd3 hν.le
    have hsum : ‖iteratedFDeriv ℝ 1 (Xmt c ν 1 μ χo χy M) (ε • WithLp.ofLp y0)‖
        + (1 + t⁻¹ * u) * ‖iteratedFDeriv ℝ 2 (Xmt c ν 1 μ χo χy M) (ε • WithLp.ofLp y0)‖
        + ν * ‖iteratedFDeriv ℝ 3 (Xmt c ν 1 μ χo χy M) (ε • WithLp.ofLp y0)‖
        ≤ |C0| * (t ^ 3 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M)
          + (1 + t⁻¹ * u) * (|C0| * (t ^ 4 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M))
          + ν * (|C0| * (t ^ 5 * ((t⁻¹ * u) ^ 2)⁻¹ * oldN0cut c ν χo M)) := by
      linarith [hd1, hm2, hm3]
    have h100 : 0 ≤ 100 * ε ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hε.le 3)
    exact le_trans hscale (le_trans (mul_le_mul_of_nonneg_left hsum h100)
      (kp_final t u ν ε (|C0|) (oldN0cut c ν χo M) ht hu1 hν hL.nu_le hνt hε (abs_nonneg _) hN))
