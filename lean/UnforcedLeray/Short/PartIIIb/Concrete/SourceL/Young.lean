import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Smooth

/-!
# Part III-b, task `PartIII-b:C/srcL/13` (`sourceLYoung`)

`𝓛T(s) = 0` for `s ≥ 1/ν`.  The stream cutoff `χ_y` vanishes on `{(ε|y'|)² < ν}`, so `X^mt` vanishes
on that open set (`young_xmt_zero_open`).  For `s > 1/ν` the receiver `(ε⁻¹/√s,0,0)` lies in this set,
so `D X^mt = 0` there; at `s = 1/ν` the derivative is the limit of the values from `s' ↓ 1/ν`.
Source 4799 of `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The stream cutoff vanishes wherever `(ε r)² < ν`. -/
theorem young_chiYr_zero {ν ε : ℝ} (χy : ℝ → ℝ) (hY : IsStreamCutoff χy) (hε : 0 < ε) {r : ℝ}
    (hr : (ε * r) ^ 2 < ν) : chiYr ν ε χy r = 0 := by
  by_cases h0 : r = 0
  · simp [chiYr, h0]
  · have hne : ε * r ≠ 0 := mul_ne_zero hε.ne' h0
    have hpos : 0 < (ε * r) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    unfold chiYr
    rw [if_neg h0]
    exact hY.zero _ ((one_le_div hpos).2 hr.le)

/-- The derivative of the stream cutoff vanishes wherever `(ε r)² < ν`. -/
theorem young_chiYr_deriv_zero {ν ε : ℝ} (χy : ℝ → ℝ) (hY : IsStreamCutoff χy) (hε : 0 < ε) {r : ℝ}
    (hr : (ε * r) ^ 2 < ν) : deriv (chiYr ν ε χy) r = 0 := by
  have hopen : IsOpen {r' : ℝ | (ε * r') ^ 2 < ν} := isOpen_lt (by fun_prop) continuous_const
  have hev : chiYr ν ε χy =ᶠ[nhds r] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hr) fun r' hr' =>
      young_chiYr_zero χy hY hε (r := r') hr'
  rw [hev.deriv_eq]
  exact deriv_const r 0

/-- `X^mt` vanishes on the open set `{(ε|y'|)² < ν}`. -/
theorem young_xmt_zero_open {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (M : Chart → Mat3) (hε : 0 < ε)
    (hY : IsStreamCutoff χy) {y : Vec3} (hy : (ε * cylR y) ^ 2 < ν) :
    Xmt c ν ε μ χo χy M y = 0 := by
  unfold Xmt streamCut
  rw [young_chiYr_zero χy hY hε hy, young_chiYr_deriv_zero χy hY hε hy]
  simp

theorem young_isOpen_U0 {ε ν : ℝ} : IsOpen {y : Vec3 | (ε * cylR y) ^ 2 < ν} := by
  unfold cylR
  exact isOpen_lt (by fun_prop) continuous_const

/-- The receiver point `(ε⁻¹/√s, 0, 0)` has `(ε |y'|)² = 1/s`. -/
theorem young_cylR_recv {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    (ε * cylR (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) ^ 2 = 1 / s := by
  have hpos : 0 < ε⁻¹ / Real.sqrt s := div_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hs)
  have hc : cylR (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) = ε⁻¹ / Real.sqrt s := by
    unfold cylR
    have h0 : (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) 0 = ε⁻¹ / Real.sqrt s := rfl
    have h1 : (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) 1 = 0 := rfl
    rw [h0, h1, show (ε⁻¹ / Real.sqrt s) ^ 2 + (0 : ℝ) ^ 2 = (ε⁻¹ / Real.sqrt s) ^ 2 by ring]
    exact Real.sqrt_sq hpos.le
  have key : ε * (ε⁻¹ / Real.sqrt s) = 1 / Real.sqrt s := by
    rw [← mul_div_assoc, mul_inv_cancel₀ hε.ne']
  rw [hc, key, div_pow, one_pow, Real.sq_sqrt hs.le]

/-- For `s > 1/ν` the derivative of `X^mt` at the receiver vanishes. -/
theorem young_fderiv_zero_gt {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (M : Chart → Mat3) (hε : 0 < ε)
    (hY : IsStreamCutoff χy) (hν : 0 < ν) {s : ℝ} (hs : 1 / ν < s) :
    fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] = 0 := by
  have hspos : 0 < s := lt_trans (one_div_pos.2 hν) hs
  have hlt : 1 < s * ν := (div_lt_iff₀ hν).1 hs
  have hmem : (ε * cylR (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) ^ 2 < ν := by
    rw [young_cylR_recv hε hspos]
    exact (div_lt_iff₀ hspos).2 (by linarith [mul_comm ν s])
  have hev : Xmt c ν ε μ χo χy M =ᶠ[nhds (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)]
      fun _ => (0 : Vec3) :=
    Filter.eventually_of_mem
      (young_isOpen_U0 (ε := ε) (ν := ν) |>.mem_nhds (show _ ∈ {y : Vec3 | (ε * cylR y) ^ 2 < ν} from hmem))
      fun y hy => young_xmt_zero_open M hε hY (y := y) hy
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

/-- `𝓛T` vanishes for `s ≥ 1/ν`. -/
theorem sourceLYoung (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) :
    SourceLYoung c mZ ρb γ ν ε μ χo χy := by
  intro h hmZ hγ T s hs
  have hνpos : 0 < 1 / ν := one_div_pos.2 h.nu_pos
  have hspos : 0 < s := lt_of_lt_of_le hνpos hs
  obtain ⟨C, k, hC⟩ := sourceLN0 mZ γ hmZ hγ
  have hfin : OldThinFinite c ν (thinRep T) := (hC c ν ρb h.c_pos h.nu_pos h.nu_le T).1
  have hX : ContDiff ℝ 7 (Xmt c ν ε μ χo χy (thinRep T)) :=
    xmtSmooth c ν ε μ χo χy h (thinRep T) hfin
  have hD6 : ContDiff ℝ 6 (fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))) :=
    hX.fderiv_right (by norm_num)
  have hcont : Continuous (fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))) := hD6.continuous
  have hD0 : fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) ![ε⁻¹ / Real.sqrt s, 0, 0] = 0 := by
    rcases eq_or_lt_of_le hs with heq | hgt
    · rw [← heq]
      have hyc : ContinuousAt (fun s' : ℝ => (![ε⁻¹ / Real.sqrt s', 0, 0] : Vec3)) (1 / ν) :=
        (contDiffOn_recvPt ε).continuousOn.continuousAt (Ioi_mem_nhds hνpos)
      have hT1 : Filter.Tendsto (fun s' : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))
          (![ε⁻¹ / Real.sqrt s', 0, 0] : Vec3)) (nhds (1 / ν))
          (nhds (fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) (![ε⁻¹ / Real.sqrt (1 / ν), 0, 0] : Vec3))) :=
        (hcont.tendsto _).comp hyc.tendsto
      have hT2 : Filter.Tendsto (fun s' : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))
          (![ε⁻¹ / Real.sqrt s', 0, 0] : Vec3)) (nhdsWithin (1 / ν) (Ioi (1 / ν)))
          (nhds (fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) (![ε⁻¹ / Real.sqrt (1 / ν), 0, 0] : Vec3))) :=
        hT1.mono_left nhdsWithin_le_nhds
      have hT3 : Filter.Tendsto (fun s' : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))
          (![ε⁻¹ / Real.sqrt s', 0, 0] : Vec3)) (nhdsWithin (1 / ν) (Ioi (1 / ν)))
          (nhds (0 : Vec3 →L[ℝ] Vec3)) := by
        refine tendsto_const_nhds.congr' ?_
        exact eventually_mem_nhdsWithin.mono fun s' hs' =>
          (young_fderiv_zero_gt (c := c) (χo := χo) (μ := μ) (thinRep T) h.eps_pos h.chiY h.nu_pos hs').symm
      exact tendsto_nhds_unique hT2 hT3
    · exact young_fderiv_zero_gt (c := c) (χo := χo) (μ := μ) (thinRep T) h.eps_pos h.chiY h.nu_pos hgt
  unfold LjFun
  show Lpt c ν ε μ χo χy (thinRep T) s = 0
  unfold Lpt
  rw [if_pos hspos, hD0]
  funext i j
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
