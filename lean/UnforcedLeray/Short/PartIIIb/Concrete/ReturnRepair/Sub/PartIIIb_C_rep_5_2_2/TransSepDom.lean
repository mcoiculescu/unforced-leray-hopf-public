import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransVanishOff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCutPoint
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.SepX0Dom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4

/-!
# `PartIII-b:C/rep/5/2/2/12` : pointwise domination of both stream transitions

Source `the November 2 reference manuscript` 5312-5316 (the transitions are
supported on `0.8/ν < s < 1/ν`), 3684-3712 (cutoff correction and commutators), 4176-4214
(outward primitive, the second transition).

Composition: off the annulus `streamAnn` the transitions vanish (`transVanishOff`); on it,
`sepTrans = streamCorr + sepComm`, the stream correction is bounded by `transCutPoint` and
`outPrimPointwise`, the commutator by `transCommPoint`, `sepX0Dom` and `outPrimPointwise`, and the
constant `ν⁻¹` absorbs the extra `L⁻¹ sepDom₀₀` term (`L = R√ν ≥ ν`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Left multiplication is monotone (local form of `tsd_mulL`). -/
theorem tsd_mulL {b c : ENNReal} (h : b ≤ c) (x : ENNReal) : x * b ≤ x * c :=
  mul_le_mul' le_rfl h

/-- Right multiplication is monotone (local form of `tsd_mulR`). -/
theorem tsd_mulR {b c : ENNReal} (h : b ≤ c) (x : ENNReal) : b * x ≤ c * x :=
  mul_le_mul' h le_rfl

/-- The transition length dominates `ν` for `0 < ν ≤ 1` and `R ≥ 1`. -/
theorem tsd_le_transLen (ν R : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hR : 1 ≤ R) :
    ν ≤ transLen ν R := by
  unfold transLen
  have hs := Real.sq_sqrt hν.le
  have hs0 := Real.sqrt_nonneg ν
  have hs1 : Real.sqrt ν ≤ 1 := by
    have h := Real.sqrt_le_sqrt hν1
    rwa [Real.sqrt_one] at h
  have h1 : ν ≤ Real.sqrt ν := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hR hs0]

/-- Off the annulus `streamAnn`, the cutoff is either `≡ 1` (`ν age < 4/5`) or `≡ 0`
(`ν age > 1`) in the sense of `transVanishOff`. -/
theorem tsd_case_out (ν R : ℝ) (y : Space) (hν : 0 < ν) (hR : 0 < R) (hy : 0 < ϱ y)
    (h : y ∉ streamAnn ν R) : ν * age R y < 4 / 5 ∨ 1 < ν * age R y := by
  have e : ν * age R y = ν * R ^ 2 / ϱ y ^ 2 := by
    unfold age
    ring
  have hs1 := Real.sq_sqrt hν.le
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 * ν / 4 by linarith)
  have hA : (R * Real.sqrt ν) ^ 2 = R ^ 2 * ν := by rw [mul_pow, hs1]
  have hB : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by rw [mul_pow, hs2]
  have hX0 : 0 ≤ R * Real.sqrt ν := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hX1 : 0 ≤ R * Real.sqrt (5 * ν / 4) := mul_nonneg hR.le (Real.sqrt_nonneg _)
  simp only [streamAnn, Set.mem_setOf_eq, not_and_or, not_le] at h
  rw [e]
  rcases h with h | h
  · right
    rw [lt_div_iff₀ (pow_pos hy 2)]
    nlinarith [mul_pos (sub_pos.2 h) (add_pos_of_nonneg_of_pos hX0 hy)]
  · left
    rw [div_lt_iff₀ (pow_pos hy 2)]
    nlinarith [mul_pos (sub_pos.2 h) (add_pos_of_pos_of_nonneg hy hX1)]

/-- The coefficient bound: the three terms of the commutator bound, with the outer constant
`ofReal ((2cX+2cY) p)`, dominate the transition majorant `W + r W₁ + r² O`. -/
theorem tsd_inner (cX cY r p : ℝ) (hcX : 0 ≤ cX) (hcY : 0 ≤ cY) (hr : 0 ≤ r) (hp : 1 ≤ p)
    (hrp : r ≤ p) (W W1 O : ENNReal) :
    ENNReal.ofReal cX * W + ENNReal.ofReal r * (ENNReal.ofReal cX * (W + W1)) +
        ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal cY * (2 * O)) ≤
      ENNReal.ofReal ((2 * cX + 2 * cY) * p) *
        (W + ENNReal.ofReal r * W1 + ENNReal.ofReal (r ^ 2) * O) := by
  have hp0 : 0 ≤ p := by linarith
  have h1 : ENNReal.ofReal cX + ENNReal.ofReal cX * ENNReal.ofReal r ≤
      ENNReal.ofReal ((2 * cX + 2 * cY) * p) := by
    rw [← ENNReal.ofReal_mul hcX, ← ENNReal.ofReal_add hcX (mul_nonneg hcX hr)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg hcX (sub_nonneg.2 hp), mul_nonneg hcX (sub_nonneg.2 hrp),
      mul_nonneg hcY hp0, mul_nonneg hcX hp0]
  have h2 : ENNReal.ofReal cX ≤ ENNReal.ofReal ((2 * cX + 2 * cY) * p) := by
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg hcX (sub_nonneg.2 hp), mul_nonneg hcY hp0, mul_nonneg hcX hp0]
  have h3 : ENNReal.ofReal cY * 2 ≤ ENNReal.ofReal ((2 * cX + 2 * cY) * p) := by
    have e : ENNReal.ofReal cY * 2 = ENNReal.ofReal (2 * cY) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      ring
    rw [e]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg hcY (sub_nonneg.2 hp), mul_nonneg hcX hp0]
  have eL : ENNReal.ofReal cX * W + ENNReal.ofReal r * (ENNReal.ofReal cX * (W + W1)) +
        ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal cY * (2 * O)) =
      (ENNReal.ofReal cX + ENNReal.ofReal cX * ENNReal.ofReal r) * W +
        ENNReal.ofReal cX * (ENNReal.ofReal r * W1) +
        (ENNReal.ofReal cY * 2) * (ENNReal.ofReal (r ^ 2) * O) := by
    ring
  have eR : ENNReal.ofReal ((2 * cX + 2 * cY) * p) *
        (W + ENNReal.ofReal r * W1 + ENNReal.ofReal (r ^ 2) * O) =
      ENNReal.ofReal ((2 * cX + 2 * cY) * p) * W +
        ENNReal.ofReal ((2 * cX + 2 * cY) * p) * (ENNReal.ofReal r * W1) +
        ENNReal.ofReal ((2 * cX + 2 * cY) * p) * (ENNReal.ofReal (r ^ 2) * O) := by
    ring
  rw [eL, eR]
  exact add_le_add (add_le_add (tsd_mulR h1 W) (tsd_mulR h2 _))
    (tsd_mulR h3 _)

/-- The algebraic core: the two bounds on the stream correction and on the commutator combine
into the transition majorant with constant `(Cc C0 + Cm (2Cx + 2C0)) p^(k+1)`. -/
theorem tsd_abstract (Cc C0 Cx Cm p r : ℝ) (k : ℕ) (hCc : 0 ≤ Cc) (hC0 : 0 ≤ C0)
    (hCx : 0 ≤ Cx) (hCm : 0 ≤ Cm) (hp : 1 ≤ p) (hr0 : 0 ≤ r) (hrp : r ≤ p)
    (W W1 O Ec Es : ENNReal)
    (hEc : Ec ≤ ENNReal.ofReal (Cc * r ^ 2) * (ENNReal.ofReal C0 * O))
    (hEs : Es ≤ ENNReal.ofReal (Cm * p ^ k) *
      (ENNReal.ofReal Cx * W + ENNReal.ofReal r * (ENNReal.ofReal Cx * (W + W1)) +
        ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal C0 * (2 * O)))) :
    Ec + Es ≤ ENNReal.ofReal ((Cc * C0 + Cm * (2 * Cx + 2 * C0)) * p ^ (k + 1)) *
      (W + ENNReal.ofReal r * W1 + ENNReal.ofReal (r ^ 2) * O) := by
  have hp0 : 0 ≤ p := by linarith
  have hpk : 0 ≤ p ^ k := pow_nonneg hp0 k
  have hpk1 : 1 ≤ p ^ (k + 1) := one_le_pow₀ hp
  have hpk1' : 0 ≤ p ^ (k + 1) := pow_nonneg hp0 _
  have hK : 0 ≤ 2 * Cx + 2 * C0 := by linarith
  have hE1 : Ec ≤ ENNReal.ofReal (Cc * C0 * p ^ (k + 1)) *
      (W + ENNReal.ofReal r * W1 + ENNReal.ofReal (r ^ 2) * O) := by
    refine hEc.trans ?_
    have e : ENNReal.ofReal (Cc * r ^ 2) * (ENNReal.ofReal C0 * O) =
        ENNReal.ofReal (Cc * C0) * (ENNReal.ofReal (r ^ 2) * O) := by
      rw [ENNReal.ofReal_mul hCc, ENNReal.ofReal_mul hCc]
      ring
    rw [e]
    have hA1 : ENNReal.ofReal (Cc * C0) ≤ ENNReal.ofReal (Cc * C0 * p ^ (k + 1)) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (mul_nonneg hCc hC0) (sub_nonneg.2 hpk1)])
    have hB1 : ENNReal.ofReal (r ^ 2) * O ≤
        W + ENNReal.ofReal r * W1 + ENNReal.ofReal (r ^ 2) * O := le_add_self
    exact mul_le_mul' hA1 hB1
  have hE2 : Es ≤ ENNReal.ofReal (Cm * (2 * Cx + 2 * C0) * p ^ (k + 1)) *
      (W + ENNReal.ofReal r * W1 + ENNReal.ofReal (r ^ 2) * O) := by
    have hfac : ENNReal.ofReal (Cm * p ^ k) * ENNReal.ofReal ((2 * Cx + 2 * C0) * p) =
        ENNReal.ofReal (Cm * (2 * Cx + 2 * C0) * p ^ (k + 1)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hCm hpk)]
      congr 1
      ring
    refine hEs.trans ?_
    refine le_trans (tsd_mulL (tsd_inner Cx C0 r p hCx hC0 hr0 hp hrp W W1 O) _) ?_
    rw [← hfac]
    apply le_of_eq
    ring
  have hsplit : ENNReal.ofReal ((Cc * C0 + Cm * (2 * Cx + 2 * C0)) * p ^ (k + 1)) =
      ENNReal.ofReal (Cc * C0 * p ^ (k + 1)) +
        ENNReal.ofReal (Cm * (2 * Cx + 2 * C0) * p ^ (k + 1)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hCc hC0) hpk1')
      (mul_nonneg (mul_nonneg hCm hK) hpk1')]
    congr 1
    ring
  rw [hsplit, add_mul]
  exact add_le_add hE1 hE2

/-- **`TransSepDom`** (pointwise domination of both stream transitions, source 5312-5316,
3684-3712, 4176-4214), composed from `transVanishOff`, `transCutPoint`, `transCommPoint`,
`sepX0Dom` and `outPrimPointwise`. -/
theorem transSepDom : TransSepDom := by
  classical
  unfold TransSepDom
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨Cc, hCc0, hCut⟩ := transCutPoint χy hχ
  obtain ⟨Cx, hCx0, hX0⟩ := sepX0Dom σ₁ σ₂ hσ
  obtain ⟨Cm, k, hCm0, hComm⟩ := transCommPoint σ₁ σ₂ hσ χy hχ
  obtain ⟨C0, hC00, hOut⟩ := (outPrimPointwise_of IIIa.sepWDominated IIIa.sepKernelBounds :
    OutPrimPointwise) σ₁ σ₂ hσ
  refine ⟨Cc * C0 + Cm * (2 * Cx + 2 * C0), k + 1,
    add_nonneg (mul_nonneg hCc0 hC00) (mul_nonneg hCm0 (by linarith)), ?_⟩
  intro ν μ R P hν hν1 hR1 hP hμ T hT hM hA τ y hy
  have hR0 : 0 < R := by linarith
  have hμ0 : (0 : ℝ) ≤ 2 * μ + 2 := by linarith [hμ.1]
  by_cases hann : y ∈ streamAnn ν R
  · have hann' : R * Real.sqrt ν ≤ ϱ y ∧ ϱ y ≤ R * Real.sqrt (5 * ν / 4) := hann
    have hin : R * Real.sqrt ν ≤ ϱ y := hann'.1
    have hrO : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by linarith) (by linarith)) hR0
    obtain ⟨hXd0, hXd1⟩ :=
      hX0 ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hrO hrr hP T hT hM τ y hin
    obtain ⟨hOW, hOX⟩ :=
      hOut ν μ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P hν hμ hrO hrr hP T hT τ (ϱ y)
        (y 2) hin
    have hXbd0 : ‖sepX0 ν μ T τ y‖ₑ ≤
        ENNReal.ofReal Cx * IIIa.sepDom 0 0 (transGap ν R) (IIIa.srcNorm T) τ y := hXd0
    have hXbd1 : ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ ≤
        ENNReal.ofReal Cx * (IIIa.sepDom 0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          IIIa.sepDom 0 1 (transGap ν R) (IIIa.srcNorm T) τ y) := hXd1
    have hOW' : ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| ≤
        ENNReal.ofReal C0 * outMaj 0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2) :=
      le_trans hOW
        (tsd_mulL (outMaj_anti_a hμ0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) _)
    have hOX' : ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)| ≤
        ENNReal.ofReal C0 * (2 * outMaj 0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) :=
      le_trans hOX
        (tsd_mulL
          (tsd_mulL (outMaj_anti_a hμ0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) _)
          _)
    have hcut := hCut ν R hν hR0 (sepWre ν μ T) τ y hy
    simp only [Set.indicator_of_mem hann] at hcut
    have hEc : ‖streamCorr ν R χy (sepWre ν μ T) τ y‖ₑ ≤
        ENNReal.ofReal (Cc * (transLen ν R)⁻¹ ^ 2) *
          (ENNReal.ofReal C0 * outMaj 0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) :=
      le_trans hcut (tsd_mulL hOW' _)
    have hEs : ‖sepComm ν μ R χy T τ y‖ₑ ≤ ENNReal.ofReal (Cm * ν⁻¹ ^ k) *
        (ENNReal.ofReal Cx * IIIa.sepDom 0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal (transLen ν R)⁻¹ *
            (ENNReal.ofReal Cx * (IIIa.sepDom 0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
              IIIa.sepDom 0 1 (transGap ν R) (IIIa.srcNorm T) τ y)) +
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            (ENNReal.ofReal C0 * (2 * outMaj 0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)))) := by
      refine le_trans (hComm ν μ R P hν hν1 hR1 hP hμ T hT hM hA τ y hann) ?_
      exact tsd_mulL
        (add_le_add (add_le_add hXbd0 (tsd_mulL hXbd1 (ENNReal.ofReal (transLen ν R)⁻¹)))
          (tsd_mulL hOX' (ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2)))) _
    have hTM : transMaj ν R (IIIa.srcNorm T) τ y =
        IIIa.sepDom 0 0 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal (transLen ν R)⁻¹ * IIIa.sepDom 0 1 (transGap ν R) (IIIa.srcNorm T) τ y +
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            outMaj 0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2) := by
      simp only [transMaj, transMajW, transMajD, transMajS, Set.indicator_of_mem hann]
    have hST : sepTrans ν μ R χy T τ y =
        streamCorr ν R χy (sepWre ν μ T) τ y + sepComm ν μ R χy T τ y := rfl
    rw [hST, hTM]
    have hp1 : (1 : ℝ) ≤ ν⁻¹ := by
      have h := inv_anti₀ hν hν1
      rwa [inv_one] at h
    have hrp : (transLen ν R)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν (tsd_le_transLen ν R hν hν1 hR1)
    have hr0 : 0 ≤ (transLen ν R)⁻¹ :=
      inv_nonneg.2 (mul_nonneg hR0.le (Real.sqrt_nonneg _))
    refine (enorm_add_le _ _).trans ?_
    exact tsd_abstract Cc C0 Cx Cm ν⁻¹ (transLen ν R)⁻¹ k hCc0 hC00 hCx0 hCm0 hp1 hr0 hrp
      _ _ _ _ _ hEc hEs
  · have hc := tsd_case_out ν R y hν hR0 hy hann
    rw [transVanishOff ν μ R χy hχ hν hR0 T τ y hy hc]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete
