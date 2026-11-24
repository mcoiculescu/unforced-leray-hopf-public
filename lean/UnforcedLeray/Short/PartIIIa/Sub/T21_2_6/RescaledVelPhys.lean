import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# `PartIII-a:T21/2/6/3`: the physical velocity bound (`RescaledVelPhys`)

Source of record: `the November 2 reference manuscript` lines 290-336 (`sct:comparison`:
`‖D^j(v - V_c^p)‖_∞ ≤ C_j ν⁻¹ a^{-(5+j)/2} e^{-b_j c²/a}`), and 2866-2873 (`‖D^j V_c^p‖_∞ ≤
C_j a^{-(3+j)/2}`). Take `b₀ = 1`. For `θ ≥ b ≥ 1` we have `νa ≤ 1`, hence `a ≤ c²` with `c = ν⁻²`
and `ν ≤ 1`; the Gaussian factor is absorbed by `e^{-t} ≤ 1/t` with `t = b_j c²/a`, which gives
`ν⁻¹ c⁻² a^{-(5+j)/2} a = ν³ a^{-(3+j)/2} ≤ a^{-(3+j)/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The power identity `a^{-(5+j)/2} · a = (a^{3/2} (√a)^j)⁻¹` for `a > 0`. -/
theorem rpow_identity_vel (a : ℝ) (ha : 0 < a) (j : ℕ) :
    a ^ (-((5 + (j : ℝ)) / 2)) * a = (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ j)⁻¹ := by
  have hs : Real.sqrt a ^ j = a ^ ((1 / 2 : ℝ) * j) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  have h1 : a ^ (-((5 + (j : ℝ)) / 2)) * a = a ^ (-((5 + (j : ℝ)) / 2) + 1) := by
    rw [Real.rpow_add ha, Real.rpow_one]
  rw [hs, h1, ← Real.rpow_add ha, ← Real.rpow_neg ha.le]
  congr 1
  ring

/-- **The physical velocity bound** (SP 290-336, 2866-2873). -/
theorem rescaledVelPhys_of (hcmp : UnforcedLeray.Short.PartI.TrainComparison)
    (hVc : VcWeightedJet) : RescaledVelPhys := by
  choose Cj βj Nj hCj hβj hNj hbd using fun j : ℕ => hcmp 2 (by norm_num) j
  choose G hG using fun j : ℕ => hVc 0 j
  refine ⟨1, fun b hb => ?_⟩
  refine ⟨(|Cj 0 / βj 0| + |G 0|) + (|Cj 1 / βj 1| + |G 1|) + (|Cj 2 / βj 2| + |G 2|),
    min 1 (min (Nj 0) (min (Nj 1) (Nj 2))), lt_min one_pos (lt_min (hNj 0) (lt_min (hNj 1) (hNj 2))),
    fun ν hν tr hbuc r hr hθ j hj x => ?_⟩
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_left _ _)
  have hN0 : ν ≤ Nj 0 := le_trans hν.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hN1 : ν ≤ Nj 1 :=
    le_trans hν.2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hN2 : ν ≤ Nj 2 :=
    le_trans hν.2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hνpos : 0 < ν := hν.1
  have ha : 0 < clockA ν r := by
    unfold clockA
    nlinarith [mul_nonneg hνpos.le hr]
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hνpos _
  -- `νa ≤ 1`, from `b ≤ θ = (νa)⁻¹` and `b ≥ 1`
  have hνa : ν * clockA ν r ≤ 1 := by
    have hθ' : b ≤ (ν * clockA ν r)⁻¹ := hθ
    have h1 : (1 : ℝ) ≤ (ν * clockA ν r)⁻¹ := le_trans hb hθ'
    have hpos : 0 < ν * clockA ν r := mul_pos hνpos ha
    have key : (ν * clockA ν r) * (ν * clockA ν r)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]
  have hcsq : (ν ^ (-2 : ℝ)) ^ 2 = ((ν ^ 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hνpos.le, Real.rpow_two, inv_pow]
  have hac : clockA ν r ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hcsq, ← one_div, le_div_iff₀ (by positivity)]
    have h3 : ν ^ 3 ≤ 1 := pow_le_one₀ hνpos.le hν1
    nlinarith [mul_le_mul hνa h3 (by positivity) zero_le_one]
  have hcinv : ((ν ^ (-2 : ℝ)) ^ 2)⁻¹ = ν ^ 4 := by
    rw [hcsq, inv_inv]
    ring
  have hν3 : ν⁻¹ * ν ^ 4 = ν ^ 3 := by
    calc ν⁻¹ * ν ^ 4 = ν⁻¹ * ν * ν ^ 3 := by ring
      _ = ν ^ 3 := by rw [inv_mul_cancel₀ hνpos.ne', one_mul]
  have hν3le : ν ^ 3 ≤ 1 := pow_le_one₀ hνpos.le hν1
  -- the per-derivative bound, for any `j` with `ν ≤ N_j`
  have key : ∀ j : ℕ, ν ≤ Nj j → ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (tr.v r) x‖ ≤
        (|Cj j / βj j| + |G j|) * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ := by
    intro j hNj' x
    have hX : 0 ≤ (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ :=
      inv_nonneg.2 (mul_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg (Real.sqrt_nonneg _) _))
    have hK : 0 ≤ Cj j * ν⁻¹ * clockA ν r ^ (-((5 + (j : ℝ)) / 2)) :=
      mul_nonneg (mul_nonneg (hCj j).le (inv_nonneg.2 hνpos.le)) (Real.rpow_nonneg ha.le _)
    have hM : 0 ≤ Cj j * ν⁻¹ * clockA ν r ^ (-((5 + (j : ℝ)) / 2)) *
        Real.exp (-(βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)) :=
      mul_nonneg hK (Real.exp_pos _).le
    have hbj := hbd j ν hνpos hNj' tr hbuc r hr hac
    have hpt' : ‖iteratedFDeriv ℝ j (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z) x‖
        ≤ Cj j * ν⁻¹ * clockA ν r ^ (-((5 + (j : ℝ)) / 2)) *
          Real.exp (-(βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)) :=
      UnforcedLeray.B0277.norm_le_of_supNormD_le hM hbj.2 x
    -- the Gaussian factor: `e^{-t} ≤ 1/t`
    have hexp : Real.exp (-(βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)) ≤
        clockA ν r / (βj j * (ν ^ (-2 : ℝ)) ^ 2) := by
      have ht : 0 < βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r :=
        div_pos (mul_pos (hβj j) (pow_pos hc 2)) ha
      have h1 : βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r ≤
          Real.exp (βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r) := by
        linarith [Real.add_one_le_exp (βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)]
      rw [Real.exp_neg]
      calc (Real.exp (βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r))⁻¹
          ≤ (βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)⁻¹ := inv_anti₀ ht h1
        _ = clockA ν r / (βj j * (ν ^ (-2 : ℝ)) ^ 2) := inv_div _ _
    have hAerr : Cj j * ν⁻¹ * clockA ν r ^ (-((5 + (j : ℝ)) / 2)) *
        Real.exp (-(βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)) ≤
        (Cj j / βj j) * ν ^ 3 * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ := by
      have hid := rpow_identity_vel (clockA ν r) ha j
      calc Cj j * ν⁻¹ * clockA ν r ^ (-((5 + (j : ℝ)) / 2)) *
            Real.exp (-(βj j * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r))
          ≤ Cj j * ν⁻¹ * clockA ν r ^ (-((5 + (j : ℝ)) / 2)) *
            (clockA ν r / (βj j * (ν ^ (-2 : ℝ)) ^ 2)) := mul_le_mul_of_nonneg_left hexp hK
        _ = (Cj j / βj j) * (ν⁻¹ * ((ν ^ (-2 : ℝ)) ^ 2)⁻¹) *
            (clockA ν r ^ (-((5 + (j : ℝ)) / 2)) * clockA ν r) := by ring
        _ = (Cj j / βj j) * ν ^ 3 * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ := by
          rw [hcinv, hν3, hid]
    -- the Gaussian-small part of the vortex, `‖D^j V_c^p‖_∞`
    have hGj := hG j ν (ν ^ (-2 : ℝ)) r hνpos hc hr hac x
    simp only [pow_zero, one_mul] at hGj
    have hBG : ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r) x‖ ≤
        |G j| * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ :=
      hGj.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX)
    -- smoothness and the splitting `v = (v - V_c^p) + V_c^p`
    have hsmV : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
    have hsmVc : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r) :=
      UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha
    have hsplit : tr.v r = (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z) +
        UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r := by
      funext z
      simp
    have hA : ContDiffAt ℝ j (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z) x :=
      (hsmV.sub hsmVc).contDiffAt.of_le (by first | exact le_top | simp)
    have hB : ContDiffAt ℝ j (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r) x :=
      hsmVc.contDiffAt.of_le (by first | exact le_top | simp)
    rw [hsplit, iteratedFDeriv_add_apply hA hB]
    have hfin : (Cj j / βj j) * ν ^ 3 * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ ≤
        |Cj j / βj j| * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ := by
      have hKnn : 0 ≤ Cj j / βj j := div_nonneg (hCj j).le (hβj j).le
      have h1 : (Cj j / βj j) * ν ^ 3 ≤ |Cj j / βj j| :=
        le_trans (mul_le_of_le_one_right hKnn hν3le) (le_abs_self _)
      exact mul_le_mul_of_nonneg_right h1 hX
    calc _ ≤ ‖iteratedFDeriv ℝ j (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z) x‖
          + ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r) x‖ := norm_add_le _ _
      _ ≤ (Cj j / βj j) * ν ^ 3 * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ +
          |G j| * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ :=
        add_le_add (hpt'.trans hAerr) hBG
      _ ≤ |Cj j / βj j| * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ +
          |G j| * (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ := by linarith
      _ = _ := by ring
  have hXnn : ∀ j : ℕ, 0 ≤ (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r) ^ j)⁻¹ := fun j =>
    inv_nonneg.2 (mul_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg (Real.sqrt_nonneg _) _))
  interval_cases j
  · exact (key 0 hN0 x).trans (mul_le_mul_of_nonneg_right
      (by linarith [abs_nonneg (Cj 0 / βj 0), abs_nonneg (Cj 1 / βj 1), abs_nonneg (Cj 2 / βj 2),
        abs_nonneg (G 0), abs_nonneg (G 1), abs_nonneg (G 2)]) (hXnn 0))
  · exact (key 1 hN1 x).trans (mul_le_mul_of_nonneg_right
      (by linarith [abs_nonneg (Cj 0 / βj 0), abs_nonneg (Cj 1 / βj 1), abs_nonneg (Cj 2 / βj 2),
        abs_nonneg (G 0), abs_nonneg (G 1), abs_nonneg (G 2)]) (hXnn 1))
  · exact (key 2 hN2 x).trans (mul_le_mul_of_nonneg_right
      (by linarith [abs_nonneg (Cj 0 / βj 0), abs_nonneg (Cj 1 / βj 1), abs_nonneg (Cj 2 / βj 2),
        abs_nonneg (G 0), abs_nonneg (G 1), abs_nonneg (G 2)]) (hXnn 2))

end UnforcedLeray.Short.IIIa
