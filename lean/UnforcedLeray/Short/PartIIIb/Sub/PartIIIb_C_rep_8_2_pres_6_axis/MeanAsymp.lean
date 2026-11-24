import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemPointwise
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemainderSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth

/-!
# `PartIII-b:C/rep/8/2/pres/6/axis/2`: the leading mean at the axis (`axisEvMeanAsymp_of`)

Source `the November 2 reference manuscript`:
`sct:expansion` (447-459) at `N = 0`, `p = ∞`; the heat identity `K G = -G` (1268-1269); and the
leading mean at the axis (1310-1322).

With `R = meanRemainder tr 0` and `S = meanStream tr = R + a₀ G_{νs}`, the completion
`(1 - η∂_η - 2s∂_s) S - 2a₀G_{νs}` equals `R - η∂_ηR - 2s∂_sR` because
`(1-K)G_{νs} = 2G_{νs}` (`AxisEvOrg.heatKernel1_completion`).  The three pointwise bounds
`MeanRemPointwise` at `(m',b',l') = (0,0,0), (1,1,0), (0,0,1)` give `s^{-3/2}` each, and
`s · s^{-5/2} = s^{-3/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIa (polyConst)

namespace AxisEvMean

/-- The Part I/II polynomial majorant at `c = (ν²)⁻¹`, `0 < ν ≤ 1`. -/
theorem polyConst_le_inv (C : ℝ) (M : ℕ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    UnforcedLeray.Short.PartIIa.polyConst C M ν (ν ^ 2)⁻¹ ≤ |C| * 3 ^ M * ν⁻¹ ^ (2 * M) :=
  UnforcedLeray.Short.IIIa.polyP_le_inv_pow C M hν hν1

/-- `ν^{-2} = (ν²)⁻¹` for real exponent `-2`. -/
theorem rpow_neg_two {ν : ℝ} (hν : 0 < ν) : ν ^ (-(2 : ℝ)) = (ν ^ 2)⁻¹ := by
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- `s · s^{-5/2} = s^{-3/2}` for `s > 0`. -/
theorem mul_rpow_five_halves {s : ℝ} (hs : 0 < s) :
    s * s ^ (-(5 / 2 : ℝ)) = s ^ (-(3 / 2 : ℝ)) := by
  rw [show (-(3 / 2 : ℝ)) = -(5 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hs, Real.rpow_one, mul_comm]

end AxisEvMean

/-- **`PartIII-b:C/rep/8/2/pres/6/axis/2`: the mean stream completion is the leading heat mode**
(source 447-459, 1268-1269, 1310-1322). -/
theorem axisEvMeanAsymp_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : AxisEvMeanAsymp := by
  have hPt : UnforcedLeray.Short.PartIIa.MeanRemPointwise :=
    UnforcedLeray.Short.PartIIa.meanRemPointwise_of hM
      (UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of hE
        UnforcedLeray.Short.PartIIa.heatKernelIterSmooth)
      (UnforcedLeray.Short.PartIIa.sliceDerivContinuous_of
        UnforcedLeray.Short.PartIIa.ageDerivSmooth)
      UnforcedLeray.Short.PartIIa.essSupPointwise
  have hRS := UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of hE
    UnforcedLeray.Short.PartIIa.heatKernelIterSmooth
  obtain ⟨Ca, Ma, νa, hνa0, Ha⟩ := hPt 2 0 0 0 0 (by norm_num)
  obtain ⟨Cb, Mb, νb, hνb0, Hb⟩ := hPt 2 0 1 1 0 (by norm_num)
  obtain ⟨Cc, Mc, νc, hνc0, Hc⟩ := hPt 2 0 0 0 1 (by norm_num)
  refine ⟨(|Ca| * 3 ^ Ma + |Cb| * 3 ^ Mb + 2 * (|Cc| * 3 ^ Mc)), 2 * (Ma + Mb + Mc),
    min (min νa νb) (min νc 1), lt_min (lt_min hνa0 hνb0) (lt_min hνc0 one_pos), ?_⟩
  intro ν hν c hc tr hbuc s hs η
  have hν0 : 0 < ν := hν.1
  have hνa' : ν ≤ νa := (hν.2.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνb' : ν ≤ νb := (hν.2.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hνc' : ν ≤ νc := (hν.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := (hν.2.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcT := UnforcedLeray.Short.IIIa.period_eq_trainPeriod hν0 hc
  subst hcT
  have hc2 : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := hc
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc2]
    positivity
  have hs0 : 0 < s := by linarith only [hs]
  have ht1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).2 hν1
  -- the three pointwise bounds, with exponents normalized
  have hA : |UnforcedLeray.Short.PartI.meanRemainder tr 0 s η| ≤
      UnforcedLeray.Short.PartIIa.polyConst Ca Ma ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ)) := by
    have h := Ha ν hν0 hνa' tr hbuc s hs η
    simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.cast_zero] at h
    rw [show ((0 : ℝ) - 0 - 2 * 0 - 3) / 2 - 0 = -(3 / 2 : ℝ) by norm_num] at h
    exact h
  have hB : |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η| ≤
      UnforcedLeray.Short.PartIIa.polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ)) := by
    have h := Hb ν hν0 hνb' tr hbuc s hs η
    simp only [pow_one, iteratedDeriv_one, iteratedDeriv_zero, Nat.cast_one, Nat.cast_zero] at h
    rw [show ((1 : ℝ) - 1 - 2 * 0 - 3) / 2 - 0 = -(3 / 2 : ℝ) by norm_num] at h
    exact h
  have hC : |deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s| ≤
      UnforcedLeray.Short.PartIIa.polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) * s ^ (-(5 / 2 : ℝ)) := by
    have h := Hc ν hν0 hνc' tr hbuc s hs η
    simp only [pow_zero, one_mul, iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_one,
      Nat.cast_zero] at h
    rw [show ((0 : ℝ) - 0 - 2 * 0 - 3) / 2 - 1 = -(5 / 2 : ℝ) by norm_num] at h
    exact h
  -- smoothness of the remainder and the heat-kernel slices
  have hRsm := hRS ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) hν0 hcpos tr hbuc 0
  have hmem : (s, η) ∈ Ioi 0 ×ˢ (univ : Set ℝ) := Set.mk_mem_prod hs0 (Set.mem_univ _)
  have hFR : DifferentiableAt ℝ (fun x : ℝ × ℝ =>
      UnforcedLeray.Short.PartI.meanRemainder tr 0 x.1 x.2) (s, η) :=
    (hRsm.contDiffAt (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) hmem)).differentiableAt
      (by simp)
  have hRe : DifferentiableAt ℝ (fun e : ℝ => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η :=
    DifferentiableAt.comp (g := fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanRemainder tr 0 x.1 x.2)
      (f := fun e : ℝ => (s, e)) η hFR (by fun_prop)
  have hRs : DifferentiableAt ℝ (fun r : ℝ => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s :=
    DifferentiableAt.comp (g := fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanRemainder tr 0 x.1 x.2)
      (f := fun r : ℝ => (r, η)) s hFR (by fun_prop)
  have hGe : DifferentiableAt ℝ (fun e : ℝ => UnforcedLeray.Short.PartI.heatKernel1 (ν * s) e) η :=
    (AxisEvOrg.hasDerivAt_heatKernel1_eta (mul_pos hν0 hs0) η).differentiableAt
  have hGs : DifferentiableAt ℝ (fun r : ℝ => UnforcedLeray.Short.PartI.heatKernel1 (ν * r) η) s :=
    (AxisEvOrg.hasDerivAt_heatKernel1_age hν0 hs0 η).differentiableAt
  -- `S = R₀ + a₀ G_{νr}` pointwise
  have hsplit : ∀ r e : ℝ, UnforcedLeray.Short.PartI.meanStream tr r e =
      UnforcedLeray.Short.PartI.meanRemainder tr 0 r e +
        UnforcedLeray.Short.PartI.meanCoeff tr 0 * UnforcedLeray.Short.PartI.heatKernel1 (ν * r) e := by
    intro r e
    unfold UnforcedLeray.Short.PartI.meanRemainder
    simp only [zero_add, Finset.sum_range_one, mul_zero, iteratedDeriv_zero]
    ring
  have hDe : deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η =
      deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η +
        UnforcedLeray.Short.PartI.meanCoeff tr 0 *
          deriv (fun e => UnforcedLeray.Short.PartI.heatKernel1 (ν * s) e) η := by
    have hEq : (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) =ᶠ[𝓝 η]
        (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e +
          UnforcedLeray.Short.PartI.meanCoeff tr 0 *
            UnforcedLeray.Short.PartI.heatKernel1 (ν * s) e) :=
      Filter.Eventually.of_forall (fun e => hsplit s e)
    have h1 := hRe.hasDerivAt.add (hGe.hasDerivAt.const_mul (UnforcedLeray.Short.PartI.meanCoeff tr 0))
    rw [hEq.deriv_eq]
    exact h1.deriv
  have hDs : deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s =
      deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s +
        UnforcedLeray.Short.PartI.meanCoeff tr 0 *
          deriv (fun r => UnforcedLeray.Short.PartI.heatKernel1 (ν * r) η) s := by
    have hEq : (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) =ᶠ[𝓝 s]
        (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η +
          UnforcedLeray.Short.PartI.meanCoeff tr 0 *
            UnforcedLeray.Short.PartI.heatKernel1 (ν * r) η) :=
      Filter.Eventually.of_forall (fun r => hsplit r η)
    have h1 := hRs.hasDerivAt.add (hGs.hasDerivAt.const_mul (UnforcedLeray.Short.PartI.meanCoeff tr 0))
    rw [hEq.deriv_eq]
    exact h1.deriv
  have hcomp := AxisEvOrg.heatKernel1_completion hν0 hs0 η
  -- the completion minus the leading mode
  have key : UnforcedLeray.Short.IIIa.meanCompletion tr s η -
      2 * UnforcedLeray.Short.PartI.meanCoeff tr 0 *
        UnforcedLeray.Short.PartI.heatKernel1 (ν * s) η =
      UnforcedLeray.Short.PartI.meanRemainder tr 0 s η -
        (η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η +
          2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s) := by
    unfold UnforcedLeray.Short.IIIa.meanCompletion
    rw [hDe, hDs, hsplit s η]
    linear_combination UnforcedLeray.Short.PartI.meanCoeff tr 0 * hcomp
  rw [key]
  -- assemble the bounds
  have hsp := AxisEvMean.mul_rpow_five_halves hs0
  have hT0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
  have hX : |η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η| ≤
      polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ)) := by
    rw [abs_mul]
    exact hB
  have hY : |2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s| ≤
      2 * (polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ))) := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * s)]
    calc 2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s|
        ≤ 2 * s * (polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) * s ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hC (by linarith)
      _ = 2 * (polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) * (s * s ^ (-(5 / 2 : ℝ)))) := by ring
      _ = 2 * (polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ))) := by rw [hsp]
  have htri : |UnforcedLeray.Short.PartI.meanRemainder tr 0 s η -
        (η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η +
          2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s)| ≤
      |UnforcedLeray.Short.PartI.meanRemainder tr 0 s η| +
        |η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η| +
        |2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s| := by
    have h1 := abs_sub (UnforcedLeray.Short.PartI.meanRemainder tr 0 s η)
      (η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η +
          2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s)
    have h2 := abs_add_le (η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η)
      (2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s)
    linarith
  -- the three constants, uniform in `ν ≤ 1`
  have hPa : polyConst Ca Ma ν (ν ^ (-(2 : ℝ))) ≤
      |Ca| * 3 ^ Ma * (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) := by
    rw [AxisEvMean.rpow_neg_two hν0]
    exact le_trans (AxisEvMean.polyConst_le_inv Ca Ma hν0 hν1)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hPb : polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) ≤
      |Cb| * 3 ^ Mb * (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) := by
    rw [AxisEvMean.rpow_neg_two hν0]
    exact le_trans (AxisEvMean.polyConst_le_inv Cb Mb hν0 hν1)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hPc : polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) ≤
      |Cc| * 3 ^ Mc * (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) := by
    rw [AxisEvMean.rpow_neg_two hν0]
    exact le_trans (AxisEvMean.polyConst_le_inv Cc Mc hν0 hν1)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hsumP : polyConst Ca Ma ν (ν ^ (-(2 : ℝ))) + polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) +
      2 * polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) ≤
      (|Ca| * 3 ^ Ma + |Cb| * 3 ^ Mb + 2 * (|Cc| * 3 ^ Mc)) * (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) := by
    calc polyConst Ca Ma ν (ν ^ (-(2 : ℝ))) + polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) +
          2 * polyConst Cc Mc ν (ν ^ (-(2 : ℝ)))
        ≤ |Ca| * 3 ^ Ma * (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) +
            |Cb| * 3 ^ Mb * (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) +
            2 * (|Cc| * 3 ^ Mc * (ν⁻¹ ^ (2 * (Ma + Mb + Mc)))) :=
          add_le_add (add_le_add hPa hPb) (mul_le_mul_of_nonneg_left hPc (by norm_num))
      _ = (|Ca| * 3 ^ Ma + |Cb| * 3 ^ Mb + 2 * (|Cc| * 3 ^ Mc)) *
            (ν⁻¹ ^ (2 * (Ma + Mb + Mc))) := by ring
  calc |UnforcedLeray.Short.PartI.meanRemainder tr 0 s η -
        (η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η +
          2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s)|
      ≤ |UnforcedLeray.Short.PartI.meanRemainder tr 0 s η| +
        |η * deriv (fun e => UnforcedLeray.Short.PartI.meanRemainder tr 0 s e) η| +
        |2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanRemainder tr 0 r η) s| := htri
    _ ≤ polyConst Ca Ma ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ)) +
        polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ)) +
        2 * (polyConst Cc Mc ν (ν ^ (-(2 : ℝ))) * s ^ (-(3 / 2 : ℝ))) := by
          linarith [hA, hX, hY]
    _ = (polyConst Ca Ma ν (ν ^ (-(2 : ℝ))) + polyConst Cb Mb ν (ν ^ (-(2 : ℝ))) +
        2 * polyConst Cc Mc ν (ν ^ (-(2 : ℝ)))) * s ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ ((|Ca| * 3 ^ Ma + |Cb| * 3 ^ Mb + 2 * (|Cc| * 3 ^ Mc)) *
        (ν⁻¹ ^ (2 * (Ma + Mb + Mc)))) * s ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hsumP hT0
    _ = (|Ca| * 3 ^ Ma + |Cb| * 3 ^ Mb + 2 * (|Cc| * 3 ^ Mc)) * ν⁻¹ ^ (2 * (Ma + Mb + Mc)) *
        s ^ (-(3 / 2 : ℝ)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
