import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis.FluctSharp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis.MeanAsymp
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateFluctVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateMeanVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.RaisedStreamSplit
import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# `PartIII-b:C/rep/8/2/pres/6/axis/4`: the train has the axis decay (`axisEvTrainDecay_of`)

Source `the November 2 reference manuscript`:
the term-by-term axis limit (1310-1323), the leading mean `2R⁻¹a₀G_ν` (1321-1322), and the
Part I readings `sct:mean` (397-404), `sct:fluctuation` (439-446), `sct:expansion` (447-459).

For a fixed BUC train at `c = cOf ν = ν⁻²` the raw profile `b = (v₁, v₂ + εH)` satisfies
`AxisEvDecay b g` with `g x = ε·2a₀G_ν(x)`:
* `|v| ≤ K(1+s)⁻¹` for `s ≥ 1` (`LateFluctVel`, `LateMeanVel` at `m_Z = 0`), so `√s|b₀| ≤ K(√s)⁻¹`;
* `√s b₁(s, ξ, √s x) - g x = √s v₁ + ε√s H̃ + ε√s(S_completion - 2a₀G_{νs}(√s x))`, where
  `H̃` is the fluctuation completion (`AxisEvFluctSharp`, `O((1+s)⁻¹)`) and the mean remainder
  is `O(s^{-3/2})` (`AxisEvMeanAsymp`); the leading mean cancels by `heatKernel1_scale`.
  Each term is `O((√s)⁻¹)`, and `late_small` gives the threshold.

The constants depend on the train and `ε`, which is allowed: `AxisEvDecay` quantifies over
`S` after the train and `ε` are fixed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI (hfluct hmean meanCoeff heatKernel1)

namespace AxisEvTrainDecayAux

/-- `√s |A| ≤ K(√s)⁻¹` when `|A| ≤ K(1+s)⁻¹`, for `s ≥ 1`. -/
theorem sqrt_mul_abs_le_inv {s K A : ℝ} (hs : 1 ≤ s) (hK : 0 ≤ K)
    (hA : |A| ≤ K * (1 + s)⁻¹) : Real.sqrt s * |A| ≤ K * (Real.sqrt s)⁻¹ := by
  calc Real.sqrt s * |A| ≤ Real.sqrt s * (K * (1 + s)⁻¹) :=
        mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg s)
    _ = K * (Real.sqrt s * (1 + s)⁻¹) := by ring
    _ ≤ K * (Real.sqrt s)⁻¹ :=
        mul_le_mul_of_nonneg_left (AxisEvOrg.sqrt_mul_inv_one_add_le (by linarith)) hK

/-- `√s |A| ≤ K(√s)⁻¹` when `|A| ≤ K s^{-3/2}`, for `s ≥ 1`. -/
theorem sqrt_mul_abs_le_inv_rpow {s K A : ℝ} (hs : 1 ≤ s) (hK : 0 ≤ K)
    (hA : |A| ≤ K * s ^ (-(3 / 2 : ℝ))) : Real.sqrt s * |A| ≤ K * (Real.sqrt s)⁻¹ := by
  calc Real.sqrt s * |A| ≤ Real.sqrt s * (K * s ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg s)
    _ = K * (Real.sqrt s * s ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ K * (Real.sqrt s)⁻¹ := mul_le_mul_of_nonneg_left (AxisEvOrg.sqrt_mul_rpow_le hs) hK

/-- A component of a vector is bounded by its norm. -/
theorem abs_apply_le_norm (w : UnforcedLeray.Train.Vec) (i : Fin 2) : |w i| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le w i

end AxisEvTrainDecayAux

/-- **`PartIII-b:C/rep/8/2/pres/6/axis/4`: the train has the axis decay** (source 1310-1323,
397-404, 439-459). -/
theorem axisEvTrainDecay_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : AxisEvTrainDecay := by
  have hSm : UnforcedLeray.Short.PartIIa.MeanStreamSmooth :=
    fun nu c hnu hc tr hb => (hE nu c hnu hc tr hb).1
  have hSp : UnforcedLeray.Short.IIIa.RaisedStreamSplit :=
    UnforcedLeray.Short.IIIa.raisedStreamSplit_of UnforcedLeray.Short.PartI.trainStreamSmooth hSm
  have hMP : UnforcedLeray.Short.PartIIa.MeanStreamPointwise :=
    UnforcedLeray.Short.PartIIa.meanStreamPointwise_of hM hSm
      (UnforcedLeray.Short.PartIIa.sliceDerivContinuous_of
        UnforcedLeray.Short.PartIIa.ageDerivSmooth)
      UnforcedLeray.Short.PartIIa.essSupPointwise
  have hFV : UnforcedLeray.Short.IIIa.LateFluctVel :=
    UnforcedLeray.Short.IIIa.lateFluctVel_of hF
  have hMV : UnforcedLeray.Short.IIIa.LateMeanVel :=
    UnforcedLeray.Short.IIIa.lateMeanVel_of hE hMP
  have hFS : AxisEvFluctSharp := axisEvFluctSharp_of hF hE
  have hMA : AxisEvMeanAsymp := axisEvMeanAsymp_of hM hE
  obtain ⟨C1, k1, ν1, hν1, H1⟩ := hFV 0 le_rfl
  obtain ⟨C2, k2, ν2, hν2, H2⟩ := hMV 0 le_rfl
  unfold AxisEvFluctSharp at hFS
  unfold AxisEvMeanAsymp at hMA
  obtain ⟨C3, k3, ν3, hν3, H3⟩ := hFS
  obtain ⟨C4, k4, ν4, hν4, H4⟩ := hMA
  unfold AxisEvTrainDecay
  refine ⟨min (min ν1 ν2) (min ν3 ν4), lt_min (lt_min hν1 hν2) (lt_min hν3 hν4), ?_⟩
  intro ν hν hνle tr hb ε
  have m1 : ν ∈ Ioc 0 ν1 :=
    ⟨hν, le_trans hνle (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have m2 : ν ∈ Ioc 0 ν2 :=
    ⟨hν, le_trans hνle (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have m3 : ν ∈ Ioc 0 ν3 :=
    ⟨hν, le_trans hνle (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have m4 : ν ∈ Ioc 0 ν4 :=
    ⟨hν, le_trans hνle (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hc : UnforcedLeray.Short.PartIIIb.Concrete.cOf ν = (ν ^ 2)⁻¹ := rfl
  have hcpos : 0 < UnforcedLeray.Short.PartIIIb.Concrete.cOf ν := inv_pos.2 (pow_pos hν 2)
  -- pointwise bounds of the velocity (`LateFluctVel`, `LateMeanVel` at `m_Z = 0`)
  have hf : ∀ s : ℝ, 1 ≤ s → ∀ ξ η : ℝ,
      ‖hfluct (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) (ξ, η)‖ ≤
        C1 * ν⁻¹ ^ k1 * (1 + s)⁻¹ := by
    intro s hs ξ η
    have h := H1 ν m1 _ hc tr hb s hs ξ η
    rw [AxisEvOrg.transWeight_zero, one_mul, Real.rpow_neg_one] at h
    exact h
  have hm : ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      ‖hmean (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) η‖ ≤
        C2 * ν⁻¹ ^ k2 * (1 + s)⁻¹ := by
    intro s hs η
    have h := H2 ν m2 _ hc tr hb s hs 0 η
    rw [AxisEvOrg.transWeight_zero, one_mul, Real.rpow_neg_one] at h
    exact h
  have hKv0 : 0 ≤ |C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2| := by positivity
  have hv : ∀ s : ℝ, 1 ≤ s → ∀ ξ η : ℝ,
      ‖tr.v s (ξ, η)‖ ≤ (|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) * (1 + s)⁻¹ := by
    intro s hs ξ η
    have key : tr.v s (ξ, η) = hfluct (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) (ξ, η)
        + hmean (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) η := by
      unfold hfluct
      exact (sub_add_cancel _ _).symm
    have hinv : 0 ≤ (1 + s)⁻¹ := inv_nonneg.2 (by linarith)
    rw [key]
    calc ‖hfluct (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) (ξ, η)
          + hmean (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) η‖
        ≤ ‖hfluct (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) (ξ, η)‖
          + ‖hmean (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) (tr.v s) η‖ := norm_add_le _ _
      _ ≤ C1 * ν⁻¹ ^ k1 * (1 + s)⁻¹ + C2 * ν⁻¹ ^ k2 * (1 + s)⁻¹ :=
          add_le_add (hf s hs ξ η) (hm s hs η)
      _ ≤ |C1 * ν⁻¹ ^ k1| * (1 + s)⁻¹ + |C2 * ν⁻¹ ^ k2| * (1 + s)⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hinv)
            (mul_le_mul_of_nonneg_right (le_abs_self _) hinv)
      _ = (|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) * (1 + s)⁻¹ := by ring
  unfold AxisEvDecay
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_const.mul (continuous_const.mul (AxisEvOrg.continuous_heatKernel1 ν))
  · intro e he
    obtain ⟨S, hS1, hS⟩ := AxisEvOrg.late_small (|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) e he
    refine ⟨S, fun s hs ξ η => ?_⟩
    have hs1 : 1 ≤ s := le_trans hS1 hs
    have hb0 : |UnforcedLeray.Cons.C03.rawProfile ε tr.v tr.ψ (s, (ξ, η)) 0|
        ≤ (|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) * (1 + s)⁻¹ := by
      rw [UnforcedLeray.Cons.C03.rawProfile_zero]
      exact (AxisEvTrainDecayAux.abs_apply_le_norm _ 0).trans (hv s hs1 ξ η)
    exact (AxisEvTrainDecayAux.sqrt_mul_abs_le_inv hs1 hKv0 hb0).trans (hS s hs)
  · intro e he
    obtain ⟨S, hS1, hS⟩ := AxisEvOrg.late_small
      ((|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) + |ε| * |C3 * ν⁻¹ ^ k3|
        + |ε| * |C4 * ν⁻¹ ^ k4|) e he
    refine ⟨S, fun s hs ξ x => ?_⟩
    have hs1 : 1 ≤ s := le_trans hS1 hs
    have hs0 : 0 < s := by linarith
    have hsplit := hSp ν (UnforcedLeray.Short.PartIIIb.Concrete.cOf ν) hν hcpos tr hb s hs0 ξ
      (Real.sqrt s * x)
    have hsc := AxisEvOrg.heatKernel1_scale hν hs0 x
    have hid : Real.sqrt s * UnforcedLeray.Cons.C03.rawProfile ε tr.v tr.ψ (s, (ξ, Real.sqrt s * x)) 1
        - ε * (2 * meanCoeff tr 0 * heatKernel1 ν x)
        = Real.sqrt s * tr.v s (ξ, Real.sqrt s * x) 1
          + ε * (Real.sqrt s * UnforcedLeray.Cons.C03.raisedStream
              (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x))
          + ε * (Real.sqrt s * (UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
              - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x))) := by
      rw [UnforcedLeray.Cons.C03.rawProfile_one]
      dsimp only
      rw [hsplit]
      linear_combination (ε * (2 * meanCoeff tr 0)) * hsc
    have hA1 : Real.sqrt s * |tr.v s (ξ, Real.sqrt s * x) 1|
        ≤ (|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) * (Real.sqrt s)⁻¹ :=
      AxisEvTrainDecayAux.sqrt_mul_abs_le_inv hs1 hKv0
        ((AxisEvTrainDecayAux.abs_apply_le_norm _ 1).trans (hv s hs1 ξ (Real.sqrt s * x)))
    have hA2 : Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream
        (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x)|
        ≤ |C3 * ν⁻¹ ^ k3| * (Real.sqrt s)⁻¹ :=
      AxisEvTrainDecayAux.sqrt_mul_abs_le_inv hs1 (abs_nonneg _)
        ((H3 ν m3 _ hc tr hb s hs1 ξ (Real.sqrt s * x)).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.2 (by linarith))))
    have hA3 : Real.sqrt s * |UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
        - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x)|
        ≤ |C4 * ν⁻¹ ^ k4| * (Real.sqrt s)⁻¹ :=
      AxisEvTrainDecayAux.sqrt_mul_abs_le_inv_rpow hs1 (abs_nonneg _)
        ((H4 ν m4 _ hc tr hb s hs1 (Real.sqrt s * x)).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
    have e1 : |Real.sqrt s * tr.v s (ξ, Real.sqrt s * x) 1|
        = Real.sqrt s * |tr.v s (ξ, Real.sqrt s * x) 1| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s)]
    have e2 : |ε * (Real.sqrt s * UnforcedLeray.Cons.C03.raisedStream
        (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x))|
        = |ε| * (Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream
        (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg s)]
    have e3 : |ε * (Real.sqrt s * (UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
        - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x)))|
        = |ε| * (Real.sqrt s * |UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
        - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg s)]
    rw [hid]
    calc |Real.sqrt s * tr.v s (ξ, Real.sqrt s * x) 1
          + ε * (Real.sqrt s * UnforcedLeray.Cons.C03.raisedStream
              (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x))
          + ε * (Real.sqrt s * (UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
              - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x)))|
        ≤ |Real.sqrt s * tr.v s (ξ, Real.sqrt s * x) 1|
          + |ε * (Real.sqrt s * UnforcedLeray.Cons.C03.raisedStream
              (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x))|
          + |ε * (Real.sqrt s * (UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
              - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x)))| :=
          abs_add_three _ _ _
      _ = Real.sqrt s * |tr.v s (ξ, Real.sqrt s * x) 1|
          + |ε| * (Real.sqrt s * |UnforcedLeray.Cons.C03.raisedStream
              (UnforcedLeray.Short.IIIa.fluctStream tr) s ξ (Real.sqrt s * x)|)
          + |ε| * (Real.sqrt s * |UnforcedLeray.Short.IIIa.meanCompletion tr s (Real.sqrt s * x)
              - 2 * meanCoeff tr 0 * heatKernel1 (ν * s) (Real.sqrt s * x)|) := by
          rw [e1, e2, e3]
      _ ≤ (|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) * (Real.sqrt s)⁻¹
          + |ε| * (|C3 * ν⁻¹ ^ k3| * (Real.sqrt s)⁻¹)
          + |ε| * (|C4 * ν⁻¹ ^ k4| * (Real.sqrt s)⁻¹) :=
          add_le_add (add_le_add hA1 (mul_le_mul_of_nonneg_left hA2 (abs_nonneg ε)))
            (mul_le_mul_of_nonneg_left hA3 (abs_nonneg ε))
      _ = ((|C1 * ν⁻¹ ^ k1| + |C2 * ν⁻¹ ^ k2|) + |ε| * |C3 * ν⁻¹ ^ k3|
            + |ε| * |C4 * ν⁻¹ ^ k4|) * (Real.sqrt s)⁻¹ := by ring
      _ ≤ e := hS s hs
