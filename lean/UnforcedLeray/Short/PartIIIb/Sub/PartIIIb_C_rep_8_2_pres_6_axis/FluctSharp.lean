import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateFluctCompletion

/-!
# `PartIII-b:C/rep/8/2/pres/6/axis/1`: the fluctuation is flat at the axis (`axisEvFluctSharp_of`)

Source `the November 2 reference manuscript`:
`sct:fluctuation` (439-446) and the flatness of the fluctuations at the axis (1317-1318).

The completion `(1 - η∂_η - 2s∂_s)ψ̃` is read from the three Part I instances of
`TrainFluctuationDecay` with `(ℓ, j) = (0,0), (1,0), (0,1)` at weight exponent `m = 1`,
where `√(jap 1 (q,η)) = √(1+η²) ≥ max 1 |η|`, so no transverse weight is needed.  The exponential
age decay is absorbed with rate `a = κ ν⁵` (`c = ν⁻²`).  Using `(1+s)·e^{-as} ≤ G (1+s)⁻¹` with
`G = (1 + 2a⁻¹)²` (the square of `IIIa.one_add_mul_exp_neg_le` at `a/2`) gives the power
`(1+s)⁻¹` of the target.  The mean-stream smoothness `hSm` is `(hE ·).1` (`TrainMeanEquations`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace AxisEvFluct

open UnforcedLeray.Short.IIIa

/-- `1 ≤ √(jap 1 (q,η))`, since `jap 1 (q,η) = 1 + η²`. -/
theorem one_le_sqrt_jap_one (q η : ℝ) : 1 ≤ Real.sqrt (UnforcedLeray.Train.jap 1 (q, η)) := by
  apply Real.one_le_sqrt.2
  show (1 : ℝ) ≤ (1 + η ^ 2) ^ 1
  rw [pow_one]
  linarith [sq_nonneg η]

/-- `|η| ≤ √(jap 1 (q,η))`. -/
theorem abs_le_sqrt_jap_one (q η : ℝ) :
    |η| ≤ Real.sqrt (UnforcedLeray.Train.jap 1 (q, η)) := by
  apply Real.abs_le_sqrt
  show η ^ 2 ≤ (1 + η ^ 2) ^ 1
  rw [pow_one]
  linarith

/-- Rates: for `κs ≤ κ` and `c = ν⁻²`, `e^{-κ ν s/c²} ≤ e^{-(κs ν⁵) s}`. -/
theorem expo_le {κ κs ν s c : ℝ} (hc : c = (ν ^ 2)⁻¹) (hκ : κs ≤ κ) (hν : 0 < ν) (hs : 0 ≤ s) :
    Real.exp (-(κ * ν * s / c ^ 2)) ≤ Real.exp (-((κs * ν ^ 5) * s)) := by
  have e : κ * ν * s / c ^ 2 = κ * ν ^ 5 * s := by
    rw [hc, inv_pow, div_inv_eq_mul]
    ring
  rw [e]
  apply Real.exp_le_exp.2
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ (pow_nonneg hν.le 5)) hs

/-- `(1+s) e^{-as} ≤ (1 + 2a⁻¹)² (1+s)⁻¹` for `a > 0`, `s ≥ 0`. -/
theorem decay_inv {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (1 + s) * Real.exp (-(a * s)) ≤ (1 + 2 * a⁻¹) ^ 2 * (1 + s)⁻¹ := by
  have hA : 0 < 1 + s := by linarith
  have hX : (1 + s) * Real.exp (-((a / 2) * s)) ≤ 1 + 2 * a⁻¹ := by
    have h := one_add_mul_exp_neg_le (half_pos ha) hs
    have e : (a / 2)⁻¹ = 2 * a⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [e] at h
    exact h
  have hX0 : 0 ≤ (1 + s) * Real.exp (-((a / 2) * s)) := mul_nonneg hA.le (Real.exp_nonneg _)
  have hG0 : 0 ≤ 1 + 2 * a⁻¹ := by
    have := inv_nonneg.2 ha.le
    linarith
  have hXX : ((1 + s) * Real.exp (-((a / 2) * s))) * ((1 + s) * Real.exp (-((a / 2) * s))) ≤
      (1 + 2 * a⁻¹) ^ 2 := by
    rw [sq]
    exact mul_le_mul hX hX hX0 hG0
  have hexp : Real.exp (-(a * s)) = Real.exp (-((a / 2) * s)) * Real.exp (-((a / 2) * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have key : (1 + s) * ((1 + s) * Real.exp (-(a * s))) ≤ (1 + 2 * a⁻¹) ^ 2 := by
    have e : (1 + s) * ((1 + s) * Real.exp (-(a * s))) =
        ((1 + s) * Real.exp (-((a / 2) * s))) * ((1 + s) * Real.exp (-((a / 2) * s))) := by
      rw [hexp]
      ring
    rw [e]
    exact hXX
  rw [← div_eq_mul_inv, le_div_iff₀ hA]
  have e2 : (1 + s) * Real.exp (-(a * s)) * (1 + s) = (1 + s) * ((1 + s) * Real.exp (-(a * s))) := by
    ring
  rw [e2]
  exact key

end AxisEvFluct

open UnforcedLeray.Short.IIIa

/-- **`PartIII-b:C/rep/8/2/pres/6/axis/1`: the fluctuation completion is flat at the axis**
(source 439-446, 1317-1318): from the Part I fluctuation decay and the mean-stream equations,
the stream completion of `ψ̃` is `O(ν^{-k}(1+s)⁻¹)` for `s ≥ 1` and small `ν`. -/
theorem axisEvFluctSharp_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : AxisEvFluctSharp := by
  have hSm : UnforcedLeray.Short.PartIIa.MeanStreamSmooth :=
    fun nu c hnu hc tr hb => (hE nu c hnu hc tr hb).1
  obtain ⟨C0, N0, κ0, ν0, hC0, hκ0, hν0, H0⟩ := hF 2 (by norm_num) 1 0 0
  obtain ⟨C1, N1, κ1, ν1, hC1, hκ1, hν1, H1⟩ := hF 2 (by norm_num) 1 1 0
  obtain ⟨C2, N2, κ2, ν2, hC2, hκ2, hν2, H2⟩ := hF 2 (by norm_num) 1 0 1
  refine ⟨(|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) *
      (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2,
    2 * (N0 + N1 + N2) + 10, min (min ν0 ν1) (min ν2 1),
    lt_min (lt_min hν0 hν1) (lt_min hν2 one_pos), ?_⟩
  intro ν hν c hc tr hbuc s hs q η
  have hν0' : 0 < ν := hν.1
  have hνa : ν ≤ ν0 := (hν.2.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνb : ν ≤ ν1 := (hν.2.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hνc : ν ≤ ν2 := (hν.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hν1' : ν ≤ 1 := (hν.2.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcT := period_eq_trainPeriod hν0' hc
  subst hcT
  have hc2 : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := hc
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc2]
    positivity
  have hs0 : 0 < s := by linarith only [hs]
  have hA : 0 < 1 + s := by linarith only [hs0]
  have hone : (1 : ℝ) ≤ 1 + s := by linarith only [hs0]
  have hs2 : (0 : ℝ) ≤ 2 * s := mul_nonneg (by norm_num) hs0.le
  have hsm := hSm ν _ hν0' hcpos tr hbuc
  have hH0 := H0 ν hν0' hνa tr hbuc s hs0
  have hH1 := H1 ν hν0' hνb tr hbuc s hs0
  have hH2 := H2 ν hν0' hνc tr hbuc s hs0
  dsimp only at hH0 hH1 hH2
  have ht1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0').2 hν1'
  have hκmpos : 0 < min κ0 (min κ1 κ2) := lt_min hκ0 (lt_min hκ1 hκ2)
  -- differentiability of the fluctuation stream at the age `s > 0`
  have hdiff : DifferentiableAt ℝ (fluctStream tr s) (q, η) := by
    have hG : DifferentiableAt ℝ
        (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) (s, η) :=
      (hsm.contDiffAt (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ)
        (Set.mk_mem_prod hs0 (Set.mem_univ _)))).differentiableAt (by simp)
    have hG2 : DifferentiableAt ℝ
        (fun z : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr s z.2) (q, η) :=
      DifferentiableAt.comp (q, η)
        (g := fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (f := fun z : ℝ × ℝ => (s, z.2)) hG (by fun_prop)
    exact ((tr.isTrain.stream_differentiable s hs0.le) (q, η)).sub hG2
  -- polynomial majorants and their nonnegativity
  have hP0nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC0.le N0 hν0' hcpos.le
  have hP1nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC1.le N1 hν0' hcpos.le
  have hP2nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC2.le N2 hν0' hcpos.le
  have hK0nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := mul_nonneg hP0nn (Real.exp_nonneg _)
  have hK1nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := mul_nonneg hP1nn (Real.exp_nonneg _)
  have hK2nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := mul_nonneg hP2nn (Real.exp_nonneg _)
  -- pointwise bounds from the three Part I instances (weight `√(jap 1) ≥ 1`, `≥ |η|`)
  have hF0 : |fluctStream tr s (q, η)| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK0nn hH0.1.2 (q, η)
    rw [lfc_norm_ageJet_zero, Real.norm_eq_abs] at h
    exact le_trans (le_mul_of_one_le_left (abs_nonneg _) (AxisEvFluct.one_le_sqrt_jap_one q η)) h
  have hF1 : |deriv (fun r => fluctStream tr r (q, η)) s| ≤
      UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK1nn hH1.1.2 (q, η)
    rw [lfc_norm_ageJet_one_zero, Real.norm_eq_abs] at h
    exact le_trans (le_mul_of_one_le_left (abs_nonneg _) (AxisEvFluct.one_le_sqrt_jap_one q η)) h
  have hD2 : |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK2nn hH2.1.2 (q, η)
    rw [lfc_norm_ageJet_zero_one] at h
    exact le_trans (mul_le_mul_of_nonneg_right (AxisEvFluct.abs_le_sqrt_jap_one q η) (norm_nonneg _)) h
  -- the stream completion, split into its three pieces
  have hder := lfc_abs_deriv_le (fluctStream tr s) q η hdiff
  have hraw : |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      |fluctStream tr s (q, η)| + |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
        2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    have h1 : |η * deriv (fun t => fluctStream tr s (q, t)) η +
        2 * s * deriv (fun t => fluctStream tr t (q, η)) s| ≤
        |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
          2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| := by
      calc _ ≤ |η * deriv (fun t => fluctStream tr s (q, t)) η| +
            |2 * s * deriv (fun t => fluctStream tr t (q, η)) s| := abs_add_le _ _
        _ = |η| * |deriv (fun t => fluctStream tr s (q, t)) η| +
            2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs2]
        _ ≤ |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
            2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| :=
          add_le_add (mul_le_mul_of_nonneg_left hder (abs_nonneg η)) le_rfl
    calc _ ≤ |fluctStream tr s (q, η)| + |η * deriv (fun t => fluctStream tr s (q, t)) η +
            2 * s * deriv (fun t => fluctStream tr t (q, η)) s| := abs_sub _ _
      _ ≤ _ := (add_le_add le_rfl h1).trans_eq (add_assoc _ _ _).symm
  have hsF1 : 2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| ≤
      2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) :=
    mul_le_mul_of_nonneg_left hF1 hs2
  have hrawB : |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) +
        2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) := by
    linarith [hraw, hF0, hD2, hsF1]
  -- common rate `a = κ ν⁵` with `κ = min κ0 (min κ1 κ2)`
  have hE0 := AxisEvFluct.expo_le hc2 (min_le_left κ0 (min κ1 κ2)) hν0' hs0.le
  have hE1 := AxisEvFluct.expo_le hc2 ((min_le_right κ0 (min κ1 κ2)).trans (min_le_left κ1 κ2)) hν0' hs0.le
  have hE2 := AxisEvFluct.expo_le hc2 ((min_le_right κ0 (min κ1 κ2)).trans (min_le_right κ1 κ2)) hν0' hs0.le
  have hX0 : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) :=
    mul_le_mul_of_nonneg_left hE0 hP0nn
  have hX1 : UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) :=
    mul_le_mul_of_nonneg_left hE1 hP1nn
  have hX2 : UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) :=
    mul_le_mul_of_nonneg_left hE2 hP2nn
  have hsX1 : 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) * Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) ≤
      2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) :=
    mul_le_mul_of_nonneg_left hX1 hs2
  -- `(1+s) e^{-as}` absorbs the weight `s` and the common exponential
  have hEnn : 0 ≤ Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := Real.exp_nonneg _
  have hQ0 : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hEnn hone) hP0nn
  have hQ2 : UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hEnn hone) hP2nn
  have hQ1 : 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) ≤
      2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
    have hP1E : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := mul_nonneg hP1nn hEnn
    calc 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)))
        ≤ 2 * (1 + s) * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) :=
          mul_le_mul_of_nonneg_right (by linarith) hP1E
      _ = 2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by ring
  have hmain : |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) + UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
        ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
    have eR : (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) + UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
        ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) =
        UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by ring
    rw [eR]
    linarith [hrawB, hX0, hX2, hsX1, hQ0, hQ2, hQ1]
  -- polynomial constants, uniformly in `ν ≤ 1`
  have hP0 : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      |C0| * 3 ^ N0 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    rw [hc2]
    exact le_trans (polyP_le_inv_pow C0 N0 hν0' hν1')
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hP1 : UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      |C1| * 3 ^ N1 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    rw [hc2]
    exact le_trans (polyP_le_inv_pow C1 N1 hν0' hν1')
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hP2 : UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      |C2| * 3 ^ N2 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    rw [hc2]
    exact le_trans (polyP_le_inv_pow C2 N2 hν0' hν1')
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hS : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) + UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
      2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    calc UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) + UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
        ≤ |C0| * 3 ^ N0 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) + |C2| * 3 ^ N2 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) +
            2 * (|C1| * 3 ^ N1 * ν⁻¹ ^ (2 * (N0 + N1 + N2))) :=
          add_le_add (add_le_add hP0 hP2) (mul_le_mul_of_nonneg_left hP1 (by norm_num))
      _ = (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) *
            ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by ring
  -- the decay constant `(1 + 2a⁻¹)²` at `a = κ ν⁵` is at most `(1 + 2κ⁻¹)² ν⁻¹¹⁰`
  have hGle : (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 ≤
      (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 := by
    have ht5 : 1 ≤ ν⁻¹ ^ 5 := one_le_pow₀ ht1
    have e : (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ = (min κ0 (min κ1 κ2))⁻¹ * ν⁻¹ ^ 5 := by
      rw [mul_inv, ← inv_pow]
    have h1 : 1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ ≤
        (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5 := by
      rw [e]
      have key : (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5 =
          1 + 2 * ((min κ0 (min κ1 κ2))⁻¹ * ν⁻¹ ^ 5) + (ν⁻¹ ^ 5 - 1) := by ring
      rw [key]
      linarith only [ht5]
    have hk : 0 ≤ (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ :=
      inv_nonneg.2 (mul_nonneg hκmpos.le (pow_nonneg hν0'.le 5))
    have hnn : 0 ≤ 1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ := by
      linarith only [hk]
    have h2 := pow_le_pow_left₀ hnn h1 2
    calc (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2
        ≤ ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5) ^ 2 := h2
      _ = (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 := by ring
  have hGb := AxisEvFluct.decay_inv (mul_pos hκmpos (pow_pos hν0' 5)) hs0.le
  have hG : (1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) ≤
      (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 * (1 + s)⁻¹ :=
    le_trans hGb (mul_le_mul_of_nonneg_right hGle (inv_nonneg.2 hA.le))
  have hKc : 0 ≤ |C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1) := by positivity
  -- assemble
  calc |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η|
      ≤ (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) + UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
        ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := hmain
    _ ≤ ((|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2))) *
        ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 * (1 + s)⁻¹) :=
        mul_le_mul hS hG (mul_nonneg hA.le (Real.exp_nonneg _))
          (mul_nonneg hKc (pow_nonneg (inv_nonneg.2 hν0'.le) _))
    _ = (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) *
          (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 *
          ν⁻¹ ^ (2 * (N0 + N1 + N2) + 10) * (1 + s)⁻¹ := by
        rw [pow_add]
        ring


end UnforcedLeray.Short.PartIIIb.Concrete
