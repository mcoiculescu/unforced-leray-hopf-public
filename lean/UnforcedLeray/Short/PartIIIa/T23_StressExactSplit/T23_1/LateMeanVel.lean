import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org

/-!
# `PartIII-a:T23/1/2`: the late mean velocity (`lateMeanVel_of`)

Source of record: `the November 2 reference manuscript` lines 2719-2721
(mean velocity of size `(1+s)^{-1}` on transverse scale `√(1+s)`), 397-404 (`sct:mean`) and
447-459 (`sct:expansion`).

Route: the mean equations give `\bar v = (-S_η, 0)`, so `|\bar v| = |S_η|`; the pointwise
Part II bound (`MeanStreamPointwise`) at `(m', b', l') = (0,1,0)` and `(2n,1,0)` with
`n = ⌈m_Z/2⌉₊` bounds `|S_η|` and `|η|^{2n}|S_η|`; the transverse weight is
`W ≤ 2^n (1 + η^{2n}/(1+s)^n)` (`transWeight_le_two_pow`).
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- Norm of a planar vector whose second component vanishes: `‖x‖ = |x_1|`. -/
theorem lmv_norm_of_second_zero (x : EuclideanSpace ℝ (Fin 2)) (h1 : x 1 = 0) :
    ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, h1]
  simp [Real.sqrt_sq_eq_abs]

/-- Component of the normalized horizontal average: `(hmean c f η) i = hmean c (f · i) η`, for
`f` whose horizontal slice at `η` is integrable on every interval. -/
theorem lmv_component (i : Fin 2) (f : UnforcedLeray.Cyl.Plane → EuclideanSpace ℝ (Fin 2))
    (c η : ℝ)
    (hint : IntegrableOn (fun q : ℝ => f (q, η)) (Ioc (-c / 2) (c / 2))) :
    UnforcedLeray.Short.PartI.hmean c f η i =
      UnforcedLeray.Short.PartI.hmean c (fun z => f z i) η := by
  have key : (∫ q in Ioc (-c / 2) (c / 2), f (q, η)) i =
      ∫ q in Ioc (-c / 2) (c / 2), f (q, η) i := by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i) hint
    simpa using this.symm
  simp only [UnforcedLeray.Short.PartI.hmean, PiLp.smul_apply, smul_eq_mul]
  rw [key]

theorem lateMeanVel_of (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hP : UnforcedLeray.Short.PartIIa.MeanStreamPointwise) :
    UnforcedLeray.Short.IIIa.LateMeanVel := by
  intro mZ hmZ
  obtain ⟨C1, M1, ν1, hC1, hν1, H1⟩ := hP 2 0 1 0 (by norm_num)
  obtain ⟨C2, M2, ν2, hC2, hν2, H2⟩ := hP 2 (2 * ⌈mZ / 2⌉₊) 1 0 (by norm_num)
  refine ⟨2 ^ ⌈mZ / 2⌉₊ * (|C1| * 3 ^ M1 + |C2| * 3 ^ M2), 2 * (M1 + M2),
    min (min ν1 ν2) 1, lt_min (lt_min hν1 hν2) one_pos, ?_⟩
  intro ν hν c hc tr hbuc s hs q η
  have hν0 : 0 < ν := hν.1
  have hνa : ν ≤ ν1 := (hν.2.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνb : ν ≤ ν2 := (hν.2.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hν1' : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hcT := period_eq_trainPeriod hν0 hc
  subst hcT
  have hc2 : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := hc
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc2]; positivity
  have hEs := hE ν _ hν0 hcpos tr hbuc
  have hcomp := hEs.2 s (by linarith) η
  have hc0 := hcomp.2.1
  have hc1 := hcomp.2.2
  -- continuity of the velocity along horizontal lines, at the fixed age `s ≥ 1`
  have hcont : Continuous (fun q : ℝ => tr.v s (q, η)) := by
    have hg : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Set.Ici 0 ×ˢ Set.univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hg.comp_continuous (f := fun q : ℝ => (s, (q, η))) (by fun_prop)
      (fun q => Set.mk_mem_prod (show (0 : ℝ) ≤ s by linarith) (Set.mem_univ _))
  have hint : ∀ a b : ℝ, IntegrableOn (fun q : ℝ => tr.v s (q, η)) (Ioc a b) :=
    fun a b => hcont.integrableOn_Ioc
  have hcomp_i : ∀ i : Fin 2,
      UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (tr.v s) η i =
        UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
          (fun z => tr.v s z i) η :=
    fun i => lmv_component i (tr.v s) _ η (hint _ _)
  have hnorm : ‖UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
      (tr.v s) η‖ = |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| := by
    have h1 : UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
        (tr.v s) η 1 = 0 := by
      rw [hcomp_i 1, hc1]
    rw [lmv_norm_of_second_zero _ h1, hcomp_i 0, hc0, abs_neg]
  -- polynomial constants at `c = ν^{-2} = (ν^2)⁻¹`
  have hPb1 : UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) ≤
      |C1| * 3 ^ M1 * ν⁻¹ ^ (2 * M1) := by
    have e : ν ^ (-(2 : ℝ)) = (ν ^ 2)⁻¹ := by
      rw [Real.rpow_neg hν0.le, Real.rpow_two]
    unfold UnforcedLeray.Short.PartIIa.polyConst
    rw [e]
    exact polyP_le_inv_pow C1 M1 hν0 hν1'
  have hPb2 : UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) ≤
      |C2| * 3 ^ M2 * ν⁻¹ ^ (2 * M2) := by
    have e : ν ^ (-(2 : ℝ)) = (ν ^ 2)⁻¹ := by
      rw [Real.rpow_neg hν0.le, Real.rpow_two]
    unfold UnforcedLeray.Short.PartIIa.polyConst
    rw [e]
    exact polyP_le_inv_pow C2 M2 hν0 hν1'
  -- pointwise Part II bounds for the mean stream
  have hS1 : |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
      UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 : ℝ) := by
    have h := H1 ν hν0 hνa tr hbuc s (by linarith) η
    have ex : (((0 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = -1 := by norm_num
    rw [ex] at h
    simp only [pow_zero, one_mul, iteratedDeriv_zero, iteratedDeriv_one] at h
    exact h
  have hS2 : |η| ^ (2 * ⌈mZ / 2⌉₊) *
      |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
      UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) *
        (1 + s) ^ ((⌈mZ / 2⌉₊ : ℝ) - 1) := by
    have h := H2 ν hν0 hνb tr hbuc s (by linarith) η
    have ex : (((2 * ⌈mZ / 2⌉₊ : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) =
        (⌈mZ / 2⌉₊ : ℝ) - 1 := by
      push_cast; ring
    rw [ex] at h
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h
    exact h
  have hη : |η| ^ (2 * ⌈mZ / 2⌉₊) = η ^ (2 * ⌈mZ / 2⌉₊) :=
    Even.pow_abs (even_two_mul _) η
  rw [hη] at hS2
  -- the weight at scale `√(1+s)`
  have hA : 0 < 1 + s := by linarith
  have ht0 : 0 ≤ (1 + s) ^ (-1 : ℝ) := Real.rpow_nonneg hA.le _
  have hkey : (1 + s) ^ ((⌈mZ / 2⌉₊ : ℝ) - 1) =
      (1 + s) ^ (-1 : ℝ) * (1 + s) ^ ⌈mZ / 2⌉₊ := by
    rw [show ((⌈mZ / 2⌉₊ : ℝ) - 1) = -1 + (⌈mZ / 2⌉₊ : ℝ) by ring, Real.rpow_add hA,
      Real.rpow_natCast]
  have hX : 0 < (1 + s) ^ ⌈mZ / 2⌉₊ := pow_pos hA _
  have hdiv : η ^ (2 * ⌈mZ / 2⌉₊) * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|
      / (1 + s) ^ ⌈mZ / 2⌉₊ ≤
      UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 : ℝ) := by
    rw [div_le_iff₀ hX]
    calc η ^ (2 * ⌈mZ / 2⌉₊) * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|
        ≤ UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) *
          (1 + s) ^ ((⌈mZ / 2⌉₊ : ℝ) - 1) := hS2
      _ = UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) *
          (1 + s) ^ (-1 : ℝ) * (1 + s) ^ ⌈mZ / 2⌉₊ := by rw [hkey]; ring
  have hW := transWeight_le_two_pow mZ (s := s) (by linarith) q η
  have hS0 : 0 ≤ |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| :=
    abs_nonneg _
  have hWa : transWeight mZ (s, (q, η)) *
      |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
      2 ^ ⌈mZ / 2⌉₊ * (UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) *
          (1 + s) ^ (-1 : ℝ) +
        UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 : ℝ)) := by
    calc transWeight mZ (s, (q, η)) *
          |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|
        ≤ 2 ^ ⌈mZ / 2⌉₊ * (1 + η ^ (2 * ⌈mZ / 2⌉₊) / (1 + s) ^ ⌈mZ / 2⌉₊) *
          |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| :=
          mul_le_mul_of_nonneg_right hW hS0
      _ = 2 ^ ⌈mZ / 2⌉₊ * (|deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
          η ^ (2 * ⌈mZ / 2⌉₊) *
            |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| /
              (1 + s) ^ ⌈mZ / 2⌉₊) := by ring
      _ ≤ 2 ^ ⌈mZ / 2⌉₊ * (UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) *
          (1 + s) ^ (-1 : ℝ) +
        UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hS1 hdiv) (by positivity)
  -- absorb the constants at `ν ≤ 1`
  have ht1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).2 hν1'
  have hK1 : UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) ≤
      |C1| * 3 ^ M1 * ν⁻¹ ^ (2 * (M1 + M2)) :=
    le_trans hPb1 (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hK2 : UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) ≤
      |C2| * 3 ^ M2 * ν⁻¹ ^ (2 * (M1 + M2)) :=
    le_trans hPb2 (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hsum : UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) ≤
      (|C1| * 3 ^ M1 + |C2| * 3 ^ M2) * ν⁻¹ ^ (2 * (M1 + M2)) := by
    calc _ ≤ |C1| * 3 ^ M1 * ν⁻¹ ^ (2 * (M1 + M2)) + |C2| * 3 ^ M2 * ν⁻¹ ^ (2 * (M1 + M2)) :=
          add_le_add hK1 hK2
      _ = (|C1| * 3 ^ M1 + |C2| * 3 ^ M2) * ν⁻¹ ^ (2 * (M1 + M2)) := by ring
  rw [hnorm]
  calc transWeight mZ (s, (q, η)) *
        |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|
      ≤ 2 ^ ⌈mZ / 2⌉₊ * (UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) *
          (1 + s) ^ (-1 : ℝ) +
        UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 : ℝ)) :=
        hWa
    _ = 2 ^ ⌈mZ / 2⌉₊ * ((UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) +
        UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ)))) * (1 + s) ^ (-1 : ℝ)) := by
        ring
    _ ≤ 2 ^ ⌈mZ / 2⌉₊ * ((|C1| * 3 ^ M1 + |C2| * 3 ^ M2) * ν⁻¹ ^ (2 * (M1 + M2)) *
        (1 + s) ^ (-1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsum ht0
    _ = (2 ^ ⌈mZ / 2⌉₊ * (|C1| * 3 ^ M1 + |C2| * 3 ^ M2)) * ν⁻¹ ^ (2 * (M1 + M2)) *
        (1 + s) ^ (-1 : ℝ) := by ring

end UnforcedLeray.Short.IIIa
