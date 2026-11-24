import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org

/-!
# `PartIII-a:T23/1/3`: the late fluctuation stream completion (`lateFluctCompletion_of`)

Source of record: `the November 2 reference manuscript` lines 2721-2723 (stream
completion) and 2726-2727, 439-446 (`sct:fluctuation` for the stream fluctuation).

The completion of `F = ψ̃` is `F(s,q,η) - η ∂_η F(s,q,η) - 2s ∂_s F(s,q,η)`. Its three pieces are
read from the three Part I instances `(ℓ, j) = (0,0), (1,0), (0,1)` of `TrainFluctuationDecay`, at
weight exponent `m = ⌈m_Z⌉₊ + 1`, which also absorbs the transverse weight times `|η|`
(`lfc_W_eta`). The exponential age decay is absorbed by `lfc_decay_exp` with `a = κ ν^5`
(since `c = ν^{-2}`); the resulting power `(1+s)^{-1/2}` is the target.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- `‖ageJet 0 0 F s z‖ = ‖F s z‖`. -/
theorem lfc_norm_ageJet_zero (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s : ℝ)
    (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 0 F s z‖ = ‖F s z‖ := by
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  simp [norm_iteratedFDeriv_zero, iteratedDeriv_zero]

/-- `‖ageJet 1 0 F s z‖ = |∂_s F(s,z)|`. -/
theorem lfc_norm_ageJet_one_zero (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s : ℝ)
    (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 1 0 F s z‖ = ‖deriv (fun r => F r z) s‖ := by
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  simp [norm_iteratedFDeriv_zero, iteratedDeriv_one]

/-- `‖ageJet 0 1 F s z‖ = ‖D_z F(s,z)‖`. -/
theorem lfc_norm_ageJet_zero_one (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s : ℝ)
    (z : UnforcedLeray.Cyl.Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 1 F s z‖ = ‖fderiv ℝ (F s) z‖ := by
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  simp [norm_iteratedFDeriv_one, iteratedDeriv_zero]

/-- Pointwise reading of a weighted sup bound: `√(jap m z) ‖f z‖ ≤ K`. -/
theorem lfc_pointwise_of_wSup {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    {f : UnforcedLeray.Cyl.Plane → E} {K : ℝ} (hK : 0 ≤ K)
    (h : UnforcedLeray.Short.PartI.wSupNorm m f ≤ ENNReal.ofReal K) (z : UnforcedLeray.Cyl.Plane) :
    Real.sqrt (UnforcedLeray.Train.jap m z) * ‖f z‖ ≤ K := by
  have h1 := (le_iSup
    (fun z : UnforcedLeray.Cyl.Plane =>
      ENNReal.ofReal (Real.sqrt (UnforcedLeray.Train.jap m z)) * ‖f z‖ₑ) z).trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hK).1 h1

/-- The Part I polynomial majorant is nonnegative. -/
theorem lfc_polyP_nonneg {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {ν c : ℝ} (hν : 0 < ν) (hc : 0 ≤ c) :
    0 ≤ UnforcedLeray.Short.PartI.polyP C N ν c := by
  unfold UnforcedLeray.Short.PartI.polyP
  have : 0 ≤ 1 + c + ν⁻¹ := by
    have := inv_nonneg.2 hν.le
    linarith
  exact mul_nonneg hC (pow_nonneg this N)

/-- The transverse weight is at most `√(jap (m+1))`, `m = ⌈m_Z⌉₊` (`jap` is nondecreasing in `m`). -/
theorem lfc_W_le {mZ : ℝ} (hmZ : 0 ≤ mZ) {s : ℝ} (hs : 0 ≤ s) (q η : ℝ) :
    transWeight mZ (s, (q, η)) ≤
      Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) := by
  have h1 := transWeight_le_sqrt_jap hmZ (p := (s, (q, η))) (by show (0 : ℝ) ≤ s; exact hs)
  refine h1.trans (Real.sqrt_le_sqrt ?_)
  show UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η) ≤ UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)
  unfold UnforcedLeray.Train.jap
  rw [pow_succ]
  exact le_mul_of_one_le_right (pow_nonneg (by nlinarith [sq_nonneg η]) _)
    (by nlinarith [sq_nonneg η])

/-- The weight times `|η|` is absorbed by the next jap weight:
`W |η| ≤ √(jap (m+1))`, `m = ⌈m_Z⌉₊`. -/
theorem lfc_W_eta {mZ : ℝ} (hmZ : 0 ≤ mZ) {s : ℝ} (hs : 0 ≤ s) (q η : ℝ) :
    transWeight mZ (s, (q, η)) * |η| ≤
      Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) := by
  have hW := transWeight_le_sqrt_jap hmZ (p := (s, (q, η))) (by show (0 : ℝ) ≤ s; exact hs)
  have hη : |η| ≤ Real.sqrt (1 + η ^ 2) := Real.abs_le_sqrt (by linarith [sq_nonneg η])
  have hjap : UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η) =
      UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η) * (1 + η ^ 2) := by
    unfold UnforcedLeray.Train.jap
    rw [pow_succ]
  have hj0 : 0 ≤ UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η) := by
    unfold UnforcedLeray.Train.jap
    positivity
  calc transWeight mZ (s, (q, η)) * |η|
      ≤ Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η)) * |η| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg _)
    _ ≤ Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η)) * Real.sqrt (1 + η ^ 2) :=
        mul_le_mul_of_nonneg_left hη (Real.sqrt_nonneg _)
    _ = Real.sqrt (UnforcedLeray.Train.jap ⌈mZ⌉₊ (q, η) * (1 + η ^ 2)) :=
        (Real.sqrt_mul hj0 _).symm
    _ = Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) := by rw [hjap]

/-- Horizontal derivative against the gradient: `|∂_η f(q,η)| ≤ ‖D f(q,η)‖`. -/
theorem lfc_abs_deriv_le (f : ℝ × ℝ → ℝ) (q η : ℝ) (hf : DifferentiableAt ℝ f (q, η)) :
    |deriv (fun t => f (q, t)) η| ≤ ‖fderiv ℝ f (q, η)‖ := by
  have hg : HasDerivAt (fun t : ℝ => ((q, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id' η)
  have hcomp := (hf.hasFDerivAt).comp_hasDerivAt η hg
  show |deriv (f ∘ fun t => ((q, t) : ℝ × ℝ)) η| ≤ _
  rw [hcomp.deriv]
  have hn : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  calc |fderiv ℝ f (q, η) ((0 : ℝ), (1 : ℝ))|
      = ‖fderiv ℝ f (q, η) ((0 : ℝ), (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ f (q, η)‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ f (q, η)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hn

/-- The exponential age decay, absorbed with the polynomial weight `(1+s)^{-1/2}` (SP 2726-2727):
for `a > 0`, `s ≥ 0`, both `(1+s) e^{-as}` and `e^{-as}` are at most `(1+2a⁻¹)² (1+s)^{-1/2}`. -/
theorem lfc_decay_exp {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (1 + s) * Real.exp (-(a * s)) ≤ (1 + 2 * a⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ) ∧
      Real.exp (-(a * s)) ≤ (1 + 2 * a⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ) := by
  have hA : 0 < 1 + s := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 + s) ^ (-1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.rpow_nonneg hA.le _
  have hu1 : u ≤ 1 := by
    rw [hu]; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have huu : (1 + s) * (u * u) = 1 := by
    rw [hu, ← Real.rpow_add hA, show (-1 / 2 : ℝ) + (-1 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
    field_simp
  -- `X = (1+s) e^{-(a/2)s} ≤ 1 + 2a⁻¹`
  have hX : (1 + s) * Real.exp (-((a / 2) * s)) ≤ 1 + 2 * a⁻¹ := by
    have h := one_add_mul_exp_neg_le (half_pos ha) hs
    have e : (a / 2)⁻¹ = 2 * a⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [e] at h
    exact h
  have hX0 : 0 ≤ (1 + s) * Real.exp (-((a / 2) * s)) :=
    mul_nonneg hA.le (Real.exp_nonneg _)
  have hXX : ((1 + s) * Real.exp (-((a / 2) * s))) * ((1 + s) * Real.exp (-((a / 2) * s))) ≤
      (1 + 2 * a⁻¹) ^ 2 := by
    rw [sq]
    exact mul_le_mul hX hX hX0 (by have := inv_nonneg.2 ha.le; linarith)
  have hexp : Real.exp (-(a * s)) =
      Real.exp (-((a / 2) * s)) * Real.exp (-((a / 2) * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- `Z = (1+s) e^{-as}` satisfies `(1+s) Z ≤ G`
  have hZG : (1 + s) * ((1 + s) * Real.exp (-(a * s))) ≤ (1 + 2 * a⁻¹) ^ 2 := by
    have e : (1 + s) * ((1 + s) * Real.exp (-(a * s))) =
        ((1 + s) * Real.exp (-((a / 2) * s))) * ((1 + s) * Real.exp (-((a / 2) * s))) := by
      rw [hexp]; ring
    rw [e]
    exact hXX
  have hZ0 : 0 ≤ (1 + s) * Real.exp (-(a * s)) := mul_nonneg hA.le (Real.exp_nonneg _)
  have hG0 : 0 ≤ (1 + 2 * a⁻¹) ^ 2 := by
    have := inv_nonneg.2 ha.le
    positivity
  have hpart1 : (1 + s) * Real.exp (-(a * s)) ≤ (1 + 2 * a⁻¹) ^ 2 * u := by
    calc (1 + s) * Real.exp (-(a * s))
        = (u * u) * ((1 + s) * ((1 + s) * Real.exp (-(a * s)))) := by
          linear_combination (-((1 + s) * Real.exp (-(a * s)))) * huu
      _ ≤ (u * u) * (1 + 2 * a⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hZG (mul_nonneg hu0 hu0)
      _ ≤ u * (1 + 2 * a⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hu0 hu1) hG0
      _ = (1 + 2 * a⁻¹) ^ 2 * u := by ring
  constructor
  · exact hpart1
  · have hy : Real.exp (-(a * s)) ≤ (1 + s) * Real.exp (-(a * s)) :=
      le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith)
    exact hy.trans hpart1

theorem lateFluctCompletion_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hSm : UnforcedLeray.Short.PartIIa.MeanStreamSmooth) :
    UnforcedLeray.Short.IIIa.LateFluctCompletion := by
  intro mZ hmZ
  obtain ⟨C0, N0, κ0, ν0, hC0, hκ0, hν0, H0⟩ := hF 2 (by norm_num) (⌈mZ⌉₊ + 1) 0 0
  obtain ⟨C1, N1, κ1, ν1, hC1, hκ1, hν1, H1⟩ := hF 2 (by norm_num) (⌈mZ⌉₊ + 1) 1 0
  obtain ⟨C2, N2, κ2, ν2, hC2, hκ2, hν2, H2⟩ := hF 2 (by norm_num) (⌈mZ⌉₊ + 1) 0 1
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
    rw [hc2]; positivity
  have hs0 : 0 < s := by linarith only [hs]
  have hA : 0 < 1 + s := by linarith only [hs0]
  have hs2 : (0 : ℝ) ≤ 2 * s := mul_nonneg (by norm_num) hs0.le
  have hsm := hSm ν _ hν0' hcpos tr hbuc
  have hH0 := H0 ν hν0' hνa tr hbuc s hs0
  have hH1 := H1 ν hν0' hνb tr hbuc s hs0
  have hH2 := H2 ν hν0' hνc tr hbuc s hs0
  dsimp only at hH0 hH1 hH2
  have ht1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0').2 hν1'
  have hκpos : 0 < min κ0 (min κ1 κ2) := lt_min hκ0 (lt_min hκ1 hκ2)
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
  -- pointwise bounds from the three Part I instances
  have hK0nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C0 N0 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg (lfc_polyP_nonneg hC0.le N0 hν0' hcpos.le) (Real.exp_nonneg _)
  have hK1nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg (lfc_polyP_nonneg hC1.le N1 hν0' hcpos.le) (Real.exp_nonneg _)
  have hK2nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C2 N2 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg (lfc_polyP_nonneg hC2.le N2 hν0' hcpos.le) (Real.exp_nonneg _)
  have pt0 : Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) * |fluctStream tr s (q, η)| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK0nn hH0.1.2 (q, η)
    rw [lfc_norm_ageJet_zero, Real.norm_eq_abs] at h
    exact h
  have pt1 : Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) *
      |deriv (fun r => fluctStream tr r (q, η)) s| ≤
      UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK1nn hH1.1.2 (q, η)
    rw [lfc_norm_ageJet_one_zero, Real.norm_eq_abs] at h
    exact h
  have pt2 : Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) *
      ‖fderiv ℝ (fluctStream tr s) (q, η)‖ ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK2nn hH2.1.2 (q, η)
    rw [lfc_norm_ageJet_zero_one] at h
    exact h
  -- weights
  have hWM := lfc_W_le hmZ hs0.le q η
  have hWη := lfc_W_eta hmZ hs0.le q η
  have hW0 := transWeight_nonneg mZ (s, (q, η))
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
  -- the three terms, weighted
  have e0 : transWeight mZ (s, (q, η)) * |fluctStream tr s (q, η)| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hWM (abs_nonneg _)) pt0
  have e2 : transWeight mZ (s, (q, η)) * |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hWη (norm_nonneg _)) pt2
  have e1' : transWeight mZ (s, (q, η)) * |deriv (fun t => fluctStream tr t (q, η)) s| ≤
      UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hWM (abs_nonneg _)) pt1
  have e1 : 2 * s * (transWeight mZ (s, (q, η)) * |deriv (fun t => fluctStream tr t (q, η)) s|) ≤
      2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) :=
    mul_le_mul_of_nonneg_left e1' hs2
  have hmain : transWeight mZ (s, (q, η)) *
      |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) +
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) +
      2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) := by
    have hW0' := mul_le_mul_of_nonneg_left hraw hW0
    have hsplit : transWeight mZ (s, (q, η)) *
        (|fluctStream tr s (q, η)| + |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
          2 * s * |deriv (fun t => fluctStream tr t (q, η)) s|) =
        transWeight mZ (s, (q, η)) * |fluctStream tr s (q, η)| +
          transWeight mZ (s, (q, η)) * |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
          2 * s * (transWeight mZ (s, (q, η)) * |deriv (fun t => fluctStream tr t (q, η)) s|) := by
      ring
    exact le_trans hW0' (hsplit ▸ add_le_add (add_le_add e0 e2) e1)
  -- age decay with the common rate `κ = min κ0 (min κ1 κ2)`
  have eE0 : Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := by
    have e : κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 = κ0 * ν ^ 5 * s := by
      rw [hc2, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left κ0 (min κ1 κ2)) (pow_nonneg hν0'.le 5)) hs0.le)
  have eE1 : Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := by
    have e : κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 = κ1 * ν ^ 5 * s := by
      rw [hc2, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((min_le_right κ0 (min κ1 κ2)).trans (min_le_left κ1 κ2))
        (pow_nonneg hν0'.le 5)) hs0.le)
  have eE2 : Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := by
    have e : κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 = κ2 * ν ^ 5 * s := by
      rw [hc2, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((min_le_right κ0 (min κ1 κ2)).trans (min_le_right κ1 κ2))
        (pow_nonneg hν0'.le 5)) hs0.le)
  have hdec := lfc_decay_exp (mul_pos hκpos (pow_pos hν0' 5)) hs0.le
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
  have hP0nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C0 N0 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC0.le N0 hν0' hcpos.le
  have hP1nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC1.le N1 hν0' hcpos.le
  have hP2nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C2 N2 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC2.le N2 hν0' hcpos.le
  have hPsum : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
      2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    have h := add_le_add (add_le_add hP0 hP2)
      (mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ) ≤ 2))
    exact h.trans_eq (by ring)
  -- the decay constant `G = (1 + 2a⁻¹)²` at `a = κ ν^5`, with `a⁻¹ ≤ κ⁻¹ ν^{-5}`
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
      inv_nonneg.2 (mul_nonneg hκpos.le (pow_nonneg hν0'.le 5))
    have hnn : 0 ≤ 1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ := by
      linarith only [hk]
    have h2 := pow_le_pow_left₀ hnn h1 2
    calc (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2
        ≤ ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5) ^ 2 := h2
      _ = (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 := by ring
  have hu0 : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hA.le _
  have hG0 : 0 ≤ (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 := by positivity
  have hQ : 0 ≤ ν⁻¹ ^ (2 * (N0 + N1 + N2)) := pow_nonneg (inv_nonneg.2 hν0'.le) _
  have hKc : 0 ≤ |C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1) := by positivity
  -- assemble
  have hstep1 : transWeight mZ (s, (q, η)) *
        |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
    have f0 := mul_le_mul_of_nonneg_left eE0 hP0nn
    have f2 := mul_le_mul_of_nonneg_left eE2 hP2nn
    have f1 : 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
        (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) ≤
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
      have a1 := mul_le_mul_of_nonneg_left eE1 hP1nn
      have a2 := mul_le_mul_of_nonneg_left a1 hs2
      have a3 : 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
          (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) ≤
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
        have hid : 2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν
            (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) =
            2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
              (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
              Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) +
            2 * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
              (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
              Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by ring
        rw [hid]
        exact le_add_of_nonneg_right
          (mul_nonneg (by norm_num) (mul_nonneg hP1nn (Real.exp_nonneg _)))
      exact le_trans a2 a3
    exact le_trans hmain (add_le_add (add_le_add f0 f2) f1)
  have hstep2 : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) := by
    have g0 := mul_le_mul_of_nonneg_left hdec.2 hP0nn
    have g2 := mul_le_mul_of_nonneg_left hdec.2 hP2nn
    have g1 := mul_le_mul_of_nonneg_left hdec.1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP1nn)
    exact add_le_add (add_le_add g0 g2) g1
  have hstep3 : (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) ≤
      ((|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2))) *
          ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 * (1 + s) ^ (-1 / 2 : ℝ)) :=
    mul_le_mul hPsum (mul_le_mul_of_nonneg_right hGle hu0) (mul_nonneg hG0 hu0) (mul_nonneg hKc hQ)
  have hlast : ((|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2))) *
          ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 * (1 + s) ^ (-1 / 2 : ℝ)) =
      (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) *
          (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 *
          ν⁻¹ ^ (2 * (N0 + N1 + N2) + 10) * (1 + s) ^ (-1 / 2 : ℝ) := by
    rw [pow_add]; ring
  have hmid : (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) =
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) := by
    ring
  exact le_trans hstep1 (le_trans hstep2 (le_trans (le_of_eq hmid.symm)
    (le_trans hstep3 (le_of_eq hlast))))

end UnforcedLeray.Short.IIIa
