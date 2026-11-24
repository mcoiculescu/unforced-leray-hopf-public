import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartI.StatementsTrain
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

/-!


Proves `LateMeanCoeff` (`Sub/R02.lean`) from `TrainFluctuationDecay` (`sct:fluctuation`,
source `the November 2 reference manuscript` lines 439-446, sup-norm part only) and
`TrainMeanEquations` (`sct:mean`, lines 397-404), using the coefficient formula of `sct:expansion`
(`meanCoeff`, `StatementsTrain.lean` line 111; source lines 450-453).

Route, for `0 < ν ≤ min ν₀ 1` and `c = ν^{-ρ} ≥ 1`:
* `meanCoeff tr j = A + B`, `A = (∫ η^{2j} S(0,η)) / (2j)!`,
  `B = ∫_{t>0} ∑_{k+l=j} (-(νt))^l/(l!(2k)!) ∫ η^{2k} g(t,η) dη dt`.
* `S(0) = hmean c (trainStream c)` (`IsTrain.stream_zero`) and `|trainStream c z| ≤ 20 e^{-η²/4}`
  (`abs_trainStream_le`), so `|A| ≤ C_A / (2j)!` with `C_A` a fixed Gaussian integral.
* For `t > 0`, `hmean c (v₂) = 0` (`sct:mean`) gives `g(t,·) = c⁻¹ ∫_q ṽ₁ v₂`, and
  `|g(t,η)| ≤ K_t² / (1+η²)^{j+1}` by the sup-norm part of `sct:fluctuation` (with `m = j+1`).
* `|∫ η^{2k} g dη| ≤ π K_t²` and `∫_{t>0} t^l e^{-λt} = l! (1/λ)^{l+1}` with `λ = 2κν/c²`;
  `1/λ = c² ν⁻¹ /(2κ)` is polynomial in `c, ν⁻¹`, and `ν^l ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (meanStream meanStress meanCoeff hmean hfluct ageJet wSupNorm
  trainPeriod polyP)
open UnforcedLeray.Train (jap jet)

/-! ### Continuity and the horizontal mean -/

theorem lmc_slice_continuous {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) : Continuous (fun z : ℝ × ℝ => tr.v s z) := by
  have h : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici (0 : ℝ) ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hc : Continuous (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ))) :=
    continuous_const.prodMk continuous_id
  exact h.comp_continuous hc (fun z => mk_mem_prod (mem_Ici.mpr hs) (mem_univ _))

/-- The horizontal mean commutes with the component `1`. -/
theorem lmc_hmean_apply_one {c : ℝ} (a : ℝ × ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Continuous a) (η : ℝ) :
    hmean c a η 1 = hmean c (fun z => a z 1) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

/-- A zero horizontal mean gives a zero integral over the cell. -/
theorem lmc_integral_eq_zero {c η : ℝ} (hc : c ≠ 0) (f : ℝ × ℝ → ℝ) (h : hmean c f η = 0) :
    ∫ q in Ioc (-c / 2) (c / 2), f (q, η) = 0 := by
  unfold hmean at h
  rcases smul_eq_zero.mp h with h1 | h1
  · exact absurd (inv_eq_zero.mp h1) hc
  · exact h1

/-! ### From the sup-norm bound to a pointwise bound -/

theorem lmc_pt_of_sup {E : Type*} [NormedAddCommGroup E] (m : ℕ) (f : ℝ × ℝ → E) {K : ℝ}
    (hK : 0 ≤ K) (h : wSupNorm m f ≤ ENNReal.ofReal K) (z : ℝ × ℝ) :
    jap m z * ‖f z‖ ^ 2 ≤ K ^ 2 := by
  have h1 : ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ ≤ ENNReal.ofReal K :=
    le_trans (le_iSup (fun w : ℝ × ℝ => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z) h
  have hj : (0 : ℝ) ≤ jap m z := by unfold jap; positivity
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hK] at h1
  have hs : Real.sqrt (jap m z) ^ 2 = jap m z := Real.sq_sqrt hj
  calc jap m z * ‖f z‖ ^ 2 = (Real.sqrt (jap m z) * ‖f z‖) ^ 2 := by rw [mul_pow, hs]
    _ ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) h1 2

theorem lmc_norm_ageJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → ℝ × ℝ → E) (t : ℝ) (z : ℝ × ℝ) :
    ‖ageJet 0 0 F t z‖ = ‖F t z‖ := by
  simp [ageJet, jet, iteratedDeriv_zero, norm_iteratedFDeriv_zero]

/-! ### The mean stress is bounded pointwise in `η` -/

theorem lmc_meanStress_bound {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (hc : 0 < c)
    {t : ℝ} (ht : 0 ≤ t) (hE3 : ∀ η : ℝ, hmean c (fun z => tr.v t z 1) η = 0) {m : ℕ} {K : ℝ}
    (hpt : ∀ z : ℝ × ℝ, jap m z * ‖hfluct c (tr.v t) z‖ ^ 2 ≤ K ^ 2) (η : ℝ) :
    ‖meanStress tr t η‖ ≤ K ^ 2 / (1 + η ^ 2) ^ m := by
  have hcont : Continuous (fun z : ℝ × ℝ => tr.v t z) := lmc_slice_continuous tr ht
  have hqcont : Continuous (fun q : ℝ => tr.v t (q, η)) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hqi : ∀ i : Fin 2, Continuous (fun q : ℝ => tr.v t (q, η) i) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp hqcont
  have hā1 : hmean c (tr.v t) η 1 = 0 := by
    rw [lmc_hmean_apply_one (tr.v t) hcont η]
    exact hE3 η
  have hJ : (0 : ℝ) < (1 + η ^ 2) ^ m := by positivity
  have hcne : c ≠ 0 := hc.ne'
  have hwb : ∀ q : ℝ, ‖tr.v t (q, η) - hmean c (tr.v t) η‖ ^ 2 ≤ K ^ 2 / (1 + η ^ 2) ^ m := by
    intro q
    have h := hpt (q, η)
    rw [le_div_iff₀ hJ, mul_comm]
    exact h
  set w : ℝ → EuclideanSpace ℝ (Fin 2) := fun q => tr.v t (q, η) - hmean c (tr.v t) η with hw
  have hwi : ∀ i : Fin 2, Continuous (fun q => w q i) := fun i => by
    have h1 : Continuous (fun q : ℝ => tr.v t (q, η) - hmean c (tr.v t) η) :=
      hqcont.sub continuous_const
    have h2 : Continuous (fun q : ℝ => (tr.v t (q, η) - hmean c (tr.v t) η) i) :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp h1
    exact h2
  -- pointwise identity `v₁ v₂ = w₁ w₂ + v̄₁ v₂` with `w₂ = v₂` (since `v̄₂ = 0`)
  have hid : ∀ q : ℝ, tr.v t (q, η) 0 * tr.v t (q, η) 1 =
      w q 0 * w q 1 + hmean c (tr.v t) η 0 * tr.v t (q, η) 1 := by
    intro q
    have h1 : w q 1 = tr.v t (q, η) 1 := by
      simp only [hw, PiLp.sub_apply, hā1, sub_zero]
    have h0 : w q 0 = tr.v t (q, η) 0 - hmean c (tr.v t) η 0 := by
      simp only [hw, PiLp.sub_apply]
    rw [h1, h0]
    ring
  have hI1 : Integrable (fun q : ℝ => w q 0 * w q 1) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    ((hwi 0).mul (hwi 1)).integrableOn_Ioc
  have hI2 : Integrable (fun q : ℝ => hmean c (tr.v t) η 0 * tr.v t (q, η) 1)
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (continuous_const.mul (hqi 1)).integrableOn_Ioc
  have hv1 : ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 1 = 0 :=
    lmc_integral_eq_zero hcne (fun z => tr.v t z 1) (hE3 η)
  have hmain : ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 0 * tr.v t (q, η) 1 =
      ∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1 := by
    calc ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 0 * tr.v t (q, η) 1
        = ∫ q in Ioc (-c / 2) (c / 2), (w q 0 * w q 1 + hmean c (tr.v t) η 0 * tr.v t (q, η) 1) := by
          congr 1
          funext q
          exact hid q
      _ = (∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1) +
            hmean c (tr.v t) η 0 * ∫ q in Ioc (-c / 2) (c / 2), tr.v t (q, η) 1 := by
          rw [integral_add hI1 hI2, integral_const_mul]
      _ = ∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1 := by rw [hv1, mul_zero, add_zero]
  have hbd : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖w q 0 * w q 1‖ ≤ K ^ 2 / (1 + η ^ 2) ^ m := by
    intro q _
    rw [norm_mul]
    have h0 := PiLp.norm_apply_le (w q) 0
    have h1 := PiLp.norm_apply_le (w q) 1
    calc ‖w q 0‖ * ‖w q 1‖ ≤ ‖w q‖ * ‖w q‖ := mul_le_mul h0 h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖w q‖ ^ 2 := (sq _).symm
      _ ≤ K ^ 2 / (1 + η ^ 2) ^ m := hwb q
  have hint_bd : ‖∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1‖ ≤
      K ^ 2 / (1 + η ^ 2) ^ m * c := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (-c / 2) (c / 2)) (measure_Ioc_lt_top) hbd
    rw [Real.volume_real_Ioc_of_le (by linarith)] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hms : meanStress tr t η = c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1 := by
    rw [← hmain]
    unfold meanStress hmean
    rw [smul_eq_mul]
  rw [hms, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), w q 0 * w q 1‖
      ≤ c⁻¹ * (K ^ 2 / (1 + η ^ 2) ^ m * c) :=
        mul_le_mul_of_nonneg_left hint_bd (inv_nonneg.mpr hc.le)
    _ = K ^ 2 / (1 + η ^ 2) ^ m := by field_simp

/-! ### The `η`-integral of `η^{2k} g(t,·)` -/

theorem lmc_eta_integral_bound {k j : ℕ} (hkj : k ≤ j) {K : ℝ} (G : ℝ → ℝ)
    (hG : ∀ η : ℝ, ‖G η‖ ≤ K ^ 2 / (1 + η ^ 2) ^ (j + 1)) :
    ‖∫ η : ℝ, η ^ (2 * k) * G η‖ ≤ Real.pi * K ^ 2 := by
  have hg : Integrable (fun η : ℝ => K ^ 2 * (1 + η ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hpt : ∀ η : ℝ, ‖η ^ (2 * k) * G η‖ ≤ K ^ 2 * (1 + η ^ 2)⁻¹ := by
    intro η
    have hpos : 0 ≤ η ^ (2 * k) := by rw [pow_mul]; positivity
    have hle : η ^ (2 * k) ≤ (1 + η ^ 2) ^ j := by
      calc η ^ (2 * k) = (η ^ 2) ^ k := by rw [pow_mul]
        _ ≤ (1 + η ^ 2) ^ k := pow_le_pow_left₀ (sq_nonneg η) (by linarith) k
        _ ≤ (1 + η ^ 2) ^ j := pow_le_pow_right₀ (by nlinarith [sq_nonneg η]) hkj
    have h1 : (0 : ℝ) < 1 + η ^ 2 := by positivity
    rw [norm_mul, Real.norm_of_nonneg hpos]
    calc η ^ (2 * k) * ‖G η‖ ≤ (1 + η ^ 2) ^ j * (K ^ 2 / (1 + η ^ 2) ^ (j + 1)) :=
          mul_le_mul hle (hG η) (norm_nonneg _) (by positivity)
      _ = K ^ 2 * (1 + η ^ 2)⁻¹ := by
          rw [pow_succ]
          field_simp
          ring
  calc ‖∫ η : ℝ, η ^ (2 * k) * G η‖ ≤ ∫ η : ℝ, K ^ 2 * (1 + η ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
    _ = Real.pi * K ^ 2 := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
        ring

/-! ### Gaussian and time integrals -/

theorem lmc_gauss_integrable (j : ℕ) :
    Integrable (fun η : ℝ => η ^ (2 * j) * Real.exp (-(η ^ 2 / 4))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)
    (s := ((2 * j : ℕ) : ℝ))
    (by have : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  refine h.congr (Filter.Eventually.of_forall fun η => ?_)
  simp only [Real.rpow_natCast]
  ring_nf

theorem lmc_integrable_pow_mul_exp (l : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => t ^ l * Real.exp (-(lam * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (l : ℝ)) (b := lam)
    (by have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _; linarith) one_pos hlam
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]

theorem lmc_integral_pow_mul_exp (l : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∫ t in Ioi (0 : ℝ), t ^ l * Real.exp (-(lam * t)) =
      (l.factorial : ℝ) * (1 / lam) ^ (l + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (l : ℝ)) (b := lam) one_pos
    (by have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _; linarith) hlam
  have h2 : (fun t : ℝ => t ^ l * Real.exp (-(lam * t))) =
      (fun t : ℝ => t ^ (l : ℝ) * Real.exp (-lam * t ^ (1 : ℝ))) := by
    funext t
    simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]
  rw [h2, h]
  have hG : Real.Gamma ((l : ℝ) + 1) = (l.factorial : ℝ) := Real.Gamma_nat_eq_factorial l
  have hpow : lam ^ (-((l : ℝ) + 1)) = (lam ^ (l + 1))⁻¹ := by
    rw [show -((l : ℝ) + 1) = -(((l + 1 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_neg hlam.le,
      Real.rpow_natCast]
  simp only [div_one, hG, hpow, one_div, inv_pow]
  ring

/-! ### Algebra of the coefficient terms -/

theorem lmc_term_poly (l k j N : ℕ) (hlj : l ≤ j) {ν κ c C X P : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hκ : 0 < κ) (hc : 0 < c) (hcX : c ≤ X) (hνX : ν⁻¹ ≤ X) (hX1 : 1 ≤ X)
    (hPsq : P ^ 2 = C ^ 2 * X ^ (2 * N)) :
    (Real.pi * P ^ 2 * ν ^ l / ((l.factorial : ℝ) * ((2 * k).factorial : ℝ))) *
        ((l.factorial : ℝ) * (1 / (2 * κ * ν / c ^ 2)) ^ (l + 1)) ≤
      Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * X ^ (2 * N + 3 * j + 3) *
        (1 / ((2 * k).factorial : ℝ)) := by
  have hl : (0 : ℝ) < (l.factorial : ℝ) := by positivity
  have hk : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hνne : ν ≠ 0 := hν.ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hcne : c ≠ 0 := hc.ne'
  have hY : 1 / (2 * κ * ν / c ^ 2) = c ^ 2 * ν⁻¹ * (1 / (2 * κ)) := by
    field_simp
  have hX0 : 0 ≤ X := by linarith
  have hc0 : 0 ≤ c := hc.le
  have hν0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0 hcX 2
  have h2 : 1 / (2 * κ) ≤ 1 + κ⁻¹ := by
    have e : 1 / (2 * κ) = 2⁻¹ * κ⁻¹ := by
      rw [one_div, mul_inv]
    rw [e]
    nlinarith
  have hYle : 1 / (2 * κ * ν / c ^ 2) ≤ (1 + κ⁻¹) * X ^ 3 := by
    rw [hY]
    have h1 : c ^ 2 * ν⁻¹ ≤ X ^ 3 := by
      calc c ^ 2 * ν⁻¹ ≤ X ^ 2 * X := mul_le_mul hc2 hνX hν0 (by positivity)
        _ = X ^ 3 := by ring
    have h1' : 0 ≤ c ^ 2 * ν⁻¹ := by positivity
    have h2' : 0 ≤ 1 / (2 * κ) := by positivity
    calc c ^ 2 * ν⁻¹ * (1 / (2 * κ)) ≤ X ^ 3 * (1 + κ⁻¹) :=
          mul_le_mul h1 h2 h2' (by positivity)
      _ = (1 + κ⁻¹) * X ^ 3 := by ring
  have hY0 : 0 ≤ 1 / (2 * κ * ν / c ^ 2) := by positivity
  have hZ1 : 1 ≤ (1 + κ⁻¹) * X ^ 3 := by
    have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    nlinarith
  have hpow : (1 / (2 * κ * ν / c ^ 2)) ^ (l + 1) ≤ ((1 + κ⁻¹) * X ^ 3) ^ (j + 1) :=
    (pow_le_pow_left₀ hY0 hYle (l + 1)).trans (pow_le_pow_right₀ hZ1 (by omega))
  have hνl : ν ^ l ≤ 1 := pow_le_one₀ hν.le hν1
  have hP0 : 0 ≤ Real.pi * C ^ 2 * X ^ (2 * N) :=
    mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg C)) (pow_nonneg hX0 _)
  calc (Real.pi * P ^ 2 * ν ^ l / ((l.factorial : ℝ) * ((2 * k).factorial : ℝ))) *
        ((l.factorial : ℝ) * (1 / (2 * κ * ν / c ^ 2)) ^ (l + 1))
      = (Real.pi * C ^ 2 * X ^ (2 * N)) * (ν ^ l * (1 / (2 * κ * ν / c ^ 2)) ^ (l + 1)) *
          (1 / ((2 * k).factorial : ℝ)) := by
        rw [hPsq]
        field_simp
    _ ≤ (Real.pi * C ^ 2 * X ^ (2 * N)) * (1 * ((1 + κ⁻¹) * X ^ 3) ^ (j + 1)) *
          (1 / ((2 * k).factorial : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hP0
        exact mul_le_mul hνl hpow (pow_nonneg hY0 _) zero_le_one
    _ = Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * X ^ (2 * N + 3 * j + 3) *
        (1 / ((2 * k).factorial : ℝ)) := by
          rw [mul_pow, ← pow_mul]
          ring

/-! ### The bound at a fixed viscosity and period -/

theorem lmc_aux {ν c C κ CA D : ℝ} {N j : ℕ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hc1 : 1 ≤ c) (hC : 0 < C) (hκ : 0 < κ)
    (hCA : CA = ∫ η : ℝ, 20 * (η ^ (2 * j) * Real.exp (-(η ^ 2 / 4))))
    (hD : D = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, 1 / ((2 * kl.1).factorial : ℝ))
    (hE3 : ∀ t : ℝ, 0 < t → ∀ η : ℝ, hmean c (fun z => tr.v t z 1) η = 0)
    (hsup : ∀ t : ℝ, 0 < t → ∀ z : ℝ × ℝ,
      jap (j + 1) z * ‖hfluct c (tr.v t) z‖ ^ 2 ≤
        (polyP C N ν c * Real.exp (-(κ * ν * t / c ^ 2))) ^ 2) :
    |meanCoeff tr j| ≤
      polyConst (CA / ((2 * j).factorial : ℝ) + Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * D)
        (2 * N + 3 * j + 3) ν c := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hν0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  set X : ℝ := 1 + c + ν⁻¹ with hX_def
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hcX : c ≤ X := by linarith
  have hνX : ν⁻¹ ≤ X := by linarith
  set P : ℝ := polyP C N ν c with hP_def
  have hP : P = C * X ^ N := rfl
  have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg hC.le (pow_nonneg hX0 N)
  have hPsq : P ^ 2 = C ^ 2 * X ^ (2 * N) := by rw [hP]; ring
  have hκν : 0 < 2 * κ * ν / c ^ 2 :=
    div_pos (mul_pos (mul_pos two_pos hκ) hν) (pow_pos hc0 2)
  -- the pointwise-in-time bound on the `t`-integrand
  have hFt : ∀ t : ℝ, 0 < t →
      ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
          ((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
            ∫ η : ℝ, η ^ (2 * kl.1) * meanStress tr t η‖ ≤
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
          (Real.pi * P ^ 2 * ν ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
            (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t))) := by
    intro t ht
    have hK0 : 0 ≤ P * Real.exp (-(κ * ν * t / c ^ 2)) :=
      mul_nonneg hP0 (Real.exp_pos _).le
    have hG : ∀ η : ℝ, ‖meanStress tr t η‖ ≤
        (P * Real.exp (-(κ * ν * t / c ^ 2))) ^ 2 / (1 + η ^ 2) ^ (j + 1) :=
      fun η => lmc_meanStress_bound tr hc0 ht.le (hE3 t ht) (hsup t ht) η
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun kl hkl => ?_)
    have hkl' := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
    have hI := lmc_eta_integral_bound (K := P * Real.exp (-(κ * ν * t / c ^ 2)))
      (k := kl.1) (j := j) (by omega) (fun η => meanStress tr t η) hG
    have hexp : Real.exp (-(κ * ν * t / c ^ 2)) ^ 2 =
        Real.exp (-((2 * κ * ν / c ^ 2) * t)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hA : ‖(-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))‖ =
        ν ^ kl.2 * t ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ)) := by
      have hf : (0 : ℝ) ≤ (kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ) := by positivity
      rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg (mul_nonneg hν.le ht.le),
        Real.norm_of_nonneg hf, mul_pow]
    rw [norm_mul, hA]
    calc ν ^ kl.2 * t ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ)) *
          ‖∫ η : ℝ, η ^ (2 * kl.1) * meanStress tr t η‖
        ≤ ν ^ kl.2 * t ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ)) *
            (Real.pi * (P * Real.exp (-(κ * ν * t / c ^ 2))) ^ 2) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = (Real.pi * P ^ 2 * ν ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
            (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t))) := by
          rw [mul_pow, ← hexp]
          ring
  -- the Gaussian term `A`
  have hcne : c ≠ 0 := hc0.ne'
  have hS0 : ∀ η : ℝ, meanStream tr 0 η = hmean c (UnforcedLeray.B0140.trainStream c) η := by
    intro η
    unfold meanStream
    rw [tr.isTrain.stream_zero hc1]
  have hSbd : ∀ η : ℝ, ‖meanStream tr 0 η‖ ≤ 20 * Real.exp (-(η ^ 2 / 4)) := by
    intro η
    rw [hS0 η]
    unfold hmean
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0]
    have hpt2 : ∀ q ∈ Ioc (-c / 2) (c / 2),
        ‖UnforcedLeray.B0140.trainStream c (q, η)‖ ≤ 20 * Real.exp (-(η ^ 2 / 4)) := by
      intro q _
      rw [Real.norm_eq_abs]
      exact UnforcedLeray.B0140.abs_trainStream_le hc1 (q, η)
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => UnforcedLeray.B0140.trainStream c (q, η)) measure_Ioc_lt_top hpt2
    rw [Real.volume_real_Ioc_of_le (by linarith)] at h
    calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), UnforcedLeray.B0140.trainStream c (q, η)‖
        ≤ c⁻¹ * (20 * Real.exp (-(η ^ 2 / 4)) * (c / 2 - -c / 2)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc0.le)
      _ = 20 * Real.exp (-(η ^ 2 / 4)) := by
          rw [show c / 2 - -c / 2 = c by ring]
          field_simp
  have hAint : ‖∫ η : ℝ, η ^ (2 * j) * meanStream tr 0 η‖ ≤ CA := by
    rw [hCA]
    refine norm_integral_le_of_norm_le ((lmc_gauss_integrable j).const_mul 20)
      (Filter.Eventually.of_forall fun η => ?_)
    have hpos : 0 ≤ η ^ (2 * j) := by rw [pow_mul]; positivity
    rw [norm_mul, Real.norm_of_nonneg hpos]
    calc η ^ (2 * j) * ‖meanStream tr 0 η‖
        ≤ η ^ (2 * j) * (20 * Real.exp (-(η ^ 2 / 4))) :=
          mul_le_mul_of_nonneg_left (hSbd η) hpos
      _ = 20 * (η ^ (2 * j) * Real.exp (-(η ^ 2 / 4))) := by ring
  have hfac : (0 : ℝ) < ((2 * j).factorial : ℝ) := by positivity
  have hAbd : |(∫ η : ℝ, η ^ (2 * j) * meanStream tr 0 η) / ((2 * j).factorial : ℝ)| ≤
      CA / ((2 * j).factorial : ℝ) := by
    rw [abs_div, abs_of_pos hfac]
    exact div_le_div_of_nonneg_right (by rw [← Real.norm_eq_abs]; exact hAint) hfac.le
  -- the time integral `B`
  have hgi : Integrable (fun t : ℝ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      (Real.pi * P ^ 2 * ν ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
        (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t)))) (volume.restrict (Ioi 0)) :=
    integrable_finsetSum _ (fun kl _ =>
      Integrable.const_mul (lmc_integrable_pow_mul_exp kl.2 hκν) _)
  have hgsplit : ∫ t in Ioi (0 : ℝ), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      (Real.pi * P ^ 2 * ν ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
        (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t))) =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
        ∫ t in Ioi (0 : ℝ), (Real.pi * P ^ 2 * ν ^ kl.2 /
          ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
            (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t))) :=
    integral_finsetSum _ (fun kl _ => Integrable.const_mul (lmc_integrable_pow_mul_exp kl.2 hκν) _)
  have hterm : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      ∫ t in Ioi (0 : ℝ), (Real.pi * P ^ 2 * ν ^ kl.2 /
          ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
            (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t))) ≤
        Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * X ^ (2 * N + 3 * j + 3) *
          (1 / ((2 * kl.1).factorial : ℝ)) := by
    intro kl hkl
    have hkj : kl.2 ≤ j := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
      omega
    rw [integral_const_mul, lmc_integral_pow_mul_exp kl.2 hκν]
    exact lmc_term_poly kl.2 kl.1 j N hkj hν hν1 hκ hc0 hcX hνX hX1 hPsq
  have hgint : ∫ t in Ioi (0 : ℝ), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      (Real.pi * P ^ 2 * ν ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
        (t ^ kl.2 * Real.exp (-((2 * κ * ν / c ^ 2) * t))) ≤
      Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * X ^ (2 * N + 3 * j + 3) * D := by
    rw [hgsplit, hD, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hB0 := norm_integral_le_of_norm_le hgi
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hFt t ht))
  have hB' := hB0.trans hgint
  rw [Real.norm_eq_abs] at hB'
  -- assembly
  unfold UnforcedLeray.Short.PartI.meanCoeff
  refine (abs_add_le _ _).trans ((add_le_add hAbd hB').trans ?_)
  have hXpow : 1 ≤ X ^ (2 * N + 3 * j + 3) := one_le_pow₀ hX1
  have hCAq : 0 ≤ CA / ((2 * j).factorial : ℝ) := by
    apply div_nonneg _ hfac.le
    rw [hCA]
    apply integral_nonneg
    intro η
    have hpos : 0 ≤ η ^ (2 * j) := by rw [pow_mul]; positivity
    exact mul_nonneg (by norm_num) (mul_nonneg hpos (Real.exp_pos _).le)
  have h1 : CA / ((2 * j).factorial : ℝ) ≤
      CA / ((2 * j).factorial : ℝ) * X ^ (2 * N + 3 * j + 3) :=
    le_mul_of_one_le_right hCAq hXpow
  unfold polyConst
  have e : (CA / ((2 * j).factorial : ℝ) + Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * D) *
      X ^ (2 * N + 3 * j + 3) =
      CA / ((2 * j).factorial : ℝ) * X ^ (2 * N + 3 * j + 3) +
        Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) * X ^ (2 * N + 3 * j + 3) * D := by
    ring
  rw [e]
  linarith [h1]

/-! ### Main theorem -/

theorem lateMeanCoeff_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : LateMeanCoeff := by
  unfold LateMeanCoeff
  intro ρ j hρ
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, hbound⟩ := hF ρ hρ (j + 1) 0 0
  refine ⟨(∫ η : ℝ, 20 * (η ^ (2 * j) * Real.exp (-(η ^ 2 / 4)))) / ((2 * j).factorial : ℝ) +
      Real.pi * C ^ 2 * (1 + κ⁻¹) ^ (j + 1) *
        (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, 1 / ((2 * kl.1).factorial : ℝ)),
    2 * N + 3 * j + 3, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν hνle tr hb
  have hν1 : ν ≤ 1 := le_trans hνle (min_le_right _ _)
  have hνκ : ν ≤ ν₀ := le_trans hνle (min_le_left _ _)
  have hc1 : 1 ≤ ν ^ (-ρ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < ν ^ (-ρ) := lt_of_lt_of_le one_pos hc1
  have hsup : ∀ t : ℝ, 0 < t → ∀ z : ℝ × ℝ,
      jap (j + 1) z * ‖hfluct (ν ^ (-ρ)) (tr.v t) z‖ ^ 2 ≤
        (polyP C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2))) ^ 2 := by
    intro t ht z
    have hK := hbound ν hν hνκ tr hb t ht
    dsimp only at hK
    have hK0 : 0 ≤ polyP C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * t / (ν ^ (-ρ)) ^ 2)) := by
      apply mul_nonneg _ (Real.exp_pos _).le
      unfold polyP
      exact mul_nonneg hC.le (pow_nonneg (by have := inv_nonneg.mpr hν.le; linarith) N)
    have h := lmc_pt_of_sup (j + 1)
      (ageJet 0 0 (fun r => hfluct (ν ^ (-ρ)) (tr.v r)) t) hK0 hK.2.1.2 z
    rwa [lmc_norm_ageJet_zero] at h
  have hE3 : ∀ t : ℝ, 0 < t → ∀ η : ℝ, hmean (ν ^ (-ρ)) (fun z => tr.v t z 1) η = 0 :=
    fun t ht η => ((hE ν (ν ^ (-ρ)) hν hc0 tr hb).2 t ht η).2.2
  exact lmc_aux tr hν hν1 hc1 hC hκ rfl rfl hE3 hsup
