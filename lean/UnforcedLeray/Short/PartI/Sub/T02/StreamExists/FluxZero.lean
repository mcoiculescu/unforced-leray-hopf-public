import UnforcedLeray.Short.PartI.Sub.T02_5
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/5`: `SliceFluxZero` (the horizontal flux of a slice vanishes)

Source of record: `the November 2 reference manuscript`, lines 261-288 (zero
horizontal flux). The statement is `SliceFluxZero` from `Short/PartI/Sub/T02_5.lean`.

Proof. Fix a slice `w` and put `g(η) = ∫₀^c w₂(q, η) dq`.
1. `g' = ∫₀^c ∂_η w₂ dq` by the black box `HasDerivAtEtaIntervalIntegral`.
2. `div w = 0` gives `∂_η w₂ = -∂_q w₁`, and `∫₀^c ∂_q w₁ dq = w₁(c, η) - w₁(0, η) = 0` by the FTC
   in `q` and periodicity. So `g' = 0` and `g` is constant.
3. `g(η)² ≤ c G(η)` by Cauchy-Schwarz, where `G = sliceEnergy c w`. Since `G → 0` at `+∞`, the
   constant `g(0)²` is `≤ 0`, so `g = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Lemma `SliceFluxZero`** (source lines 261-288): the horizontal flux `∫₀^c w₂(q, η) dq` of a
slice vanishes for every `η`. -/
theorem sliceFluxZero (hB : TendstoZeroOfLipschitzIntegrable) (hC : SliceEnergyProfile)
    (hD : HasDerivAtEtaIntervalIntegral) : SliceFluxZero := by
  intro c w hs
  have hc : 0 < c := hs.pos
  have hwc : Continuous w := hs.smooth.continuous
  have hcont : ∀ η : ℝ, Continuous (fun q : ℝ => w (q, η)) := fun η =>
    hwc.comp (continuous_id.prodMk continuous_const)
  -- the two components of `w` are smooth
  have hw0 : ContDiff ℝ ∞ (fun z : Plane => w z 0) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ) ∘ w)
    exact (EuclideanSpace.proj 0 : Vec →L[ℝ] ℝ).contDiff.comp hs.smooth
  have hw1 : ContDiff ℝ ∞ (fun z : Plane => w z 1) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ) ∘ w)
    exact (EuclideanSpace.proj 1 : Vec →L[ℝ] ℝ).contDiff.comp hs.smooth
  have hd0 : Differentiable ℝ (fun z : Plane => w z 0) := hw0.differentiable (by simp)
  have hC1 : ContDiff ℝ 1 (fun z : Plane => w z 1) := hw1.of_le (by norm_num)
  have hcont1 : ∀ η : ℝ, Continuous (fun q : ℝ => w (q, η) 1) := fun η =>
    hw1.continuous.comp (continuous_id.prodMk continuous_const)
  -- Step 1: differentiation under the integral sign (black box `hD`)
  have hGder : ∀ η : ℝ, HasDerivAt (fun x => ∫ q in (0 : ℝ)..c, w (q, x) 1)
      (∫ q in (0 : ℝ)..c, Cyl.partialEta (fun z : Plane => w z 1) (q, η)) η :=
    fun η => hD (fun z : Plane => w z 1) hC1 0 c η
  -- Step 2: `∂_η w₂ = -∂_q w₁` (divergence free)
  have hdiv : ∀ q η : ℝ, Cyl.partialEta (fun z : Plane => w z 1) (q, η)
      = -Cyl.partialQ (fun z : Plane => w z 0) (q, η) := by
    intro q η
    have h := hs.div (q, η)
    unfold Cyl.divergence at h
    linarith
  -- Step 3: `∫₀^c ∂_q w₁ dq = w₁(c, η) - w₁(0, η) = 0` (FTC in `q` and periodicity)
  have hper0 : ∀ η : ℝ, w (c, η) 0 = w (0, η) 0 := by
    intro η
    have h : w (c, η) = w (0, η) := by simpa using hs.periodic (0, η)
    rw [h]
  have hA : ∀ η : ℝ, ∫ q in (0 : ℝ)..c, Cyl.partialQ (fun z : Plane => w z 0) (q, η) = 0 := by
    intro η
    have hQ0 : Continuous (fun q : ℝ => Cyl.partialQ (fun z : Plane => w z 0) (q, η)) := by
      have hdq0 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (fun z : Plane => w z 0) := by
        rw [zero_add]; exact hw0.of_le (by norm_num)
      exact (Cyl.contDiff_partialQ (n := (0 : WithTop ℕ∞)) hdq0).continuous.comp
        (continuous_id.prodMk continuous_const : Continuous fun q : ℝ => (q, η))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Cyl.hasDerivAt_sliceQ hd0 x η) (hQ0.intervalIntegrable 0 c)]
    show w (c, η) 0 - w (0, η) 0 = 0
    rw [hper0 η, sub_self]
  -- Step 4: `g' = 0`, so `g` is constant
  have hderiv0 : ∀ η : ℝ, HasDerivAt (fun x => ∫ q in (0 : ℝ)..c, w (q, x) 1) 0 η := by
    intro η
    have hz : ∫ q in (0 : ℝ)..c, Cyl.partialEta (fun z : Plane => w z 1) (q, η) = 0 := by
      simp only [hdiv, intervalIntegral.integral_neg, hA η, neg_zero]
    have h := hGder η
    rw [hz] at h
    exact h
  have hdiff : Differentiable ℝ (fun x => ∫ q in (0 : ℝ)..c, w (q, x) 1) :=
    fun η => (hderiv0 η).differentiableAt
  have hconst : ∀ η : ℝ, (∫ q in (0 : ℝ)..c, w (q, η) 1) = ∫ q in (0 : ℝ)..c, w (q, 0) 1 :=
    fun η => is_const_of_deriv_eq_zero hdiff (fun x => (hderiv0 x).deriv) η 0
  -- Step 5: Cauchy-Schwarz `(∫₀^c w₂)² ≤ c ∫₀^c w₂² ≤ c G(η)`.
  -- Cauchy-Schwarz on `(0, d)` for a continuous real function: `(∫ f)² ≤ d ∫ f²`.
  have cs : ∀ (f : ℝ → ℝ) (d : ℝ), Continuous f → 0 ≤ d →
      (∫ q in (0 : ℝ)..d, f q) ^ 2 ≤ d * ∫ q in (0 : ℝ)..d, f q ^ 2 := by
    intro f d hf hd
    rcases hd.eq_or_lt with h0 | hpos
    · subst h0
      simp
    have hd0 : d ≠ 0 := hpos.ne'
    have hf2 : IntervalIntegrable (fun q => f q ^ 2) MeasureTheory.volume 0 d :=
      Continuous.intervalIntegrable (by fun_prop) 0 d
    have hfa : ∀ a : ℝ, IntervalIntegrable (fun q => 2 * a * f q) MeasureTheory.volume 0 d :=
      fun a => Continuous.intervalIntegrable (by fun_prop) 0 d
    have hexp : ∀ a : ℝ, ∫ q in (0 : ℝ)..d, (f q - a) ^ 2
        = (∫ q in (0 : ℝ)..d, f q ^ 2) - 2 * a * (∫ q in (0 : ℝ)..d, f q) + d * a ^ 2 := by
      intro a
      have hA' : IntervalIntegrable (fun q => f q ^ 2 - 2 * a * f q) MeasureTheory.volume 0 d :=
        Continuous.intervalIntegrable (by fun_prop) 0 d
      have e : (fun q => (f q - a) ^ 2) = fun q => (f q ^ 2 - 2 * a * f q) + a ^ 2 := by
        funext q
        ring
      rw [e, intervalIntegral.integral_add hA' (intervalIntegrable_const (c := a ^ 2)),
        intervalIntegral.integral_sub hf2 (hfa a), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hnn : 0 ≤ ∫ q in (0 : ℝ)..d, (f q - (∫ r in (0 : ℝ)..d, f r) / d) ^ 2 :=
      intervalIntegral.integral_nonneg hpos.le (fun q _ => sq_nonneg _)
    rw [hexp] at hnn
    have alg : ∀ I J t : ℝ, d * t = I → 0 ≤ J - 2 * t * I + d * t ^ 2 → I ^ 2 ≤ d * J := by
      intro I J t ht h
      have h2 : d * (J - 2 * t * I + d * t ^ 2) = d * J - I ^ 2 := by
        calc d * (J - 2 * t * I + d * t ^ 2) = d * J - 2 * (d * t) * I + (d * t) ^ 2 := by ring
          _ = d * J - I ^ 2 := by rw [ht]; ring
      have h3 : 0 ≤ d * (J - 2 * t * I + d * t ^ 2) := mul_nonneg hpos.le h
      linarith
    exact alg _ _ ((∫ r in (0 : ℝ)..d, f r) / d) (by field_simp) hnn
  -- Pointwise `w₂² ≤ ‖w‖²`.
  have hle : ∀ z : Plane, (w z 1) ^ 2 ≤ ‖w z‖ ^ 2 := by
    intro z
    have h1 : |w z 1| ≤ ‖w z‖ := by
      have h := PiLp.norm_apply_le (w z) 1
      rw [Real.norm_eq_abs] at h
      exact h
    nlinarith [abs_nonneg (w z 1), norm_nonneg (w z), sq_abs (w z 1)]
  have hCS : ∀ η : ℝ, (∫ q in (0 : ℝ)..c, w (q, η) 1) ^ 2 ≤ c * sliceEnergy c w η := by
    intro η
    have hgn : Continuous (fun s : ℝ => ‖w (s, η)‖ ^ 2) := ((hcont η).norm).pow 2
    have hmono : ∫ q in (0 : ℝ)..c, (w (q, η) 1) ^ 2 ≤ sliceEnergy c w η := by
      unfold sliceEnergy
      exact intervalIntegral.integral_mono_on hc.le
        (((hcont1 η).pow 2).intervalIntegrable 0 c) (hgn.intervalIntegrable 0 c)
        (fun q _ => hle (q, η))
    calc (∫ q in (0 : ℝ)..c, w (q, η) 1) ^ 2
        ≤ c * ∫ q in (0 : ℝ)..c, (w (q, η) 1) ^ 2 :=
          cs (fun q => w (q, η) 1) c (hcont1 η) hc.le
      _ ≤ c * sliceEnergy c w η := mul_le_mul_of_nonneg_left hmono hc.le
  -- Step 6: `G → 0` at `+∞`, so the constant `g(0)² ≤ c G(η) → 0` forces `g(0) = 0`.
  have hG : Tendsto (sliceEnergy c w) atTop (𝓝 0) := (sliceEnergy_tendsto hB hC hs).1
  have hT : Tendsto (fun η => c * sliceEnergy c w η) atTop (𝓝 0) := by
    have h := hG.const_mul c
    rwa [mul_zero] at h
  have hK2 : (∫ q in (0 : ℝ)..c, w (q, 0) 1) ^ 2 ≤ 0 := by
    refine ge_of_tendsto hT (Eventually.of_forall fun η => ?_)
    rw [← hconst η]
    exact hCS η
  have hK0 : ∫ q in (0 : ℝ)..c, w (q, 0) 1 = 0 :=
    (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hK2 (sq_nonneg _))
  intro η
  rw [hconst η]
  exact hK0

end UnforcedLeray.Short.PartI
