import UnforcedLeray.Short.PartIIIa.Clock.Moving

/-!
# Part III-a long assembly, H1: elementary clock facts

Monotonicity of `clockTheta` in the age, positivity of `clockN`, `clockN P ν t t = 1`, and a
positive uniform lower bound of `clockN P ν t ·` on `Icc t s` (compactness).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma one_le_clockA {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) : 1 ≤ clockA ν s := by
  unfold clockA
  nlinarith [mul_nonneg hν hs]

lemma clockA_mono {ν r s : ℝ} (hν : 0 ≤ ν) (hrs : r ≤ s) : clockA ν r ≤ clockA ν s := by
  unfold clockA
  nlinarith

lemma theta_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) : 0 < clockTheta ν s := by
  unfold clockTheta
  have h1 := one_le_clockA hν.le hs
  exact inv_pos.2 (mul_pos hν (by linarith))

lemma theta_anti {ν r s : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hrs : r ≤ s) :
    clockTheta ν s ≤ clockTheta ν r := by
  unfold clockTheta
  have h1 := one_le_clockA hν.le hr
  apply inv_anti₀ (mul_pos hν (by linarith))
  exact mul_le_mul_of_nonneg_left (clockA_mono hν.le hrs) hν.le

lemma clockN_self (P : PlanarData) {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    clockN P ν t t = 1 := by
  unfold clockN
  have hθ : clockTheta ν t ≠ 0 := (theta_pos hν ht).ne'
  rw [sub_self, mul_zero, Real.exp_zero, div_self hθ, Real.one_rpow, one_mul]

lemma clockN_pos (P : PlanarData) {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < clockN P ν t s := by
  unfold clockN
  exact mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos (div_pos (theta_pos hν ht) (theta_pos hν hs)) _)

lemma clockN_lower (P : PlanarData) {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) :
    ∃ n0 : ℝ, 0 < n0 ∧ ∀ r ∈ Icc t s, n0 ≤ clockN P ν t r := by
  have hθ : ContinuousOn (fun r => clockTheta ν r) (Icc t s) := by
    have hf : ContinuousOn (fun r => ν * clockA ν r) (Icc t s) := by
      unfold clockA
      exact continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    have h0 : ∀ r ∈ Icc t s, ν * clockA ν r ≠ 0 := by
      intro r hr
      have := one_le_clockA hν.le (le_trans ht hr.1)
      exact (mul_pos hν (by linarith)).ne'
    unfold clockTheta
    exact hf.inv₀ h0
  have hcont : ContinuousOn (fun r => clockN P ν t r) (Icc t s) := by
    unfold clockN
    have hq : ContinuousOn (fun r => clockTheta ν t / clockTheta ν r) (Icc t s) :=
      continuousOn_const.div hθ (fun r hr => (theta_pos hν (le_trans ht hr.1)).ne')
    have hp : ContinuousOn (fun r => (clockTheta ν t / clockTheta ν r) ^ P.kappa.re) (Icc t s) :=
      hq.rpow_const (fun r hr => Or.inl (div_ne_zero (theta_pos hν ht).ne'
        (theta_pos hν (le_trans ht hr.1)).ne'))
    have he : ContinuousOn (fun r => Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)))
        (Icc t s) :=
      (continuousOn_const.mul (continuousOn_const.sub hθ)).rexp
    exact he.mul hp
  obtain ⟨r0, hr0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hts) hcont
  refine ⟨clockN P ν t r0, clockN_pos P hν ht (le_trans ht hr0.1), fun r hr => ?_⟩
  exact isMinOn_iff.mp hmin r hr

end UnforcedLeray.Short.IIIa
