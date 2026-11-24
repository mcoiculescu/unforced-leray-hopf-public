import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `envSummable` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/2`)

The periodised envelope `envTerm m ν j p = (1+|x_j|)^m exp(-|x_j|²/(8a))` is summable over `j ∈ ℤ`
for `ν > 0`, `s > 0`. Use `1 + |x_j| ≤ K (1+|j|)` (with `K = (1+|η|)(1+|q|)(1+c)`, `c = ν⁻²`),
`exp(-|x_j|²/(8a)) ≤ exp(-(q-jc)²/(8a))`, and `(1+|j|)^m E_j` summable via the binomial expansion
and `gp_gauss_pow_summable`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `(1+|j|)^m exp(-α(t - jc)²)` is summable over `j ∈ ℤ`. -/
lemma wse_poly_gauss_summable (m : ℕ) (t α c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ m * Real.exp (-α * (t - (j : ℝ) * c) ^ 2)) := by
  have hs : Summable (fun j : ℤ => ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * (|(j : ℝ)| ^ k * Real.exp (-α * (t - (j : ℝ) * c) ^ 2))) :=
    summable_sum fun k _ => (gp_gauss_pow_summable t α c hα hc k).mul_left _
  refine hs.congr fun j => ?_
  have hb : (1 + |(j : ℝ)|) ^ m = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * |(j : ℝ)| ^ k := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow]
    ring
  rw [hb, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Pointwise envelope bound by a summable majorant. -/
lemma wse_envTerm_bound (m : ℕ) (ν : ℝ) (hν : 0 < ν) (p : Chart) (hp : 0 < p.1) (j : ℤ) :
    envTerm m ν j p ≤
      ((1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν))) ^ m
        * ((1 + |(j : ℝ)|) ^ m * Real.exp (-(1 / (8 * ageA ν p.1)) * (p.2.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have ha : 0 < ageA ν p.1 := by unfold ageA; positivity
  have hpos8 : 0 < 8 * ageA ν p.1 := by positivity
  have hA := gp_one_add_norm ν j p.2
  have hB : 1 + |p.2.1 - (j : ℝ) * cOf ν| ≤ (1 + |p.2.1|) * (1 + cOf ν) * (1 + |(j : ℝ)|) := by
    have h := abs_sub p.2.1 ((j : ℝ) * cOf ν)
    rw [abs_mul, abs_of_pos hc] at h
    have hA0 := abs_nonneg p.2.1
    have hB0 := abs_nonneg (j : ℝ)
    nlinarith [mul_nonneg hA0 hc.le, mul_nonneg hA0 hB0, mul_nonneg (mul_nonneg hA0 hc.le) hB0,
      mul_nonneg hc.le hB0]
  have h1 : 1 + ‖xj ν j p.2‖ ≤ ((1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν))) * (1 + |(j : ℝ)|) := by
    calc 1 + ‖xj ν j p.2‖ ≤ (1 + |p.2.2|) * (1 + |p.2.1 - (j : ℝ) * cOf ν|) := hA
      _ ≤ (1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν) * (1 + |(j : ℝ)|)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = ((1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν))) * (1 + |(j : ℝ)|) := by ring
  have hsq : (p.2.1 - (j : ℝ) * cOf ν) ^ 2 ≤ sq2 (xj ν j p.2) := by
    simp only [sq2, xj]
    nlinarith [sq_nonneg p.2.2]
  have h2 : Real.exp (-(sq2 (xj ν j p.2)) / (8 * ageA ν p.1))
      ≤ Real.exp (-(1 / (8 * ageA ν p.1)) * (p.2.1 - (j : ℝ) * cOf ν) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have e : -(sq2 (xj ν j p.2)) / (8 * ageA ν p.1)
        = -(1 / (8 * ageA ν p.1)) * sq2 (xj ν j p.2) := by ring
    rw [e]
    have hq : 0 ≤ 1 / (8 * ageA ν p.1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq hq]
  show (1 + ‖xj ν j p.2‖) ^ m * Real.exp (-(sq2 (xj ν j p.2)) / (8 * ageA ν p.1)) ≤ _
  calc (1 + ‖xj ν j p.2‖) ^ m * Real.exp (-(sq2 (xj ν j p.2)) / (8 * ageA ν p.1))
      ≤ (((1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν))) * (1 + |(j : ℝ)|)) ^ m
          * Real.exp (-(1 / (8 * ageA ν p.1)) * (p.2.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h1 m) h2 (Real.exp_pos _).le (by positivity)
    _ = ((1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν))) ^ m
        * ((1 + |(j : ℝ)|) ^ m * Real.exp (-(1 / (8 * ageA ν p.1)) * (p.2.1 - (j : ℝ) * cOf ν) ^ 2)) := by
        rw [mul_pow]
        ring

/-- **Envelope summability** (source 5063-5071, lattice sum over `j`). -/
theorem envSummable : EnvSummable := by
  intro m ν hν p hp
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have ha : 0 < ageA ν p.1 := by unfold ageA; positivity
  have hα : 0 < 1 / (8 * ageA ν p.1) := by positivity
  have hS := (wse_poly_gauss_summable m p.2.1 (1 / (8 * ageA ν p.1)) (cOf ν) hα hc).mul_left
    (((1 + |p.2.2|) * ((1 + |p.2.1|) * (1 + cOf ν))) ^ m)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => wse_envTerm_bound m ν hν p hp j) hS
  unfold envTerm
  positivity

end UnforcedLeray.Short.PartIIIb.Concrete
