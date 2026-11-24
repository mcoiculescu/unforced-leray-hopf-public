import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.ChartConj

/-!
# Helpers for `CartLiftIsTest`: periodicity and bounded support of `cartLift`

* `nsSym` depends on a tensor only through `tv4`, so `tv4`-equal tensors have equal `nsSym`.
* The `q`-reduction in `chartOf` is a shift by an integer multiple of `c`, under which
  `nsSym ∘ m` is invariant (`IsTensorTest.periodic`), so `cartLift` sees the unreduced chart point.
* `chartOf` is invariant under `τ ↦ τ + P`, `P = 2εc`, `R = ε⁻¹`.
* `cartLift` is supported in a bounded set (`IsTensorTest.band`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst

theorem cl_nsSym_zero : nsSym 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ]

/-- `nsSym` depends on the tensor only through `tv4`. -/
theorem cl_nsSym_of_tv4_eq {T T' : Ten3} (h : tv4 T = tv4 T') : nsSym T = nsSym T' := by
  have e0 : T (0, 0) = T' (0, 0) := by
    have := congrArg (fun v => v 0) h
    simpa [tv4] using this
  have e1 : symRZ T = symRZ T' := by
    have := congrArg (fun v => v 1) h
    simpa [tv4] using this
  have e2 : T (2, 2) = T' (2, 2) := by
    have := congrArg (fun v => v 2) h
    simpa [tv4] using this
  have e3 : T (1, 1) = T' (1, 1) := by
    have := congrArg (fun v => v 3) h
    simpa [tv4] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, e0, e1, e2, e3]

/-- Invariance of `nsSym ∘ m` under `q ↦ q + c`. -/
theorem cl_nsSym_qperiodic (m : Chart → Ten3) (c : ℝ)
    (hm : UnforcedLeray.B0220.QPeriodic c (fun p => tv4 (m p))) (p : Chart) :
    nsSym (m (p.1, p.2.1 + c, p.2.2)) = nsSym (m p) :=
  cl_nsSym_of_tv4_eq (hm p)

/-- Invariance of `nsSym ∘ m` under `q ↦ q + k c`, `k ∈ ℤ`. -/
theorem cl_nsSym_intshift (m : Chart → Ten3) (c : ℝ)
    (hm : UnforcedLeray.B0220.QPeriodic c (fun p => tv4 (m p))) (k : ℤ) (p : Chart) :
    nsSym (m (p.1, p.2.1 + (k : ℝ) * c, p.2.2)) = nsSym (m p) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have e : p.2.1 + ((((n : ℤ) + 1 : ℤ)) : ℝ) * c = (p.2.1 + (n : ℝ) * c) + c := by
      push_cast; ring
    rw [e, cl_nsSym_qperiodic m c hm (p.1, p.2.1 + (n : ℝ) * c, p.2.2)]
    exact ih
  | pred n ih =>
    have e : p.2.1 + ((-(n : ℤ) - 1 : ℤ) : ℝ) * c + c = p.2.1 + ((-(n : ℤ) : ℤ) : ℝ) * c := by
      push_cast; ring
    have h1 := cl_nsSym_qperiodic m c hm (p.1, p.2.1 + ((-(n : ℤ) - 1 : ℤ) : ℝ) * c, p.2.2)
    simp only at h1
    rw [e] at h1
    rw [← h1]
    exact ih

/-- The unreduced chart point of `(z, τ)`. -/
def clUnred (R : ℝ) (τ : ℝ) (z : Space) : Chart :=
  (R ^ 2 / hRad z ^ 2, (R * Real.log (hRad z / R) + R * τ / 2, R * z 2 / hRad z))

/-- `nsSym ∘ m` evaluated at the reduced chart point equals the value at the unreduced one. -/
theorem cl_nsSym_chartOf (m : Chart → Ten3) (R c : ℝ)
    (hm : UnforcedLeray.B0220.QPeriodic c (fun p => tv4 (m p))) (z : Space) (τ : ℝ) :
    nsSym (m (chartOf R c z τ)) = nsSym (m (clUnred R τ z)) := by
  have h := cl_nsSym_intshift m c hm (-⌊(R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2⌋)
    (clUnred R τ z)
  have e : (clUnred R τ z).2.1 + ((-⌊(R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2⌋ : ℤ) : ℝ) * c
      = (chartOf R c z τ).2.1 := by
    simp only [clUnred, chartOf]
    push_cast
    ring
  have hfst : (clUnred R τ z).1 = (chartOf R c z τ).1 := rfl
  have hsnd : (clUnred R τ z).2.2 = (chartOf R c z τ).2.2 := rfl
  rw [← h]
  congr 2
  exact Prod.ext hfst (Prod.ext e.symm hsnd)

/-- The `q`-reduction in `chartOf` is compatible with the shift `q ↦ q + c`. -/
theorem cl_floor_shift (X c : ℝ) (hc : 0 < c) :
    X + c - c * ⌊(X + c) / c + 1 / 2⌋ = X - c * ⌊X / c + 1 / 2⌋ := by
  have hc' : c ≠ 0 := hc.ne'
  rw [show (X + c) / c + 1 / 2 = X / c + 1 / 2 + 1 by field_simp; ring, Int.floor_add_one]
  push_cast
  ring

/-- `chartOf` is invariant under the period shift `τ ↦ τ + 2εc` (with `R = ε⁻¹`). -/
theorem cl_chartOf_period (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (z : Space) (τ : ℝ) :
    chartOf ε⁻¹ c z (τ + 2 * ε * c) = chartOf ε⁻¹ c z τ := by
  have hRP : ε⁻¹ * (τ + 2 * ε * c) / 2 = ε⁻¹ * τ / 2 + c := by
    field_simp
  have hsh := cl_floor_shift (ε⁻¹ * Real.log (hRad z / ε⁻¹) + ε⁻¹ * τ / 2) c hc
  unfold chartOf
  rw [hRP, ← add_assoc, hsh]

theorem cl_tv4_zero : tv4 0 = 0 := by
  ext i
  fin_cases i <;> simp [tv4, symRZ]

/-- The support of `cartLift` in the similarity variable: `s₀ ‖z‖² ≤ R² + L²`, `R = ε⁻¹`. -/
theorem cl_cartLift_support (ε c : ℝ) (hε : 0 < ε) (m : Chart → Ten3) (s0 s1 L : ℝ)
    (hs0 : 0 < s0)
    (hband : ∀ p : Chart, tv4 (m p) ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (τ : ℝ) (z : Space) (h : cartLift ε⁻¹ c m τ z ≠ 0) :
    s0 * ‖z‖ ^ 2 ≤ (ε⁻¹) ^ 2 + L ^ 2 := by
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  unfold cartLift at h
  have hN : nsSym (m (chartOf ε⁻¹ c z τ)) ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  have hT : tv4 (m (chartOf ε⁻¹ c z τ)) ≠ 0 := by
    intro h0
    apply hN
    rw [cl_nsSym_of_tv4_eq (h0.trans cl_tv4_zero.symm), cl_nsSym_zero]
  obtain ⟨hs, hη⟩ := hband _ hT
  have hs0le : s0 ≤ (chartOf ε⁻¹ c z τ).1 := hs.1
  have hpdef1 : (chartOf ε⁻¹ c z τ).1 = (ε⁻¹) ^ 2 / hRad z ^ 2 := rfl
  have hpdef2 : (chartOf ε⁻¹ c z τ).2.2 = ε⁻¹ * z 2 / hRad z := rfl
  have hρ2 : hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hρne : hRad z ≠ 0 := by
    intro h0
    rw [hpdef1, h0] at hs0le
    simp at hs0le
    linarith
  have h1 : s0 * hRad z ^ 2 ≤ (ε⁻¹) ^ 2 := by
    rw [hpdef1, le_div_iff₀ (by positivity)] at hs0le
    exact hs0le
  have h2 : (ε⁻¹) ^ 2 * z 2 ^ 2 ≤ L ^ 2 * hRad z ^ 2 := by
    rw [hpdef2] at hη
    have hsq : (ε⁻¹ * z 2 / hRad z) ^ 2 ≤ L ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hη 2
      rwa [sq_abs] at this
    rw [div_pow, div_le_iff₀ (by positivity)] at hsq
    nlinarith [hsq]
  have hnorm2 : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_three]
  have h3 : (ε⁻¹) ^ 2 * (s0 * z 2 ^ 2) ≤ (ε⁻¹) ^ 2 * L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le, mul_le_mul_of_nonneg_left h1 (sq_nonneg L)]
  have h4 : s0 * z 2 ^ 2 ≤ L ^ 2 :=
    le_of_mul_le_mul_left h3 (by positivity)
  have e : s0 * ‖z‖ ^ 2 = s0 * hRad z ^ 2 + s0 * z 2 ^ 2 := by
    rw [hnorm2, hρ2]
    ring
  rw [e]
  linarith

/-- The support of `cartLift` is bounded uniformly in `τ`. -/
theorem cl_cartLift_bdd (ε c : ℝ) (hε : 0 < ε) (m : Chart → Ten3) (s0 s1 L : ℝ)
    (hs0 : 0 < s0)
    (hband : ∀ p : Chart, tv4 (m p) ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∃ r : ℝ, ∀ (τ : ℝ) (z : Space), cartLift ε⁻¹ c m τ z ≠ 0 → ‖z‖ ≤ r := by
  refine ⟨((ε⁻¹) ^ 2 + L ^ 2) / s0 + 1, fun τ z hz => ?_⟩
  have h := cl_cartLift_support ε c hε m s0 s1 L hs0 hband τ z hz
  have hK : 0 ≤ ((ε⁻¹) ^ 2 + L ^ 2) / s0 := by positivity
  have hx : ‖z‖ ^ 2 ≤ ((ε⁻¹) ^ 2 + L ^ 2) / s0 := by
    rw [le_div_iff₀ hs0]
    linarith [h, mul_comm s0 (‖z‖ ^ 2)]
  nlinarith [sq_nonneg (‖z‖ - 1), hx, hK]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
