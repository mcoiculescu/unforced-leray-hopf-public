import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

set_option autoImplicit false

noncomputable section

open Set Real
open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Homogeneity of the Frobenius norm  under scalars (local copy). -/
theorem frobSmulAux (c : ℝ) (M : Mat3) : frob (c • M) = |c| * frob M := by
  unfold frob
  have h : ∑ i, ∑ j, (c • M) i j ^ 2 = c ^ 2 * ∑ i, ∑ j, M i j ^ 2 := by
    simp [Finset.mul_sum, mul_pow]
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]


/-- Entries of `D₀`. -/
theorem Dz00 : Dzero 0 0 = 12 := rfl
theorem Dz11 : Dzero 1 1 = -3 := rfl
theorem Dz22 : Dzero 2 2 = -9 := rfl
theorem Dz01 : Dzero 0 1 = 0 := by simp [Dzero]
theorem Dz10 : Dzero 1 0 = 0 := by simp [Dzero]
theorem Dz12 : Dzero 1 2 = 0 := by simp [Dzero]
theorem Dz21 : Dzero 2 1 = 0 := by simp [Dzero]

/-- On `s > 0`, `a_μ(s) = (s^{5/2}/(μ+5/2)) • D₀`. -/
theorem aMuFun_pos_eq (μ s : ℝ) (hs : 0 < s) :
    aMuFun μ s = (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) • (fun i j => Dzero i j) := by
  unfold aMuFun
  rw [if_pos hs]

/-- `(s∂_s)^j a_μ(s) = (5/2)^j a_μ(s)` for `s > 0`, written out. -/
theorem sDerivIter_aMuFun (μ : ℝ) (j : ℕ) :
    ∀ s : ℝ, 0 < s → sDerivIter j (aMuFun μ) s =
      ((5 / 2 : ℝ) ^ j * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2))) • (fun i j => Dzero i j) := by
  induction j with
  | zero =>
    intro s hs
    simp only [sDerivIter, pow_zero, one_mul]
    exact aMuFun_pos_eq μ s hs
  | succ n ih =>
    intro s hs
    have hev : sDerivIter n (aMuFun μ) =ᶠ[nhds s]
        (fun t : ℝ => ((5 / 2 : ℝ) ^ n * (t ^ (5 / 2 : ℝ) / (μ + 5 / 2))) • (fun i j => Dzero i j)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) (fun t ht => ih t ht)
    have h1 : HasDerivAt (fun t : ℝ => t ^ (5 / 2 : ℝ)) ((5 / 2 : ℝ) * s ^ ((5 / 2 : ℝ) - 1)) s :=
      Real.hasDerivAt_rpow_const (Or.inl hs.ne')
    have hd : HasDerivAt
        (fun t : ℝ => ((5 / 2 : ℝ) ^ n * (t ^ (5 / 2 : ℝ) / (μ + 5 / 2))) • (fun i j => Dzero i j))
        (((5 / 2 : ℝ) ^ n * ((5 / 2 : ℝ) * s ^ ((5 / 2 : ℝ) - 1) / (μ + 5 / 2))) •
          (fun i j => Dzero i j)) s :=
      ((h1.div_const (μ + 5 / 2)).const_mul ((5 / 2 : ℝ) ^ n)).smul_const _
    have hpow : s * s ^ ((5 / 2 : ℝ) - 1) = s ^ (5 / 2 : ℝ) := by
      conv_rhs => rw [show (5 / 2 : ℝ) = 1 + ((5 / 2 : ℝ) - 1) by norm_num, Real.rpow_add hs,
        Real.rpow_one]
    rw [sDerivIter, sDeriv, hev.deriv_eq, hd.deriv, smul_smul]
    congr 1
    have hsc : s * ((5 / 2 : ℝ) ^ n * ((5 / 2 : ℝ) * s ^ ((5 / 2 : ℝ) - 1) / (μ + 5 / 2)))
        = (5 / 2 : ℝ) ^ n * (5 / 2 : ℝ) * (s * s ^ ((5 / 2 : ℝ) - 1)) / (μ + 5 / 2) := by
      ring
    rw [hsc, hpow, pow_succ]
    ring

/-- The unit displacement `a_μ` lies in `𝒜` for `a_s ≥ 0`, `μ > 0` (source 4807-4811, 4833). -/
theorem aMuInAff (as μ : ℝ) : AMuInAff as μ := by
  intro has hμ
  have hμ2 : 0 < μ + 5 / 2 := by linarith
  have hsmooth : ContDiffOn ℝ 6 (fun s : ℝ => (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) • (fun i j => Dzero i j))
      (Ioi 0) := by
    have hc : ContDiffOn ℝ 6 (fun s : ℝ => s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) (Ioi 0) :=
      ContDiffOn.div_const (ContDiffOn.rpow_const_of_ne contDiffOn_id (fun x hx => ne_of_gt hx)) _
    exact hc.smul contDiffOn_const
  -- the Duhamel-type bound: the iterated derivatives are constant multiples of `a_μ`
  have hbound : ∀ s : ℝ, 0 < s → affTerm as 6 (aMuFun μ) s ≤
      (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
        (frob (fun i j => Dzero i j) / (μ + 5 / 2)) := by
    intro s hs
    have hterm : ∀ j ∈ Finset.range 7, frob (sDerivIter j (aMuFun μ) s) =
        (5 / 2 : ℝ) ^ j * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) * frob (fun i j => Dzero i j) := by
      intro j _
      rw [sDerivIter_aMuFun μ j s hs, frobSmulAux,
        abs_of_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
          (div_nonneg (Real.rpow_nonneg hs.le _) hμ2.le))]
    have hS : affSum 6 (aMuFun μ) s = (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
        (s ^ (5 / 2 : ℝ) / (μ + 5 / 2) * frob (fun i j => Dzero i j)) := by
      unfold affSum
      rw [Finset.sum_congr rfl hterm, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hq : s ^ (-(5 / 2 : ℝ)) * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2) * frob (fun i j => Dzero i j))
        = frob (fun i j => Dzero i j) / (μ + 5 / 2) := by
      have hp : s ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
      rw [Real.rpow_neg hs.le]
      field_simp
    have hT : affTerm as 6 (aMuFun μ) s = Real.exp (-as * s) *
        ((∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) * (frob (fun i j => Dzero i j) / (μ + 5 / 2))) := by
      unfold affTerm
      rw [hS]
      linear_combination (Real.exp (-as * s) * (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j)) * hq
    have hK : 0 ≤ (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
        (frob (fun i j => Dzero i j) / (μ + 5 / 2)) :=
      mul_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
        (div_nonneg (Real.sqrt_nonneg _) hμ2.le)
    have he : Real.exp (-as * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg has hs.le]
    rw [hT]
    exact mul_le_of_le_one_left hK he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ContDiffOn.congr hsmooth (fun s hs => aMuFun_pos_eq μ s hs)
  · intro s hs
    rw [aMuFun_pos_eq μ s hs]
    simp only [Pi.smul_apply, smul_eq_mul, Dz00, Dz11, Dz22]
    ring
  · intro s hs
    rw [aMuFun_pos_eq μ s hs]
    simp only [Pi.smul_apply, smul_eq_mul, Dz01, Dz10, Dz12, Dz21, mul_zero, and_self]
  · intro s hs
    unfold aMuFun
    rw [if_neg (not_lt.2 hs)]
  · refine ⟨(∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
        (frob (fun i j => Dzero i j) / (μ + 5 / 2)), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hbound s hs

end UnforcedLeray.Short.PartIIIb.Concrete
