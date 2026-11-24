import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.Polar
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.BInt

/-!
# `SigmaPointwise` (source 4766-4775, 4924-4927)

For almost every `x'`: `|Σ_M(x')| ≤ ρ⁻¹ B(ρ⁻²)`.  Ingredients: Frobenius of an integral is at most
the integral of Frobenius (entrywise Cauchy–Schwarz), Frobenius invariance under conjugation by
the orthogonal `rotQ`, and the a.e. integrability of `|M(u,·)|` from `OldThinFinite`, pulled back
by `polar_null`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem frob_sq (A : Mat3) : frob A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold frob
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem frob_mono (A B : Mat3) (h : ∀ i j, |A i j| ≤ |B i j|) : frob A ≤ frob B := by
  unfold frob
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => sq_le_sq.2 (h i j)

theorem frob_fun_smul (r : ℝ) (A : Mat3) : frob (fun i j => r * A i j) = |r| * frob A := by
  unfold frob
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

/-- Frobenius of an integral is at most the integral of the Frobenius norm. -/
theorem frob_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → Mat3)
    (hf : Integrable (fun x => frob (f x)) μ) :
    frob (fun i j => ∫ x, f x i j ∂μ) ≤ ∫ x, frob (f x) ∂μ := by
  set w : Mat3 := fun i j => ∫ x, f x i j ∂μ with hw
  have hint : ∀ i j, Integrable (fun x => w i j * f x i j) μ := by
    intro i j
    by_cases h : Integrable (fun x => f x i j) μ
    · exact h.const_mul _
    · have : w i j = 0 := integral_undef h
      simp [this]
  have hsum : ∑ i, ∑ j, w i j ^ 2 = ∫ x, ∑ i, ∑ j, w i j * f x i j ∂μ := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, sq]
  have hcs : ∀ x, ∑ i, ∑ j, w i j * f x i j ≤ frob w * frob (f x) := by
    intro x
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3 × Fin 3))
      (fun p => w p.1 p.2) (fun p => f x p.1 p.2)
    rw [Fintype.sum_prod_type] at h
    simpa [Fintype.sum_prod_type, frob] using h
  have hle : frob w ^ 2 ≤ frob w * ∫ x, frob (f x) ∂μ := by
    rw [frob_sq, hsum, ← integral_const_mul]
    exact integral_mono (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j)
      (hf.const_mul _) hcs
  have hI : 0 ≤ ∫ x, frob (f x) ∂μ := integral_nonneg fun x => frob_nonneg' _
  rcases (frob_nonneg' w).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hI
  · nlinarith

theorem vec_orth (Q : Mat3) (hcol : ∀ j k, ∑ b, Q b j * Q b k = if j = k then 1 else 0)
    (v : Fin 3 → ℝ) : ∑ b, (∑ j, Q b j * v j) ^ 2 = ∑ j, v j ^ 2 := by
  calc ∑ b, (∑ j, Q b j * v j) ^ 2
      = ∑ b, ∑ j, ∑ k, (Q b j * Q b k) * (v j * v k) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ j, ∑ k, (∑ b, Q b j * Q b k) * (v j * v k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ j, v j ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [hcol, ite_mul, sq]

theorem frob_conj (Q : Mat3) (hcol : ∀ j k, ∑ b, Q b j * Q b k = if j = k then 1 else 0)
    (hrow : ∀ j k, ∑ b, Q j b * Q k b = if j = k then 1 else 0) (A : Mat3) :
    frob (fun a b => ∑ i, ∑ j, Q a i * A i j * Q b j) = frob A := by
  have h1 : ∀ a b, ∑ i, ∑ j, Q a i * A i j * Q b j = ∑ j, Q b j * (∑ i, Q a i * A i j) := by
    intro a b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : frob (fun a b => ∑ i, ∑ j, Q a i * A i j * Q b j) ^ 2 = frob A ^ 2 := by
    rw [frob_sq, frob_sq]
    simp_rw [h1]
    calc ∑ a, ∑ b, (∑ j, Q b j * (∑ i, Q a i * A i j)) ^ 2
        = ∑ a, ∑ j, (∑ i, Q a i * A i j) ^ 2 :=
          Finset.sum_congr rfl fun a _ => vec_orth Q hcol _
      _ = ∑ j, ∑ a, (∑ i, Q a i * A i j) ^ 2 := Finset.sum_comm
      _ = ∑ j, ∑ i, A i j ^ 2 :=
          Finset.sum_congr rfl fun j _ => vec_orth Q hcol (fun i => A i j)
      _ = ∑ i, ∑ j, A i j ^ 2 := Finset.sum_comm
  exact (sq_eq_sq₀ (frob_nonneg' _) (frob_nonneg' _)).1 h2

theorem rotQ_orth {x' : ℝ × ℝ} (hx : 0 < x'.1 ^ 2 + x'.2 ^ 2) :
    (∀ j k, ∑ b, rotQ x' b j * rotQ x' b k = if j = k then 1 else 0) ∧
    (∀ j k, ∑ b, rotQ x' j b * rotQ x' k b = if j = k then 1 else 0) := by
  have hρ : 0 < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := Real.sqrt_pos.2 hx
  have hcs : (x'.1 / Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) ^ 2 +
      (x'.2 / Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) ^ 2 = 1 := by
    rw [div_pow, div_pow, Real.sq_sqrt hx.le, ← add_div, div_self hx.ne']
  constructor <;> intro j k <;> fin_cases j <;> fin_cases k <;>
    simp [rotQ, Fin.sum_univ_three] <;> linarith

theorem frob_sigmaM_le {c ν : ℝ} {χo : ℝ → ℝ} (hχ : IsOutwardCutoff χo) (M : Chart → Mat3)
    (x' : ℝ × ℝ) (hx : 0 < x'.1 ^ 2 + x'.2 ^ 2)
    (hint : Integrable (fun y => frob (M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹, y))) (Cyl.avgμ c)) :
    frob (sigmaM c ν χo M x') ≤
      (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ * phaseB c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ := by
  set u := (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ with hu
  set ρ := Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.2 hx
  obtain ⟨hc, hr⟩ := rotQ_orth hx
  have hE : sigmaM c ν χo M x' = fun a b => ∑ i, ∑ j, rotQ x' a i *
      (fun i j => ρ⁻¹ * phaseMean c ν χo M u i j) i j * rotQ x' b j := by
    funext a b; rfl
  rw [hE, frob_conj _ hc hr, frob_fun_smul, abs_of_pos (inv_pos.2 hρ)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hρ).le
  set w : Mat3 := fun i j => ∫ y, M (u, y) i j ∂(Cyl.avgμ c) with hw
  have h1 : frob (phaseMean c ν χo M u) ≤ frob (fun i j => χo (ν * u) * w i j) := by
    apply frob_mono
    intro i j
    unfold phaseMean
    by_cases h : i = 1 ∨ j = 1
    · simp [h]; positivity
    · simp [h, hw]
  rw [frob_fun_smul, abs_of_nonneg (hχ.range _).1] at h1
  refine h1.trans ?_
  unfold phaseB
  exact mul_le_mul_of_nonneg_left (frob_integral_le _ _ hint) (hχ.range _).1

theorem sigmaPointwise : SigmaPointwise := by
  intro c ν χo hc hν hχ M hM
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (6 / 5 / ν))), Integrable
      (fun y => u ^ (-(3 / 2 : ℝ)) * frob (M (u, y))) (Cyl.avgμ c) :=
    hM.2.prod_right_ae
  rw [ae_restrict_iff' measurableSet_Ioi] at hae
  obtain ⟨t, hsubt, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hnull := polar_null htm ht0
  filter_upwards [hnull] with x' hx
  by_cases hs : x'.1 ^ 2 + x'.2 ^ 2 = 0
  · have h1 : x'.1 = 0 := by nlinarith [sq_nonneg x'.1, sq_nonneg x'.2]
    have h2 : x'.2 = 0 := by nlinarith [sq_nonneg x'.1, sq_nonneg x'.2]
    have : sigmaM c ν χo M x' = 0 := by
      funext a b
      simp [sigmaM, h1, h2]
    rw [this, hs]
    simp [frob]
  · have hpos : 0 < x'.1 ^ 2 + x'.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
    have hnt : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∉ t := fun h => hx ⟨hpos, h⟩
    by_cases hu : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ Ioi (6 / 5 / ν)
    · have hu' : ¬ ¬ ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ Ioi (6 / 5 / ν) →
          Integrable (fun y => (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ^ (-(3 / 2 : ℝ)) *
            frob (M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹, y))) (Cyl.avgμ c)) := fun h =>
        hnt (hsubt h)
      have hI := not_not.1 hu' hu
      have hu0 : 0 < (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ := inv_pos.2 hpos
      refine frob_sigmaM_le hχ M x' hpos ?_
      have := hI.const_mul ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ^ (3 / 2 : ℝ))
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [← mul_assoc, ← Real.rpow_add hu0]
      norm_num
    · have hle : ν * (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ≤ 6 / 5 := by
        have : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ≤ 6 / 5 / ν := not_lt.1 hu
        calc ν * (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ≤ ν * (6 / 5 / ν) :=
              mul_le_mul_of_nonneg_left this hν.le
          _ = 6 / 5 := by field_simp
      have h0 : phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ = 0 := by
        funext i j
        simp [phaseMean, hχ.zero _ hle]
      have : sigmaM c ν χo M x' = 0 := by
        funext a b
        simp [sigmaM, h0]
      rw [this]
      have h3 : frob (0 : Mat3) = 0 := by simp [frob]
      rw [h3]
      exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (phaseB_nonneg c ν hχ M _)

end UnforcedLeray.Short.PartIIIb.Concrete
