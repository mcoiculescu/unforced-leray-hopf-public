import UnforcedLeray.Short.PartIIIa.CanonicalTransfer
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.Dil

/-!


Source of record: `the November 2 reference manuscript`, lines 3228-3240
(`eq:ct-embeddings`) and 3176-3184.

Proof. Substituting `x = √a y` (`lintegral_cell_scale`, from the pushforward
`E0.RsDil.map_dilate_restrict` and `lintegral_map_equiv`), each component satisfies
`a * eLpNorm (a^{3/2} u_j(√a ·)) 2 (cell d) ^ 2 = a^3 * eLpNorm (u_j) 2 (cell c) ^ 2 / a^...`
which after cancelling `a` gives `eLpNorm (·) = a * eLpNorm (u_j)`; then the sum of squares
and the power `1/2` give the factor `a`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- Change of variables `x = √a y` from `cell (cellLen c a)` to `cell c`, for a lintegral. -/
lemma lintegral_cell_scale {c a : ℝ} (ha : 0 < a) (F : ℝ × ℝ → ℝ≥0∞) :
    ENNReal.ofReal a * ∫⁻ y in B0579.cell (cellLen c a), F (Real.sqrt a • y) =
      ∫⁻ z in B0579.cell c, F z := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  let g : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.smul₀ (Real.sqrt a)⁻¹ (inv_ne_zero hs)
  have hgc : ⇑g = fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z := rfl
  have h1 := lintegral_map_equiv (μ := volume.restrict (B0579.cell c))
    (fun y : ℝ × ℝ => F (Real.sqrt a • y)) g
  rw [hgc, E0.RsDil.map_dilate_restrict ha, lintegral_smul_measure] at h1
  simp only [smul_smul, mul_inv_cancel₀ hs, one_smul] at h1
  exact h1

/-- Injectivity of squaring on `ℝ≥0∞`. -/
lemma ennreal_sq_inj_aux {x y : ℝ≥0∞} (h : x ^ 2 = y ^ 2) : x = y := by
  have hx : x = (x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hy : y = (y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [hx, hy, h]

/-- The `L²` norm as the square root of a lintegral (local copy). -/
lemma eLpNorm_two_eq_scale_aux {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', htr]
  simp only [ENNReal.rpow_two]

/-- `((X) ^ (1/2)) ^ 2 = X` in `ℝ≥0∞`. -/
lemma rpow_half_sq_scale_aux (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Scaling of the squared `L²` norm of a scaled component. -/
lemma eLpNorm_sq_scale_aux {c a : ℝ} (ha : 0 < a) (k : ℝ) (h : ℝ × ℝ → ℂ) :
    ENNReal.ofReal a * eLpNorm (fun y : ℝ × ℝ => ((k : ℝ) : ℂ) * h (Real.sqrt a • y)) 2
        (volume.restrict (B0579.cell (cellLen c a))) ^ 2 =
      ENNReal.ofReal (k ^ 2) * eLpNorm h 2 (volume.restrict (B0579.cell c)) ^ 2 := by
  rw [eLpNorm_two_eq_scale_aux, eLpNorm_two_eq_scale_aux, rpow_half_sq_scale_aux,
    rpow_half_sq_scale_aux]
  have hpt : ∀ y : ℝ × ℝ, ‖((k : ℝ) : ℂ) * h (Real.sqrt a • y)‖ₑ ^ 2 =
      ENNReal.ofReal (k ^ 2) * ‖h (Real.sqrt a • y)‖ₑ ^ 2 := by
    intro y
    have hk : ‖((k : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |k| := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [enorm_mul, hk, mul_pow, ← ENNReal.ofReal_pow (abs_nonneg k), sq_abs]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hc : ENNReal.ofReal a * ∫⁻ y in B0579.cell (cellLen c a), ‖h (Real.sqrt a • y)‖ₑ ^ 2 =
      ∫⁻ z in B0579.cell c, ‖h z‖ₑ ^ 2 := lintegral_cell_scale ha (fun z => ‖h z‖ₑ ^ 2)
  rw [← hc]
  ring

/-- Coordinate form of `velNorm_scale`: the scaled component has `L²` norm `a` times. -/
lemma eLpNorm_component_scale {c a : ℝ} (ha : 0 < a) (u : ℝ × ℝ → ℂ) :
    eLpNorm (fun y : ℝ × ℝ => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2))
        2 (volume.restrict (B0579.cell (cellLen c a))) =
      ENNReal.ofReal a * eLpNorm u 2 (volume.restrict (B0579.cell c)) := by
  have e : ∀ y : ℝ × ℝ, (Real.sqrt a * y.1, Real.sqrt a * y.2) = Real.sqrt a • y :=
    fun y => rfl
  simp only [e]
  have key := eLpNorm_sq_scale_aux (c := c) ha (a ^ ((3 : ℝ) / 2)) u
  have hsq : (a ^ ((3 : ℝ) / 2)) ^ 2 = a ^ 3 := by
    rw [← Real.rpow_natCast (a ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul ha.le]
    norm_num
  have h3 : ENNReal.ofReal (a ^ 3) = ENNReal.ofReal a * ENNReal.ofReal (a ^ 2) := by
    rw [← ENNReal.ofReal_mul ha.le]; congr 1; ring
  rw [hsq, h3, mul_assoc] at key
  have ha0 : ENNReal.ofReal a ≠ 0 := by simpa using ha
  have ha1 : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have key2 := (ENNReal.mul_right_inj ha0 ha1).1 key
  apply ennreal_sq_inj_aux
  rw [key2, mul_pow, ← ENNReal.ofReal_pow ha.le]

/-- **`velNorm_scale`** (source 3228-3240, `eq:ct-embeddings`): the `L²(cell)` norm of the
scaled velocity `a^{3/2} u(√a ·)` on `cell (c/√a)` is `a` times the norm of `u` on `cell c`. -/
theorem velNorm_scale (c a : ℝ) (hc : 0 < c) (ha : 0 < a) (u : ℝ × ℝ → Fin 2 → ℂ) :
    velNorm (cellLen c a) (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
      u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) = ENNReal.ofReal a * velNorm c u := by
  unfold velNorm
  have hcomp : ∀ j : Fin 2,
      eLpNorm (fun y : ℝ × ℝ => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
        u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) 2
        (volume.restrict (B0579.cell (cellLen c a))) =
      ENNReal.ofReal a * eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) :=
    fun j => eLpNorm_component_scale ha (fun x => u x j)
  simp only [hcomp]
  have hsum : ∑ j : Fin 2, (ENNReal.ofReal a * eLpNorm (fun x => u x j) 2
        (volume.restrict (B0579.cell c))) ^ 2 =
      (ENNReal.ofReal a ^ 2) * ∑ j : Fin 2, eLpNorm (fun x => u x j) 2
        (volume.restrict (B0579.cell c)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [← ENNReal.ofReal_pow ha.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le]

end UnforcedLeray.Short.IIIa
