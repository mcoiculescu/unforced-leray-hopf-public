import UnforcedLeray.Blueprint.Localization.Nonlinear

/-!
# L9 helper: cross-product algebra on `ℝ³`

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 430–461, blueprint
units B0717–B0720). Coordinate identities for the Blueprint cross product `crossProd`:
bilinearity and its continuous bilinear form `crossCLM`, `a × (b × c) = ⟨a,c⟩b - ⟨a,b⟩c`,
`∑ⱼ eⱼ × (eⱼ × v) = -2v`, `∑ⱼ eⱼ × (x × wⱼ) = (∑ⱼ (wⱼ)ⱼ) x - ∑ⱼ xⱼ wⱼ`, and the algebraic
core of `div curl = 0` (a symmetric family of second derivatives). They give
`curl[r x × u(rx)] = -∂_r[r² u(rx)]` (line 437) once `div u = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

theorem crossProd_coord0 (a b : Space) : crossProd a b 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [crossProd, cross_apply]

theorem crossProd_coord1 (a b : Space) : crossProd a b 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [crossProd, cross_apply]

theorem crossProd_coord2 (a b : Space) : crossProd a b 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [crossProd, cross_apply]

theorem coordinateVector_apply (i j : Fin 3) :
    coordinateVector j i = if i = j then 1 else 0 := by
  simp [coordinateVector]

@[simp] theorem cv00 : coordinateVector 0 0 = 1 := by simp [coordinateVector]
@[simp] theorem cv01 : coordinateVector 0 1 = 0 := by simp [coordinateVector]
@[simp] theorem cv02 : coordinateVector 0 2 = 0 := by simp [coordinateVector]
@[simp] theorem cv10 : coordinateVector 1 0 = 0 := by simp [coordinateVector]
@[simp] theorem cv11 : coordinateVector 1 1 = 1 := by simp [coordinateVector]
@[simp] theorem cv12 : coordinateVector 1 2 = 0 := by simp [coordinateVector]
@[simp] theorem cv20 : coordinateVector 2 0 = 0 := by simp [coordinateVector]
@[simp] theorem cv21 : coordinateVector 2 1 = 0 := by simp [coordinateVector]
@[simp] theorem cv22 : coordinateVector 2 2 = 1 := by simp [coordinateVector]

theorem inner_coords (a b : Space) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- The coordinate lemmas used by `cross_simp`. -/
theorem space_ext_iff (a b : Space) : a = b ↔ a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

theorem crossProd_add_left (a a' b : Space) :
    crossProd (a + a') b = crossProd a b + crossProd a' b := by
  rw [space_ext_iff]
  simp only [crossProd_coord0, crossProd_coord1, crossProd_coord2, PiLp.add_apply]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem crossProd_add_right (a b b' : Space) :
    crossProd a (b + b') = crossProd a b + crossProd a b' := by
  rw [space_ext_iff]
  simp only [crossProd_coord0, crossProd_coord1, crossProd_coord2, PiLp.add_apply]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem crossProd_smul_left (c : ℝ) (a b : Space) :
    crossProd (c • a) b = c • crossProd a b := by
  rw [space_ext_iff]
  simp only [crossProd_coord0, crossProd_coord1, crossProd_coord2, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem crossProd_smul_right (c : ℝ) (a b : Space) :
    crossProd a (c • b) = c • crossProd a b := by
  rw [space_ext_iff]
  simp only [crossProd_coord0, crossProd_coord1, crossProd_coord2, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

@[simp] theorem crossProd_zero_left (b : Space) : crossProd 0 b = 0 := by
  simpa using crossProd_smul_left 0 0 b

@[simp] theorem crossProd_zero_right (a : Space) : crossProd a 0 = 0 := by
  simpa using crossProd_smul_right 0 a 0

/-- The cross product as a bilinear map. -/
def crossLin : Space →ₗ[ℝ] Space →ₗ[ℝ] Space :=
  LinearMap.mk₂ ℝ crossProd crossProd_add_left (fun c a b => crossProd_smul_left c a b)
    crossProd_add_right (fun c a b => crossProd_smul_right c a b)

/-- The cross product as a continuous bilinear map. -/
def crossCLM : Space →L[ℝ] Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Space →ₗ[ℝ] Space) ≃ₗ[ℝ] (Space →L[ℝ] Space)).toLinearMap
      ∘ₗ crossLin)

@[simp] theorem crossCLM_apply (a b : Space) : crossCLM a b = crossProd a b := by
  simp [crossCLM, crossLin]

theorem norm_crossProd_le (a b : Space) : ‖crossProd a b‖ ≤ ‖crossCLM‖ * ‖a‖ * ‖b‖ := by
  rw [← crossCLM_apply]
  exact crossCLM.le_opNorm₂ a b

/-- `a × (b × c) = ⟨a,c⟩ b - ⟨a,b⟩ c`. -/
theorem crossProd_crossProd (a b c : Space) :
    crossProd a (crossProd b c) = inner ℝ a c • b - inner ℝ a b • c := by
  rw [space_ext_iff]
  simp only [crossProd_coord0, crossProd_coord1, crossProd_coord2, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, inner_coords]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `∑ⱼ xⱼ eⱼ = x`. -/
theorem sum_coord_smul_basis (x : Space) : ∑ j : Fin 3, x j • coordinateVector j = x := by
  rw [space_ext_iff]
  simp [Fin.sum_univ_three]

/-- `∑ⱼ eⱼ × (eⱼ × v) = -2v`. -/
theorem sum_cross_cross_basis (v : Space) :
    ∑ j : Fin 3, crossProd (coordinateVector j) (crossProd (coordinateVector j) v) =
      (-2 : ℝ) • v := by
  rw [space_ext_iff]
  simp only [Fin.sum_univ_three, PiLp.add_apply, crossProd_coord0, crossProd_coord1,
    crossProd_coord2, cv00, cv01, cv02, cv10, cv11, cv12, cv20, cv21, cv22, PiLp.smul_apply,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `∑ⱼ eⱼ × (x × wⱼ) = (∑ⱼ (wⱼ)ⱼ) x - ∑ⱼ xⱼ wⱼ`. -/
theorem sum_cross_cross_family (x : Space) (w : Fin 3 → Space) :
    ∑ j : Fin 3, crossProd (coordinateVector j) (crossProd x (w j)) =
      (∑ j : Fin 3, w j j) • x - ∑ j : Fin 3, x j • w j := by
  rw [space_ext_iff]
  simp only [Fin.sum_univ_three, PiLp.add_apply, PiLp.sub_apply, crossProd_coord0,
    crossProd_coord1, crossProd_coord2, cv00, cv01, cv02, cv10, cv11, cv12, cv20, cv21, cv22, PiLp.smul_apply,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `∑ⱼ (∂ⱼ c) eⱼ × a = (∑ⱼ (∂ⱼ c) eⱼ) × a`, pulled out of a curl. -/
theorem sum_crossProd_smul (d : Fin 3 → ℝ) (a : Space) :
    ∑ j : Fin 3, crossProd (coordinateVector j) (d j • a) =
      crossProd (∑ j : Fin 3, d j • coordinateVector j) a := by
  rw [space_ext_iff]
  simp only [Fin.sum_univ_three, PiLp.add_apply, crossProd_coord0,
    crossProd_coord1, crossProd_coord2, cv00, cv01, cv02, cv10, cv11, cv12, cv20, cv21, cv22, PiLp.smul_apply,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The algebraic core of `div curl = 0`: for a symmetric family `M i j = M j i` of vectors,
`∑ᵢ (∑ⱼ eⱼ × M i j)ᵢ = 0`. -/
theorem sum_coord_sum_cross_symm (M : Fin 3 → Fin 3 → Space)
    (hM : ∀ i j, M i j = M j i) :
    ∑ i : Fin 3, (∑ j : Fin 3, crossProd (coordinateVector j) (M i j)) i = 0 := by
  simp only [Fin.sum_univ_three, PiLp.add_apply, crossProd_coord0,
    crossProd_coord1, crossProd_coord2, cv00, cv01, cv02, cv10, cv11, cv12, cv20, cv21, cv22]
  rw [hM 1 0, hM 2 0, hM 2 1]
  ring

end UnforcedLeray.L09
