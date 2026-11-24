import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# `PartIII-b:C/grad/3/4/1/2/1/9`: the decomposition leaf `GPsiProp`

Source `the November 2 reference manuscript`
4974-4975, 5063-5079.  The lattice term of `ψ^p_A` is
`Σ_{ab} A^y_{ab}(s) λ_{ab}` with `λ_{ab} = [a=b] ψ_j - (x_j)_b ∂_a ψ_j`, where
`ψ_j = -2 a⁻¹ E`, `∂_q ψ_j = u a⁻² E`, `∂_η ψ_j = η a⁻² E`, `E = exp(-(u²+η²)/(4a))`.
The kernel expressions are explicit, and the two partial derivatives are computed by one-variable
`HasDerivAt` along the coordinate lines.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The explicit kernel expressions `λ_{ab}` (level `0` only). -/
def gPsiE : Fin 2 → Fin 2 → GExpr :=
  ![![[(-2, 1, 0, 0), (-1, 2, 2, 0)], [(-1, 2, 1, 1)]],
    ![[(-1, 2, 1, 1)], [(-2, 1, 0, 0), (-1, 2, 0, 2)]]]

/-- The level-indexed family: only the coefficient level `r = 0` is used. -/
def gPsiEx : Fin 3 → Fin 2 → Fin 2 → GExpr :=
  fun r a b => if r = 0 then gPsiE a b else []

lemma gPsi_glevel : GLevel 0 gPsiEx := by
  intro r hr a b
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  simp [gPsiEx, hr0]

lemma gPsi_gEval_nil (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ) : gEval [] ν j s x = 0 := by
  simp [gEval]

lemma gPsi_lin (f : ℝ × ℝ → ℝ) (y w : ℝ × ℝ) :
    fderiv ℝ f y w = w.1 * fderiv ℝ f y (ei 0) + w.2 * fderiv ℝ f y (ei 1) := by
  have hw : w = w.1 • ei 0 + w.2 • ei 1 := by
    ext <;> simp [ei]
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `∂_q ψ_j = u a⁻² E` (one-variable derivative along the line `τ ↦ (τ, x2)`). -/
lemma gPsi_dq (ν s : ℝ) (j : ℤ) (hA : 0 < ageA ν s) (x1 x2 : ℝ) :
    fderiv ℝ (psij ν s j) (x1, x2) (ei 0) =
      (x1 - (j : ℝ) * cOf ν) * (ageA ν s)⁻¹ ^ 2 *
        Real.exp (-((x1 - (j : ℝ) * cOf ν) ^ 2 + x2 ^ 2) / (4 * ageA ν s)) := by
  have hA' : ageA ν s ≠ 0 := hA.ne'
  have hd : DifferentiableAt ℝ (psij ν s j) (x1, x2) := by
    unfold psij sq2 xj
    fun_prop
  have hp : HasDerivAt (fun τ : ℝ => ((τ, x2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x1 :=
    (hasDerivAt_id' x1).prodMk (hasDerivAt_const x1 x2)
  have hc := hd.hasFDerivAt.comp_hasDerivAt x1 hp
  have hei : ei 0 = ((1 : ℝ), (0 : ℝ)) := by simp [ei]
  have h1 : HasDerivAt (fun τ : ℝ => τ - (j : ℝ) * cOf ν) 1 x1 :=
    (hasDerivAt_id' x1).sub_const _
  have h2 := (h1.pow 2).add_const (x2 ^ 2)
  have h3 := (((h2.neg).div_const (4 * ageA ν s)).exp).const_mul (-2 * (ageA ν s)⁻¹)
  have hH : HasDerivAt (fun τ : ℝ => psij ν s j (τ, x2))
      ((x1 - (j : ℝ) * cOf ν) * (ageA ν s)⁻¹ ^ 2 *
        Real.exp (-((x1 - (j : ℝ) * cOf ν) ^ 2 + x2 ^ 2) / (4 * ageA ν s))) x1 := by
    refine h3.congr_deriv ?_
    norm_num
    field_simp
    ring
  rw [hei, ← hc.deriv]
  exact hH.deriv

/-- `∂_η ψ_j = η a⁻² E` (one-variable derivative along the line `η ↦ (x1, η)`). -/
lemma gPsi_deta (ν s : ℝ) (j : ℤ) (hA : 0 < ageA ν s) (x1 x2 : ℝ) :
    fderiv ℝ (psij ν s j) (x1, x2) (ei 1) =
      x2 * (ageA ν s)⁻¹ ^ 2 *
        Real.exp (-((x1 - (j : ℝ) * cOf ν) ^ 2 + x2 ^ 2) / (4 * ageA ν s)) := by
  have hA' : ageA ν s ≠ 0 := hA.ne'
  have hd : DifferentiableAt ℝ (psij ν s j) (x1, x2) := by
    unfold psij sq2 xj
    fun_prop
  have hp : HasDerivAt (fun η : ℝ => ((x1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x2 :=
    (hasDerivAt_const x2 x1).prodMk (hasDerivAt_id' x2)
  have hc := hd.hasFDerivAt.comp_hasDerivAt x2 hp
  have hei : ei 1 = ((0 : ℝ), (1 : ℝ)) := by simp [ei]
  have h2 := ((hasDerivAt_id' x2).pow 2).const_add ((x1 - (j : ℝ) * cOf ν) ^ 2)
  have h3 := (((h2.neg).div_const (4 * ageA ν s)).exp).const_mul (-2 * (ageA ν s)⁻¹)
  have hH : HasDerivAt (fun η : ℝ => psij ν s j (x1, η))
      (x2 * (ageA ν s)⁻¹ ^ 2 *
        Real.exp (-((x1 - (j : ℝ) * cOf ν) ^ 2 + x2 ^ 2) / (4 * ageA ν s))) x2 := by
    refine h3.congr_deriv ?_
    norm_num
    field_simp
    ring
  rw [hei, ← hc.deriv]
  exact hH.deriv

lemma gPsi_e00 (ν : ℝ) (j : ℤ) (s : ℝ) (hA : 0 < ageA ν s) (y : ℝ × ℝ) :
    gEval (gPsiE 0 0) ν j s y =
      psij ν s j y - (y.1 - (j : ℝ) * cOf ν) * fderiv ℝ (psij ν s j) y (ei 0) := by
  obtain ⟨y1, y2⟩ := y
  rw [gPsi_dq ν s j hA y1 y2]
  simp only [gPsiE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, gEval, gMon,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, psij, sq2, xj, pow_one, pow_zero,
    mul_one, one_mul]
  ring

lemma gPsi_e01 (ν : ℝ) (j : ℤ) (s : ℝ) (hA : 0 < ageA ν s) (y : ℝ × ℝ) :
    gEval (gPsiE 0 1) ν j s y = -y.2 * fderiv ℝ (psij ν s j) y (ei 0) := by
  obtain ⟨y1, y2⟩ := y
  rw [gPsi_dq ν s j hA y1 y2]
  simp only [gPsiE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, gEval, gMon,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_one, pow_zero,
    mul_one, one_mul]
  ring

lemma gPsi_e10 (ν : ℝ) (j : ℤ) (s : ℝ) (hA : 0 < ageA ν s) (y : ℝ × ℝ) :
    gEval (gPsiE 1 0) ν j s y = -(y.1 - (j : ℝ) * cOf ν) * fderiv ℝ (psij ν s j) y (ei 1) := by
  obtain ⟨y1, y2⟩ := y
  rw [gPsi_deta ν s j hA y1 y2]
  simp only [gPsiE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, gEval, gMon,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_one, pow_zero,
    mul_one, one_mul]
  ring

lemma gPsi_e11 (ν : ℝ) (j : ℤ) (s : ℝ) (hA : 0 < ageA ν s) (y : ℝ × ℝ) :
    gEval (gPsiE 1 1) ν j s y =
      psij ν s j y - y.2 * fderiv ℝ (psij ν s j) y (ei 1) := by
  obtain ⟨y1, y2⟩ := y
  rw [gPsi_deta ν s j hA y1 y2]
  simp only [gPsiE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, gEval, gMon,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, psij, sq2, xj, pow_one, pow_zero,
    mul_one, one_mul]
  ring

/-- Pointwise identity for one lattice term, at `s > 0`. -/
lemma gPsi_pt (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (hν : 0 < ν) (s : ℝ) (hs : 0 < s)
    (y : ℝ × ℝ) :
    gradPsiTm ν χf A j s y = GSum gPsiEx ν j (Ay ν χf A) s y := by
  have hA : 0 < ageA ν s := by
    have := mul_pos hν hs
    unfold ageA
    linarith
  have hG : GSum gPsiEx ν j (Ay ν χf A) s y =
      Ay ν χf A s 0 0 * gEval (gPsiE 0 0) ν j s y
        + Ay ν χf A s 0 2 * gEval (gPsiE 0 1) ν j s y
        + Ay ν χf A s 2 0 * gEval (gPsiE 1 0) ν j s y
        + Ay ν χf A s 2 2 * gEval (gPsiE 1 1) ν j s y := by
    unfold GSum
    simp [gPsiEx, gCoef, gPsi_gEval_nil, Fin.sum_univ_three, Fin.sum_univ_two, mi] <;> ring
  rw [hG]
  show psipATerm ν χf A s y j = _
  unfold psipATerm
  unfold merTrace merApply
  rw [gPsi_lin]
  rw [gPsi_e00 ν j s hA y, gPsi_e01 ν j s hA y, gPsi_e10 ν j s hA y, gPsi_e11 ν j s hA y]
  simp only [xj]
  ring

theorem gPsiProp : GPsiProp := by
  refine ⟨gPsiEx, gPsi_glevel, ?_⟩
  intro ν χf A j hν s hs
  unfold GCombo
  exact Filter.eventually_of_mem (Ioi_mem_nhds hs) (fun s' hs' y => gPsi_pt ν χf A j hν s' hs' y)

end UnforcedLeray.Short.PartIIIb.Concrete
