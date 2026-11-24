import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3Eq

/-!
# Part II-a, block `B₃`: the leaf `CoeffB3QEq` (task `PartII-a:R02/11/4`)

Target: `coeffB3QEq : CoeffB3QEq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`partialQ (coeffB₃ ν g) x = ν * (-jet 0 0 1 g x - jet 1 0 1 g x + jet 2 0 1 g x + jet 3 0 1 g x)`.

Source of record: `the November 2 reference manuscript`, lines 1250-1267 (B3; every
`q` derivative is exponentially small).

Route: `coeffB3Eq` gives `B₃[g] = ν(-g - Kg + K²g + K³g)` on `{s > 0}`, hence (locality of `∂_q`)
`∂_q B₃[g] = ν(-∂_q g - ∂_q Kg + ∂_q K²g + ∂_q K³g)` at `x`.  The commutation `[K, ∂_q] = 0`
(`partialQ_ageOperator`, needs `C²` at the point) gives `∂_q K^n g = K^n ∂_q g` on `{s > 0}` by
induction on `n`, and the jets `jet n 0 1 g` are the iterates `K^n ∂_q g`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- Locality of `∂_q` on a neighbourhood. -/
theorem pq_congr_of {F G : ProfilePoint → ℝ} {x : ProfilePoint} (h : F =ᶠ[𝓝 x] G) :
    partialQ F x = partialQ G x := by
  unfold partialQ
  rw [h.fderiv_eq]

/-- `∂_q` of a constant multiple at a point of differentiability. -/
theorem pq_const_mul_of (c : ℝ) {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : DifferentiableAt ℝ f x) :
    partialQ (fun y => c * f y) x = c * partialQ f x := by
  unfold partialQ
  rw [fderiv_const_mul hf]
  simp

/-- `∂_q` of a four-term linear combination at a point of differentiability. -/
theorem pq4_of (f0 f1 f2 f3 : ProfilePoint → ℝ) {x : ProfilePoint}
    (h0 : DifferentiableAt ℝ f0 x) (h1 : DifferentiableAt ℝ f1 x)
    (h2 : DifferentiableAt ℝ f2 x) (h3 : DifferentiableAt ℝ f3 x) (a0 a1 a2 a3 : ℝ) :
    partialQ (fun y => a0 * f0 y + a1 * f1 y + a2 * f2 y + a3 * f3 y) x =
      a0 * partialQ f0 x + a1 * partialQ f1 x + a2 * partialQ f2 x + a3 * partialQ f3 x := by
  have h01 : DifferentiableAt ℝ (fun y => a0 * f0 y) x := h0.const_mul a0
  have h012 : DifferentiableAt ℝ (fun y => a0 * f0 y + a1 * f1 y) x :=
    h01.add (h1.const_mul a1)
  have h0123 : DifferentiableAt ℝ (fun y => a0 * f0 y + a1 * f1 y + a2 * f2 y) x :=
    h012.add (h2.const_mul a2)
  rw [partialQ_add_mul h0123 h3 a3, partialQ_add_mul h012 h2 a2, partialQ_add_mul h01 h1 a1,
    pq_const_mul_of a0 h0]

/-- **Leaf `CoeffB3QEq`** (source lines 1250-1267): `∂_qB₃[g] = ν(-∂_qg - K∂_qg + K²∂_qg + K³∂_qg)`
on `{s > 0}`, using `[K, ∂_q] = 0` and `B₃ = ν(-g - Kg + K²g + K³g)` (`coeffB3Eq`). -/
theorem coeffB3QEq : CoeffB3QEq := by
  unfold CoeffB3QEq
  intro ν g hg x hx
  -- smoothness of the iterates `K^n g` on `{s > 0}`
  have hK : ∀ n : ℕ, ContDiffOn ℝ ∞ (ageOperator^[n] g) {y : ProfilePoint | 0 < y.2.2} := by
    intro n
    induction n with
    | zero => exact hg
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact contDiffOn_ageOperator ih
  -- `∂_q K^n g = K^n ∂_q g` on `{s > 0}` (commutator `[K, ∂_q] = 0`, by induction)
  have hC : ∀ n : ℕ, ∀ y : ProfilePoint, 0 < y.2.2 →
      partialQ (ageOperator^[n] g) y = ageOperator^[n] (partialQ g) y := by
    intro n
    induction n with
    | zero => intro y _; rfl
    | succ n ih =>
      intro y hy
      have hCa : ContDiffAt ℝ 2 (ageOperator^[n] g) y :=
        ((hK n).contDiffAt (isOpen_late.mem_nhds hy)).of_le (by simp)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', partialQ_ageOperator hCa]
      apply kx_ageOp_congr
      exact Filter.eventually_of_mem (isOpen_late.mem_nhds hy) (fun z hz => ih z hz)
  have hd0 : DifferentiableAt ℝ g x := differentiableAt_of_late hg hx
  have hd1 : DifferentiableAt ℝ (ageOperator g) x :=
    differentiableAt_of_late (contDiffOn_ageOperator hg) hx
  have hd2 : DifferentiableAt ℝ (ageOperator (ageOperator g)) x :=
    differentiableAt_of_late (contDiffOn_ageOperator (contDiffOn_ageOperator hg)) hx
  have hd3 : DifferentiableAt ℝ (ageOperator (ageOperator (ageOperator g))) x :=
    differentiableAt_of_late
      (contDiffOn_ageOperator (contDiffOn_ageOperator (contDiffOn_ageOperator hg))) hx
  have hΦ : DifferentiableAt ℝ
      (fun y => -1 * g y + (-1) * ageOperator g y + 1 * ageOperator (ageOperator g) y +
        1 * ageOperator (ageOperator (ageOperator g)) y) x :=
    ((((hd0.const_mul (-1)).add (hd1.const_mul (-1))).add (hd2.const_mul 1)).add
      (hd3.const_mul 1))
  -- pointwise form of `B₃` on `{s > 0}`
  have hE : ∀ y : ProfilePoint, 0 < y.2.2 →
      coeffB₃ ν g y = ν * (-1 * g y + (-1) * ageOperator g y +
        1 * ageOperator (ageOperator g) y + 1 * ageOperator (ageOperator (ageOperator g)) y) := by
    intro y hy
    have h : coeffB₃ ν g y = ν * (-g y - ageOperator g y + ageOperator (ageOperator g) y +
        ageOperator (ageOperator (ageOperator g)) y) := coeffB3Eq ν g hg y hy
    rw [h]
    ring
  have hev : coeffB₃ ν g =ᶠ[𝓝 x] (fun y => ν * (-1 * g y + (-1) * ageOperator g y +
      1 * ageOperator (ageOperator g) y + 1 * ageOperator (ageOperator (ageOperator g)) y)) :=
    Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun y hy => hE y hy)
  have c1 : partialQ (ageOperator g) x = ageOperator (partialQ g) x := hC 1 x hx
  have c2 : partialQ (ageOperator (ageOperator g)) x =
      ageOperator (ageOperator (partialQ g)) x := hC 2 x hx
  have c3 : partialQ (ageOperator (ageOperator (ageOperator g))) x =
      ageOperator (ageOperator (ageOperator (partialQ g))) x := hC 3 x hx
  rw [pq_congr_of hev, pq_const_mul_of ν hΦ,
    pq4_of g (ageOperator g) (ageOperator (ageOperator g))
      (ageOperator (ageOperator (ageOperator g))) hd0 hd1 hd2 hd3 (-1) (-1) 1 1,
    c1, c2, c3]
  show ν * (-1 * partialQ g x + (-1) * ageOperator (partialQ g) x +
      1 * ageOperator (ageOperator (partialQ g)) x +
      1 * ageOperator (ageOperator (ageOperator (partialQ g))) x) =
    ν * (-partialQ g x - ageOperator (partialQ g) x + ageOperator (ageOperator (partialQ g)) x +
      ageOperator (ageOperator (ageOperator (partialQ g))) x)
  ring

end UnforcedLeray.Short.PartIIa.BlockB3
