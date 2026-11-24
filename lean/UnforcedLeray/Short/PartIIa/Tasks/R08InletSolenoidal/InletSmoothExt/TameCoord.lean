import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/6`: the coordinates are tame

Source of record: `the November 2 reference manuscript`, lines 1330-1334
("Each derivative costs `C/r`"; "including smoothness at nonzero axis points").

This file proves the Prop `TameCoord` of `Sub/R08_2.lean`: for all `δ M`, the coordinate
`y ↦ y 2`, the horizontal part `Axi.hor`, and every constant `y ↦ v` (in any normed space `E`)
are `FlatOn (flatRegion δ M) 0`.

Method. Each map is a continuous linear map (`EuclideanSpace.proj 2`, `Axi.horL`) or a constant,
hence `C^∞`. With `κ = 0` and `N = 0`, the flatness bound is a uniform bound on each iterated
derivative over the region. The zeroth derivative is bounded on `flatRegion δ M`: by `|y 2| ≤ M`
for the coordinate, and by `‖hor y‖ ≤ 1` from `ϱ y < 1` for `hor`. A continuous linear map has
first derivative `L` and vanishing higher derivatives. A constant has vanishing derivatives of
order `≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- A `C^∞` function whose iterated derivatives are bounded on `W` is `FlatOn W 0`
(take `N = 0`, `C = B`; then `exp (-0 / ϱ²) = 1`). -/
theorem tcdFlatOfBdd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set Space}
    {f : Space → E} (hf : ContDiff ℝ ∞ f)
    (hW : ∀ n : ℕ, ∃ B : ℝ, ∀ y ∈ W, ‖iteratedFDeriv ℝ n f y‖ ≤ B) : FlatOn W 0 f := by
  refine ⟨hf.contDiffOn, fun n => ?_⟩
  obtain ⟨B, hB⟩ := hW n
  exact ⟨B, 0, fun y hy => by simpa using hB y hy⟩

/-- Iterated derivatives of order `k + 1` of a continuous linear map `L` are at most `‖L‖`:
for `k = 0` the derivative is `L`, and for `k ≥ 1` it is `0`. -/
theorem tcdIterClmSucc {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Space →L[ℝ] F) (k : ℕ) (x : Space) : ‖iteratedFDeriv ℝ (k + 1) (⇑L) x‖ ≤ ‖L‖ := by
  cases k with
  | zero => simp
  | succ k =>
    have hfd : fderiv ℝ (⇑L) = fun _ : Space => L := funext fun y => by simp
    rw [← norm_iteratedFDeriv_fderiv, hfd, iteratedFDeriv_succ_const]
    simp

/-- A continuous linear map `f = L`, bounded on `W`, is `FlatOn W 0`. -/
theorem tcdFlatClm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {W : Set Space}
    (L : Space →L[ℝ] F) (f : Space → F) (hf : f = ⇑L) (hW : ∃ B : ℝ, ∀ y ∈ W, ‖f y‖ ≤ B) :
    FlatOn W 0 f := by
  subst hf
  refine tcdFlatOfBdd L.contDiff fun n => ?_
  cases n with
  | zero =>
    obtain ⟨B, hB⟩ := hW
    exact ⟨B, fun y hy => by simpa using hB y hy⟩
  | succ k => exact ⟨‖L‖, fun y _ => tcdIterClmSucc L k y⟩

/-- Membership in `flatRegion δ M`, unfolded. -/
theorem tcdMemFlat {δ M : ℝ} {y : Space} (hy : y ∈ flatRegion δ M) :
    y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M := hy

/-- On `ϱ < 1` the horizontal part has norm at most `1`: `‖hor y‖² = ϱ(y)²`. -/
theorem tcdNormHorLe {y : Space} (h : Axi.ϱ y < 1) : ‖Axi.hor y‖ ≤ 1 := by
  have hsq : ‖Axi.hor y‖ ^ 2 = Axi.ϱ y ^ 2 := by
    rw [Axi.ϱ_sq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp
  have h0 : 0 ≤ Axi.ϱ y := Axi.ϱ_nonneg y
  nlinarith [norm_nonneg (Axi.hor y), mul_nonneg h0 (sub_nonneg.2 h.le)]

/-- A constant function is `FlatOn W 0` for every `W`. -/
theorem tcdFlatConst {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set Space}
    (v : E) : FlatOn W 0 (fun _ : Space => v) := by
  refine tcdFlatOfBdd contDiff_const fun n => ?_
  cases n with
  | zero => exact ⟨‖v‖, fun y _ => by simp⟩
  | succ k => exact ⟨‖v‖, fun y _ => by rw [iteratedFDeriv_succ_const]; simp⟩

/-- **`TameCoord`** (task `PartII-a:R08/2/6`, source lines 1330-1334): `y ↦ y 2`, `Axi.hor`
and every constant are tame on `flatRegion δ M`. -/
theorem tameCoord : TameCoord := by
  intro δ M
  refine ⟨?_, ?_, ?_⟩
  · refine tcdFlatClm (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (fun y : Space => y 2)
      rfl ⟨M, fun y hy => ?_⟩
    show ‖y 2‖ ≤ M
    rw [Real.norm_eq_abs]
    exact (tcdMemFlat hy).2.2.2
  · refine tcdFlatClm Axi.horL Axi.hor (funext fun v => (Axi.horL_apply v).symm)
      ⟨1, fun y hy => tcdNormHorLe (tcdMemFlat hy).2.1⟩
  · intro E _ _ v
    exact tcdFlatConst v

end UnforcedLeray.Short.PartIIa
