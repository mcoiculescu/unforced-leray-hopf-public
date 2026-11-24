import UnforcedLeray.Short.PartIIIa.Sub.T20

/-!
# Part III-a, task `PartIII-a:T20/5`: `velNorm` is the `Lp` norm

Source of record: `the November 2 reference manuscript`, lines 3230-3240
(the `eq:ct-embeddings` block whose norm `velNorm` is used). Target: `CTE.VelNormEqLp`
(`Sub/T20.lean`).

Proof. Write `G = ⇑F` and `μ = cellVol c = volume.restrict (cell c)`.
* `‖G x‖ₑ ^ 2 = ∑ j, ‖G x j‖ₑ ^ 2` pointwise (`EuclideanSpace.nnnorm_eq`).
* Each component satisfies `eLpNorm (G · j) 2 μ ^ 2 = ∫⁻ ‖G x j‖ₑ ^ 2 dμ`.
* Summing over `j` and exchanging the finite sum with the integral gives
  `∑ j, eLpNorm (G · j) 2 μ ^ 2 = ∫⁻ ‖G x‖ₑ ^ 2 dμ`, so `velNorm c G = eLpNorm G 2 μ`.
* `‖F‖ = (eLpNorm G 2 μ).toReal` and `eLpNorm G 2 μ < ∞`, so `ofReal ‖F‖ = eLpNorm G 2 μ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace CTE

/-- `‖v‖ₑ ^ 2 = ∑ i, ‖v i‖ₑ ^ 2` on `EuclideanSpace ℂ (Fin 2)`. -/
private lemma enorm_sq_euclid_aux (v : B0581.Vel) :
    ‖v‖ₑ ^ 2 = ∑ i : Fin 2, ‖v i‖ₑ ^ 2 := by
  have h : ‖v‖₊ ^ 2 = ∑ i : Fin 2, ‖v i‖₊ ^ 2 := by
    rw [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt]
  simp only [enorm_eq_nnnorm]
  rw [← ENNReal.coe_pow, h, ENNReal.ofNNReal_finsetSum]
  simp only [ENNReal.coe_pow]

/-- The `L²` norm of a function on `ℝ × ℝ` as the square root of a lintegral. -/
private lemma eLpNorm_two_eq_aux {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', htr]
  simp only [ENNReal.rpow_two]

/-- `((a ^ (1/2)) ^ 2 = a` in `ℝ≥0∞`. -/
private lemma rpow_half_sq_aux (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **`velNorm` is the `Lp` norm**: for an `L²(cell; ℂ²)` element `F`,
`velNorm c F = ofReal ‖F‖` (`‖F x‖² = ∑_j |F x j|²` in `EuclideanSpace ℂ (Fin 2)`). -/
theorem velNorm_eq_lp : VelNormEqLp := by
  unfold VelNormEqLp
  intro c _ F
  have hG : AEStronglyMeasurable (F : B0579.Plane → B0581.Vel) (B0581.cellVol c) :=
    Lp.aestronglyMeasurable F
  have hcoord : ∀ j : Fin 2,
      AEMeasurable (fun x => ‖(F : B0579.Plane → B0581.Vel) x j‖ₑ ^ 2) (B0581.cellVol c) := by
    intro j
    have h1 : AEStronglyMeasurable (fun x => (F : B0579.Plane → B0581.Vel) x j)
        (B0581.cellVol c) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) j).comp_aestronglyMeasurable hG
    exact (h1.enorm).pow_const 2
  have hcomp : ∀ j : Fin 2,
      eLpNorm (fun x => (F : B0579.Plane → B0581.Vel) x j) 2 (B0581.cellVol c) ^ 2
        = ∫⁻ x, ‖(F : B0579.Plane → B0581.Vel) x j‖ₑ ^ 2 ∂(B0581.cellVol c) := by
    intro j
    rw [eLpNorm_two_eq_aux, rpow_half_sq_aux]
  have hsum : ∑ j : Fin 2,
      eLpNorm (fun x => (F : B0579.Plane → B0581.Vel) x j) 2 (B0581.cellVol c) ^ 2
        = ∫⁻ x, ‖(F : B0579.Plane → B0581.Vel) x‖ₑ ^ 2 ∂(B0581.cellVol c) := by
    calc ∑ j : Fin 2,
          eLpNorm (fun x => (F : B0579.Plane → B0581.Vel) x j) 2 (B0581.cellVol c) ^ 2
        = ∑ j : Fin 2, ∫⁻ x, ‖(F : B0579.Plane → B0581.Vel) x j‖ₑ ^ 2 ∂(B0581.cellVol c) :=
          Finset.sum_congr rfl (fun j _ => hcomp j)
      _ = ∫⁻ x, ∑ j : Fin 2, ‖(F : B0579.Plane → B0581.Vel) x j‖ₑ ^ 2 ∂(B0581.cellVol c) :=
          (lintegral_finsetSum' _ (fun j _ => hcoord j)).symm
      _ = ∫⁻ x, ‖(F : B0579.Plane → B0581.Vel) x‖ₑ ^ 2 ∂(B0581.cellVol c) :=
          lintegral_congr (fun x => (enorm_sq_euclid_aux _).symm)
  show (∑ j : Fin 2,
      eLpNorm (fun x => (F : B0579.Plane → B0581.Vel) x j) 2 (B0581.cellVol c) ^ 2) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal ‖F‖
  rw [hsum, ← eLpNorm_two_eq_aux, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]

end CTE

end UnforcedLeray.Short.IIIa
