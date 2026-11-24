import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Lap.Trace

/-!
# Equivariance of the second-order contractions (`PartIII-b:IIIb-D2/3/2/11/4`, source 4280-4282,
6314-6316)

`cdiffUUD2Eqv_proved`: `C_diff` and `(U ⊗ U):D²X` commute with a linear isometry `g` when `U` and
`X` do.  `C_diff` is the trace `∑_j Ψ(e_j, e_j)` of the bilinear map
`Ψ(u, v) = D²X(u, DU v) - D²U(u, DX v)` (`cdiffPsi`), so `trace_equiv` applies; `(U ⊗ U):D²X` is
`D²X(U, U)` (`coord_expand`, `coord_expand_left`) and uses the equivariance of `D²X` directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The bilinear map whose trace is `C_diff`. -/
def cdiffPsi (U X : Space → Space) (y u v : Space) : Space :=
  hessOp X y u (fderiv ℝ U y v) - hessOp U y u (fderiv ℝ X y v)

theorem cdiffUUD2Eqv_proved : CdiffUUD2Eqv := by
  intro g U X hU hX hGU hGX y
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hC : ∀ z, physCdiff U X z =
      ∑ j : Fin 3, cdiffPsi U X z (coordinateVector j) (coordinateVector j) := by
    intro z
    unfold physCdiff cdiffPsi
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_sub_distrib]
    congr 1
    · exact coord_expand (Ψ := fun u v => hessOp X z u v) (hess_add_right hX z)
        (hess_smul_right hX z) (coordinateVector j) (fderiv ℝ U z (coordinateVector j))
    · exact coord_expand (Ψ := fun u v => hessOp U z u v) (hess_add_right hU z)
        (hess_smul_right hU z) (coordinateVector j) (fderiv ℝ X z (coordinateVector j))
  have hUU : ∀ z, hessOp X z (U z) (U z) = physUUD2 U X z := by
    intro z
    unfold physUUD2
    calc hessOp X z (U z) (U z)
        = ∑ l : Fin 3, U z l • hessOp X z (U z) (coordinateVector l) :=
          (coord_expand (Ψ := fun u v => hessOp X z u v) (hess_add_right hX z)
            (hess_smul_right hX z) (U z) (U z)).symm
      _ = ∑ l : Fin 3, U z l • ∑ j : Fin 3, U z j • hessOp X z (coordinateVector j)
            (coordinateVector l) :=
          Finset.sum_congr rfl fun l _ =>
            congrArg (fun t => U z l • t)
              (coord_expand_left (Ψ := fun u v => hessOp X z u v) (hess_add_left X z)
                (hess_smul_left X z) (U z) (coordinateVector l)).symm
      _ = ∑ j : Fin 3, ∑ l : Fin 3, (U z j * U z l) • hessOp X z (coordinateVector j)
            (coordinateVector l) := by
          simp only [Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by
            rw [mul_comm]
  have hequiv : ∀ z u v, cdiffPsi U X (g z) (g u) (g v) = g (cdiffPsi U X z u v) := by
    intro z u v
    unfold cdiffPsi
    rw [fderivEqv_proved g U hUd hGU z v, fderivEqv_proved g X hXd hGX z v,
      hess_equiv g X hX hGX z u (fderiv ℝ U z v), hess_equiv g U hU hGU z u (fderiv ℝ X z v),
      map_sub]
  have hP1 : ∀ z u u' v, cdiffPsi U X z (u + u') v = cdiffPsi U X z u v + cdiffPsi U X z u' v := by
    intro z u u' v
    unfold cdiffPsi
    rw [hess_add_left X z, hess_add_left U z]
    abel
  have hP2 : ∀ z (c : ℝ) u v, cdiffPsi U X z (c • u) v = c • cdiffPsi U X z u v := by
    intro z c u v
    unfold cdiffPsi
    rw [hess_smul_left X z, hess_smul_left U z, smul_sub]
  have hP3 : ∀ z u v v', cdiffPsi U X z u (v + v') = cdiffPsi U X z u v + cdiffPsi U X z u v' := by
    intro z u v v'
    unfold cdiffPsi
    rw [map_add, map_add, hess_add_right hX z, hess_add_right hU z]
    abel
  have hP4 : ∀ z (c : ℝ) u v, cdiffPsi U X z u (c • v) = c • cdiffPsi U X z u v := by
    intro z c u v
    unfold cdiffPsi
    rw [map_smul, map_smul, hess_smul_right hX z, hess_smul_right hU z, smul_sub]
  constructor
  · rw [hC (g y), hC y]
    exact trace_equiv g (cdiffPsi U X) hequiv hP1 hP2 hP3 hP4 y
  · rw [← hUU (g y), ← hUU y, hGU y]
    exact hess_equiv g X hX hGX y (U y) (U y)

end UnforcedLeray.Short.PartIIIb.Concrete
