import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonD3Div

/-!
# `PartIII-b:C/rep/8/1/1/1/3/2/1`: the Newton kernel dictionary `KernelDict`

Source `the November 2 reference manuscript`
lines 3600-3610 (`K_0 = D^2(4π|x|)^{-1}` off the origin) and 4776-4782 (`D^3 N`, `N = 1/(4π|x|)`,
`newtonD3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace TWBridge

/-- The continuous linear equivalence `Space ≃L[ℝ] Vec3` (`WithLp.ofLp`). -/
def euFrom : Space ≃L[ℝ] Vec3 := EuclideanSpace.equiv (Fin 3) ℝ

theorem euFrom_apply (x : Space) : euFrom x = WithLp.ofLp x := rfl

theorem euFrom_coord (a : Fin 3) : euFrom (coordinateVector a) = Pi.single a 1 := by
  ext b
  simp [euFrom, coordinateVector, Pi.single_apply]

theorem euFrom_ne_zero {x : Space} (hx : x ≠ 0) : WithLp.ofLp x ≠ 0 := by
  intro h
  apply hx
  exact WithLp.ofLp_injective 2 h

theorem fderiv_comp_euFrom (G : Vec3 → ℝ) (x : Space) (a : Fin 3) :
    fderiv ℝ (fun y : Space => G (euFrom y)) x (coordinateVector a) =
      DaxD a G (euFrom x) := by
  have hd : fderiv ℝ (G ∘ euFrom) x =
      (fderiv ℝ G (euFrom x)).comp (euFrom : Space →L[ℝ] Vec3) :=
    ContinuousLinearEquiv.comp_right_fderiv euFrom
  change (fderiv ℝ (G ∘ euFrom) x) (coordinateVector a) = _
  rw [hd]
  change fderiv ℝ G (euFrom x) (euFrom (coordinateVector a)) = _
  rw [euFrom_coord a]
  rfl

theorem newtonN_euFrom (y : Space) :
    (4 * Real.pi * ‖y‖)⁻¹ = newtonN (euFrom y) := by
  unfold newtonN
  rw [one_div, EuclideanSpace.norm_eq]
  have h : ∑ i : Fin 3, ‖y i‖ ^ 2 = ∑ i : Fin 3, (euFrom y) i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    rfl
  rw [h]

theorem heatLerayK0_eq_DaxD (i j : Fin 3) (x : Space) :
    IIIa.heatLerayK0 i j x = DaxD i (DaxD j newtonN) (euFrom x) := by
  unfold IIIa.heatLerayK0 IIIa.part2
  have h1 : (fun y : Space => (4 * Real.pi * ‖y‖)⁻¹) = fun y => newtonN (euFrom y) :=
    funext newtonN_euFrom
  have h2 : (fun y : Space => fderiv ℝ (fun z => (4 * Real.pi * ‖z‖)⁻¹) y (coordinateVector j)) =
      fun y => DaxD j newtonN (euFrom y) := by
    funext y
    rw [h1, fderiv_comp_euFrom]
  rw [h2, fderiv_comp_euFrom]

theorem newtonD3_symm23 {w : Vec3} (hw : w ≠ 0) (i j k : Fin 3) :
    newtonD3 w i j k = newtonD3 w i k j := by
  have hN : ContDiffOn ℝ NewtonD3.ii newtonN NewtonD3.punct := NewtonD3.newtonN_contDiffOn
  show fderiv ℝ (DaxD j (DaxD k newtonN)) w (Pi.single i 1) =
    fderiv ℝ (DaxD k (DaxD j newtonN)) w (Pi.single i 1)
  exact congrFD (f := DaxD j (DaxD k newtonN)) (g := DaxD k (DaxD j newtonN))
    (fun y hy => swap_ptD hN hy j k) hw (Pi.single i 1)

end TWBridge

theorem kernelDict : TWBridge.KernelDict := by
  intro x hx i j k
  have hw : WithLp.ofLp x ≠ 0 := TWBridge.euFrom_ne_zero hx
  have hsym : newtonD3 (WithLp.ofLp x) i j k = newtonD3 (WithLp.ofLp x) i k j :=
    TWBridge.newtonD3_symm23 hw i j k
  refine ⟨?_, hsym⟩
  have h1 : (fun x' : Space => IIIa.heatLerayK0 i j x') =
      fun x' => DaxD i (DaxD j newtonN) (TWBridge.euFrom x') :=
    funext (TWBridge.heatLerayK0_eq_DaxD i j)
  rw [h1, TWBridge.fderiv_comp_euFrom, TWBridge.euFrom_apply]
  have hN : ContDiffOn ℝ NewtonD3.ii newtonN NewtonD3.punct := NewtonD3.newtonN_contDiffOn
  have hDj : ContDiffOn ℝ NewtonD3.ii (DaxD j newtonN) NewtonD3.punct := DaxD_smooth hN j
  rw [swap_ptD hDj hw k i]
  exact hsym.symm

end UnforcedLeray.Short.PartIIIb.Concrete
