import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonD3Div

/-!
# Harmonicity of the third Newton derivative (source 4797-4800, 5383-5387)

`Σ_l ∂_l∂_l (∂_i∂_j∂_k N) = 0` off the origin, in the `iteratedFDeriv` trace form.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The second derivative along `(e_l, e_l)` as a nested directional derivative. -/
theorem iter2_diag {f : Vec3 → ℝ} {w : Vec3} (hf : ContDiffAt ℝ 2 f w) (l : Fin 3) :
    iteratedFDeriv ℝ 2 f w ![Pi.single l 1, Pi.single l 1] =
      fderiv ℝ (fun y => fderiv ℝ f y (Pi.single l 1)) w (Pi.single l 1) := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ f) w :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply hdF (differentiableAt_const _)]
  simp

/-- Trace of the Hessian of the kernel `newtonD3 · i j k` vanishes off `0`. -/
theorem newtonD3_trace {w : Vec3} (hw : w ≠ 0) (i j k : Fin 3) :
    ∑ l : Fin 3, iteratedFDeriv ℝ 2 (fun z => newtonD3 z i j k) w
      ![Pi.single l 1, Pi.single l 1] = 0 := by
  have hN : ContDiffOn ℝ NewtonD3.ii newtonN NewtonD3.punct := NewtonD3.newtonN_contDiffOn
  have hG : ContDiffOn ℝ NewtonD3.ii (DaxD k newtonN) NewtonD3.punct := DaxD_smooth hN k
  have hh : ContDiffOn ℝ NewtonD3.ii (DaxD j (DaxD k newtonN)) NewtonD3.punct := DaxD_smooth hG j
  have hQ : ∀ l : Fin 3, ContDiffOn ℝ NewtonD3.ii (DaxD l (DaxD l (DaxD j (DaxD k newtonN))))
      NewtonD3.punct := fun l => DaxD_smooth (DaxD_smooth hh l) l
  have hf : ContDiffOn ℝ NewtonD3.ii (fun z => newtonD3 z i j k) NewtonD3.punct :=
    DaxD_smooth hh i
  have hfc : ContDiffAt ℝ 2 (fun z => newtonD3 z i j k) w := by
    have := hf.contDiffAt (NewtonD3.isOpen_punct.mem_nhds hw)
    exact this.of_le (by simp [NewtonD3.ii])
  -- the divergence statement for `h = ∂_j∂_k N`
  have hS : ∀ y : Vec3, y ≠ 0 →
      ∑ l, DaxD l (DaxD l (DaxD j (DaxD k newtonN))) y = 0 := by
    intro y hy
    exact newtonD3Div y hy j k
  have hRy : ∀ y : Vec3, y ≠ 0 →
      ∑ l, DaxD l (DaxD l (DaxD i (DaxD j (DaxD k newtonN)))) y = 0 := by
    intro y hy
    have hd : ∀ l ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun z => DaxD l (DaxD l (DaxD j (DaxD k newtonN))) z) y :=
      fun l _ => diffAt_of_smoothD (hQ l) hy
    have h1 : fderiv ℝ (fun z => ∑ l, DaxD l (DaxD l (DaxD j (DaxD k newtonN))) z) y
        (Pi.single i 1) = 0 := fderiv_eq_zero_of (fun z hz => hS z hz) hy _
    rw [fderiv_fun_sum hd] at h1
    simp only [sum_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact chainC hh hy l i
  have hconv : ∀ l : Fin 3, iteratedFDeriv ℝ 2 (fun z => newtonD3 z i j k) w
      ![Pi.single l 1, Pi.single l 1] =
        DaxD l (DaxD l (DaxD i (DaxD j (DaxD k newtonN)))) w := by
    intro l
    rw [iter2_diag hfc l]
    rfl
  simp only [hconv]
  exact hRy w hw

end UnforcedLeray.Short.PartIIIb.Concrete
