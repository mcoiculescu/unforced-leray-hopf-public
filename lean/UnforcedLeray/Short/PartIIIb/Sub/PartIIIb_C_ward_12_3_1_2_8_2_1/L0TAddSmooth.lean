import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommuteProps
import UnforcedLeray.Units.B0411.Operators

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1`: additivity of `L₀ᵗ` on smooth fields

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Proves `L0TAddSmooth` (`ProjCommuteProps.lean`): for smooth
`A, B`, `L₀ᵗ(A + B) = L₀ᵗA + L₀ᵗB`, from additivity of `∂_τ`, `∂_{y_j}`, `y·∇`, `Δ` and `driftT`
on `C¹` fields (`fderiv_add`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartIIIb.Concrete

namespace UnforcedLeray.Short.PartIIIb.Concrete.L0TAddSmoothAux

theorem diffC {G : ℝ × UnforcedLeray.Space → CVec3} (hG : ContDiff ℝ ∞ G) :
    Differentiable ℝ G :=
  hG.differentiable (by simp)

theorem dτ_add_aux {A B : ℝ × UnforcedLeray.Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) : dτ (A + B) = dτ A + dτ B := by
  funext p
  simp [dτ, fderiv_add (hA p) (hB p)]

theorem radialT_add_aux {A B : ℝ × UnforcedLeray.Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : radialT (A + B) = radialT A + radialT B := by
  funext p
  simp only [radialT, Pi.add_apply, dy_add (diffC hA) (diffC hB), smul_add,
    Finset.sum_add_distrib]

theorem lapT_add_aux {A B : ℝ × UnforcedLeray.Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : lapT (A + B) = lapT A + lapT B := by
  have h2 : ∀ j : Fin 3, dy j (dy j (A + B)) = dy j (dy j A) + dy j (dy j B) := fun j => by
    rw [dy_add (diffC hA) (diffC hB) j,
      dy_add (diffC (contDiff_dy hA j)) (diffC (contDiff_dy hB j)) j]
  funext p
  simp only [lapT, Pi.add_apply, h2, Finset.sum_add_distrib]

theorem driftT_add_aux {A B : ℝ × UnforcedLeray.Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : driftT (A + B) = driftT A + driftT B := by
  funext p
  simp only [driftT, Pi.add_apply, dτ_add_aux (diffC hA) (diffC hB),
    radialT_add_aux hA hB, Pi.add_apply]
  module

theorem L0T_add_aux (ν : ℝ) {A B : ℝ × UnforcedLeray.Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : L0T ν (A + B) = L0T ν A + L0T ν B := by
  simp only [L0T, nuLapT]
  rw [driftT_add_aux hA hB, lapT_add_aux hA hB]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

end UnforcedLeray.Short.PartIIIb.Concrete.L0TAddSmoothAux

theorem l0TAddSmooth : UnforcedLeray.Short.PartIIIb.Concrete.L0TAddSmooth := by
  intro ν A B hA hB
  exact UnforcedLeray.Short.PartIIIb.Concrete.L0TAddSmoothAux.L0T_add_aux ν hA hB
