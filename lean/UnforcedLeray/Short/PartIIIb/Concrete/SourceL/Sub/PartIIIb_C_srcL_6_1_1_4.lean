import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3

/-!
# Smoothness of `newtonD3` off the origin (task `PartIII-b:C/srcL/6/1/1/4`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
`newtonD3 x i j k = ∂_i∂_j∂_k N(x)` with `N = 1/(4π|x|)` is `C^∞` on `ℝ³ \ {0}`; this is the
statement `NewtonD3.newtonD3_contDiffOn` (three applications of `ContDiffOn.fderiv_of_isOpen` on
the punctured space `{x ≠ 0}`, composed with a fixed basis vector `Pi.single`), restated on the
carrier of the Concrete layer.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem newtonD3_contDiffOn (i j k : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Vec3 => newtonD3 x i j k) {x : Vec3 | x ≠ 0} :=
  NewtonD3.newtonD3_contDiffOn i j k

end UnforcedLeray.Short.PartIIIb.Concrete
