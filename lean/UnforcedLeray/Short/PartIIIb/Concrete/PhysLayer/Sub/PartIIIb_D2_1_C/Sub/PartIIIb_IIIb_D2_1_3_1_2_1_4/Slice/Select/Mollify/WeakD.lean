import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.WeakD.Core
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.WeakD.SliceLoc

/-!
# `convYWeakD`: slice weak derivative of the `y`-convolution

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
For a.e. phase `τ` the slice `y ↦ Φ(τ, y)` is locally integrable (`convYW_ae_locInt`), and for such
slices `(K *_y Φ)(τ)` is differentiable with derivative `(∂ⱼK) *_y Φ` (`convYW_fderiv`), so
integration by parts against each compactly supported smooth test `θ` gives the weak derivative
identity componentwise (`convYW_core`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem convYWeakD : ConvYWeakD := by
  unfold ConvYWeakD SliceWeakD
  intro P hP K hK hKc Φ hΦ j
  filter_upwards [convYW_ae_locInt hP hΦ] with τ hτ
  intro θ hθ hθc
  exact convYW_core K hK hKc (fun z => Φ (τ, z)) hτ (EuclideanSpace.single j (1 : ℝ)) θ hθ hθc

end UnforcedLeray.Short.PartIIIb.Concrete
