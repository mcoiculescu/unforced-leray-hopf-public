import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The symmetrised tensor is no larger than the tensor (source 2675)

`tensorNorm (nsSym T)² = T₀₀² + T₁₁² + T₂₂² + 2·symRZ²` with `symRZ = (T₀₂ + T₂₀)/2`, and
`2·((a+b)/2)² ≤ a² + b²`, so the norm of `nsSym T` is at most the Euclidean norm of `T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem nsSymNormLe_holds : NsSymNormLe := by
  intro T
  unfold UnforcedLeray.Short.IIIa.tensorNorm UnforcedLeray.Short.PartIIIb.NearInst.nsSym
    UnforcedLeray.Short.PartIIIb.NearInst.symRZ
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fintype.sum_prod_type, Fin.sum_univ_three]
  nlinarith [sq_nonneg (T (0, 1)), sq_nonneg (T (1, 0)), sq_nonneg (T (1, 2)),
    sq_nonneg (T (2, 1)), sq_nonneg (T (0, 2) - T (2, 0))]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
