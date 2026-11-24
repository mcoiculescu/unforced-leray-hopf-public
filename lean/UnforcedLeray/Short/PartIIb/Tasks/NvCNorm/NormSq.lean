import UnforcedLeray.Short.PartIIb.Sub.T07

/-!


Source of record: `the November 2 reference manuscript`, lines 1902-1906
(the complex lift `N_v b = N_v(Re b) + i N_v(Im b)`).

Proves `NvCNormSq`: for `u v : Space`, `‖u + i v‖² = ‖u‖² + ‖v‖²` in `ℂ³`, where real vectors
are seen in `ℂ³` by `B0412.realC`.

Proof: expand both sides as coordinate sums (`EuclideanSpace.norm_sq_eq`,
`EuclideanSpace.real_norm_sq_eq`), then check each coordinate with `Complex.sq_norm` and
`Complex.normSq_add_mul_I`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem nvCNormSq : NvCNormSq := by
  unfold NvCNormSq
  intro u v
  have hcoord : ∀ i : Fin 3,
      (UnforcedLeray.B0412.realC u + Complex.I • UnforcedLeray.B0412.realC v) i
        = ((u i : ℝ) : ℂ) + ((v i : ℝ) : ℂ) * Complex.I := by
    intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      UnforcedLeray.B0412.realC_apply]
    ring
  rw [EuclideanSpace.norm_sq_eq
      (UnforcedLeray.B0412.realC u + Complex.I • UnforcedLeray.B0412.realC v),
    EuclideanSpace.real_norm_sq_eq u, EuclideanSpace.real_norm_sq_eq v,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcoord i, Complex.sq_norm, Complex.normSq_add_mul_I]

end UnforcedLeray.Short.IIb
