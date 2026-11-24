import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/3`: `gl_pairTransport` (the pairing is invariant under the transport)

Source of record: `the November 2 reference manuscript` lines 1912-1921, chart 1639-1668.
Mathematics: `cApp S` is the complexification of the real isometry `S`, so it preserves the bilinear
product `dotL` (`dotL_cApp`). Hence `dotL (trF T Φ (t,y)) (trF T f (t,y)) = dotL (Φ (t, T y)) (f (t, T y))`,
and the `y`-integral is invariant under the measure preserving map `T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace PairTr

theorem realC_decomp (u : CVec3) :
    u = B0412.realC (reS u) + Complex.I • B0412.realC (imS u) := by
  ext i
  simp [B0412.realC_apply, reS, imS]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

theorem dotL_realC (x y : Space) :
    dotL (B0412.realC x) (B0412.realC y) = ((inner ℝ x y : ℝ) : ℂ) := by
  rw [dotL_apply]
  simp [B0412.realC_apply, PiLp.inner_apply, mul_comm]

theorem dotL_cApp (S : Space ≃ₗᵢ[ℝ] Space) (u v : CVec3) :
    dotL (cApp S u) (cApp S v) = dotL u v := by
  have hu := realC_decomp u
  have hv := realC_decomp v
  conv_rhs => rw [hu, hv]
  unfold cApp
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, dotL_realC, LinearIsometryEquiv.inner_map_map]

end PairTr

theorem gl_pairTransport : UnforcedLeray.Short.IIb.GLPairTransport := by
  intro P T Φ f
  have hpt : ∀ t : ℝ, (∫ y, dotL (trF T Φ (t, y)) (trF T f (t, y))) =
      ∫ y, dotL (Φ (t, y)) (f (t, y)) := by
    intro t
    have h1 : ∀ y : Space, dotL (trF T Φ (t, y)) (trF T f (t, y)) =
        (fun z : Space => dotL (Φ (t, z)) (f (t, z))) (T y) := by
      intro y
      exact PairTr.dotL_cApp T.symm _ _
    simp only [h1]
    exact T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding
      (fun z : Space => dotL (Φ (t, z)) (f (t, z)))
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro t _
  exact (hpt t).symm

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_pairTransport
