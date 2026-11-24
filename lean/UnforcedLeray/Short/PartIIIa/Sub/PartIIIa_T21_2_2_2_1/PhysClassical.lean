import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ChiBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjDtDeriv

/-!
# `PartIII-a:T21/2/2/2/1/1`: the physical classical adjoint equation (reduction)

Source: `the November 2 reference manuscript` lines 3052-3060.

The physical residual `physKappa tr φ r` coincides with the reduced-coordinate residual
`ladChi tr φ r` (`ladChi = ∂_rφ + νΔφ + v·∇φ`, `LinAdjDualitySub.lean`). Hence `PhysAdjClassical`
follows from the two analytic leaves `LadAdjPointwise` (the classical adjoint identity for
jointly smooth weak solutions) and `LadChiBound` (the `X_{-m,c}` bound of `χ`, needs `1 ≤ c`,
i.e. `ν ≤ 1`). This file proves that reduction; the leaves are not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.E0

/-- Reduction: `PhysAdjClassical m` from the two leaves `LadAdjPointwise m` and `LadChiBound m`. -/
theorem physAdjClassical_of (m : ℝ) (hP : UnforcedLeray.Short.IIIa.LadAdjPointwise m)
    (hC : UnforcedLeray.Short.IIIa.LadChiBound m) : PhysAdjClassical m := by
  intro ν hν tr t s ht hts g φ hφ hν1 hB r hr
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  obtain ⟨M, hM⟩ := hC ν (ν ^ (-2 : ℝ)) tr t s g φ hν hc1 ht hts hB hφ
  have hk : ∀ x : ℝ × ℝ, physKappa tr φ r x =
      UnforcedLeray.Short.IIIa.ladChi tr φ r x := by
    intro x
    have hd : deriv (fun r' => φ r' x) r = UnforcedLeray.Short.IIIa.ladDt φ r x :=
      (UnforcedLeray.Short.IIIa.ladDt_hasDerivAt hφ.jointSmooth hr x).deriv
    simp only [physKappa, UnforcedLeray.Short.IIIa.ladChi, UnforcedLeray.Short.IIIa.ladTransport,
      UnforcedLeray.Short.IIIa.ladLapCx, lapCx, hd]
    ring
  have hfun : physKappa tr φ r = UnforcedLeray.Short.IIIa.ladChi tr φ r := funext hk
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hM r hr).1
  · intro ψ uψ hψ hu
    rw [hfun]
    exact hP ν (ν ^ (-2 : ℝ)) tr t s g φ hν hc ht hts hB hφ r hr ψ uψ hψ hu

/-- `PhysAdjClassical m` for `8 < m` (the leaves `ladAdjPointwise`, `ladChiBound` are proved;
`LadChiBound` needs `8 < m`). The statement `PhysAdjClassical m` for all `m` carries no such
hypothesis and must be strengthened by `8 < m`. -/
theorem physAdjClassical (m : ℝ) (hm : 8 < m) : PhysAdjClassical m :=
  physAdjClassical_of m (UnforcedLeray.Short.IIIa.ladAdjPointwise m)
    (UnforcedLeray.Short.IIIa.ladChiBound m hm)

end UnforcedLeray.Short.IIIa.E0
