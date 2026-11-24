import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelSmooth.Conv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerVelConv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Bdd

/-!
# `KerVelSmooth`: the kernel velocity of a cylinder test is smooth, periodic, bounded, and
commutes with `∂_k`

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3058.
By the convolution form `KerVelConv` (`kerVel d ψ x l = ∫_{C_d} K_d(z)_l ψ(x - z) dz`), the
kernel velocity is the convolution `kvsConv` whose derivative falls on the test (`Conv.lean`);
boundedness is `kerVelBdd`; periodicity is pointwise, since `ψ` is `d`-periodic.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerVelSmooth : UnforcedLeray.Short.IIIa.KerVelSmooth := by
  intro d hd ψ hψ j
  have hd0 : 0 < d := by linarith
  have hconv : ∀ x : ℝ × ℝ, kerVel d ψ x j = kvsConv d j ψ x :=
    fun x => kerVelConv d hd ψ hψ x j
  have hfun : (fun x => kerVel d ψ x j) = kvsConv d j ψ := funext hconv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact contDiff_infty.2 (fun n => kvs_contDiff hd j n ψ hψ)
  · intro k x
    show fderiv ℝ (fun y => kerVel d ψ y j) x (UnforcedLeray.B0579.dir k) =
      kerVel d (UnforcedLeray.B0579.pd k ψ) x j
    rw [hfun, kvs_fderiv_apply hd hψ j x (UnforcedLeray.B0579.dir k),
      kerVelConv d hd (UnforcedLeray.B0579.pd k ψ) (hψ.pd k) x j]
    rfl
  · obtain ⟨B, hB⟩ := kerVelBdd d hd ψ hψ
    exact ⟨B, fun x => hB x j⟩
  · intro x
    rw [hconv, hconv]
    unfold kvsConv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have e : ((x.1 + d, x.2) - z : ℝ × ℝ) = ((x - z).1 + d, (x - z).2) := by
      ext <;> simp <;> ring
    simp only [e]
    rw [hψ.periodic]

end UnforcedLeray.Short.IIIa
