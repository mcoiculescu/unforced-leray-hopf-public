import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b0
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L2.CouplingCompact
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Leaf B2: compactness of the planar damped interaction (SP 2972-2974)

`A0 = couplingW + R`, `couplingW` compact (sector truncations, `CouplingCompact`), and `R = A0 - couplingW`
maps the dense class of smooth compactly supported elements into the finite-dimensional closed
subspace of elements a.e. equal to `a e₀ + b e₁`, hence has finite-dimensional range.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace PlanarB

/-- A bounded operator on `L²_m` that sends a dense set into a closed finite-dimensional subspace
is compact. -/
theorem isCompactOperator_of_dense_maps_into {m : ℝ} (R : Planar.L2w m →L[ℂ] Planar.L2w m)
    (S : Submodule ℂ (Planar.L2w m)) [FiniteDimensional ℂ S]
    (D : Set (Planar.L2w m)) (hD : Dense D) (hRD : ∀ W ∈ D, R W ∈ S) :
    IsCompactOperator R := by
  have hS : IsClosed (S : Set (Planar.L2w m)) := Submodule.closed_of_finiteDimensional S
  have hall : ∀ W, R W ∈ S := by
    have hcl : IsClosed (R ⁻¹' (S : Set (Planar.L2w m))) := hS.preimage R.continuous
    intro W
    have : W ∈ closure D := hD W
    exact (closure_minimal hRD hcl) this
  haveI : ProperSpace S := FiniteDimensional.proper_rclike ℂ S
  refine ⟨S.subtype '' (closedBall (0 : S) ‖R‖), (isCompact_closedBall _ _).image
    S.subtypeL.continuous, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Planar.L2w m) one_pos) fun x hx => ?_
  have hx' : ‖x‖ < 1 := by simpa using hx
  refine ⟨⟨R x, hall x⟩, ?_, rfl⟩
  rw [mem_closedBall_zero_iff]
  show ‖R x‖ ≤ ‖R‖
  calc ‖R x‖ ≤ ‖R‖ * ‖x‖ := R.le_opNorm x
    _ ≤ ‖R‖ * 1 := by gcongr
    _ = ‖R‖ := mul_one _

/-- **Leaf B2 (compactness, SP 2972-2974).** -/
theorem planarDampedIntCompact_proof (κ : PlanarFrameKernels) :
    PlanarDampedIntCompact κ := by
  intro _ P _ m hm _ A0 hA0
  obtain ⟨lam, hp, hh, ℓ, _, _, hΦ⟩ := hA0
  set μ := Planar.wMeasure m with hμ
  let e : Fin 2 → ℂ → ℂ := fun i z => κ.e i (cToPlane z)
  have hcont : Continuous cToPlane := by unfold cToPlane; fun_prop
  have hecont : ∀ i, Continuous (e i) := fun i => (κ.e_cont i).comp hcont
  let E : Fin 2 → (ℂ →ₘ[μ] ℂ) := fun i => AEEqFun.mk (e i) (hecont i).aestronglyMeasurable
  let V : Submodule ℂ (ℂ →ₘ[μ] ℂ) := Submodule.span ℂ {E 0, E 1}
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  let ι : Planar.L2w m →ₗ[ℂ] (ℂ →ₘ[μ] ℂ) := (Lp.LpSubmodule ℂ ℂ 2 μ).subtype
  let S : Submodule ℂ (Planar.L2w m) := V.comap ι
  haveI : FiniteDimensional ℂ S := by
    let g : S →ₗ[ℂ] V := LinearMap.codRestrict V (ι ∘ₗ S.subtype) (fun x => x.2)
    have hg : Function.Injective g := by
      intro x y hxy
      have h2 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h2)
    have hN : IsNoetherian ℂ V := isNoetherian_of_isNoetherianRing_of_finite ℂ V
    exact Module.Finite.of_injective g hg
  set R : Planar.L2w m →L[ℂ] Planar.L2w m := A0 - Planar.couplingW hm with hR
  haveI hloc0 : IsLocallyFiniteMeasure μ :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  have hdense := Lp.dense_hasCompactSupport_contDiff (μ := μ) (F := ℂ) (p := 2) (by simp)
  have hkey : ∀ W ∈ {f : Planar.L2w m | ∃ g : ℂ → ℂ, f =ᵐ[μ] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g}, R W ∈ S := by
    rintro W ⟨Φ, hWΦ, hcs, hsm⟩
    have h1 := hΦ Φ hsm hcs W ((Planar.volume_ac m).ae_eq hWΦ)
    have h1' := (Planar.wMeasure_ac m).ae_eq h1
    set a : Fin 2 → ℂ := fun i =>
      (((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam i) * planarLamPair κ i Φ with ha
    have hRW : R W = A0 W - Planar.couplingW hm W := rfl
    have h2 : ⇑(R W) =ᵐ[μ] fun z => a 0 * e 0 z + a 1 * e 1 z := by
      rw [hRW]
      filter_upwards [Lp.coeFn_sub (A0 W) (Planar.couplingW hm W), h1'] with z hz1 hz2
      rw [hz1, Pi.sub_apply, hz2, Fin.sum_univ_two]
      simp only [ha, e]
      ring
    have h3 : ι (R W) = a 0 • E 0 + a 1 • E 1 := by
      apply AEEqFun.ext
      filter_upwards [AEEqFun.coeFn_add (a 0 • E 0) (a 1 • E 1),
        AEEqFun.coeFn_smul (a 0) (E 0), AEEqFun.coeFn_smul (a 1) (E 1),
        AEEqFun.coeFn_mk (e 0) (hecont 0).aestronglyMeasurable,
        AEEqFun.coeFn_mk (e 1) (hecont 1).aestronglyMeasurable, h2] with z h3 h4 h5 h6 h7 h8
      calc ((ι (R W) : ℂ →ₘ[μ] ℂ) : ℂ → ℂ) z = (⇑(R W)) z := rfl
        _ = a 0 * e 0 z + a 1 * e 1 z := h8
        _ = _ := by
          rw [h3, Pi.add_apply, h4, h5, Pi.smul_apply, Pi.smul_apply]
          simp only [E, h6, h7, smul_eq_mul]
    show ι (R W) ∈ V
    rw [h3]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hRc : IsCompactOperator R :=
    isCompactOperator_of_dense_maps_into R S _ hdense hkey
  have hA : A0 = R + Planar.couplingW hm := by simp [hR]
  rw [hA, ContinuousLinearMap.coe_add']
  exact hRc.add (CouplingCompactL2.isCompactOperator_couplingW hm)

end PlanarB

end OrgSplit3

end BlockPropagatorInteriorSub

end UnforcedLeray.Short.IIIa
