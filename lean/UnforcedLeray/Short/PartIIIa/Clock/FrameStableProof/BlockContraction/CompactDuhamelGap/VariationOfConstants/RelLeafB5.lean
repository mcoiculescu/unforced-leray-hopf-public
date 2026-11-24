import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB6
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelRegularityReg

/-!
# `PartIII-a:T21/c3/2/1/2/2/3`: leaf `RelB5` of `RelRegularityOrg` (partial)

Source of record: `the November 2 reference manuscript` (SP), lines 2974-2982.

`RelB5` asks for a bound of `‖A_rel r‖` on `[0, B]` for every parameter set of `RelCtx`
(`1 ≤ b`, `0 < ν` arbitrary).  The drafted interaction package (`RelIntA.goodAt_package`,
`OrgSplit.relInteractionA`) gives the bound only in the source regime `b ≥ b_prop`,
`ν ≤ ν_prop(b)`.  This file proves:
* `relB5_pin_unique`: `IsDampedComplBlockInt` determines `A_rel τ` on `[0, B]` (density of the
  smooth class, `relB6b_leaf`);
* `relB5_regime`: the `RelB5` bound in the source regime, with `K_A` uniform in `ν`, the train
  and the block (from `relInteractionA` and uniqueness);
* `relB5_of_goodAtBlock`: `RelB5` from the uniform good-age package `GoodAt` on the age range
  `[t₁, t₂]` of the block (`RelGoodAtBlock`), via `RelIntA.exists_op` and uniqueness.
The missing input for `RelB5` as stated is `RelGoodAtBlock κ` outside the source regime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa
namespace RelRegularityOrg

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub.OrgSplit
  BlockPropagatorInteriorSub.OrgSplit.RelIntA

/-- The pin `IsDampedComplBlockInt` determines `A_rel τ` for `τ ∈ [0, B]`. -/
theorem relB5_pin_unique {κ : PlanarFrameKernels} {P : PlanarData} {ν m : ℝ} (hm : 8 < m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {A₁ A₂ : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (h₁ : IsDampedComplBlockInt κ P ν m tr t₁ B A₁)
    (h₂ : IsDampedComplBlockInt κ P ν m tr t₁ B A₂)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) B) : A₁ τ = A₂ τ := by
  have hE : EqOn (A₁ τ) (A₂ τ) (relSmoothClass m) := by
    rintro W ⟨Φ, hΦs, hΦc, hWΦ⟩
    have e1 := h₁ τ hτ Φ hΦs hΦc W hWΦ
    have e2 := h₂ τ hτ Φ hΦs hΦc W hWΦ
    exact Lp.ext ((Planar.wMeasure_ac m).ae_le (e1.trans e2.symm))
  exact DFunLike.coe_injective
    (Continuous.ext_on (relB6b_leaf m hm) (A₁ τ).continuous (A₂ τ).continuous hE)

/-- `RelB5` in the source regime (`b ≥ b_prop`, `ν ≤ ν_prop`), with `K_A` uniform in `ν`, the
train and the block (SP 2974-2982). -/
theorem relB5_regime (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) (P : PlanarData)
    (hP : IsPlanarReference P) (m : ℝ) (hm : 8 < m) (K B : ℝ) (hB : 0 < B) :
    ∃ K_A b_prop : ℝ, 0 ≤ K_A ∧ ∀ b : ℝ, b_prop ≤ b → ∃ ν_prop : ℝ, 0 < ν_prop ∧
      ∀ ν ∈ Ioc 0 ν_prop, ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
        RelCtx κ P m K B b ν tr t₁ t₂ →
        ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A := by
  obtain ⟨K_A, b_prop, hKA, h⟩ := relInteractionA κ hκ P hP m hm K B hB
  refine ⟨K_A, b_prop, hKA, fun b hb => ?_⟩
  obtain ⟨ν_prop, hν_prop, hν⟩ := h b hb
  refine ⟨ν_prop, hν_prop, fun ν hνI tr t₁ t₂ ctx A_rel hA r hr => ?_⟩
  obtain ⟨_, _, _, _, _, _, hF, htr, ht₁, h12, hbt, hBdef⟩ := ctx
  obtain ⟨A, hApin, hAb, -⟩ := hν ν hνI hF tr htr t₁ t₂ ht₁ h12 hbt hBdef
  rw [relB5_pin_unique hm hA hApin hr]
  exact hAb r

/-- The good-age package `GoodAt` (the `X_{m,d(r)}` bound of `movDampedComplInt` with constant
`K_A`, `d(r) ≥ 1`, a.e. additivity) uniformly on the age range of the block, for every parameter
set of `RelCtx` (SP 2974-2982). -/
def RelGoodAtBlock (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelCtx κ P m K B b ν tr t₁ t₂ →
    ∃ K_A : ℝ, 0 ≤ K_A ∧ ∀ r ∈ Icc t₁ t₂, GoodAt κ P m K_A tr r

/-- `RelB5` from the uniform good-age package on the block. -/
theorem relB5_of_goodAtBlock (κ : PlanarFrameKernels) (h : RelGoodAtBlock κ) : RelB5 κ := by
  intro P m K B b ν tr t₁ t₂ ctx A_rel hA
  obtain ⟨K_A, hKA, hgood⟩ := h P m K B b ν tr t₁ t₂ ctx
  obtain ⟨_hκ, _hP, hm, _hB, _hb, hν, _hF, _htr, ht₁, h12, _hbt, hBdef⟩ := ctx
  refine ⟨K_A, fun τ hτ => ?_⟩
  have hr := VariationOfConstantsSub.ageAt_mem_Icc hν ht₁ h12 hBdef hτ
  obtain ⟨T, hTrep, hTn⟩ := exists_op κ P tr (ageAt ν t₁ τ) hKA (hgood _ hr)
  have hE : EqOn (A_rel τ) T (relSmoothClass m) := by
    rintro W ⟨Φ, hΦs, hΦc, hWΦ⟩
    have e1 := hA τ hτ Φ hΦs hΦc W hWΦ
    have e2 : (T W : ℂ → ℂ) =ᵐ[volume] opFun κ P tr (ageAt ν t₁ τ) W :=
      (volume_ac_wMeasure m).ae_le (hTrep W)
    have hc : cylRep W =ᵐ[volume.restrict
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))))] Φ := by
      have h2 : (fun y => (W : ℂ → ℂ) (planeToC y)) =ᵐ[volume]
          fun y => Φ (cToPlane (planeToC y)) :=
        measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp hWΦ
      refine ae_restrict_of_ae (h2.mono fun y hy => ?_)
      simp only [cylRep, hy, cToPlane_planeToC]
    have e3 : opFun κ P tr (ageAt ν t₁ τ) W = fun z =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
          (movDampedComplInt κ P tr (ageAt ν t₁ τ) Φ) (cToPlane z) := by
      funext z
      unfold opFun
      rw [movDampedComplInt_congr κ P tr (ageAt ν t₁ τ) hc]
    rw [e3] at e2
    exact Lp.ext ((Planar.wMeasure_ac m).ae_le (e1.trans e2.symm))
  have hEq : A_rel τ = T := DFunLike.coe_injective
    (Continuous.ext_on (relB6b_leaf m hm) (A_rel τ).continuous T.continuous hE)
  rw [hEq]
  exact hTn

/-- Leaf `RelB5` in the source regime (SP 2974-2982), from `relB5_regime`. -/
theorem relB5_leaf (κ : PlanarFrameKernels) : RelB5Reg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨K_A, b_prop, _hKA, h⟩ := relB5_regime κ hκ P hP m hm K B hB
  refine ⟨b_prop, fun b hb _ => ?_⟩
  obtain ⟨ν_prop, hν_prop, hν⟩ := h b hb
  exact ⟨ν_prop, hν_prop, fun ν hνI tr t₁ t₂ ctx A_rel hA =>
    ⟨K_A, hν ν hνI tr t₁ t₂ ctx A_rel hA⟩⟩

end RelRegularityOrg
end UnforcedLeray.Short.IIIa
