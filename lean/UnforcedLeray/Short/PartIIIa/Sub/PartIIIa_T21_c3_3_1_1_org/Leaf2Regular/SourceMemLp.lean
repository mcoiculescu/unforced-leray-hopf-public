import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.DuhamelSplit

/-!
# Helper for `ComplSourceRegular` (`PartIII-a:T21/c3/3/1/1/2/2/4`): what is missing, and part (a)

Source `the November 2 reference manuscript` (SP) lines 2919-2925, 2937-2958.



* Parts (b), (c) fail for admissible propagators: `IsFreeMovingPropagator` fixes `U` only a.e. on
  cylinder data and bounds it through the lower integral `eLpNorm`, so `U' g = U g + L g • 1_N`
  (`L` a `ℂ`-linear functional on all functions vanishing on the span of the continuous cylinder
  images `movCx a f₁ f₂`; `N` of inner measure zero and positive outer measure) satisfies all four
  clauses whenever `U` does, and `U' s t₁ (compl F w t₁)` is not a.e. measurable when
  `L (compl F w t₁) ≠ 0` (discontinuous datum `f`).  `PropagatorMeas` below is the missing clause.
* Part (a) needs finiteness of the mode-forcing norms (`ForceFinite`): `ComplForcingMeasurable`
  gives only measurability, and `complModeForceOscillator`/`complModeForceEulerError` bound them
  only for `ν ≤ ν₁(b)`, `b ≥ b₁`, not for the arbitrary `ν`, `b ≥ 1` of the statement.
  Given `ForceFinite`, part (a) is `complSource_memLp_of` below.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

namespace Leaf2RegularNeeded

/-- The clause missing from `IsFreeMovingPropagator`: `U` maps `X_{m,d(s₁)}` to a.e. strongly
measurable functions (the propagator of `freeMovingPropagatorExists` is a coerced `Lp` map, so it
has this property: `Lp.aestronglyMeasurable`). -/
def PropagatorMeas (ν m : ℝ) (t₁ t₂ : ℝ) (U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)) : Prop :=
  ∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ → ∀ g : ℝ × ℝ → ℂ,
    MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) →
    AEStronglyMeasurable (U s₂ s₁ g) (B0579.cellMeasure (dd ν s₂) m)

/-- Finiteness of the mode-forcing norms on `[t₁, t₂]` (from `complModeForceOscillator` and
`complModeForceEulerError` for `ν ≤ min ν₁ ν₂`, `b ≥ max b₁ b₂`). -/
def ForceFinite (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) : Prop :=
  ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
    xNorm (dd ν r) m (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) ≠ ⊤

/-- **Part (a) of `ComplSourceRegular` from `ForceFinite`**: the complement source lies in
`X_{m,d(r)}` for `r ∈ [t₁, t₂]` (`memLp_compl`, `LocInteractionConcl`, `H0Hyp`, the forcing
measurability of `ComplForcingMeasurable`). -/
theorem complSource_memLp_of (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ}
    (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {t₁ t₂ C_loc C_H0 : ℝ}
    (hm : 0 ≤ m) (ht₁ : 0 ≤ t₁) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hFlow : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hInt : LocInteractionConcl ν m tr t₁ t₂ C_loc)
    (hH0 : H0Hyp κ (periodizedFrame κ ν m b K hν hF) tr w t₁ t₂ C_H0)
    (hforce : ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      AEStronglyMeasurable (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)
        (B0579.cellMeasure (dd ν r) m))
    (hFin : ForceFinite κ P ν m b K hν hF tr t₁ t₂) :
    ∀ r ∈ Icc t₁ t₂, MemLp (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) 2
      (B0579.cellMeasure (dd ν r) m) := by
  intro r hr
  set F := periodizedFrame κ ν m b K hν hF with hFdef
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hbr : b ≤ clockTheta ν r := hbt₂.trans (theta_anti hν hr0 hr.2)
  have hW : MemLp (compl F w r) 2 (B0579.cellMeasure (dd ν r) m) :=
    memLp_compl F hm hν ht₁ hr.1 hbr hFlow
  obtain ⟨hLm, hLb⟩ := hInt r hr _ hW
  have hL : MemLp (interactionTerm tr r (compl F w r)) 2 (B0579.cellMeasure (dd ν r) m) :=
    ⟨hLm, lt_of_le_of_lt hLb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩
  have hH : MemLp (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) 2
      (B0579.cellMeasure (dd ν r) m) :=
    ⟨aesm_complFiniteRankCoupling F hr0 hbr _,
      lt_of_le_of_lt (hH0 r hr) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩
  have hS : ∀ j : Fin 2, MemLp (fun y => ampl F w r j * complModeForce κ P F tr r j y) 2
      (B0579.cellMeasure (dd ν r) m) := fun j =>
    MemLp.const_mul ⟨hforce r hr j, lt_top_iff_ne_top.2 (hFin r hr j)⟩ _
  have hSum : MemLp (fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y) 2
      (B0579.cellMeasure (dd ν r) m) := by
    have := memLp_finsetSum' (μ := B0579.cellMeasure (dd ν r) m) (p := 2)
      (f := fun j : Fin 2 => fun y => ampl F w r j * complModeForce κ P F tr r j y)
      Finset.univ (fun j _ => hS j)
    convert this using 1
    ext y; simp [Finset.sum_apply]
  exact (hL.add hH).add hSum

/-- **Part (b) of `ComplSourceRegular` from `PropagatorMeas`**. -/
theorem complInit_aesm_of (κ : PlanarFrameKernels) {ν m b K : ℝ} (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {t₁ t₂ : ℝ}
    (hm : 0 ≤ m) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hFlow : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)} (hMeas : PropagatorMeas ν m t₁ t₂ U) :
    ∀ s ∈ Icc t₁ t₂,
      AEStronglyMeasurable (U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁))
        (B0579.cellMeasure (dd ν s) m) := fun s hs =>
  hMeas t₁ s le_rfl hs.1 hs.2 _
    (memLp_compl _ hm hν ht₁ le_rfl (hbt₂.trans (theta_anti hν ht₁ h12)) hFlow)

end Leaf2RegularNeeded

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
