import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.XNorm
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.PerturbDuhamel.WeakFlowDuhamel.Gronwall

/-!
# Organizer file for `PartIII-a:T21/c3/3/1/1` (free-rate Duhamel for the moving complement)

Source `the November 2 reference manuscript` (SP) lines 2919-2925, 2937-2958,
2982-2988.  The leaf `WeakFlowDuhamelSub.ComplFreeRateDuhamel κ` (in `WeakFlowDuhamel.lean`) is
reduced to four analytic Props about the free moving propagator `U` on `X_{m,d}`:

* `FreeMovingPropagatorExists` (a): extension of the free moving evolution by density (SP 2937-2958);
* `ComplMildFreeBound` (b): mild representation of `compl F w` by `U` with the explicit source
  `complSource` (SP 2919-2925), in norm form (Minkowski inside);
* `LocInteractionConcl` (c): the pointwise-in-`W` bound `‖(K_d W)·∇E_mov‖ ≤ C_loc ‖W‖` from the
  adjoint localized bound by cylinder-test density (SP 2953-2958);
* `ComplForcingMeasurable` (d): measurability of the mode forcings and of their norm profile.

The theorem `complFreeRate_inst` proves, from these, the per-instance conclusion of
`ComplFreeRateDuhamel`; the glue (`intro`s and `exact`) is the task `PartIII-a:T21/c3/3/1/1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

/-- Cell length at age `r`. -/
abbrev dd (ν r : ℝ) : ℝ := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)

/-- The hypothesis `hFree` of `ComplFreeRateDuhamel`: free moving energy bound at rate
`normGrowthConst m + 1` on cylinder data (SP 2937-2958). -/
def FreeEnergyHyp (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : Prop :=
  ∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
    ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
      ∀ ω₀ : ℝ → B0579.Plane → ℝ,
        UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₂)) m
            (JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ≤
          ENNReal.ofReal
              (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s₁)) m
              (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ)))

/-- The hypothesis `hLoc` of `ComplFreeRateDuhamel`: adjoint localized interaction bound (SP 2953-2958). -/
def LocalizedHyp (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ C_loc : ℝ) : Prop :=
  ∀ r ∈ Icc t₁ t₂, ∀ Φ : ℝ × ℝ → ℂ,
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    MemLp Φ 2 (B0579.cellMeasure d (-m)) →
    ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
      h1Norm d m χ gχ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
      xNorm d (-m) χ ≤ ENNReal.ofReal C_loc * xNorm d (-m) Φ ∧
      ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
        ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
          ∫ y in B0579.cell d,
            Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
              uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ)

/-- The interaction term `-(K_{d(r)} W)·∇E_mov(r)` of the moving linearised Euler operator
(SP 2863-2865, 2919-2925). -/
def interactionTerm {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  -(kerVelCx (dd ν r) W y 0 * ((movingTrainGradE tr r y 0 : ℝ) : ℂ) +
    kerVelCx (dd ν r) W y 1 * ((movingTrainGradE tr r y 1 : ℝ) : ℂ))

/-- The source of the complement equation (SP 2919-2925):
`L_int W⊥ - E H₀ W⊥ + ∑_j α_j complModeForce_j`, with `W⊥ = compl F w r`. -/
def complSource (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ)
    (y : ℝ × ℝ) : ℂ :=
  (interactionTerm tr r (compl F w r) y +
      complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y) +
    ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y

/-- The complex moving image `J_a⁻¹ f₁ + i J_a⁻¹ f₂` of a pair of real data (SP 2937-2958). -/
def movCx (a : ℝ) (f₁ f₂ : B0579.Plane → ℝ) (y : ℝ × ℝ) : ℂ :=
  JscaleInv a (fun x => ((f₁ x : ℝ) : ℂ)) y + Complex.I * JscaleInv a (fun x => ((f₂ x : ℝ) : ℂ)) y

/-- `U` maps `X_{m,d(s₁)}` to a.e. strongly measurable functions (SP 2937-2958; the propagator of
`freeMovingPropagatorExists` is a coerced `Lp` map). -/
def PropagatorMeas (ν m : ℝ) (t₁ t₂ : ℝ) (U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)) : Prop :=
  ∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ → ∀ g : ℝ × ℝ → ℂ,
    MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) →
    AEStronglyMeasurable (U s₂ s₁ g) (B0579.cellMeasure (dd ν s₂) m)

/-- `U` is the free moving propagator on `X_{m,d}` (SP 2937-2958): it is bounded at rate
`normGrowthConst m + 1` on all functions (trivially when the norm is infinite), it is `ℂ`-linear on
`X_{m,d(s₁)}` (a.e. in `X_{m,d(s₂)}`) for `t₁ ≤ s₁ ≤ s₂ ≤ t₂`, and it agrees with the free cylinder
flow in moving coordinates on real data and on complex cylinder data
`J⁻¹ f₁ + i J⁻¹ f₂` (the extension of the free evolution by density and linearity). -/
def IsFreeMovingPropagator (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) (U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)) : Prop :=
  (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ → ∀ g : ℝ × ℝ → ℂ,
    xNorm (dd ν s₂) m (U s₂ s₁ g) ≤
      ENNReal.ofReal (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
        xNorm (dd ν s₁) m g) ∧
  (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
    ∀ f₀ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₀ →
      ∀ ω₀ : ℝ → B0579.Plane → ℝ,
        UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₀ ω₀ →
        U s₂ s₁ (JscaleInv (clockA ν s₁) (fun x => ((f₀ x : ℝ) : ℂ))) =ᵐ[
            B0579.cellMeasure (dd ν s₂) m]
          JscaleInv (clockA ν s₂) (fun x => ((ω₀ s₂ x : ℝ) : ℂ))) ∧
  (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
    (∀ g h : ℝ × ℝ → ℂ, MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) →
      MemLp h 2 (B0579.cellMeasure (dd ν s₁) m) →
      U s₂ s₁ (fun y => g y + h y) =ᵐ[B0579.cellMeasure (dd ν s₂) m]
        fun y => U s₂ s₁ g y + U s₂ s₁ h y) ∧
    (∀ (c : ℂ) (g : ℝ × ℝ → ℂ), MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) →
      U s₂ s₁ (fun y => c * g y) =ᵐ[B0579.cellMeasure (dd ν s₂) m]
        fun y => c * U s₂ s₁ g y)) ∧
  (∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₂ →
    ∀ f₁ f₂ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₁ →
      B0579.IsCylTest (ν ^ (-2 : ℝ)) f₂ →
      ∀ ω₁ ω₂ : ℝ → B0579.Plane → ℝ,
        UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₁ ω₁ →
        UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₂ ω₂ →
        U s₂ s₁ (movCx (clockA ν s₁) f₁ f₂) =ᵐ[B0579.cellMeasure (dd ν s₂) m]
          movCx (clockA ν s₂) (ω₁ s₂) (ω₂ s₂)) ∧
  PropagatorMeas ν m t₁ t₂ U

/-- Existence of free cylinder flows for every cylinder test datum at every age in `[t₁, t₂]`
(SP 2937-2958, PartII-b `HasFreeCylFlowFamily`).  Without it `IsFreeMovingPropagator` does not pin
`U` down (e.g. `U = 0` satisfies it when no flows exist), so leaf (b) needs it. -/
def FreeFlowAvail (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) :
    Prop :=
  ∀ s ∈ Icc t₁ t₂, ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
    ∃ ω : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω

/-- **Leaf (e)** (SP 2937-2958, 2085-2090): for a BUC train that is `δ = 1`-close to the
periodized Gaussian vortex on the ages `s ≤ Σ/ν` with `Σ = (ν b)⁻¹` (`TrainClose tr (ν b)⁻¹ 1`,
which is `FmrTrainClose` for `ν ≤ ν₀(b)`), free cylinder flows exist for all cylinder data at all
ages in `[t₁, t₂]` when `b ≤ θ(t₂)` (then `t₂ ≤ Σ/ν`).  Proved from `freeCylinderBound_proof`
(`PartII-b:T24`) with the `Params` built from `tr` (`c = ν⁻²`) in `Leaf5Proof.lean`.  The extra
hypotheses `1 ≤ b`, `b ≤ θ(t₂)`, `TrainClose` are what `IsBUCTrain` alone does not give. -/
def FreeFlowAvailExists (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ b : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  0 < b → b ≤ clockTheta ν t₂ → UnforcedLeray.Short.IIb.TrainClose tr (ν * b)⁻¹ 1 →
  FreeFlowAvail ν m tr t₁ t₂

/-- **Leaf (a)** (SP 2937-2958, `eq:short-causal-free-moving`): the free moving evolution on
cylinder data extends by density and linearity to a propagator `U` on `X_{m,d}` with the free
energy bound; uses existence of free cylinder flows for dense data (PartII-b `HasFreeCylFlowFamily`
/ `freeCylPropagatorCLM`) and the scaling `JscaleInv`. -/
def FreeMovingPropagatorExists (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  FreeEnergyHyp ν m tr t₁ t₂ → ∃ U, IsFreeMovingPropagator ν m tr t₁ t₂ U

/-- Conclusion of the cylinder-test density step (SP 2953-2958): for all `W` in `X_{m,d(r)}` the
interaction term is a.e. strongly measurable with `‖L_int W‖ ≤ C_loc ‖W‖`. -/
def LocInteractionConcl (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ C_loc : ℝ) : Prop :=
  ∀ r ∈ Icc t₁ t₂, ∀ W : ℝ × ℝ → ℂ, MemLp W 2 (B0579.cellMeasure (dd ν r) m) →
    AEStronglyMeasurable (interactionTerm tr r W) (B0579.cellMeasure (dd ν r) m) ∧
    xNorm (dd ν r) m (interactionTerm tr r W) ≤ ENNReal.ofReal C_loc * xNorm (dd ν r) m W

/-- **Leaf (c)** (SP 2953-2958): `LocalizedHyp` implies `LocInteractionConcl` (duality
`XNormDuality` + cylinder-test density; `IsKernelBiotSavart` vs `kerVelCx`). -/
def LocInteractionBound (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ C_loc : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → 0 ≤ C_loc →
  LocalizedHyp ν m tr t₁ t₂ C_loc → LocInteractionConcl ν m tr t₁ t₂ C_loc

/-- The finite-rank coupling hypothesis `hH0` of `ComplFreeRateDuhamel`. -/
def H0Hyp (κ : PlanarFrameKernels) {ν m b K : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (w : ℝ → ℝ × ℝ → ℂ)
    (t₁ t₂ C_H0 : ℝ) : Prop :=
  ∀ r ∈ Icc t₁ t₂,
    xNorm (dd ν r) m
        (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) ≤
      ENNReal.ofReal C_H0 * xNorm (dd ν r) m (compl F w r)

/-- **Leaf (b)** (SP 2919-2925, 2937-2958): mild representation of the complement `compl F w` by
the free moving propagator `U` with the source `complSource`, in the norm form
`‖W⊥(s)‖ ≤ ‖U(s,t₁)W⊥(t₁)‖ + ∫_{(t₁,s]} a(r)⁻² ‖U(s,r) src(r)‖ dr`
(uniqueness of weak forced free flows by duality with the backward free adjoint flow; Minkowski for
the `X_{m,d}`-norm of the parametric integral from `Conv.mixedNorm_integral_le`). -/
def ComplMildFreeBound (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) : Prop :=
  IsSeedKernels κ → IsPlanarReference P → 8 < m → 1 ≤ b →
  UnforcedLeray.Short.PartI.IsBUCTrain tr → 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ)
    (U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)),
    IsFreeMovingPropagator ν m tr t₁ t₂ U → FreeFlowAvail ν m tr t₁ t₂ →
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
    HasZeroCirculation (ν ^ (-2 : ℝ)) f →
    LocInteractionConcl ν m tr t₁ t₂ C_loc →
    H0Hyp κ (periodizedFrame κ ν m b K hν hF) tr w t₁ t₂ C_H0 →
    ∀ s ∈ Icc t₁ t₂,
      xNorm (dd ν s) m (compl (periodizedFrame κ ν m b K hν hF) w s) ≤
        xNorm (dd ν s) m (U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁)) +
          ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
            xNorm (dd ν s) m
              (U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r))

/-- **Leaf (d)** (SP 2916-2925, 2991-2997): the mode forcings are a.e. strongly measurable on
`X_{m,d(r)}` for `r ∈ [t₁, t₂]`, and `r ↦ ∑_j |α_j(r)| ‖complModeForce_j(r)‖` is a.e. measurable
on `(t₁, t₂]` (strong continuity of the weak flow; measurability of `r ↦ perE κ d(r)`). -/
def ComplForcingMeasurable (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) : Prop :=
  IsSeedKernels κ → IsPlanarReference P → 8 < m → 1 ≤ b →
  UnforcedLeray.Short.PartI.IsBUCTrain tr → 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
    (∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      AEStronglyMeasurable (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)
        (B0579.cellMeasure (dd ν r) m)) ∧
    AEMeasurable (fun r => ∑ j : Fin 2,
        ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ *
          xNorm (dd ν r) m (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j))
      (volume.restrict (Ioc t₁ t₂))

/-- Norm of the source: `‖src(r)‖ ≤ (C_loc + C_H0) ‖W⊥(r)‖ + ∑_j |α_j| ‖force_j‖`. -/
theorem xNorm_complSource_le (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K r C_loc C_H0 : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (w : ℝ → ℝ × ℝ → ℂ)
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) (hC_loc : 0 ≤ C_loc) (hC_H0 : 0 ≤ C_H0)
    (hL_meas : AEStronglyMeasurable (interactionTerm tr r (compl F w r))
      (B0579.cellMeasure (dd ν r) m))
    (hL_bdd : xNorm (dd ν r) m (interactionTerm tr r (compl F w r)) ≤
      ENNReal.ofReal C_loc * xNorm (dd ν r) m (compl F w r))
    (hH0_bdd : xNorm (dd ν r) m
        (complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r))) ≤
      ENNReal.ofReal C_H0 * xNorm (dd ν r) m (compl F w r))
    (hforce : ∀ j : Fin 2, AEStronglyMeasurable (complModeForce κ P F tr r j)
      (B0579.cellMeasure (dd ν r) m)) :
    xNorm (dd ν r) m (complSource κ P F tr w r) ≤
      ENNReal.ofReal (C_loc + C_H0) * xNorm (dd ν r) m (compl F w r) +
        ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ *
          xNorm (dd ν r) m (complModeForce κ P F tr r j) := by
  set d := dd ν r with hd
  have h1 : xNorm d m (fun y => interactionTerm tr r (compl F w r) y +
        complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y) ≤
      ENNReal.ofReal (C_loc + C_H0) * xNorm d m (compl F w r) := by
    have hH0_meas := aesm_complFiniteRankCoupling F hr hbr (movH0 κ tr r · (compl F w r))
    have htri := eLpNorm_add_le hL_meas hH0_meas (p := 2) (by norm_num)
    calc _ ≤ _ := htri
      _ ≤ ENNReal.ofReal C_loc * xNorm d m (compl F w r) +
          ENNReal.ofReal C_H0 * xNorm d m (compl F w r) := add_le_add hL_bdd hH0_bdd
      _ = _ := by rw [← add_mul, ENNReal.ofReal_add hC_loc hC_H0]
  have hA : AEStronglyMeasurable
      (fun y => interactionTerm tr r (compl F w r) y +
        complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y)
      (B0579.cellMeasure d m) :=
    hL_meas.add (aesm_complFiniteRankCoupling F hr hbr _)
  have hS : ∀ j ∈ (Finset.univ : Finset (Fin 2)), AEStronglyMeasurable
      (fun y => ampl F w r j * complModeForce κ P F tr r j y) (B0579.cellMeasure d m) :=
    fun j _ => (hforce j).const_mul _
  have hsum : xNorm d m (fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y) ≤
      ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ * xNorm d m (complModeForce κ P F tr r j) := by
    have := eLpNorm_sum_le (μ := B0579.cellMeasure d m) (p := 2)
      (f := fun j : Fin 2 => fun y => ampl F w r j * complModeForce κ P F tr r j y)
      (s := Finset.univ) hS (by norm_num)
    have heq : (∑ j : Fin 2, fun y => ampl F w r j * complModeForce κ P F tr r j y) =
        fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y := by
      ext y; simp [Finset.sum_apply]
    rw [heq] at this
    refine this.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold xNorm
    have hsmul : (fun y => ampl F w r j * complModeForce κ P F tr r j y) =
        ampl F w r j • complModeForce κ P F tr r j := rfl
    rw [hsmul, eLpNorm_const_smul, ofReal_norm]
  have hB : AEStronglyMeasurable
      (fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y)
      (B0579.cellMeasure d m) := by
    have := Finset.aestronglyMeasurable_sum (μ := B0579.cellMeasure d m) Finset.univ hS
    convert this using 1
    ext y; simp [Finset.sum_apply]
  have htri : xNorm d m (complSource κ P F tr w r) ≤
      xNorm d m (fun y => interactionTerm tr r (compl F w r) y +
        complFiniteRankCoupling F r (movH0 κ tr r · (compl F w r)) y) +
      xNorm d m (fun y => ∑ j : Fin 2, ampl F w r j * complModeForce κ P F tr r j y) :=
    eLpNorm_add_le hA hB (by norm_num)
  exact htri.trans (add_le_add h1 hsum)

/-- **Per-instance free-rate Duhamel inequality** (the body of `ComplFreeRateDuhamel κ` after its
`intro`s), from leaves (a)-(d). -/
theorem complFreeRate_inst (κ : PlanarFrameKernels) (P : PlanarData) (hSeed : IsSeedKernels κ)
    (hP : IsPlanarReference P) {m K C_loc C_H0 b : ℝ} (hm : 8 < m) (hC_loc : 0 ≤ C_loc)
    (hC_H0 : 0 ≤ C_H0) (hb1 : 1 ≤ b) {ν : ℝ} (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hbt₂ : b ≤ clockTheta ν t₂) {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ}
    {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} (hFlow : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hCirc : HasZeroCirculation (ν ^ (-2 : ℝ)) f)
    (hFree : FreeEnergyHyp ν m tr t₁ t₂) (hLoc : LocalizedHyp ν m tr t₁ t₂ C_loc)
    (hH0 : H0Hyp κ (periodizedFrame κ ν m b K hν hF) tr w t₁ t₂ C_H0)
    (hA : FreeMovingPropagatorExists ν m tr t₁ t₂)
    (hB : ComplMildFreeBound κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0)
    (hC : LocInteractionBound ν m tr t₁ t₂ C_loc)
    (hD : ComplForcingMeasurable κ P ν m b K hν hF tr t₁ t₂)
    (hE : FreeFlowAvailExists ν m tr t₁ t₂ b)
    (hTC : UnforcedLeray.Short.IIb.TrainClose tr (ν * b)⁻¹ 1) :
    ∃ G : ℝ → ℝ≥0∞,
      AEMeasurable G (volume.restrict (Ioc t₁ t₂)) ∧
      (∀ᵐ r ∂(volume.restrict (Ioc t₁ t₂)),
        G r ≤ ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ *
          xNorm (dd ν r) m (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)) ∧
      ∀ s ∈ Icc t₁ t₂,
        xNorm (dd ν s) m (compl (periodizedFrame κ ν m b K hν hF) w s) ≤
          ENNReal.ofReal (Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν t₁))) *
              xNorm (dd ν t₁) m (compl (periodizedFrame κ ν m b K hν hF) w t₁) +
            ∫⁻ r in Ioc t₁ s,
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
                  Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν r))) *
                (ENNReal.ofReal (C_loc + C_H0) *
                    xNorm (dd ν r) m (compl (periodizedFrame κ ν m b K hν hF) w r) + G r) := by
  set F := periodizedFrame κ ν m b K hν hF with hFdef
  obtain ⟨U, hU⟩ := hA hm hν ht₁ h12 htr hFree
  have hInt := hC hm hν ht₁ h12 hC_loc hLoc
  have hMild := hB hSeed hP hm hb1 htr ht₁ h12 hbt₂ f w u U hU (hE hm hν ht₁ h12 htr (by linarith) hbt₂ hTC) hFlow hCirc hInt hH0
  obtain ⟨hFm, hGm⟩ := hD hSeed hP hm hb1 htr ht₁ h12 hbt₂ f w u hFlow
  have hm0 : 0 ≤ m := by linarith
  have hrb : ∀ r ∈ Icc t₁ t₂, 0 ≤ r ∧ b ≤ clockTheta ν r := fun r hr =>
    ⟨ht₁.trans hr.1, hbt₂.trans (theta_anti hν (ht₁.trans hr.1) hr.2)⟩
  refine ⟨fun r => ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ *
      xNorm (dd ν r) m (complModeForce κ P F tr r j), hGm,
    Filter.Eventually.of_forall fun r => le_rfl, ?_⟩
  intro s hs
  refine (hMild s hs).trans (add_le_add ?_ ?_)
  · exact (hU.1 t₁ s le_rfl hs.1 hs.2 _)
  · refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    have hr' : r ∈ Icc t₁ t₂ := ⟨hr.1.le, hr.2.trans hs.2⟩
    obtain ⟨hr0, hbr⟩ := hrb r hr'
    have hW := memLp_compl F hm0 hν ht₁ hr'.1 hbr hFlow
    obtain ⟨hLm, hLb⟩ := hInt r hr' _ hW
    have hsrc := xNorm_complSource_le κ P F tr w hr0 hbr hC_loc hC_H0 hLm hLb (hH0 r hr')
      (hFm r hr')
    have hUb := hU.1 r s hr'.1 hr.2 hs.2 (complSource κ P F tr w r)
    have hz : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := by
      have : 0 < clockA ν r := by unfold clockA; positivity
      positivity
    have hexp : 0 ≤ Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν r)) :=
      (Real.exp_pos _).le
    rw [ENNReal.ofReal_mul hz]
    rw [mul_assoc]
    gcongr
    exact hUb.trans (by gcongr)
end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
