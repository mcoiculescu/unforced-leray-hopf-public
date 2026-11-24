import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Defs

/-!
# Split of `ComplDuhamelRep` (`PartIII-a:T21/c3/3/1/1/2/2`)

Source `the November 2 reference manuscript` (SP) lines 2905-2925, 2937-2958.

`ComplDuhamelRep` (Leaf2Defs.lean) says that `W⊥ = compl F w` is the mild solution of the free moving
evolution `U` with source `S = complSource`.  The source proves it by uniqueness of weak forced
free flows, by duality with the backward free adjoint flow of cylinder data.  Four leaves:

* `FreeMovingDuality` (ii-a): backward free adjoint flows `Φ` of every datum `Γ ∈ X_{-m,d(s)}`
  exist (regular, `IsFreeAdjointFlow`), and `⟨U(s,s₁) g, Γ⟩ = ⟨g, Φ(s₁)⟩` (the extension by
  density of the cylinder-data duality of the two weak formulations).
* `ComplWeakEq` (i): the moving pairing `⟨W⊥(s), Γ⟩` obeys the Duhamel identity against `Φ`
  (differentiate the moving pairing, `(ΛW)' = H₀W`; `movH0`, `complModeForce`).
* `ComplSourceRegular` (iii): `S(r) ∈ X_{m,d(r)}`; measurability of `U(s,t₁)W⊥(t₁)`, and a jointly
  measurable representative `G` of `a(r)⁻² U(s,r) S(r)`.
* `DualUniq` (ii-b): an `X_m` function is determined by its pairings against `X_{-m}`.

The assembly `ComplDuhamelRep` from these (Fubini for the pairing of the `r`-integral, then
`DualUniq`) is the unconditional task `PartIII-a:T21/c3/3/1/1/2/2`, file `Leaf2Rep.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

/-- The tested right-hand side of the free backward adjoint `-∂_rφ = νΔφ + v·∇φ` at age `r`:
`φ (νΔψ - v·∇ψ)` (the free part of `adjIntegrand`). -/
def freeAdjIntegrand {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (φ : ℝ × ℝ → ℂ) (r : ℝ)
    (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  φ x * ((ν * UnforcedLeray.Short.IIb.lapP ψ x -
    (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)

/-- `φ` is a regular weak reverse-time solution on `[t, s]` in `X_{-m,c}` of the free adjoint
equation (no Biot-Savart term) with terminal datum `g` at age `s` (SP 2937-2958; the free analogue
of `IsAdjointFlow`, SP 3060). -/
structure IsFreeAdjointFlow (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop where
  terminal : φ s =ᵐ[volume.restrict (B0579.cell c)] g
  memX : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m))
  strongCont : ∀ r ∈ Icc t s,
    Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0)
  periodic : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x
  smooth : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ r)
  jointSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)
  memH1 : ∀ r ∈ Ico t s, ∀ k : Fin 2, MemLp (pdCx k (φ r)) 2 (B0579.cellMeasure c (-m))
  strongContH1 : ∀ r ∈ Ico t s, ∀ k : Fin 2,
    Tendsto (fun r' => xNorm c (-m) (pdCx k (φ r') - pdCx k (φ r))) (𝓝[Ico t s] r) (𝓝 0)
  integrable : ∀ ψ, B0579.IsCylTest c ψ → ∀ r ∈ Icc t s,
    IntegrableOn (freeAdjIntegrand tr (φ r) r ψ) (B0579.cell c)
  timeIntegrable : ∀ ψ, B0579.IsCylTest c ψ →
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x) volume t s
  weak : ∀ ψ, B0579.IsCylTest c ψ → ∀ r ∈ Icc t s,
    ∫ x in B0579.cell c, φ r x * (ψ x : ℂ) =
      (∫ x in B0579.cell c, g x * (ψ x : ℂ)) +
        ∫ r' in r..s, ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r') r' ψ x

/-- `Φ` is the moving backward free adjoint flow of the moving terminal datum `Γ` at age `s`:
`Φ(r) = a(r)⁻¹ φ(r, √a(r) ·)` for a regular physical free adjoint `φ` with terminal datum
`physAdj a(s) Γ` (SP 2937-2958, 3036-3037). -/
def MovingFreeAdjoint (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (Γ : ℝ × ℝ → ℂ) (Φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∃ φ : ℝ → ℝ × ℝ → ℂ,
    IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) Γ) φ ∧
    ∀ r ∈ Icc t s, Φ r =ᵐ[volume.restrict (B0579.cell (dd ν r))] movingPhi ν φ r

/-- **Leaf (ii-b)** (SP 2937-2958): a function of `X_{m,d}` is determined a.e. by its pairings with
`X_{-m,d}` (take `Γ = conj(A - B) (1 + q² + η²)^m`). -/
def DualUniq : Prop :=
  ∀ (d m : ℝ) (A B : ℝ × ℝ → ℂ), MemLp A 2 (B0579.cellMeasure d m) →
    MemLp B 2 (B0579.cellMeasure d m) →
    (∀ Γ : ℝ × ℝ → ℂ, MemLp Γ 2 (B0579.cellMeasure d (-m)) →
      ∫ y in B0579.cell d, A y * Γ y = ∫ y in B0579.cell d, B y * Γ y) →
    A =ᵐ[B0579.cellMeasure d m] B

/-- **Leaf (ii-a)** (SP 2937-2958): duality of the free moving propagator `U` with the backward
free adjoint flow: for every `Γ ∈ X_{-m,d(s₂)}` there is a regular moving adjoint flow `Φ` on
`[t₁, s₂]` with terminal datum `Γ` such that `⟨U(s₂,s₁) g, Γ⟩ = ⟨g, Φ(s₁)⟩` for all
`g ∈ X_{m,d(s₁)}`, `t₁ ≤ s₁ ≤ s₂ ≤ t₂`.  (Existence: Volterra construction as for
`AdjointWeakExists` without the Biot-Savart term; identity: cylinder data by the two weak
formulations, then by boundedness of `U` and density.) -/
def FreeMovingDuality (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  ∀ U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
    IsFreeMovingPropagator ν m tr t₁ t₂ U → FreeFlowAvail ν m tr t₁ t₂ →
    ∀ s₂ ∈ Icc t₁ t₂, ∀ Γ : ℝ × ℝ → ℂ, MemLp Γ 2 (B0579.cellMeasure (dd ν s₂) (-m)) →
      ∃ Φ : ℝ → ℝ × ℝ → ℂ, MovingFreeAdjoint ν m tr t₁ s₂ Γ Φ ∧
        ∀ s₁ ∈ Icc t₁ s₂, ∀ g : ℝ × ℝ → ℂ, MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) →
          ∫ y in B0579.cell (dd ν s₂), U s₂ s₁ g y * Γ y =
            ∫ y in B0579.cell (dd ν s₁), g y * Φ s₁ y

/-- **Leaf (i)** (SP 2905-2925): the moving pairing of the complement against a moving free
adjoint flow `Φ` obeys the Duhamel identity with the source `complSource`:
`⟨W⊥(s), Γ⟩ = ⟨W⊥(t₁), Φ(t₁)⟩ + ∫_{(t₁,s]} a(r)⁻² ⟨S(r), Φ(r)⟩ dr`, provided the time integrand is
integrable (differentiate the moving pairing, `(ΛW)' = H₀W`; uses `movH0`, `movOscRes`,
`movEulerRes`, `complModeForce`, `IsLinearisedFlow.weak`). -/
def ComplWeakEq (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) : Prop :=
  IsSeedKernels κ → IsPlanarReference P → 8 < m → 1 ≤ b →
  UnforcedLeray.Short.PartI.IsBUCTrain tr → 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
  (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
  (∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
    xNorm (dd ν r) m (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) ≠ ⊤) →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
    HasZeroCirculation (ν ^ (-2 : ℝ)) f →
    (∀ r ∈ Icc t₁ t₂, ∀ s' ∈ Icc r t₂, ∀ i : Fin 2,
      ampl (periodizedFrame κ ν m b K hν hF) w s' i - ampl (periodizedFrame κ ν m b K hν hF) w r i =
        ∫ q in Ioc r s', (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q i (movingW ν w q)) →
    LocInteractionConcl ν m tr t₁ t₂ C_loc →
    H0Hyp κ (periodizedFrame κ ν m b K hν hF) tr w t₁ t₂ C_H0 →
    ∀ s ∈ Icc t₁ t₂, ∀ (Γ : ℝ × ℝ → ℂ) (Φ : ℝ → ℝ × ℝ → ℂ),
      MemLp Γ 2 (B0579.cellMeasure (dd ν s) (-m)) → MovingFreeAdjoint ν m tr t₁ s Γ Φ →
      IntegrableOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ∫ y in B0579.cell (dd ν r),
          complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r y * Φ r y) (Ioc t₁ s) →
      ∫ y in B0579.cell (dd ν s), compl (periodizedFrame κ ν m b K hν hF) w s y * Γ y =
        (∫ y in B0579.cell (dd ν t₁),
            compl (periodizedFrame κ ν m b K hν hF) w t₁ y * Φ t₁ y) +
          ∫ r in Ioc t₁ s, (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
            ∫ y in B0579.cell (dd ν r),
              complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r y * Φ r y

/-- **Leaf (iii)** (SP 2919-2925, 2937-2958): regularity of the Duhamel data.  The source lies in
`X_{m,d(r)}` for `r ∈ [t₁, t₂]` (`LocInteractionConcl`, `H0Hyp`, the mode forcings of
`ComplForcingMeasurable`); `U(s,t₁)W⊥(t₁)` is a.e. strongly measurable (`U` is, a.e., the limit of
its values on cylinder data); and `a(r)⁻² U(s,r) S(r)` has a jointly measurable representative `G`
on `(t₁, s] × cell d(s)` (measurability of `r ↦ U s r (S r)` in `X_{m,d(s)}` via the duality leaf
and measurability of the pairings `r ↦ ⟨S r, Φ r⟩`).  `hD` is the forcing measurability leaf. -/
def ComplSourceRegular (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ) : Prop :=
  ComplForcingMeasurable κ P ν m b K hν hF tr t₁ t₂ →
  IsSeedKernels κ → IsPlanarReference P → 8 < m → 1 ≤ b →
  UnforcedLeray.Short.PartI.IsBUCTrain tr → 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ)
    (U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)),
    IsFreeMovingPropagator ν m tr t₁ t₂ U → FreeFlowAvail ν m tr t₁ t₂ →
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
    HasZeroCirculation (ν ^ (-2 : ℝ)) f →
    LocInteractionConcl ν m tr t₁ t₂ C_loc →
    H0Hyp κ (periodizedFrame κ ν m b K hν hF) tr w t₁ t₂ C_H0 →
    (∀ r ∈ Icc t₁ t₂, MemLp (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) 2
      (B0579.cellMeasure (dd ν r) m)) ∧
    ∀ s ∈ Icc t₁ t₂,
      AEStronglyMeasurable (U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁))
        (B0579.cellMeasure (dd ν s) m) ∧
      ∃ G : ℝ → ℝ × ℝ → ℂ,
        (∀ r ∈ Ioc t₁ s, G r =ᵐ[B0579.cellMeasure (dd ν s) m]
          fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
            U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) y) ∧
        AEStronglyMeasurable (Function.uncurry G)
          ((volume.restrict (Ioc t₁ s)).prod (B0579.cellMeasure (dd ν s) m))

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
