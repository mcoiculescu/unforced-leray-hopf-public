import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org

/-!
# Leaf (b) of `PartIII-a:T21/c3/3/1/1`: Props and conditional assembly

Source `the November 2 reference manuscript` (SP) lines 2919-2925, 2937-2958.
`ComplMildFreeBound` follows from two Props:

* `XNormIntegralLe` (Minkowski in `X_{m,d}`; `Conv.mixedNorm_integral_le`, `Lib/ConvIneq/MinkowskiMixed.lean`);
* `ComplDuhamelRep` (the complement `W⊥ = compl F w` is the mild solution of the free moving
  evolution with source `complSource`, by uniqueness of weak forced free flows via duality with the
  backward free adjoint flow of cylinder data; SP 2919-2925).

`complMildFreeBound_of` is the assembly; the task `PartIII-a:T21/c3/3/1/1/2` composes it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

/-- Minkowski's integral inequality in `X_{m,d}` (norm of a parametric integral). -/
def XNormIntegralLe : Prop :=
  ∀ (d m a b : ℝ) (G : ℝ → ℝ × ℝ → ℂ),
    AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioc a b)).prod (B0579.cellMeasure d m)) →
    xNorm d m (fun y => ∫ r in Ioc a b, G r y) ≤ ∫⁻ r in Ioc a b, xNorm d m (G r)

/-- The mild (Duhamel) representation of the complement by the free moving propagator, with the
measurability facts needed to take norms (SP 2919-2925, 2937-2958). -/
def ComplDuhamelRep (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ) (hν : 0 < ν)
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
      AEStronglyMeasurable (U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁))
        (B0579.cellMeasure (dd ν s) m) ∧
      ∃ G : ℝ → ℝ × ℝ → ℂ,
        (∀ r ∈ Ioc t₁ s, G r =ᵐ[B0579.cellMeasure (dd ν s) m]
          fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
            U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) y) ∧
        AEStronglyMeasurable (Function.uncurry G)
          ((volume.restrict (Ioc t₁ s)).prod (B0579.cellMeasure (dd ν s) m)) ∧
        (∫⁻ r in Ioc t₁ s, xNorm (dd ν s) m (G r) ≠ ⊤ →
          compl (periodizedFrame κ ν m b K hν hF) w s =ᵐ[B0579.cellMeasure (dd ν s) m]
            fun y => U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁) y +
              ∫ r in Ioc t₁ s, G r y)

/-- Assembly of `ComplMildFreeBound` from Minkowski and the Duhamel representation. -/
theorem complMildFreeBound_of (κ : PlanarFrameKernels) (P : PlanarData) (ν m b K : ℝ)
    (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc C_H0 : ℝ)
    (hMink : XNormIntegralLe) (hRep : ComplDuhamelRep κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0) :
    ComplMildFreeBound κ P ν m b K hν hF tr t₁ t₂ C_loc C_H0 := by
  intro hSeed hP hm hb htr ht₁ h12 hbt₂ f w u U hU hAvail hFlow hCirc hInt hH0 s hs
  obtain ⟨hm1, G, hGe, hm2, hEq⟩ := hRep hSeed hP hm hb htr ht₁ h12 hbt₂ f w u U hU hAvail hFlow
    hCirc hInt hH0 s hs
  have hnorm : ∀ r ∈ Ioc t₁ s, xNorm (dd ν s) m (G r) =
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        xNorm (dd ν s) m
          (U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r)) := by
    intro r hr
    have h1 : xNorm (dd ν s) m (G r) = xNorm (dd ν s) m
        (fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
          U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) y) :=
      eLpNorm_congr_ae (hGe r hr)
    rw [h1]
    simp only [xNorm]
    have : (fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
            U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) y) =
            (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) •
              U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r) := rfl
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have hcl : 0 ≤ clockA ν r := by
      unfold clockA
      have : 0 ≤ ν * r := mul_nonneg hν.le hr0
      linarith
    have hz : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := Real.rpow_nonneg hcl _
    rw [this, eLpNorm_const_smul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
  have hint : ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
      xNorm (dd ν s) m
        (U s r (complSource κ P (periodizedFrame κ ν m b K hν hF) tr w r)) =
      ∫⁻ r in Ioc t₁ s, xNorm (dd ν s) m (G r) :=
    (setLIntegral_congr_fun measurableSet_Ioc fun r hr => (hnorm r hr).symm)
  by_cases hfin : ∫⁻ r in Ioc t₁ s, xNorm (dd ν s) m (G r) = ⊤
  · rw [hint, hfin]
    simp
  · have hEq' := hEq hfin
    have hint_meas : AEStronglyMeasurable (fun y => ∫ r in Ioc t₁ s, G r y)
        (B0579.cellMeasure (dd ν s) m) := by
      haveI : SFinite (B0579.cellMeasure (dd ν s) m) := by
        unfold B0579.cellMeasure; infer_instance
      exact hm2.prod_swap.integral_prod_right' (ν := volume.restrict (Ioc t₁ s))
    rw [hint]
    calc xNorm (dd ν s) m (compl (periodizedFrame κ ν m b K hν hF) w s)
        = xNorm (dd ν s) m (fun y => U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁) y +
            ∫ r in Ioc t₁ s, G r y) := eLpNorm_congr_ae hEq'
      _ ≤ xNorm (dd ν s) m (U s t₁ (compl (periodizedFrame κ ν m b K hν hF) w t₁)) +
            xNorm (dd ν s) m (fun y => ∫ r in Ioc t₁ s, G r y) :=
          eLpNorm_add_le hm1 hint_meas (by norm_num)
      _ ≤ _ := by
          gcongr
          exact hMink _ _ _ _ G hm2

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
