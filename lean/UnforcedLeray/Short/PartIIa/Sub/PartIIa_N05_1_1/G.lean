import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.Defs
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.ProductRuleWt
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.PhaseTest
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.ChainRule

/-!
# `Sub/PartII-a_N05_1_1/G`: Proof of `PhaseGradTransportWt` (`PartII-a:N05/1/1/1`)

Proves the true `s^{1/2}`-weighted gradient transport `phaseGradTransportWt : N05_1_1G.PhaseGradTransportWt`
(with constant `C = 1`) via the Hilbert adjoint `(U ∘ B0223.liftVec)† : Yq P 2 →L[ℂ] HSpace c MeridC`,
together with the one-line parent assembly
`phaseD2CutoffSQE_of_gen : N05_1_1Org.PhaseGeneratorTransport → PhaseD2CutoffSQE`
combining `phaseGradTransportWt` and `N05_1_1G.phaseCutoffProductRuleWt`.

## R5 / R11 Blocker Note on Verbatim `N05_1_1Org.PhaseGradTransport`
As documented in `G/Defs.lean` (see `the November 2 reference manuscript` lines 1644–1647, 1680),
`HSpace c MeridC = L²(s^{-3/2} ds dq dη)` while `(Q_ε b, ∂_η b, ε b_r) ∈ H_T = L²(s^{-1/2} ds dq dη)`.
Accordingly, `N05_1_1Org.PhaseGradTransport` (which omits `s^{1/2}` as `s → 0⁺`) is mathematically
false, whereas on `supp χ ⊆ {σ ≤ s ≤ H₁}` (`σ > 0`), `s^{-1/2} ≤ σ^{-1/2}` is absorbed into `Γ^k` by
`N05_1_1G.phaseCutoffProductRuleWt`. Because `Sub/PartII-a_N05_1_1.lean` is imported by accepted

or organizer can re-target `PartII-a:N05/1/1/1` to `phaseGradTransportWt` and close
`PartII-a:N05/1/1` (`Final.lean`) in 1 line via `phaseD2CutoffSQE_of_gen`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1G

private theorem integral_fromWt_eq_inner {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (fromWt (periodize c (W : Profile → MeridC)) p) (φ p) ∂(cellMeasure c) =
      inner ℂ W (toH (isMeridTest_ageScaleMerid 1 hφ)) := by
  rw [inner_toH_ageScale hc W 1 hφ]
  have hexp : (1 : ℝ) - 3 / 2 = -(1 / 2 : ℝ) := by norm_num
  simp only [fromWt, hexp]

private theorem integral_unwt_eq_inner {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC)
    {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    ∫ p, inner ℂ (periodize c (W : Profile → MeridC) p) (ψ p) ∂(cellMeasure c) =
      inner ℂ W (toH (isMeridTest_ageScaleMerid (3 / 2) hψ)) := by
  rw [inner_toH_ageScale hc W (3 / 2) hψ]
  have hexp : (3 / 2 : ℝ) - 3 / 2 = 0 := by norm_num
  simp only [hexp, Real.rpow_zero, one_smul]

private theorem inner_grad_dy {P : ℝ} [Fact (0 < P)] {v g : Yq P 2} {j : Fin 3}
    (hj : HasPhaseOp (fun Ψ => -dy j Ψ) v g) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    inner ℂ g (testElem P 2 Φ) = -inner ℂ v (testElem P 2 (dy j Φ)) := by
  rw [inner_testElem_right hΦ g, ← hj (conjTest Φ) (isPhaseTest_conjTest hΦ)]
  dsimp only
  rw [dy_conjTest j hΦ, phasePair_neg (isPhaseTest_conjTest (hΦ.dy j)) v, map_neg,
    ← inner_testElem_right (hΦ.dy j) v]

end N05_1_1G

/-- True `s^{1/2}`-weighted gradient transport (`PartII-a:N05/1/1/1`, with `C = 1`). -/
theorem phaseGradTransportWt : N05_1_1G.PhaseGradTransportWt := by
  refine ⟨1, zero_le_one, ?_⟩
  intro ν c ε _hν hc hε _hε1 P _ hP _hP1 U hU w v grad_v hv hgrad
  let Wli : HSpace c MeridC →ₗᵢ[ℂ] Yq P 2 := U.comp (B0223.liftVec hε hc hP)
  let W : HSpace c MeridC →L[ℂ] Yq P 2 := Wli.toContinuousLinearMap
  let Wadj : Yq P 2 →L[ℂ] HSpace c MeridC := ContinuousLinearMap.adjoint W
  have hW_norm : ‖W‖ ≤ 1 := Wli.norm_toContinuousLinearMap_le
  have hWadj_norm : ‖Wadj‖ ≤ 1 := by
    show ‖ContinuousLinearMap.adjoint W‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact hW_norm
  have hWadj_le : ∀ g : Yq P 2, ‖Wadj g‖ ≤ ‖g‖ := fun g =>
    (Wadj.le_opNorm g).trans ((mul_le_mul_of_nonneg_right hWadj_norm (norm_nonneg g)).trans
      (one_mul ‖g‖).le)
  have hW_toH : ∀ {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ),
      W (N05_1_1G.toH hψ) = testElem P 2 (N05_1_1G.meridPhaseTest ε P ψ) := fun hψ =>
    N05_1_1G.lift_toH_eq_testElem hc hε hP U hU hψ
  have hw_inner : ∀ {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ),
      inner ℂ w (N05_1_1G.toH hψ) =
        inner ℂ (v : Yq P 2) (testElem P 2 (N05_1_1G.meridPhaseTest ε P ψ)) := fun {ψ} hψ => by
    rw [← Wli.inner_map_map w (N05_1_1G.toH hψ)]
    have hv' : Wli w = (v : Yq P 2) := hv.symm
    have hψ' : Wli (N05_1_1G.toH hψ) = testElem P 2 (N05_1_1G.meridPhaseTest ε P ψ) :=
      hW_toH hψ
    rw [hv', hψ']
  let Qw : HSpace c MeridC :=
    Wadj (N05_1_1G.mulUnitR P 0 (grad_v 0) + N05_1_1G.mulUnitR P 1 (grad_v 1))
  let Ew : HSpace c MeridC := Wadj (grad_v 2)
  refine ⟨Qw, Ew, ?_, ?_, ?_⟩
  · -- `WeakQWt c ε w Qw`
    intro φ hφ
    set ψ := N05_1_1G.ageScaleMerid 1 φ
    have hψ : IsMeridTest c ψ := N05_1_1G.isMeridTest_ageScaleMerid 1 hφ
    set Φ := N05_1_1G.meridPhaseTest ε P ψ
    have hΦ : IsPhaseTest P Φ := N05_1_1G.isPhaseTest_meridPhaseTest hε hP hψ
    have hU0 : IsPhaseTest P (N05_1_1G.unitRTest 0 Φ) :=
      N05_1_1G.isPhaseTest_unitRTest_meridPhaseTest hε hP 0 hψ
    have hU1 : IsPhaseTest P (N05_1_1G.unitRTest 1 Φ) :=
      N05_1_1G.isPhaseTest_unitRTest_meridPhaseTest hε hP 1 hψ
    have hQtest : IsMeridTest c (fun p => pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p)) :=
      N05_1_1P.mt_sub (N05_1_1P.mt_pdQ hφ)
        (N05_1_1P.mt_smul (N05_1_1P.SP.const c ε)
          (N05_1_1P.mt_add (N05_1_1P.mt_opK hφ) (N05_1_1P.mt_smul (N05_1_1P.SP.const c 2) hφ)))
    rw [N05_1_1G.integral_fromWt_eq_inner hc Qw hφ,
      N05_1_1G.integral_unwt_eq_inner hc w hQtest]
    show inner ℂ (ContinuousLinearMap.adjoint W _) (N05_1_1G.toH hψ) = _
    rw [ContinuousLinearMap.adjoint_inner_left, hW_toH hψ, inner_add_left,
      N05_1_1G.inner_mulUnitR_testElem 0 (grad_v 0) hΦ hU0,
      N05_1_1G.inner_mulUnitR_testElem 1 (grad_v 1) hΦ hU1]
    change inner ℂ (grad_v 0) (testElem P 2 (N05_1_1G.unitRTest 0 Φ)) +
        inner ℂ (grad_v 1) (testElem P 2 (N05_1_1G.unitRTest 1 Φ)) = _
    rw [N05_1_1G.inner_grad_dy (hgrad 0) hU0,
      N05_1_1G.inner_grad_dy (hgrad 1) hU1,
      ← neg_add, ← inner_add_right,
      ← testElem_add ((hU0.dy 0).isSliceTest 2) ((hU1.dy 1).isSliceTest 2),
      N05_1_1G.dy_radial_meridPhaseTest hε hP hφ,
      hw_inner (N05_1_1G.isMeridTest_ageScaleMerid (3 / 2) hQtest)]
  · -- `WeakEtaWt c w Ew`
    intro φ hφ
    set ψ := N05_1_1G.ageScaleMerid 1 φ
    have hψ : IsMeridTest c ψ := N05_1_1G.isMeridTest_ageScaleMerid 1 hφ
    set Φ := N05_1_1G.meridPhaseTest ε P ψ
    have hΦ : IsPhaseTest P Φ := N05_1_1G.isPhaseTest_meridPhaseTest hε hP hψ
    have hη : IsMeridTest c (pdEta φ) := N05_1_1P.mt_pdEta hφ
    rw [N05_1_1G.integral_fromWt_eq_inner hc Ew hφ,
      N05_1_1G.integral_unwt_eq_inner hc w hη]
    show inner ℂ (ContinuousLinearMap.adjoint W (grad_v 2)) (N05_1_1G.toH hψ) = _
    rw [ContinuousLinearMap.adjoint_inner_left, hW_toH hψ,
      N05_1_1G.inner_grad_dy (hgrad 2) hΦ,
      N05_1_1G.dy_two_meridPhaseTest hε hP hφ,
      hw_inner (N05_1_1G.isMeridTest_ageScaleMerid (3 / 2) hη)]
  · -- Norm bound `‖Qw‖ + ‖Ew‖ ≤ 1 * (‖v‖ + ∑ j, ‖grad_v j‖)`
    have hQ_le : ‖Qw‖ ≤ ‖grad_v 0‖ + ‖grad_v 1‖ :=
      (hWadj_le _).trans ((norm_add_le _ _).trans
        (add_le_add (N05_1_1G.norm_mulUnitR_le 0 (grad_v 0))
          (N05_1_1G.norm_mulUnitR_le 1 (grad_v 1))))
    have hE_le : ‖Ew‖ ≤ ‖grad_v 2‖ := hWadj_le (grad_v 2)
    have hsum : ∑ j : Fin 3, ‖grad_v j‖ = ‖grad_v 0‖ + ‖grad_v 1‖ + ‖grad_v 2‖ :=
      Fin.sum_univ_three _
    have hv0 : 0 ≤ ‖(v : Yq P 2)‖ := norm_nonneg _
    linarith

/-- One-line assembly of `PhaseD2CutoffSQE` (`PartII-a:N05/1/1`) from `PhaseGeneratorTransport`
(`PartII-a:N05/1/2`), bypassing the false unweighted `N05_1_1Org.PhaseGradTransport`. -/
theorem phaseD2CutoffSQE_of_gen (hT : N05_1_1Org.PhaseGeneratorTransport) :
    PhaseD2CutoffSQE :=
  N05_1_1G.phaseD2CutoffSQE_of_wt phaseGradTransportWt hT N05_1_1G.phaseCutoffProductRuleWt

end UnforcedLeray.Short.PartIIa
