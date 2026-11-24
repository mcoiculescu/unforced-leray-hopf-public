import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.ComplexAdjointOp
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.SliceTaylor

/-!
# Part II-a, task `PartII-a:F02/10`: the adjoint of the phase semigroup on a phase test

Source of record: `the November 2 reference manuscript`, lines 1363-1370.
Proves the Prop `PhaseAdjointTaylor` of `Sub/F02.lean`. The adjoint is
`ψ_s = A.compLpL (testElem Φ)` with `A` the bounded complex adjoint of `ComplexAdjointOp`
(`ComplexAdjointOp.lean`); the duality is the first conjunct of `ComplexAdjointOp` applied pointwise
in the phase, and the Taylor bound is the uniform slice bound `SliceTaylor` (`SliceTaylor.lean`),
lifted to `Y_{q'}` by `Lp.norm_le_of_ae_bound` on the probability measure `haarAddCircle`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

set_option maxHeartbeats 1600000 in
/-- **The adjoint of the phase semigroup on a phase test** (task `PartII-a:F02/10`). -/
theorem phaseAdjointTaylor : UnforcedLeray.Short.PartIIa.PhaseAdjointTaylor := by
  intro r _ h1 h3 P _ nu hnu Φ hΦ
  have hq : r ≠ ⊤ := ne_top_of_lt h3
  have hp : conjExp r ≠ ⊤ := conjExp_ne_top h1
  have hp1 : (1 : ℝ≥0∞) ≤ conjExp r := (conjExp_fact (q := r)).out
  have hSL : UnforcedLeray.Short.PartIIa.SliceTaylor := sliceTaylor
  have hCO : UnforcedLeray.Short.PartIIa.ComplexAdjointOp := complexAdjointOp
  obtain ⟨C, hC0, hT⟩ := hSL nu (conjExp r) P Φ hnu hp1 hp hΦ
  refine ⟨C, hC0, fun s hs0 hs1 => ?_⟩
  obtain ⟨A, hA1, hA2⟩ := hCO r hq h1 nu s hnu.le hs0.le
  have hGt : IsPhaseTest P (F02.genT nu Φ) := F02.isPhaseTest_genT hΦ nu
  have hs : IsSliceTest P (conjExp r) Φ := hΦ.isSliceTest (conjExp r)
  have hsG : IsSliceTest P (conjExp r) (F02.genT nu Φ) := hGt.isSliceTest (conjExp r)
  refine ⟨A.compLpL (conjExp r) AddCircle.haarAddCircle (testElem P (conjExp r) Φ), ?_, ?_⟩
  · -- duality, pointwise in the phase
    intro x
    change phasePairing P r (testElem P (conjExp r) Φ) _ =
      phasePairing P r (A.compLpL (conjExp r) AddCircle.haarAddCircle (testElem P (conjExp r) Φ)) x
    rw [phasePairing_apply, phasePairing_apply]
    refine integral_congr_ae ?_
    filter_upwards [(B0421.freeC hq nu s).coeFn_compLpL (μ := AddCircle.haarAddCircle) (p := r) x,
      A.coeFn_compLpL (μ := AddCircle.haarAddCircle) (p := conjExp r)
        (testElem P (conjExp r) Φ)] with τ e1 e2
    simp only [e1, e2]
    exact (hA1 _ _).symm
  · -- the Taylor bound in Y_{q'}
    have hψ0 : ⇑(testElem P (conjExp r) Φ) =ᵐ[AddCircle.haarAddCircle] ⇑(circleSlice hs) := by
      rw [testElem_of hs]
      exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp r) (volume : Measure Space))
        (p := conjExp r) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
    have hgT : ⇑(testElem P (conjExp r) (F02.genT nu Φ)) =ᵐ[AddCircle.haarAddCircle]
        ⇑(circleSlice hsG) := by
      rw [testElem_of hsG]
      exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp r) (volume : Measure Space))
        (p := conjExp r) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsG)
    have hψs := A.coeFn_compLpL (μ := AddCircle.haarAddCircle) (p := conjExp r)
      (testElem P (conjExp r) Φ)
    -- the slice bound at every phase point
    have hpt : ∀ τ : AddCircle P,
        ‖A (circleSlice hs τ) - circleSlice hs τ - (s : ℂ) • circleSlice hsG τ‖ ≤ C * s ^ 2 := by
      intro τ
      induction τ using QuotientAddGroup.induction_on with
      | H t =>
        simp only [circleSlice_coe]
        have hsl : ⇑(sliceMap hs.2 t) =ᵐ[volume] fun y => Φ (t, y) :=
          MemLp.coeFn_toLp (hs.2.memLp t)
        have hsG' : ⇑(sliceMap hsG.2 t) =ᵐ[volume] fun y => F02.genT nu Φ (t, y) :=
          MemLp.coeFn_toLp (hsG.2.memLp t)
        have hAs : ⇑(A (sliceMap hs.2 t)) =ᵐ[volume] adjC nu s (fun z => Φ (t, z)) :=
          hA2 _ _ hsl
        have hcongr : eLpNorm (⇑(A (sliceMap hs.2 t) - sliceMap hs.2 t -
              (s : ℂ) • sliceMap hsG.2 t)) (conjExp r) volume =
            eLpNorm (fun y => adjC nu s (fun z => Φ (t, z)) y - Φ (t, y) -
              (s : ℂ) • F02.genT nu Φ (t, y)) (conjExp r) volume := by
          apply eLpNorm_congr_ae
          filter_upwards [Lp.coeFn_sub (A (sliceMap hs.2 t) - sliceMap hs.2 t)
              ((s : ℂ) • sliceMap hsG.2 t),
            Lp.coeFn_sub (A (sliceMap hs.2 t)) (sliceMap hs.2 t),
            Lp.coeFn_smul (s : ℂ) (sliceMap hsG.2 t), hAs, hsl, hsG'] with y e1 e2 e3 e4 e5 e6
          simp only [Pi.sub_apply, Pi.smul_apply] at e1 e2 e3 ⊢
          rw [e1, e2, e3, e4, e5, e6]
        rw [Lp.norm_def, hcongr]
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hT t s hs0 hs1)).trans_eq
          (ENNReal.toReal_ofReal (mul_nonneg hC0 (sq_nonneg s)))
    -- the a.e. bound on the phase circle
    have hfC : ∀ᵐ τ ∂AddCircle.haarAddCircle,
        ‖(A.compLpL (conjExp r) AddCircle.haarAddCircle (testElem P (conjExp r) Φ) -
          testElem P (conjExp r) Φ - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)) τ‖
          ≤ C * s ^ 2 := by
      filter_upwards [Lp.coeFn_sub
          (A.compLpL (conjExp r) AddCircle.haarAddCircle (testElem P (conjExp r) Φ) -
            testElem P (conjExp r) Φ) ((s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)),
        Lp.coeFn_sub (A.compLpL (conjExp r) AddCircle.haarAddCircle (testElem P (conjExp r) Φ))
          (testElem P (conjExp r) Φ),
        Lp.coeFn_smul (s : ℂ) (testElem P (conjExp r) (F02.genT nu Φ)),
        hψs, hψ0, hgT] with τ e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, e6, Pi.sub_apply, Pi.smul_apply]
      exact hpt τ
    have hbd := Lp.norm_le_of_ae_bound (μ := AddCircle.haarAddCircle) (C := C * s ^ 2)
      (mul_nonneg hC0 (sq_nonneg s)) hfC
    have hmu : measureUnivNNReal (AddCircle.haarAddCircle (T := P)) = 1 := by
      simp [measureUnivNNReal]
    simpa [hmu] using hbd

end UnforcedLeray.Short.PartIIa
