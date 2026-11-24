import UnforcedLeray.Short.PartI.Sub.T02_2_3
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.SlicePartials
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.ParamDerivC1
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Part I, task `PartI:T02/2/3`, leaf `pbTimeAvgSmooth`: the time-integrated pressure is smooth

Source of record: `the November 2 reference manuscript`, line 447.
Target `pbTimeAvgSmooth : PbTimeAvgSmooth` (definition in `Sub/T02_2_3.lean`).

Proof.  If `T ≤ 0` then `a = b = 0` and every time integral vanishes.  If `T > 0`, let `P z = ∫_a^b F σ z dσ`
and let `P1`, `P2` be the integrals of `∂_q F`, `∂_η F`.  By `pbParamDerivC1` applied to `F`,
`∂_q F`, `∂_η F`: `P` is `C¹`, `∂_q P = P1`, `∂_η P = P2`, and `P1`, `P2` are `C¹` with
`∂_q P1`, `∂_η P2` the integrals of the second partials.  Writing `fderiv P z v = ∂_q P z · v₁ + ∂_η P z · v₂`
shows `fderiv P` is `C¹`, so `P` is `C²`.  The Laplacian identity follows from the partial identities
and `intervalIntegral.integral_add`, the integrands being continuous in `σ` by `pbSlicePartials`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- A slice in time of a jointly `C^∞` family is continuous in `σ`. -/
theorem pbTA_cont_slice {K : ℝ → Plane → ℝ} {T : ℝ}
    (hK : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => K x.1 x.2) (Icc 0 T ×ˢ univ)) (z : Plane) :
    ContinuousOn (fun σ : ℝ => K σ z) (Icc 0 T) := by
  have hc : Continuous (fun σ : ℝ => ((σ, z) : ℝ × Plane)) :=
    continuous_id.prodMk continuous_const
  refine hK.continuousOn.comp hc.continuousOn ?_
  intro σ hσ
  exact ⟨hσ, mem_univ z⟩

/-- For a differentiable function on the plane, the derivative in direction `v` is the
combination of its two partials. -/
theorem pbTA_fderiv_apply {P : Plane → ℝ} (hP : Differentiable ℝ P) (z v : Plane) :
    fderiv ℝ P z v = Cyl.partialQ P z * v.1 + Cyl.partialEta P z * v.2 := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have key : fderiv ℝ P z (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) =
      Cyl.partialQ P z * v.1 + Cyl.partialEta P z * v.2 := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      ← Cyl.partialQ_eq_fderiv hP z, ← Cyl.partialEta_eq_fderiv hP z]
    ring
  rwa [← hv] at key

/-- **Time-integrated pressure is smooth** (source line 447; leaf of `PressureBounded`). -/
theorem pbTimeAvgSmooth : PbTimeAvgSmooth := by
  intro T F a b ha hb hF
  rcases le_or_gt T 0 with hT | hT
  · -- `T ≤ 0` forces `a = b = 0`, and all the integrals vanish
    have ha0 : a = 0 := le_antisymm (ha.2.trans hT) ha.1
    have hb0 : b = 0 := le_antisymm (hb.2.trans hT) hb.1
    subst ha0
    subst hb0
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [intervalIntegral.integral_same]
      exact contDiff_const
    · intro z
      simp [Cyl.partialQ]
    · intro z
      simp [Cyl.partialEta]
    · intro z
      simp [Train.lapS, Cyl.partialQ, Cyl.partialEta]
  · -- the case `T > 0`
    have hF1 : ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) :=
      hF.of_le (by simp)
    obtain ⟨hG1, hG2⟩ := pbSlicePartials T F hT hF
    have hG1c : ContDiffOn ℝ 1 (fun x : ℝ × Plane => Cyl.partialQ (F x.1) x.2)
        (Icc 0 T ×ˢ univ) :=
      hG1.of_le (by simp)
    have hG2c : ContDiffOn ℝ 1 (fun x : ℝ × Plane => Cyl.partialEta (F x.1) x.2)
        (Icc 0 T ×ˢ univ) :=
      hG2.of_le (by simp)
    -- second-order slice partials
    obtain ⟨hGQQ, _⟩ := pbSlicePartials T (fun σ w => Cyl.partialQ (F σ) w) hT hG1
    obtain ⟨_, hGEE⟩ := pbSlicePartials T (fun σ w => Cyl.partialEta (F σ) w) hT hG2
    -- differentiation under the time integral
    obtain ⟨hPC1, hPq, hPe⟩ := pbParamDerivC1 T F a b hT ha hb hF1
    have hQ := pbParamDerivC1 T (fun σ w => Cyl.partialQ (F σ) w) a b hT ha hb hG1c
    have hE := pbParamDerivC1 T (fun σ w => Cyl.partialEta (F σ) w) a b hT ha hb hG2c
    have hQC1 : ContDiff ℝ 1 (fun z : Plane => ∫ σ in a..b, Cyl.partialQ (F σ) z) := hQ.1
    have hEC1 : ContDiff ℝ 1 (fun z : Plane => ∫ σ in a..b, Cyl.partialEta (F σ) z) := hE.1
    have hQQ : ∀ z : Plane,
        Cyl.partialQ (fun w => ∫ σ in a..b, Cyl.partialQ (F σ) w) z =
          ∫ σ in a..b, Cyl.partialQ (Cyl.partialQ (F σ)) z := hQ.2.1
    have hEE : ∀ z : Plane,
        Cyl.partialEta (fun w => ∫ σ in a..b, Cyl.partialEta (F σ) w) z =
          ∫ σ in a..b, Cyl.partialEta (Cyl.partialEta (F σ)) z := hE.2.2
    have hPQ : Cyl.partialQ (fun w => ∫ σ in a..b, F σ w) =
        fun z => ∫ σ in a..b, Cyl.partialQ (F σ) z := funext hPq
    have hPE : Cyl.partialEta (fun w => ∫ σ in a..b, F σ w) =
        fun z => ∫ σ in a..b, Cyl.partialEta (F σ) z := funext hPe
    have hPQQ : ∀ z : Plane,
        Cyl.partialQ (Cyl.partialQ (fun w => ∫ σ in a..b, F σ w)) z =
          ∫ σ in a..b, Cyl.partialQ (Cyl.partialQ (F σ)) z := by
      intro z
      rw [hPQ]
      exact hQQ z
    have hPEE : ∀ z : Plane,
        Cyl.partialEta (Cyl.partialEta (fun w => ∫ σ in a..b, F σ w)) z =
          ∫ σ in a..b, Cyl.partialEta (Cyl.partialEta (F σ)) z := by
      intro z
      rw [hPE]
      exact hEE z
    -- integrability of the second partials in `σ`
    have hint1 : ∀ z : Plane,
        IntervalIntegrable (fun σ : ℝ => Cyl.partialQ (Cyl.partialQ (F σ)) z) volume a b := by
      intro z
      have hc : ContinuousOn (fun σ : ℝ => Cyl.partialQ (Cyl.partialQ (F σ)) z) (Icc 0 T) :=
        pbTA_cont_slice (K := fun σ w => Cyl.partialQ (Cyl.partialQ (F σ)) w) hGQQ z
      exact ContinuousOn.intervalIntegrable (hc.mono (uIcc_subset_Icc ha hb))
    have hint2 : ∀ z : Plane,
        IntervalIntegrable (fun σ : ℝ => Cyl.partialEta (Cyl.partialEta (F σ)) z) volume a b := by
      intro z
      have hc : ContinuousOn (fun σ : ℝ => Cyl.partialEta (Cyl.partialEta (F σ)) z) (Icc 0 T) :=
        pbTA_cont_slice (K := fun σ w => Cyl.partialEta (Cyl.partialEta (F σ)) w) hGEE z
      exact ContinuousOn.intervalIntegrable (hc.mono (uIcc_subset_Icc ha hb))
    -- the first partials of `P` are `C¹`
    have hc1 : ContDiff ℝ 1 (fun z : Plane => Cyl.partialQ (fun w => ∫ σ in a..b, F σ w) z) := by
      rw [hPQ]
      exact hQC1
    have hc2 : ContDiff ℝ 1 (fun z : Plane => Cyl.partialEta (fun w => ∫ σ in a..b, F σ w) z) := by
      rw [hPE]
      exact hEC1
    have hdiffP : Differentiable ℝ (fun z : Plane => ∫ σ in a..b, F σ z) :=
      hPC1.differentiable (by simp)
    have hfd : ∀ z v : Plane,
        fderiv ℝ (fun w : Plane => ∫ σ in a..b, F σ w) z v =
          Cyl.partialQ (fun w : Plane => ∫ σ in a..b, F σ w) z * v.1 +
            Cyl.partialEta (fun w : Plane => ∫ σ in a..b, F σ w) z * v.2 :=
      fun z v => pbTA_fderiv_apply hdiffP z v
    refine ⟨?_, hPq, hPe, ?_⟩
    · -- `P` is `C²`: its derivative is `C¹` since its partials are
      rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv_apply]
      refine ⟨hdiffP, fun h => absurd h (by simp), fun v => ?_⟩
      simp only [hfd]
      exact (hc1.mul contDiff_const).add (hc2.mul contDiff_const)
    · intro z
      show Cyl.partialQ (Cyl.partialQ (fun w => ∫ σ in a..b, F σ w)) z +
          Cyl.partialEta (Cyl.partialEta (fun w => ∫ σ in a..b, F σ w)) z =
        ∫ σ in a..b, (Cyl.partialQ (Cyl.partialQ (F σ)) z +
          Cyl.partialEta (Cyl.partialEta (F σ)) z)
      rw [hPQQ z, hPEE z, intervalIntegral.integral_add (hint1 z) (hint2 z)]

end UnforcedLeray.Short.PartI
