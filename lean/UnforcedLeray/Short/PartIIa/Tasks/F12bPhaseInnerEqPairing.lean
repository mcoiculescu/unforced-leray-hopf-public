import UnforcedLeray.Short.PartIIa.Sub.F12

/-!


Proves `PhaseInnerEqPairing` (defined in `Sub/F12.lean`): the coordinatewise conjugate of a phase
test is a phase test, and the Hilbert inner product of `Y_2` against `testElem Φ` equals the phase
pairing against the conjugate test, `⟨Φ, g⟩_{Y_2} = phasePair P 2 (conj Φ) g`.

Source of record: `the November 2 reference manuscript`, lines 1546-1586 (cited by
`Sub/F12.lean`; the separation step of the completion uses this identity).

Proof outline.
1. `conjF Φ` is smooth (componentwise `star ∘ Φ_k`, then `PiLp.contDiff_toLp`), periodic and
   compactly supported in `y`, since conjugation commutes with the evaluation at `(τ, y)`.
2. Both sides are integrals over the phase circle. Each `Y_2`-element `testElem` agrees
   haar-a.e. with its continuous slice map `circleSlice`, and the slices are `L²` elements whose
   coercions are a.e. equal to `Φ(t, ·)`.
3. Pointwise on the circle, `L²`-inner against `g τ` is the spatial integral of `conj(Φ_τ) · g_τ`
   by `L2.inner_def`, and this matches `innerPair` applied to the conjugate slice by
   `innerPair_apply` and `inner_eq_dotL_conj`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Coordinatewise conjugation of a phase test is a phase test. -/
theorem conjF_isPhaseTest {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (conjF Φ) where
  smooth := by
    have hk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun p : ℝ × Space => star (Φ p k)) := by
      intro k
      have hc : ContDiff ℝ ∞ (fun v : CVec3 => v k) := contDiff_piLp_apply 2
      have h := Complex.conjCLE.contDiff.comp (hc.comp hΦ.smooth)
      convert h using 1
      funext p
      simp
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × Space =>
        (WithLp.toLp 2 (fun k => star (Φ p k)) : CVec3)) :=
      PiLp.contDiff_toLp.comp (contDiff_pi.2 hk)
    exact h1
  periodic τ y := by
    simp only [conjF, hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by
      simp [conjF, hR τ y hy]
      rfl⟩

/-- Hilbert inner product on `ℂ³` against the bilinear dot product of the conjugate vector. -/
theorem inner_eq_dotL_conj (v w : CVec3) :
    inner ℂ v w = dotL (WithLp.toLp 2 fun k => star (v k)) w := by
  rw [dotL_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

/-- **Task `PartII-a:F12/2`**: the conjugate of a phase test is a phase test, and the Hilbert inner
product of `Y_2` against `testElem Φ` is the phase pairing against the conjugate test. -/
theorem phaseInnerEqPairing : PhaseInnerEqPairing := by
  unfold PhaseInnerEqPairing
  intro P hP Φ hΦ
  have hΨ : IsPhaseTest P (conjF Φ) := conjF_isPhaseTest hΦ
  refine ⟨hΨ, fun g => ?_⟩
  have hs : IsSliceTest P 2 Φ := hΦ.isSliceTest 2
  have hsΨ : IsSliceTest P (conjExp 2) (conjF Φ) := hΨ.isSliceTest (conjExp 2)
  -- `Y_2`-elements agree haar-a.e. with their continuous slice maps
  have hae1 : ⇑(testElem P 2 Φ) =ᵐ[AddCircle.haarAddCircle (T := P)] ⇑(circleSlice hs) := by
    rw [testElem_of hs]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space)) (p := 2)
      (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  have hae2 : ⇑(testElem P (conjExp 2) (conjF Φ)) =ᵐ[AddCircle.haarAddCircle (T := P)]
      ⇑(circleSlice hsΨ) := by
    rw [testElem_of hsΨ]
    exact ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp 2) (volume : Measure Space))
      (p := conjExp 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hsΨ)
  -- at every point of the circle, the conjugate slice is the conjugate of the slice
  have key : ∀ τ : AddCircle P, ∀ᵐ y ∂(volume : Measure Space),
      (circleSlice hsΨ τ) y = WithLp.toLp 2 (fun k => star ((circleSlice hs τ) y k)) := by
    intro τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      simp only [circleSlice_coe, sliceMap]
      filter_upwards [MemLp.coeFn_toLp (hsΨ.2.memLp t), MemLp.coeFn_toLp (hs.2.memLp t)]
        with y h1 h2
      rw [h1, h2]
      rfl
  -- the pointwise identity on the circle
  have hpt : ∀ τ : AddCircle P,
      inner ℂ (circleSlice hs τ) (g τ) = innerPair 2 (circleSlice hsΨ τ) (g τ) := by
    intro τ
    rw [L2.inner_def, innerPair_apply]
    refine integral_congr_ae ?_
    filter_upwards [key τ] with y hy
    rw [hy, inner_eq_dotL_conj]
  have hL : inner ℂ (testElem P 2 Φ) g =
      ∫ τ, inner ℂ (circleSlice hs τ) (g τ) ∂AddCircle.haarAddCircle (T := P) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hae1] with τ hτ
    rw [hτ]
  have hR : phasePair P 2 (conjF Φ) g =
      ∫ τ, innerPair 2 (circleSlice hsΨ τ) (g τ) ∂AddCircle.haarAddCircle (T := P) := by
    rw [phasePair, phasePairing_apply]
    refine integral_congr_ae ?_
    filter_upwards [hae2] with τ hτ
    rw [hτ]
  rw [hL, hR]
  exact integral_congr_ae (ae_of_all _ hpt)

end UnforcedLeray.Short.PartIIa
