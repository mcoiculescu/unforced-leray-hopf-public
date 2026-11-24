import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.Lib.LerayC.Complex

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

def realSliceProjection :
    Lp CVec3 q (volume : Measure Space) →L[ℝ]
      Lp CVec3 q (volume : Measure Space) :=
  (ofReV.compLpL q volume).comp (reV.compLpL q volume)

def realPhaseProjection : Yq P q →L[ℝ] Yq P q :=
  (realSliceProjection (q := q)).compLpL q AddCircle.haarAddCircle

theorem realSliceProjection_coe_ae
    (f : Lp CVec3 q (volume : Measure Space)) :
    (realSliceProjection f : Space → CVec3) =ᵐ[volume]
      fun y => ofReV (reV (f y)) := by
  exact (ofReV.coeFn_compLpL (μ := volume) (p := q) (reV.compLpL q volume f)).trans
    ((reV.coeFn_compLpL (μ := volume) (p := q) f).mono fun y hy => by
      simpa using congrArg ofReV hy)

theorem realPhaseProjection_coe_ae (w : Yq P q) :
    (realPhaseProjection w : AddCircle P → Lp CVec3 q (volume : Measure Space))
      =ᵐ[AddCircle.haarAddCircle]
      fun τ => realSliceProjection (w τ) := by
  exact (realSliceProjection (q := q)).coeFn_compLpL w

theorem realC_eq_ofReV : UnforcedLeray.B0412.realC = ofReV := by
  funext x
  ext i
  simp [UnforcedLeray.B0412.realC_apply, ofReV_apply]

/-- Every slice of a smooth real phase test, complexified into `ℂ³`, belongs to the real
subspace of the dual spatial `L^q` class. -/
theorem testElem_realSlice_of_phaseTest {φ : ℝ × Space → Space}
    (hφ : IsPhaseTest P φ) :
    ∀ᵐ τ ∂AddCircle.haarAddCircle (T := P),
      ∃ r : Lp Space (conjExp q) (volume : Measure Space),
        (testElem P (conjExp q) (fun x => UnforcedLeray.B0412.realC (φ x)) τ :
          Lp CVec3 (conjExp q) volume) = ofReV.compLpL (conjExp q) volume r := by
  have hH : IsSliceTest P (conjExp q) (fun x => ofReV (φ x)) :=
    (hφ.clm_comp ofReV).isSliceTest (conjExp q)
  have hHpair : (∀ τ y, ofReV (φ (τ + P, y)) = ofReV (φ (τ, y))) ∧
      SliceCont (conjExp q) (fun x => ofReV (φ x)) := by
    change _ ∧ SliceCont (conjExp q) (fun x => ofReV (φ x)) at hH
    exact hH
  have hHs : SliceCont (conjExp q) (fun x => ofReV (φ x)) := hHpair.2
  have hfun : (fun x => UnforcedLeray.B0412.realC (φ x)) = fun x => ofReV (φ x) := by
    funext x
    rw [realC_eq_ofReV]
  have hslice (τ : ℝ) :
      ofReV.compLpL (conjExp q) volume
        (reV.compLpL (conjExp q) volume (sliceMap hHs τ)) = sliceMap hHs τ := by
    apply Lp.ext
    filter_upwards [realSliceProjection_coe_ae (sliceMap hHs τ),
      MemLp.coeFn_toLp (hHs.memLp τ)] with y hproj hcoe
    change (sliceMap hHs τ : Space → CVec3) y = ofReV (φ (τ, y)) at hcoe
    change (realSliceProjection (sliceMap hHs τ) : Space → CVec3) y =
      (sliceMap hHs τ : Space → CVec3) y
    rw [hproj, hcoe]
    simp [reV_ofReV]
  have htest := testElem_of hH
  have hcoe := ContinuousMap.coeFn_toLp
    (E := Lp CVec3 (conjExp q) (volume : Measure Space))
    (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hH)
  filter_upwards [hcoe] with τ hτ
  induction τ using QuotientAddGroup.induction_on with
  | H t =>
    refine ⟨reV.compLpL (conjExp q) volume (sliceMap hHs t), ?_⟩
    rw [hfun, htest, hτ, circleSlice_coe]
    exact (hslice t).symm

theorem dotL_ofReV_realProjection (u : Space) (v : CVec3) :
    dotL (ofReV u) (ofReV (reV v)) = ((dotL (ofReV u) v).re : ℂ) := by
  simp [dotL_apply, ofReV_apply, reV_apply, Complex.mul_re]

theorem innerPair_realSliceProjection
    (r : Lp Space (conjExp q) (volume : Measure Space))
    (f : Lp CVec3 q (volume : Measure Space)) :
    innerPair q (ofReV.compLpL (conjExp q) volume r) (realSliceProjection f) =
      ((innerPair q (ofReV.compLpL (conjExp q) volume r) f).re : ℂ) := by
  let g : Lp CVec3 (conjExp q) (volume : Measure Space) :=
    ofReV.compLpL (conjExp q) volume r
  have hInt : Integrable (fun y : Space => dotL (g y) (f y)) volume := by
    exact memLp_one_iff_integrable.mp
      (dotL.memLp_of_bilin 1 (Lp.memLp g) (Lp.memLp f))
  have hAE : (fun y : Space => dotL (g y) (realSliceProjection f y)) =ᵐ[volume]
      fun y => ((dotL (g y) (f y)).re : ℂ) := by
    filter_upwards [ofReV.coeFn_compLpL (μ := volume) (p := conjExp q) r,
      realSliceProjection_coe_ae f] with y hg hp
    rw [hg, hp]
    exact dotL_ofReV_realProjection (r y) (f y)
  change innerPair q g (realSliceProjection f) = ((innerPair q g f).re : ℂ)
  rw [innerPair_apply, innerPair_apply]
  rw [integral_congr_ae hAE, integral_complex_ofReal]
  exact congrArg Complex.ofReal (integral_re hInt)

theorem phasePairing_realPhaseProjection_of_realSlices
    (ψ : Yq P (conjExp q)) (w : Yq P q)
    (hψ : ∀ᵐ τ ∂AddCircle.haarAddCircle (T := P),
      ∃ r : Lp Space (conjExp q) (volume : Measure Space),
        (ψ τ : Lp CVec3 (conjExp q) volume) =
          ofReV.compLpL (conjExp q) volume r) :
    phasePairing P q ψ (realPhaseProjection w) =
      ((phasePairing P q ψ w).re : ℂ) := by
  have hInt : Integrable (fun τ : AddCircle P => innerPair q (ψ τ) (w τ))
      AddCircle.haarAddCircle := by
    exact memLp_one_iff_integrable.mp
      ((innerPair q).memLp_of_bilin 1 (Lp.memLp ψ) (Lp.memLp w))
  have hAE : (fun τ : AddCircle P => innerPair q (ψ τ) (realPhaseProjection w τ))
      =ᵐ[AddCircle.haarAddCircle]
      fun τ => ((innerPair q (ψ τ) (w τ)).re : ℂ) := by
    filter_upwards [hψ, realPhaseProjection_coe_ae w] with τ hreal hproj
    obtain ⟨r, hr⟩ := hreal
    rw [hproj, hr]
    exact innerPair_realSliceProjection r (w τ)
  rw [phasePairing_apply, phasePairing_apply]
  rw [integral_congr_ae hAE, integral_complex_ofReal]
  exact congrArg Complex.ofReal (integral_re hInt)

theorem realSliceProjection_eq_of_ae_real
    (f : Lp CVec3 q (volume : Measure Space))
    (hf : ∀ᵐ y ∂volume, ofReV (reV (f y)) = f y) :
    realSliceProjection f = f := by
  apply Lp.ext
  exact (realSliceProjection_coe_ae f).trans hf

omit [Fact (1 ≤ q)] in
theorem realTest_testElem_slices {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ)
    (hreal : ∀ x, ofReV (reV (Φ x)) = Φ x) :
    ∀ᵐ τ ∂AddCircle.haarAddCircle (T := P),
      ∃ r : Lp Space (conjExp q) (volume : Measure Space),
        ((testElem P (conjExp q) Φ : Yq P (conjExp q)) τ) =
          ofReV.compLpL (conjExp q) volume r := by
  let hs := hΦ.isSliceTest (conjExp q)
  have hOuter := ContinuousMap.coeFn_toLp
    (E := Lp CVec3 (conjExp q) (volume : Measure Space))
    (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  rw [testElem_of hs]
  filter_upwards [hOuter] with τ hτ
  rw [hτ]
  refine ⟨reV.compLpL (conjExp q) volume (circleSlice hs τ), ?_⟩
  have hfix : realSliceProjection (circleSlice hs τ) = circleSlice hs τ := by
    apply realSliceProjection_eq_of_ae_real
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      rw [circleSlice_coe]
      filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
      dsimp only [sliceMap]
      rw [hy]
      exact hreal (t, y)
  exact hfix.symm

theorem phasePair_realPhaseProjection_of_realTest
    (φ : ℝ × Space → Space) (hφ : IsPhaseTest P φ) (w : Yq P q) :
    phasePair P q (fun x => ofReV (φ x)) (realPhaseProjection w) =
      ((phasePair P q (fun x => ofReV (φ x)) w).re : ℂ) := by
  have hΦ : IsPhaseTest P (fun x => ofReV (φ x)) := hφ.clm_comp ofReV
  have hreal : ∀ x, ofReV (reV (ofReV (φ x))) = ofReV (φ x) := by
    intro x
    rw [reV_ofReV]
  exact phasePairing_realPhaseProjection_of_realSlices
    (testElem P (conjExp q) (fun x => ofReV (φ x))) w
    (realTest_testElem_slices hΦ hreal)

theorem realPhaseProjection_eq_of_realSub (w : Yq P q)
    (hw : w ∈ UnforcedLeray.Cons.C03.Concrete.realSub P q) :
    w = realPhaseProjection w := by
  have hreal (φ : ℝ × Space → Space) (hφ : IsPhaseTest P φ) :
      phasePair P q (fun x => ofReV (φ x)) w =
        phasePair P q (fun x => ofReV (φ x)) (realPhaseProjection w) := by
    have hIm : (phasePair P q (fun x => ofReV (φ x)) w).im = 0 := by
      simpa only [← realC_eq_ofReV] using (mem_realSub P q).1 hw φ hφ
    have hproj := phasePair_realPhaseProjection_of_realTest φ hφ w
    calc
      phasePair P q (fun x => ofReV (φ x)) w =
          ((phasePair P q (fun x => ofReV (φ x)) w).re : ℂ) := by
            apply Complex.ext <;> simp [hIm]
      _ = phasePair P q (fun x => ofReV (φ x)) (realPhaseProjection w) := hproj.symm
  apply UnforcedLeray.B0411.eq_of_forall_phasePair
  intro Φ hΦ
  let φR : ℝ × Space → Space := fun x => reV (Φ x)
  let φI : ℝ × Space → Space := fun x => imV (Φ x)
  have hR : IsPhaseTest P φR := hΦ.clm_comp reV
  have hI : IsPhaseTest P φI := hΦ.clm_comp imV
  have hdecomp : Φ = (fun x => ofReV (φR x)) +
      Complex.I • (fun x => ofReV (φI x)) := by
    funext x
    have h := ofReV_reV_add_ofImV_imV (Φ x)
    simpa [φR, φI, Pi.add_apply, Pi.smul_apply, I_smul_ofReV] using h.symm
  rw [hdecomp]
  have hRc : IsPhaseTest P (fun x => ofReV (φR x)) := hR.clm_comp ofReV
  have hIc : IsPhaseTest P (fun x => ofReV (φI x)) := hI.clm_comp ofReV
  rw [phasePair_add hRc (hIc.const_smul Complex.I),
      phasePair_add hRc (hIc.const_smul Complex.I),
      phasePair_const_smul hIc, phasePair_const_smul hIc]
  rw [hreal φR hR, hreal φI hI]

#print axioms realSliceProjection_coe_ae
#print axioms realPhaseProjection_coe_ae
#print axioms dotL_ofReV_realProjection
#print axioms innerPair_realSliceProjection
#print axioms testElem_realSlice_of_phaseTest
#print axioms phasePairing_realPhaseProjection_of_realSlices
#print axioms realTest_testElem_slices
#print axioms phasePair_realPhaseProjection_of_realTest
#print axioms realPhaseProjection_eq_of_realSub

end UnforcedLeray.Cons.C03.Concrete
