import UnforcedLeray.Lib.LerayC.Phase
import UnforcedLeray.Lib.PhaseSpace.Graph

/-!
# The Leray projection on `Y_p` takes values in the solenoidal fields (INF01 T17)


§5, Level 2 (with T15 `lerayLp_isSolenoidal`); block 3C LERAY-C; decision D2 (distributional
identities on `Y_q` are pairings against smooth `P`-periodic tests, `PhaseSpace.IsPhaseSolenoidal`).

Manuscript: unit B0414 (`paper/main.tex` lines 7336–7344: `P_σ` is the projection onto the
solenoidal fields, `Y_{q,σ}`), unit B0429 (lines 3591–3621: `P` maps `Y_p` into `Y_{p,σ}` and
"hence preserves the graph"), unit B0439 (lines 7364–7387: `R_μ = (μ+L_0)^{-1}P_σ` is defined
on `Y_q` with values in the solenoidal graph).

* `integral_dotL_gradT_lerayC`: for a scalar phase test `φ` (complex valued), every phase `t`
  and `G ∈ L^p(R³;ℂ³)`, `∫ ∇_yφ(t,y) · (𝔓G)(y) dy = 0` (bilinear dot product, no conjugation);
  real and imaginary parts reduce to `lerayLp_isSolenoidal` (T15);
* `lerayY_isPhaseSolenoidal`: `div (𝔓f) = 0` in the sense of `PhaseSpace.IsPhaseSolenoidal`, for
  every `f ∈ Y_p`, `1 < p < ∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.RieszLp

open UnforcedLeray.PhaseSpace (CVec3 Yq)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {P : ℝ} [Fact (0 < P)]

theorem gradT_apply_coord (φ : ℝ × Space → ℂ) (z : ℝ × Space) (i : Fin 3) :
    PhaseSpace.gradT φ z i = PhaseSpace.dy i φ z := by
  simp [PhaseSpace.gradT, Pi.single_apply]

theorem complex_mul_expand (α β γ δ : ℝ) :
    ((α : ℂ) + (β : ℂ) * Complex.I) * ((γ : ℂ) + (δ : ℂ) * Complex.I) =
      ((α * γ - β * δ : ℝ) : ℂ) + Complex.I * ((α * δ + β * γ : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

/-- The integrand of `IsSolenoidal`: `∑ᵢ vᵢ ∂ᵢc`. -/
def solPair (v : SpatialField) (c : Space → ℝ) (y : Space) : ℝ :=
  ∑ i : Fin 3, (v y) i * spatialTestDerivative i c y

/-- **Slice identity.** For a complex scalar phase test `φ`, a phase `t` and
`G ∈ L^p(R³;ℂ³)`, `1 < p < ∞`: `∫ ∇_yφ(t,y) · (𝔓G)(y) dy = 0`. -/
theorem integral_dotL_gradT_lerayC (hp1 : 1 < p) (hp : p ≠ ⊤) {φ : ℝ × Space → ℂ}
    (hφ : PhaseSpace.IsPhaseTest P φ) (t : ℝ) (G : Lp CVec3 p (volume : Measure Space)) :
    ∫ y, PhaseSpace.dotL (PhaseSpace.gradT φ (t, y)) (lerayC p hp1 hp G y) = 0 := by
  set ψ : Space → ℂ := fun y => φ (t, y) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψc : HasCompactSupport ψ := hφ.hasCompactSupport_slice t
  set a : Space → ℝ := fun y => (ψ y).re with hadef
  set b : Space → ℝ := fun y => (ψ y).im with hbdef
  have ha : IsSpatialTest a :=
    ⟨Complex.reCLM.contDiff.comp hψs, hψc.comp_left Complex.zero_re⟩
  have hb : IsSpatialTest b :=
    ⟨Complex.imCLM.contDiff.comp hψs, hψc.comp_left Complex.zero_im⟩
  have hd : ∀ (y : Space) (i : Fin 3), PhaseSpace.dy i φ (t, y) =
      (spatialTestDerivative i a y : ℂ) + (spatialTestDerivative i b y : ℂ) * Complex.I := by
    intro y i
    have hφd : HasFDerivAt φ (fderiv ℝ φ (t, y)) (t, y) :=
      (hφ.smooth.differentiable (by simp) (t, y)).hasFDerivAt
    have hψd : HasFDerivAt ψ ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
      hφd.comp y (hasFDerivAt_prodMk_right t y)
    have hra : HasFDerivAt a (Complex.reCLM.comp
        ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space))) y :=
      Complex.reCLM.hasFDerivAt.comp y hψd
    have hrb : HasFDerivAt b (Complex.imCLM.comp
        ((fderiv ℝ φ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space))) y :=
      Complex.imCLM.hasFDerivAt.comp y hψd
    simp only [spatialTestDerivative, PhaseSpace.dy, hra.fderiv, hrb.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, Complex.reCLM_apply,
      Complex.imCLM_apply]
    exact (Complex.re_add_im _).symm
  set u : SpatialField := (lerayLp p hp1 hp (reV.compLpL p volume G) : SpatialField) with hudef
  set w : SpatialField := (lerayLp p hp1 hp (imV.compLpL p volume G) : SpatialField) with hwdef
  have hu : IsSolenoidal u := lerayLp_isSolenoidal hp1 hp _
  have hw : IsSolenoidal w := lerayLp_isSolenoidal hp1 hp _
  have hpt : (fun y => PhaseSpace.dotL (PhaseSpace.gradT φ (t, y)) (lerayC p hp1 hp G y))
      =ᵐ[volume] fun y => ((solPair u a y - solPair w b y : ℝ) : ℂ) +
        Complex.I * ((solPair w a y + solPair u b y : ℝ) : ℂ) := by
    filter_upwards [coeFn_lerayC hp1 hp G] with y hy
    rw [hy, PhaseSpace.dotL_apply]
    have e : ∀ i : Fin 3, PhaseSpace.gradT φ (t, y) i *
        (ofReV (u y) + ofImV (w y)) i =
        (((spatialTestDerivative i a y * u y i - spatialTestDerivative i b y * w y i : ℝ) : ℂ) +
          Complex.I * ((spatialTestDerivative i a y * w y i +
            spatialTestDerivative i b y * u y i : ℝ) : ℂ)) := by
      intro i
      rw [gradT_apply_coord, hd y i, PiLp.add_apply, ofReV_apply, ofImV_apply,
        complex_mul_expand]
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [solPair]
    push_cast
    congr 1
    · rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  have i1 := hu.integrable a ha
  have i2 := hw.integrable b hb
  have i3 := hw.integrable a ha
  have i4 := hu.integrable b hb
  have z1 := hu.identity a ha
  have z2 := hw.identity b hb
  have z3 := hw.identity a ha
  have z4 := hu.identity b hb
  rw [integral_congr_ae hpt, integral_add ((i1.sub i2).ofReal) (((i3.add i4).ofReal).const_mul _),
    integral_complex_ofReal, MeasureTheory.integral_const_mul, integral_complex_ofReal]
  have e1 : ∫ y, (solPair u a y - solPair w b y) = 0 := by
    simp only [solPair]
    rw [integral_sub i1 i2, z1, z2, sub_zero]
  have e2 : ∫ y, (solPair w a y + solPair u b y) = 0 := by
    simp only [solPair]
    rw [integral_add i3 i4, z3, z4, add_zero]
  rw [e1, e2]
  simp

/-- **INF01 T17 (solenoidal values).** For `1 < p < ∞` and every `f ∈ Y_p`, the Leray projection
`𝔓f` is distributionally solenoidal on the phase space (`PhaseSpace.IsPhaseSolenoidal`;
B0414, `paper/main.tex` lines 7336–7344; B0429, lines 3591–3621). -/
theorem lerayY_isPhaseSolenoidal (hp1 : 1 < p) (hp : p ≠ ⊤) (f : Yq P p) :
    PhaseSpace.IsPhaseSolenoidal (lerayY P p hp1 hp f) := by
  intro φ hφ
  have hs := hφ.gradT.isSliceTest (PhaseSpace.conjExp p)
  rw [PhaseSpace.phasePair, PhaseSpace.phasePairing_apply, PhaseSpace.testElem_of hs]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [ContinuousMap.coeFn_toLp
      (E := Lp CVec3 (PhaseSpace.conjExp p) (volume : Measure Space))
      (p := PhaseSpace.conjExp p) (𝕜 := ℂ) AddCircle.haarAddCircle (PhaseSpace.circleSlice hs),
    coeFn_lerayY hp1 hp f] with τ h1 h2
  rw [h1, h2]
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective τ
  rw [PhaseSpace.circleSlice_coe, PhaseSpace.innerPair_apply]
  have h3 : (fun y => PhaseSpace.dotL ((PhaseSpace.sliceMap hs.2 t : Space → CVec3) y)
      (lerayC p hp1 hp (f (t : AddCircle P)) y)) =ᵐ[volume]
      fun y => PhaseSpace.dotL (PhaseSpace.gradT φ (t, y))
        (lerayC p hp1 hp (f (t : AddCircle P)) y) := by
    filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
    simp only [PhaseSpace.sliceMap]
    rw [hy]
  rw [integral_congr_ae h3]
  exact integral_dotL_gradT_lerayC hp1 hp hφ t _

end UnforcedLeray.RieszLp
