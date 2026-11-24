import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1_1

/-!
# Part II-a, task `PartII-a:F09/1/3/1/1/3`: Re/Im splitting of the forward slice remainder

Source `the November 2 reference manuscript`, lines 1403-1413, 1426-1428.
Proves `FwdSliceDecomp`: a.e. in `y`, the slice remainder
`S_ν(s)Φ_t - Φ_t + s(L₀Φ_t - ∂_τΦ_t)` equals `ofReV (fwdXk reV) + ofImV (fwdXk imV)`.
Mirror of `SliceCalc.decomp_adjC` (Tasks/F02BodyResolventEquation/SliceTaylor/Bounds.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Componentwise identity `K(L₀Φ - ∂_τΦ)(t,y) = -K(G Φ_t)(y)`, the forward generator on a slice. -/
theorem fwdDecomp_K (ν : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (K : CVec3 →L[ℝ] Space) (t : ℝ) (y : Space) :
    K ((L0 ν Φ) (t, y) - (dτ Φ) (t, y)) = -fwdGen ν (fun z => K (Φ (t, z))) y := by
  have e : (L0 ν Φ) (t, y) - (dτ Φ) (t, y) =
      -((1 / 2 : ℝ) • radialT Φ (t, y)) - ν • lapT Φ (t, y) - (1 / 2 : ℝ) • Φ (t, y) := by
    simp only [L0, T0]
    module
  have hL := SliceCalc.vecLaplacian_clm_slice hΦ K t y
  have hR := SliceCalc.fderiv_clm_slice_self (hΦ.differentiable (by simp)) K t y
  rw [e]
  simp only [fwdGen, hL, hR, map_sub, map_neg, map_smul]
  module

/-- Pointwise forward slice decomposition, before taking Re/Im parts of the Lp classes. -/
theorem fwd_pointwise (ν s t : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (y : Space) :
    ofReV (fwdXk ν s reV t Φ y) + ofImV (fwdXk ν s imV t Φ y) =
      ofReV (AncientLocalization.freeEvolution ν s (fun z => reV (Φ (t, z))) y) +
        ofImV (AncientLocalization.freeEvolution ν s (fun z => imV (Φ (t, z))) y) -
        Φ (t, y) + (s : ℂ) • ((L0 ν Φ) (t, y) - (dτ Φ) (t, y)) := by
  have hw : ofReV (fwdGen ν (fun w => reV (Φ (t, w))) y) +
      ofImV (fwdGen ν (fun w => imV (Φ (t, w))) y) =
        -((L0 ν Φ) (t, y) - (dτ Φ) (t, y)) := by
    have h := ofReV_reV_add_ofImV_imV ((L0 ν Φ) (t, y) - (dτ Φ) (t, y))
    rw [fwdDecomp_K ν hΦ reV t y, fwdDecomp_K ν hΦ imV t y, map_neg, map_neg] at h
    rw [← h]
    abel
  have e2 := SliceCalc.alg_decomp (AncientLocalization.freeEvolution ν s (fun z => reV (Φ (t, z))) y)
    (AncientLocalization.freeEvolution ν s (fun z => imV (Φ (t, z))) y)
    (reV (Φ (t, y))) (imV (Φ (t, y)))
    (fwdGen ν (fun w => reV (Φ (t, w))) y) (fwdGen ν (fun w => imV (Φ (t, w))) y) s
  rw [ofReV_reV_add_ofImV_imV, hw] at e2
  unfold fwdXk
  rw [← e2, smul_neg]
  abel

/-- **Re/Im splitting of the forward slice remainder** (task `PartII-a:F09/1/3/1/1/3`). -/
theorem fwdSliceDecomp : FwdSliceDecomp := by
  intro p _ hp P _ ν Φ hΦ t s
  have hF : ⇑(sliceMap (hΦ.isSliceTest p).2 t) =ᵐ[volume] fun y => Φ (t, y) := by
    unfold sliceMap
    exact MemLp.coeFn_toLp _
  have hG1 : ⇑(sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t) =ᵐ[volume]
      fun y => (L0 ν Φ) (t, y) := by
    unfold sliceMap
    exact MemLp.coeFn_toLp _
  have hG2 : ⇑(sliceMap (hΦ.dτ.isSliceTest p).2 t) =ᵐ[volume] fun y => (dτ Φ) (t, y) := by
    unfold sliceMap
    exact MemLp.coeFn_toLp _
  have hR : ⇑(reV.compLpL p volume (sliceMap (hΦ.isSliceTest p).2 t)) =ᵐ[volume]
      fun z => reV (Φ (t, z)) := by
    filter_upwards [reV.coeFn_compLpL (μ := volume) (p := p) (sliceMap (hΦ.isSliceTest p).2 t),
      hF] with z h1 h2
    rw [h1, h2]
  have hI : ⇑(imV.compLpL p volume (sliceMap (hΦ.isSliceTest p).2 t)) =ᵐ[volume]
      fun z => imV (Φ (t, z)) := by
    filter_upwards [imV.coeFn_compLpL (μ := volume) (p := p) (sliceMap (hΦ.isSliceTest p).2 t),
      hF] with z h1 h2
    rw [h1, h2]
  have hA1 : ∀ᵐ y ∂(volume : Measure Space),
      ofReV (AncientLocalization.freeEvolution ν s
        (⇑(reV.compLpL p volume (sliceMap (hΦ.isSliceTest p).2 t))) y) =
      ofReV (AncientLocalization.freeEvolution ν s (fun z => reV (Φ (t, z))) y) := by
    filter_upwards [UnforcedLeray.B0418.freeEvolution_congr_ae hR ν s] with y hy
    rw [hy]
  have hA2 : ∀ᵐ y ∂(volume : Measure Space),
      ofImV (AncientLocalization.freeEvolution ν s
        (⇑(imV.compLpL p volume (sliceMap (hΦ.isSliceTest p).2 t))) y) =
      ofImV (AncientLocalization.freeEvolution ν s (fun z => imV (Φ (t, z))) y) := by
    filter_upwards [UnforcedLeray.B0418.freeEvolution_congr_ae hI ν s] with y hy
    rw [hy]
  filter_upwards [UnforcedLeray.B0421.coeFn_freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 t),
    hA1, hA2, hF, hG1, hG2,
    Lp.coeFn_add (UnforcedLeray.B0421.freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 t) -
        sliceMap (hΦ.isSliceTest p).2 t)
      ((s : ℂ) • (sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t -
        sliceMap (hΦ.dτ.isSliceTest p).2 t)),
    Lp.coeFn_sub (UnforcedLeray.B0421.freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 t))
      (sliceMap (hΦ.isSliceTest p).2 t),
    Lp.coeFn_smul (s : ℂ) (sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t -
        sliceMap (hΦ.dτ.isSliceTest p).2 t),
    Lp.coeFn_sub (sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t)
      (sliceMap (hΦ.dτ.isSliceTest p).2 t)]
    with y h0 hA1y hA2y hFy hG1y hG2y e1 e2 e3 e4
  rw [e1, Pi.add_apply, e2, Pi.sub_apply, e3, Pi.smul_apply, e4, Pi.sub_apply, h0, hFy, hG1y,
    hG2y, hA1y, hA2y]
  exact (fwd_pointwise ν s t hΦ.smooth y).symm

end UnforcedLeray.Short.PartIIa
