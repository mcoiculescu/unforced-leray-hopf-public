import UnforcedLeray.Short.PartI.Sub.L_T02_1_4_6_4_5_2

/-!
# Part I, task `PartI:T02/1/4/6/4/5/2/4`: `L²(cell)` Lipschitz bound of the first partials

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `AdvLipGradDiff`.  The a.e. identification of `∂_q (w r) - ∂_q (w s)` with
`vecH3CellDerivCLM iQ (u r - u s)` (linearity of the operator) and the operator-norm bound give the
claim with `K = max ‖vecH3CellDerivCLM iQ‖ ‖vecH3CellDerivCLM iEta‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The `L²(cell)` norm of an element of `L2v c` is the ENNReal lift of its norm. -/
theorem advGradDiff_eLpNorm_eq {c : ℝ} (x : Cyl.L2v c) :
    eLpNorm (⇑x) 2 (Cyl.cellμ c) = ENNReal.ofReal ‖x‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top x)]

/-- The `∂_q` derivative of the representative agrees a.e. with `vecH3CellDerivCLM iQ`. -/
theorem advGradDiff_partialQ_ae {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    (vecH3CellDerivCLM (Cyl.iQ (k := 2)) (u ⟨r, hr⟩) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Cyl.partialQ (w r) := by
  have hd : Differentiable ℝ (w r) := (hw.smooth r hr).differentiable (by simp)
  have hrep : (vecH3CellDerivCLM (Cyl.iQ (k := 2)) (u ⟨r, hr⟩) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Sob.iterD [((1 : ℝ), (0 : ℝ))] (w r) := by
    have h := hw.represents ⟨r, hr⟩ (Cyl.iQ (k := 2))
    rwa [Cyl.word_iQ c (k := 2)] at h
  have hfun : Sob.iterD [((1 : ℝ), (0 : ℝ))] (w r) = Cyl.partialQ (w r) :=
    funext fun z => by
      rw [Cyl.partialQ_eq_fderiv hd z]
      rfl
  rw [hfun] at hrep
  exact hrep

/-- The `∂_η` derivative of the representative agrees a.e. with `vecH3CellDerivCLM iEta`. -/
theorem advGradDiff_partialEta_ae {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
    {w : ℝ → Plane → Vec} (hw : IsSpatialRepOn c T u w) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    (vecH3CellDerivCLM (Cyl.iEta (k := 2)) (u ⟨r, hr⟩) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Cyl.partialEta (w r) := by
  have hd : Differentiable ℝ (w r) := (hw.smooth r hr).differentiable (by simp)
  have hrep : (vecH3CellDerivCLM (Cyl.iEta (k := 2)) (u ⟨r, hr⟩) : Plane → Vec) =ᵐ[Cyl.cellμ c]
      Sob.iterD [((0 : ℝ), (1 : ℝ))] (w r) := by
    have h := hw.represents ⟨r, hr⟩ (Cyl.iEta (k := 2))
    rwa [Cyl.word_iEta c (k := 2)] at h
  have hfun : Sob.iterD [((0 : ℝ), (1 : ℝ))] (w r) = Cyl.partialEta (w r) :=
    funext fun z => by
      rw [Cyl.partialEta_eq_fderiv hd z]
      rfl
  rw [hfun] at hrep
  exact hrep

/-- The difference of two first partials is the image of the difference of the `H³` points. -/
theorem advGradDiff_le {c : ℝ} (L : VectorH3 c →L[ℝ] Cyl.L2v c) (x y : VectorH3 c) {K : ℝ}
    (hK : ‖L‖ ≤ K) (hK0 : 0 ≤ K) :
    eLpNorm (⇑(L (x - y))) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := by
  rw [advGradDiff_eLpNorm_eq, ← ENNReal.ofReal_mul hK0]
  refine ENNReal.ofReal_le_ofReal ?_
  exact (L.le_opNorm (x - y)).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

theorem advLipGradDiff_proof : UnforcedLeray.Short.PartI.AdvLipGradDiff := by
  intro ν c T hν hc hc1 hT u hu w hw
  have hQ0 := norm_nonneg (vecH3CellDerivCLM (c := c) (Cyl.iQ (k := 2)))
  have hE0 := norm_nonneg (vecH3CellDerivCLM (c := c) (Cyl.iEta (k := 2)))
  refine ⟨max ‖vecH3CellDerivCLM (c := c) (Cyl.iQ (k := 2))‖
      ‖vecH3CellDerivCLM (c := c) (Cyl.iEta (k := 2))‖,
    le_max_of_le_left hQ0, ?_⟩
  intro r hr s hs
  constructor
  · -- the first component
    have hae : (fun z => Cyl.partialQ (w r) z - Cyl.partialQ (w s) z) =ᵐ[Cyl.cellμ c]
        ⇑(vecH3CellDerivCLM (Cyl.iQ (k := 2)) (u ⟨r, hr⟩ - u ⟨s, hs⟩)) := by
      filter_upwards [advGradDiff_partialQ_ae hw hr, advGradDiff_partialQ_ae hw hs,
        Lp.coeFn_sub (vecH3CellDerivCLM (Cyl.iQ (k := 2)) (u ⟨r, hr⟩))
          (vecH3CellDerivCLM (Cyl.iQ (k := 2)) (u ⟨s, hs⟩))] with z h1 h2 h3
      rw [map_sub, h3, Pi.sub_apply, h1, h2]
    rw [eLpNorm_congr_ae hae]
    exact advGradDiff_le (vecH3CellDerivCLM (Cyl.iQ (k := 2))) (u ⟨r, hr⟩) (u ⟨s, hs⟩) (le_max_left _ _) (le_max_of_le_left hQ0)
  · have hae : (fun z => Cyl.partialEta (w r) z - Cyl.partialEta (w s) z) =ᵐ[Cyl.cellμ c]
        ⇑(vecH3CellDerivCLM (Cyl.iEta (k := 2)) (u ⟨r, hr⟩ - u ⟨s, hs⟩)) := by
      filter_upwards [advGradDiff_partialEta_ae hw hr, advGradDiff_partialEta_ae hw hs,
        Lp.coeFn_sub (vecH3CellDerivCLM (Cyl.iEta (k := 2)) (u ⟨r, hr⟩))
          (vecH3CellDerivCLM (Cyl.iEta (k := 2)) (u ⟨s, hs⟩))] with z h1 h2 h3
      rw [map_sub, h3, Pi.sub_apply, h1, h2]
    rw [eLpNorm_congr_ae hae]
    exact advGradDiff_le (vecH3CellDerivCLM (Cyl.iEta (k := 2))) (u ⟨r, hr⟩) (u ⟨s, hs⟩) (le_max_right _ _) (le_max_of_le_left hQ0)

end UnforcedLeray.Short.PartI
