import UnforcedLeray.Short.PartI.Sub.L_T02_1_4_6_4_5_2

/-!
# Part I, task `PartI:T02/1/4/6/4/5/2/3`: uniform `L²(cell)` bound of the first partials

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `AdvLipGradBound`.  By `IsSpatialRepOn.represents` at the words `iQ`, `iEta`, the first
partials of `w r` are a.e. equal to `vecH3CellDerivCLM iQ (u r)` and `vecH3CellDerivCLM iEta (u r)`,
whose `L²` norms are bounded by the operator norms times `‖u r‖`.  The norm of `u` is bounded on
`[0,T]` by compactness and continuity.
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
theorem advGradBound_eLpNorm_eq {c : ℝ} (x : Cyl.L2v c) :
    eLpNorm (⇑x) 2 (Cyl.cellμ c) = ENNReal.ofReal ‖x‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top x)]

/-- The `∂_q` derivative of the representative agrees a.e. with `vecH3CellDerivCLM iQ`. -/
theorem advGradBound_partialQ_ae {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
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
theorem advGradBound_partialEta_ae {c T : ℝ} {u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)}
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

/-- One `L²` bound: a bounded linear image of a vector of norm `≤ M`. -/
theorem advGradBound_le {c : ℝ} (L : VectorH3 c →L[ℝ] Cyl.L2v c) (x : VectorH3 c) {M K : ℝ}
    (hx : ‖x‖ ≤ M) (hK : ‖L‖ * M ≤ K) :
    eLpNorm (⇑(L x)) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal K := by
  rw [advGradBound_eLpNorm_eq]
  exact ENNReal.ofReal_le_ofReal ((L.le_opNorm x).trans
    ((mul_le_mul_of_nonneg_left hx (norm_nonneg L)).trans hK))

theorem advLipGradBound_proof : UnforcedLeray.Short.PartI.AdvLipGradBound := by
  intro ν c T hν hc hc1 hT u hu w hw
  have : CompactSpace (Icc (0 : ℝ) T) := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨B, hB⟩ := (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) T)))
    |>.exists_bound_of_continuousOn u.continuous.continuousOn
  have hB' : ∀ x : Icc (0 : ℝ) T, ‖u x‖ ≤ max B 0 := fun x =>
    (hB x (mem_univ x)).trans (le_max_left _ _)
  have hQ0 := norm_nonneg (vecH3CellDerivCLM (c := c) (Cyl.iQ (k := 2)))
  have hE0 := norm_nonneg (vecH3CellDerivCLM (c := c) (Cyl.iEta (k := 2)))
  refine ⟨(‖vecH3CellDerivCLM (c := c) (Cyl.iQ (k := 2))‖ +
      ‖vecH3CellDerivCLM (c := c) (Cyl.iEta (k := 2))‖) * max B 0,
    mul_nonneg (add_nonneg hQ0 hE0) (le_max_right _ _), ?_⟩
  intro r hr
  constructor
  · rw [eLpNorm_congr_ae (advGradBound_partialQ_ae hw hr).symm]
    refine advGradBound_le (vecH3CellDerivCLM (Cyl.iQ (k := 2))) (u ⟨r, hr⟩) (hB' _) ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE0) (le_max_right _ _)
  · rw [eLpNorm_congr_ae (advGradBound_partialEta_ae hw hr).symm]
    refine advGradBound_le (vecH3CellDerivCLM (Cyl.iEta (k := 2))) (u ⟨r, hr⟩) (hB' _) ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hQ0) (le_max_right _ _)

end UnforcedLeray.Short.PartI
