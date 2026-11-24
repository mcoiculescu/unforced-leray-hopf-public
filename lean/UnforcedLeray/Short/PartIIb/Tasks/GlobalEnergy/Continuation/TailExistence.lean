import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.LinearGlue
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.BodySourceGlue
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.TailExistence.UnitStep

/-!
# `TailExistence` (`PartII-b:F7/2/1`): Meridional tail existence on `[T, ∞)` (`SP 2213–2217, 2289–2295`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2213–2217 (`short-bg:body-eq`) and lines 2289–2295 (`short-bg:global-energy`).

This module reduces `UnforcedLeray.Short.IIb.MeridionalTailExistence` unconditionally (`0 sorry`)
to the single real unit-interval 2D cylinder Oseen/Stokes `H¹_σ(C_c)` evolution step
`TailExistenceAux.RealCylUnitOseenStep`:
1. `toCell` periodic retraction and null-slice cleanup upgrading the initial datum `(u, uq, uη)`
   and body source `(g, gq, gη)` on `(T, ∞)` to everywhere-`p.c`-periodic `StronglyMeasurable`
   fields whose slices belong to `H¹_σ(C_c)` at **every** `s : ℝ`;
2. `ℂ = ℝ ⊕ i ℝ` splitting of `IsCylH1Slice` and `sliceH1Norm` into real and imaginary parts, and
   complex recombination of `IsTailMeridionalSolution` and `cylSliceH1` continuity;
3. `Nat.rec` inductive unit-step `[T + n, T + n + 1]` pasting on `[T, ∞)` via `⌊s - T⌋₊`, proving
   joint `StronglyMeasurable`, everywhere `p.c`-periodicity, `IsCylH1Slice` on every slice,
   two-sided `cylSliceH1` continuity across all unit seams `T + k`, compact-interval `sliceH1Norm`
   bounds, global `weak_q` / `weak_eta` / `solenoidal` via `TailPeriodizeAux.sliceWeakToJoint`, and
   smooth 1D bump partition-of-unity weak PDE seam gluing across `s = T + 1, …, T + N`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.TailExistenceAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.LinearBodySourceHelp

/-! ## 1. Real / complex slice and profile conversions -/

/-- Real part of a complex cylinder slice. -/
def reSlice (u : B0579.Plane → CMerid) : B0579.Plane → Fin 2 → ℝ :=
  fun y i => (u y i).re

/-- Imaginary part of a complex cylinder slice, realized as `reSlice ((-I) • u)`. -/
def imSlice (u : B0579.Plane → CMerid) : B0579.Plane → Fin 2 → ℝ :=
  reSlice (fun y => (-Complex.I) • u y)

/-- Real part of a complex profile. -/
def reProf (w : CProf) : Coord → Fin 2 → ℝ :=
  fun x i => (w x i).re

/-- Imaginary part of a complex profile, realized as `reProf ((-I) • w)`. -/
def imProf (w : CProf) : Coord → Fin 2 → ℝ :=
  reProf (fun x => (-Complex.I) • w x)

private lemma imSlice_apply (u : B0579.Plane → CMerid) (y : B0579.Plane) (i : Fin 2) :
    imSlice u y i = (u y i).im := by
  simp [imSlice, reSlice]

private lemma imProf_apply (w : CProf) (x : Coord) (i : Fin 2) :
    imProf w x i = (w x i).im := by
  simp [imProf, reProf]

private lemma ofRealSlice_re_im (u : B0579.Plane → CMerid) (y : B0579.Plane) :
    ofRealSlice (reSlice u) y + Complex.I • ofRealSlice (imSlice u) y = u y := by
  ext i
  simp only [ofRealSlice, reSlice, imSlice_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact Complex.ext (by simp) (by simp)

private lemma ofRealProf_re_im (w : CProf) (x : Coord) :
    ofRealProf (reProf w) x + Complex.I • ofRealProf (imProf w) x = w x := by
  ext i
  simp only [ofRealProf, reProf, imProf_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact Complex.ext (by simp) (by simp)

private lemma stronglyMeasurable_ofRealSlice {w : B0579.Plane → Fin 2 → ℝ}
    (hw : StronglyMeasurable w) : StronglyMeasurable (ofRealSlice w) := by
  have hm : Measurable (ofRealSlice w) := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    exact Complex.measurable_ofReal.comp (((continuous_apply i).comp_stronglyMeasurable hw).measurable)
  exact hm.stronglyMeasurable

private lemma stronglyMeasurable_ofRealProf {w : Coord → Fin 2 → ℝ}
    (hw : StronglyMeasurable w) : StronglyMeasurable (ofRealProf w) := by
  have hm : Measurable (ofRealProf w) := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    exact Complex.measurable_ofReal.comp (((continuous_apply i).comp_stronglyMeasurable hw).measurable)
  exact hm.stronglyMeasurable

private lemma stronglyMeasurable_reSlice {u : B0579.Plane → CMerid}
    (hu : StronglyMeasurable u) : StronglyMeasurable (reSlice u) := by
  refine (measurable_pi_lambda _ fun i => ?_).stronglyMeasurable
  exact Complex.continuous_re.measurable.comp
    (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hu).measurable)

private lemma stronglyMeasurable_imSlice {u : B0579.Plane → CMerid}
    (hu : StronglyMeasurable u) : StronglyMeasurable (imSlice u) :=
  stronglyMeasurable_reSlice (hu.const_smul (-Complex.I))

private lemma stronglyMeasurable_reProf {w : CProf}
    (hw : StronglyMeasurable w) : StronglyMeasurable (reProf w) := by
  refine (measurable_pi_lambda _ fun i => ?_).stronglyMeasurable
  exact Complex.continuous_re.measurable.comp
    (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hw).measurable)

private lemma stronglyMeasurable_imProf {w : CProf}
    (hw : StronglyMeasurable w) : StronglyMeasurable (imProf w) :=
  stronglyMeasurable_reProf (hw.const_smul (-Complex.I))

private lemma norm_ofReal_re_le (v : CMerid) :
    ‖(WithLp.toLp 2 fun i : Fin 2 => (((v i).re : ℝ) : ℂ) : CMerid)‖ ≤ ‖v‖ := by
  have hsq : ‖(WithLp.toLp 2 fun i : Fin 2 => (((v i).re : ℝ) : ℂ) : CMerid)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact sq_le_sq.2 (by simpa [abs_of_nonneg (norm_nonneg _)] using Complex.abs_re_le_norm (v i))
  nlinarith [norm_nonneg (WithLp.toLp 2 fun i : Fin 2 => (((v i).re : ℝ) : ℂ) : CMerid),
    norm_nonneg v]

private lemma cylSliceL2_ofRealSlice_reSlice_le (c : ℝ) (u : B0579.Plane → CMerid) :
    cylSliceL2 c (ofRealSlice (reSlice u)) ≤ cylSliceL2 c u :=
  eLpNorm_mono fun y => norm_ofReal_re_le (u y)

private lemma norm_unit_smul_cmerid {ζ : ℂ} (hζ : ‖ζ‖ = 1) (v : CMerid) :
    ‖ζ • v‖ = ‖v‖ := by
  have hsq : ‖ζ • v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [PiLp.smul_apply, hζ]
  nlinarith [norm_nonneg (ζ • v), norm_nonneg v]

private lemma cylSliceL2_unit_smul (c : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (u : B0579.Plane → CMerid) :
    cylSliceL2 c (fun y => ζ • u y) = cylSliceL2 c u := by
  unfold cylSliceL2
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_unit_smul_cmerid hζ (u y))

private lemma cylSliceL2_ofRealSlice_imSlice_le (c : ℝ) (u : B0579.Plane → CMerid) :
    cylSliceL2 c (ofRealSlice (imSlice u)) ≤ cylSliceL2 c u := by
  refine (cylSliceL2_ofRealSlice_reSlice_le c (fun y => (-Complex.I) • u y)).trans ?_
  rw [cylSliceL2_unit_smul c (by simp) u]

private lemma sliceH1Norm_ofRealProf_reProf_le (c : ℝ) (g gq gη : CProf) (s : ℝ) :
    sliceH1Norm c (ofRealProf (reProf g)) (ofRealProf (reProf gq)) (ofRealProf (reProf gη)) s ≤
      sliceH1Norm c g gq gη s :=
  add_le_add
    (add_le_add (cylSliceL2_ofRealSlice_reSlice_le c (fun y => g (s, y)))
      (cylSliceL2_ofRealSlice_reSlice_le c (fun y => gq (s, y))))
    (cylSliceL2_ofRealSlice_reSlice_le c (fun y => gη (s, y)))

private lemma sliceH1Norm_ofRealProf_imProf_le (c : ℝ) (g gq gη : CProf) (s : ℝ) :
    sliceH1Norm c (ofRealProf (imProf g)) (ofRealProf (imProf gq)) (ofRealProf (imProf gη)) s ≤
      sliceH1Norm c g gq gη s :=
  add_le_add
    (add_le_add (cylSliceL2_ofRealSlice_imSlice_le c (fun y => g (s, y)))
      (cylSliceL2_ofRealSlice_imSlice_le c (fun y => gq (s, y))))
    (cylSliceL2_ofRealSlice_imSlice_le c (fun y => gη (s, y)))

private lemma hasWeakCellDerivC_smul (c : ℝ) (j : Fin 2) (ζ : ℂ) {φ g : B0579.Plane → ℂ}
    (h : IIIa.HasWeakCellDerivC c j φ g) :
    IIIa.HasWeakCellDerivC c j (fun y => ζ * φ y) (fun y => ζ * g y) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 ψ hψ
    refine ⟨(h1.const_mul ζ).congr (Eventually.of_forall fun y => by dsimp only; ring),
      (h2.const_mul ζ).congr (Eventually.of_forall fun y => by dsimp only; ring)⟩
  · have h1 : (fun y => ζ * φ y * (B0579.pd j ψ y : ℂ)) =
        fun y => ζ * (φ y * (B0579.pd j ψ y : ℂ)) := funext fun y => by ring
    have h2 : (fun y => ζ * g y * (ψ y : ℂ)) =
        fun y => ζ * (g y * (ψ y : ℂ)) := funext fun y => by ring
    rw [h1, h2, integral_const_mul, integral_const_mul, h.2 ψ hψ, mul_neg]

private lemma hasWeakCellDerivC_re (c : ℝ) (j : Fin 2) {φ g : B0579.Plane → ℂ}
    (h : IIIa.HasWeakCellDerivC c j φ g) :
    IIIa.HasWeakCellDerivC c j (fun y => ((φ y).re : ℂ)) (fun y => ((g y).re : ℂ)) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 ψ hψ
    have h1' : IntegrableOn (fun y => (((φ y * (B0579.pd j ψ y : ℂ)).re : ℝ) : ℂ))
        (B0579.cell c) :=
      Complex.ofRealCLM.integrable_comp (Complex.reCLM.integrable_comp h1)
    have h2' : IntegrableOn (fun y => (((g y * (ψ y : ℂ)).re : ℝ) : ℂ))
        (B0579.cell c) :=
      Complex.ofRealCLM.integrable_comp (Complex.reCLM.integrable_comp h2)
    refine ⟨h1'.congr (Eventually.of_forall fun y => by simp),
      h2'.congr (Eventually.of_forall fun y => by simp)⟩
  · obtain ⟨h1, h2⟩ := h.1 ψ hψ
    have hre1 : ∫ y in B0579.cell c, (φ y).re * B0579.pd j ψ y =
        (∫ y in B0579.cell c, φ y * (B0579.pd j ψ y : ℂ)).re := by
      refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans
        (Complex.reCLM.integral_comp_comm h1)
      simp
    have hre2 : ∫ y in B0579.cell c, (g y).re * ψ y =
        (∫ y in B0579.cell c, g y * (ψ y : ℂ)).re := by
      refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans
        (Complex.reCLM.integral_comp_comm h2)
      simp
    have h1r : IntegrableOn (fun y => (φ y).re * B0579.pd j ψ y) (B0579.cell c) :=
      (Complex.reCLM.integrable_comp h1).congr (Eventually.of_forall fun y => by simp)
    have h2r : IntegrableOn (fun y => (g y).re * ψ y) (B0579.cell c) :=
      (Complex.reCLM.integrable_comp h2).congr (Eventually.of_forall fun y => by simp)
    have hL : ∫ y in B0579.cell c, ((φ y).re : ℂ) * (B0579.pd j ψ y : ℂ) =
        ((∫ y in B0579.cell c, (φ y).re * B0579.pd j ψ y : ℝ) : ℂ) := by
      refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans
        (Complex.ofRealCLM.integral_comp_comm h1r)
      simp
    have hR : ∫ y in B0579.cell c, ((g y).re : ℂ) * (ψ y : ℂ) =
        ((∫ y in B0579.cell c, (g y).re * ψ y : ℝ) : ℂ) := by
      refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans
        (Complex.ofRealCLM.integral_comp_comm h2r)
      simp
    rw [hL, hR, hre1, hre2, h.2 ψ hψ, Complex.neg_re, Complex.ofReal_neg]

private lemma isCylSolenoidalSlice_smul (c : ℝ) (ζ : ℂ) {u : B0579.Plane → CMerid}
    (h : IsCylSolenoidalSlice c u) :
    IsCylSolenoidalSlice c (fun y => ζ • u y) := by
  intro ψ hψ
  obtain ⟨hI, h0⟩ := h ψ hψ
  have heq : (fun y => (ζ • u y) 0 * (B0579.pd 0 ψ y : ℂ) + (ζ • u y) 1 * (B0579.pd 1 ψ y : ℂ)) =
      fun y => ζ * (u y 0 * (B0579.pd 0 ψ y : ℂ) + u y 1 * (B0579.pd 1 ψ y : ℂ)) := by
    funext y; simp [PiLp.smul_apply]; ring
  rw [heq]
  exact ⟨hI.const_mul ζ, by rw [integral_const_mul, h0, mul_zero]⟩

private lemma isCylSolenoidalSlice_re (c : ℝ) {u : B0579.Plane → CMerid}
    (h : IsCylSolenoidalSlice c u) :
    IsCylSolenoidalSlice c (ofRealSlice (reSlice u)) := by
  intro ψ hψ
  obtain ⟨hI, h0⟩ := h ψ hψ
  have hIr : IntegrableOn
      (fun y => (u y 0).re * B0579.pd 0 ψ y + (u y 1).re * B0579.pd 1 ψ y) (B0579.cell c) :=
    (Complex.reCLM.integrable_comp hI).congr (Eventually.of_forall fun y => by simp)
  have hIc : IntegrableOn
      (fun y => ofRealSlice (reSlice u) y 0 * (B0579.pd 0 ψ y : ℂ) +
        ofRealSlice (reSlice u) y 1 * (B0579.pd 1 ψ y : ℂ)) (B0579.cell c) :=
    (Complex.ofRealCLM.integrable_comp hIr).congr
      (Eventually.of_forall fun y => by simp [ofRealSlice, reSlice])
  refine ⟨hIc, ?_⟩
  have hLr : ∫ y in B0579.cell c, ((u y 0).re * B0579.pd 0 ψ y + (u y 1).re * B0579.pd 1 ψ y) = 0 := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans
      ((Complex.reCLM.integral_comp_comm hI).trans (by simp [h0]))
    simp
  have hLc : ∫ y in B0579.cell c,
      (ofRealSlice (reSlice u) y 0 * (B0579.pd 0 ψ y : ℂ) +
        ofRealSlice (reSlice u) y 1 * (B0579.pd 1 ψ y : ℂ)) =
      ((∫ y in B0579.cell c, ((u y 0).re * B0579.pd 0 ψ y + (u y 1).re * B0579.pd 1 ψ y) : ℝ) : ℂ) := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans
      (Complex.ofRealCLM.integral_comp_comm hIr)
    simp [ofRealSlice, reSlice]
  rw [hLc, hLr, Complex.ofReal_zero]

private lemma isCylH1Slice_smul (c : ℝ) (ζ : ℂ) {u uq uη : B0579.Plane → CMerid}
    (h : IsCylH1Slice c u uq uη) :
    IsCylH1Slice c (fun y => ζ • u y) (fun y => ζ • uq y) (fun y => ζ • uη y) where
  sm_u := h.sm_u.const_smul ζ
  sm_uq := h.sm_uq.const_smul ζ
  sm_uη := h.sm_uη.const_smul ζ
  weak_q k := hasWeakCellDerivC_smul c 0 ζ (h.weak_q k)
  weak_eta k := hasWeakCellDerivC_smul c 1 ζ (h.weak_eta k)
  solenoidal := isCylSolenoidalSlice_smul c ζ h.solenoidal
  memL2_u := h.memL2_u.const_smul ζ
  memL2_uq := h.memL2_uq.const_smul ζ
  memL2_uη := h.memL2_uη.const_smul ζ

private lemma isCylH1Slice_re (c : ℝ) {u uq uη : B0579.Plane → CMerid}
    (h : IsCylH1Slice c u uq uη) :
    IsCylH1Slice c (ofRealSlice (reSlice u))
      (ofRealSlice (reSlice uq)) (ofRealSlice (reSlice uη)) where
  sm_u := stronglyMeasurable_ofRealSlice (stronglyMeasurable_reSlice h.sm_u)
  sm_uq := stronglyMeasurable_ofRealSlice (stronglyMeasurable_reSlice h.sm_uq)
  sm_uη := stronglyMeasurable_ofRealSlice (stronglyMeasurable_reSlice h.sm_uη)
  weak_q k := hasWeakCellDerivC_re c 0 (h.weak_q k)
  weak_eta k := hasWeakCellDerivC_re c 1 (h.weak_eta k)
  solenoidal := isCylSolenoidalSlice_re c h.solenoidal
  memL2_u := ⟨(stronglyMeasurable_ofRealSlice
      (stronglyMeasurable_reSlice h.sm_u)).aestronglyMeasurable,
    (cylSliceL2_ofRealSlice_reSlice_le c u).trans_lt h.memL2_u.eLpNorm_lt_top⟩
  memL2_uq := ⟨(stronglyMeasurable_ofRealSlice
      (stronglyMeasurable_reSlice h.sm_uq)).aestronglyMeasurable,
    (cylSliceL2_ofRealSlice_reSlice_le c uq).trans_lt h.memL2_uq.eLpNorm_lt_top⟩
  memL2_uη := ⟨(stronglyMeasurable_ofRealSlice
      (stronglyMeasurable_reSlice h.sm_uη)).aestronglyMeasurable,
    (cylSliceL2_ofRealSlice_reSlice_le c uη).trans_lt h.memL2_uη.eLpNorm_lt_top⟩

private lemma isCylH1Slice_im (c : ℝ) {u uq uη : B0579.Plane → CMerid}
    (h : IsCylH1Slice c u uq uη) :
    IsCylH1Slice c (ofRealSlice (imSlice u))
      (ofRealSlice (imSlice uq)) (ofRealSlice (imSlice uη)) :=
  isCylH1Slice_re c (isCylH1Slice_smul c (-Complex.I) h)

private lemma isCylH1Slice_zero (c : ℝ) :
    IsCylH1Slice c (0 : B0579.Plane → CMerid) 0 0 where
  sm_u := stronglyMeasurable_const
  sm_uq := stronglyMeasurable_const
  sm_uη := stronglyMeasurable_const
  weak_q _ := ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩
  weak_eta _ := ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩
  solenoidal _ _ := ⟨by simp, by simp⟩
  memL2_u := MemLp.zero
  memL2_uq := MemLp.zero
  memL2_uη := MemLp.zero

/-! ## 2. `toCell` periodic retraction and slicewise `IsCylH1Slice` source upgrade -/

private def toCell (c : ℝ) (z : B0579.Plane) : B0579.Plane :=
  (z.1 - c * (⌊(z.1 + c / 2) / c⌋ : ℝ), z.2)

private lemma measurable_toCell (c : ℝ) : Measurable (toCell c) := by
  unfold toCell
  have hfl : Measurable (fun z : B0579.Plane => (⌊(z.1 + c / 2) / c⌋ : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (((measurable_fst.add measurable_const).div_const c).floor)
  exact (measurable_fst.sub (measurable_const.mul hfl)).prodMk measurable_snd

private lemma toCell_periodic {c : ℝ} (hc : 0 < c) (z : B0579.Plane) :
    toCell c (z.1 + c, z.2) = toCell c z := by
  unfold toCell
  ext
  · dsimp only
    have hdiv : (z.1 + c + c / 2) / c = (z.1 + c / 2) / c + 1 := by
      field_simp [hc.ne']
      ring
    rw [hdiv, Int.floor_add_one]
    push_cast
    ring
  · rfl

private lemma toCell_eq_self_of_mem_cell {c : ℝ} (hc : 0 < c) {z : B0579.Plane}
    (hz : z ∈ B0579.cell c) : toCell c z = z := by
  have hlo : 0 ≤ (z.1 + c / 2) / c := div_nonneg (by linarith [hz.1.1]) hc.le
  have hhi : (z.1 + c / 2) / c < 1 := (div_lt_one hc).2 (by linarith [hz.1.2])
  have hfl : ⌊(z.1 + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hlo, by simpa using hhi⟩
  ext
  · simp [toCell, hfl]
  · rfl

private lemma hasWeakCellDerivC_congr_cell {c : ℝ} {j : Fin 2} {φ φ' g g' : B0579.Plane → ℂ}
    (hφ : ∀ᵐ y ∂(volume.restrict (B0579.cell c)), φ' y = φ y)
    (hg : ∀ᵐ y ∂(volume.restrict (B0579.cell c)), g' y = g y)
    (h : IIIa.HasWeakCellDerivC c j φ g) :
    IIIa.HasWeakCellDerivC c j φ' g' := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 ψ hψ
    refine ⟨h1.congr_fun_ae (hφ.mono fun y hy => by simp [hy]),
      h2.congr_fun_ae (hg.mono fun y hy => by simp [hy])⟩
  · have e1 : ∫ y in B0579.cell c, φ' y * (B0579.pd j ψ y : ℂ) =
        ∫ y in B0579.cell c, φ y * (B0579.pd j ψ y : ℂ) :=
      integral_congr_ae (hφ.mono fun y hy => by simp [hy])
    have e2 : ∫ y in B0579.cell c, g' y * (ψ y : ℂ) =
        ∫ y in B0579.cell c, g y * (ψ y : ℂ) :=
      integral_congr_ae (hg.mono fun y hy => by simp [hy])
    rw [e1, e2, h.2 ψ hψ]

private lemma isCylSolenoidalSlice_congr_cell {c : ℝ} {u u' : B0579.Plane → CMerid}
    (hu : ∀ᵐ y ∂(volume.restrict (B0579.cell c)), u' y = u y)
    (h : IsCylSolenoidalSlice c u) :
    IsCylSolenoidalSlice c u' := by
  intro ψ hψ
  obtain ⟨hI, h0⟩ := h ψ hψ
  have hae : (fun y => u' y 0 * (B0579.pd 0 ψ y : ℂ) + u' y 1 * (B0579.pd 1 ψ y : ℂ)) =ᵐ[
      volume.restrict (B0579.cell c)]
      fun y => u y 0 * (B0579.pd 0 ψ y : ℂ) + u y 1 * (B0579.pd 1 ψ y : ℂ) :=
    hu.mono fun y hy => by simp [hy]
  exact ⟨hI.congr_fun_ae hae.symm, (integral_congr_ae hae).trans h0⟩

private lemma isCylH1Slice_toCell {c : ℝ} (hc : 0 < c) {u uq uη : B0579.Plane → CMerid}
    (h : IsCylH1Slice c u uq uη) :
    let up := fun y => u (toCell c y)
    let uqp := fun y => uq (toCell c y)
    let uηp := fun y => uη (toCell c y)
    IsCylH1Slice c up uqp uηp ∧
      cylSliceH1 c (fun y => up y - u y) (fun y => uqp y - uq y) (fun y => uηp y - uη y) = 0 := by
  intro up uqp uηp
  have hae_cell : ∀ (w : B0579.Plane → CMerid),
      (fun y => w (toCell c y)) =ᵐ[volume.restrict (B0579.cell c)] w := by
    intro w
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall fun y hy => ?_)
    dsimp only
    rw [toCell_eq_self_of_mem_cell hc hy]
  have hzero : ∀ (w : B0579.Plane → CMerid),
      cylSliceL2 c (fun y => w (toCell c y) - w y) = 0 := by
    intro w
    unfold cylSliceL2
    refine eLpNorm_eq_zero_of_ae_zero ?_
    filter_upwards [hae_cell w] with y hy
    simp [hy]
  refine ⟨{
    sm_u := h.sm_u.comp_measurable (measurable_toCell c)
    sm_uq := h.sm_uq.comp_measurable (measurable_toCell c)
    sm_uη := h.sm_uη.comp_measurable (measurable_toCell c)
    weak_q := fun k => hasWeakCellDerivC_congr_cell
      ((hae_cell u).mono fun y hy => congrArg (fun v => v k) hy)
      ((hae_cell uq).mono fun y hy => congrArg (fun v => v k) hy) (h.weak_q k)
    weak_eta := fun k => hasWeakCellDerivC_congr_cell
      ((hae_cell u).mono fun y hy => congrArg (fun v => v k) hy)
      ((hae_cell uη).mono fun y hy => congrArg (fun v => v k) hy) (h.weak_eta k)
    solenoidal := isCylSolenoidalSlice_congr_cell (hae_cell u) h.solenoidal
    memL2_u := h.memL2_u.ae_eq (hae_cell u).symm
    memL2_uq := h.memL2_uq.ae_eq (hae_cell uq).symm
    memL2_uη := h.memL2_uη.ae_eq (hae_cell uη).symm
  }, by simp [cylSliceH1, up, uqp, uηp, hzero]⟩

private def coordQShift (t : ℝ) (x : Coord) : Coord := x + (0, (t, 0))

private lemma qPeriodic_coordQShift_int {c : ℝ} {w : CProf} (hw : QPeriodic c w) (k : ℤ) :
    ∀ᵐ x : Coord, 0 < x.1 → w (coordQShift ((k : ℝ) * c) x) = w x := by
  have h1 : ∀ᵐ x : Coord, 0 < x.1 → w (coordQShift c x) = w x := by
    filter_upwards [QPerHalf.ae_imp hw] with x hx hpos
    have heq : coordQShift c x = qShift c x := by ext <;> simp [coordQShift, qShift]
    rw [heq]; exact hx hpos
  induction k using Int.induction_on with
  | zero =>
    refine Eventually.of_forall fun x _ => ?_
    have heq : coordQShift (((0 : ℤ) : ℝ) * c) x = x := by ext <;> simp [coordQShift]
    rw [heq]
  | succ n ih =>
    have hshift : ∀ᵐ x : Coord,
        0 < (coordQShift ((n : ℝ) * c) x).1 →
          w (coordQShift c (coordQShift ((n : ℝ) * c) x)) = w (coordQShift ((n : ℝ) * c) x) :=
      (measurePreserving_add_right volume ((0, ((n : ℝ) * c, 0)) : Coord)).quasiMeasurePreserving.ae h1
    filter_upwards [ih, hshift] with x hih hsh hpos
    have hpos' : 0 < (coordQShift ((n : ℝ) * c) x).1 := by simpa [coordQShift] using hpos
    push_cast
    have hcomp : coordQShift (((n : ℝ) + 1) * c) x =
        coordQShift c (coordQShift ((n : ℝ) * c) x) := by
      (ext <;> simp [coordQShift]); ring
    rw [hcomp, hsh hpos']
    simpa using hih hpos
  | pred n ih =>
    have hshift : ∀ᵐ x : Coord,
        0 < (coordQShift ((-(n : ℝ) - 1) * c) x).1 →
          w (coordQShift c (coordQShift ((-(n : ℝ) - 1) * c) x)) =
            w (coordQShift ((-(n : ℝ) - 1) * c) x) :=
      (measurePreserving_add_right volume
        ((0, ((-(n : ℝ) - 1) * c, 0)) : Coord)).quasiMeasurePreserving.ae h1
    filter_upwards [ih, hshift] with x hih hsh hpos
    have hpos' : 0 < (coordQShift ((-(n : ℝ) - 1) * c) x).1 := by simpa [coordQShift] using hpos
    have hcomp : coordQShift c (coordQShift ((-(n : ℝ) - 1) * c) x) =
        coordQShift (-(n : ℝ) * c) x := by
      (ext <;> simp [coordQShift]); ring
    have hsh' := hsh hpos'
    rw [hcomp] at hsh'
    have hcast : (((-(n : ℤ) - 1 : ℤ) : ℝ) * c) = (-(n : ℝ) - 1) * c := by push_cast; ring
    have hih' : w (coordQShift (-(n : ℝ) * c) x) = w x := by simpa using hih hpos
    rw [hcast, ← hsh', hih']

private def toCellProf (c : ℝ) (w : CProf) : CProf :=
  fun x => w (x.1, toCell c x.2)

private lemma stronglyMeasurable_toCellProf (c : ℝ) {w : CProf} (hw : StronglyMeasurable w) :
    StronglyMeasurable (toCellProf c w) :=
  hw.comp_measurable (measurable_fst.prodMk ((measurable_toCell c).comp measurable_snd))

private lemma toCellProf_periodic {c : ℝ} (hc : 0 < c) (w : CProf) (x : Coord) :
    toCellProf c w (qShift c x) = toCellProf c w x := by
  simp [toCellProf, qShift, toCell_periodic hc]

private lemma toCellProf_ae_eq {c : ℝ} {w : CProf} (hw : QPeriodic c w) :
    ∀ᵐ x : Coord, 0 < x.1 → toCellProf c w x = w x := by
  have hall : ∀ᵐ x : Coord, ∀ k : ℤ, 0 < x.1 → w (coordQShift ((k : ℝ) * c) x) = w x :=
    ae_all_iff.2 (qPeriodic_coordQShift_int hw)
  filter_upwards [hall] with x hx hpos
  let k : ℤ := -⌊(x.2.1 + c / 2) / c⌋
  have heq : (x.1, toCell c x.2) = coordQShift ((k : ℝ) * c) x := by
    ext
    · simp [coordQShift]
    · simp [toCell, coordQShift, k]; ring
    · simp [toCell, coordQShift]
  rw [toCellProf, heq]
  exact hx k hpos

private lemma measurable_cylSliceL2 (c : ℝ) {w : CProf} (hw : StronglyMeasurable w) :
    Measurable (fun s : ℝ => cylSliceL2 c (fun y => w (s, y))) := by
  have key : (fun s : ℝ => cylSliceL2 c (fun y => w (s, y))) =
      fun s => (∫⁻ y in B0579.cell c, ‖w (s, y)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    funext s
    unfold cylSliceL2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rfl
  rw [key]
  exact ((hw.enorm.pow_const (2 : ℝ)).lintegral_prod_right').pow_const (1 / (2 : ℝ))

private lemma measurable_sliceH1Norm (c : ℝ) {g gq gη : CProf}
    (hg : StronglyMeasurable g) (hgq : StronglyMeasurable gq) (hgη : StronglyMeasurable gη) :
    Measurable (sliceH1Norm c g gq gη) :=
  ((measurable_cylSliceL2 c hg).add (measurable_cylSliceL2 c hgq)).add (measurable_cylSliceL2 c hgη)

private lemma ae_div_zero_of_isCylSourceH1 {c : ℝ} {g gq gη : CProf}
    (hg : IsCylSourceH1 c g gq gη) :
    ∀ᵐ x : Coord, 0 < x.1 → gq x 0 + gη x 1 = 0 := by
  have hloc : LocallyIntegrableOn (fun x => gq x 0 + gη x 1) DriftWeakSHelp.Upos volume :=
    (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hg.weak_q 0).1 φ hφ).2)).add
      (DriftWeakSHelp.locInt_of_tests _ (fun φ hφ => ((hg.weak_eta 1).1 φ hφ).2))
  have : (volume : Measure Coord).IsAddHaarMeasure := DriftWeakSHelp.instIsAddHaarVolCoord
  have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro φ hφs hφc hφU
    have hφ : IsCoordTest φ := ⟨hφs, hφc, hφU⟩
    have hIq := ((hg.weak_q 0).1 φ hφ).2
    have hIη := ((hg.weak_eta 1).1 φ hφ).2
    have hadd : ∫ x, (gq x 0 + gη x 1) * (φ x : ℂ) =
        (∫ x, gq x 0 * (φ x : ℂ)) + ∫ x, gη x 1 * (φ x : ℂ) := by
      rw [← integral_add hIq hIη]; congr 1; funext x; ring
    have hctQ : (fun x => g x 0 * (coordTranspose vQ0 dZero φ x : ℂ)) =
        fun x => -(g x 0 * (cpd 1 φ x : ℂ)) := by
      funext x; rw [wb_ct_Q]; push_cast; ring
    have hctE : (fun x => g x 1 * (coordTranspose vEta dZero φ x : ℂ)) =
        fun x => -(g x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; rw [wb_ct_E]; push_cast; ring
    have hIq' : Integrable (fun x => g x 0 * (cpd 1 φ x : ℂ)) := by
      have h := ((hg.weak_q 0).1 φ hφ).1; rw [hctQ] at h
      exact h.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hIη' : Integrable (fun x => g x 1 * (cpd 2 φ x : ℂ)) := by
      have h := ((hg.weak_eta 1).1 φ hφ).1; rw [hctE] at h
      exact h.neg.congr (Eventually.of_forall fun x => neg_neg _)
    have hsol := (hg.solenoidal φ hφ).2
    have hzero : ∫ x, (gq x 0 + gη x 1) * (φ x : ℂ) = 0 := by
      rw [hadd, (hg.weak_q 0).2 φ hφ, (hg.weak_eta 1).2 φ hφ, hctQ, hctE,
        integral_neg, integral_neg, ← neg_add, ← integral_add hIq' hIη', hsol, neg_zero]
    simp only [Complex.real_smul]
    convert hzero using 2
    funext x; ring)
  filter_upwards [hae] with x hx hp
  exact hx (DriftWeakSHelp.mem_Upos.2 hp)

private lemma isCylSolenoidalSlice_of_weak_and_div {c : ℝ}
    {u uq uη : B0579.Plane → CMerid}
    (hwq : IIIa.HasWeakCellDerivC c 0 (fun y => u y 0) (fun y => uq y 0))
    (hwη : IIIa.HasWeakCellDerivC c 1 (fun y => u y 1) (fun y => uη y 1))
    (hdiv : ∀ᵐ y ∂(volume.restrict (B0579.cell c)), uq y 0 + uη y 1 = 0) :
    IsCylSolenoidalSlice c u := by
  intro ψ hψ
  obtain ⟨h10, h20⟩ := hwq.1 ψ hψ
  obtain ⟨h11, h21⟩ := hwη.1 ψ hψ
  refine ⟨h10.add h11, ?_⟩
  rw [integral_add h10 h11, hwq.2 ψ hψ, hwη.2 ψ hψ, ← neg_add, ← integral_add h20 h21, neg_eq_zero]
  refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
  filter_upwards [hdiv] with y hy
  have : uq y 0 * (ψ y : ℂ) + uη y 1 * (ψ y : ℂ) = (uq y 0 + uη y 1) * (ψ y : ℂ) := by ring
  rw [this, hy, zero_mul]

private lemma upgradeTailSource {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    {g gq gη : CProf} (hg : IsCylSourceH1 c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) < ⊤) :
    ∃ g₁ gq₁ gη₁ : CProf,
      StronglyMeasurable g₁ ∧ StronglyMeasurable gq₁ ∧ StronglyMeasurable gη₁ ∧
      (∀ x : Coord, g₁ (qShift c x) = g₁ x ∧
        gq₁ (qShift c x) = gq₁ x ∧ gη₁ (qShift c x) = gη₁ x) ∧
      (∀ s : ℝ, IsCylH1Slice c (fun y => g₁ (s, y))
        (fun y => gq₁ (s, y)) (fun y => gη₁ (s, y))) ∧
      (∀ᵐ x : Coord, T < x.1 → g₁ x = g x ∧ gq₁ x = gq x ∧ gη₁ x = gη x) ∧
      (∀ s : ℝ, sliceH1Norm c g₁ gq₁ gη₁ s ≤ sliceH1Norm c g gq gη s) := by
  let gp := toCellProf c g
  let gqp := toCellProf c gq
  let gηp := toCellProf c gη
  have hsm_gp : StronglyMeasurable gp := stronglyMeasurable_toCellProf c hg.sm_g
  have hsm_gqp : StronglyMeasurable gqp := stronglyMeasurable_toCellProf c hg.sm_gq
  have hsm_gηp : StronglyMeasurable gηp := stronglyMeasurable_toCellProf c hg.sm_gη
  have hper_gp : QPeriodic c gp := QPerHalf.of_ae (Eventually.of_forall (toCellProf_periodic hc g))
  have hper_gqp : QPeriodic c gqp := QPerHalf.of_ae (Eventually.of_forall (toCellProf_periodic hc gq))
  have hper_gηp : QPeriodic c gηp := QPerHalf.of_ae (Eventually.of_forall (toCellProf_periodic hc gη))
  have hae_gp := toCellProf_ae_eq hg.periodic_g
  have hae_gqp := toCellProf_ae_eq hg.periodic_gq
  have hae_gηp := toCellProf_ae_eq hg.periodic_gη
  have hwq_gp : HasWeakVec vQ0 dZero gp gqp := hasWeakVec_congr hae_gp hae_gqp hg.weak_q
  have hwη_gp : HasWeakVec vEta dZero gp gηp := hasWeakVec_congr hae_gp hae_gηp hg.weak_eta
  have hsol_gp : ∀ φ, IsCoordTest φ →
      Integrable (fun x => gp x 0 * (cpd 1 φ x : ℂ) + gp x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (gp x 0 * (cpd 1 φ x : ℂ) + gp x 1 * (cpd 2 φ x : ℂ)) = 0 := by
    intro φ hφ
    obtain ⟨hI, h0⟩ := hg.solenoidal φ hφ
    have hae : (fun x => gp x 0 * (cpd 1 φ x : ℂ) + gp x 1 * (cpd 2 φ x : ℂ)) =ᵐ[volume]
        fun x => g x 0 * (cpd 1 φ x : ℂ) + g x 1 * (cpd 2 φ x : ℂ) := by
      filter_upwards [hae_gp] with x hx
      by_cases hp : 0 < x.1
      · have hxeq : gp x = g x := hx hp
        rw [hxeq]
      · have h1 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 1)) hp
        have h2 := F10K0Help.isCoordTest_zero_of_nonpos
          (planarTest_isCoordTest_partial hφ (cdir 2)) hp
        change fderiv ℝ φ x (cdir 1) = 0 at h1
        change fderiv ℝ φ x (cdir 2) = 0 at h2
        simp [cpd, h1, h2]
    exact ⟨hI.congr hae.symm, (integral_congr_ae hae).trans h0⟩
  have hsrc_gp : IsCylSourceH1 c gp gqp gηp :=
    ⟨hsm_gp, hsm_gqp, hsm_gηp, hper_gp, hper_gqp, hper_gηp, hwq_gp, hwη_gp, hsol_gp⟩
  have hnorm_eq : ∀ s : ℝ, sliceH1Norm c gp gqp gηp s = sliceH1Norm c g gq gη s := by
    intro s
    have hcell : ∀ w : CProf,
        (fun y => toCellProf c w (s, y)) =ᵐ[volume.restrict (B0579.cell c)] fun y => w (s, y) :=
      fun w => (ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (Eventually.of_forall fun y hy => by simp [toCellProf, toCell_eq_self_of_mem_cell hc hy])
    exact sliceH1Norm_congr_ae_cell (hcell g) (hcell gq) (hcell gη)
  have hfin_ae : ∀ᵐ s ∂volume, T < s → sliceH1Norm c gp gqp gηp s < ⊤ := by
    have hlt : (∫⁻ s in Ioi T, sliceH1Norm c gp gqp gηp s) < ⊤ := by
      simpa [hnorm_eq] using hg_int
    exact (ae_restrict_iff' measurableSet_Ioi).1
      (ae_lt_top (measurable_sliceH1Norm c hsm_gp hsm_gqp hsm_gηp) hlt.ne)
  have hw0 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 0 gp gqp
    hsm_gp hsm_gqp hper_gp hper_gqp hwq_gp
  have hw1 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 1 gp gηp
    hsm_gp hsm_gηp hper_gp hper_gηp hwη_gp
  have hdiv_prod : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure B0579.Plane),
      0 < (s, y).1 → gqp (s, y) 0 + gηp (s, y) 1 = 0 :=
    Measure.ae_ae_of_ae_prod (ae_div_zero_of_isCylSourceH1 hsrc_gp)
  have hgood_ae : ∀ᵐ s ∂volume, T < s →
      IsCylH1Slice c (fun y => gp (s, y)) (fun y => gqp (s, y)) (fun y => gηp (s, y)) := by
    filter_upwards [hfin_ae, hw0, hw1, hdiv_prod] with s hfin h0 h1 hdiv hsT
    have hs0 : 0 < s := hT.trans hsT
    have hfin' := hfin hsT
    have hm_u : MemLp (fun y => gp (s, y)) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(hsm_gp.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        (le_self_add.trans le_self_add).trans_lt hfin'⟩
    have hm_uq : MemLp (fun y => gqp (s, y)) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(hsm_gqp.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        (le_add_self.trans le_self_add).trans_lt hfin'⟩
    have hm_uη : MemLp (fun y => gηp (s, y)) 2 (volume.restrict (B0579.cell c)) :=
      ⟨(hsm_gηp.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        le_add_self.trans_lt hfin'⟩
    have hq_s := h0 hs0 hm_u hm_uq
    have hη_s := h1 hs0 hm_u hm_uη
    have hdiv_s : ∀ᵐ y ∂(volume.restrict (B0579.cell c)), gqp (s, y) 0 + gηp (s, y) 1 = 0 :=
      ae_restrict_of_ae (hdiv.mono fun y hy => hy hs0)
    exact {
      sm_u := hsm_gp.comp_measurable measurable_prodMk_left
      sm_uq := hsm_gqp.comp_measurable measurable_prodMk_left
      sm_uη := hsm_gηp.comp_measurable measurable_prodMk_left
      weak_q := hq_s
      weak_eta := hη_s
      solenoidal := isCylSolenoidalSlice_of_weak_and_div (hq_s 0) (hη_s 1) hdiv_s
      memL2_u := hm_u
      memL2_uq := hm_uq
      memL2_uη := hm_uη
    }
  let Bad : Set ℝ := {s : ℝ | ¬ (T < s →
    IsCylH1Slice c (fun y => gp (s, y)) (fun y => gqp (s, y)) (fun y => gηp (s, y)))}
  have hBad_null : volume Bad = 0 := ae_iff.1 hgood_ae
  obtain ⟨N, hBad_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hBad_null
  let G : Set Coord := (Ioi T \ N) ×ˢ univ
  have hG_meas : MeasurableSet G := (measurableSet_Ioi.diff hN_meas).prod MeasurableSet.univ
  let g₁ : CProf := G.indicator gp
  let gq₁ : CProf := G.indicator gqp
  let gη₁ : CProf := G.indicator gηp
  have hN_prod_null : (volume : Measure Coord) (N ×ˢ univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, hN_null, zero_mul]
  have hae_notN : ∀ᵐ x : Coord, x.1 ∉ N := by
    rw [ae_iff]
    exact measure_mono_null
      (fun x hx => (⟨by simpa using hx, trivial⟩ : x ∈ N ×ˢ univ)) hN_prod_null
  refine ⟨g₁, gq₁, gη₁, hsm_gp.indicator hG_meas, hsm_gqp.indicator hG_meas,
    hsm_gηp.indicator hG_meas, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x.1 ∈ Ioi T \ N
    · have hxs : (qShift c x) ∈ G := ⟨hx, trivial⟩
      have hxG : x ∈ G := ⟨hx, trivial⟩
      simp [g₁, gq₁, gη₁, hxG, hxs, gp, gqp, gηp, toCellProf_periodic hc]
    · have hxs : (qShift c x) ∉ G := fun h => hx h.1
      have hxG : x ∉ G := fun h => hx h.1
      simp [g₁, gq₁, gη₁, hxG, hxs]
  · intro s
    by_cases hs : s ∈ Ioi T \ N
    · have hnotBad : s ∉ Bad := fun hb => hs.2 (hBad_sub hb)
      have hsl : IsCylH1Slice c (fun y => gp (s, y)) (fun y => gqp (s, y)) (fun y => gηp (s, y)) := by
        by_contra hnot
        exact hnotBad fun h => hnot (h hs.1)
      have heq_u : (fun y => g₁ (s, y)) = fun y => gp (s, y) :=
        funext fun y => Set.indicator_of_mem (s := G) ⟨hs, trivial⟩ gp
      have heq_uq : (fun y => gq₁ (s, y)) = fun y => gqp (s, y) :=
        funext fun y => Set.indicator_of_mem (s := G) ⟨hs, trivial⟩ gqp
      have heq_uη : (fun y => gη₁ (s, y)) = fun y => gηp (s, y) :=
        funext fun y => Set.indicator_of_mem (s := G) ⟨hs, trivial⟩ gηp
      rwa [heq_u, heq_uq, heq_uη]
    · have heq_u : (fun y => g₁ (s, y)) = 0 :=
        funext fun y => Set.indicator_of_notMem (s := G) (fun h => hs h.1) gp
      have heq_uq : (fun y => gq₁ (s, y)) = 0 :=
        funext fun y => Set.indicator_of_notMem (s := G) (fun h => hs h.1) gqp
      have heq_uη : (fun y => gη₁ (s, y)) = 0 :=
        funext fun y => Set.indicator_of_notMem (s := G) (fun h => hs h.1) gηp
      rw [heq_u, heq_uq, heq_uη]
      exact isCylH1Slice_zero c
  · filter_upwards [hae_notN, hae_gp, hae_gqp, hae_gηp] with x hxN h1 h2 h3 hxT
    have hxG : x ∈ G := ⟨⟨hxT, hxN⟩, trivial⟩
    have hp : 0 < x.1 := hT.trans hxT
    exact ⟨(Set.indicator_of_mem hxG gp).trans (h1 hp),
      (Set.indicator_of_mem hxG gqp).trans (h2 hp),
      (Set.indicator_of_mem hxG gηp).trans (h3 hp)⟩
  · intro s
    by_cases hs : s ∈ Ioi T \ N
    · have heq_u : (fun y => g₁ (s, y)) = fun y => gp (s, y) :=
        funext fun y => Set.indicator_of_mem (s := G) ⟨hs, trivial⟩ gp
      have heq_uq : (fun y => gq₁ (s, y)) = fun y => gqp (s, y) :=
        funext fun y => Set.indicator_of_mem (s := G) ⟨hs, trivial⟩ gqp
      have heq_uη : (fun y => gη₁ (s, y)) = fun y => gηp (s, y) :=
        funext fun y => Set.indicator_of_mem (s := G) ⟨hs, trivial⟩ gηp
      have : sliceH1Norm c g₁ gq₁ gη₁ s = sliceH1Norm c gp gqp gηp s := by
        simp [sliceH1Norm, heq_u, heq_uq, heq_uη]
      rw [this, hnorm_eq]
    · have heq_u : (fun y => g₁ (s, y)) = 0 :=
        funext fun y => Set.indicator_of_notMem (fun h => hs h.1) gp
      have heq_uq : (fun y => gq₁ (s, y)) = 0 :=
        funext fun y => Set.indicator_of_notMem (fun h => hs h.1) gqp
      have heq_uη : (fun y => gη₁ (s, y)) = 0 :=
        funext fun y => Set.indicator_of_notMem (fun h => hs h.1) gηp
      simp [sliceH1Norm, heq_u, heq_uq, heq_uη]

/-! ## 3. Integrability and 1D smooth-bump seam gluing for the meridional PDE -/

private lemma cylSliceL2_sub_le (c : ℝ) {u v w : B0579.Plane → CMerid}
    (hu : StronglyMeasurable u) (hv : StronglyMeasurable v) (hw : StronglyMeasurable w) :
    cylSliceL2 c (fun y => u y - w y) ≤
      cylSliceL2 c (fun y => u y - v y) + cylSliceL2 c (fun y => v y - w y) := by
  have heq : (fun y => u y - w y) = (fun y => u y - v y) + (fun y => v y - w y) := by
    funext y; simp
  unfold cylSliceL2
  rw [heq]
  exact eLpNorm_add_le (hu.sub hv).aestronglyMeasurable (hv.sub hw).aestronglyMeasurable
    (by norm_num)

private lemma cylSliceL2_symm (c : ℝ) (u v : B0579.Plane → CMerid) :
    cylSliceL2 c (fun y => u y - v y) = cylSliceL2 c (fun y => v y - u y) := by
  have heq : (fun y => u y - v y) = -(fun y => v y - u y) := by funext y; simp
  unfold cylSliceL2
  rw [heq, eLpNorm_neg]

private lemma cylSliceH1_triangle (c : ℝ) {u uq uη v vq vη w wq wη : B0579.Plane → CMerid}
    (hu : StronglyMeasurable u) (huq : StronglyMeasurable uq) (huη : StronglyMeasurable uη)
    (hv : StronglyMeasurable v) (hvq : StronglyMeasurable vq) (hvη : StronglyMeasurable vη)
    (hw : StronglyMeasurable w) (hwq : StronglyMeasurable wq) (hwη : StronglyMeasurable wη) :
    cylSliceH1 c (fun y => u y - w y) (fun y => uq y - wq y) (fun y => uη y - wη y) ≤
      cylSliceH1 c (fun y => u y - v y) (fun y => uq y - vq y) (fun y => uη y - vη y) +
        cylSliceH1 c (fun y => v y - w y) (fun y => vq y - wq y) (fun y => vη y - wη y) := by
  refine (add_le_add (add_le_add (cylSliceL2_sub_le c hu hv hw) (cylSliceL2_sub_le c huq hvq hwq))
    (cylSliceL2_sub_le c huη hvη hwη)).trans (le_of_eq ?_)
  unfold cylSliceH1; ac_rfl

private lemma cylSliceH1_symm (c : ℝ) (u uq uη v vq vη : B0579.Plane → CMerid) :
    cylSliceH1 c (fun y => u y - v y) (fun y => uq y - vq y) (fun y => uη y - vη y) =
      cylSliceH1 c (fun y => v y - u y) (fun y => vq y - uq y) (fun y => vη y - uη y) := by
  simp only [cylSliceH1, cylSliceL2_symm c u v, cylSliceL2_symm c uq vq, cylSliceL2_symm c uη vη]

private lemma sliceH1Norm_le_add_diff (c : ℝ) {Z Zq Zη : CProf}
    (hZ : StronglyMeasurable Z) (hZq : StronglyMeasurable Zq) (hZη : StronglyMeasurable Zη)
    (s s' : ℝ) :
    sliceH1Norm c Z Zq Zη s' ≤
      sliceH1Norm c Z Zq Zη s +
        cylSliceH1 c (fun y => Z (s', y) - Z (s, y))
          (fun y => Zq (s', y) - Zq (s, y)) (fun y => Zη (s', y) - Zη (s, y)) := by
  have hL : ∀ w : CProf, StronglyMeasurable w →
      cylSliceL2 c (fun y => w (s', y)) ≤
        cylSliceL2 c (fun y => w (s, y)) + cylSliceL2 c (fun y => w (s', y) - w (s, y)) := by
    intro w hw
    have e : (fun y => w (s', y)) = (fun y => w (s, y)) + (fun y => w (s', y) - w (s, y)) := by
      funext y; simp
    unfold cylSliceL2; rw [e]
    exact eLpNorm_add_le (hw.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      ((hw.comp_measurable measurable_prodMk_left).sub
        (hw.comp_measurable measurable_prodMk_left)).aestronglyMeasurable (by norm_num)
  refine (add_le_add (add_le_add (hL Z hZ) (hL Zq hZq)) (hL Zη hZη)).trans (le_of_eq ?_)
  unfold sliceH1Norm cylSliceH1 cylSliceL2
  ring

private lemma loc_sliceH1Norm_lt_top_of_cont_Ici {c T : ℝ}
    {Z Zq Zη : CProf}
    (hZ : StronglyMeasurable Z) (hZq : StronglyMeasurable Zq) (hZη : StronglyMeasurable Zη)
    (hzero : ∀ x : Coord, x.1 < T → Z x = 0 ∧ Zq x = 0 ∧ Zη x = 0)
    (hfin_pt : ∀ s : ℝ, T ≤ s → sliceH1Norm c Z Zq Zη s < ⊤)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => Z (s', y) - Z (s, y))
        (fun y => Zq (s', y) - Zq (s, y))
        (fun y => Zη (s', y) - Zη (s, y))) (𝓝[Ici T] s) (𝓝 0)) :
    ∀ a b : ℝ, (∫⁻ s in Icc a b, sliceH1Norm c Z Zq Zη s) < ⊤ := by
  intro a b
  have hzero_s : ∀ s : ℝ, s < T → sliceH1Norm c Z Zq Zη s = 0 := by
    intro s hs
    have hZ0 : (fun y => Z (s, y)) = 0 := funext fun y => (hzero (s, y) hs).1
    have hZq0 : (fun y => Zq (s, y)) = 0 := funext fun y => (hzero (s, y) hs).2.1
    have hZη0 : (fun y => Zη (s, y)) = 0 := funext fun y => (hzero (s, y) hs).2.2
    simp [sliceH1Norm, hZ0, hZq0, hZη0]
  by_cases hbT : b < T
  · have heq : EqOn (sliceH1Norm c Z Zq Zη) (fun _ => 0) (Icc a b) :=
      fun s hs => hzero_s s (hs.2.trans_lt hbT)
    rw [setLIntegral_congr_fun measurableSet_Icc heq]
    simp
  · rw [not_lt] at hbT
    by_cases hab : b < a
    · rw [Icc_eq_empty (not_le_of_gt hab)]; simp
    · rw [not_lt] at hab
      let a' : ℝ := max a T
      have ha'T : T ≤ a' := le_max_right a T
      have ha'b : a' ≤ b := max_le hab hbT
      let K : Set ℝ := Icc a' b
      have hball : ∀ s : K, ∃ δ : ℝ, 0 < δ ∧
          ∀ s' ∈ Metric.ball (s : ℝ) δ ∩ Ici T,
            sliceH1Norm c Z Zq Zη s' ≤ sliceH1Norm c Z Zq Zη s + 1 := by
        intro ⟨s, hsK⟩
        have hsT : T ≤ s := ha'T.trans hsK.1
        have hnear := (ENNReal.tendsto_nhds_zero.1 (hcont s hsT)) 1 one_pos
        obtain ⟨U, hU_nhds, hU_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnear
        obtain ⟨δ, hδ, hbU⟩ := Metric.mem_nhds_iff.1 hU_nhds
        refine ⟨δ, hδ, fun s' hs' => ?_⟩
        exact (sliceH1Norm_le_add_diff c hZ hZq hZη s s').trans
          (add_le_add_right (hU_sub ⟨hbU hs'.1, hs'.2⟩) _)
      choose δ hδ_pos hδ_le using hball
      obtain ⟨F, hF_cov⟩ := isCompact_Icc.elim_finite_subcover
        (fun i : K => Metric.ball (i : ℝ) (δ i)) (fun _ => Metric.isOpen_ball)
        (fun s hsK => mem_iUnion.2 ⟨⟨s, hsK⟩, Metric.mem_ball_self (hδ_pos ⟨s, hsK⟩)⟩)
      let B : ℝ≥0∞ := ∑ i ∈ F, (sliceH1Norm c Z Zq Zη (i : ℝ) + 1)
      have hB_lt : B < ⊤ := ENNReal.sum_lt_top.2 fun i _ =>
        ENNReal.add_lt_top.2 ⟨hfin_pt i (ha'T.trans i.2.1), ENNReal.one_lt_top⟩
      have hle_all : ∀ s ∈ Icc a b, sliceH1Norm c Z Zq Zη s ≤ B := by
        intro s hs
        by_cases hsT : s < T
        · rw [hzero_s s hsT]; exact zero_le
        · rw [not_lt] at hsT
          have hsK : s ∈ K := ⟨max_le hs.1 hsT, hs.2⟩
          obtain ⟨i, hiF, his⟩ := mem_iUnion₂.1 (hF_cov hsK)
          exact (hδ_le i s ⟨his, hsT⟩).trans
            (Finset.single_le_sum (f := fun j : K => sliceH1Norm c Z Zq Zη (j : ℝ) + 1)
              (fun _ _ => zero_le) hiF)
      calc (∫⁻ s in Icc a b, sliceH1Norm c Z Zq Zη s)
          ≤ ∫⁻ _ in Icc a b, B := setLIntegral_mono' measurableSet_Icc hle_all
        _ = B * volume (Icc a b) := by simp
        _ < ⊤ := ENNReal.mul_lt_top hB_lt (by simp [Real.volume_Icc])

private def mulPos (A φ : Coord → ℝ) (x : Coord) : ℝ :=
  if 0 < x.1 then A x * φ x else 0

private lemma continuous_mulPos {A φ : Coord → ℝ}
    (hA : ContinuousOn A {x : Coord | 0 < x.1}) (hφ : IsCoordTest φ) :
    Continuous (mulPos A φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : 0 < x.1
  · have hopen : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
    have hcontOn : ContinuousOn (fun y => A y * φ y) {y : Coord | 0 < y.1} :=
      hA.mul hφ.smooth.continuous.continuousOn
    refine (hcontOn.continuousAt (hopen.mem_nhds hx)).congr ?_
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp [mulPos, hy]
  · have hx_not : x ∉ tsupport φ := fun hmem => hx (hφ.supp hmem).1
    have hopen : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
    refine (continuousAt_const : ContinuousAt (fun _ : Coord => (0 : ℝ)) x).congr ?_
    filter_upwards [hopen.mem_nhds hx_not] with y hy
    have hy0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    by_cases hy_pos : 0 < y.1 <;> simp [mulPos, hy_pos, hy0]

private lemma mulPos_eq_mul (A : Coord → ℝ) {φ : Coord → ℝ} (hφ : IsCoordTest φ) (x : Coord) :
    mulPos A φ x = A x * φ x := by
  by_cases hx : 0 < x.1
  · simp [mulPos, hx]
  · have h0 : φ x = 0 := F10K0Help.isCoordTest_zero_of_nonpos hφ hx
    simp [mulPos, hx, h0]

private lemma integrable_pde_terms (p : Params)
    {Z Zq Zη g : CProf}
    (hZ : StronglyMeasurable Z) (hZq : StronglyMeasurable Zq) (hZη : StronglyMeasurable Zη)
    (hg : StronglyMeasurable g)
    (hZ_per : QPeriodic p.c Z) (hZq_per : QPeriodic p.c Zq) (hZη_per : QPeriodic p.c Zη)
    (hg_per : QPeriodic p.c g)
    (hZ_loc : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, sliceH1Norm p.c Z Zq Zη s) < ⊤)
    (hg_loc : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun y => g (s, y))) < ⊤)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    Integrable (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train Z Zq Zη) Ψ) ∧
      Integrable (cdot g Ψ) := by
  have hc : 0 < p.c := p.c_pos
  have hcomp_meas : ∀ {w : CProf}, StronglyMeasurable w → ∀ k : Fin 2,
      AEStronglyMeasurable (fun x : Coord => w x k) volume := fun hw k =>
    ((EuclideanSpace.proj (𝕜 := ℂ) k).continuous.comp_stronglyMeasurable hw).aestronglyMeasurable
  have hcomp_per : ∀ {w : CProf}, QPeriodic p.c w → ∀ k : Fin 2,
      ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), w (qShift p.c x) k = w x k :=
    fun hp k => hp.mono fun _ hx => congrArg (fun v : CMerid => v k) hx
  have hcomp_L2_le : ∀ (w : CProf) (s : ℝ) (k : Fin 2),
      eLpNorm (fun z => w (s, z) k) 2 (volume.restrict (B0579.cell p.c)) ≤
        cylSliceL2 p.c (fun z => w (s, z)) := by
    intro w s k
    refine eLpNorm_mono_enorm fun z => ?_
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    exact_mod_cast PiLp.norm_apply_le (w (s, z)) k
  have hint_pair : ∀ {w : CProf}, StronglyMeasurable w → QPeriodic p.c w →
      (∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun z => w (s, z))) < ⊤) →
      ∀ (k : Fin 2) {φ : Coord → ℝ}, IsCoordTest φ →
      ∀ {A : Coord → ℝ}, ContinuousOn A {x : Coord | 0 < x.1} →
      Integrable (fun x : Coord => w x k * ((A x * φ x : ℝ) : ℂ)) := by
    intro w hw hw_per hw_loc k φ hφ A hA
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hφ
    have hw_k : (∫⁻ s in Icc a b,
        eLpNorm (fun z => w (s, z) k) 2 (volume.restrict (B0579.cell p.c))) < ⊤ :=
      (lintegral_mono fun s => hcomp_L2_le w s k).trans_lt (hw_loc a b ha)
    have hα_cont : Continuous (mulPos A φ) := continuous_mulPos hA hφ
    have hα_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → mulPos A φ x = 0 := by
      intro x hx
      rw [mulPos_eq_mul A hφ x, (hbox x hx).1, mul_zero]
    have hI := (TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
      hc ha hab hR (hcomp_meas hw k) (hcomp_per hw_per k) hw_k hα_cont hα_supp).1
    exact hI.congr (Eventually.of_forall fun x => by dsimp only; rw [mulPos_eq_mul A hφ x])
  have hZ_L2 : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun z => Z (s, z))) < ⊤ :=
    fun a b ha => (lintegral_mono fun _ => le_self_add.trans le_self_add).trans_lt (hZ_loc a b ha)
  have hZq_L2 : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun z => Zq (s, z))) < ⊤ :=
    fun a b ha => (lintegral_mono fun _ => le_add_self.trans le_self_add).trans_lt (hZ_loc a b ha)
  have hZη_L2 : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun z => Zη (s, z))) < ⊤ :=
    fun a b ha => (lintegral_mono fun _ => le_add_self).trans_lt (hZ_loc a b ha)
  have hpos_eq : FlatBvWL.U0 = {x : Coord | 0 < x.1} := by ext x; simp [FlatBvWL.U0]
  have hcont_v : ∀ k : Fin 2, ContinuousOn (fun x : Coord => p.train.v x.1 x.2 k)
      {x : Coord | 0 < x.1} := by
    intro k; have h := (FlatBvWL.gC_contDiffOn p.train k).continuousOn; rwa [hpos_eq] at h
  have hcont_dv : ∀ (e : ℝ × ℝ) (i : Fin 2),
      ContinuousOn (fun x : Coord => fderiv ℝ (fun z => p.train.v x.1 z i) x.2 e)
        {x : Coord | 0 < x.1} := by
    intro e i
    have h := (FlatBvWL.gD_contDiffOn p.train i e).continuousOn
    rw [hpos_eq] at h
    exact h.congr fun x hx => (FlatBvWL.gD_eq p.train i e hx).symm
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_finsetSum Finset.univ fun i _ => ?_
    have hφ := hΨ.smooth i
    have hφ0 : IsCoordTest (cpd 0 (fun y => Ψ y i)) := planarTest_isCoordTest_partial hφ (cdir 0)
    have hφ11 : IsCoordTest (cpd 1 (cpd 1 (fun y => Ψ y i))) :=
      planarTest_isCoordTest_partial (planarTest_isCoordTest_partial hφ (cdir 1)) (cdir 1)
    have hφ22 : IsCoordTest (cpd 2 (cpd 2 (fun y => Ψ y i))) :=
      planarTest_isCoordTest_partial (planarTest_isCoordTest_partial hφ (cdir 2)) (cdir 2)
    have I0 := hint_pair hZ hZ_per hZ_L2 i hφ0 (A := fun _ => -1) continuousOn_const
    have I1 := hint_pair hZ hZ_per hZ_L2 i hφ11 (A := fun _ => -p.ν) continuousOn_const
    have I2 := hint_pair hZ hZ_per hZ_L2 i hφ22 (A := fun _ => -p.ν) continuousOn_const
    refine ((I0.add I1).add I2).congr (Eventually.of_forall fun x => ?_)
    unfold meridTranspose cpd
    simp only [Pi.add_apply]
    push_cast; ring
  · unfold cdot
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    have hφ := hΨ.smooth i
    have J1 := hint_pair hZq hZq_per hZq_L2 i hφ (hcont_v 0)
    have J2 := hint_pair hZη hZη_per hZη_L2 i hφ (hcont_v 1)
    have J3 := hint_pair hZ hZ_per hZ_L2 0 hφ (hcont_dv (1, 0) i)
    have J4 := hint_pair hZ hZ_per hZ_L2 1 hφ (hcont_dv (0, 1) i)
    refine (((J1.add J2).add J3).add J4).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, flatBv, WithLp.ofLp_toLp]
    push_cast; ring
  · unfold cdot
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    simpa using hint_pair hg hg_per hg_loc i (hΨ.smooth i) (A := fun _ => 1) continuousOn_const

private def mulTime (β : ℝ → ℝ) (Ψ : Coord → Fin 2 → ℝ) : Coord → Fin 2 → ℝ :=
  fun x i => β x.1 * Ψ x i

private lemma cpd_mulTime_scalar {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    cpd 0 (fun y => β y.1 * φ y) x = deriv β x.1 * φ x + β x.1 * cpd 0 φ x ∧
      cpd 1 (fun y => β y.1 * φ y) x = β x.1 * cpd 1 φ x ∧
      cpd 2 (fun y => β y.1 * φ y) x = β x.1 * cpd 2 φ x := by
  have hf1 : HasFDerivAt (fun y : Coord => y.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x := hasFDerivAt_fst
  have hdβ : HasFDerivAt (fun y : Coord => β y.1)
      (deriv β x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    ((hβ.contDiffAt.differentiableAt (by simp)).hasDerivAt).comp_hasFDerivAt x hf1
  have hdφ : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hmul : fderiv ℝ (fun y : Coord => β y.1 * φ y) x =
      β x.1 • fderiv ℝ φ x + φ x • (deriv β x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) :=
    (hdβ.mul hdφ).fderiv
  have hv : ∀ v : Coord, fderiv ℝ (fun y : Coord => β y.1 * φ y) x v =
      β x.1 * fderiv ℝ φ x v + φ x * (deriv β x.1 * v.1) := by
    intro v; rw [hmul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · change fderiv ℝ (fun y : Coord => β y.1 * φ y) x (cdir 0) =
      deriv β x.1 * φ x + β x.1 * cpd 0 φ x
    rw [hv, show (cdir 0).1 = 1 from rfl]; unfold cpd; ring
  · change fderiv ℝ (fun y : Coord => β y.1 * φ y) x (cdir 1) = β x.1 * cpd 1 φ x
    rw [hv, show (cdir 1).1 = 0 from rfl]; unfold cpd; ring
  · change fderiv ℝ (fun y : Coord => β y.1 * φ y) x (cdir 2) = β x.1 * cpd 2 φ x
    rw [hv, show (cdir 2).1 = 0 from rfl]; unfold cpd; ring

private lemma isPlanarSolTest_mulTime {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    IsPlanarSolTest (mulTime β Ψ) where
  smooth i := ⟨(hβ.comp contDiff_fst).mul (hΨ.smooth i).smooth,
    (hΨ.smooth i).compact.mul_left,
    tsupport_mul_subset_right.trans (hΨ.smooth i).supp⟩
  div_free x := by
    have h0 := (cpd_mulTime_scalar hβ (hΨ.smooth 0).smooth x).2.1
    have h1 := (cpd_mulTime_scalar hβ (hΨ.smooth 1).smooth x).2.2
    change cpd 1 (fun y => β y.1 * Ψ y 0) x + cpd 2 (fun y => β y.1 * Ψ y 1) x = 0
    rw [h0, h1, ← mul_add, hΨ.div_free x, mul_zero]

private lemma meridTranspose_mulTime (ν : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) (x : Coord) (i : Fin 2) :
    meridTranspose ν (mulTime β Ψ) x i =
      (β x.1 : ℂ) * meridTranspose ν Ψ x i - ((deriv β x.1 * Ψ x i : ℝ) : ℂ) := by
  have hφ := (hΨ.smooth i).smooth
  have hφ1 : ContDiff ℝ ∞ (cpd 1 (fun z => Ψ z i)) :=
    (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 1)).smooth
  have hφ2 : ContDiff ℝ ∞ (cpd 2 (fun z => Ψ z i)) :=
    (planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 2)).smooth
  have hc0 := (cpd_mulTime_scalar hβ hφ x).1
  have hc1_fun : (fun y => cpd 1 (fun z => β z.1 * Ψ z i) y) =
      fun y => β y.1 * cpd 1 (fun z => Ψ z i) y :=
    funext fun y => (cpd_mulTime_scalar hβ hφ y).2.1
  have hc2_fun : (fun y => cpd 2 (fun z => β z.1 * Ψ z i) y) =
      fun y => β y.1 * cpd 2 (fun z => Ψ z i) y :=
    funext fun y => (cpd_mulTime_scalar hβ hφ y).2.2
  have hc11 := (cpd_mulTime_scalar hβ hφ1 x).2.1
  have hc22 := (cpd_mulTime_scalar hβ hφ2 x).2.2
  unfold meridTranspose mulTime
  rw [hc0, hc1_fun, hc2_fun, hc11, hc22]
  push_cast; ring

private def seamBump0 : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def βM (s₀ ε s : ℝ) : ℝ := seamBump0 ((s - s₀) / ε)
private def βL (s₀ ε s : ℝ) : ℝ := if s < s₀ then 1 - βM s₀ ε s else 0
private def βR (s₀ ε s : ℝ) : ℝ := if s₀ < s then 1 - βM s₀ ε s else 0

private lemma βM_eq_one_of_abs_le {s₀ ε s : ℝ} (hε : 0 < ε) (hs : |s - s₀| ≤ ε / 2) :
    βM s₀ ε s = 1 := by
  apply seamBump0.one_of_mem_closedBall
  dsimp [seamBump0]
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hε]
  exact (div_le_iff₀ hε).2 (by linarith)

private lemma βM_eq_zero_of_abs_ge {s₀ ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ |s - s₀|) :
    βM s₀ ε s = 0 := by
  apply seamBump0.zero_of_le_dist
  dsimp [seamBump0]
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hε]
  exact (one_le_div hε).2 hs

private lemma contDiff_βM (s₀ ε : ℝ) : ContDiff ℝ ∞ (βM s₀ ε) :=
  seamBump0.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)

private lemma contDiff_βL (s₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (βL s₀ ε) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < s₀ + ε / 2
  · have hc1 : ContDiff ℝ ∞ (fun t : ℝ => (1 : ℝ) - βM s₀ ε t) :=
      contDiff_const.sub (contDiff_βM s₀ ε)
    refine (hc1.contDiffAt (x := s)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
    by_cases ht0 : t < s₀
    · simp [βL, ht0]
    · rw [not_lt] at ht0
      have habs : |t - s₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith [mem_Iio.1 ht]⟩
      simp [βL, not_lt.2 ht0, βM_eq_one_of_abs_le hε habs]
  · rw [not_lt] at hs
    have hs' : s₀ - ε / 2 < s := by linarith
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs'] with t ht
    by_cases ht0 : t < s₀
    · have habs : |t - s₀| ≤ ε / 2 := abs_le.2 ⟨by linarith [mem_Ioi.1 ht], by linarith⟩
      simp [βL, ht0, βM_eq_one_of_abs_le hε habs]
    · simp [βL, ht0]

private lemma contDiff_βR (s₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (βR s₀ ε) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s₀ - ε / 2 < s
  · have hc1 : ContDiff ℝ ∞ (fun t : ℝ => (1 : ℝ) - βM s₀ ε t) :=
      contDiff_const.sub (contDiff_βM s₀ ε)
    refine (hc1.contDiffAt (x := s)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    by_cases ht0 : s₀ < t
    · simp [βR, ht0]
    · rw [not_lt] at ht0
      have habs : |t - s₀| ≤ ε / 2 := abs_le.2 ⟨by linarith [mem_Ioi.1 ht], by linarith⟩
      simp [βR, not_lt.2 ht0, βM_eq_one_of_abs_le hε habs]
  · rw [not_lt] at hs
    have hs' : s < s₀ + ε / 2 := by linarith
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hs'] with t ht
    by_cases ht0 : s₀ < t
    · have habs : |t - s₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith [mem_Iio.1 ht]⟩
      simp [βR, ht0, βM_eq_one_of_abs_le hε habs]
    · simp [βR, ht0]

private lemma β_partition_sum (s₀ : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    βL s₀ ε s + βR s₀ ε s + βM s₀ ε s = 1 := by
  rcases lt_trichotomy s s₀ with hlt | heq | hgt
  · have hnot : ¬ s₀ < s := not_lt.2 hlt.le
    simp [βL, βR, hlt, hnot]
  · subst heq
    have h1 : βM s ε s = 1 := βM_eq_one_of_abs_le hε (by simp; positivity)
    simp [βL, βR]; exact h1
  · have hnot : ¬ s < s₀ := not_lt.2 hgt.le
    simp [βL, βR, hgt, hnot]

private lemma glue_equation_at_seam (p : Params) {a_dom s₀ b_dom : ℝ}
    (ha_pos : 0 < a_dom) (has₀ : a_dom < s₀) (hs₀b : s₀ < b_dom)
    {Z Zq Zη g : CProf}
    (hZ : StronglyMeasurable Z) (hZq : StronglyMeasurable Zq) (hZη : StronglyMeasurable Zη)
    (hg : StronglyMeasurable g)
    (hZ_per : QPeriodic p.c Z) (hZq_per : QPeriodic p.c Zq) (hZη_per : QPeriodic p.c Zη)
    (hg_per : QPeriodic p.c g)
    (hZ_loc : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, sliceH1Norm p.c Z Zq Zη s) < ⊤)
    (hg_loc : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun y => g (s, y))) < ⊤)
    (hZ_s₀_L2 : MemLp (fun y => Z (s₀, y)) 2 (volume.restrict (B0579.cell p.c)))
    (hZ_cont_s₀ : Tendsto (fun s => cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y))) (𝓝 s₀) (𝓝 0))
    (heq_L : ∀ Φ, IsPlanarSolTest Φ →
      (∀ i, tsupport (fun x => Φ x i) ⊆ Ioo a_dom s₀ ×ˢ univ) →
      ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i +
          cdot (flatBv p.train Z Zq Zη) Φ x) = ∫ x, cdot g Φ x)
    (heq_R : ∀ Φ, IsPlanarSolTest Φ →
      (∀ i, tsupport (fun x => Φ x i) ⊆ Ioo s₀ b_dom ×ˢ univ) →
      ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i +
          cdot (flatBv p.train Z Zq Zη) Φ x) = ∫ x, cdot g Φ x) :
    ∀ Ψ, IsPlanarSolTest Ψ →
      (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo a_dom b_dom ×ˢ univ) →
      ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train Z Zq Zη) Ψ x) = ∫ x, cdot g Ψ x := by
  intro Ψ hΨ hΨ_supp
  have hc : 0 < p.c := p.c_pos
  obtain ⟨hInt_M, hInt_B, hInt_G⟩ :=
    integrable_pde_terms p hZ hZq hZη hg hZ_per hZq_per hZη_per hg_per hZ_loc hg_loc hΨ
  let D_val : ℂ :=
    (∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i + cdot (flatBv p.train Z Zq Zη) Ψ x)) -
      ∫ x, cdot g Ψ x
  suffices hD0 : D_val = 0 by exact sub_eq_zero.1 hD0
  let F_Ψ : Coord → ℂ := fun x =>
    ∑ i : Fin 2, Z x i * meridTranspose p.ν Ψ x i + cdot (flatBv p.train Z Zq Zη) Ψ x - cdot g Ψ x
  have hF_int : Integrable F_Ψ volume := (hInt_M.add hInt_B).sub hInt_G
  have hD_eq : D_val = ∫ x, F_Ψ x :=
    (integral_sub (hInt_M.add hInt_B) hInt_G).symm
  obtain ⟨a0, b0', R0, ha0, hab0, hR0, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 0)
  obtain ⟨a1, b1', R1, ha1, hab1, hR1, hbox1⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 1)
  let R : ℝ := max R0 R1
  have hR : 0 < R := lt_of_lt_of_le hR0 (le_max_left R0 R1)
  have hΨ_R : ∀ (i : Fin 2) (x : Coord), (R < |x.2.1| ∨ R < |x.2.2|) → Ψ x i = 0 := by
    intro i x hx
    fin_cases i
    · refine (hbox0 x ?_).1
      rcases hx with hq | hη
      · exact Or.inr (Or.inl ((le_max_left R0 R1).trans_lt hq))
      · exact Or.inr (Or.inr ((le_max_left R0 R1).trans_lt hη))
    · refine (hbox1 x ?_).1
      rcases hx with hq | hη
      · exact Or.inr (Or.inl ((le_max_right R0 R1).trans_lt hq))
      · exact Or.inr (Or.inr ((le_max_right R0 R1).trans_lt hη))
  let δ₀ : ℝ := min (s₀ - a_dom) (b_dom - s₀) / 2
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  -- Jump functional J(s) = ∑_i ∫_{cell} Z(s, y)_i * qPeriodize(Ψ_i)(s, y)
  let J : ℝ → ℂ := fun s => ∑ i : Fin 2,
    ∫ y in B0579.cell p.c, Z (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)
  -- Step A: For every ε ∈ (0, δ₀], D_val = I_bulk(ε) - I_jump(ε)
  have hDecomp : ∀ ε : ℝ, 0 < ε → ε ≤ δ₀ →
      D_val = (∫ x, (βM s₀ ε x.1 : ℂ) * F_Ψ x) -
        ∫ s in Icc (s₀ - ε) (s₀ + ε), ((deriv (βM s₀ ε) s : ℝ) : ℂ) * J s := by
    intro ε hε hεδ
    have ha_ε : a_dom < s₀ - ε := by
      have : 2 * δ₀ ≤ s₀ - a_dom := by dsimp [δ₀]; linarith [min_le_left (s₀ - a_dom) (b_dom - s₀)]
      linarith
    have hb_ε : s₀ + ε < b_dom := by
      have : 2 * δ₀ ≤ b_dom - s₀ := by dsimp [δ₀]; linarith [min_le_right (s₀ - a_dom) (b_dom - s₀)]
      linarith
    have hs_pos : 0 < s₀ - ε := ha_pos.trans ha_ε
    let ΨL := mulTime (βL s₀ ε) Ψ
    let ΨR := mulTime (βR s₀ ε) Ψ
    let ΨM := mulTime (βM s₀ ε) Ψ
    have hΨL_test : IsPlanarSolTest ΨL := isPlanarSolTest_mulTime (contDiff_βL s₀ hε) hΨ
    have hΨR_test : IsPlanarSolTest ΨR := isPlanarSolTest_mulTime (contDiff_βR s₀ hε) hΨ
    have hΨM_test : IsPlanarSolTest ΨM := isPlanarSolTest_mulTime (contDiff_βM s₀ ε) hΨ
    have hΨL_supp : ∀ i, tsupport (fun x => ΨL x i) ⊆ Ioo a_dom s₀ ×ˢ univ := by
      intro i
      have hsub1 : tsupport (fun x => ΨL x i) ⊆ tsupport (fun x => Ψ x i) :=
        tsupport_mul_subset_right
      have hsub2 : tsupport (fun x => ΨL x i) ⊆ Iic (s₀ - ε / 2) ×ˢ univ := by
        refine closure_minimal ?_ (isClosed_Iic.prod isClosed_univ)
        intro x hx
        rw [Function.mem_support] at hx
        refine ⟨?_, trivial⟩
        by_contra hgt; rw [mem_Iic, not_le] at hgt
        apply hx
        by_cases hlt : x.1 < s₀
        · have habs : |x.1 - s₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
          simp [ΨL, mulTime, βL, hlt, βM_eq_one_of_abs_le hε habs]
        · simp [ΨL, mulTime, βL, hlt]
      intro x hx
      exact ⟨⟨(hΨ_supp i (hsub1 hx)).1.1,
        lt_of_le_of_lt (hsub2 hx).1 (by linarith)⟩, trivial⟩
    have hΨR_supp : ∀ i, tsupport (fun x => ΨR x i) ⊆ Ioo s₀ b_dom ×ˢ univ := by
      intro i
      have hsub1 : tsupport (fun x => ΨR x i) ⊆ tsupport (fun x => Ψ x i) :=
        tsupport_mul_subset_right
      have hsub2 : tsupport (fun x => ΨR x i) ⊆ Ici (s₀ + ε / 2) ×ˢ univ := by
        refine closure_minimal ?_ (isClosed_Ici.prod isClosed_univ)
        intro x hx
        rw [Function.mem_support] at hx
        refine ⟨?_, trivial⟩
        by_contra hlt; rw [mem_Ici, not_le] at hlt
        apply hx
        by_cases hgt : s₀ < x.1
        · have habs : |x.1 - s₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
          simp [ΨR, mulTime, βR, hgt, βM_eq_one_of_abs_le hε habs]
        · simp [ΨR, mulTime, βR, hgt]
      intro x hx
      exact ⟨⟨lt_of_lt_of_le (by linarith) (hsub2 hx).1,
        (hΨ_supp i (hsub1 hx)).1.2⟩, trivial⟩
    obtain ⟨hIL_M, hIL_B, hIL_G⟩ :=
      integrable_pde_terms p hZ hZq hZη hg hZ_per hZq_per hZη_per hg_per hZ_loc hg_loc hΨL_test
    obtain ⟨hIR_M, hIR_B, hIR_G⟩ :=
      integrable_pde_terms p hZ hZq hZη hg hZ_per hZq_per hZη_per hg_per hZ_loc hg_loc hΨR_test
    obtain ⟨hIM_M, hIM_B, hIM_G⟩ :=
      integrable_pde_terms p hZ hZq hZη hg hZ_per hZq_per hZη_per hg_per hZ_loc hg_loc hΨM_test
    have hL0 : ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨL x i +
        cdot (flatBv p.train Z Zq Zη) ΨL x - cdot g ΨL x) = 0 :=
      (integral_sub (hIL_M.add hIL_B) hIL_G).trans
        (sub_eq_zero.2 (heq_L ΨL hΨL_test hΨL_supp))
    have hR0 : ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨR x i +
        cdot (flatBv p.train Z Zq Zη) ΨR x - cdot g ΨR x) = 0 :=
      (integral_sub (hIR_M.add hIR_B) hIR_G).trans
        (sub_eq_zero.2 (heq_R ΨR hΨR_test hΨR_supp))
    -- Pointwise identity F_Ψ = F_{ΨL} + F_{ΨR} + F_{ΨM}
    have hF_split : ∀ x : Coord, F_Ψ x =
        (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨL x i +
          cdot (flatBv p.train Z Zq Zη) ΨL x - cdot g ΨL x) +
        (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨR x i +
          cdot (flatBv p.train Z Zq Zη) ΨR x - cdot g ΨR x) +
        (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨM x i +
          cdot (flatBv p.train Z Zq Zη) ΨM x - cdot g ΨM x) := by
      intro x
      have hpart := β_partition_sum s₀ hε x.1
      have hΨ_sum : Ψ = fun y i => ΨL y i + ΨR y i + ΨM y i := by
        funext y i
        have hp := β_partition_sum s₀ hε y.1
        dsimp [ΨL, ΨR, ΨM, mulTime]
        calc Ψ y i = 1 * Ψ y i := (one_mul _).symm
          _ = (βL s₀ ε y.1 + βR s₀ ε y.1 + βM s₀ ε y.1) * Ψ y i := by rw [hp]
          _ = _ := by ring
      have hMT_sum : ∀ i : Fin 2, meridTranspose p.ν Ψ x i =
          meridTranspose p.ν ΨL x i + meridTranspose p.ν ΨR x i + meridTranspose p.ν ΨM x i := by
        intro i
        have hL_mt := meridTranspose_mulTime p.ν (contDiff_βL s₀ hε) hΨ x i
        have hR_mt := meridTranspose_mulTime p.ν (contDiff_βR s₀ hε) hΨ x i
        have hM_mt := meridTranspose_mulTime p.ν (contDiff_βM s₀ ε) hΨ x i
        have hd_sum : deriv (βL s₀ ε) x.1 + deriv (βR s₀ ε) x.1 + deriv (βM s₀ ε) x.1 = 0 := by
          have hdL : HasDerivAt (βL s₀ ε) (deriv (βL s₀ ε) x.1) x.1 :=
            (((contDiff_βL s₀ hε).contDiffAt (x := x.1)).differentiableAt (by simp)).hasDerivAt
          have hdR : HasDerivAt (βR s₀ ε) (deriv (βR s₀ ε) x.1) x.1 :=
            (((contDiff_βR s₀ hε).contDiffAt (x := x.1)).differentiableAt (by simp)).hasDerivAt
          have hdM : HasDerivAt (βM s₀ ε) (deriv (βM s₀ ε) x.1) x.1 :=
            (((contDiff_βM s₀ ε).contDiffAt (x := x.1)).differentiableAt (by simp)).hasDerivAt
          have hd1 : HasDerivAt (fun s => βL s₀ ε s + βR s₀ ε s + βM s₀ ε s)
              (deriv (βL s₀ ε) x.1 + deriv (βR s₀ ε) x.1 + deriv (βM s₀ ε) x.1) x.1 :=
            (hdL.add hdR).add hdM
          have hd_const : HasDerivAt (fun s => βL s₀ ε s + βR s₀ ε s + βM s₀ ε s) 0 x.1 := by
            simpa [funext (β_partition_sum s₀ hε)] using hasDerivAt_const x.1 (1 : ℝ)
          exact hd1.unique hd_const
        change meridTranspose p.ν Ψ x i =
          meridTranspose p.ν (mulTime (βL s₀ ε) Ψ) x i +
            meridTranspose p.ν (mulTime (βR s₀ ε) Ψ) x i +
            meridTranspose p.ν (mulTime (βM s₀ ε) Ψ) x i
        rw [hL_mt, hR_mt, hM_mt]
        calc meridTranspose p.ν Ψ x i
            = (1 : ℂ) * meridTranspose p.ν Ψ x i - ((0 * Ψ x i : ℝ) : ℂ) := by simp
          _ = ((βL s₀ ε x.1 + βR s₀ ε x.1 + βM s₀ ε x.1 : ℝ) : ℂ) * meridTranspose p.ν Ψ x i -
                (((deriv (βL s₀ ε) x.1 + deriv (βR s₀ ε) x.1 + deriv (βM s₀ ε) x.1) * Ψ x i : ℝ) : ℂ) := by
              rw [hpart, hd_sum]; norm_num
          _ = _ := by push_cast; ring
      dsimp only [F_Ψ, cdot, ΨL, ΨR, ΨM, mulTime]
      simp only [Fin.sum_univ_two, hMT_sum 0, hMT_sum 1]
      have hpC : ((βL s₀ ε x.1 : ℂ) + (βR s₀ ε x.1 : ℂ) + (βM s₀ ε x.1 : ℂ)) = 1 := by
        exact_mod_cast hpart
      calc Z x 0 * (meridTranspose p.ν ΨL x 0 + meridTranspose p.ν ΨR x 0 + meridTranspose p.ν ΨM x 0) +
            Z x 1 * (meridTranspose p.ν ΨL x 1 + meridTranspose p.ν ΨR x 1 + meridTranspose p.ν ΨM x 1) +
            (flatBv p.train Z Zq Zη x 0 * (Ψ x 0 : ℂ) + flatBv p.train Z Zq Zη x 1 * (Ψ x 1 : ℂ)) -
            (g x 0 * (Ψ x 0 : ℂ) + g x 1 * (Ψ x 1 : ℂ))
          = Z x 0 * (meridTranspose p.ν ΨL x 0 + meridTranspose p.ν ΨR x 0 + meridTranspose p.ν ΨM x 0) +
            Z x 1 * (meridTranspose p.ν ΨL x 1 + meridTranspose p.ν ΨR x 1 + meridTranspose p.ν ΨM x 1) +
            ((βL s₀ ε x.1 : ℂ) + (βR s₀ ε x.1 : ℂ) + (βM s₀ ε x.1 : ℂ)) *
              (flatBv p.train Z Zq Zη x 0 * (Ψ x 0 : ℂ) + flatBv p.train Z Zq Zη x 1 * (Ψ x 1 : ℂ) -
                (g x 0 * (Ψ x 0 : ℂ) + g x 1 * (Ψ x 1 : ℂ))) := by
              rw [hpC, one_mul]; ring
        _ = _ := by push_cast; ring
    have hIL_tot : Integrable (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν ΨL x i +
        cdot (flatBv p.train Z Zq Zη) ΨL x - cdot g ΨL x) volume := (hIL_M.add hIL_B).sub hIL_G
    have hIR_tot : Integrable (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν ΨR x i +
        cdot (flatBv p.train Z Zq Zη) ΨR x - cdot g ΨR x) volume := (hIR_M.add hIR_B).sub hIR_G
    have hIM_tot : Integrable (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν ΨM x i +
        cdot (flatBv p.train Z Zq Zη) ΨM x - cdot g ΨM x) volume := (hIM_M.add hIM_B).sub hIM_G
    have hD_M : D_val = ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨM x i +
        cdot (flatBv p.train Z Zq Zη) ΨM x - cdot g ΨM x) := by
      have hsplit_int : ∫ x, F_Ψ x =
          ((∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨL x i +
            cdot (flatBv p.train Z Zq Zη) ΨL x - cdot g ΨL x)) +
          ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨR x i +
            cdot (flatBv p.train Z Zq Zη) ΨR x - cdot g ΨR x)) +
          ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν ΨM x i +
            cdot (flatBv p.train Z Zq Zη) ΨM x - cdot g ΨM x) :=
        (integral_congr_ae (Eventually.of_forall hF_split)).trans
          ((integral_add (hIL_tot.add hIR_tot) hIM_tot).trans
            (congrArg (· + _) (integral_add hIL_tot hIR_tot)))
      rw [hD_eq, hsplit_int, hL0, hR0, add_zero, zero_add]
    -- Expand ΨM integrand into βM * F_Ψ - jump
    have hM_expand : (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν ΨM x i +
        cdot (flatBv p.train Z Zq Zη) ΨM x - cdot g ΨM x) =
        fun x => (βM s₀ ε x.1 : ℂ) * F_Ψ x -
          ∑ i : Fin 2, Z x i * ((deriv (βM s₀ ε) x.1 * Ψ x i : ℝ) : ℂ) := by
      funext x
      have h0 := meridTranspose_mulTime p.ν (contDiff_βM s₀ ε) hΨ x 0
      have h1 := meridTranspose_mulTime p.ν (contDiff_βM s₀ ε) hΨ x 1
      dsimp only [F_Ψ, cdot, ΨM]
      simp only [Fin.sum_univ_two, h0, h1, mulTime]
      push_cast; ring
    have hbulk_int : Integrable (fun x => (βM s₀ ε x.1 : ℂ) * F_Ψ x) volume := by
      refine hF_int.bdd_mul (c := 1)
        ((Complex.continuous_ofReal.comp ((contDiff_βM s₀ ε).continuous.comp continuous_fst)).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      unfold βM
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg seamBump0.nonneg]
      exact seamBump0.le_one
    -- Unfold jump integral via qPeriodize on Icc (s₀ - ε) (s₀ + ε)
    have hab_ε : s₀ - ε ≤ s₀ + ε := by linarith
    have hZ_i_loc : ∀ i : Fin 2, (∫⁻ s in Icc (s₀ - ε) (s₀ + ε),
        eLpNorm (fun z => Z (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      refine (lintegral_mono fun s => ?_).trans_lt (hZ_loc (s₀ - ε) (s₀ + ε) hs_pos)
      refine (eLpNorm_mono_enorm fun z => ?_).trans (le_self_add.trans le_self_add)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact_mod_cast PiLp.norm_apply_le (Z (s, z)) i
    have hα_supp : ∀ (i : Fin 2) (x : Coord),
        (x.1 ∉ Icc (s₀ - ε) (s₀ + ε) ∨ R < |x.2.1| ∨ R < |x.2.2|) →
        deriv (βM s₀ ε) x.1 * Ψ x i = 0 := by
      intro i x hx
      rcases hx with hs_out | hR_out
      · have hd0 : deriv (βM s₀ ε) x.1 = 0 := by
          have habs_gt : ε < |x.1 - s₀| := by
            by_contra hle; rw [not_lt] at hle
            exact hs_out ⟨by linarith [(abs_le.1 hle).1], by linarith [(abs_le.1 hle).2]⟩
          have hev : βM s₀ ε =ᶠ[𝓝 x.1] 0 := by
            have hopen : IsOpen {t : ℝ | ε < |t - s₀|} :=
              isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
            filter_upwards [hopen.mem_nhds habs_gt] with t ht
            exact βM_eq_zero_of_abs_ge hε (le_of_lt ht)
          simpa using hev.deriv_eq
        rw [hd0, zero_mul]
      · rw [hΨ_R i x hR_out, mul_zero]
    have hα_cont : ∀ i : Fin 2, Continuous (fun x : Coord => deriv (βM s₀ ε) x.1 * Ψ x i) :=
      fun i => ((ContDiff.continuous_deriv (contDiff_βM s₀ ε) (by simp)).comp
        continuous_fst).mul (hΨ.smooth i).smooth.continuous
    have hZi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => Z x i) volume :=
      fun i => ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hZ).aestronglyMeasurable
    have hZi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        Z (qShift p.c x) i = Z x i :=
      fun i => hZ_per.mono fun _ hx => congrArg (fun v => v i) hx
    obtain ⟨hJ0_int, hJ0_cell, hJ0_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
        hc hs_pos hab_ε hR (hZi_meas 0) (hZi_per 0) (hZ_i_loc 0) (hα_cont 0) (hα_supp 0)
    obtain ⟨hJ1_int, hJ1_cell, hJ1_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
        hc hs_pos hab_ε hR (hZi_meas 1) (hZi_per 1) (hZ_i_loc 1) (hα_cont 1) (hα_supp 1)
    have hqP_pull : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane),
        TailPeriodizeAux.qPeriodize p.c (fun x => deriv (βM s₀ ε) x.1 * Ψ x i) s y =
          deriv (βM s₀ ε) s * TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y := by
      intro i s y
      unfold TailPeriodizeAux.qPeriodize
      dsimp only
      exact tsum_mul_left
    have hcell_fub : ∀ {F : Coord → ℂ},
        IntegrableOn F (Icc (s₀ - ε) (s₀ + ε) ×ˢ B0579.cell p.c) volume →
        IntegrableOn (fun s : ℝ => ∫ y in B0579.cell p.c, F (s, y)) (Icc (s₀ - ε) (s₀ + ε)) volume := by
      intro F hF
      have hF' : Integrable F
          ((volume.restrict (Icc (s₀ - ε) (s₀ + ε))).prod (volume.restrict (B0579.cell p.c))) := by
        rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hF'.integral_prod_left
    have hs0_int := hcell_fub hJ0_cell
    have hs1_int := hcell_fub hJ1_cell
    dsimp only at hs0_int hs1_int
    have hjump_sum_eq : (fun x : Coord => ∑ i : Fin 2, Z x i * ((deriv (βM s₀ ε) x.1 * Ψ x i : ℝ) : ℂ)) =
        fun x => Z x 0 * ((deriv (βM s₀ ε) x.1 * Ψ x 0 : ℝ) : ℂ) +
          Z x 1 * ((deriv (βM s₀ ε) x.1 * Ψ x 1 : ℝ) : ℂ) := by
      funext x; rw [Fin.sum_univ_two]
    have hjump_int : Integrable (fun x : Coord =>
        ∑ i : Fin 2, Z x i * ((deriv (βM s₀ ε) x.1 * Ψ x i : ℝ) : ℂ)) volume :=
      hjump_sum_eq ▸ (hJ0_int.add hJ1_int)
    rw [hD_M, hM_expand, integral_sub hbulk_int hjump_int]
    congr 1
    rw [hjump_sum_eq, integral_add hJ0_int hJ1_int, hJ0_eq, hJ1_eq, ← integral_add hs0_int hs1_int]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    dsimp only [J]
    rw [Fin.sum_univ_two, mul_add]
    congr 1 <;> {
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [hqP_pull]
      push_cast; ring
    }
  -- Step B: Continuity of J at s₀
  have hJ_cont : Tendsto J (𝓝 s₀) (𝓝 (J s₀)) := by
    let B_R : Set B0579.Plane := Ico (-(p.c / 2)) (p.c / 2) ×ˢ Icc (-R) R
    have hBR_meas : MeasurableSet B_R := measurableSet_Ico.prod measurableSet_Icc
    have hBR_sub : B_R ⊆ B0579.cell p.c := prod_mono Subset.rfl (subset_univ _)
    have hBR_fin : volume B_R < ⊤ := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top (by simp [Real.volume_Ico]) (by simp [Real.volume_Icc])
    obtain ⟨K, hK⟩ := exists_nat_gt ((p.c / 2 + R) / p.c + 1)
    let Ik : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
    have hqP_zero_outside : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane),
        y ∈ B0579.cell p.c \ B_R →
        TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y = 0 := by
      intro i s y ⟨hy_cell, hy_notB⟩
      have hnot_η : y.2 ∉ Icc (-R) R := fun hη => hy_notB ⟨hy_cell.1, hη⟩
      have hη_gt : R < |y.2| := by by_contra hle; rw [not_lt] at hle; exact hnot_η (abs_le.1 hle)
      unfold TailPeriodizeAux.qPeriodize
      simp_rw [hΨ_R i (s, (y.1 + (_ : ℝ) * p.c, y.2)) (Or.inr hη_gt)]
      exact tsum_zero
    have hqP_fin : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane), y ∈ B_R →
        TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y =
          ∑ k ∈ Ik, Ψ (s, (y.1 + (k : ℝ) * p.c, y.2)) i := by
      intro i s y hy
      unfold TailPeriodizeAux.qPeriodize
      refine tsum_eq_sum fun k hk => hΨ_R i _ (Or.inl ?_)
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
      have hk_abs : (K : ℝ) + 1 ≤ |(k : ℝ)| := by
        have hk_int : (K : ℤ) + 1 ≤ |k| := by
          rcases hk with h1 | h2
          · rw [abs_of_neg (by omega)]; omega
          · rw [abs_of_nonneg (by omega)]; omega
        exact_mod_cast hk_int
      have hy_abs : |y.1| ≤ p.c / 2 := abs_le.2 ⟨hy.1.1, le_of_lt hy.1.2⟩
      have hKc : p.c / 2 + R + p.c < ((K : ℝ) + 1) * p.c := by
        have h := mul_lt_mul_of_pos_right hK hc
        have hd : ((p.c / 2 + R) / p.c + 1) * p.c = p.c / 2 + R + p.c := by field_simp [hc.ne']
        nlinarith [hc]
      have hkc : ((K : ℝ) + 1) * p.c ≤ |(k : ℝ) * p.c| := by
        rw [abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_right hk_abs hc.le
      have htri : |(k : ℝ) * p.c| - |y.1| ≤ |y.1 + (k : ℝ) * p.c| := by
        have h := abs_sub_abs_le_abs_sub ((k : ℝ) * p.c) (-y.1)
        simpa [sub_neg_eq_add, add_comm] using h
      linarith
    -- Uniform continuity and uniform bound on qPeriodize over B_R
    have hΨ_uc : ∀ i : Fin 2, UniformContinuous (fun x : Coord => Ψ x i) :=
      fun i => (hΨ.smooth i).compact.uniformContinuous_of_continuous (hΨ.smooth i).smooth.continuous
    have hΨ_bdd : ∀ i : Fin 2, ∃ M_i : ℝ, 0 ≤ M_i ∧ ∀ x : Coord, |Ψ x i| ≤ M_i := by
      intro i
      obtain ⟨C_i, hC_i⟩ := (hΨ.smooth i).compact.exists_bound_of_continuousOn
        (hΨ.smooth i).smooth.continuous.continuousOn
      refine ⟨max 0 C_i, le_max_left 0 C_i, fun x => ?_⟩
      by_cases hx : x ∈ tsupport (fun y => Ψ y i)
      · exact (Real.norm_eq_abs _ ▸ hC_i x hx).trans (le_max_right 0 C_i)
      · rw [image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) hx, abs_zero]
        exact le_max_left 0 C_i
    choose M_Ψ hM_Ψ_nn hM_Ψ using hΨ_bdd
    let M_qP : ℝ := (Ik.card : ℝ) * max (M_Ψ 0) (M_Ψ 1)
    have hM_qP_nn : 0 ≤ M_qP := mul_nonneg (Nat.cast_nonneg _) (le_max_of_le_left (hM_Ψ_nn 0))
    have hqP_bdd : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane), y ∈ B_R →
        |TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y| ≤ M_qP := by
      intro i s y hy
      rw [hqP_fin i s y hy]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Ik, |Ψ (s, (y.1 + (k : ℝ) * p.c, y.2)) i|
          ≤ ∑ _ ∈ Ik, max (M_Ψ 0) (M_Ψ 1) := Finset.sum_le_sum fun k _ => by
            fin_cases i
            · exact (hM_Ψ 0 _).trans (le_max_left _ _)
            · exact (hM_Ψ 1 _).trans (le_max_right _ _)
        _ = M_qP := by simp [M_qP]
    have hqP_unif : ∀ (i : Fin 2) {η_tol : ℝ}, 0 < η_tol →
        ∀ᶠ s in 𝓝 s₀, ∀ y ∈ B_R,
          |TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y -
            TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y| ≤ η_tol := by
      intro i η_tol hη_tol
      have hpos_card : 0 < (Ik.card : ℝ) + 1 := by positivity
      obtain ⟨δ_u, hδ_u, hu_mod⟩ := Metric.uniformContinuous_iff.1 (hΨ_uc i)
        (η_tol / ((Ik.card : ℝ) + 1)) (div_pos hη_tol hpos_card)
      filter_upwards [Metric.ball_mem_nhds s₀ hδ_u] with s hs y hy
      rw [hqP_fin i s y hy, hqP_fin i s₀ y hy, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Ik, |Ψ (s, (y.1 + (k : ℝ) * p.c, y.2)) i - Ψ (s₀, (y.1 + (k : ℝ) * p.c, y.2)) i|
          ≤ ∑ _ ∈ Ik, (η_tol / ((Ik.card : ℝ) + 1)) := Finset.sum_le_sum fun k _ => by
            have hd : dist ((s, (y.1 + (k : ℝ) * p.c, y.2)) : Coord)
                (s₀, (y.1 + (k : ℝ) * p.c, y.2)) < δ_u := by
              simpa [Prod.dist_eq] using Metric.mem_ball.1 hs
            exact le_of_lt (Real.dist_eq _ _ ▸ hu_mod hd)
        _ = (Ik.card : ℝ) * (η_tol / ((Ik.card : ℝ) + 1)) := by simp
        _ = η_tol * ((Ik.card : ℝ) / ((Ik.card : ℝ) + 1)) := by ring
        _ ≤ η_tol := mul_le_of_le_one_right hη_tol.le
            ((div_le_one hpos_card).2 (by linarith))
    -- Show each i ∈ Fin 2 summand of J is continuous at s₀
    refine tendsto_finsetSum Finset.univ fun i _ => ?_
    -- Reduce integral over cell p.c to finite-measure box B_R
    have hcell_eq_BR : ∀ s : ℝ,
        ∫ y in B0579.cell p.c, Z (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) =
          ∫ y in B_R, Z (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) := by
      intro s
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (B0579.measurableSet_cell p.c) hBR_sub fun y hy => ?_
      rw [hqP_zero_outside i s y hy, Complex.ofReal_zero, mul_zero]
    simp_rw [hcell_eq_BR]
    -- Integrability of Z(s₀, ·) i on B_R
    have hZ0_BR_int : IntegrableOn (fun y => Z (s₀, y) i) B_R volume := by
      have hm_vec : MemLp (fun y => Z (s₀, y)) 2 (volume.restrict B_R) :=
        hZ_s₀_L2.mono_measure (Measure.restrict_mono hBR_sub le_rfl)
      have hm_comp : MemLp (fun y => Z (s₀, y) i) 2 (volume.restrict B_R) :=
        ((EuclideanSpace.proj (𝕜 := ℂ) i).lipschitzWith.comp_memLp (by simp) hm_vec)
      have : Fact (volume B_R < ⊤) := ⟨hBR_fin⟩
      exact hm_comp.integrable (by norm_num)
    rw [Metric.tendsto_nhds]
    intro tol htol
    let C1 : ℝ := M_qP * ((volume B_R).toReal ^ (1 / (2 : ℝ))) + 1
    have hC1_pos : 0 < C1 := by positivity
    let C2 : ℝ := (∫ y in B_R, ‖Z (s₀, y) i‖) + 1
    have hC2_pos : 0 < C2 :=
      add_pos_of_nonneg_of_pos (integral_nonneg fun _ => norm_nonneg _) zero_lt_one
    have hnear_L2 := (ENNReal.tendsto_nhds_zero.1 hZ_cont_s₀)
      (ENNReal.ofReal (tol / (2 * C1)))
      (ENNReal.ofReal_pos.2 (div_pos htol (mul_pos two_pos hC1_pos)))
    have hnear_qP := hqP_unif i (div_pos htol (mul_pos two_pos hC2_pos))
    filter_upwards [hnear_L2, hnear_qP] with s hs_L2 hs_qP
    -- Integrability of Z(s, ·) i on B_R from hs_L2 < ⊤
    have hZs_memL2 : MemLp (fun y => Z (s, y)) 2 (volume.restrict B_R) := by
      have hd_mem : MemLp (fun y => Z (s, y) - Z (s₀, y)) 2 (volume.restrict B_R) :=
        ⟨(((hZ.comp_measurable measurable_prodMk_left).sub
          (hZ.comp_measurable measurable_prodMk_left)).aestronglyMeasurable),
          (eLpNorm_mono_measure _ (Measure.restrict_mono hBR_sub le_rfl)).trans_lt
            (hs_L2.trans_lt ENNReal.ofReal_lt_top)⟩
      have heq : (fun y => Z (s, y)) = (fun y => Z (s, y) - Z (s₀, y)) + fun y => Z (s₀, y) := by
        funext y; simp
      rw [heq]
      exact hd_mem.add (hZ_s₀_L2.mono_measure (Measure.restrict_mono hBR_sub le_rfl))
    have hZs_BR_int : IntegrableOn (fun y => Z (s, y) i) B_R volume := by
      have hm_comp : MemLp (fun y => Z (s, y) i) 2 (volume.restrict B_R) :=
        ((EuclideanSpace.proj (𝕜 := ℂ) i).lipschitzWith.comp_memLp (by simp) hZs_memL2)
      have : Fact (volume B_R < ⊤) := ⟨hBR_fin⟩
      exact hm_comp.integrable (by norm_num)
    have hqP_cont_y : ∀ t : ℝ, ContinuousOn
        (fun y : B0579.Plane => (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) t y : ℂ)) B_R := by
      intro t
      have hsum_cont : ContinuousOn
          (fun y : B0579.Plane => ∑ k ∈ Ik, (Ψ (t, (y.1 + (k : ℝ) * p.c, y.2)) i : ℂ)) B_R := by
        refine continuousOn_finsetSum Ik fun k _ => ?_
        exact (Complex.continuous_ofReal.comp
          ((hΨ.smooth i).smooth.continuous.comp
            (continuous_const.prodMk ((continuous_fst.add continuous_const).prodMk continuous_snd)))).continuousOn
      exact hsum_cont.congr fun y hy => by simp [hqP_fin i t y hy]
    have hint_s : IntegrableOn (fun y => Z (s, y) i *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) B_R volume :=
      hZs_BR_int.mul_bdd ((hqP_cont_y s).aestronglyMeasurable hBR_meas)
        ((ae_restrict_iff' hBR_meas).2 (Eventually.of_forall fun y hy => by
          simpa [Complex.norm_real, Real.norm_eq_abs] using hqP_bdd i s y hy))
    have hint_s0 : IntegrableOn (fun y => Z (s₀, y) i *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℂ)) B_R volume :=
      hZ0_BR_int.mul_bdd ((hqP_cont_y s₀).aestronglyMeasurable hBR_meas)
        ((ae_restrict_iff' hBR_meas).2 (Eventually.of_forall fun y hy => by
          simpa [Complex.norm_real, Real.norm_eq_abs] using hqP_bdd i s₀ y hy))
    have hint_mid : IntegrableOn (fun y => Z (s₀, y) i *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) B_R volume :=
      hZ0_BR_int.mul_bdd ((hqP_cont_y s).aestronglyMeasurable hBR_meas)
        ((ae_restrict_iff' hBR_meas).2 (Eventually.of_forall fun y hy => by
          simpa [Complex.norm_real, Real.norm_eq_abs] using hqP_bdd i s y hy))
    rw [dist_eq_norm, ← integral_sub hint_s hint_s0]
    have hsplit_int : (fun y => Z (s, y) i *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) -
          Z (s₀, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℂ)) =
        fun y => (Z (s, y) i - Z (s₀, y) i) *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) +
          Z (s₀, y) i *
          ((TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y -
            TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℝ) : ℂ) := by
      funext y; push_cast; ring
    have hint_A : IntegrableOn (fun y => (Z (s, y) i - Z (s₀, y) i) *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) B_R volume :=
      (hint_s.sub hint_mid).congr (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
    have hint_B' : IntegrableOn (fun y => Z (s₀, y) i *
        ((TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y -
          TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℝ) : ℂ)) B_R volume :=
      (hint_mid.sub hint_s0).congr
        (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; push_cast; ring)
    rw [hsplit_int, integral_add hint_A hint_B']
    -- Bound term A via L¹ ≤ L² * vol^(1/2) on B_R
    have hnorm_A : ‖∫ y in B_R, (Z (s, y) i - Z (s₀, y) i) *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)‖ < tol / 2 := by
      have hd_int : IntegrableOn (fun y => ‖Z (s, y) i - Z (s₀, y) i‖) B_R volume :=
        (hZs_BR_int.sub hZ0_BR_int).norm
      have h1 : ‖∫ y in B_R, (Z (s, y) i - Z (s₀, y) i) *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)‖ ≤
          ∫ y in B_R, M_qP * ‖Z (s, y) i - Z (s₀, y) i‖ := by
        refine (norm_integral_le_integral_norm _).trans
          (setIntegral_mono_on hint_A.norm (hd_int.const_mul M_qP) hBR_meas fun y hy => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hqP_bdd i s y hy) (norm_nonneg _)
      have hL1_L2 : ∫ y in B_R, ‖Z (s, y) i - Z (s₀, y) i‖ ≤
          (cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y))).toReal *
            (volume B_R).toReal ^ (1 / (2 : ℝ)) := by
        have hdiff_BR_int : IntegrableOn (fun y => Z (s, y) i - Z (s₀, y) i) B_R volume :=
          hZs_BR_int.sub hZ0_BR_int
        have h_enn : ENNReal.ofReal (∫ y in B_R, ‖Z (s, y) i - Z (s₀, y) i‖) =
            eLpNorm (fun y => Z (s, y) i - Z (s₀, y) i) 1 (volume.restrict B_R) := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hdiff_BR_int,
            eLpNorm_one_eq_lintegral_enorm]
        have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
          (μ := volume.restrict B_R) (by norm_num) hdiff_BR_int.aestronglyMeasurable
        have hexp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / (2 : ℝ)) := by norm_num
        rw [hexp, Measure.restrict_apply_univ] at hH
        have hcomp_le : eLpNorm (fun y => Z (s, y) i - Z (s₀, y) i) 2 (volume.restrict B_R) ≤
            cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y)) := by
          refine (eLpNorm_mono_enorm fun y => ?_).trans
            (eLpNorm_mono_measure _ (Measure.restrict_mono hBR_sub le_rfl))
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
          exact_mod_cast PiLp.norm_apply_le (Z (s, y) - Z (s₀, y)) i
        have hfin_cyl : cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y)) ≠ ⊤ :=
          (hs_L2.trans_lt ENNReal.ofReal_lt_top).ne
        have hfin_rpow : (volume B_R) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBR_fin.ne
        have hle_enn : ENNReal.ofReal (∫ y in B_R, ‖Z (s, y) i - Z (s₀, y) i‖) ≤
            cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y)) * (volume B_R) ^ (1 / (2 : ℝ)) :=
          h_enn.le.trans (hH.trans (mul_le_mul_of_nonneg_right hcomp_le zero_le))
        have htr := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin_cyl hfin_rpow) hle_enn
        rwa [ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _),
          ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at htr
      have hcyl_lt : (cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y))).toReal ≤ tol / (2 * C1) := by
        have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs_L2
        rwa [ENNReal.toReal_ofReal (le_of_lt (div_pos htol (by positivity)))] at htr
      calc ‖∫ y in B_R, (Z (s, y) i - Z (s₀, y) i) *
            (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)‖
          ≤ M_qP * ∫ y in B_R, ‖Z (s, y) i - Z (s₀, y) i‖ := by rw [← integral_const_mul]; exact h1
        _ ≤ M_qP * ((cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y))).toReal *
              (volume B_R).toReal ^ (1 / (2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hL1_L2 hM_qP_nn
        _ = (cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y))).toReal *
              (M_qP * (volume B_R).toReal ^ (1 / (2 : ℝ))) := by ring
        _ ≤ (tol / (2 * C1)) * (M_qP * (volume B_R).toReal ^ (1 / (2 : ℝ))) :=
            mul_le_mul_of_nonneg_right hcyl_lt
              (mul_nonneg hM_qP_nn (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        _ < (tol / (2 * C1)) * C1 := by
            refine mul_lt_mul_of_pos_left ?_ (div_pos htol (by positivity))
            dsimp [C1]; linarith
        _ = tol / 2 := by
            have hne : C1 ≠ 0 := hC1_pos.ne'
            field_simp [hne]
    -- Bound term B via uniform continuity on B_R
    have hnorm_B : ‖∫ y in B_R, Z (s₀, y) i *
        ((TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y -
          TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℝ) : ℂ)‖ < tol / 2 := by
      have h1 : ‖∫ y in B_R, Z (s₀, y) i *
          ((TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y -
            TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℝ) : ℂ)‖ ≤
          ∫ y in B_R, (tol / (2 * C2)) * ‖Z (s₀, y) i‖ := by
        refine (norm_integral_le_integral_norm _).trans
          (setIntegral_mono_on hint_B'.norm (hZ0_BR_int.norm.const_mul _) hBR_meas fun y hy => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hs_qP y hy) (norm_nonneg _)
      calc ‖∫ y in B_R, Z (s₀, y) i *
            ((TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y -
              TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s₀ y : ℝ) : ℂ)‖
          ≤ (tol / (2 * C2)) * ∫ y in B_R, ‖Z (s₀, y) i‖ := by rw [← integral_const_mul]; exact h1
        _ < (tol / (2 * C2)) * C2 := by
            refine mul_lt_mul_of_pos_left ?_ (div_pos htol (mul_pos two_pos hC2_pos))
            dsimp [C2]; linarith
        _ = tol / 2 := by
            have hne : C2 ≠ 0 := hC2_pos.ne'
            field_simp [hne]
    exact (norm_add_le _ _).trans_lt (by linarith)
  -- Step C: Send ε_n = δ₀ / (n + 2) → 0⁺; bulk → 0 by DCT and jump → 0 by FTC + hJ_cont
  let εSeq : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 2)
  have hε_pos : ∀ n, 0 < εSeq n := fun n => div_pos hδ₀ (by positivity)
  have hε_le : ∀ n, εSeq n ≤ δ₀ := fun n => div_le_self hδ₀.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hε_tendsto : Tendsto εSeq atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ₀)).div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    simpa [εSeq] using h
  -- Bulk → 0 by DCT
  have hbulk_zero : Tendsto (fun n => ∫ x, (βM s₀ (εSeq n) x.1 : ℂ) * F_Ψ x) atTop (𝓝 0) := by
    have hnull_s0 : (volume : Measure Coord) (({s₀} : Set ℝ) ×ˢ univ) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    have hae_ne : ∀ᵐ x : Coord, x.1 ≠ s₀ := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => (⟨by simpa using hx, trivial⟩ : x ∈ ({s₀} : Set ℝ) ×ˢ univ)) hnull_s0
    have hae_lim : ∀ᵐ x : Coord,
        Tendsto (fun n => (βM s₀ (εSeq n) x.1 : ℂ) * F_Ψ x) atTop (𝓝 0) := by
      filter_upwards [hae_ne] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hε_tendsto.eventually (gt_mem_nhds (abs_pos.2 (sub_ne_zero.2 hx)))] with n hn
      simp [βM_eq_zero_of_abs_ge (hε_pos n) (le_of_lt hn)]
    simpa using tendsto_integral_of_dominated_convergence (fun x => ‖F_Ψ x‖)
      (fun n => ((Complex.continuous_ofReal.comp
        ((contDiff_βM s₀ (εSeq n)).continuous.comp continuous_fst)).aestronglyMeasurable).mul
        hF_int.aestronglyMeasurable)
      hF_int.norm
      (fun n => Eventually.of_forall fun x => by
        dsimp only [Pi.mul_apply, Function.comp_apply, βM]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg seamBump0.nonneg]
        exact mul_le_of_le_one_left (norm_nonneg _) seamBump0.le_one)
      hae_lim
  -- Jump → 0 by ∫ deriv (βM s₀ ε) = 0 and |deriv (βM s₀ ε)| ≤ C_b / ε on [s₀ - ε, s₀ + ε]
  obtain ⟨C_b0, hC_b0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((ContDiff.continuous_deriv_one seamBump0.contDiff).continuousOn
      (s := Icc (-1 : ℝ) 1))
  let C_b : ℝ := max 0 C_b0
  have hC_b_nn : 0 ≤ C_b := le_max_left 0 C_b0
  have hderiv_bump_bdd : ∀ u : ℝ, |deriv seamBump0 u| ≤ C_b := by
    intro u
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · exact (Real.norm_eq_abs _ ▸ hC_b0 u hu).trans (le_max_right 0 C_b0)
    · have habs : 1 < |u| := by by_contra hle; rw [not_lt] at hle; exact hu (abs_le.1 hle)
      have hev : (seamBump0 : ℝ → ℝ) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {t : ℝ | 1 < |t|} := isOpen_lt continuous_const continuous_abs
        filter_upwards [hopen.mem_nhds habs] with t ht
        apply seamBump0.zero_of_le_dist
        dsimp [seamBump0]; rw [Real.dist_eq, sub_zero]; exact le_of_lt ht
      rw [hev.deriv_eq]; simp [hC_b_nn]
  have hderiv_βM_bdd : ∀ (ε : ℝ), 0 < ε → ∀ s : ℝ, |deriv (βM s₀ ε) s| ≤ C_b / ε := by
    intro ε hε s
    have hd : HasDerivAt (βM s₀ ε) (deriv seamBump0 ((s - s₀) / ε) * ε⁻¹) s := by
      have h1 : HasDerivAt seamBump0 (deriv seamBump0 ((s - s₀) / ε)) ((s - s₀) / ε) :=
        (((seamBump0.contDiff : ContDiff ℝ 1 seamBump0).differentiable (by simp))
          ((s - s₀) / ε)).hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (t - s₀) / ε) ε⁻¹ s := by
        simpa [div_eq_mul_inv] using ((hasDerivAt_id s).sub_const s₀).mul_const ε⁻¹
      exact h1.comp s h2
    rw [hd.deriv, abs_mul, abs_of_pos (inv_pos.2 hε), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hderiv_bump_bdd _) hε.le
  have hint_deriv_zero : ∀ (ε : ℝ), 0 < ε →
      ∫ s in Icc (s₀ - ε) (s₀ + ε), ((deriv (βM s₀ ε) s : ℝ) : ℂ) = 0 := by
    intro ε hε
    have hcont_d : Continuous (deriv (βM s₀ ε)) :=
      ContDiff.continuous_deriv (contDiff_βM s₀ ε) (by simp)
    have hint_r : ∫ s in Icc (s₀ - ε) (s₀ + ε), deriv (βM s₀ ε) s = 0 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s _ => ((contDiff_βM s₀ ε).contDiffAt.differentiableAt (by simp)).hasDerivAt)
          (hcont_d.intervalIntegrable _ _)]
      have hR_end : βM s₀ ε (s₀ + ε) = 0 := βM_eq_zero_of_abs_ge hε (by simp [abs_of_pos hε])
      have hL_end : βM s₀ ε (s₀ - ε) = 0 := βM_eq_zero_of_abs_ge hε (by simp [abs_of_pos hε])
      rw [hR_end, hL_end, sub_self]
    have hcomm := Complex.ofRealCLM.integral_comp_comm
      (μ := volume.restrict (Icc (s₀ - ε) (s₀ + ε)))
      (hcont_d.continuousOn.integrableOn_Icc)
    exact hcomm.trans (by simp [hint_r])
  have hjump_zero : Tendsto (fun n =>
      ∫ s in Icc (s₀ - εSeq n) (s₀ + εSeq n), ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * J s)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro tol htol
    let K_b : ℝ := 2 * C_b + 1
    have hKb_pos : 0 < K_b := by positivity
    obtain ⟨δ_J, hδ_J, hJ_mod⟩ :=
      Metric.mem_nhds_iff.1 (Metric.tendsto_nhds.1 hJ_cont (tol / K_b) (div_pos htol hKb_pos))
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
      (hε_tendsto.eventually (gt_mem_nhds hδ_J))
    refine ⟨N₀, fun n hn => ?_⟩
    have hε := hε_pos n
    have hε_lt : εSeq n < δ_J := hN₀ n hn
    have hd_int : IntegrableOn (fun s => ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ))
        (Icc (s₀ - εSeq n) (s₀ + εSeq n)) volume :=
      (Complex.continuous_ofReal.comp
        (ContDiff.continuous_deriv (contDiff_βM s₀ (εSeq n)) (by simp))).continuousOn.integrableOn_Icc
    have hs_pos : 0 < s₀ - εSeq n := by
      have : 2 * δ₀ ≤ s₀ - a_dom := by dsimp [δ₀]; linarith [min_le_left (s₀ - a_dom) (b_dom - s₀)]
      linarith [hε_le n, ha_pos]
    have hdJ_int : IntegrableOn (fun s => ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * J s)
        (Icc (s₀ - εSeq n) (s₀ + εSeq n)) volume := by
      have hpart_i : ∀ i : Fin 2, IntegrableOn (fun s => ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) *
          ∫ y in B0579.cell p.c, Z (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))
          (Icc (s₀ - εSeq n) (s₀ + εSeq n)) volume := by
        intro i
        have hZi_loc : (∫⁻ s in Icc (s₀ - εSeq n) (s₀ + εSeq n),
            eLpNorm (fun z => Z (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
          refine (lintegral_mono fun s => ?_).trans_lt (hZ_loc _ _ hs_pos)
          refine (eLpNorm_mono_enorm fun z => ?_).trans (le_self_add.trans le_self_add)
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm]; exact_mod_cast PiLp.norm_apply_le (Z (s, z)) i
        have hα_supp : ∀ x : Coord,
            (x.1 ∉ Icc (s₀ - εSeq n) (s₀ + εSeq n) ∨ R < |x.2.1| ∨ R < |x.2.2|) →
            deriv (βM s₀ (εSeq n)) x.1 * Ψ x i = 0 := by
          intro x hx
          rcases hx with hs_out | hR_out
          · have habs_gt : εSeq n < |x.1 - s₀| := by
              by_contra hle; rw [not_lt] at hle
              exact hs_out ⟨by linarith [(abs_le.1 hle).1], by linarith [(abs_le.1 hle).2]⟩
            have hev : βM s₀ (εSeq n) =ᶠ[𝓝 x.1] 0 := by
              have hopen : IsOpen {t : ℝ | εSeq n < |t - s₀|} :=
                isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
              filter_upwards [hopen.mem_nhds habs_gt] with t ht
              exact βM_eq_zero_of_abs_ge hε (le_of_lt ht)
            rw [show deriv (βM s₀ (εSeq n)) x.1 = 0 by simpa using hev.deriv_eq, zero_mul]
          · rw [hΨ_R i x hR_out, mul_zero]
        obtain ⟨_, hcell_i, _⟩ := TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
          hc hs_pos (by linarith) hR
          (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hZ).aestronglyMeasurable)
          (hZ_per.mono fun _ hx => congrArg (fun v => v i) hx)
          hZi_loc
          (((ContDiff.continuous_deriv (contDiff_βM s₀ (εSeq n)) (by simp)).comp continuous_fst).mul
            (hΨ.smooth i).smooth.continuous)
          hα_supp
        have hF' : Integrable
            (fun x : Coord => Z x i *
              (TailPeriodizeAux.qPeriodize p.c (fun y => deriv (βM s₀ (εSeq n)) y.1 * Ψ y i) x.1 x.2 : ℂ))
            ((volume.restrict (Icc (s₀ - εSeq n) (s₀ + εSeq n))).prod
              (volume.restrict (B0579.cell p.c))) := by
          rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
        refine hF'.integral_prod_left.congr (Eventually.of_forall fun s => ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        have hpull : TailPeriodizeAux.qPeriodize p.c (fun y => deriv (βM s₀ (εSeq n)) y.1 * Ψ y i) s y =
            deriv (βM s₀ (εSeq n)) s * TailPeriodizeAux.qPeriodize p.c (fun y => Ψ y i) s y := by
          unfold TailPeriodizeAux.qPeriodize; dsimp only; exact tsum_mul_left
        dsimp only
        rw [hpull]; push_cast; ring
      exact ((hpart_i 0).add (hpart_i 1)).congr
        (Eventually.of_forall fun s => by dsimp [J]; rw [Fin.sum_univ_two, mul_add])
    have hdJ0_int : IntegrableOn (fun s => ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * J s₀)
        (Icc (s₀ - εSeq n) (s₀ + εSeq n)) volume := hd_int.mul_const (J s₀)
    have hsub_eq : ∫ s in Icc (s₀ - εSeq n) (s₀ + εSeq n), ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * J s =
        ∫ s in Icc (s₀ - εSeq n) (s₀ + εSeq n), ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * (J s - J s₀) := by
      have h0 : ∫ s in Icc (s₀ - εSeq n) (s₀ + εSeq n), ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * J s₀ = 0 := by
        rw [integral_mul_const, hint_deriv_zero (εSeq n) hε, zero_mul]
      rw [← sub_zero (∫ s in Icc (s₀ - εSeq n) (s₀ + εSeq n), ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * J s),
        ← h0, ← integral_sub hdJ_int hdJ0_int]
      exact setIntegral_congr_fun measurableSet_Icc fun s _ => by ring
    rw [dist_zero_right, hsub_eq]
    have hpt_bdd : ∀ s ∈ Icc (s₀ - εSeq n) (s₀ + εSeq n),
        ‖((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * (J s - J s₀)‖ ≤ (C_b / εSeq n) * (tol / K_b) := by
      intro s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hs_ball : dist s s₀ < δ_J := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact mul_le_mul (hderiv_βM_bdd (εSeq n) hε s)
        (le_of_lt (dist_eq_norm (J s) (J s₀) ▸ hJ_mod (Metric.mem_ball.2 hs_ball)))
        (norm_nonneg _) (div_nonneg hC_b_nn hε.le)
    have hconst_int : IntegrableOn (fun _ : ℝ => (C_b / εSeq n) * (tol / K_b))
        (Icc (s₀ - εSeq n) (s₀ + εSeq n)) volume := integrableOn_const (by simp [Real.volume_Icc])
    have hdiff_int : IntegrableOn
        (fun s => ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * (J s - J s₀))
        (Icc (s₀ - εSeq n) (s₀ + εSeq n)) volume :=
      (hdJ_int.sub hdJ0_int).congr (Eventually.of_forall fun s => by simp only [Pi.sub_apply]; ring)
    have hbound1 : ‖∫ s in Icc (s₀ - εSeq n) (s₀ + εSeq n),
        ((deriv (βM s₀ (εSeq n)) s : ℝ) : ℂ) * (J s - J s₀)‖ ≤
        ∫ _ in Icc (s₀ - εSeq n) (s₀ + εSeq n), (C_b / εSeq n) * (tol / K_b) :=
      (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_on hdiff_int.norm hconst_int measurableSet_Icc hpt_bdd)
    have hvol_calc : (∫ _ in Icc (s₀ - εSeq n) (s₀ + εSeq n), (C_b / εSeq n) * (tol / K_b)) =
        (2 * C_b) * (tol / K_b) := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc,
        show s₀ + εSeq n - (s₀ - εSeq n) = 2 * εSeq n by ring,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      have hne : εSeq n ≠ 0 := hε.ne'
      field_simp [hne]
    refine hbound1.trans_lt ?_
    rw [hvol_calc]
    calc (2 * C_b) * (tol / K_b)
        < K_b * (tol / K_b) :=
          mul_lt_mul_of_pos_right (by dsimp [K_b]; linarith) (div_pos htol hKb_pos)
      _ = tol := mul_div_cancel₀ tol hKb_pos.ne'
  -- Combine Step A + Step C: constant sequence D_val converges to 0 - 0 = 0
  have hlim_D : Tendsto (fun _ : ℕ => D_val) atTop (𝓝 0) := by
    simpa using (hbulk_zero.sub hjump_zero).congr'
      (Eventually.of_forall fun n => (hDecomp (εSeq n) (hε_pos n) (hε_le n)).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hlim_D

/-! ## 5. Inductive unit-step pasting on `[T, ∞)` for real data -/

private structure UnitStepSol (p : Params) (t₀ : ℝ)
    (u₀ uq₀ uη₀ : B0579.Plane → Fin 2 → ℝ)
    (g₀ gq₀ gη₀ : Coord → Fin 2 → ℝ) where
  z : Coord → Fin 2 → ℝ
  zq : Coord → Fin 2 → ℝ
  zη : Coord → Fin 2 → ℝ
  sm_z : StronglyMeasurable z
  sm_zq : StronglyMeasurable zq
  sm_zη : StronglyMeasurable zη
  per : ∀ x : Coord, z (qShift p.c x) = z x ∧
    zq (qShift p.c x) = zq x ∧ zη (qShift p.c x) = zη x
  slice_h1 : ∀ s ∈ Icc t₀ (t₀ + 1), IsCylH1Slice p.c (fun y => ofRealProf z (s, y))
    (fun y => ofRealProf zq (s, y)) (fun y => ofRealProf zη (s, y))
  init : cylSliceH1 p.c (fun y => ofRealProf z (t₀, y) - ofRealSlice u₀ y)
    (fun y => ofRealProf zq (t₀, y) - ofRealSlice uq₀ y)
    (fun y => ofRealProf zη (t₀, y) - ofRealSlice uη₀ y) = 0
  cont : ∀ s ∈ Icc t₀ (t₀ + 1),
    Tendsto (fun s' => cylSliceH1 p.c
      (fun y => ofRealProf z (s', y) - ofRealProf z (s, y))
      (fun y => ofRealProf zq (s', y) - ofRealProf zq (s, y))
      (fun y => ofRealProf zη (s', y) - ofRealProf zη (s, y)))
      (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 0)
  eq_unit : ∀ Ψ, IsPlanarSolTest Ψ →
    (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo t₀ (t₀ + 1) ×ˢ univ) →
    ∫ x, (∑ i : Fin 2, ofRealProf z x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x) =
      ∫ x, cdot (ofRealProf g₀) Ψ x

private def unitCutProf (t₀ : ℝ) (w : Coord → Fin 2 → ℝ) : Coord → Fin 2 → ℝ :=
  (Ioo t₀ (t₀ + 1) ×ˢ univ).indicator w

private lemma ofRealProf_unitCutProf (t₀ : ℝ) (w : Coord → Fin 2 → ℝ) :
    ofRealProf (unitCutProf t₀ w) = (Ioo t₀ (t₀ + 1) ×ˢ univ).indicator (ofRealProf w) := by
  funext x
  by_cases hx : x ∈ Ioo t₀ (t₀ + 1) ×ˢ univ
  · simp [unitCutProf, ofRealProf, hx]
  · ext i; simp [unitCutProf, ofRealProf, hx]

private lemma chooseUnitStep (hStep : RealCylUnitOseenStep)
    {p : Params} {d dm dp t₀ : ℝ} (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀)
    {u₀ uq₀ uη₀ : B0579.Plane → Fin 2 → ℝ}
    (hu_sm : StronglyMeasurable u₀) (huq_sm : StronglyMeasurable uq₀)
    (huη_sm : StronglyMeasurable uη₀)
    (hu_per : ∀ y : B0579.Plane, u₀ (y.1 + p.c, y.2) = u₀ y ∧
      uq₀ (y.1 + p.c, y.2) = uq₀ y ∧ uη₀ (y.1 + p.c, y.2) = uη₀ y)
    (hu_h1 : IsCylH1Slice p.c (ofRealSlice u₀) (ofRealSlice uq₀) (ofRealSlice uη₀))
    {g gq gη : Coord → Fin 2 → ℝ}
    (hg_sm : StronglyMeasurable g) (hgq_sm : StronglyMeasurable gq)
    (hgη_sm : StronglyMeasurable gη)
    (hg_per : ∀ x : Coord, g (qShift p.c x) = g x ∧
      gq (qShift p.c x) = gq x ∧ gη (qShift p.c x) = gη x)
    (hg_h1 : ∀ s : ℝ, IsCylH1Slice p.c (fun y => ofRealProf g (s, y))
      (fun y => ofRealProf gq (s, y)) (fun y => ofRealProf gη (s, y)))
    (hg_int : (∫⁻ s in Ioo t₀ (t₀ + 1),
      sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη) s) < ⊤) :
    Nonempty (UnitStepSol p t₀ u₀ uq₀ uη₀
      (unitCutProf t₀ g) (unitCutProf t₀ gq) (unitCutProf t₀ gη)) := by
  have hm_set : MeasurableSet (Ioo t₀ (t₀ + 1) ×ˢ (univ : Set B0579.Plane)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  let g₀ := unitCutProf t₀ g
  let gq₀ := unitCutProf t₀ gq
  let gη₀ := unitCutProf t₀ gη
  have hper₀ : ∀ x : Coord, g₀ (qShift p.c x) = g₀ x ∧
      gq₀ (qShift p.c x) = gq₀ x ∧ gη₀ (qShift p.c x) = gη₀ x := by
    intro x
    by_cases hx : x.1 ∈ Ioo t₀ (t₀ + 1)
    · have hxS : x ∈ Ioo t₀ (t₀ + 1) ×ˢ univ := ⟨hx, trivial⟩
      have hxsS : qShift p.c x ∈ Ioo t₀ (t₀ + 1) ×ˢ univ := ⟨hx, trivial⟩
      simp [g₀, gq₀, gη₀, unitCutProf, hxS, hxsS, (hg_per x).1, (hg_per x).2.1, (hg_per x).2.2]
    · have hxS : x ∉ Ioo t₀ (t₀ + 1) ×ˢ univ := fun h => hx h.1
      have hxsS : qShift p.c x ∉ Ioo t₀ (t₀ + 1) ×ˢ univ := fun h => hx h.1
      simp [g₀, gq₀, gη₀, unitCutProf, hxS, hxsS]
  have hsupp₀ : ∀ x : Coord, x.1 ∉ Ioo t₀ (t₀ + 1) → g₀ x = 0 ∧ gq₀ x = 0 ∧ gη₀ x = 0 := by
    intro x hx
    have hxS : x ∉ Ioo t₀ (t₀ + 1) ×ˢ univ := fun h => hx h.1
    simp [g₀, gq₀, gη₀, unitCutProf, hxS]
  have hh1₀ : ∀ s : ℝ, IsCylH1Slice p.c (fun y => ofRealProf g₀ (s, y))
      (fun y => ofRealProf gq₀ (s, y)) (fun y => ofRealProf gη₀ (s, y)) := by
    intro s
    by_cases hs : s ∈ Ioo t₀ (t₀ + 1)
    · have heq : ∀ w, (fun y => ofRealProf (unitCutProf t₀ w) (s, y)) =
          fun y => ofRealProf w (s, y) := fun w => funext fun y => by
        rw [ofRealProf_unitCutProf]
        exact Set.indicator_of_mem (s := Ioo t₀ (t₀ + 1) ×ˢ univ) ⟨hs, trivial⟩ _
      simpa [g₀, gq₀, gη₀, heq] using hg_h1 s
    · have heq : ∀ w, (fun y => ofRealProf (unitCutProf t₀ w) (s, y)) = 0 :=
        fun w => funext fun y => by
          rw [ofRealProf_unitCutProf]
          exact Set.indicator_of_notMem (s := Ioo t₀ (t₀ + 1) ×ˢ univ) (fun h => hs h.1) _
      simpa [g₀, gq₀, gη₀, heq] using isCylH1Slice_zero p.c
  have hint₀ : (∫⁻ s in Ioo t₀ (t₀ + 1),
      sliceH1Norm p.c (ofRealProf g₀) (ofRealProf gq₀) (ofRealProf gη₀) s) < ⊤ := by
    have hcongr : EqOn
        (sliceH1Norm p.c (ofRealProf g₀) (ofRealProf gq₀) (ofRealProf gη₀))
        (sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη))
        (Ioo t₀ (t₀ + 1)) := fun s hs => by
      have heq : ∀ w, (fun y => ofRealProf (unitCutProf t₀ w) (s, y)) =
          fun y => ofRealProf w (s, y) := fun w => funext fun y => by
        rw [ofRealProf_unitCutProf]
        exact Set.indicator_of_mem (s := Ioo t₀ (t₀ + 1) ×ˢ univ) ⟨hs, trivial⟩ _
      simp [sliceH1Norm, g₀, gq₀, gη₀, heq]
    exact (setLIntegral_congr_fun measurableSet_Ioo hcongr).trans_lt hg_int
  obtain ⟨z, zq, zη, hsmz, hsmzq, hsmzη, hper, hsl, hinit, hcont, heq⟩ :=
    hStep hbg ht₀ hu_sm huq_sm huη_sm hu_per hu_h1
      (hg_sm.indicator hm_set) (hgq_sm.indicator hm_set) (hgη_sm.indicator hm_set)
      hper₀ hsupp₀ hh1₀ hint₀
  exact ⟨⟨z, zq, zη, hsmz, hsmzq, hsmzη, hper, hsl, hinit, hcont, heq⟩⟩

private lemma measurable_nat_dispatch {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {idx : α → ℕ} (hidx : Measurable idx) {F : ℕ → α → β} (hF : ∀ k, Measurable (F k)) :
    Measurable (fun a => F (idx a) a) := by
  intro S hS
  have hpre : (fun a => F (idx a) a) ⁻¹' S = ⋃ k : ℕ, idx ⁻¹' {k} ∩ F k ⁻¹' S := by
    ext a; simp
  rw [hpre]
  exact MeasurableSet.iUnion fun k => (hidx (measurableSet_singleton k)).inter (hF k hS)

private lemma realTailExistence_of_unitStep (hStep : RealCylUnitOseenStep)
    {p : Params} {d dm dp T : ℝ} (hbg : BgRegime p d dm dp) (hT : 0 < T)
    {u₀ uq₀ uη₀ : B0579.Plane → Fin 2 → ℝ}
    (hu_sm : StronglyMeasurable u₀) (huq_sm : StronglyMeasurable uq₀)
    (huη_sm : StronglyMeasurable uη₀)
    (hu_per : ∀ y : B0579.Plane, u₀ (y.1 + p.c, y.2) = u₀ y ∧
      uq₀ (y.1 + p.c, y.2) = uq₀ y ∧ uη₀ (y.1 + p.c, y.2) = uη₀ y)
    (hu_h1 : IsCylH1Slice p.c (ofRealSlice u₀) (ofRealSlice uq₀) (ofRealSlice uη₀))
    {g gq gη : Coord → Fin 2 → ℝ}
    (hg_sm : StronglyMeasurable g) (hgq_sm : StronglyMeasurable gq)
    (hgη_sm : StronglyMeasurable gη)
    (hg_per : ∀ x : Coord, g (qShift p.c x) = g x ∧
      gq (qShift p.c x) = gq x ∧ gη (qShift p.c x) = gη x)
    (hg_h1 : ∀ s : ℝ, IsCylH1Slice p.c (fun y => ofRealProf g (s, y))
      (fun y => ofRealProf gq (s, y)) (fun y => ofRealProf gη (s, y)))
    (hg_int : (∫⁻ s in Ioi T,
      sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη) s) < ⊤) :
    ∃ Z Zq Zη : CProf,
      StronglyMeasurable Z ∧ StronglyMeasurable Zq ∧ StronglyMeasurable Zη ∧
      QPeriodic p.c Z ∧ QPeriodic p.c Zq ∧ QPeriodic p.c Zη ∧
      cylSliceH1 p.c (fun y => Z (T, y) - ofRealSlice u₀ y)
        (fun y => Zq (T, y) - ofRealSlice uq₀ y)
        (fun y => Zη (T, y) - ofRealSlice uη₀ y) = 0 ∧
      IsTailMeridionalSolution p T (ofRealProf g) Z Zq Zη ∧
      ∀ s : ℝ, T ≤ s →
        Tendsto (fun s' => cylSliceH1 p.c
          (fun y => Z (s', y) - Z (s, y))
          (fun y => Zq (s', y) - Zq (s, y))
          (fun y => Zη (s', y) - Zη (s, y))) (𝓝[Ici T] s) (𝓝 0) := by
  have hg_unit_int : ∀ n : ℕ, (∫⁻ s in Ioo (T + (n : ℝ)) (T + (n : ℝ) + 1),
      sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη) s) < ⊤ := by
    intro n
    refine (lintegral_mono_set (fun s hs => ?_)).trans_lt hg_int
    exact lt_of_le_of_lt (by linarith [Nat.cast_nonneg (α := ℝ) n]) hs.1
  -- Recursively construct unit steps S_n on [T + n, T + n + 1]
  let mkBase : UnitStepSol p (T + (0 : ℕ)) u₀ uq₀ uη₀
      (unitCutProf (T + (0 : ℕ)) g) (unitCutProf (T + (0 : ℕ)) gq)
      (unitCutProf (T + (0 : ℕ)) gη) :=
    Classical.choice (chooseUnitStep hStep hbg (by simpa using hT)
      hu_sm huq_sm huη_sm hu_per hu_h1 hg_sm hgq_sm hgη_sm hg_per hg_h1 (hg_unit_int 0))
  let mkSucc : ∀ (n : ℕ) {ua uqa uηa : B0579.Plane → Fin 2 → ℝ}
      (prev : UnitStepSol p (T + (n : ℝ)) ua uqa uηa
        (unitCutProf (T + (n : ℝ)) g) (unitCutProf (T + (n : ℝ)) gq)
        (unitCutProf (T + (n : ℝ)) gη)),
      UnitStepSol p (T + ((n + 1 : ℕ) : ℝ))
        (fun y => prev.z (T + ((n + 1 : ℕ) : ℝ), y))
        (fun y => prev.zq (T + ((n + 1 : ℕ) : ℝ), y))
        (fun y => prev.zη (T + ((n + 1 : ℕ) : ℝ), y))
        (unitCutProf (T + ((n + 1 : ℕ) : ℝ)) g)
        (unitCutProf (T + ((n + 1 : ℕ) : ℝ)) gq)
        (unitCutProf (T + ((n + 1 : ℕ) : ℝ)) gη) := fun n {_ _ _} prev =>
    have htn1_pos : 0 < T + ((n + 1 : ℕ) : ℝ) := by positivity
    have hmem : T + ((n + 1 : ℕ) : ℝ) ∈ Icc (T + (n : ℝ)) (T + (n : ℝ) + 1) := by
      refine ⟨by push_cast; linarith, by push_cast; linarith⟩
    Classical.choice (chooseUnitStep hStep hbg htn1_pos
      (prev.sm_z.comp_measurable measurable_prodMk_left)
      (prev.sm_zq.comp_measurable measurable_prodMk_left)
      (prev.sm_zη.comp_measurable measurable_prodMk_left)
      (fun y => prev.per (T + ((n + 1 : ℕ) : ℝ), y))
      (prev.slice_h1 (T + ((n + 1 : ℕ) : ℝ)) hmem)
      hg_sm hgq_sm hgη_sm hg_per hg_h1
      (hg_unit_int (n + 1)))
  -- Pack recursive sequence as Sigma over initial data
  let pack : ∀ n : ℕ, Σ (init_d : (B0579.Plane → Fin 2 → ℝ) ×
      (B0579.Plane → Fin 2 → ℝ) × (B0579.Plane → Fin 2 → ℝ)),
      UnitStepSol p (T + (n : ℝ)) init_d.1 init_d.2.1 init_d.2.2
        (unitCutProf (T + (n : ℝ)) g) (unitCutProf (T + (n : ℝ)) gq)
        (unitCutProf (T + (n : ℝ)) gη) :=
    Nat.rec ⟨(u₀, uq₀, uη₀), mkBase⟩ (fun n ih =>
      ⟨((fun y => ih.2.z (T + ((n + 1 : ℕ) : ℝ), y)),
        (fun y => ih.2.zq (T + ((n + 1 : ℕ) : ℝ), y)),
        (fun y => ih.2.zη (T + ((n + 1 : ℕ) : ℝ), y))),
       mkSucc n ih.2⟩)
  have hpack_zero : (pack 0).1 = (u₀, uq₀, uη₀) := rfl
  have hpack_succ : ∀ n : ℕ, (pack (n + 1)).1 =
      ((fun y => (pack n).2.z (T + ((n + 1 : ℕ) : ℝ), y)),
       (fun y => (pack n).2.zq (T + ((n + 1 : ℕ) : ℝ), y)),
       (fun y => (pack n).2.zη (T + ((n + 1 : ℕ) : ℝ), y))) := fun _ => rfl
  -- Define pasted real profiles on [T, ∞) via ⌊x.1 - T⌋₊ (0 for x.1 < T)
  let z_raw : Coord → Fin 2 → ℝ := fun x =>
    if x.1 < T then 0 else (pack ⌊x.1 - T⌋₊).2.z x
  let zq_raw : Coord → Fin 2 → ℝ := fun x =>
    if x.1 < T then 0 else (pack ⌊x.1 - T⌋₊).2.zq x
  let zη_raw : Coord → Fin 2 → ℝ := fun x =>
    if x.1 < T then 0 else (pack ⌊x.1 - T⌋₊).2.zη x
  let Z : CProf := ofRealProf z_raw
  let Zq : CProf := ofRealProf zq_raw
  let Zη : CProf := ofRealProf zη_raw
  -- Measurability of z_raw, zq_raw, zη_raw
  have hidx_meas : Measurable (fun x : Coord => ⌊x.1 - T⌋₊) :=
    (measurable_fst.sub measurable_const).nat_floor
  have hsm_raw : StronglyMeasurable z_raw ∧ StronglyMeasurable zq_raw ∧ StronglyMeasurable zη_raw := by
    have hm_piece : ∀ (F : ℕ → Coord → Fin 2 → ℝ), (∀ k, StronglyMeasurable (F k)) →
        StronglyMeasurable (fun x : Coord => if x.1 < T then (0 : Fin 2 → ℝ) else F ⌊x.1 - T⌋₊ x) := by
      intro F hF
      have hm_disp : Measurable (fun x : Coord => F ⌊x.1 - T⌋₊ x) :=
        measurable_nat_dispatch hidx_meas (fun k => (hF k).measurable)
      have heq : (fun x : Coord => if x.1 < T then (0 : Fin 2 → ℝ) else F ⌊x.1 - T⌋₊ x) =
          Set.piecewise {x : Coord | x.1 < T} 0 (fun x => F ⌊x.1 - T⌋₊ x) := by
        funext x; by_cases hx : x.1 < T <;> simp [Set.piecewise, hx]
      rw [heq]
      exact StronglyMeasurable.piecewise (measurableSet_lt measurable_fst measurable_const)
        stronglyMeasurable_const hm_disp.stronglyMeasurable
    exact ⟨hm_piece _ (fun k => (pack k).2.sm_z),
      hm_piece _ (fun k => (pack k).2.sm_zq),
      hm_piece _ (fun k => (pack k).2.sm_zη)⟩
  have hZ_sm : StronglyMeasurable Z := stronglyMeasurable_ofRealProf hsm_raw.1
  have hZq_sm : StronglyMeasurable Zq := stronglyMeasurable_ofRealProf hsm_raw.2.1
  have hZη_sm : StronglyMeasurable Zη := stronglyMeasurable_ofRealProf hsm_raw.2.2
  -- Everywhere p.c-periodicity
  have hper_raw : ∀ x : Coord, z_raw (qShift p.c x) = z_raw x ∧
      zq_raw (qShift p.c x) = zq_raw x ∧ zη_raw (qShift p.c x) = zη_raw x := by
    intro x
    have hp := (pack ⌊x.1 - T⌋₊).2.per x
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [z_raw, qShift]; split_ifs with hx
      · rfl
      · exact hp.1
    · dsimp only [zq_raw, qShift]; split_ifs with hx
      · rfl
      · exact hp.2.1
    · dsimp only [zη_raw, qShift]; split_ifs with hx
      · rfl
      · exact hp.2.2
  have hper_all : ∀ x : Coord, Z (qShift p.c x) = Z x ∧
      Zq (qShift p.c x) = Zq x ∧ Zη (qShift p.c x) = Zη x := fun x =>
    ⟨by dsimp [Z, ofRealProf]; rw [(hper_raw x).1],
     by dsimp [Zq, ofRealProf]; rw [(hper_raw x).2.1],
     by dsimp [Zη, ofRealProf]; rw [(hper_raw x).2.2]⟩
  have hZ_per : QPeriodic p.c Z := QPerHalf.of_ae (Eventually.of_forall fun x => (hper_all x).1)
  have hZq_per : QPeriodic p.c Zq := QPerHalf.of_ae (Eventually.of_forall fun x => (hper_all x).2.1)
  have hZη_per : QPeriodic p.c Zη := QPerHalf.of_ae (Eventually.of_forall fun x => (hper_all x).2.2)
  -- Slab identification for s ∈ [T + n, T + n + 1)
  have hslab_eq : ∀ (n : ℕ) (s : ℝ), T + (n : ℝ) ≤ s → s < T + (n : ℝ) + 1 →
      (fun y => Z (s, y)) = (fun y => ofRealProf (pack n).2.z (s, y)) ∧
      (fun y => Zq (s, y)) = (fun y => ofRealProf (pack n).2.zq (s, y)) ∧
      (fun y => Zη (s, y)) = (fun y => ofRealProf (pack n).2.zη (s, y)) := by
    intro n s hlo hhi
    have hnot : ¬ s < T := not_lt.2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hfl : ⌊s - T⌋₊ = n :=
      (Nat.floor_eq_iff (by linarith [Nat.cast_nonneg (α := ℝ) n])).2 ⟨by linarith, by linarith⟩
    refine ⟨funext fun y => ?_, funext fun y => ?_, funext fun y => ?_⟩
    · dsimp only [Z, ofRealProf, z_raw]; split_ifs; rw [hfl]
    · dsimp only [Zq, ofRealProf, zq_raw]; split_ifs; rw [hfl]
    · dsimp only [Zη, ofRealProf, zη_raw]; split_ifs; rw [hfl]
  -- Helper to rewrite cylSliceH1 differences from slice equalities
  have hcyl_congr : ∀ {s' s : ℝ} {u' uq' uη' u uq uη : B0579.Plane → CMerid},
      (fun y => Z (s', y)) = u' → (fun y => Zq (s', y)) = uq' → (fun y => Zη (s', y)) = uη' →
      (fun y => Z (s, y)) = u → (fun y => Zq (s, y)) = uq → (fun y => Zη (s, y)) = uη →
      cylSliceH1 p.c (fun y => Z (s', y) - Z (s, y))
        (fun y => Zq (s', y) - Zq (s, y)) (fun y => Zη (s', y) - Zη (s, y)) =
      cylSliceH1 p.c (fun y => u' y - u y) (fun y => uq' y - uq y) (fun y => uη' y - uη y) := by
    intro s' s u' uq' uη' u uq uη e1 e2 e3 f1 f2 f3
    have d1 : (fun y => Z (s', y) - Z (s, y)) = fun y => u' y - u y :=
      funext fun y => by rw [congrFun e1 y, congrFun f1 y]
    have d2 : (fun y => Zq (s', y) - Zq (s, y)) = fun y => uq' y - uq y :=
      funext fun y => by rw [congrFun e2 y, congrFun f2 y]
    have d3 : (fun y => Zη (s', y) - Zη (s, y)) = fun y => uη' y - uη y :=
      funext fun y => by rw [congrFun e3 y, congrFun f3 y]
    rw [d1, d2, d3]
  -- IsCylH1Slice at EVERY s : ℝ
  have hsl_all : ∀ s : ℝ, IsCylH1Slice p.c (fun y => Z (s, y))
      (fun y => Zq (s, y)) (fun y => Zη (s, y)) := by
    intro s
    by_cases hs : s < T
    · have h0 : (fun y => Z (s, y)) = 0 ∧ (fun y => Zq (s, y)) = 0 ∧ (fun y => Zη (s, y)) = 0 := by
        refine ⟨funext fun y => ?_, funext fun y => ?_, funext fun y => ?_⟩ <;>
          (ext i; simp [Z, Zq, Zη, ofRealProf, z_raw, zq_raw, zη_raw, hs])
      rw [h0.1, h0.2.1, h0.2.2]
      exact isCylH1Slice_zero p.c
    · rw [not_lt] at hs
      let n : ℕ := ⌊s - T⌋₊
      have hlo : T + (n : ℝ) ≤ s := by linarith [Nat.floor_le (sub_nonneg.2 hs)]
      have hhi : s < T + (n : ℝ) + 1 := by linarith [Nat.lt_floor_add_one (s - T)]
      obtain ⟨e1, e2, e3⟩ := hslab_eq n s hlo hhi
      rw [e1, e2, e3]
      exact (pack n).2.slice_h1 s ⟨hlo, hhi.le⟩
  -- Initial datum at T
  have hinit_T : cylSliceH1 p.c (fun y => Z (T, y) - ofRealSlice u₀ y)
      (fun y => Zq (T, y) - ofRealSlice uq₀ y)
      (fun y => Zη (T, y) - ofRealSlice uη₀ y) = 0 := by
    obtain ⟨e1, e2, e3⟩ := hslab_eq 0 T (by simp) (by simp)
    have ht0 : T = T + ((0 : ℕ) : ℝ) := by simp
    have f1 : (fun y => Z (T, y) - ofRealSlice u₀ y) =
        fun y => ofRealProf (pack 0).2.z (T + ((0 : ℕ) : ℝ), y) - ofRealSlice (pack 0).1.1 y :=
      funext fun y => by rw [congrFun e1 y, congrArg (fun t => ofRealProf (pack 0).2.z (t, y)) ht0]; rfl
    have f2 : (fun y => Zq (T, y) - ofRealSlice uq₀ y) =
        fun y => ofRealProf (pack 0).2.zq (T + ((0 : ℕ) : ℝ), y) - ofRealSlice (pack 0).1.2.1 y :=
      funext fun y => by rw [congrFun e2 y, congrArg (fun t => ofRealProf (pack 0).2.zq (t, y)) ht0]; rfl
    have f3 : (fun y => Zη (T, y) - ofRealSlice uη₀ y) =
        fun y => ofRealProf (pack 0).2.zη (T + ((0 : ℕ) : ℝ), y) - ofRealSlice (pack 0).1.2.2 y :=
      funext fun y => by rw [congrFun e3 y, congrArg (fun t => ofRealProf (pack 0).2.zη (t, y)) ht0]; rfl
    rw [f1, f2, f3]
    exact (pack 0).2.init
  -- Continuity in cylSliceH1 on [T, ∞)
  have hcont_Ici : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => Z (s', y) - Z (s, y))
        (fun y => Zq (s', y) - Zq (s, y))
        (fun y => Zη (s', y) - Zη (s, y))) (𝓝[Ici T] s) (𝓝 0) := by
    intro s hsT
    generalize hk_def : ⌊s - T⌋₊ = k
    have hlo : T + (k : ℝ) ≤ s := by
      have := Nat.floor_le (sub_nonneg.2 hsT)
      rw [hk_def] at this; linarith
    have hhi : s < T + (k : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (s - T)
      rw [hk_def] at this; linarith
    clear hk_def
    obtain ⟨es1, es2, es3⟩ := hslab_eq k s hlo hhi
    by_cases hgt : T + (k : ℝ) < s
    · -- Interior of slab k: Ioo (T + k) (T + k + 1) ∈ 𝓝 s
      have hopen_mem : Ioo (T + (k : ℝ)) (T + (k : ℝ) + 1) ∈ 𝓝[Ici T] s :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hgt hhi)
      have hnhds_le : 𝓝[Ici T] s ≤ 𝓝[Icc (T + (k : ℝ)) (T + (k : ℝ) + 1)] s :=
        nhdsWithin_le_iff.2 (Filter.mem_of_superset hopen_mem Ioo_subset_Icc_self)
      refine (((pack k).2.cont s ⟨hlo, hhi.le⟩).mono_left hnhds_le).congr' ?_
      filter_upwards [hopen_mem] with s' hs'
      obtain ⟨e1, e2, e3⟩ := hslab_eq k s' hs'.1.le hs'.2
      exact (hcyl_congr e1 e2 e3 es1 es2 es3).symm
    · -- Seam s = T + k
      have hs_eq : s = T + (k : ℝ) := le_antisymm (not_lt.1 hgt) hlo
      rcases k with _ | m
      · have hsT_eq : s = T := by simpa using hs_eq
        rw [hsT_eq] at es1 es2 es3 ⊢
        have hIco_mem : Ico (T + ((0 : ℕ) : ℝ)) (T + ((0 : ℕ) : ℝ) + 1) ∈ 𝓝[Ici T] T := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          refine ⟨Iio (T + 1), Iio_mem_nhds (by linarith), ?_⟩
          intro s' ⟨hs'1, hs'2⟩
          exact ⟨by simpa using hs'2, by simpa using hs'1⟩
        have hnhds_le : 𝓝[Ici T] T ≤ 𝓝[Icc (T + ((0 : ℕ) : ℝ)) (T + ((0 : ℕ) : ℝ) + 1)] T :=
          nhdsWithin_le_iff.2 (Filter.mem_of_superset hIco_mem Ico_subset_Icc_self)
        refine (((pack 0).2.cont T ⟨by simp, by simp⟩).mono_left hnhds_le).congr' ?_
        filter_upwards [hIco_mem] with s' hs'
        obtain ⟨e1, e2, e3⟩ := hslab_eq 0 s' hs'.1 hs'.2
        exact (hcyl_congr e1 e2 e3 es1 es2 es3).symm
      · -- Two-sided continuity at interior seam s = T + (m + 1) > T
        have hs_m1 : s = T + (m : ℝ) + 1 := by rw [hs_eq]; push_cast; ring
        have hseam_zero : cylSliceH1 p.c
            (fun y => ofRealProf (pack m).2.z (s, y) - ofRealProf (pack (m + 1)).2.z (s, y))
            (fun y => ofRealProf (pack m).2.zq (s, y) - ofRealProf (pack (m + 1)).2.zq (s, y))
            (fun y => ofRealProf (pack m).2.zη (s, y) - ofRealProf (pack (m + 1)).2.zη (s, y)) = 0 := by
          rw [cylSliceH1_symm, hs_eq]
          exact (pack (m + 1)).2.init
        rw [ENNReal.tendsto_nhds_zero]
        intro ε hε
        have hR_lim := (ENNReal.tendsto_nhds_zero.1
          ((pack (m + 1)).2.cont s ⟨hs_eq.ge, by rw [hs_eq]; linarith⟩)) ε hε
        have hL_lim := (ENNReal.tendsto_nhds_zero.1
          ((pack m).2.cont s ⟨by rw [hs_m1]; linarith, hs_m1.le⟩)) ε hε
        obtain ⟨UR, hUR_nhds, hUR_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hR_lim
        obtain ⟨UL, hUL_nhds, hUL_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hL_lim
        obtain ⟨δR, hδR, hbR⟩ := Metric.mem_nhds_iff.1 hUR_nhds
        obtain ⟨δL, hδL, hbL⟩ := Metric.mem_nhds_iff.1 hUL_nhds
        let δ : ℝ := min (min δR δL) (1 / 2)
        have hδ : 0 < δ := lt_min (lt_min hδR hδL) (by norm_num)
        refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds s hδ) ?_)
        intro s' hs'
        change cylSliceH1 p.c (fun y => Z (s', y) - Z (s, y))
          (fun y => Zq (s', y) - Zq (s, y)) (fun y => Zη (s', y) - Zη (s, y)) ≤ ε
        have hd_lt : |s' - s| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hs'
        have hd_half : |s' - s| < 1 / 2 := hd_lt.trans_le (min_le_right _ _)
        by_cases hs'ge : s ≤ s'
        · have hs'lo : T + ((m + 1 : ℕ) : ℝ) ≤ s' := by linarith [hs_eq]
          have hs'hi : s' < T + ((m + 1 : ℕ) : ℝ) + 1 := by
            linarith [(abs_lt.1 hd_half).2, hs_eq]
          obtain ⟨e1, e2, e3⟩ := hslab_eq (m + 1) s' hs'lo hs'hi
          rw [hcyl_congr e1 e2 e3 es1 es2 es3]
          have hball_R : s' ∈ Metric.ball s δR := Metric.mem_ball.2
            (hd_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
          exact hUR_sub ⟨hbR hball_R, hs'lo, hs'hi.le⟩
        · rw [not_le] at hs'ge
          have hs'lo : T + (m : ℝ) ≤ s' := by linarith [(abs_lt.1 hd_half).1, hs_m1]
          have hs'hi : s' < T + (m : ℝ) + 1 := by linarith [hs_m1]
          obtain ⟨e1, e2, e3⟩ := hslab_eq m s' hs'lo hs'hi
          rw [hcyl_congr e1 e2 e3 es1 es2 es3]
          have htri := cylSliceH1_triangle p.c
            (u := fun y => ofRealProf (pack m).2.z (s', y))
            (uq := fun y => ofRealProf (pack m).2.zq (s', y))
            (uη := fun y => ofRealProf (pack m).2.zη (s', y))
            (v := fun y => ofRealProf (pack m).2.z (s, y))
            (vq := fun y => ofRealProf (pack m).2.zq (s, y))
            (vη := fun y => ofRealProf (pack m).2.zη (s, y))
            (w := fun y => ofRealProf (pack (m + 1)).2.z (s, y))
            (wq := fun y => ofRealProf (pack (m + 1)).2.zq (s, y))
            (wη := fun y => ofRealProf (pack (m + 1)).2.zη (s, y))
            (stronglyMeasurable_ofRealProf (pack m).2.sm_z |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack m).2.sm_zq |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack m).2.sm_zη |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack m).2.sm_z |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack m).2.sm_zq |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack m).2.sm_zη |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack (m + 1)).2.sm_z |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack (m + 1)).2.sm_zq |>.comp_measurable measurable_prodMk_left)
            (stronglyMeasurable_ofRealProf (pack (m + 1)).2.sm_zη |>.comp_measurable measurable_prodMk_left)
          rw [hseam_zero, add_zero] at htri
          have hball_L : s' ∈ Metric.ball s δL := Metric.mem_ball.2
            (hd_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
          exact htri.trans (hUL_sub ⟨hbL hball_L, hs'lo, hs'hi.le⟩)
  -- Local sliceH1Norm finiteness on every [a, b]
  have hzero_ltT : ∀ x : Coord, x.1 < T → Z x = 0 ∧ Zq x = 0 ∧ Zη x = 0 := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩ <;> (ext i; simp [Z, Zq, Zη, ofRealProf, z_raw, zq_raw, zη_raw, hx])
  have hfin_pt : ∀ s : ℝ, T ≤ s → sliceH1Norm p.c Z Zq Zη s < ⊤ := fun s _ =>
    ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨(hsl_all s).memL2_u.eLpNorm_lt_top, (hsl_all s).memL2_uq.eLpNorm_lt_top⟩,
      (hsl_all s).memL2_uη.eLpNorm_lt_top⟩
  have hZ_loc : ∀ a b : ℝ, (∫⁻ s in Icc a b, sliceH1Norm p.c Z Zq Zη s) < ⊤ :=
    loc_sliceH1Norm_lt_top_of_cont_Ici hZ_sm hZq_sm hZη_sm hzero_ltT hfin_pt hcont_Ici
  -- Global weak_q and weak_eta via TailPeriodizeAux.sliceWeakToJoint
  have hwq_Z : HasWeakVec vQ0 dZero Z Zq :=
    TailPeriodizeAux.sliceWeakToJoint p.c_pos 0 Z Zq hZ_sm hZq_sm hZ_per hZq_per
      (fun a b _ => (lintegral_mono fun _ => le_self_add).trans_lt (hZ_loc a b))
      (Eventually.of_forall fun s _ i => (hsl_all s).weak_q i)
  have hwη_Z : HasWeakVec vEta dZero Z Zη :=
    TailPeriodizeAux.sliceWeakToJoint p.c_pos 1 Z Zη hZ_sm hZη_sm hZ_per hZη_per
      (fun a b _ => (lintegral_mono fun s =>
        add_le_add (le_self_add : cylSliceL2 p.c (fun y => Z (s, y)) ≤ _) le_rfl).trans_lt
        (hZ_loc a b))
      (Eventually.of_forall fun s _ i => (hsl_all s).weak_eta i)
  -- Global solenoidal on Ioi 0 ×ˢ univ
  have hsol_Z : ∀ φ, IsCoordTest φ →
      Integrable (fun x => Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (Z x 0 * (cpd 1 φ x : ℂ) + Z x 1 * (cpd 2 φ x : ℂ)) = 0 := by
    intro φ hφ
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hφ
    have hZi_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
        eLpNorm (fun z => Z (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      refine (lintegral_mono fun s => ?_).trans_lt (hZ_loc a b)
      refine (eLpNorm_mono_enorm fun z => ?_).trans (le_self_add.trans le_self_add)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]; exact_mod_cast PiLp.norm_apply_le (Z (s, z)) i
    have hcpd1_cont : Continuous (cpd 1 φ) := (planarTest_isCoordTest_partial hφ (cdir 1)).smooth.continuous
    have hcpd2_cont : Continuous (cpd 2 φ) := (planarTest_isCoordTest_partial hφ (cdir 2)).smooth.continuous
    have hZi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => Z x i) volume :=
      fun i => ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hZ_sm).aestronglyMeasurable
    obtain ⟨hint0, hcell0, heq0⟩ := TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
      p.c_pos ha hab hR (hZi_meas 0)
      (hZ_per.mono fun _ hx => congrArg (fun v => v 0) hx)
      (hZi_loc 0) hcpd1_cont (fun x hx => (hbox x hx).2 1)
    obtain ⟨hint1, hcell1, heq1⟩ := TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize
      p.c_pos ha hab hR (hZi_meas 1)
      (hZ_per.mono fun _ hx => congrArg (fun v => v 1) hx)
      (hZi_loc 1) hcpd2_cont (fun x hx => (hbox x hx).2 2)
    have hfub : ∀ {F : Coord → ℂ}, IntegrableOn F (Icc a b ×ˢ B0579.cell p.c) volume →
        IntegrableOn (fun s => ∫ z in B0579.cell p.c, F (s, z)) (Icc a b) volume ∧
          ∀ᵐ s ∂(volume.restrict (Icc a b)), IntegrableOn (fun z => F (s, z)) (B0579.cell p.c) volume := by
      intro F hF
      have hF' : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell p.c))) := by
        rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact ⟨hF'.integral_prod_left, hF'.prod_right_ae⟩
    obtain ⟨hs0, hz0⟩ := hfub hcell0
    obtain ⟨hs1, hz1⟩ := hfub hcell1
    refine ⟨hint0.add hint1, ?_⟩
    rw [integral_add hint0 hint1, heq0, heq1, ← integral_add hs0 hs1]
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
    filter_upwards [hz0, hz1] with s hi0 hi1
    rw [← integral_add hi0 hi1]
    have hpd0 : (fun z => TailPeriodizeAux.qPeriodize p.c (cpd 1 φ) s z) =
        B0579.pd 0 (TailPeriodizeAux.qPeriodize p.c φ s) :=
      funext fun z => (TailPeriodizeAux.pd_qPeriodize p.c_pos hφ s 0 z).symm
    have hpd1 : (fun z => TailPeriodizeAux.qPeriodize p.c (cpd 2 φ) s z) =
        B0579.pd 1 (TailPeriodizeAux.qPeriodize p.c φ s) :=
      funext fun z => (TailPeriodizeAux.pd_qPeriodize p.c_pos hφ s 1 z).symm
    simp_rw [hpd0, hpd1]
    exact ((hsl_all s).solenoidal _ (TailPeriodizeAux.isCylTest_qPeriodize p.c_pos hφ s)).2
  -- Equation on each unit slab Ioo (T + n) (T + n + 1) ×ˢ univ
  have heq_unit_slab : ∀ n : ℕ, ∀ Φ, IsPlanarSolTest Φ →
      (∀ i, tsupport (fun x => Φ x i) ⊆ Ioo (T + (n : ℝ)) (T + (n : ℝ) + 1) ×ˢ univ) →
      ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i +
          cdot (flatBv p.train Z Zq Zη) Φ x) = ∫ x, cdot (ofRealProf g) Φ x := by
    intro n Φ hΦ hΦ_supp
    have hstep_eq := (pack n).2.eq_unit Φ hΦ hΦ_supp
    have hL_congr : (fun x => ∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i +
        cdot (flatBv p.train Z Zq Zη) Φ x) =
        fun x => ∑ i : Fin 2, ofRealProf (pack n).2.z x i * meridTranspose p.ν Φ x i +
          cdot (flatBv p.train (ofRealProf (pack n).2.z)
            (ofRealProf (pack n).2.zq) (ofRealProf (pack n).2.zη)) Φ x := by
      funext x
      by_cases hx : x.1 ∈ Ioo (T + (n : ℝ)) (T + (n : ℝ) + 1)
      · obtain ⟨e1, e2, e3⟩ := hslab_eq n x.1 hx.1.le hx.2
        have hZx : Z x = ofRealProf (pack n).2.z x := congrFun e1 x.2
        have hZqx : Zq x = ofRealProf (pack n).2.zq x := congrFun e2 x.2
        have hZηx : Zη x = ofRealProf (pack n).2.zη x := congrFun e3 x.2
        simp [cdot, flatBv, hZx, hZqx, hZηx]
      · have hΦ0 : ∀ i : Fin 2, Φ x i = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun y => Φ y i) (fun hmem => hx (hΦ_supp i hmem).1)
        have hMT0 : ∀ i : Fin 2, meridTranspose p.ν Φ x i = 0 := by
          intro i
          have hnot : x ∉ tsupport (fun y => Φ y i) := fun hmem => hx (hΦ_supp i hmem).1
          have hev : (fun y => Φ y i) =ᶠ[𝓝 x] 0 := by
            filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hnot] with y hy
            exact image_eq_zero_of_notMem_tsupport (f := fun z => Φ z i) hy
          have hc0 : cpd 0 (fun y => Φ y i) x = 0 := by
            change fderiv ℝ (fun y => Φ y i) x (cdir 0) = 0; rw [hev.fderiv_eq]; simp
          have hc11 : cpd 1 (fun y => cpd 1 (fun z => Φ z i) y) x = 0 := by
            have hev1 : cpd 1 (fun z => Φ z i) =ᶠ[𝓝 x] 0 := by
              filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hnot] with y hy
              have hy_ev : (fun z => Φ z i) =ᶠ[𝓝 y] 0 := by
                filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy] with z hz
                exact image_eq_zero_of_notMem_tsupport (f := fun w => Φ w i) hz
              change fderiv ℝ (fun z => Φ z i) y (cdir 1) = 0; rw [hy_ev.fderiv_eq]; simp
            change fderiv ℝ (cpd 1 (fun z => Φ z i)) x (cdir 1) = 0; rw [hev1.fderiv_eq]; simp
          have hc22 : cpd 2 (fun y => cpd 2 (fun z => Φ z i) y) x = 0 := by
            have hev2 : cpd 2 (fun z => Φ z i) =ᶠ[𝓝 x] 0 := by
              filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hnot] with y hy
              have hy_ev : (fun z => Φ z i) =ᶠ[𝓝 y] 0 := by
                filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy] with z hz
                exact image_eq_zero_of_notMem_tsupport (f := fun w => Φ w i) hz
              change fderiv ℝ (fun z => Φ z i) y (cdir 2) = 0; rw [hy_ev.fderiv_eq]; simp
            change fderiv ℝ (cpd 2 (fun z => Φ z i)) x (cdir 2) = 0; rw [hev2.fderiv_eq]; simp
          simp [meridTranspose, hc0, hc11, hc22]
        simp [cdot, hΦ0, hMT0]
    have hR_congr : cdot (ofRealProf g) Φ =
        cdot (ofRealProf (unitCutProf (T + (n : ℝ)) g)) Φ := by
      funext x
      by_cases hx : x.1 ∈ Ioo (T + (n : ℝ)) (T + (n : ℝ) + 1)
      · have hg_eq : ofRealProf (unitCutProf (T + (n : ℝ)) g) x = ofRealProf g x := by
          rw [ofRealProf_unitCutProf]
          exact Set.indicator_of_mem (s := Ioo (T + (n : ℝ)) (T + (n : ℝ) + 1) ×ˢ univ) ⟨hx, trivial⟩ _
        simp [cdot, hg_eq]
      · have hΦ0 : ∀ i : Fin 2, Φ x i = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun y => Φ y i) (fun hmem => hx (hΦ_supp i hmem).1)
        simp [cdot, hΦ0]
    rw [hL_congr, hstep_eq, hR_congr]
  -- Prepare g' := (Ioi T ×ˢ univ).indicator (ofRealProf g) so g' is locally L¹(L²) on ALL a > 0
  let g_tail : CProf := (Ioi T ×ˢ univ).indicator (ofRealProf g)
  have hg_tail_sm : StronglyMeasurable g_tail :=
    (stronglyMeasurable_ofRealProf hg_sm).indicator (measurableSet_Ioi.prod MeasurableSet.univ)
  have hg_tail_per : QPeriodic p.c g_tail := QPerHalf.of_ae (Eventually.of_forall fun x => by
    dsimp only [g_tail]
    by_cases hx : T < x.1
    · rw [Set.indicator_of_mem (a := qShift p.c x) (s := Ioi T ×ˢ univ) ⟨mem_Ioi.2 hx, trivial⟩,
          Set.indicator_of_mem (a := x) (s := Ioi T ×ˢ univ) ⟨mem_Ioi.2 hx, trivial⟩]
      dsimp [ofRealProf]; rw [(hg_per x).1]
    · rw [Set.indicator_of_notMem (a := qShift p.c x) (s := Ioi T ×ˢ univ) (fun h => hx (mem_Ioi.1 h.1)),
          Set.indicator_of_notMem (a := x) (s := Ioi T ×ˢ univ) (fun h => hx (mem_Ioi.1 h.1))])
  have hg_tail_loc : ∀ a b : ℝ, 0 < a → (∫⁻ s in Icc a b, cylSliceL2 p.c (fun y => g_tail (s, y))) < ⊤ := by
    intro a b _
    have hle : ∀ s : ℝ, cylSliceL2 p.c (fun y => g_tail (s, y)) ≤
        (Ioi T).indicator (sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη)) s := by
      intro s
      by_cases hs : T < s
      · have heq : (fun y => g_tail (s, y)) = fun y => ofRealProf g (s, y) :=
          funext fun y => Set.indicator_of_mem (a := (s, y)) (s := Ioi T ×ˢ univ)
            ⟨mem_Ioi.2 hs, trivial⟩ (ofRealProf g)
        rw [heq, Set.indicator_of_mem (mem_Ioi.2 hs)]
        exact le_self_add.trans le_self_add
      · have heq : (fun y => g_tail (s, y)) = 0 :=
          funext fun y => Set.indicator_of_notMem (a := (s, y)) (s := Ioi T ×ˢ univ)
            (fun h => hs (mem_Ioi.1 h.1)) (ofRealProf g)
        rw [heq, Set.indicator_of_notMem (fun h => hs (mem_Ioi.1 h))]
        simp [cylSliceL2]
    calc (∫⁻ s in Icc a b, cylSliceL2 p.c (fun y => g_tail (s, y)))
        ≤ ∫⁻ s, (Ioi T).indicator
            (sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη)) s :=
          (setLIntegral_le_lintegral _ _).trans (lintegral_mono hle)
      _ = ∫⁻ s in Ioi T, sliceH1Norm p.c (ofRealProf g) (ofRealProf gq) (ofRealProf gη) s :=
          lintegral_indicator measurableSet_Ioi _
      _ < ⊤ := hg_int
  -- Inductive seam gluing across T + 1, ..., T + N
  have heq_prefix : ∀ N : ℕ, ∀ Φ, IsPlanarSolTest Φ →
      (∀ i, tsupport (fun x => Φ x i) ⊆ Ioo T (T + ((N + 1 : ℕ) : ℝ)) ×ˢ univ) →
      ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i +
          cdot (flatBv p.train Z Zq Zη) Φ x) = ∫ x, cdot g_tail Φ x := by
    intro N
    induction N with
    | zero =>
      intro Φ hΦ hΦ_supp
      have h0 := heq_unit_slab 0 Φ hΦ (by simpa using hΦ_supp)
      refine h0.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
      by_cases hx : T < x.1
      · have hgx : g_tail x = ofRealProf g x :=
          Set.indicator_of_mem (a := x) (s := Ioi T ×ˢ univ) ⟨mem_Ioi.2 hx, trivial⟩ (ofRealProf g)
        simp only [cdot, hgx]
      · have hΦ0 : ∀ i : Fin 2, Φ x i = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun y => Φ y i) (fun hmem => hx (hΦ_supp i hmem).1.1)
        simp [cdot, hΦ0]
    | succ N ih =>
      let s₀ : ℝ := T + ((N + 1 : ℕ) : ℝ)
      have hs₀_gt : T < s₀ := by dsimp [s₀]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
      have hs₀_lt : s₀ < T + ((N + 1 + 1 : ℕ) : ℝ) := by dsimp [s₀]; push_cast; linarith
      -- Two-sided L²(cell) continuity of Z at s₀ > T (since Ici T ∈ 𝓝 s₀!)
      have hcont_s₀ : Tendsto (fun s => cylSliceL2 p.c (fun y => Z (s, y) - Z (s₀, y)))
          (𝓝 s₀) (𝓝 0) := by
        have hnhds_eq : 𝓝[Ici T] s₀ = 𝓝 s₀ := nhdsWithin_eq_nhds.2 (Ici_mem_nhds hs₀_gt)
        have hH1 := hcont_Ici s₀ hs₀_gt.le
        rw [hnhds_eq] at hH1
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hH1
          (fun _ => zero_le) (fun _ => le_self_add.trans le_self_add)
      have heq_R_slab : ∀ Φ, IsPlanarSolTest Φ →
          (∀ i, tsupport (fun x => Φ x i) ⊆ Ioo s₀ (T + ((N + 1 + 1 : ℕ) : ℝ)) ×ˢ univ) →
          ∫ x, (∑ i : Fin 2, Z x i * meridTranspose p.ν Φ x i +
              cdot (flatBv p.train Z Zq Zη) Φ x) = ∫ x, cdot g_tail Φ x := by
        intro Φ hΦ hΦ_supp
        have hsub : ∀ i, tsupport (fun x => Φ x i) ⊆
            Ioo (T + ((N + 1 : ℕ) : ℝ)) (T + ((N + 1 : ℕ) : ℝ) + 1) ×ˢ univ := by
          intro i x hx
          have hmem := hΦ_supp i hx
          refine ⟨⟨hmem.1.1, ?_⟩, trivial⟩
          have : T + ((N + 1 + 1 : ℕ) : ℝ) = T + ((N + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
          linarith [hmem.1.2]
        refine (heq_unit_slab (N + 1) Φ hΦ hsub).trans
          (integral_congr_ae (Eventually.of_forall fun x => ?_))
        by_cases hx : T < x.1
        · have hgx : g_tail x = ofRealProf g x :=
            Set.indicator_of_mem (a := x) (s := Ioi T ×ˢ univ) ⟨mem_Ioi.2 hx, trivial⟩ (ofRealProf g)
          simp only [cdot, hgx]
        · have hΦ0 : ∀ i : Fin 2, Φ x i = 0 := fun i =>
            image_eq_zero_of_notMem_tsupport (f := fun y => Φ y i)
              (fun hmem => hx (hs₀_gt.trans (hΦ_supp i hmem).1.1))
          simp [cdot, hΦ0]
      exact glue_equation_at_seam p hT hs₀_gt hs₀_lt
        hZ_sm hZq_sm hZη_sm hg_tail_sm hZ_per hZq_per hZη_per hg_tail_per
        (fun a b _ => hZ_loc a b) hg_tail_loc (hsl_all s₀).memL2_u hcont_s₀
        ih heq_R_slab
  -- Assemble IsTailMeridionalSolution p T (ofRealProf g) Z Zq Zη
  refine ⟨Z, Zq, Zη, hZ_sm, hZq_sm, hZη_sm, hZ_per, hZq_per, hZη_per, hinit_T, ?_, hcont_Ici⟩
  refine {
    periodic := Eventually.of_forall fun x _ => hper_all x
    weak_q := fun i φ hφ _ => ⟨((hwq_Z i).1 φ hφ).1, ((hwq_Z i).1 φ hφ).2, (hwq_Z i).2 φ hφ⟩
    weak_eta := fun i φ hφ _ => ⟨((hwη_Z i).1 φ hφ).1, ((hwη_Z i).1 φ hφ).2, (hwη_Z i).2 φ hφ⟩
    solenoidal := fun φ hφ _ => hsol_Z φ hφ
    equation := fun Ψ hΨ hΨ_supp => by
      obtain ⟨hIM, hIB, hIG_tail⟩ :=
        integrable_pde_terms p hZ_sm hZq_sm hZη_sm hg_tail_sm hZ_per hZq_per hZη_per hg_tail_per
          (fun a b _ => hZ_loc a b) hg_tail_loc hΨ
      have hcdot_eq : cdot (ofRealProf g) Ψ = cdot g_tail Ψ := by
        funext x
        by_cases hx : T < x.1
        · have hgx : g_tail x = ofRealProf g x :=
            Set.indicator_of_mem (a := x) (s := Ioi T ×ˢ univ) ⟨mem_Ioi.2 hx, trivial⟩ (ofRealProf g)
          simp only [cdot, hgx]
        · have hΨ0 : ∀ i : Fin 2, Ψ x i = 0 := fun i =>
            image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) (fun hmem => hx (hΨ_supp i hmem).1)
          simp [cdot, hΨ0]
      obtain ⟨a0, b0', _, _, _, _, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 0)
      obtain ⟨a1, b1', _, _, _, _, hbox1⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 1)
      obtain ⟨N, hN⟩ := exists_nat_gt (max b0' b1' - T)
      have hΨ_N : ∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo T (T + ((N + 1 : ℕ) : ℝ)) ×ˢ univ := by
        intro i
        have hbox_le : ∀ x ∈ Function.support (fun y => Ψ y i), x.1 ≤ max b0' b1' := by
          intro x hx
          rw [Function.mem_support] at hx
          fin_cases i
          · by_contra hgt; rw [not_le] at hgt
            exact hx ((hbox0 x (Or.inl fun hm => not_le_of_gt hgt (hm.2.trans (le_max_left _ _)))).1)
          · by_contra hgt; rw [not_le] at hgt
            exact hx ((hbox1 x (Or.inl fun hm => not_le_of_gt hgt (hm.2.trans (le_max_right _ _)))).1)
        have htsupp_le : tsupport (fun y => Ψ y i) ⊆ Iic (max b0' b1') ×ˢ univ :=
          closure_minimal (fun x hx => ⟨hbox_le x hx, trivial⟩) (isClosed_Iic.prod isClosed_univ)
        intro x hx
        refine ⟨⟨(hΨ_supp i hx).1, ?_⟩, trivial⟩
        have h1 : x.1 ≤ max b0' b1' := (htsupp_le hx).1
        push_cast; linarith
      exact ⟨hIM, hIB, hcdot_eq ▸ hIG_tail, hcdot_eq ▸ heq_prefix N Ψ hΨ hΨ_N⟩
  }

end UnforcedLeray.Short.IIb.TailExistenceAux

namespace UnforcedLeray.Short.IIb

open TailExistenceAux

/-- **Conditional target theorem for `PartII-b:F7/2/1` (`MeridionalTailExistence`)**:
proves `MeridionalTailExistence` unconditionally (`0 sorry`) from the single real unit-interval
2D cylinder Oseen/Stokes `H¹_σ(C_c)` evolution leaf `TailExistenceAux.RealCylUnitOseenStep`. -/
private theorem meridionalTailExistence_of_unitStep
    (hStep : TailExistenceAux.RealCylUnitOseenStep) :
    UnforcedLeray.Short.IIb.MeridionalTailExistence := by
  intro p d dm dp T hbg hT u uq uη hu g gq gη hg hg_int
  have hc : 0 < p.c := p.c_pos
  -- 1. Upgrade initial slice (u, uq, uη) via toCell p.c and split into real / imaginary parts
  let up := fun y => u (toCell p.c y)
  let uqp := fun y => uq (toCell p.c y)
  let uηp := fun y => uη (toCell p.c y)
  obtain ⟨hup_h1, hup_diff⟩ := isCylH1Slice_toCell hc hu
  have hup_per_re : ∀ y : B0579.Plane,
      reSlice up (y.1 + p.c, y.2) = reSlice up y ∧
        reSlice uqp (y.1 + p.c, y.2) = reSlice uqp y ∧
        reSlice uηp (y.1 + p.c, y.2) = reSlice uηp y := by
    intro y
    refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩ <;>
      { dsimp only [reSlice, up, uqp, uηp]; rw [toCell_periodic hc] }
  have hup_per_im : ∀ y : B0579.Plane,
      imSlice up (y.1 + p.c, y.2) = imSlice up y ∧
        imSlice uqp (y.1 + p.c, y.2) = imSlice uqp y ∧
        imSlice uηp (y.1 + p.c, y.2) = imSlice uηp y := by
    intro y
    refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩ <;>
      { simp only [imSlice_apply]; dsimp only [up, uqp, uηp]; rw [toCell_periodic hc] }
  -- 2. Upgrade tail source (g, gq, gη) on Ioi T and split into real / imaginary parts
  obtain ⟨g₁, gq₁, gη₁, hg₁_sm, hgq₁_sm, hgη₁_sm, hg₁_per, hg₁_h1, hg₁_ae, hg₁_le⟩ :=
    upgradeTailSource hc hT hg hg_int
  have hg₁_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g₁ gq₁ gη₁ s) < ⊤ :=
    (lintegral_mono hg₁_le).trans_lt hg_int
  have hg_re_per : ∀ x : Coord, reProf g₁ (qShift p.c x) = reProf g₁ x ∧
      reProf gq₁ (qShift p.c x) = reProf gq₁ x ∧
      reProf gη₁ (qShift p.c x) = reProf gη₁ x := by
    intro x
    refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
    · dsimp only [reProf]; rw [(hg₁_per x).1]
    · dsimp only [reProf]; rw [(hg₁_per x).2.1]
    · dsimp only [reProf]; rw [(hg₁_per x).2.2]
  have hg_im_per : ∀ x : Coord, imProf g₁ (qShift p.c x) = imProf g₁ x ∧
      imProf gq₁ (qShift p.c x) = imProf gq₁ x ∧
      imProf gη₁ (qShift p.c x) = imProf gη₁ x := by
    intro x
    refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
    · simp only [imProf_apply]; rw [(hg₁_per x).1]
    · simp only [imProf_apply]; rw [(hg₁_per x).2.1]
    · simp only [imProf_apply]; rw [(hg₁_per x).2.2]
  have hg_re_h1 : ∀ s : ℝ, IsCylH1Slice p.c (fun y => ofRealProf (reProf g₁) (s, y))
      (fun y => ofRealProf (reProf gq₁) (s, y))
      (fun y => ofRealProf (reProf gη₁) (s, y)) := fun s => isCylH1Slice_re p.c (hg₁_h1 s)
  have hg_im_h1 : ∀ s : ℝ, IsCylH1Slice p.c (fun y => ofRealProf (imProf g₁) (s, y))
      (fun y => ofRealProf (imProf gq₁) (s, y))
      (fun y => ofRealProf (imProf gη₁) (s, y)) := fun s => isCylH1Slice_im p.c (hg₁_h1 s)
  have hg_re_int : (∫⁻ s in Ioi T, sliceH1Norm p.c
      (ofRealProf (reProf g₁)) (ofRealProf (reProf gq₁)) (ofRealProf (reProf gη₁)) s) < ⊤ :=
    (lintegral_mono (sliceH1Norm_ofRealProf_reProf_le p.c g₁ gq₁ gη₁)).trans_lt hg₁_int
  have hg_im_int : (∫⁻ s in Ioi T, sliceH1Norm p.c
      (ofRealProf (imProf g₁)) (ofRealProf (imProf gq₁)) (ofRealProf (imProf gη₁)) s) < ⊤ :=
    (lintegral_mono (sliceH1Norm_ofRealProf_imProf_le p.c g₁ gq₁ gη₁)).trans_lt hg₁_int
  -- 3. Solve real and imaginary tail evolutions on [T, ∞)
  obtain ⟨ZR, ZqR, ZηR, hZR_sm, hZqR_sm, hZηR_sm, _, _, _, hinitR, hsolR, hcontR⟩ :=
    realTailExistence_of_unitStep hStep hbg hT
      (stronglyMeasurable_reSlice hup_h1.sm_u)
      (stronglyMeasurable_reSlice hup_h1.sm_uq)
      (stronglyMeasurable_reSlice hup_h1.sm_uη)
      hup_per_re (isCylH1Slice_re p.c hup_h1)
      (stronglyMeasurable_reProf hg₁_sm)
      (stronglyMeasurable_reProf hgq₁_sm)
      (stronglyMeasurable_reProf hgη₁_sm)
      hg_re_per hg_re_h1 hg_re_int
  obtain ⟨ZI, ZqI, ZηI, hZI_sm, hZqI_sm, hZηI_sm, _, _, _, hinitI, hsolI, hcontI⟩ :=
    realTailExistence_of_unitStep hStep hbg hT
      (stronglyMeasurable_imSlice hup_h1.sm_u)
      (stronglyMeasurable_imSlice hup_h1.sm_uq)
      (stronglyMeasurable_imSlice hup_h1.sm_uη)
      hup_per_im (isCylH1Slice_im p.c hup_h1)
      (stronglyMeasurable_imProf hg₁_sm)
      (stronglyMeasurable_imProf hgq₁_sm)
      (stronglyMeasurable_imProf hgη₁_sm)
      hg_im_per hg_im_h1 hg_im_int
  -- 4. Recombine z₂ = ZR + I • ZI
  let z₂ : CProf := fun x => ZR x + Complex.I • ZI x
  let zq₂ : CProf := fun x => ZqR x + Complex.I • ZqI x
  let zη₂ : CProf := fun x => ZηR x + Complex.I • ZηI x
  have hz₂_sm : StronglyMeasurable z₂ := hZR_sm.add (hZI_sm.const_smul Complex.I)
  have hzq₂_sm : StronglyMeasurable zq₂ := hZqR_sm.add (hZqI_sm.const_smul Complex.I)
  have hzη₂_sm : StronglyMeasurable zη₂ := hZηR_sm.add (hZηI_sm.const_smul Complex.I)
  have hcomb_L2 : ∀ (A B : B0579.Plane → CMerid),
      StronglyMeasurable A → StronglyMeasurable B →
      cylSliceL2 p.c (fun y => A y + Complex.I • B y) ≤ cylSliceL2 p.c A + cylSliceL2 p.c B := by
    intro A B hA hB
    have hI : cylSliceL2 p.c (fun y => Complex.I • B y) = cylSliceL2 p.c B :=
      cylSliceL2_unit_smul p.c (by simp) B
    unfold cylSliceL2 at hI ⊢
    rw [← hI]
    exact eLpNorm_add_le hA.aestronglyMeasurable
      (hB.const_smul Complex.I).aestronglyMeasurable (by norm_num)
  have hcomb_H1 : ∀ (A Aq Aη B Bq Bη : B0579.Plane → CMerid),
      StronglyMeasurable A → StronglyMeasurable Aq → StronglyMeasurable Aη →
      StronglyMeasurable B → StronglyMeasurable Bq → StronglyMeasurable Bη →
      cylSliceH1 p.c (fun y => A y + Complex.I • B y)
        (fun y => Aq y + Complex.I • Bq y) (fun y => Aη y + Complex.I • Bη y) ≤
      cylSliceH1 p.c A Aq Aη + cylSliceH1 p.c B Bq Bη := by
    intro A Aq Aη B Bq Bη hA hAq hAη hB hBq hBη
    have hRearr : ∀ a1 b1 a2 b2 a3 b3 : ℝ≥0∞,
        (a1 + b1) + (a2 + b2) + (a3 + b3) = (a1 + a2 + a3) + (b1 + b2 + b3) :=
      fun _ _ _ _ _ _ => by ac_rfl
    exact (add_le_add (add_le_add (hcomb_L2 A B hA hB) (hcomb_L2 Aq Bq hAq hBq))
      (hcomb_L2 Aη Bη hAη hBη)).trans_eq (hRearr _ _ _ _ _ _)
  -- Initial slice at T: z₂(T) - u = (z₂(T) - up) + (up - u)
  have hinit_up : cylSliceH1 p.c (fun y => z₂ (T, y) - up y)
      (fun y => zq₂ (T, y) - uqp y) (fun y => zη₂ (T, y) - uηp y) = 0 := by
    have heq_u : (fun y => z₂ (T, y) - up y) =
        fun y => (ZR (T, y) - ofRealSlice (reSlice up) y) +
          Complex.I • (ZI (T, y) - ofRealSlice (imSlice up) y) := by
      funext y; rw [← ofRealSlice_re_im up y]; dsimp [z₂]; rw [smul_sub]; abel
    have heq_uq : (fun y => zq₂ (T, y) - uqp y) =
        fun y => (ZqR (T, y) - ofRealSlice (reSlice uqp) y) +
          Complex.I • (ZqI (T, y) - ofRealSlice (imSlice uqp) y) := by
      funext y; rw [← ofRealSlice_re_im uqp y]; dsimp [zq₂]; rw [smul_sub]; abel
    have heq_uη : (fun y => zη₂ (T, y) - uηp y) =
        fun y => (ZηR (T, y) - ofRealSlice (reSlice uηp) y) +
          Complex.I • (ZηI (T, y) - ofRealSlice (imSlice uηp) y) := by
      funext y; rw [← ofRealSlice_re_im uηp y]; dsimp [zη₂]; rw [smul_sub]; abel
    rw [heq_u, heq_uq, heq_uη]
    refine le_antisymm ?_ zero_le
    refine (hcomb_H1
      (fun y => ZR (T, y) - ofRealSlice (reSlice up) y)
      (fun y => ZqR (T, y) - ofRealSlice (reSlice uqp) y)
      (fun y => ZηR (T, y) - ofRealSlice (reSlice uηp) y)
      (fun y => ZI (T, y) - ofRealSlice (imSlice up) y)
      (fun y => ZqI (T, y) - ofRealSlice (imSlice uqp) y)
      (fun y => ZηI (T, y) - ofRealSlice (imSlice uηp) y)
      ((hZR_sm.comp_measurable measurable_prodMk_left).sub
        (stronglyMeasurable_ofRealSlice (stronglyMeasurable_reSlice hup_h1.sm_u)))
      ((hZqR_sm.comp_measurable measurable_prodMk_left).sub
        (stronglyMeasurable_ofRealSlice (stronglyMeasurable_reSlice hup_h1.sm_uq)))
      ((hZηR_sm.comp_measurable measurable_prodMk_left).sub
        (stronglyMeasurable_ofRealSlice (stronglyMeasurable_reSlice hup_h1.sm_uη)))
      ((hZI_sm.comp_measurable measurable_prodMk_left).sub
        (stronglyMeasurable_ofRealSlice (stronglyMeasurable_imSlice hup_h1.sm_u)))
      ((hZqI_sm.comp_measurable measurable_prodMk_left).sub
        (stronglyMeasurable_ofRealSlice (stronglyMeasurable_imSlice hup_h1.sm_uq)))
      ((hZηI_sm.comp_measurable measurable_prodMk_left).sub
        (stronglyMeasurable_ofRealSlice (stronglyMeasurable_imSlice hup_h1.sm_uη)))).trans ?_
    simpa using add_le_add (le_of_eq hinitR) (le_of_eq hinitI)
  have hinit_u : cylSliceH1 p.c (fun y => z₂ (T, y) - u y)
      (fun y => zq₂ (T, y) - uq y) (fun y => zη₂ (T, y) - uη y) = 0 := by
    refine le_antisymm ?_ zero_le
    refine (cylSliceH1_triangle p.c
      (u := fun y => z₂ (T, y)) (uq := fun y => zq₂ (T, y)) (uη := fun y => zη₂ (T, y))
      (v := up) (vq := uqp) (vη := uηp)
      (w := u) (wq := uq) (wη := uη)
      (hz₂_sm.comp_measurable measurable_prodMk_left)
      (hzq₂_sm.comp_measurable measurable_prodMk_left)
      (hzη₂_sm.comp_measurable measurable_prodMk_left)
      hup_h1.sm_u hup_h1.sm_uq hup_h1.sm_uη
      hu.sm_u hu.sm_uq hu.sm_uη).trans ?_
    rw [hinit_up, hup_diff, add_zero]
  -- Continuity of z₂ on [T, ∞)
  have hcont_z₂ : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0) := by
    intro s hsT
    have hsum : Tendsto (fun s' =>
        cylSliceH1 p.c (fun y => ZR (s', y) - ZR (s, y))
          (fun y => ZqR (s', y) - ZqR (s, y)) (fun y => ZηR (s', y) - ZηR (s, y)) +
        cylSliceH1 p.c (fun y => ZI (s', y) - ZI (s, y))
          (fun y => ZqI (s', y) - ZqI (s, y)) (fun y => ZηI (s', y) - ZηI (s, y)))
        (𝓝[Ici T] s) (𝓝 0) := by
      simpa using (hcontR s hsT).add (hcontI s hsT)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun s' => ?_
    have heq_u : (fun y => z₂ (s', y) - z₂ (s, y)) =
        fun y => (ZR (s', y) - ZR (s, y)) + Complex.I • (ZI (s', y) - ZI (s, y)) := by
      funext y; dsimp [z₂]; rw [smul_sub]; abel
    have heq_uq : (fun y => zq₂ (s', y) - zq₂ (s, y)) =
        fun y => (ZqR (s', y) - ZqR (s, y)) + Complex.I • (ZqI (s', y) - ZqI (s, y)) := by
      funext y; dsimp [zq₂]; rw [smul_sub]; abel
    have heq_uη : (fun y => zη₂ (s', y) - zη₂ (s, y)) =
        fun y => (ZηR (s', y) - ZηR (s, y)) + Complex.I • (ZηI (s', y) - ZηI (s, y)) := by
      funext y; dsimp [zη₂]; rw [smul_sub]; abel
    rw [heq_u, heq_uq, heq_uη]
    exact hcomb_H1
      (fun y => ZR (s', y) - ZR (s, y))
      (fun y => ZqR (s', y) - ZqR (s, y))
      (fun y => ZηR (s', y) - ZηR (s, y))
      (fun y => ZI (s', y) - ZI (s, y))
      (fun y => ZqI (s', y) - ZqI (s, y))
      (fun y => ZηI (s', y) - ZηI (s, y))
      ((hZR_sm.comp_measurable measurable_prodMk_left).sub
        (hZR_sm.comp_measurable measurable_prodMk_left))
      ((hZqR_sm.comp_measurable measurable_prodMk_left).sub
        (hZqR_sm.comp_measurable measurable_prodMk_left))
      ((hZηR_sm.comp_measurable measurable_prodMk_left).sub
        (hZηR_sm.comp_measurable measurable_prodMk_left))
      ((hZI_sm.comp_measurable measurable_prodMk_left).sub
        (hZI_sm.comp_measurable measurable_prodMk_left))
      ((hZqI_sm.comp_measurable measurable_prodMk_left).sub
        (hZqI_sm.comp_measurable measurable_prodMk_left))
      ((hZηI_sm.comp_measurable measurable_prodMk_left).sub
        (hZηI_sm.comp_measurable measurable_prodMk_left))
  -- Assemble IsTailMeridionalSolution p T g z₂ zq₂ zη₂
  refine ⟨z₂, zq₂, zη₂, hz₂_sm, hzq₂_sm, hzη₂_sm, hinit_u, ?_, hcont_z₂⟩
  refine {
    periodic := by
      filter_upwards [hsolR.periodic, hsolI.periodic] with x hxR hxI hxT
      obtain ⟨r1, r2, r3⟩ := hxR hxT
      obtain ⟨i1, i2, i3⟩ := hxI hxT
      exact ⟨by simp [z₂, r1, i1], by simp [zq₂, r2, i2], by simp [zη₂, r3, i3]⟩
    weak_q := fun k φ hφ hsupp => by
      obtain ⟨hR1, hR2, hReq⟩ := hsolR.weak_q k φ hφ hsupp
      obtain ⟨hI1, hI2, hIeq⟩ := hsolI.weak_q k φ hφ hsupp
      have e1 : (fun x => z₂ x k * (coordTranspose vQ0 dZero φ x : ℂ)) =
          fun x => ZR x k * (coordTranspose vQ0 dZero φ x : ℂ) +
            Complex.I * (ZI x k * (coordTranspose vQ0 dZero φ x : ℂ)) := by
        funext x; simp [z₂, PiLp.add_apply, PiLp.smul_apply]; ring
      have e2 : (fun x => zq₂ x k * (φ x : ℂ)) =
          fun x => ZqR x k * (φ x : ℂ) + Complex.I * (ZqI x k * (φ x : ℂ)) := by
        funext x; simp [zq₂, PiLp.add_apply, PiLp.smul_apply]; ring
      refine ⟨e1 ▸ (hR1.add (hI1.const_mul Complex.I)),
        e2 ▸ (hR2.add (hI2.const_mul Complex.I)), ?_⟩
      rw [e1, e2, integral_add hR2 (hI2.const_mul Complex.I),
        integral_add hR1 (hI1.const_mul Complex.I), integral_const_mul, integral_const_mul,
        hReq, hIeq]
    weak_eta := fun k φ hφ hsupp => by
      obtain ⟨hR1, hR2, hReq⟩ := hsolR.weak_eta k φ hφ hsupp
      obtain ⟨hI1, hI2, hIeq⟩ := hsolI.weak_eta k φ hφ hsupp
      have e1 : (fun x => z₂ x k * (coordTranspose vEta dZero φ x : ℂ)) =
          fun x => ZR x k * (coordTranspose vEta dZero φ x : ℂ) +
            Complex.I * (ZI x k * (coordTranspose vEta dZero φ x : ℂ)) := by
        funext x; simp [z₂, PiLp.add_apply, PiLp.smul_apply]; ring
      have e2 : (fun x => zη₂ x k * (φ x : ℂ)) =
          fun x => ZηR x k * (φ x : ℂ) + Complex.I * (ZηI x k * (φ x : ℂ)) := by
        funext x; simp [zη₂, PiLp.add_apply, PiLp.smul_apply]; ring
      refine ⟨e1 ▸ (hR1.add (hI1.const_mul Complex.I)),
        e2 ▸ (hR2.add (hI2.const_mul Complex.I)), ?_⟩
      rw [e1, e2, integral_add hR2 (hI2.const_mul Complex.I),
        integral_add hR1 (hI1.const_mul Complex.I), integral_const_mul, integral_const_mul,
        hReq, hIeq]
    solenoidal := fun φ hφ hsupp => by
      obtain ⟨hR_int, hR0⟩ := hsolR.solenoidal φ hφ hsupp
      obtain ⟨hI_int, hI0⟩ := hsolI.solenoidal φ hφ hsupp
      have heq : (fun x => z₂ x 0 * (cpd 1 φ x : ℂ) + z₂ x 1 * (cpd 2 φ x : ℂ)) =
          fun x => (ZR x 0 * (cpd 1 φ x : ℂ) + ZR x 1 * (cpd 2 φ x : ℂ)) +
            Complex.I * (ZI x 0 * (cpd 1 φ x : ℂ) + ZI x 1 * (cpd 2 φ x : ℂ)) := by
        funext x; simp [z₂, PiLp.add_apply, PiLp.smul_apply]; ring
      refine ⟨heq ▸ (hR_int.add (hI_int.const_mul Complex.I)), ?_⟩
      rw [heq, integral_add hR_int (hI_int.const_mul Complex.I), integral_const_mul,
        hR0, hI0, mul_zero, add_zero]
    equation := fun Ψ hΨ hsupp => by
      obtain ⟨hRM, hRB, hRG, hReq⟩ := hsolR.equation Ψ hΨ hsupp
      obtain ⟨hIM, hIB, hIG, hIeq⟩ := hsolI.equation Ψ hΨ hsupp
      have eM : (fun x => ∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i) =
          fun x => (∑ i : Fin 2, ZR x i * meridTranspose p.ν Ψ x i) +
            Complex.I * (∑ i : Fin 2, ZI x i * meridTranspose p.ν Ψ x i) := by
        funext x; simp [z₂, Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply]; ring
      have eB : cdot (flatBv p.train z₂ zq₂ zη₂) Ψ =
          fun x => cdot (flatBv p.train ZR ZqR ZηR) Ψ x +
            Complex.I * cdot (flatBv p.train ZI ZqI ZηI) Ψ x := by
        funext x
        simp only [cdot, flatBv, z₂, zq₂, zη₂, Fin.sum_univ_two,
          PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
        ring
      have eG₁ : cdot g₁ Ψ =
          fun x => cdot (ofRealProf (reProf g₁)) Ψ x +
            Complex.I * cdot (ofRealProf (imProf g₁)) Ψ x := by
        funext x
        have hg1x := (ofRealProf_re_im g₁ x).symm
        conv_lhs => rw [show cdot g₁ Ψ x = ∑ i : Fin 2, g₁ x i * (Ψ x i : ℂ) from rfl, hg1x]
        simp [cdot, Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply]; ring
      have hae_g : cdot g Ψ =ᵐ[volume] cdot g₁ Ψ := by
        filter_upwards [hg₁_ae] with x hx
        by_cases hxT : T < x.1
        · simp [cdot, (hx hxT).1]
        · have hΨ0 : ∀ i : Fin 2, Ψ x i = 0 := fun i =>
            image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) (fun hmem => hxT (hsupp i hmem).1)
          simp [cdot, hΨ0]
      have hG₁_int : Integrable (cdot g₁ Ψ) volume :=
        eG₁ ▸ (hRG.add (hIG.const_mul Complex.I))
      have hM_int : Integrable (fun x => ∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i) volume :=
        eM ▸ (hRM.add (hIM.const_mul Complex.I))
      have hB_int : Integrable (cdot (flatBv p.train z₂ zq₂ zη₂) Ψ) volume :=
        eB ▸ (hRB.add (hIB.const_mul Complex.I))
      refine ⟨hM_int, hB_int, hG₁_int.congr hae_g.symm, ?_⟩
      have hR_tot : Integrable (fun x => ∑ i : Fin 2, ZR x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train ZR ZqR ZηR) Ψ x) volume := hRM.add hRB
      have hI_tot : Integrable (fun x => ∑ i : Fin 2, ZI x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train ZI ZqI ZηI) Ψ x) volume := hIM.add hIB
      have hLHS : ∫ x, (∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train z₂ zq₂ zη₂) Ψ x) =
          (∫ x, (∑ i : Fin 2, ZR x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train ZR ZqR ZηR) Ψ x)) +
            Complex.I * ∫ x, (∑ i : Fin 2, ZI x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train ZI ZqI ZηI) Ψ x) := by
        refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans
          ((integral_add hR_tot (hI_tot.const_mul Complex.I)).trans
            (congrArg (_ + ·) (integral_const_mul Complex.I _)))
        have hm := congrFun eM x
        have hb := congrFun eB x
        dsimp only at hm hb ⊢
        rw [hm, hb]; ring
      have hRHS : ∫ x, cdot g Ψ x =
          (∫ x, cdot (ofRealProf (reProf g₁)) Ψ x) +
            Complex.I * ∫ x, cdot (ofRealProf (imProf g₁)) Ψ x := by
        rw [integral_congr_ae hae_g, eG₁, integral_add hRG (hIG.const_mul Complex.I),
          integral_const_mul]
      rw [hLHS, hRHS, hReq, hIeq]
  }

/-- **Target theorem for `PartII-b:F7/2/1` (`MeridionalTailExistence`)**:
unconditional meridional tail existence on `[T, ∞)` (`SP 2213–2217, 2289–2295`). -/
theorem meridionalTailExistence_proof : UnforcedLeray.Short.IIb.MeridionalTailExistence :=
  meridionalTailExistence_of_unitStep TailExistenceAux.realCylUnitOseenStep_proof

end UnforcedLeray.Short.IIb
