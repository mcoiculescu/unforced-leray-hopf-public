import UnforcedLeray.Short.PartI.Sub.PartI_T13
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.HmeanC2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanEnergy

/-!
# `PartI:T13/1` (`Sub/PartI_T13/SmoothL2.lean`): `OverlapFluctuationSmoothL2`

Source of record: `the November 2 reference manuscript`, lines 304-313, 389-396
(old 354-362).

Proves `overlapFluctuationSmoothL2_proof : OverlapFluctuationSmoothL2`:
1. `CellSmoothL2 1 U` for `U = overlapField ν c tr.v T` (`overlapField_cellSmoothL2`);
2. For any `U : Plane → Vec` with `CellSmoothL2 1 U`, the horizontal fluctuation `W = hfluct 1 U`
   satisfies `CellSmoothL2 1 W` and `wordComp w W k` is either `wordComp w U k` or
   `hfluct 1 (wordComp w U k)`;
3. Horizontal fluctuation is an `L²` contraction on each slice `Y` and hence on `Cyl.cell 1`, so
   `jetEnergy 1 j W ≤ jetEnergy 1 j U ≤ 2 * 2 ^ j * (cellL2 1 (jet j U)).toReal ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2)

/-! ### 1. Smoothness and word derivatives of `hmean 1` and `hfluct 1` -/

/-- For a `C^∞` scalar field `f : Plane → ℝ`, the horizontal average `hmean 1 f` is `C^n` for every
`n : ℕ`. -/
theorem hmean_unit_contDiff_nat (n : ℕ) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ n (hmean 1 f) := by
  induction n generalizing f with
  | zero =>
    exact contDiff_zero.2 (cpH2_continuous_hmean one_pos hf.continuous)
  | succ n ih =>
    push_cast
    rw [contDiff_succ_iff_deriv]
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
    refine ⟨fun e => (cpH2_hasDerivAt_hmean hf1 e).differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [cpH2_deriv_hmean hf1]
    exact ih (B0151.contDiff_derivWord hf [false])

/-- For a `C^∞` scalar field `f : Plane → ℝ`, the horizontal average `hmean 1 f` is `C^∞`. -/
theorem hmean_unit_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hmean 1 f) :=
  contDiff_infty.2 fun n => hmean_unit_contDiff_nat n hf

/-- For a `C^∞` scalar field `f : Plane → ℝ`, the horizontal fluctuation `hfluct 1 f` is `C^∞`. -/
theorem hfluct_unit_scalar_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hfluct 1 f) :=
  hf.sub ((hmean_unit_contDiff hf).comp contDiff_snd)

/-- Coordinate projection of `hfluct 1 a` on the unit cylinder. -/
theorem hfluct_unit_apply_vec {a : Plane → Vec} (ha : Continuous a) (z : Plane) (k : Fin 2) :
    (hfluct 1 a z) k = hfluct 1 (fun w => a w k) z := by
  have hint : Integrable (fun q : ℝ => a (q, z.2)) (volume.restrict (Ioc (-1 / 2) (1 / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hfluct hmean
  rw [PiLp.sub_apply, PiLp.smul_apply]
  congr 2
  simpa using h.symm

/-- For a `C^∞` vector field `U : Plane → Vec`, `hfluct 1 U` is `C^∞`. -/
theorem hfluct_unit_vec_contDiff {U : Plane → Vec} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (hfluct 1 U) := by
  refine contDiff_euclidean.2 fun k => ?_
  have hk : ContDiff ℝ ∞ (fun w : Plane => U w k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hU
  have heq : (fun z : Plane => (hfluct 1 U z) k) = hfluct 1 (fun w => U w k) := by
    funext z
    exact hfluct_unit_apply_vec hU.continuous z k
  rw [heq]
  exact hfluct_unit_scalar_contDiff hk

/-- If `U` is `1`-periodic in the horizontal variable, so is `hfluct 1 U`. -/
theorem hfluct_unit_isPeriodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Plane → E} (hper : Cyl.IsPeriodic 1 U) :
    Cyl.IsPeriodic 1 (hfluct 1 U) := by
  intro z
  unfold hfluct
  change U (z.1 + 1, z.2) - hmean 1 U z.2 = U z - hmean 1 U z.2
  rw [hper z]

/-- Horizontal derivative of `hfluct 1 g` equals `Cyl.partialQ g`. -/
theorem partialQ_hfluct_unit_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    Cyl.partialQ (hfluct 1 g) = Cyl.partialQ g := by
  funext z
  unfold Cyl.partialQ hfluct
  have hd1 : HasDerivAt (fun x : ℝ => g (x, z.2)) (deriv (fun x : ℝ => g (x, z.2)) z.1) z.1 :=
    ((hg.differentiable (by simp)).differentiableAt.comp z.1
      (differentiableAt_id.prodMk (differentiableAt_const z.2))).hasDerivAt
  have hd2 : HasDerivAt (fun _ : ℝ => hmean 1 g z.2) 0 z.1 :=
    hasDerivAt_const z.1 (hmean 1 g z.2)
  exact (hd1.sub hd2).deriv.trans (sub_zero _)

/-- Vertical derivative of `hfluct 1 g` equals `hfluct 1 (Cyl.partialEta g)`. -/
theorem partialEta_hfluct_unit_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    Cyl.partialEta (hfluct 1 g) = hfluct 1 (Cyl.partialEta g) := by
  funext z
  unfold Cyl.partialEta hfluct
  have hd1 : HasDerivAt (fun y : ℝ => g (z.1, y)) (Cyl.partialEta g z) z.2 :=
    Cyl.hasDerivAt_sliceEta (hg.differentiable (by simp)) z.1 z.2
  have hd2 : HasDerivAt (fun y : ℝ => hmean 1 g y) (hmean 1 (Cyl.partialEta g) z.2) z.2 :=
    cpH2_hasDerivAt_hmean (hg.of_le (by simp)) z.2
  exact (hd1.sub hd2).deriv

/-- For any word `w` and `C^∞` scalar field `f : Plane → ℝ`, `B0151.derivWord w (hfluct 1 f)` is
either `B0151.derivWord w f` or `hfluct 1 (B0151.derivWord w f)`. -/
theorem derivWord_hfluct_unit_or (w : List Bool) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    B0151.derivWord w (hfluct 1 f) = B0151.derivWord w f ∨
      B0151.derivWord w (hfluct 1 f) = hfluct 1 (B0151.derivWord w f) := by
  induction w with
  | nil => exact Or.inr rfl
  | cons b w' ih =>
    have hw' : ContDiff ℝ ∞ (B0151.derivWord w' f) := B0151.contDiff_derivWord hf w'
    rcases ih with h1 | h2
    · left
      cases b <;> simp [B0151.derivWord, h1]
    · cases b
      · right
        show Cyl.partialEta (B0151.derivWord w' (hfluct 1 f)) =
          hfluct 1 (Cyl.partialEta (B0151.derivWord w' f))
        rw [h2, partialEta_hfluct_unit_eq hw']
      · left
        show Cyl.partialQ (B0151.derivWord w' (hfluct 1 f)) =
          Cyl.partialQ (B0151.derivWord w' f)
        rw [h2, partialQ_hfluct_unit_eq hw']

/-- For any word `w`, coordinate `k : Fin 2`, and `C^∞` vector field `U : Plane → Vec`,
`wordComp w (hfluct 1 U) k` is either `wordComp w U k` or `hfluct 1 (wordComp w U k)`. -/
theorem wordComp_hfluct_unit_or (w : List Bool) {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    (k : Fin 2) :
    wordComp w (hfluct 1 U) k = wordComp w U k ∨
      wordComp w (hfluct 1 U) k = hfluct 1 (wordComp w U k) := by
  have hk : ContDiff ℝ ∞ (fun z : Plane => U z k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hU
  have heq : (fun z : Plane => (hfluct 1 U z) k) = hfluct 1 (fun z => U z k) := by
    funext z
    exact hfluct_unit_apply_vec hU.continuous z k
  unfold wordComp
  rw [heq]
  exact derivWord_hfluct_unit_or w hk

/-! ### 2. Slice and cell `L²` contraction for `hfluct 1` -/

/-- On each horizontal slice `Y`, `∫_{X ∈ [-1/2, 1/2)} (hfluct 1 g (X, Y))² ≤
∫_{X ∈ [-1/2, 1/2)} g(X, Y)²`. -/
theorem slice_integral_hfluct_unit_sq_le {g : Plane → ℝ} (hg : Continuous g) (Y : ℝ) :
    ∫ X in Ico (-1 / 2 : ℝ) (1 / 2), (hfluct 1 g (X, Y)) ^ 2 ≤
      ∫ X in Ico (-1 / 2 : ℝ) (1 / 2), g (X, Y) ^ 2 := by
  let μI : Measure ℝ := volume.restrict (Ico (-1 / 2 : ℝ) (1 / 2))
  set m : ℝ := hmean 1 g Y
  have hm_eq : m = ∫ X, g (X, Y) ∂μI := by
    have h := meanEnergy_hmean_Ico (c := 1) g Y
    simpa [m, μI] using h
  have hgY : Continuous (fun X : ℝ => g (X, Y)) :=
    hg.comp (continuous_id.prodMk continuous_const)
  have hi1 : Integrable (fun X : ℝ => g (X, Y)) μI :=
    hgY.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hi2 : Integrable (fun X : ℝ => g (X, Y) ^ 2) μI :=
    (hgY.pow 2).integrableOn_Icc.mono_set Ico_subset_Icc_self
  have him : Integrable (fun X : ℝ => 2 * m * g (X, Y)) μI := hi1.const_mul (2 * m)
  have hic : Integrable (fun _ : ℝ => m ^ 2) μI := by
    have : IsFiniteMeasure μI :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
    exact integrable_const (m ^ 2)
  have hpt : (fun X : ℝ => (hfluct 1 g (X, Y)) ^ 2) =
      fun X : ℝ => (g (X, Y) ^ 2 - 2 * m * g (X, Y)) + m ^ 2 := by
    funext X
    unfold hfluct
    change (g (X, Y) - m) ^ 2 = (g (X, Y) ^ 2 - 2 * m * g (X, Y)) + m ^ 2
    ring
  have hvol : ∫ _X, m ^ 2 ∂μI = m ^ 2 := by
    change ∫ _X in Ico (-1 / 2 : ℝ) (1 / 2), m ^ 2 = m ^ 2
    rw [setIntegral_const, Measure.real, Real.volume_Ico,
      show (1 / 2 : ℝ) - (-1 / 2) = 1 by ring, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul]
  have hlin : ∫ X, 2 * m * g (X, Y) ∂μI = 2 * m ^ 2 := by
    rw [integral_const_mul, ← hm_eq]
    ring
  have hexpand : ∫ X, (hfluct 1 g (X, Y)) ^ 2 ∂μI = (∫ X, g (X, Y) ^ 2 ∂μI) - m ^ 2 := by
    have h1 := integral_add (hi2.sub him) hic
    have h2 := integral_sub hi2 him
    dsimp only [Pi.add_apply, Pi.sub_apply] at h1 h2
    rw [hpt, h1, h2, hlin, hvol]
    ring
  change ∫ X, (hfluct 1 g (X, Y)) ^ 2 ∂μI ≤ ∫ X, g (X, Y) ^ 2 ∂μI
  rw [hexpand]
  linarith [sq_nonneg m]

/-- For a continuous scalar field `g ∈ L²(Cyl.cell 1)`, `hfluct 1 g ∈ L²(Cyl.cell 1)` and
`∫_{Cyl.cell 1} (hfluct 1 g)² ≤ ∫_{Cyl.cell 1} g²`. -/
theorem memLp_and_integral_hfluct_unit_sq_le {g : Plane → ℝ} (hg : Continuous g)
    (hgL2 : MemLp g 2 (Cyl.cellμ 1)) :
    MemLp (hfluct 1 g) 2 (Cyl.cellμ 1) ∧
      ∫ z in Cyl.cell 1, (hfluct 1 g z) ^ 2 ≤ ∫ z in Cyl.cell 1, g z ^ 2 := by
  let μI : Measure ℝ := volume.restrict (Ico (-1 / 2 : ℝ) (1 / 2))
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  have hprod_g : Integrable (fun z : Plane => g z ^ 2) (μI.prod volume) := by
    rw [← Cyl.cellμ_eq_prod 1]
    exact hgL2.integrable_sq
  let Φ : ℝ → ℝ := fun Y => 1⁻¹ * ∫ X in Ico (-1 / 2 : ℝ) (1 / 2), g (X, Y) ^ 2
  have hΦ_int : Integrable Φ volume := hprod_g.integral_prod_right.const_mul 1⁻¹
  have hΦ_prod : Integrable (fun z : Plane => Φ z.2) (Cyl.cellμ 1) := by
    rw [Cyl.cellμ_eq_prod 1]
    exact hΦ_int.comp_snd _
  have hm_cont : Continuous (fun z : Plane => hmean 1 g z.2) :=
    (cpH2_continuous_hmean one_pos hg).comp continuous_snd
  have hm_sq : ∀ z : Plane, (hmean 1 g z.2) ^ 2 ≤ Φ z.2 := fun z =>
    meanEnergy_hmean_sq_le one_pos hg (hg.pow 2) (fun _ => le_rfl) z.2
  have hm_mem : MemLp (fun z : Plane => hmean 1 g z.2) 2 (Cyl.cellμ 1) := by
    refine (memLp_two_iff_integrable_sq hm_cont.aestronglyMeasurable).2 ?_
    refine Integrable.mono' hΦ_prod (hm_cont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hm_sq z
  have hfluct_mem : MemLp (hfluct 1 g) 2 (Cyl.cellμ 1) := hgL2.sub hm_mem
  refine ⟨hfluct_mem, ?_⟩
  have hprod_w : Integrable (fun z : Plane => (hfluct 1 g z) ^ 2) (μI.prod volume) := by
    rw [← Cyl.cellμ_eq_prod 1]
    exact hfluct_mem.integrable_sq
  change ∫ z, (hfluct 1 g z) ^ 2 ∂(Cyl.cellμ 1) ≤ ∫ z, g z ^ 2 ∂(Cyl.cellμ 1)
  rw [Cyl.cellμ_eq_prod 1, MeasureTheory.integral_prod_symm _ hprod_w,
    MeasureTheory.integral_prod_symm _ hprod_g]
  exact integral_mono hprod_w.integral_prod_right hprod_g.integral_prod_right
    (fun Y => slice_integral_hfluct_unit_sq_le hg Y)

/-! ### 3. `CellSmoothL2 1 (hfluct 1 U)` and `jetEnergy` bound -/

/-- If `U : Plane → Vec` satisfies `CellSmoothL2 1 U`, then `W = hfluct 1 U` satisfies
`CellSmoothL2 1 W` and `∫_{Cyl.cell 1} (wordComp w W k)² ≤ ∫_{Cyl.cell 1} (wordComp w U k)²`
for every word `w` and coordinate `k : Fin 2`. -/
theorem cellSmoothL2_hfluct_unit {U : Plane → Vec} (hU : CellSmoothL2 1 U) :
    CellSmoothL2 1 (hfluct 1 U) ∧
      ∀ (w : List Bool) (k : Fin 2),
        ∫ z in Cyl.cell 1, (wordComp w (hfluct 1 U) k z) ^ 2 ≤
          ∫ z in Cyl.cell 1, (wordComp w U k z) ^ 2 := by
  have hword : ∀ (w : List Bool) (k : Fin 2),
      MemLp (wordComp w (hfluct 1 U) k) 2 (Cyl.cellμ 1) ∧
        ∫ z in Cyl.cell 1, (wordComp w (hfluct 1 U) k z) ^ 2 ≤
          ∫ z in Cyl.cell 1, (wordComp w U k z) ^ 2 := by
    intro w k
    have hg_cont : Continuous (wordComp w U k) :=
      (B0151.contDiff_derivWord
        ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hU.1) w).continuous
    have hg_L2 : MemLp (wordComp w U k) 2 (Cyl.cellμ 1) := hU.2.2 w k
    rcases wordComp_hfluct_unit_or w hU.1 k with heq | heq
    · rw [heq]
      exact ⟨hg_L2, le_rfl⟩
    · rw [heq]
      exact memLp_and_integral_hfluct_unit_sq_le hg_cont hg_L2
  refine ⟨⟨hfluct_unit_vec_contDiff hU.1, hfluct_unit_isPeriodic hU.2.1,
    fun w k => (hword w k).1⟩, fun w k => (hword w k).2⟩

/-- For `U : Plane → Vec` with `CellSmoothL2 1 U` and every `j : ℕ`,
`jetEnergy 1 j (hfluct 1 U) ≤ jetEnergy 1 j U`. -/
theorem jetEnergy_hfluct_unit_le {U : Plane → Vec} (hU : CellSmoothL2 1 U) (j : ℕ) :
    jetEnergy 1 j (hfluct 1 U) ≤ jetEnergy 1 j U := by
  obtain ⟨hW, hword_le⟩ := cellSmoothL2_hfluct_unit hU
  have hJW : jetEnergy 1 j (hfluct 1 U) = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell 1, (wordComp w (hfluct 1 U) k z) ^ 2 := by
    unfold jetEnergy jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [integral_finsetSum]
      · simp [sq]
      · exact fun k _ => (hW.2.2 w k).integrable_mul (hW.2.2 w k)
    · exact fun w _ => integrable_finsetSum _ fun k _ => (hW.2.2 w k).integrable_mul (hW.2.2 w k)
  have hJU : jetEnergy 1 j U = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell 1, (wordComp w U k z) ^ 2 := by
    unfold jetEnergy jetPair
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [integral_finsetSum]
      · simp [sq]
      · exact fun k _ => (hU.2.2 w k).integrable_mul (hU.2.2 w k)
    · exact fun w _ => integrable_finsetSum _ fun k _ => (hU.2.2 w k).integrable_mul (hU.2.2 w k)
  rw [hJW, hJU]
  exact Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun k _ => hword_le w k

/-- **Proof of `OverlapFluctuationSmoothL2` (`PartI:T13/1`)** (source lines 304-313, 389-396). -/
theorem overlapFluctuationSmoothL2_proof : OverlapFluctuationSmoothL2 := by
  intro ν c hν hc tr htr T hT
  let U := overlapField ν c tr.v T
  have hU : CellSmoothL2 1 U := overlapField_cellSmoothL2 hν hc tr htr hT
  obtain ⟨hW, _⟩ := cellSmoothL2_hfluct_unit hU
  refine ⟨hU, hW, fun j => ?_⟩
  obtain ⟨CL2, _, hBrL2⟩ := jetL2Bridge_proof j
  have hlt : cellL2 1 (jet j U) < ⊤ :=
    (hBrL2 1 le_rfl U hU).trans_lt ENNReal.ofReal_lt_top
  have hL2 : cellL2 1 (jet j U) ≤ ENNReal.ofReal (cellL2 1 (jet j U)).toReal :=
    le_of_eq (ENNReal.ofReal_toReal hlt.ne).symm
  exact (jetEnergy_hfluct_unit_le hU j).trans
    (jetEnergy_le_of_cellL2_le hU j ENNReal.toReal_nonneg hL2)

end UnforcedLeray.Short.PartI
