import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.EnergyLocInt
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.CoreToSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.SmoothToC1
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part III-a, task `PartIII-a:T19/3/1` (`TrainAdvectionEnergyIdentity`)

Source of record: `the November 2 reference manuscript` (SP), lines 3518-3527
(Step P5 of `prop:short-polynomial-causal`).

Proves `trainAdvectionEnergyIdentity : TrainAdvectionEnergyIdentity`:
for any causal zero-entrance energy solution `IsCausalEnergySolution c ν μ (trainVel tr) F b G`
around a BUC train `tr`, tested against any nonnegative `C¹` compactly supported weight `ψ` on
`(0, ∞)`, the weighted energy inequality holds with strain rate
`L(s) = (B0277.supNormD 1 (tr.v s)).toReal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace AdvectionEnergyAux

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Short.IIIa.CoreToSmoothAux
open UnforcedLeray.Short.IIIa.SmoothToC1Aux

/-! ### 1. Cell equality and train slice regularity / derivative bounds -/

lemma cell_eq_cylCell (c : ℝ) : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

/-- Smoothness of the spatial slice `tr.v s` for `s ≥ 0`. -/
lemma contDiff_train_slice {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have h1 : ContDiff ℝ ∞ (fun z : Plane => (s, z)) := contDiff_const.prodMk contDiff_id
  exact tr.isTrain.smooth_v.comp_contDiff h1 (fun z => ⟨hs, trivial⟩)

lemma contDiff_train_comp {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin 2) : ContDiff ℝ ∞ (fun z : Plane => tr.v s z i) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp (contDiff_train_slice tr hs)

lemma diff_train_comp {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (i : Fin 2) : Differentiable ℝ (fun z : Plane => tr.v s z i) :=
  (contDiff_train_comp tr hs i).differentiable (by simp)

lemma partialQ_vec_apply {v : Plane → Vec} (hv : Differentiable ℝ v) (z : Plane) (i : Fin 2) :
    UnforcedLeray.Cyl.partialQ (fun y => v y i) z = UnforcedLeray.Cyl.partialQ v z i := by
  have h := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z.1
    (UnforcedLeray.Cyl.hasDerivAt_sliceQ hv z.1 z.2)
  exact h.deriv

lemma partialEta_vec_apply {v : Plane → Vec} (hv : Differentiable ℝ v) (z : Plane) (i : Fin 2) :
    UnforcedLeray.Cyl.partialEta (fun y => v y i) z = UnforcedLeray.Cyl.partialEta v z i := by
  have h := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z.2
    (UnforcedLeray.Cyl.hasDerivAt_sliceEta hv z.1 z.2)
  exact h.deriv

lemma vec_norm_sq_eq (w : Vec) : w 0 ^ 2 + w 1 ^ 2 = ‖w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

lemma partialQ_sq_sum_le {v : Plane → Vec} (hv : Differentiable ℝ v) (z : Plane) :
    UnforcedLeray.Cyl.partialQ (fun y => v y 0) z ^ 2 +
      UnforcedLeray.Cyl.partialQ (fun y => v y 1) z ^ 2 ≤ ‖fderiv ℝ v z‖ ^ 2 := by
  rw [partialQ_vec_apply hv z 0, partialQ_vec_apply hv z 1, vec_norm_sq_eq,
    UnforcedLeray.Cyl.partialQ_eq_fderiv hv z]
  have h1 : ‖fderiv ℝ v z (1, 0)‖ ≤ ‖fderiv ℝ v z‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
    ContinuousLinearMap.le_opNorm (fderiv ℝ v z) (1, 0)
  have hnorm : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by
    simp [Prod.norm_def]
  rw [hnorm, mul_one] at h1
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

lemma partialEta_sq_sum_le {v : Plane → Vec} (hv : Differentiable ℝ v) (z : Plane) :
    UnforcedLeray.Cyl.partialEta (fun y => v y 0) z ^ 2 +
      UnforcedLeray.Cyl.partialEta (fun y => v y 1) z ^ 2 ≤ ‖fderiv ℝ v z‖ ^ 2 := by
  rw [partialEta_vec_apply hv z 0, partialEta_vec_apply hv z 1, vec_norm_sq_eq,
    UnforcedLeray.Cyl.partialEta_eq_fderiv hv z]
  have h1 : ‖fderiv ℝ v z (0, 1)‖ ≤ ‖fderiv ℝ v z‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
    ContinuousLinearMap.le_opNorm (fderiv ℝ v z) (0, 1)
  have hnorm : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by
    simp [Prod.norm_def]
  rw [hnorm, mul_one] at h1
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- For a BUC train, `B0277.supNormD 1 (tr.v s)` is finite and bounded on `[0, S]`, and bounds
`‖fderiv ℝ (tr.v s) z‖` pointwise. -/
lemma supNormD_one_bound_on {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {S : ℝ} (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc 0 S,
      UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤ ENNReal.ofReal M ∧
      (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal ≤ M ∧
      ∀ z : Plane, ‖fderiv ℝ (tr.v s) z‖ ≤ (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal := by
  obtain ⟨M₀, hM₀⟩ := htr.deriv_bound hS 1
  refine ⟨max M₀ 0, le_max_right _ _, fun s hs => ?_⟩
  have hle : UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤ ENNReal.ofReal (max M₀ 0) :=
    UnforcedLeray.B0277.supNormD_le_ofReal fun z => (hM₀ s hs z).trans (le_max_left _ _)
  have hlt : UnforcedLeray.B0277.supNormD 1 (tr.v s) < ⊤ :=
    lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have htoReal : (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal ≤ max M₀ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this
  refine ⟨hle, htoReal, fun z => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ ≤ (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal := by
    apply UnforcedLeray.B0277.norm_le_of_supNormD_le ENNReal.toReal_nonneg _ z
    rw [ENNReal.ofReal_toReal hlt.ne]
  simpa [norm_iteratedFDeriv_one] using h1

lemma trainVel_bound_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {S : ℝ} (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 < M ∧ ∀ s ≤ S, ∀ x : ℝ × ℝ, ∀ i : Fin 2,
      ‖(trainVel tr s x i : ℂ)‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound hS
  refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun s hs x i => ?_⟩
  rw [Complex.norm_real]
  unfold trainVel
  split_ifs with hs0
  · have h1 : ‖tr.v s x i‖ ≤ ‖tr.v s x‖ := PiLp.norm_apply_le (tr.v s x) i
    exact (h1.trans (hM₀ s ⟨hs0, hs⟩ x)).trans (le_max_left _ _)
  · simp

lemma tnorm2_flatMult_sq_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) {p : ℝ × (ℝ × ℝ)} {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ i : Fin 2, ‖(trainVel tr p.1 p.2 i : ℂ)‖ ≤ M) :
    tnorm2 (flatMult tr u p) ^ 2 ≤ 8 * M ^ 2 * vnorm2 (u p) ^ 2 := by
  rw [domEN_tnorm2_sq, domEN_vnorm2_sq]
  have hij : ∀ i j : Fin 2, ‖flatMult tr u p i j‖ ^ 2 ≤
      2 * M ^ 2 * ‖u p j‖ ^ 2 + 2 * M ^ 2 * ‖u p i‖ ^ 2 := by
    intro i j
    have h1 : ‖flatMult tr u p i j‖ ≤ M * ‖u p j‖ + ‖u p i‖ * M := by
      unfold flatMult
      calc ‖(trainVel tr p.1 p.2 i : ℂ) * u p j + u p i * (trainVel tr p.1 p.2 j : ℂ)‖
          ≤ ‖(trainVel tr p.1 p.2 i : ℂ) * u p j‖ + ‖u p i * (trainVel tr p.1 p.2 j : ℂ)‖ :=
            norm_add_le _ _
        _ = ‖(trainVel tr p.1 p.2 i : ℂ)‖ * ‖u p j‖ + ‖u p i‖ * ‖(trainVel tr p.1 p.2 j : ℂ)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ M * ‖u p j‖ + ‖u p i‖ * M :=
            add_le_add (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hM j) (norm_nonneg _))
    have h2 : ‖flatMult tr u p i j‖ ^ 2 ≤ (M * ‖u p j‖ + ‖u p i‖ * M) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (M * ‖u p j‖ - ‖u p i‖ * M)]
  calc ∑ i : Fin 2, ∑ j : Fin 2, ‖flatMult tr u p i j‖ ^ 2
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, (2 * M ^ 2 * ‖u p j‖ ^ 2 + 2 * M ^ 2 * ‖u p i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = 8 * M ^ 2 * ∑ i : Fin 2, ‖u p i‖ ^ 2 := by
        simp only [Fin.sum_univ_two]
        ring

/-! ### 2. Measurability of `s ↦ (B0277.supNormD 1 (tr.v s)).toReal` on `(0, ∞)` -/

/-- For each `z : Plane`, `s ↦ fderiv ℝ (tr.v s) z` is continuous on `Ioi 0`. -/
lemma continuousOn_fderiv_slice {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (z : Plane) :
    ContinuousOn (fun s : ℝ => fderiv ℝ (tr.v s) z) (Ioi 0) := by
  let V : ℝ × Plane → Vec := fun p => tr.v p.1 p.2
  have hU_open : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hV_sm : ContDiffOn ℝ ∞ V (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hV_fd : ContinuousOn (fderiv ℝ V) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := by
    have h1 := hV_sm.continuousOn_fderivWithin hU_open.uniqueDiffOn (by exact_mod_cast le_top)
    refine h1.congr fun p hp => ?_
    exact (fderivWithin_of_isOpen hU_open hp).symm
  have h_emb : Continuous (fun s : ℝ => (s, z)) := continuous_id.prodMk continuous_const
  have h_comp : ContinuousOn (fun s : ℝ =>
      (fderiv ℝ V (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) (Ioi 0) := by
    have h_fd_s : ContinuousOn (fun s : ℝ => fderiv ℝ V (s, z)) (Ioi 0) :=
      hV_fd.comp h_emb.continuousOn (fun s hs => ⟨hs, trivial⟩)
    exact ((ContinuousLinearMap.compL ℝ Plane (ℝ × Plane) Vec).flip
      (ContinuousLinearMap.inr ℝ ℝ Plane)).continuous.comp_continuousOn h_fd_s
  refine h_comp.congr fun s hs => ?_
  have hV_diff : DifferentiableAt ℝ V (s, z) :=
    (hV_sm.contDiffAt (hU_open.mem_nhds ⟨hs, trivial⟩)).differentiableAt (by simp)
  have hinr : HasFDerivAt (fun w : Plane => (s, w)) (ContinuousLinearMap.inr ℝ ℝ Plane) z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  exact (hV_diff.hasFDerivAt.comp z hinr).fderiv

/-- `s ↦ if 0 < s then B0277.supNormD 1 (tr.v s) else 0` is lower semicontinuous on `ℝ`,
hence measurable. -/
theorem measurable_supNormD_one_ite {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    Measurable (fun s : ℝ => if 0 < s then UnforcedLeray.B0277.supNormD 1 (tr.v s) else 0) := by
  let g : Plane → ℝ → ℝ≥0∞ := fun z s =>
    if 0 < s then ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ₑ else 0
  have hg_lsc : ∀ z : Plane, LowerSemicontinuous (g z) := by
    intro z
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro y
    have hcont : ContinuousOn (fun s : ℝ => ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ₑ) (Ioi 0) := by
      have h1 : ContinuousOn (fun s : ℝ => ‖fderiv ℝ (tr.v s) z‖ₑ) (Ioi 0) :=
        continuous_enorm.comp_continuousOn (continuousOn_fderiv_slice tr z)
      refine h1.congr fun s _ => ?_
      dsimp only
      rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_one]
    have hpre : g z ⁻¹' Ioi y = Ioi (0 : ℝ) ∩ (fun s : ℝ => ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ₑ) ⁻¹' Ioi y := by
      ext s
      simp only [mem_preimage, mem_Ioi, mem_inter_iff, g]
      split_ifs with hs
      · simp [hs]
      · simp [hs]
    rw [hpre]
    exact hcont.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
  have h_sup : (fun s : ℝ => if 0 < s then UnforcedLeray.B0277.supNormD 1 (tr.v s) else 0) =
      fun s : ℝ => ⨆ z : Plane, g z s := by
    ext s
    dsimp [g, UnforcedLeray.B0277.supNormD]
    split_ifs <;> simp
  rw [h_sup]
  exact (lowerSemicontinuous_iSup hg_lsc).measurable

theorem measurable_supNormD_one_toReal_ite {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    Measurable (fun s : ℝ =>
      if 0 < s then (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal else 0) := by
  convert ENNReal.measurable_toReal.comp (measurable_supNormD_one_ite tr) using 1
  ext s
  dsimp
  split_ifs <;> simp

/-- On any compact interval `[s₁, s₂] ⊂ (0, ∞)`, `s ↦ (B0277.supNormD 1 (tr.v s)).toReal` is
integrable. -/
theorem integrableOn_supNormD_one_Icc {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) :
    IntegrableOn (fun s : ℝ => (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal) (Icc s₁ s₂) := by
  have hs₂ : 0 ≤ s₂ := hs₁.le.trans hs₁₂
  obtain ⟨M, _, hM⟩ := supNormD_one_bound_on tr htr hs₂
  have hm : Measurable (fun s : ℝ =>
      if 0 < s then (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal else 0) :=
    measurable_supNormD_one_toReal_ite tr
  have hI : IntegrableOn (fun s : ℝ =>
      if 0 < s then (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal else 0) (Icc s₁ s₂) := by
    refine IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
    split_ifs
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (hM s ⟨hs0.le, hs.2⟩).2.1
  refine hI.congr_fun (fun s hs => ?_) measurableSet_Icc
  have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
  simp [hs0]

/-! ### 3. Pointwise stretching algebra and divergence-free cell IBP -/

/-- Pure algebraic sum-of-squares bound for a trace-free 2×2 matrix acting on `(f₀, f₁)`. -/
lemma stretching_quad_le {dv00 dv01 dv10 dv11 L f0 f1 : ℝ}
    (hdiv : dv00 + dv11 = 0) (hL0 : 0 ≤ L)
    (hq : dv00 ^ 2 + dv10 ^ 2 ≤ L ^ 2) (hη : dv01 ^ 2 + dv11 ^ 2 ≤ L ^ 2) :
    -(dv00 * f0 ^ 2 + (dv01 + dv10) * f0 * f1 + dv11 * f1 ^ 2) ≤ L * (f0 ^ 2 + f1 ^ 2) := by
  have hdv11 : dv11 = -dv00 := by linarith
  have hη' : dv01 ^ 2 + dv00 ^ 2 ≤ L ^ 2 := by
    calc dv01 ^ 2 + dv00 ^ 2 = dv01 ^ 2 + dv11 ^ 2 := by rw [hdv11]; ring
      _ ≤ L ^ 2 := hη
  set A : ℝ := -(dv00 * f0 ^ 2 + (dv01 + dv10) * f0 * f1 + dv11 * f1 ^ 2)
  set B : ℝ := L * (f0 ^ 2 + f1 ^ 2)
  have hB0 : 0 ≤ B := mul_nonneg hL0 (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hA_eq : A = -(dv00 * (f0 ^ 2 - f1 ^ 2) + (dv01 + dv10) * f0 * f1) := by
    dsimp [A]; rw [hdv11]; ring
  have hdiff : B ^ 2 - A ^ 2 =
      (1 / 2) * (L ^ 2 - (dv00 ^ 2 + dv10 ^ 2)) * (f0 ^ 2 + f1 ^ 2) ^ 2 +
      (1 / 2) * (L ^ 2 - (dv01 ^ 2 + dv00 ^ 2)) * (f0 ^ 2 + f1 ^ 2) ^ 2 +
      (1 / 4) * (dv01 - dv10) ^ 2 * (f0 ^ 2 + f1 ^ 2) ^ 2 +
      (2 * dv00 * f0 * f1 - (1 / 2) * (dv01 + dv10) * (f0 ^ 2 - f1 ^ 2)) ^ 2 := by
    dsimp [B]; rw [hA_eq]; ring
  have hsq : A ^ 2 ≤ B ^ 2 := by
    have h1 : 0 ≤ L ^ 2 - (dv00 ^ 2 + dv10 ^ 2) := sub_nonneg.2 hq
    have h2 : 0 ≤ L ^ 2 - (dv01 ^ 2 + dv00 ^ 2) := sub_nonneg.2 hη'
    have h3 : 0 ≤ (f0 ^ 2 + f1 ^ 2) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (dv01 - dv10) ^ 2 := sq_nonneg _
    have h5 : 0 ≤ (2 * dv00 * f0 * f1 - (1 / 2) * (dv01 + dv10) * (f0 ^ 2 - f1 ^ 2)) ^ 2 :=
      sq_nonneg _
    have hnn : 0 ≤ B ^ 2 - A ^ 2 := by
      rw [hdiff]
      positivity
    linarith
  have habs : |A| ≤ |B| := sq_le_sq.1 hsq
  rw [abs_of_nonneg hB0] at habs
  exact (le_abs_self A).trans habs

/-- Product of a bounded continuous function with two `L²(cell)` functions is integrable on the cell. -/
lemma integrableOn_bdd_mul_l2 {c M : ℝ} {g a b : Plane → ℝ}
    (hg : Continuous g) (hM : ∀ x, |g x| ≤ M)
    (ha : MemLp a 2 (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hb : MemLp b 2 (volume.restrict (UnforcedLeray.Cyl.cell c))) :
    IntegrableOn (fun x => g x * (a x * b x)) (UnforcedLeray.Cyl.cell c) := by
  have hab : Integrable (fun x => a x * b x) (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    ha.integrable_mul hb
  have hM' : ∀ᵐ x ∂volume.restrict (UnforcedLeray.Cyl.cell c), ‖g x‖ ≤ M :=
    ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM x
  exact hab.bdd_mul hg.aestronglyMeasurable hM'

/-- Real-part divergence-free advection/stretching inequality on `Cyl.cell c` for a smooth
`c`-periodic divergence-free real vector field `f` in `H¹(cell)`. -/
lemma real_field_advection_ibp {c M₀ L : ℝ} (hc : 0 < c) (hL0 : 0 ≤ L)
    {v : Plane → Vec} (hv_sm : ContDiff ℝ ∞ v) (hv_per : UnforcedLeray.Cyl.IsPeriodic c v)
    (hv_div : ∀ x, UnforcedLeray.Cyl.divergence v x = 0)
    (hv_bdd : ∀ (i : Fin 2) (x : Plane), |v x i| ≤ M₀)
    (hv_grad : ∀ x : Plane, ‖fderiv ℝ v x‖ ≤ L)
    {f : Fin 2 → Plane → ℝ} (hf_diff : ∀ i, Differentiable ℝ (f i))
    (hf_per : ∀ i, UnforcedLeray.Cyl.IsPeriodic c (f i))
    (hf_L2 : ∀ i, MemLp (f i) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hpd0_L2 : ∀ i, MemLp (UnforcedLeray.Cyl.partialQ (f i)) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hpd1_L2 : ∀ i, MemLp (UnforcedLeray.Cyl.partialEta (f i)) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hf_div : ∀ x, UnforcedLeray.Cyl.partialQ (f 0) x + UnforcedLeray.Cyl.partialEta (f 1) x = 0) :
    (∫ x in UnforcedLeray.Cyl.cell c,
      ((2 * v x 0 * f 0 x) * UnforcedLeray.Cyl.partialQ (f 0) x +
       (v x 0 * f 1 x + v x 1 * f 0 x) * UnforcedLeray.Cyl.partialEta (f 0) x +
       (v x 1 * f 0 x + v x 0 * f 1 x) * UnforcedLeray.Cyl.partialQ (f 1) x +
       (2 * v x 1 * f 1 x) * UnforcedLeray.Cyl.partialEta (f 1) x)) ≤
      L * ∫ x in UnforcedLeray.Cyl.cell c, (f 0 x ^ 2 + f 1 x ^ 2) := by
  have hv_diff : Differentiable ℝ v := hv_sm.differentiable (by simp)
  have hvi_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => v x i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hv_sm
  have hvi_diff : ∀ i : Fin 2, Differentiable ℝ (fun x => v x i) := fun i =>
    (hvi_sm i).differentiable (by simp)
  have hvi_cont : ∀ i : Fin 2, Continuous (fun x => v x i) := fun i => (hvi_sm i).continuous
  let dv00 : Plane → ℝ := UnforcedLeray.Cyl.partialQ (fun y => v y 0)
  let dv01 : Plane → ℝ := UnforcedLeray.Cyl.partialEta (fun y => v y 0)
  let dv10 : Plane → ℝ := UnforcedLeray.Cyl.partialQ (fun y => v y 1)
  let dv11 : Plane → ℝ := UnforcedLeray.Cyl.partialEta (fun y => v y 1)
  have hdv_cont : Continuous dv00 ∧ Continuous dv01 ∧ Continuous dv10 ∧ Continuous dv11 := by
    have h0 : ContDiff ℝ (0 + 1) (fun y => v y 0) := (hvi_sm 0).of_le (by simp)
    have h1 : ContDiff ℝ (0 + 1) (fun y => v y 1) := (hvi_sm 1).of_le (by simp)
    exact ⟨(UnforcedLeray.Cyl.contDiff_partialQ h0).continuous,
      (UnforcedLeray.Cyl.contDiff_partialEta h0).continuous,
      (UnforcedLeray.Cyl.contDiff_partialQ h1).continuous,
      (UnforcedLeray.Cyl.contDiff_partialEta h1).continuous⟩
  have hq_sq : ∀ x, dv00 x ^ 2 + dv10 x ^ 2 ≤ L ^ 2 := fun x =>
    (partialQ_sq_sum_le hv_diff x).trans (pow_le_pow_left₀ (norm_nonneg _) (hv_grad x) 2)
  have hη_sq : ∀ x, dv01 x ^ 2 + dv11 x ^ 2 ≤ L ^ 2 := fun x =>
    (partialEta_sq_sum_le hv_diff x).trans (pow_le_pow_left₀ (norm_nonneg _) (hv_grad x) 2)
  have hdv_bdd : ∀ x, |dv00 x| ≤ L ∧ |dv01 x| ≤ L ∧ |dv10 x| ≤ L ∧ |dv11 x| ≤ L := by
    intro x
    have h1 : dv00 x ^ 2 ≤ L ^ 2 := by linarith [hq_sq x, sq_nonneg (dv10 x)]
    have h2 : dv10 x ^ 2 ≤ L ^ 2 := by linarith [hq_sq x, sq_nonneg (dv00 x)]
    have h3 : dv01 x ^ 2 ≤ L ^ 2 := by linarith [hη_sq x, sq_nonneg (dv11 x)]
    have h4 : dv11 x ^ 2 ≤ L ^ 2 := by linarith [hη_sq x, sq_nonneg (dv01 x)]
    rw [← abs_of_nonneg hL0]
    exact ⟨sq_le_sq.1 h1, sq_le_sq.1 h3, sq_le_sq.1 h2, sq_le_sq.1 h4⟩
  let df00 : Plane → ℝ := UnforcedLeray.Cyl.partialQ (f 0)
  let df01 : Plane → ℝ := UnforcedLeray.Cyl.partialEta (f 0)
  let df10 : Plane → ℝ := UnforcedLeray.Cyl.partialQ (f 1)
  let df11 : Plane → ℝ := UnforcedLeray.Cyl.partialEta (f 1)
  let W₀ : Plane → ℝ := fun x =>
    (1 / 2) * v x 0 * (f 0 x * f 0 x + f 1 x * f 1 x) +
      (v x 0 * f 0 x + v x 1 * f 1 x) * f 0 x
  let W₁ : Plane → ℝ := fun x =>
    (1 / 2) * v x 1 * (f 0 x * f 0 x + f 1 x * f 1 x) +
      (v x 0 * f 0 x + v x 1 * f 1 x) * f 1 x
  let W₀' : Plane → ℝ := fun x =>
    ((1 / 2) * dv00 x * (f 0 x * f 0 x + f 1 x * f 1 x) +
      (1 / 2) * v x 0 * ((df00 x * f 0 x + f 0 x * df00 x) + (df10 x * f 1 x + f 1 x * df10 x))) +
    (((dv00 x * f 0 x + v x 0 * df00 x) + (dv10 x * f 1 x + v x 1 * df10 x)) * f 0 x +
      (v x 0 * f 0 x + v x 1 * f 1 x) * df00 x)
  let W₁' : Plane → ℝ := fun x =>
    ((1 / 2) * dv11 x * (f 0 x * f 0 x + f 1 x * f 1 x) +
      (1 / 2) * v x 1 * ((df01 x * f 0 x + f 0 x * df01 x) + (df11 x * f 1 x + f 1 x * df11 x))) +
    (((dv01 x * f 0 x + v x 0 * df01 x) + (dv11 x * f 1 x + v x 1 * df11 x)) * f 1 x +
      (v x 0 * f 0 x + v x 1 * f 1 x) * df11 x)
  have hdW₀ : ∀ q η, HasDerivAt (fun q' => W₀ (q', η)) (W₀' (q, η)) q := by
    intro q η
    have hv0 := UnforcedLeray.Cyl.hasDerivAt_sliceQ (hvi_diff 0) q η
    have hv1 := UnforcedLeray.Cyl.hasDerivAt_sliceQ (hvi_diff 1) q η
    have hf0 := UnforcedLeray.Cyl.hasDerivAt_sliceQ (hf_diff 0) q η
    have hf1 := UnforcedLeray.Cyl.hasDerivAt_sliceQ (hf_diff 1) q η
    exact (((hv0.const_mul (1 / 2)).mul ((hf0.mul hf0).add (hf1.mul hf1))).add
      (((hv0.mul hf0).add (hv1.mul hf1)).mul hf0))
  have hdW₁ : ∀ q η, HasDerivAt (fun η' => W₁ (q, η')) (W₁' (q, η)) η := by
    intro q η
    have hv0 := UnforcedLeray.Cyl.hasDerivAt_sliceEta (hvi_diff 0) q η
    have hv1 := UnforcedLeray.Cyl.hasDerivAt_sliceEta (hvi_diff 1) q η
    have hf0 := UnforcedLeray.Cyl.hasDerivAt_sliceEta (hf_diff 0) q η
    have hf1 := UnforcedLeray.Cyl.hasDerivAt_sliceEta (hf_diff 1) q η
    exact (((hv1.const_mul (1 / 2)).mul ((hf0.mul hf0).add (hf1.mul hf1))).add
      (((hv0.mul hf0).add (hv1.mul hf1)).mul hf1))
  have hW₀_per : UnforcedLeray.Cyl.IsPeriodic c W₀ := by
    intro z
    dsimp [W₀]
    have hvz : v (z.1 + c, z.2) = v z := hv_per z
    rw [hvz, hf_per 0 z, hf_per 1 z]
  have hint_v : ∀ (i a b : Fin 2),
      IntegrableOn (fun x => v x i * (f a x * f b x)) (UnforcedLeray.Cyl.cell c) :=
    fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (hf_L2 a) (hf_L2 b)
  have hint_v_q : ∀ (i a b : Fin 2),
      IntegrableOn (fun x => v x i * (f a x * UnforcedLeray.Cyl.partialQ (f b) x))
        (UnforcedLeray.Cyl.cell c) :=
    fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (hf_L2 a) (hpd0_L2 b)
  have hint_v_η : ∀ (i a b : Fin 2),
      IntegrableOn (fun x => v x i * (f a x * UnforcedLeray.Cyl.partialEta (f b) x))
        (UnforcedLeray.Cyl.cell c) :=
    fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (hf_L2 a) (hpd1_L2 b)
  have hint_dv00 : ∀ (a b : Fin 2),
      IntegrableOn (fun x => dv00 x * (f a x * f b x)) (UnforcedLeray.Cyl.cell c) :=
    fun a b => integrableOn_bdd_mul_l2 hdv_cont.1 (fun x => (hdv_bdd x).1) (hf_L2 a) (hf_L2 b)
  have hint_dv01 : ∀ (a b : Fin 2),
      IntegrableOn (fun x => dv01 x * (f a x * f b x)) (UnforcedLeray.Cyl.cell c) :=
    fun a b => integrableOn_bdd_mul_l2 hdv_cont.2.1 (fun x => (hdv_bdd x).2.1) (hf_L2 a) (hf_L2 b)
  have hint_dv10 : ∀ (a b : Fin 2),
      IntegrableOn (fun x => dv10 x * (f a x * f b x)) (UnforcedLeray.Cyl.cell c) :=
    fun a b => integrableOn_bdd_mul_l2 hdv_cont.2.2.1 (fun x => (hdv_bdd x).2.2.1) (hf_L2 a) (hf_L2 b)
  have hint_dv11 : ∀ (a b : Fin 2),
      IntegrableOn (fun x => dv11 x * (f a x * f b x)) (UnforcedLeray.Cyl.cell c) :=
    fun a b => integrableOn_bdd_mul_l2 hdv_cont.2.2.2 (fun x => (hdv_bdd x).2.2.2) (hf_L2 a) (hf_L2 b)
  have hcell_meas : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hW₁_int : IntegrableOn W₁ (UnforcedLeray.Cyl.cell c) := by
    have h1 := ((hint_v 1 0 0).add (hint_v 1 1 1)).const_mul (1 / 2)
    have h2 := (hint_v 0 0 1).add (hint_v 1 1 1)
    refine IntegrableOn.congr_fun (h1.add h2) (fun x _ => ?_) hcell_meas
    dsimp [W₁]; ring
  have hW₀'_int : IntegrableOn W₀' (UnforcedLeray.Cyl.cell c) := by
    have h1 := ((hint_dv00 0 0).add (hint_dv00 1 1)).const_mul (1 / 2)
    have h2 := (hint_v_q 0 0 0).const_mul 3
    have h3 := (hint_v_q 0 1 1).add ((hint_v_q 1 0 1).add (hint_v_q 1 1 0))
    have h4 := (hint_dv00 0 0).add (hint_dv10 1 0)
    refine IntegrableOn.congr_fun ((h1.add h2).add (h3.add h4)) (fun x _ => ?_) hcell_meas
    dsimp [W₀', df00, df10]; ring
  have hW₁'_int : IntegrableOn W₁' (UnforcedLeray.Cyl.cell c) := by
    have h1 := ((hint_dv11 0 0).add (hint_dv11 1 1)).const_mul (1 / 2)
    have h2 := (hint_v_η 1 1 1).const_mul 3
    have h3 := (hint_v_η 1 0 0).add ((hint_v_η 0 0 1).add (hint_v_η 0 1 0))
    have h4 := (hint_dv01 0 1).add (hint_dv11 1 1)
    refine IntegrableOn.congr_fun ((h1.add h2).add (h3.add h4)) (fun x _ => ?_) hcell_meas
    dsimp [W₁', df01, df11]; ring
  have hI₀ : ∫ x in UnforcedLeray.Cyl.cell c, W₀' x = 0 :=
    UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc hW₀_per hdW₀ hW₀'_int
  have hI₁ : ∫ x in UnforcedLeray.Cyl.cell c, W₁' x = 0 :=
    UnforcedLeray.Cyl.integral_cell_deriv_eta hdW₁ hW₁_int hW₁'_int
  let P_adv : Plane → ℝ := fun x =>
    (2 * v x 0 * f 0 x) * df00 x +
    (v x 0 * f 1 x + v x 1 * f 0 x) * df01 x +
    (v x 1 * f 0 x + v x 0 * f 1 x) * df10 x +
    (2 * v x 1 * f 1 x) * df11 x
  let S_str : Plane → ℝ := fun x =>
    dv00 x * f 0 x ^ 2 + (dv01 x + dv10 x) * f 0 x * f 1 x + dv11 x * f 1 x ^ 2
  have hP_int : IntegrableOn P_adv (UnforcedLeray.Cyl.cell c) := by
    have h1 := ((hint_v_q 0 0 0).const_mul 2).add ((hint_v_η 0 1 0).add (hint_v_η 1 0 0))
    have h2 := ((hint_v_q 1 0 1).add (hint_v_q 0 1 1)).add ((hint_v_η 1 1 1).const_mul 2)
    refine IntegrableOn.congr_fun (h1.add h2) (fun x _ => ?_) hcell_meas
    dsimp [P_adv, df00, df01, df10, df11]; ring
  have hS_int : IntegrableOn S_str (UnforcedLeray.Cyl.cell c) := by
    have h1 := (hint_dv00 0 0).add ((hint_dv01 0 1).add (hint_dv10 0 1))
    refine (h1.add (hint_dv11 1 1)).congr_fun (fun x _ => ?_) hcell_meas
    dsimp [S_str]; ring
  have hpt_sum : ∀ x : Plane, W₀' x + W₁' x = P_adv x + S_str x := by
    intro x
    have hdvx : dv00 x + dv11 x = 0 := hv_div x
    have hdfx : df00 x + df11 x = 0 := hf_div x
    dsimp [W₀', W₁', P_adv, S_str]
    linear_combination
      ((1 / 2) * (f 0 x * f 0 x + f 1 x * f 1 x)) * hdvx +
      (v x 0 * f 0 x + v x 1 * f 1 x) * hdfx
  have hsum_zero : (∫ x in UnforcedLeray.Cyl.cell c, P_adv x) +
      (∫ x in UnforcedLeray.Cyl.cell c, S_str x) = 0 := by
    rw [← integral_add hP_int hS_int]
    have heq : (fun x => P_adv x + S_str x) = (fun x => W₀' x + W₁' x) :=
      funext fun x => (hpt_sum x).symm
    rw [heq, integral_add hW₀'_int hW₁'_int, hI₀, hI₁, add_zero]
  have hP_eq_neg_S : (∫ x in UnforcedLeray.Cyl.cell c, P_adv x) =
      ∫ x in UnforcedLeray.Cyl.cell c, -S_str x := by
    rw [integral_neg]
    linarith [hsum_zero]
  have hf_sq_int : IntegrableOn (fun x => f 0 x ^ 2 + f 1 x ^ 2) (UnforcedLeray.Cyl.cell c) := by
    have h0 : IntegrableOn (fun x => f 0 x ^ 2) (UnforcedLeray.Cyl.cell c) :=
      IntegrableOn.congr_fun ((hf_L2 0).integrable_mul (hf_L2 0))
        (fun x _ => (sq (f 0 x)).symm) hcell_meas
    have h1 : IntegrableOn (fun x => f 1 x ^ 2) (UnforcedLeray.Cyl.cell c) :=
      IntegrableOn.congr_fun ((hf_L2 1).integrable_mul (hf_L2 1))
        (fun x _ => (sq (f 1 x)).symm) hcell_meas
    exact h0.add h1
  rw [hP_eq_neg_S, ← integral_const_mul]
  refine integral_mono hS_int.neg (hf_sq_int.const_mul L) (fun x => ?_)
  exact stretching_quad_le (hv_div x) hL0 (hq_sq x) (hη_sq x)

/-! ### 4. Mollified complex slice bound and passage to `k → ∞` on a good slice -/

lemma memLp_re {μ : Measure Plane} {g : Plane → ℂ} (hg : MemLp g 2 μ) :
    MemLp (fun x => (g x).re) 2 μ := by
  refine MemLp.of_le_mul (c := 1) hg (Complex.continuous_re.comp_aestronglyMeasurable hg.1)
    (ae_of_all _ fun x => ?_)
  rw [one_mul, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm (g x)

lemma memLp_im {μ : Measure Plane} {g : Plane → ℂ} (hg : MemLp g 2 μ) :
    MemLp (fun x => (g x).im) 2 μ := by
  refine MemLp.of_le_mul (c := 1) hg (Complex.continuous_im.comp_aestronglyMeasurable hg.1)
    (ae_of_all _ fun x => ?_)
  rw [one_mul, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm (g x)

/-- On a good slice `s > 0`, the mollified field `u_k = LMMollU J b k s` satisfies
`∫_cell lmP_pair H_k G_k ≤ L * LMMollE c J b k s`, where
`H_k x i j = v x i * u_k x j + u_k x i * v x j` and `G_k x i j = LMPd j (u_k · i) x`. -/
lemma moll_slice_advection_le {c ν : ℝ} (hc : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {s : ℝ} (hs : 0 < s)
    (hb : LMCellL2 c (fun y => b (s, y)))
    (hdiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in UnforcedLeray.B0579.cell c,
        (b (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
          b (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0)
    (k : ℕ) :
    (∫ x in UnforcedLeray.B0579.cell c,
      lmP_pair
        (fun x i j => (tr.v s x i : ℂ) * LMMollU J b k s x j +
          LMMollU J b k s x i * (tr.v s x j : ℂ))
        (fun x i j => LMPd j (fun y => LMMollU J b k s y i) x) x) ≤
      (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal * LMMollE c J b k s := by
  let v : Plane → Vec := tr.v s
  let L : ℝ := (UnforcedLeray.B0277.supNormD 1 v).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hv_sm : ContDiff ℝ ∞ v := contDiff_train_slice tr hs.le
  have hv_per : UnforcedLeray.Cyl.IsPeriodic c v := tr.isTrain.periodic_v s hs.le
  have hv_div : ∀ x, UnforcedLeray.Cyl.divergence v x = 0 := tr.isTrain.solenoidal s hs.le
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound hs.le
  have hv_bdd : ∀ (i : Fin 2) (x : Plane), |v x i| ≤ M₀ := fun i x => by
    have h1 : |v x i| ≤ ‖v x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (v x) i
    exact h1.trans (hM₀ s ⟨hs.le, le_rfl⟩ x)
  obtain ⟨_, _, hM₁⟩ := supNormD_one_bound_on tr htr hs.le
  have hv_grad : ∀ x : Plane, ‖fderiv ℝ v x‖ ≤ L := (hM₁ s ⟨hs.le, le_rfl⟩).2.2
  let u : LMSpField := LMMollU J b k s
  have hu_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => u x i) := hJ.smooth k _ hb
  have hu_diff : ∀ i : Fin 2, Differentiable ℝ (fun x => u x i) :=
    fun i => (hu_sm i).differentiable (by simp)
  have hu_per : ∀ (x : Plane) (i : Fin 2), u (x.1 + c, x.2) i = u x i := hJ.periodic k _ hb
  have hu_L2 : LMCellL2 c u := hJ.memL2 k _ hb
  obtain ⟨_, hgrad_spec⟩ := hJ.gradL2 k
  have hu_gradL2 : ∀ i j : Fin 2,
      MemLp (LMPd j (fun y => u y i)) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    fun i j => (hgrad_spec _ hb i j).1
  have hu_div : ∀ x : Plane, LMPd 0 (fun y => u y 0) x + LMPd 1 (fun y => u y 1) x = 0 :=
    hJ.divFreeWeak k _ hb hdiv
  let f_re : Fin 2 → Plane → ℝ := fun i x => (u x i).re
  let f_im : Fin 2 → Plane → ℝ := fun i x => (u x i).im
  have hre_diff : ∀ i, Differentiable ℝ (f_re i) := fun i => lmSW_re_diff (hu_diff i)
  have him_diff : ∀ i, Differentiable ℝ (f_im i) := fun i => lmSW_im_diff (hu_diff i)
  have hre_per : ∀ i, UnforcedLeray.Cyl.IsPeriodic c (f_re i) :=
    fun i x => congrArg Complex.re (hu_per x i)
  have him_per : ∀ i, UnforcedLeray.Cyl.IsPeriodic c (f_im i) :=
    fun i x => congrArg Complex.im (hu_per x i)
  have hre_L2 : ∀ i, MemLp (f_re i) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro i
    rw [← cell_eq_cylCell]
    exact memLp_re (hu_L2 i)
  have him_L2 : ∀ i, MemLp (f_im i) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro i
    rw [← cell_eq_cylCell]
    exact memLp_im (hu_L2 i)
  have hre_pd0_eq : ∀ i x, UnforcedLeray.Cyl.partialQ (f_re i) x = (LMPd 0 (fun y => u y i) x).re := by
    intro i x
    rw [lmSW_partialQ_re (hu_diff i) x, lmSW_LMPd0 (hu_diff i) x]
  have him_pd0_eq : ∀ i x, UnforcedLeray.Cyl.partialQ (f_im i) x = (LMPd 0 (fun y => u y i) x).im := by
    intro i x
    rw [lmSW_partialQ_im (hu_diff i) x, lmSW_LMPd0 (hu_diff i) x]
  have hre_pd1_eq : ∀ i x, UnforcedLeray.Cyl.partialEta (f_re i) x = (LMPd 1 (fun y => u y i) x).re := by
    intro i x
    rw [lmSW_partialEta_re (hu_diff i) x, lmSW_LMPd1 (hu_diff i) x]
  have him_pd1_eq : ∀ i x, UnforcedLeray.Cyl.partialEta (f_im i) x = (LMPd 1 (fun y => u y i) x).im := by
    intro i x
    rw [lmSW_partialEta_im (hu_diff i) x, lmSW_LMPd1 (hu_diff i) x]
  have hre_pd0_L2 : ∀ i, MemLp (UnforcedLeray.Cyl.partialQ (f_re i)) 2
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro i
    rw [← cell_eq_cylCell, show UnforcedLeray.Cyl.partialQ (f_re i) =
      fun x => (LMPd 0 (fun y => u y i) x).re from funext (hre_pd0_eq i)]
    exact memLp_re (hu_gradL2 i 0)
  have him_pd0_L2 : ∀ i, MemLp (UnforcedLeray.Cyl.partialQ (f_im i)) 2
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro i
    rw [← cell_eq_cylCell, show UnforcedLeray.Cyl.partialQ (f_im i) =
      fun x => (LMPd 0 (fun y => u y i) x).im from funext (him_pd0_eq i)]
    exact memLp_im (hu_gradL2 i 0)
  have hre_pd1_L2 : ∀ i, MemLp (UnforcedLeray.Cyl.partialEta (f_re i)) 2
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro i
    rw [← cell_eq_cylCell, show UnforcedLeray.Cyl.partialEta (f_re i) =
      fun x => (LMPd 1 (fun y => u y i) x).re from funext (hre_pd1_eq i)]
    exact memLp_re (hu_gradL2 i 1)
  have him_pd1_L2 : ∀ i, MemLp (UnforcedLeray.Cyl.partialEta (f_im i)) 2
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro i
    rw [← cell_eq_cylCell, show UnforcedLeray.Cyl.partialEta (f_im i) =
      fun x => (LMPd 1 (fun y => u y i) x).im from funext (him_pd1_eq i)]
    exact memLp_im (hu_gradL2 i 1)
  have hre_div : ∀ x, UnforcedLeray.Cyl.partialQ (f_re 0) x +
      UnforcedLeray.Cyl.partialEta (f_re 1) x = 0 := by
    intro x
    rw [hre_pd0_eq 0 x, hre_pd1_eq 1 x, ← Complex.add_re, hu_div x, Complex.zero_re]
  have him_div : ∀ x, UnforcedLeray.Cyl.partialQ (f_im 0) x +
      UnforcedLeray.Cyl.partialEta (f_im 1) x = 0 := by
    intro x
    rw [him_pd0_eq 0 x, him_pd1_eq 1 x, ← Complex.add_im, hu_div x, Complex.zero_im]
  have h_re_ibp := real_field_advection_ibp hc hL0 hv_sm hv_per hv_div hv_bdd hv_grad
    hre_diff hre_per hre_L2 hre_pd0_L2 hre_pd1_L2 hre_div
  have h_im_ibp := real_field_advection_ibp hc hL0 hv_sm hv_per hv_div hv_bdd hv_grad
    him_diff him_per him_L2 him_pd0_L2 him_pd1_L2 him_div
  let P_re : Plane → ℝ := fun x =>
    (2 * v x 0 * f_re 0 x) * UnforcedLeray.Cyl.partialQ (f_re 0) x +
    (v x 0 * f_re 1 x + v x 1 * f_re 0 x) * UnforcedLeray.Cyl.partialEta (f_re 0) x +
    (v x 1 * f_re 0 x + v x 0 * f_re 1 x) * UnforcedLeray.Cyl.partialQ (f_re 1) x +
    (2 * v x 1 * f_re 1 x) * UnforcedLeray.Cyl.partialEta (f_re 1) x
  let P_im : Plane → ℝ := fun x =>
    (2 * v x 0 * f_im 0 x) * UnforcedLeray.Cyl.partialQ (f_im 0) x +
    (v x 0 * f_im 1 x + v x 1 * f_im 0 x) * UnforcedLeray.Cyl.partialEta (f_im 0) x +
    (v x 1 * f_im 0 x + v x 0 * f_im 1 x) * UnforcedLeray.Cyl.partialQ (f_im 1) x +
    (2 * v x 1 * f_im 1 x) * UnforcedLeray.Cyl.partialEta (f_im 1) x
  have hvi_cont : ∀ i : Fin 2, Continuous (fun x => v x i) := fun i =>
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hv_sm).continuous
  have hcell_meas : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hPre_int : IntegrableOn P_re (UnforcedLeray.Cyl.cell c) := by
    have hq : ∀ (i a b : Fin 2), IntegrableOn
        (fun x => v x i * (f_re a x * UnforcedLeray.Cyl.partialQ (f_re b) x))
        (UnforcedLeray.Cyl.cell c) :=
      fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (hre_L2 a) (hre_pd0_L2 b)
    have hη : ∀ (i a b : Fin 2), IntegrableOn
        (fun x => v x i * (f_re a x * UnforcedLeray.Cyl.partialEta (f_re b) x))
        (UnforcedLeray.Cyl.cell c) :=
      fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (hre_L2 a) (hre_pd1_L2 b)
    refine IntegrableOn.congr_fun ((((hq 0 0 0).const_mul 2).add ((hη 0 1 0).add (hη 1 0 0))).add
      (((hq 1 0 1).add (hq 0 1 1)).add ((hη 1 1 1).const_mul 2)))
      (fun x _ => by dsimp [P_re]; ring) hcell_meas
  have hPim_int : IntegrableOn P_im (UnforcedLeray.Cyl.cell c) := by
    have hq : ∀ (i a b : Fin 2), IntegrableOn
        (fun x => v x i * (f_im a x * UnforcedLeray.Cyl.partialQ (f_im b) x))
        (UnforcedLeray.Cyl.cell c) :=
      fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (him_L2 a) (him_pd0_L2 b)
    have hη : ∀ (i a b : Fin 2), IntegrableOn
        (fun x => v x i * (f_im a x * UnforcedLeray.Cyl.partialEta (f_im b) x))
        (UnforcedLeray.Cyl.cell c) :=
      fun i a b => integrableOn_bdd_mul_l2 (hvi_cont i) (hv_bdd i) (him_L2 a) (him_pd1_L2 b)
    refine IntegrableOn.congr_fun ((((hq 0 0 0).const_mul 2).add ((hη 0 1 0).add (hη 1 0 0))).add
      (((hq 1 0 1).add (hq 0 1 1)).add ((hη 1 1 1).const_mul 2)))
      (fun x _ => by dsimp [P_im]; ring) hcell_meas
  have hEre_int : IntegrableOn (fun x => f_re 0 x ^ 2 + f_re 1 x ^ 2) (UnforcedLeray.Cyl.cell c) := by
    have h0 : IntegrableOn (fun x => f_re 0 x ^ 2) (UnforcedLeray.Cyl.cell c) :=
      IntegrableOn.congr_fun ((hre_L2 0).integrable_mul (hre_L2 0))
        (fun x _ => (sq (f_re 0 x)).symm) hcell_meas
    have h1 : IntegrableOn (fun x => f_re 1 x ^ 2) (UnforcedLeray.Cyl.cell c) :=
      IntegrableOn.congr_fun ((hre_L2 1).integrable_mul (hre_L2 1))
        (fun x _ => (sq (f_re 1 x)).symm) hcell_meas
    exact h0.add h1
  have hEim_int : IntegrableOn (fun x => f_im 0 x ^ 2 + f_im 1 x ^ 2) (UnforcedLeray.Cyl.cell c) := by
    have h0 : IntegrableOn (fun x => f_im 0 x ^ 2) (UnforcedLeray.Cyl.cell c) :=
      IntegrableOn.congr_fun ((him_L2 0).integrable_mul (him_L2 0))
        (fun x _ => (sq (f_im 0 x)).symm) hcell_meas
    have h1 : IntegrableOn (fun x => f_im 1 x ^ 2) (UnforcedLeray.Cyl.cell c) :=
      IntegrableOn.congr_fun ((him_L2 1).integrable_mul (him_L2 1))
        (fun x _ => (sq (f_im 1 x)).symm) hcell_meas
    exact h0.add h1
  have hpair_eq : ∀ x : Plane,
      lmP_pair
        (fun x i j => (v x i : ℂ) * u x j + u x i * (v x j : ℂ))
        (fun x i j => LMPd j (fun y => u y i) x) x = P_re x + P_im x := by
    intro x
    unfold lmP_pair
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    dsimp [P_re, P_im, f_re, f_im]
    rw [hre_pd0_eq 0 x, hre_pd0_eq 1 x, hre_pd1_eq 0 x, hre_pd1_eq 1 x,
      him_pd0_eq 0 x, him_pd0_eq 1 x, him_pd1_eq 0 x, him_pd1_eq 1 x]
    simp only [Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    ring
  have hE_eq : ∀ x : Plane, vnorm2 (u x) ^ 2 =
      (f_re 0 x ^ 2 + f_re 1 x ^ 2) + (f_im 0 x ^ 2 + f_im 1 x ^ 2) := by
    intro x
    rw [domEN_vnorm2_sq, Fin.sum_univ_two, lmP_norm_sq_eq (u x 0), lmP_norm_sq_eq (u x 1)]
    dsimp [f_re, f_im]
    ring
  unfold LMMollE
  rw [cell_eq_cylCell, show (∫ x in UnforcedLeray.Cyl.cell c,
      lmP_pair (fun x i j => (v x i : ℂ) * u x j + u x i * (v x j : ℂ))
        (fun x i j => LMPd j (fun y => u y i) x) x) =
      ∫ x in UnforcedLeray.Cyl.cell c, (P_re x + P_im x) from
        integral_congr_ae (ae_of_all _ hpair_eq),
    integral_add hPre_int hPim_int,
    show (∫ x in UnforcedLeray.Cyl.cell c, vnorm2 (u x) ^ 2) =
      ∫ x in UnforcedLeray.Cyl.cell c,
        ((f_re 0 x ^ 2 + f_re 1 x ^ 2) + (f_im 0 x ^ 2 + f_im 1 x ^ 2)) from
        integral_congr_ae (ae_of_all _ hE_eq),
    integral_add hEre_int hEim_int, mul_add]
  exact add_le_add h_re_ibp h_im_ibp

/-- On a good slice `s > 0`, passing to the mollifier limit `k → ∞` gives
`energyR c (flatMult tr b) G s ≤ (B0277.supNormD 1 (tr.v s)).toReal * energyE c b s`. -/
theorem goodSlice_advection_energyR_le {c ν : ℝ} {μ : ℂ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {F b G} (hD : FreeSolData c ν μ F b G)
    {s : ℝ} (hs : 0 < s) (hgs : LMGoodSlice c F G b s) :
    energyR c (flatMult tr b) G s ≤
      (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal * energyE c b s := by
  have hc : 0 < c := hD.pos_c
  obtain ⟨J, hJ⟩ := hasLMMollifier c hc
  have ⟨hb, hcol, _⟩ := hgs
  let v : Plane → Vec := tr.v s
  let L : ℝ := (UnforcedLeray.B0277.supNormD 1 v).toReal
  obtain ⟨M₀, hM₀_pos, hM₀_all⟩ := trainVel_bound_le tr htr hs.le
  have hv_bdd : ∀ (i : Fin 2) (x : Plane), |v x i| ≤ M₀ := fun i x => by
    have h := hM₀_all s le_rfl x i
    simpa [trainVel, hs.le, v, Complex.norm_real] using h
  have hv_cont : ∀ i : Fin 2, Continuous (fun x => v x i) :=
    fun i => (contDiff_train_comp tr hs.le i).continuous
  let H : Plane → Fin 2 → Fin 2 → ℂ := fun x i j => flatMult tr b (s, x) i j
  let H_k : ℕ → Plane → Fin 2 → Fin 2 → ℂ := fun k x i j =>
    (v x i : ℂ) * LMMollU J b k s x j + LMMollU J b k s x i * (v x j : ℂ)
  let G_k : ℕ → Plane → Fin 2 → Fin 2 → ℂ := fun k x i j =>
    J k (fun y i' => G (s, y) i' j) x i
  have hH_eq : ∀ x i j, H x i j = (v x i : ℂ) * b (s, x) j + b (s, x) i * (v x j : ℂ) := by
    intro x i j
    simp [H, flatMult, trainVel, hs.le, v]
  have hmul_memL2 : ∀ {u : LMSpField}, LMCellL2 c u → ∀ j : Fin 2,
      LMCellL2 c (fun x i => (v x i : ℂ) * u x j + u x i * (v x j : ℂ)) := by
    intro u hu j i
    have h1 : MemLp (fun x => (v x i : ℂ) * u x j) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
      refine MemLp.of_le_mul (c := M₀) (hu j)
        (((Complex.continuous_ofReal.comp (hv_cont i)).aestronglyMeasurable).mul (hu j).1)
        (ae_of_all _ fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hv_bdd i x) (norm_nonneg _)
    have h2 : MemLp (fun x => u x i * (v x j : ℂ)) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
      refine MemLp.of_le_mul (c := M₀) (hu i)
        ((hu i).1.mul ((Complex.continuous_ofReal.comp (hv_cont j)).aestronglyMeasurable))
        (ae_of_all _ fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hv_bdd j x) (norm_nonneg _)
    exact h1.add h2
  have hH_L2 : ∀ j : Fin 2, LMCellL2 c (fun x i => H x i j) := by
    intro j i
    have h := hmul_memL2 hb j i
    have heq : (fun x => H x i j) =
        fun x => (v x i : ℂ) * b (s, x) j + b (s, x) i * (v x j : ℂ) :=
      funext fun x => hH_eq x i j
    rwa [heq]
  have hHk_L2 : ∀ (k : ℕ) (j : Fin 2), LMCellL2 c (fun x i => H_k k x i j) :=
    fun k j => hmul_memL2 (hJ.memL2 k _ hb) j
  have hGk_L2 : ∀ (k : ℕ) (j : Fin 2), LMCellL2 c (fun x i => G_k k x i j) :=
    fun k j => hJ.memL2 k _ (hcol j)
  have hpd : ∀ (k : ℕ) (x : Plane) (i j : Fin 2),
       LMPd j (fun y => LMMollU J b k s y i) x = G_k k x i j :=
    fun k x i j => lmMoll_pd_eq hJ hb hcol (fun i' j' => hD.sol.weakGrad s hs i' j') k i j x
  have hbd_k : ∀ k : ℕ,
      (∫ x in UnforcedLeray.B0579.cell c, lmP_pair (H_k k) (G_k k) x) ≤ L * energyE c b s := by
    intro k
    have h1 := moll_slice_advection_le hc tr htr hJ hs hb (hD.sol.divFree s hs) k
    have heq : (fun x => lmP_pair (H_k k)
        (fun x i j => LMPd j (fun y => LMMollU J b k s y i) x) x) =
        fun x => lmP_pair (H_k k) (G_k k) x := by
      funext x; unfold lmP_pair; simp only [hpd]
    rw [heq] at h1
    have hdom := (lmMollDomEN c ν μ F b G hD J hJ s hs hgs k).2.1
    exact h1.trans (mul_le_mul_of_nonneg_left hdom ENNReal.toReal_nonneg)
  have h_tendsto_HGk : Tendsto (fun k : ℕ => ∫ x in UnforcedLeray.B0579.cell c, lmP_pair H (G_k k) x)
      atTop (𝓝 (energyR c (flatMult tr b) G s)) :=
    lm_tendsto_tpair hGk_L2 hcol hH_L2 (fun j => hJ.tendsto _ (hcol j))
  have h_tendsto_diff : Tendsto (fun k : ℕ =>
      (∫ x in UnforcedLeray.B0579.cell c, lmP_pair (H_k k) (G_k k) x) -
        ∫ x in UnforcedLeray.B0579.cell c, lmP_pair H (G_k k) x) atTop (𝓝 0) := by
    have hH_diff_pt : ∀ (k : ℕ) (x : Plane) (i j : Fin 2),
        ‖H_k k x i j - H x i j‖ ^ 2 ≤
          8 * M₀ ^ 2 * ∑ m : Fin 2, ‖LMMollU J b k s x m - b (s, x) m‖ ^ 2 := by
      intro k x i j
      have hsub : H_k k x i j - H x i j =
          (v x i : ℂ) * (LMMollU J b k s x j - b (s, x) j) +
            (LMMollU J b k s x i - b (s, x) i) * (v x j : ℂ) := by
        dsimp [H_k]; rw [hH_eq x i j]; ring
      have h_le_sum : ∀ m : Fin 2, ‖LMMollU J b k s x m - b (s, x) m‖ ≤
          ‖LMMollU J b k s x 0 - b (s, x) 0‖ + ‖LMMollU J b k s x 1 - b (s, x) 1‖ := by
        intro m
        fin_cases m
        · change ‖LMMollU J b k s x 0 - b (s, x) 0‖ ≤
            ‖LMMollU J b k s x 0 - b (s, x) 0‖ + ‖LMMollU J b k s x 1 - b (s, x) 1‖
          linarith [norm_nonneg (LMMollU J b k s x 1 - b (s, x) 1)]
        · change ‖LMMollU J b k s x 1 - b (s, x) 1‖ ≤
            ‖LMMollU J b k s x 0 - b (s, x) 0‖ + ‖LMMollU J b k s x 1 - b (s, x) 1‖
          linarith [norm_nonneg (LMMollU J b k s x 0 - b (s, x) 0)]
      have h1 : ‖H_k k x i j - H x i j‖ ≤
          2 * M₀ * (‖LMMollU J b k s x 0 - b (s, x) 0‖ + ‖LMMollU J b k s x 1 - b (s, x) 1‖) := by
        rw [hsub]
        have ha : ‖(v x i : ℂ) * (LMMollU J b k s x j - b (s, x) j)‖ ≤
            M₀ * (‖LMMollU J b k s x 0 - b (s, x) 0‖ + ‖LMMollU J b k s x 1 - b (s, x) 1‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact (mul_le_mul_of_nonneg_right (hv_bdd i x) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (h_le_sum j) hM₀_pos.le)
        have hb' : ‖(LMMollU J b k s x i - b (s, x) i) * (v x j : ℂ)‖ ≤
            M₀ * (‖LMMollU J b k s x 0 - b (s, x) 0‖ + ‖LMMollU J b k s x 1 - b (s, x) 1‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact (mul_le_mul_of_nonneg_right (hv_bdd j x) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (h_le_sum i) hM₀_pos.le)
        linarith [norm_add_le ((v x i : ℂ) * (LMMollU J b k s x j - b (s, x) j))
          ((LMMollU J b k s x i - b (s, x) i) * (v x j : ℂ))]
      rw [Fin.sum_univ_two]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖LMMollU J b k s x 0 - b (s, x) 0‖ - ‖LMMollU J b k s x 1 - b (s, x) 1‖)]
    have hD_int : ∀ k : ℕ, Integrable
        (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2)
        (volume.restrict (UnforcedLeray.B0579.cell c)) := fun k =>
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
        lmP_sq_integrable ((hHk_L2 k j i).sub (hH_L2 j i))
    have hU_int : ∀ k : ℕ, Integrable
        (fun x => ∑ m : Fin 2, ‖LMMollU J b k s x m - b (s, x) m‖ ^ 2)
        (volume.restrict (UnforcedLeray.B0579.cell c)) := fun k =>
      integrable_finsetSum _ fun m _ =>
        lmP_sq_integrable ((hJ.memL2 k _ hb m).sub (hb m))
    have hD_lim : Tendsto (fun k : ℕ => ∫ x in UnforcedLeray.B0579.cell c,
        ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2) atTop (𝓝 0) := by
      have hU_lim : Tendsto (fun k : ℕ => 32 * M₀ ^ 2 * ∫ x in UnforcedLeray.B0579.cell c,
          ∑ m : Fin 2, ‖LMMollU J b k s x m - b (s, x) m‖ ^ 2) atTop (𝓝 0) := by
        simpa only [mul_zero, LMMollU] using (hJ.tendsto _ hb).const_mul (32 * M₀ ^ 2)
      refine squeeze_zero (fun k => integral_nonneg fun x =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun k => ?_) hU_lim
      rw [← integral_const_mul (32 * M₀ ^ 2)]
      refine integral_mono (hD_int k) ((hU_int k).const_mul _) (fun x => ?_)
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      linarith [hH_diff_pt k x 0 0, hH_diff_pt k x 0 1, hH_diff_pt k x 1 0, hH_diff_pt k x 1 1]
    set M_N : ℝ := energyN c G s
    have hMN0 : 0 ≤ M_N := integral_nonneg fun x => sq_nonneg _
    rw [Metric.tendsto_nhds]
    intro ε hε
    let l : ℝ := ε / (2 * (M_N + 1))
    have hlpos : 0 < l := div_pos hε (by linarith)
    have hlM : l * M_N ≤ ε / 2 := by
      have e : ε = 2 * (l * M_N) + 2 * l := by dsimp [l]; field_simp
      linarith
    filter_upwards [hD_lim.eventually (gt_mem_nhds (mul_pos hlpos hε))] with k hk
    have hP1 : Integrable (lmP_pair (H_k k) (G_k k))
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        lmP_mul_integrable (hHk_L2 k j i) (hGk_L2 k j i)
    have hP2 : Integrable (lmP_pair H (G_k k))
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        lmP_mul_integrable (hH_L2 j i) (hGk_L2 k j i)
    have hGk_sq_int : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2)
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        lmP_sq_integrable (hGk_L2 k j i)
    have hpt_comm : ∀ x, 2 * l * |lmP_pair (H_k k) (G_k k) x - lmP_pair H (G_k k) x| ≤
        l ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) +
          ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2 := by
      intro x
      have hcomm1 : lmP_pair (H_k k) (G_k k) x = lmP_pair (G_k k) (H_k k) x := by
        unfold lmP_pair; congr 1; funext i; congr 1; funext j; ring
      have hcomm2 : lmP_pair H (G_k k) x = lmP_pair (G_k k) H x := by
        unfold lmP_pair; congr 1; funext i; congr 1; funext j; ring
      rw [hcomm1, hcomm2]
      exact lmP_pt_bound (G_k k x) (H_k k x) (H x) l hlpos
    have key1 := lmP_abs_integral_sub_le (lmP_pair (H_k k) (G_k k)) (lmP_pair H (G_k k))
      (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2)
      (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2)
      l hlpos hP1 hP2 hGk_sq_int (hD_int k) hpt_comm
    have hGk_le_MN : (∫ x in UnforcedLeray.B0579.cell c,
        ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) ≤ M_N := by
      have heq_N : (∫ x in UnforcedLeray.B0579.cell c,
          ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) = LMMollN c J b k s := by
        unfold LMMollN
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only
        rw [domEN_tnorm2_sq]
        simp only [hpd]
      rw [heq_N]
      exact (lmMollDomEN c ν μ F b G hD J hJ s hs hgs k).2.2.2
    have h3 : l ^ 2 * (∫ x in UnforcedLeray.B0579.cell c,
        ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) ≤ l * ε / 2 := by
      calc l ^ 2 * (∫ x in UnforcedLeray.B0579.cell c,
            ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2)
          ≤ l ^ 2 * M_N := mul_le_mul_of_nonneg_left hGk_le_MN (sq_nonneg l)
        _ = l * (l * M_N) := by ring
        _ ≤ l * (ε / 2) := mul_le_mul_of_nonneg_left hlM hlpos.le
        _ = l * ε / 2 := by ring
    have h4 : 2 * l * |(∫ x in UnforcedLeray.B0579.cell c, lmP_pair (H_k k) (G_k k) x) -
        (∫ x in UnforcedLeray.B0579.cell c, lmP_pair H (G_k k) x)| < 2 * l * ε := by
      linarith [key1, h3, hk, mul_pos hlpos hε]
    rw [Real.dist_eq, sub_zero]
    exact lt_of_mul_lt_mul_left h4 (by linarith)
  have h_tendsto : Tendsto (fun k : ℕ => ∫ x in UnforcedLeray.B0579.cell c, lmP_pair (H_k k) (G_k k) x)
      atTop (𝓝 (energyR c (flatMult tr b) G s)) := by
    have h1 := h_tendsto_diff.add h_tendsto_HGk
    rw [zero_add] at h1
    exact h1.congr fun k => sub_add_cancel _ _
  exact le_of_tendsto' h_tendsto hbd_k

/-! ### 5. Effective free-equation forcing `F' = F - flatMult tr b` -/

lemma l2loc_flatMult {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤) :
    L2locTensor c (flatMult tr b) := by
  intro s₁ s₂ hs₁ hs₁₂
  have hs₂ : 0 ≤ s₂ := (hs₁.trans hs₁₂).le
  obtain ⟨M, hM, hMb⟩ := trainVel_bound_le tr htr hs₂
  have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (tnorm2 (flatMult tr b p) ^ 2) ≤
      ENNReal.ofReal (8 * M ^ 2) *
        ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hmeas_set fun p hp => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hp1 := tnorm2_flatMult_sq_le tr b hM.le (hMb p.1 hp.1.2 p.2)
    have hp2 : 0 ≤ tnorm2 (G p) ^ 2 := sq_nonneg _
    nlinarith
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hLoc s₁ s₂ hs₁ hs₁₂))

lemma l2loc_sub {c : ℝ} {A B : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hAm : ∀ i j, Measurable fun p => A p i j)
    (hAloc : L2locTensor c A) (hBloc : L2locTensor c B) :
    L2locTensor c (fun p i j => A p i j - B p i j) := by
  intro s₁ s₂ hs₁ hs₁₂
  have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpt : ∀ p, tnorm2 (fun i j => A p i j - B p i j) ^ 2 ≤
      2 * tnorm2 (A p) ^ 2 + 2 * tnorm2 (B p) ^ 2 := by
    intro p
    rw [domEN_tnorm2_sq, domEN_tnorm2_sq, domEN_tnorm2_sq]
    have hij : ∀ i j : Fin 2, ‖A p i j - B p i j‖ ^ 2 ≤ 2 * ‖A p i j‖ ^ 2 + 2 * ‖B p i j‖ ^ 2 := by
      intro i j
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (A p i j) (B p i j)) 2
      nlinarith [sq_nonneg (‖A p i j‖ - ‖B p i j‖)]
    calc ∑ i : Fin 2, ∑ j : Fin 2, ‖A p i j - B p i j‖ ^ 2
        ≤ ∑ i : Fin 2, ∑ j : Fin 2, (2 * ‖A p i j‖ ^ 2 + 2 * ‖B p i j‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖A p i j‖ ^ 2) +
          2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖B p i j‖ ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (tnorm2 (fun i j => A p i j - B p i j) ^ 2) ≤
      ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (2 * tnorm2 (A p) ^ 2 + 2 * tnorm2 (B p) ^ 2) :=
    setLIntegral_mono' hmeas_set fun p _ => ENNReal.ofReal_le_ofReal (hpt p)
  have hA2 : ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (2 * tnorm2 (A p) ^ 2) < ⊤ := by
    have heq : (fun p => ENNReal.ofReal (2 * tnorm2 (A p) ^ 2)) =
        fun p => ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (A p) ^ 2) := by
      funext p; rw [ENNReal.ofReal_mul (by norm_num)]
    rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hAloc s₁ s₂ hs₁ hs₁₂)
  have hB2 : ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (2 * tnorm2 (B p) ^ 2) < ⊤ := by
    have heq : (fun p => ENNReal.ofReal (2 * tnorm2 (B p) ^ 2)) =
        fun p => ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (B p) ^ 2) := by
      funext p; rw [ENNReal.ofReal_mul (by norm_num)]
    rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hBloc s₁ s₂ hs₁ hs₁₂)
  have hAB : ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (2 * tnorm2 (A p) ^ 2 + 2 * tnorm2 (B p) ^ 2) < ⊤ :=
    EnergyLocInt.lintegral_ofReal_add_lt_top
      (measurable_const.mul ((EnergyLocInt.measurable_tnorm2_pt hAm).pow_const 2)) hA2 hB2
  exact lt_of_le_of_lt h1 hAB

/-- On any good slice `s > 0`, `0 ≤ energyR c F' G s + J_F s + L_str s * energyE c b s`. -/
lemma goodSlice_energyR_add_J_nonneg {c ν : ℝ} {μ : ℂ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hFmeas : ∀ i j, Measurable fun p => F p i j)
    (hD' : FreeSolData c ν μ (fun p i j => F p i j - flatMult tr b p i j) b G)
    {s : ℝ} (hs : 0 < s)
    (hgs' : LMGoodSlice c (fun p i j => F p i j - flatMult tr b p i j) G b s) :
    0 ≤ energyR c (fun p i j => F p i j - flatMult tr b p i j) G s +
      ((∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))) +
        (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal * energyE c b s) := by
  have ⟨hb, hcolG, hcolF'⟩ := hgs'
  let v : Plane → Vec := tr.v s
  obtain ⟨M₀, _, hM₀_all⟩ := trainVel_bound_le tr htr hs.le
  have hv_bdd : ∀ (i : Fin 2) (x : Plane), |v x i| ≤ M₀ := fun i x => by
    have h := hM₀_all s le_rfl x i
    simpa [trainVel, hs.le, v, Complex.norm_real] using h
  have hv_cont : ∀ i : Fin 2, Continuous (fun x => v x i) :=
    fun i => (contDiff_train_comp tr hs.le i).continuous
  have hMult_L2 : ∀ j : Fin 2, LMCellL2 c (fun x i => flatMult tr b (s, x) i j) := by
    intro j i
    have h1 : MemLp (fun x => (v x i : ℂ) * b (s, x) j) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) := by
      refine MemLp.of_le_mul (c := M₀) (hb j)
        (((Complex.continuous_ofReal.comp (hv_cont i)).aestronglyMeasurable).mul (hb j).1)
        (ae_of_all _ fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hv_bdd i x) (norm_nonneg _)
    have h2 : MemLp (fun x => b (s, x) i * (v x j : ℂ)) 2
        (volume.restrict (UnforcedLeray.B0579.cell c)) := by
      refine MemLp.of_le_mul (c := M₀) (hb i)
        ((hb i).1.mul ((Complex.continuous_ofReal.comp (hv_cont j)).aestronglyMeasurable))
        (ae_of_all _ fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hv_bdd j x) (norm_nonneg _)
    have hsum := h1.add h2
    have heq : (fun x => flatMult tr b (s, x) i j) =
        fun x => (v x i : ℂ) * b (s, x) j + b (s, x) i * (v x j : ℂ) := by
      funext x; simp [flatMult, trainVel, hs.le, v]
    rwa [heq]
  have hcolF : ∀ j : Fin 2, LMCellL2 c (fun x i => F (s, x) i j) := by
    intro j i
    have hsum := (hcolF' j i).add (hMult_L2 j i)
    have heq : (fun x => F (s, x) i j) =
        fun x => (F (s, x) i j - flatMult tr b (s, x) i j) + flatMult tr b (s, x) i j :=
      funext fun x => (sub_add_cancel _ _).symm
    rwa [heq]
  have hRF_int : Integrable (lmP_pair (fun x => F (s, x)) (fun x => G (s, x)))
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      lmP_mul_integrable (hcolF j i) (hcolG j i)
  have hRMult_int : Integrable (lmP_pair (fun x => flatMult tr b (s, x)) (fun x => G (s, x)))
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      lmP_mul_integrable (hMult_L2 j i) (hcolG j i)
  have hR_sub : energyR c (fun p i j => F p i j - flatMult tr b p i j) G s =
      energyR c F G s - energyR c (flatMult tr b) G s := by
    unfold energyR
    have hpt : (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
        (((F (s, x) i j - flatMult tr b (s, x) i j).re * (G (s, x) i j).re +
          (F (s, x) i j - flatMult tr b (s, x) i j).im * (G (s, x) i j).im))) =
        fun x => lmP_pair (fun x => F (s, x)) (fun x => G (s, x)) x -
          lmP_pair (fun x => flatMult tr b (s, x)) (fun x => G (s, x)) x := by
      funext x
      unfold lmP_pair
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    rw [hpt, integral_sub hRF_int hRMult_int]
    rfl
  -- Also `0 ≤ energyR c F G s + ∫_cell tnorm2(F(s,x)) * tnorm2(G(s,x))`
  have hF_sq_int : Integrable (fun x => tnorm2 (F (s, x)) ^ 2)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have heq : (fun x => tnorm2 (F (s, x)) ^ 2) =
        fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2 :=
      funext fun x => domEN_tnorm2_sq _
    rw [heq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      lmP_sq_integrable (hcolF j i)
  have hG_sq_int : Integrable (fun x => tnorm2 (G (s, x)) ^ 2)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have heq : (fun x => tnorm2 (G (s, x)) ^ 2) =
        fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
      funext fun x => domEN_tnorm2_sq _
    rw [heq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      lmP_sq_integrable (hcolG j i)
  have hJF_int : Integrable (fun x => tnorm2 (F (s, x)) * tnorm2 (G (s, x)))
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have hF_m : Measurable fun x => tnorm2 (F (s, x)) :=
      ct_measurable_tnorm2 fun i j => (hFmeas i j).comp (measurable_const.prodMk measurable_id)
    have hG_m : Measurable fun x => tnorm2 (G (s, x)) :=
      ct_measurable_tnorm2 fun i j =>
        (hD'.sol.gradMeasurable i j).comp (measurable_const.prodMk measurable_id)
    refine (hF_sq_int.add hG_sq_int).mono' (hF_m.mul hG_m).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact ct_abs_mul_le _ _
  have hRF_JF_nn : 0 ≤ energyR c F G s +
      ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)) := by
    change 0 ≤ (∫ x in UnforcedLeray.B0579.cell c,
        lmP_pair (fun x => F (s, x)) (fun x => G (s, x)) x) +
      ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))
    rw [← integral_add hRF_int hJF_int]
    apply integral_nonneg
    intro x
    have h1 := abs_sum_re_le_tnorm2_mul (F (s, x)) (G (s, x))
    have h2 := neg_abs_le (lmP_pair (fun x => F (s, x)) (fun x => G (s, x)) x)
    unfold lmP_pair at h2 ⊢
    dsimp only [Pi.add_apply, Pi.zero_apply] at h2 ⊢
    linarith
  have hadv := goodSlice_advection_energyR_le tr htr hD' hs hgs'
  linarith

end AdvectionEnergyAux

open AdvectionEnergyAux
open UnforcedLeray.Short.IIIa.CoreToSmoothAux
open UnforcedLeray.Short.IIIa.SmoothToC1Aux

/-- **Leaf `PartIII-a:T19/3/1` (`trainAdvectionEnergyIdentity`)** (SP lines 3518-3527):
Distributional weighted energy inequality for any causal zero-entrance energy solution around a BUC
train `tr`. -/
theorem trainAdvectionEnergyIdentity : UnforcedLeray.Short.IIIa.TrainAdvectionEnergyIdentity := by
  intro c ν γ μ hc hν hγ tr htr F b G hFloc hFmeas hcaus ψ hψ hψc hψsupp hψnn
  -- 1. Reduce to the free equation with effective forcing `F' = F - flatMult tr b`
  let F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => F p i j - flatMult tr b p i j
  have hsol_free : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F' b G := by
    have h0 : (fun p i j => F p i j + (0 : ℂ)) = F := by funext p i j; exact add_zero _
    have hcaus' : IsCausalEnergySolution c ν μ (trainVel tr)
        (fun p i j => F p i j + 0) b G := by
      rw [h0]; exact hcaus
    have hred := causal_free_reduction tr μ hcaus'
    have hF' : (fun p i j => (F p i j - flatMult tr b p i j) + 0) = F' := by
      funext p i j; exact add_zero _
    rwa [hF'] at hred
  have hbm : ∀ i, Measurable fun p => b p i := hcaus.measurable
  have hMult_meas : ∀ i j, Measurable fun p => flatMult tr b p i j :=
    measurable_flatMult tr hbm
  have hF'meas : ∀ i j, Measurable fun p => F' p i j :=
    fun i j => (hFmeas i j).sub (hMult_meas i j)
  have hMult_loc : L2locTensor c (flatMult tr b) := l2loc_flatMult tr htr hcaus.energyLoc
  have hF'loc : L2locTensor c F' := l2loc_sub hFmeas hFloc hMult_loc
  have hD' : FreeSolData c ν μ F' b G := ⟨hc, hν, hF'loc, hF'meas, hsol_free⟩
  have hCore' : CoreIdentity c ν μ F' b G :=
    lionsMagenesCyl (flatWeakFromDensity divFreeCutoffDensity) c ν μ F' b G hD'
  -- 2. Locate compact support of `ψ` in `[s₁, s₂] ⊂ [s₁/2, s₂ + 1] ⊂ (0, ∞)`
  obtain ⟨s1, s2, hs1, hs12, hsub⟩ :=
    exists_Icc_contains (tsupport ψ) (hψc : IsCompact (tsupport ψ)) hψsupp
  set a : ℝ := s1 / 2
  set b_end : ℝ := s2 + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b_end := by dsimp [a, b_end]; linarith
  have hKc : IsCompact (Icc a b_end) := isCompact_Icc
  have hKm : MeasurableSet (Icc a b_end) := measurableSet_Icc
  obtain ⟨hEI, hNI, hR_F'I, _⟩ := energyLocIntegrable c ν μ F' b G hD' a b_end ha hab
  let L_str : ℝ → ℝ := fun s => (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal
  let L_ite : ℝ → ℝ := fun s => if 0 < s then L_str s else 0
  let J_F : ℝ → ℝ := fun s => ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))
  let J_tot : ℝ → ℝ := fun s => J_F s + L_str s * energyE c b s
  have hJ_FI : IntegrableOn J_F (Icc a b_end) := by
    have hGm : ∀ i j, Measurable fun p => G p i j := hcaus.gradMeasurable
    have hTF : Measurable fun p => tnorm2 (F p) := EnergyLocInt.measurable_tnorm2_pt hFmeas
    have hTG : Measurable fun p => tnorm2 (G p) := EnergyLocInt.measurable_tnorm2_pt hGm
    have hA : ∫⁻ p in Icc a b_end ×ˢ UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) < ⊤ :=
      EnergyLocInt.lintegral_ofReal_add_lt_top (hTF.pow_const 2)
        (hFloc a b_end ha hab) (hcaus.energyLoc a b_end ha hab)
    have hJb : ∀ p, |tnorm2 (F p) * tnorm2 (G p)| ≤
        tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
      have h2 := EnergyLocInt.abs_mul_le_sq_add' (tnorm2 (F p)) (tnorm2 (G p))
      linarith [sq_nonneg (vnorm2 (b p))]
    exact EnergyLocInt.integrableOn_cell_integral (fun p => tnorm2 (F p) * tnorm2 (G p))
      (fun p => tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) (hTF.mul hTG) hJb hA
  obtain ⟨M_L, hML0, hML_bd⟩ := supNormD_one_bound_on tr htr (ha.trans hab).le
  have hL_meas : Measurable L_ite := measurable_supNormD_one_toReal_ite tr
  have hLE_int : IntegrableOn (fun s => L_str s * energyE c b s) (Icc a b_end) := by
    have h1 : IntegrableOn (fun s => L_ite s * energyE c b s) (Icc a b_end) := by
      have hbd_ae : ∀ᵐ s ∂volume.restrict (Icc a b_end), ‖L_ite s‖ ≤ M_L := by
        filter_upwards [ae_restrict_mem hKm] with s hs
        have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
        dsimp [L_ite, L_str]
        split_ifs
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        exact (hML_bd s ⟨hs0.le, hs.2⟩).2.1
      exact hEI.bdd_mul hL_meas.aestronglyMeasurable.restrict hbd_ae
    refine h1.congr_fun (fun s hs => ?_) hKm
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    dsimp [L_ite]
    split_ifs
    rfl
  have hJ_tot_int : IntegrableOn J_tot (Icc a b_end) := hJ_FI.add hLE_int
  have hE0 : ∀ s, 0 ≤ energyE c b s := fun s => integral_nonneg fun _ => sq_nonneg _
  have hRJ_tot : ∀ᵐ s ∂(volume.restrict (Icc a b_end)),
      0 ≤ energyR c F' G s + J_tot s := by
    have hae_Ioi := (ae_restrict_iff' measurableSet_Ioi).1 (lmAeGoodSlice c ν μ F' b G hD')
    rw [ae_restrict_iff' hKm]
    filter_upwards [hae_Ioi] with s hs hs_ab
    have hs0 : 0 < s := lt_of_lt_of_le ha hs_ab.1
    exact goodSlice_energyR_add_J_nonneg tr htr hFmeas hD' hs0 (hs hs0)
  -- 3. Mollify `ψ` via `sm ψ n` (`SmoothToC1Aux`) and apply `real_core` for each `n ≥ N1`
  have hψcont : Continuous ψ := hψ.continuous
  have hdψcont : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hdψc : HasCompactSupport (deriv ψ) := hψc.deriv
  have hsuppd : tsupport (deriv ψ) ⊆ Icc s1 s2 := tsupport_deriv_subset.trans hsub
  have hψ0 : ∀ s, s ∉ Icc a b_end → ψ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hs ⟨by dsimp [a]; linarith [(hsub h).1], by dsimp [b_end]; linarith [(hsub h).2]⟩)
  have hdψ0 : ∀ s, s ∉ Icc a b_end → deriv ψ s = 0 := fun s hs =>
    deriv_of_notMem_tsupport
      (fun h => hs ⟨by dsimp [a]; linarith [(hsub h).1], by dsimp [b_end]; linarith [(hsub h).2]⟩)
  obtain ⟨N1, hN1⟩ := exists_nat_one_div_lt (show (0 : ℝ) < min a 1 from lt_min ha one_pos)
  have hthr : ∀ n, N1 ≤ n → 1 / ((n : ℝ) + 1) ≤ a ∧ 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n hn
    have hN : (N1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N1 : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 := lt_of_le_of_lt h1 hN1
    exact ⟨(h2.trans_le (min_le_left _ _)).le, (h2.trans_le (min_le_right _ _)).le⟩
  have hzero_n : ∀ n, N1 ≤ n → ∀ x, x ∉ Icc a b_end → sm ψ n x = 0 := fun n hn x hx =>
    sm_zero ψ s1 s2 hsub n (hthr n hn).1 (hthr n hn).2 hx
  have hcs : ∀ n, N1 ≤ n → HasCompactSupport (sm ψ n) := fun n hn =>
    HasCompactSupport.intro isCompact_Icc (fun x hx => hzero_n n hn x hx)
  have htsupp_Icc : ∀ n, N1 ≤ n → tsupport (sm ψ n) ⊆ Icc a b_end := fun n hn => by
    have hsub' : Function.support (sm ψ n) ⊆ Icc a b_end := fun x hx => by
      by_contra h
      exact hx (hzero_n n hn x h)
    exact closure_minimal hsub' isClosed_Icc
  have htsupp : ∀ n, N1 ≤ n → tsupport (sm ψ n) ⊆ Ioi 0 := fun n hn =>
    (htsupp_Icc n hn).trans (fun s hs => lt_of_lt_of_le ha hs.1)
  have hderiv : ∀ n, deriv (sm ψ n) = sm (deriv ψ) n := fun n =>
    funext fun x => (sm_hasDerivAt ψ hψc hψ n x).deriv
  have hcontder : ∀ n, Continuous (deriv (sm ψ n)) := fun n => by
    rw [hderiv n]
    exact (sm_contDiff _ hdψcont n).continuous
  have hqK : ContinuousOn (qWt γ ν) (Icc a b_end) := fun s hs =>
    (hasDerivAt_qWt γ ν hν (lt_of_lt_of_le ha hs.1)).continuousAt.continuousWithinAt
  have hpowK : ContinuousOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Icc a b_end) := fun s hs =>
    (Real.continuousAt_rpow_const s _ (Or.inl (lt_of_lt_of_le ha hs.1).ne')).continuousWithinAt
  have hpow3K : ContinuousOn (fun s : ℝ => s ^ (-3 / 2 : ℝ)) (Icc a b_end) := fun s hs =>
    (Real.continuousAt_rpow_const s _ (Or.inl (lt_of_lt_of_le ha hs.1).ne')).continuousWithinAt
  have hUI : IntegrableOn (Uf c ν γ b) (Icc a b_end) :=
    (intK_mul hKc hEI hqK).congr_fun (fun s _ => (Uf_eq c ν γ b s).symm) hKm
  have hVI : IntegrableOn (Vf c ν γ G) (Icc a b_end) :=
    (intK_mul hKc hNI hqK).congr_fun (fun s _ => (Vf_eq c ν γ G s).symm) hKm
  have hJI' : IntegrableOn (Jf c ν γ F G) (Icc a b_end) :=
    (intK_mul hKc hJ_FI hqK).congr_fun (fun s _ => (Jf_eq c ν γ F G s).symm) hKm
  have hLUI : IntegrableOn (fun s => L_str s * Uf c ν γ b s) (Icc a b_end) :=
    (intK_mul hKc hLE_int hqK).congr_fun (fun s _ => by rw [Uf_eq]; ring) hKm
  have hA1 : IntegrableOn (fun s => (1 / 2 + 2 * μ.re) * s ^ (-3 / 2 : ℝ) * Uf c ν γ b s)
      (Icc a b_end) :=
    intK_mul hKc hUI (continuousOn_const.mul hpow3K)
  have hA2 : IntegrableOn (fun s => 2 * ν * s ^ (-1 / 2 : ℝ) * Vf c ν γ G s)
      (Icc a b_end) :=
    intK_mul hKc hVI (continuousOn_const.mul hpowK)
  have hAI : IntegrableOn (fun s => Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s)
      (Icc a b_end) := hA1.add hA2
  have hBI : IntegrableOn (fun s => s ^ (-1 / 2 : ℝ) * Uf c ν γ b s) (Icc a b_end) :=
    intK_mul hKc hUI hpowK
  have h2powK : ContinuousOn (fun s : ℝ => 2 * s ^ (-1 / 2 : ℝ)) (Icc a b_end) :=
    continuousOn_const.mul hpowK
  have hBLI : IntegrableOn (fun s => 2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) (Icc a b_end) :=
    (intK_mul hKc hLUI h2powK).congr_fun (fun s _ => by dsimp only; ring) hKm
  have hCI : IntegrableOn (fun s => s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
      (Icc a b_end) :=
    intK_mul hKc hJI' hpowK
  -- Smooth inequality for each `n ≥ N1`
  have hle_n : ∀ᶠ n in atTop,
      (∫ s in Ioi (0 : ℝ), sm ψ n s * Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s) ≤
        ((∫ s in Ioi (0 : ℝ), deriv (sm ψ n) s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) +
          ∫ s in Ioi (0 : ℝ), sm ψ n s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))) +
        2 * ∫ s in Ioi (0 : ℝ), sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s := by
    filter_upwards [eventually_ge_atTop N1] with n hn
    have hsm_cd : ContDiff ℝ ∞ (sm ψ n) := sm_contDiff ψ hψcont n
    have hcore_n := hCore' (wWeight γ ν (sm ψ n))
      (contDiff_wWeight γ ν (sm ψ n) hsm_cd hν (htsupp n hn))
      (hasCompactSupport_wWeight γ ν (sm ψ n) (hcs n hn))
      ((tsupport_wWeight_subset γ ν (sm ψ n)).trans (htsupp n hn))
    have hrc := real_core γ ν μ.re a b_end hν hγ ha hab (sm ψ n) hsm_cd
      (htsupp_Icc n hn) (fun s => sm_nonneg ψ hψnn n s)
      (energyE c b) (energyN c G) (energyR c F' G) J_tot
      hEI hNI hR_F'I hJ_tot_int hE0 hRJ_tot hcore_n
    simp only [ ← Uf_eq, ← Vf_eq] at hrc
    have hJtot_eq : ∀ s : ℝ, qWt γ ν s * J_tot s = Jf c ν γ F G s + L_str s * Uf c ν γ b s := by
      intro s
      dsimp [J_tot]
      rw [mul_add, ← Jf_eq, ← mul_left_comm, ← Uf_eq]
    simp only [hJtot_eq] at hrc
    -- Split the `Jf + L_str * Uf` integral over `Icc a b_end`
    have hz_tot : ∀ s, s ∉ Icc a b_end →
        sm ψ n s * s ^ (-1 / 2 : ℝ) * (Jf c ν γ F G s + L_str s * Uf c ν γ b s) = 0 :=
      fun s hs => by simp [hzero_n n hn s hs]
    have hz_J : ∀ s, s ∉ Icc a b_end →
        sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s = 0 :=
      fun s hs => by simp [hzero_n n hn s hs]
    have hz_L : ∀ s, s ∉ Icc a b_end →
        sm ψ n s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) = 0 :=
      fun s hs => by simp [hzero_n n hn s hs]
    have hI_J : IntegrableOn (fun s => sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
        (Icc a b_end) :=
      (intK_mul hKc hCI hsm_cd.continuous.continuousOn).congr_fun (fun s _ => by ring) hKm
    have hI_L : IntegrableOn (fun s => sm ψ n s * s ^ (-1 / 2 : ℝ) * (L_str s * Uf c ν γ b s))
        (Icc a b_end) :=
      (intK_mul hKc hLUI (hsm_cd.continuous.continuousOn.mul hpowK)).congr_fun
        (fun s _ => by dsimp only [Pi.mul_apply]) hKm
    have hsplit_J : (2 : ℝ) * (∫ s in Ioi (0 : ℝ),
        sm ψ n s * s ^ (-1 / 2 : ℝ) * (Jf c ν γ F G s + L_str s * Uf c ν γ b s)) =
        (∫ s in Ioi (0 : ℝ), sm ψ n s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))) +
        2 * ∫ s in Ioi (0 : ℝ), sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s := by
      rw [toK_Ioi a b_end ha _ hz_tot, toK_Ioi a b_end ha _ hz_L, toK_Ioi a b_end ha _ hz_J]
      have heq_add : (fun s => sm ψ n s * s ^ (-1 / 2 : ℝ) *
          (Jf c ν γ F G s + L_str s * Uf c ν γ b s)) =
          fun s => sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s +
            sm ψ n s * s ^ (-1 / 2 : ℝ) * (L_str s * Uf c ν γ b s) := by
        funext s; ring
      have heq_2L : (fun s => 2 * (sm ψ n s * s ^ (-1 / 2 : ℝ) * (L_str s * Uf c ν γ b s))) =
          fun s => sm ψ n s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) := by
        funext s; ring
      rw [heq_add, integral_add hI_J hI_L, ← heq_2L, integral_const_mul 2]
      ring
    unfold Aw
    linarith [hrc, hsplit_J]
  -- 4. Pass to the limit `n → ∞` using `tendsto_Ioi_dom`
  obtain ⟨MΨ, hMΨ⟩ := sm_bound ψ hψcont hψc
  obtain ⟨MD, hMD⟩ := sm_bound (deriv ψ) hdψcont hdψc
  have hpt : ∀ s, Tendsto (fun n => sm ψ n s) atTop (𝓝 (ψ s)) := fun s =>
    sm_tendsto ψ hψcont hψc s
  have hptd : ∀ s, Tendsto (fun n => deriv (sm ψ n) s) atTop (𝓝 (deriv ψ s)) := fun s => by
    simp only [hderiv]
    exact sm_tendsto (deriv ψ) hdψcont hdψc s
  have hLHS : Tendsto (fun n => ∫ s in Ioi (0 : ℝ), sm ψ n s * Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s)
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), ψ s * Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s)) := by
    refine tendsto_Ioi_dom a b_end ha _ _ _ (hAI.abs.const_mul MΨ) ?_ ?_ ?_ ?_ ?_
    · exact fun n => ((sm_contDiff ψ hψcont n).continuous.aestronglyMeasurable).mul
        hAI.aestronglyMeasurable
    · exact fun s => (hpt s).mul_const _
    · filter_upwards [hMΨ] with n hn s _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      rw [hzero_n n hn s hs, zero_mul]
    · intro s hs
      rw [hψ0 s hs, zero_mul]
  have hRHS1a : Tendsto (fun n => ∫ s in Ioi (0 : ℝ),
      deriv (sm ψ n) s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))) := by
    refine tendsto_Ioi_dom a b_end ha _ _ _ (hBI.abs.const_mul MD) ?_ ?_ ?_ ?_ ?_
    · exact fun n => (hcontder n).aestronglyMeasurable.mul hBI.aestronglyMeasurable
    · exact fun s => (hptd s).mul_const _
    · filter_upwards [hMD] with n hn s _
      rw [congrFun (hderiv n) s, abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      rw [congrFun (hderiv n) s, sm_zero (deriv ψ) s1 s2 hsuppd n (hthr n hn).1 (hthr n hn).2 hs,
        zero_mul]
    · intro s hs
      rw [hdψ0 s hs, zero_mul]
  have hRHS1b : Tendsto (fun n => ∫ s in Ioi (0 : ℝ),
      sm ψ n s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)))
      atTop (𝓝 (∫ s in Ioi (0 : ℝ),
        ψ s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)))) := by
    refine tendsto_Ioi_dom a b_end ha _ _ _ (hBLI.abs.const_mul MΨ) ?_ ?_ ?_ ?_ ?_
    · exact fun n => ((sm_contDiff ψ hψcont n).continuous.aestronglyMeasurable).mul
        hBLI.aestronglyMeasurable
    · exact fun s => (hpt s).mul_const _
    · filter_upwards [hMΨ] with n hn s _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      rw [hzero_n n hn s hs, zero_mul]
    · intro s hs
      rw [hψ0 s hs, zero_mul]
  have hCeq : ∀ n, (fun s => sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s) =
      fun s => sm ψ n s * (s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s) := fun n =>
    funext fun s => mul_assoc _ _ _
  have hRHS2 : Tendsto (fun n => ∫ s in Ioi (0 : ℝ), sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)) := by
    refine tendsto_Ioi_dom a b_end ha _ _ _ (hCI.abs.const_mul MΨ) ?_ ?_ ?_ ?_ ?_
    · exact fun n => by
        rw [hCeq n]
        exact ((sm_contDiff ψ hψcont n).continuous.aestronglyMeasurable).mul
          hCI.aestronglyMeasurable
    · exact fun s => by
        simpa only [mul_assoc] using (hpt s).mul_const (s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
    · filter_upwards [hMΨ] with n hn s _
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      simp [hzero_n n hn s hs]
    · intro s hs
      simp [hψ0 s hs]
  have hlim := le_of_tendsto_of_tendsto hLHS
    ((hRHS1a.add hRHS1b).add (hRHS2.const_mul 2)) hle_n
  -- Combine `deriv ψ` and `2 * L_str * ψ` integrals on `Ioi 0`
  have hz_1a : ∀ s, s ∉ Icc a b_end →
      deriv ψ s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s) = 0 := fun s hs => by
    rw [hdψ0 s hs, zero_mul]
  have hz_1b : ∀ s, s ∉ Icc a b_end →
      ψ s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) = 0 := fun s hs => by
    rw [hψ0 s hs, zero_mul]
  have hz_1ab : ∀ s, s ∉ Icc a b_end →
      (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s) = 0 := fun s hs => by
    rw [hdψ0 s hs, hψ0 s hs]; ring
  have hI_1a : IntegrableOn (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))
      (Icc a b_end) :=
    intK_mul hKc hBI hdψcont.continuousOn
  have hI_1b : IntegrableOn (fun s => ψ s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)))
      (Icc a b_end) :=
    intK_mul hKc hBLI hψcont.continuousOn
  have hcomb : (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) +
      (∫ s in Ioi (0 : ℝ), ψ s * (2 * L_str s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))) =
      ∫ s in Ioi (0 : ℝ), (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s) := by
    rw [toK_Ioi a b_end ha _ hz_1a, toK_Ioi a b_end ha _ hz_1b, toK_Ioi a b_end ha _ hz_1ab,
      ← integral_add hI_1a hI_1b]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    ring
  rw [hcomb] at hlim
  exact hlim

end UnforcedLeray.Short.IIIa
