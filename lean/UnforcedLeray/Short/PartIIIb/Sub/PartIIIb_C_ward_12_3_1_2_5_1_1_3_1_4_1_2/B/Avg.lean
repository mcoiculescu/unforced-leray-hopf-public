import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.B.Open
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Horizontal averaging does not increase a sup bound on joint jets (open `s > 0`)

For `F : ℝ → Plane → ℝ` that is `C^∞` on `D = (0,∞) × Plane`, the horizontal average
`x ↦ hmean c (F x.1) x.2.2` (a function on `ℝ × Plane`) is `C^∞` on `D`, and a bound `K` on the
joint jets of `F` of orders `≤ N` on `D` is a bound for its joint jets of orders `≤ N`
(source `shorter-proof-2026-11-02.tex` 397-404).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.PO

open UnforcedLeray.Cyl (Plane)

/-- The domain `s > 0`. -/
abbrev DD : Set (ℝ × Plane) := Ioi (0 : ℝ) ×ˢ (univ : Set Plane)

theorem isOpen_DD : IsOpen DD := isOpen_Ioi.prod isOpen_univ

/-- The projection `(s,q,η) ↦ (s,0,η)`. -/
def projA : (ℝ × Plane) →L[ℝ] (ℝ × Plane) :=
  (ContinuousLinearMap.fst ℝ ℝ Plane).prod
    ((0 : (ℝ × Plane) →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)))

theorem projA_apply (y : ℝ × Plane) : projA y = (y.1, (0, y.2.2)) := rfl

theorem norm_projA_le : ‖projA‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
  rw [projA_apply, one_mul]
  have h1 : ‖y.1‖ ≤ ‖y‖ := norm_fst_le y
  have h2 : ‖y.2.2‖ ≤ ‖y‖ := (norm_snd_le y.2).trans (norm_snd_le y)
  rw [Prod.norm_def, Prod.norm_def, norm_zero]
  exact max_le h1 (max_le (norm_nonneg _) h2)

theorem slice_jet {H : ℝ × Plane → ℝ} (hH : ContDiffOn ℝ ∞ H DD) (q : ℝ) (n : ℕ)
    {y : ℝ × Plane} (hy : 0 < y.1) :
    iteratedFDeriv ℝ n (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) y =
      (iteratedFDeriv ℝ n H (y.1, (q, y.2.2))).compContinuousLinearMap (fun _ => projA) := by
  set w : ℝ × Plane := (0, (q, 0)) with hw
  have hf : ContDiffOn ℝ ∞ (fun z : ℝ × Plane => H (z + w)) DD := by
    refine hH.comp (contDiffOn_id.add contDiffOn_const) (fun z hz => ?_)
    simpa [hw] using hz
  have hfun : (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) =
      (fun z : ℝ × Plane => H (z + w)) ∘ projA := by
    funext y'
    simp [projA_apply, hw]
  have hopen : IsOpen (projA ⁻¹' DD) := isOpen_DD.preimage projA.continuous
  have hmem : projA y ∈ DD := ⟨by simpa [projA_apply] using hy, mem_univ _⟩
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (n := ∞) (i := n) projA hf
    isOpen_DD.uniqueDiffOn hopen.uniqueDiffOn hmem (by exact_mod_cast le_top)
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := (fun z : ℝ × Plane => H (z + w)) ∘ projA) n
    hopen (show y ∈ projA ⁻¹' DD from hmem)
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : ℝ × Plane => H (z + w)) n
    isOpen_DD hmem
  rw [e1, e2, ← hfun, iteratedFDeriv_comp_add_right] at key
  rw [key]
  congr 2
  simp [projA_apply, hw]

theorem slice_jet_norm {H : ℝ × Plane → ℝ} (hH : ContDiffOn ℝ ∞ H DD) (q : ℝ) (n : ℕ)
    {y : ℝ × Plane} (hy : 0 < y.1) :
    ‖iteratedFDeriv ℝ n (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) y‖ ≤
      ‖iteratedFDeriv ℝ n H (y.1, (q, y.2.2))‖ := by
  rw [slice_jet hH q n hy]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖projA‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun _ _ => norm_projA_le)
  calc _ ≤ ‖iteratedFDeriv ℝ n H (y.1, (q, y.2.2))‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

theorem slice_contDiffOn {H : ℝ × Plane → ℝ} (hH : ContDiffOn ℝ ∞ H DD) (q : ℝ) :
    ContDiffOn ℝ ∞ (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) DD := by
  have : ContDiff ℝ ∞ (fun y : ℝ × Plane => ((y.1, (q, y.2.2)) : ℝ × Plane)) := by fun_prop
  exact hH.comp this.contDiffOn (fun y hy => ⟨hy.1, mem_univ _⟩)

theorem slice_meas {H : ℝ × Plane → ℝ} (hH : ContDiffOn ℝ ∞ H DD) (n : ℕ) {y : ℝ × Plane}
    (hy : 0 < y.1) (μ : Measure ℝ) :
    AEStronglyMeasurable
      (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) y) μ := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n H) DD := by
    have := hH.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top)
      isOpen_DD.uniqueDiffOn
    exact this.congr (fun z hz => (iteratedFDerivWithin_of_isOpen n isOpen_DD hz).symm)
  have hg : Continuous (fun q : ℝ => ((y.1, (q, y.2.2)) : ℝ × Plane)) := by fun_prop
  have h1 : Continuous (fun q : ℝ => iteratedFDeriv ℝ n H (y.1, (q, y.2.2))) :=
    hc.comp_continuous hg (fun q => ⟨hy, mem_univ _⟩)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Plane) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => projA)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => projA)).continuous
  refine ((hT.comp h1).aestronglyMeasurable).congr (Eventually.of_forall fun q => ?_)
  exact (slice_jet hH q n hy).symm

theorem slice_locDom {H : ℝ × Plane → ℝ} (hH : ContDiffOn ℝ ∞ H DD) (c : ℝ) :
    LocDom (volume.restrict (Ioc (-c / 2) (c / 2)))
      (fun (q : ℝ) (y : ℝ × Plane) => H (y.1, (q, y.2.2))) DD := by
  intro n x hx
  have hx1 : 0 < x.1 := hx.1
  set r : ℝ := x.1 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hball : ∀ y ∈ Metric.closedBall x r, 0 < y.1 := by
    intro y hy
    have h := (Metric.mem_closedBall.1 hy)
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, abs_le] at h
    have := h.1.1
    linarith
  have hKc : IsCompact ((fun p : (ℝ × Plane) × ℝ => ((p.1.1, (p.2, p.1.2.2)) : ℝ × Plane)) ''
      (Metric.closedBall x r ×ˢ Icc (-c / 2) (c / 2))) :=
    ((isCompact_closedBall x r).prod isCompact_Icc).image (by fun_prop)
  have hsub : ((fun p : (ℝ × Plane) × ℝ => ((p.1.1, (p.2, p.1.2.2)) : ℝ × Plane)) ''
      (Metric.closedBall x r ×ˢ Icc (-c / 2) (c / 2))) ⊆ DD := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hball p.1 hp.1, mem_univ _⟩
  have hc : ContinuousOn (iteratedFDeriv ℝ n H) DD := by
    have := hH.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top)
      isOpen_DD.uniqueDiffOn
    exact this.congr (fun z hz => (iteratedFDerivWithin_of_isOpen n isOpen_DD hz).symm)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨Metric.closedBall x r, Metric.closedBall_mem_nhds x hr0, fun _ => C,
    integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-c / 2) (c / 2)))]
    with q hq y hy
  refine (slice_jet_norm hH q n (hball y hy)).trans (hC _ ⟨(y, q), ⟨hy, Ioc_subset_Icc_self hq⟩, rfl⟩)

/-- **Horizontal averaging preserves joint-jet bounds** (SP 397-404). -/
theorem hmean_jets {c : ℝ} (hc : 0 < c) (F : ℝ → Plane → ℝ) (N : ℕ) (K : ℝ)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) DD)
    (hK : ∀ k : ℕ, k ≤ N → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ k (fun x : ℝ × Plane => F x.1 x.2) y‖ ≤ K) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.hmean c (F x.1) x.2.2) DD ∧
    ∀ k : ℕ, k ≤ N → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ k
        (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.hmean c (F x.1) x.2.2) y‖ ≤ K := by
  set μ : Measure ℝ := volume.restrict (Ioc (-c / 2) (c / 2)) with hμ
  set H : ℝ × Plane → ℝ := fun x => F x.1 x.2 with hH
  have hHsm : ContDiffOn ℝ ∞ H DD := hF
  have hsm := fun q => slice_contDiffOn hHsm q
  have hmeas : ∀ (n : ℕ), ∀ x ∈ DD, AEStronglyMeasurable
      (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) x) μ :=
    fun n x hx => slice_meas hHsm n hx.1 μ
  have hdom := slice_locDom hHsm c
  have hI : ContDiffOn ℝ ∞ (fun y : ℝ × Plane => ∫ q, H (y.1, (q, y.2.2)) ∂μ) DD :=
    contDiffOn_int (F := fun (q : ℝ) (y : ℝ × Plane) => H (y.1, (q, y.2.2))) isOpen_DD
      (ae_of_all _ hsm) hmeas hdom
  have hfun : (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.hmean c (F x.1) x.2.2) =
      fun y => c⁻¹ • ∫ q, H (y.1, (q, y.2.2)) ∂μ := rfl
  rw [hfun]
  refine ⟨hI.const_smul c⁻¹, fun k hk y hy => ?_⟩
  have hat : ContDiffAt ℝ ∞ (fun y : ℝ × Plane => ∫ q, H (y.1, (q, y.2.2)) ∂μ) y :=
    hI.contDiffAt (isOpen_DD.mem_nhds ⟨hy, mem_univ _⟩)
  rw [iteratedFDeriv_const_smul_apply' (hat.of_le (by exact_mod_cast le_top)),
    norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc]
  have hyD : y ∈ DD := ⟨hy, mem_univ _⟩
  rw [iteratedFDeriv_int_eq (F := fun (q : ℝ) (y : ℝ × Plane) => H (y.1, (q, y.2.2)))
    isOpen_DD (ae_of_all _ hsm) hmeas hdom k hyD]
  have hfin : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun q : ℝ => iteratedFDeriv ℝ k (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) y)
    (C := K) (by
      filter_upwards with q
      exact (slice_jet_norm hHsm q k hy).trans (hK k hk _ hy))
  have hmu : μ.real univ = c := by
    rw [hμ, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hmu] at hb
  calc c⁻¹ * ‖∫ q, iteratedFDeriv ℝ k (fun y' : ℝ × Plane => H (y'.1, (q, y'.2.2))) y ∂μ‖
      ≤ c⁻¹ * (K * c) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = K := by field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.PO
