import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvDerivCyl
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvFlowCyl
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont.GlobE
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace VtvYRMeasAux

open UnforcedLeray.Short.IIIa.GlobEAux (pd_slice contOn_pd_Ec)

/-- Continuity of the slice derivative of a function smooth on `(0,∞) × ℝ²`. -/
theorem contOn_fd {F : ℝ × (ℝ × ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (j : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (fun y => F (p.1, y)) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have h1 : ContinuousOn (fun p => fderiv ℝ F p ((0 : ℝ), B0579.dir j))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (hF.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  refine h1.congr fun p hp => ?_
  have := pd_slice hF hp.1 j p.2
  simpa using this

/-- The `s`-derivative as a derivative of the uncurried function. -/
theorem deriv_eq {η : ℝ → ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2)) (s : ℝ) (x : ℝ × ℝ) :
    deriv (fun s' => η s' x) s =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2) (s, x) ((1 : ℝ), (0 : ℝ × ℝ)) := by
  have hGdiff : Differentiable ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) :=
    hG.differentiable (by simp)
  have hG' : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x)) (s, x) :=
    (hGdiff (s, x)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  exact (hG'.comp_hasDerivAt s hline).deriv

theorem contDiff_D {F : ℝ × (ℝ × ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (v : ℝ × (ℝ × ℝ)) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ F p v) :=
  (contDiff_infty_iff_fderiv.1 hF).2.clm_apply contDiff_const

/-- Continuity of `(s,x) ↦ ∂_j ∂_sη(s,x)`. -/
theorem contOn_dsEta {η : ℝ → ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2)) (j : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      B0579.pd j (fun x => deriv (fun s' => η s' x) p.1) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hF1 := contDiff_D hG ((1 : ℝ), (0 : ℝ × ℝ))
  have := contOn_fd hF1.contDiffOn j
  refine this.congr fun p hp => ?_
  have h : (fun x => deriv (fun s' => η s' x) p.1) = fun y =>
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2) (p.1, y) ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun y => deriv_eq hG p.1 y
  rw [h]

/-- Continuity of `(s,x) ↦ ∂_jη(s,x)`. -/
theorem contOn_Eta {η : ℝ → ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2)) (j : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (η p.1) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  contOn_fd (F := fun p : ℝ × (ℝ × ℝ) => η p.1 p.2) hG.contDiffOn j

/-- Continuity of `(s,x) ↦ ∂_j(νΔη(s)+v·∇η(s))(x)`. -/
theorem contOn_flow {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {η : ℝ → ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2)) (j : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (vtvFlowTest tr p.1 (η p.1)) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  set G : ℝ × (ℝ × ℝ) → ℝ := fun p => η p.1 p.2 with hGdef
  set D : Fin 2 → ℝ × (ℝ × ℝ) → ℝ := fun k p => fderiv ℝ G p ((0 : ℝ), B0579.dir k) with hD
  set DD : Fin 2 → Fin 2 → ℝ × (ℝ × ℝ) → ℝ :=
    fun j k p => fderiv ℝ (D k) p ((0 : ℝ), B0579.dir j) with hDD
  have hDs : ∀ k, ContDiff ℝ ∞ (D k) := fun k => contDiff_D hG _
  have hDDs : ∀ j k, ContDiff ℝ ∞ (DD j k) := fun j k => contDiff_D (hDs k) _
  have hS : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hV : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 i)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn hS
  set W : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    ν * (DD 0 0 p + DD 1 1 p) + (tr.v p.1 p.2 0 * D 0 p + tr.v p.1 p.2 1 * D 1 p) with hW
  have hWs : ContDiffOn ℝ ∞ W (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiffOn_const.mul ((hDDs 0 0).contDiffOn.add (hDDs 1 1).contDiffOn)).add
      (((hV 0).mul (hDs 0).contDiffOn).add ((hV 1).mul (hDs 1).contDiffOn))
  refine (contOn_fd hWs j).congr fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  have e1 : ∀ k, B0579.pd k (η p.1) = fun y => D k (p.1, y) := fun k =>
    funext fun y => pd_slice (F := G) hG.contDiffOn hp1 k y
  have e2 : ∀ j k, B0579.pd j (B0579.pd k (η p.1)) = fun y => DD j k (p.1, y) := fun j k => by
    rw [e1 k]
    exact funext fun y => pd_slice (F := D k) (hDs k).contDiffOn hp1 j y
  have key : vtvFlowTest tr p.1 (η p.1) = fun y => W (p.1, y) := by
    funext y
    simp only [vtvFlowTest, UnforcedLeray.Short.IIIa.lapP]
    rw [e2 0 0, e2 1 1, e1 0, e1 1]
  rw [key]

end VtvYRMeasAux

open VtvYRMeasAux
open UnforcedLeray.Short.IIIa.GlobEAux (contOn_pd_Ec)

/-- Parametric integrals of AE-strongly measurable integrands are AE-strongly measurable. -/
theorem vtv_paramAESM (c s₁ s₂ : ℝ) {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))) :
    AEStronglyMeasurable (fun s => ∫ x in B0579.cell c, F (s, x))
      (volume.restrict (Icc s₁ s₂)) := by
  have h : AEStronglyMeasurable F
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hF
  exact h.integral_prod_right'

theorem vtv_measurableSet_cell (c : ℝ) : MeasurableSet (B0579.cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- An `L²(cell)` function times a continuous function supported in a band is integrable. -/
theorem vtv_integrableOn_mul {c R : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (B0579.cell c)))
    {K : ℝ × ℝ → ℝ} (hK : Continuous K) (hR : ∀ x : ℝ × ℝ, R < |x.2| → K x = 0) :
    IntegrableOn (fun x => u x * (K x : ℂ)) (B0579.cell c) := by
  set C : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R with hC
  have hCc : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hKc : Continuous (fun x => (K x : ℂ)) := Complex.continuous_ofReal.comp hK
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hKc.continuousOn
  have hcellm := vtv_measurableSet_cell c
  have hCm : MeasurableSet C := measurableSet_Icc.prod measurableSet_Icc
  have hfin : IntegrableOn (fun x => u x * (K x : ℂ)) (B0579.cell c ∩ C) := by
    haveI : IsFiniteMeasure (volume.restrict (B0579.cell c ∩ C)) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono inter_subset_right) hCc.measure_lt_top⟩
    have hle : (volume.restrict (B0579.cell c ∩ C)) ≤ volume.restrict (B0579.cell c) :=
      Measure.restrict_mono inter_subset_left le_rfl
    have hu' : MemLp u 2 (volume.restrict (B0579.cell c ∩ C)) := hu.mono_measure hle
    have hu1 : Integrable u (volume.restrict (B0579.cell c ∩ C)) := hu'.integrable one_le_two
    refine Integrable.mono' (hu1.norm.const_mul M) ?_ ?_
    · exact hu'.aestronglyMeasurable.mul hKc.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (hcellm.inter hCm)] with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM x hx.2) (norm_nonneg _)
  refine hfin.of_forall_diff_eq_zero hcellm fun x hx => ?_
  have hx2 : R < |x.2| := by
    by_contra h
    push_neg at h
    exact hx.2 ⟨hx.1, Ico_subset_Icc_self hx.1.1, abs_le.1 h⟩
  simp [hR x hx2]

theorem vtvYRMeas : VtvYRMeas := by
  intro ν c μ tr om g b G f H η hη s₁ s₂ hs₁
  obtain ⟨hν, hc, hBUC, hE, hBS, hf, hcurl, hid, hOm⟩ := H
  have hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => η p.1 p.2) := hη.1
  have hSm : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (vtv_measurableSet_cell c)
  have hSU : Icc s₁ s₂ ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun p hp => ⟨lt_of_lt_of_le hs₁ hp.1.1, mem_univ _⟩
  have aesm_real : ∀ {H : ℝ × (ℝ × ℝ) → ℝ},
      ContinuousOn H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) →
      AEStronglyMeasurable (fun p => (H p : ℂ)) (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) :=
    fun hH => (Complex.continuous_ofReal.comp_continuousOn (hH.mono hSU)).aestronglyMeasurable hSm
  have hb : ∀ i, AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => b p i)
      (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) := fun i =>
    (hE.measurable i).aestronglyMeasurable
  have hfm : ∀ i, AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => f p i)
      (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) := fun i =>
    (hf s₁ s₂ hs₁ i).aestronglyMeasurable
  have hpow : AEStronglyMeasurable (fun s : ℝ => (s : ℂ) ^ (μ : ℂ))
      (volume.restrict (Icc s₁ s₂)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Icc
    refine ContinuousOn.cpow (Complex.continuous_ofReal.continuousOn) continuousOn_const ?_
    intro s hs
    exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le hs₁ hs.1)
  have hae : ∀ {F₁ F₂ : ℝ → ℂ}, (∀ s ∈ Icc s₁ s₂, F₁ s = F₂ s) →
      F₁ =ᵐ[volume.restrict (Icc s₁ s₂)] F₂ := fun h =>
    (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall h)
  constructor
  · -- Y
    have key : ∀ s ∈ Icc s₁ s₂, vtvY μ c om s (fun x => deriv (fun s' => η s' x) s) =
        (s : ℂ) ^ (μ : ℂ) * ∫ x in B0579.cell c,
          (b (s, x) 0 * (B0579.pd 1 (fun x => deriv (fun s' => η s' x) s) x : ℂ) -
            b (s, x) 1 * (B0579.pd 0 (fun x => deriv (fun s' => η s' x) s) x : ℂ)) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
      unfold vtvY
      rw [(hBS s hs0).2.2 _ (vtvDerivCyl c η hη s)]
    have hmeas : AEStronglyMeasurable (fun s : ℝ => (s : ℂ) ^ (μ : ℂ) *
        ∫ x in B0579.cell c,
          (b (s, x) 0 * (B0579.pd 1 (fun x => deriv (fun s' => η s' x) s) x : ℂ) -
            b (s, x) 1 * (B0579.pd 0 (fun x => deriv (fun s' => η s' x) s) x : ℂ)))
        (volume.restrict (Icc s₁ s₂)) := by
      have hP := vtv_paramAESM c s₁ s₂
        (F := fun p : ℝ × (ℝ × ℝ) =>
          b p 0 * (B0579.pd 1 (fun x => deriv (fun s' => η s' x) p.1) p.2 : ℂ) -
            b p 1 * (B0579.pd 0 (fun x => deriv (fun s' => η s' x) p.1) p.2 : ℂ))
        (((hb 0).mul (aesm_real (contOn_dsEta hG 1))).sub
          ((hb 1).mul (aesm_real (contOn_dsEta hG 0))))
      exact hpow.mul hP
    exact hmeas.congr (hae fun s hs => (key s hs).symm)
  · -- R
    obtain ⟨s₁', s₂', R, _, hband⟩ := hη.2.2
    have key : ∀ s ∈ Icc s₁ s₂, vtvR μ tr om g b s (η s) =
        (s : ℂ) ^ (μ : ℂ) * ((∫ x in B0579.cell c,
            (f (s, x) 0 * (B0579.pd 1 (η s) x : ℂ) - f (s, x) 1 * (B0579.pd 0 (η s) x : ℂ))) +
          ((∫ x in B0579.cell c,
            (b (s, x) 0 * (B0579.pd 1 (vtvFlowTest tr s (η s)) x : ℂ) -
              b (s, x) 1 * (B0579.pd 0 (vtvFlowTest tr s (η s)) x : ℂ))) -
           ∫ x in B0579.cell c,
            (b (s, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
              b (s, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) *
              (η s x : ℂ))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
      have hηc : B0579.IsCylTest c (η s) := hη.2.1 s
      have hw := vtvFlowCyl ν c tr s hs0 (η s) hηc
      have hint1 := hOm s hs0 _ hw
      have hcont : ∀ i : Fin 2, Continuous (fun x : ℝ × ℝ =>
          B0579.pd i (UnforcedLeray.B0238.Ec tr s) x * η s x) := fun i =>
        (((contOn_pd_Ec tr i).comp_continuous
          (continuous_const.prodMk continuous_id) (fun x => ⟨hs0, mem_univ _⟩)).mul
            hηc.continuous)
      have hvan : ∀ i : Fin 2, ∀ x : ℝ × ℝ, R < |x.2| →
          B0579.pd i (UnforcedLeray.B0238.Ec tr s) x * η s x = 0 := fun i x hx => by
        rw [hband s x (Or.inr (Or.inr hx)), mul_zero]
      have hI : ∀ i : Fin 2, IntegrableOn (fun x : ℝ × ℝ => b (s, x) i *
          ((B0579.pd i (UnforcedLeray.B0238.Ec tr s) x * η s x : ℝ) : ℂ))
          (B0579.cell c) := fun i =>
        vtv_integrableOn_mul ((hBS s hs0).1 i) (hcont i) (hvan i)
      have hint2 : IntegrableOn (fun x : ℝ × ℝ =>
          (b (s, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
            b (s, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) *
              (η s x : ℂ)) (B0579.cell c) := by
        refine ((hI 0).add (hI 1)).congr_fun (fun x _ => ?_) (vtv_measurableSet_cell c)
        simp only [Pi.add_apply]
        push_cast
        ring
      have hsplit : ∫ x in B0579.cell c,
          UnforcedLeray.Short.IIIa.flowIntegrand tr (om s) (fun x => b (s, x)) s (η s) x =
          (∫ x in B0579.cell c, om s x * ((vtvFlowTest tr s (η s) x : ℝ) : ℂ)) -
            ∫ x in B0579.cell c,
              (b (s, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
                b (s, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) *
                (η s x : ℂ) := integral_sub hint1 hint2
      unfold vtvR
      rw [hcurl s hs0 (η s) hηc, hsplit, (hBS s hs0).2.2 _ hw]
    have hmeas : AEStronglyMeasurable (fun s : ℝ => (s : ℂ) ^ (μ : ℂ) *
        ((∫ x in B0579.cell c,
            (f (s, x) 0 * (B0579.pd 1 (η s) x : ℂ) - f (s, x) 1 * (B0579.pd 0 (η s) x : ℂ))) +
          ((∫ x in B0579.cell c,
            (b (s, x) 0 * (B0579.pd 1 (vtvFlowTest tr s (η s)) x : ℂ) -
              b (s, x) 1 * (B0579.pd 0 (vtvFlowTest tr s (η s)) x : ℂ))) -
           ∫ x in B0579.cell c,
            (b (s, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
              b (s, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) *
              (η s x : ℂ))))
        (volume.restrict (Icc s₁ s₂)) := by
      have hP1 := vtv_paramAESM c s₁ s₂
        (F := fun p : ℝ × (ℝ × ℝ) =>
          f p 0 * (B0579.pd 1 (η p.1) p.2 : ℂ) - f p 1 * (B0579.pd 0 (η p.1) p.2 : ℂ))
        (((hfm 0).mul (aesm_real (contOn_Eta hG 1))).sub
          ((hfm 1).mul (aesm_real (contOn_Eta hG 0))))
      have hP2 := vtv_paramAESM c s₁ s₂
        (F := fun p : ℝ × (ℝ × ℝ) =>
          b p 0 * (B0579.pd 1 (vtvFlowTest tr p.1 (η p.1)) p.2 : ℂ) -
            b p 1 * (B0579.pd 0 (vtvFlowTest tr p.1 (η p.1)) p.2 : ℂ))
        (((hb 0).mul (aesm_real (contOn_flow tr hG 1))).sub
          ((hb 1).mul (aesm_real (contOn_flow tr hG 0))))
      have hEc : ∀ i, AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) =>
          ((B0579.pd i (UnforcedLeray.B0238.Ec tr p.1) p.2 : ℝ) : ℂ))
          (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) := fun i =>
        aesm_real (contOn_pd_Ec tr i)
      have hη' : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => ((η p.1 p.2 : ℝ) : ℂ))
          (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) :=
        aesm_real hG.continuous.continuousOn
      have hP3 := vtv_paramAESM c s₁ s₂
        (F := fun p : ℝ × (ℝ × ℝ) =>
          (b p 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr p.1) p.2 : ℝ) : ℂ) +
            b p 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr p.1) p.2 : ℝ) : ℂ)) *
              ((η p.1 p.2 : ℝ) : ℂ))
        ((((hb 0).mul (hEc 0)).add ((hb 1).mul (hEc 1))).mul hη')
      exact hpow.mul (hP1.add (hP2.sub hP3))
    exact hmeas.congr (hae fun s hs => (key s hs).symm)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
