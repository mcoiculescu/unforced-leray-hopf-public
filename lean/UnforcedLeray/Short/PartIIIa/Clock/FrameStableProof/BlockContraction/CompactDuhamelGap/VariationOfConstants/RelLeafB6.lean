import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelRegularityOrg
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.JointMeas2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.LpMeas
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.HeatDecomp
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# `PartIII-a:T21/c3/2/1/2/2/4`: leaf `RelB6` of `RelRegularityOrg`

Source of record: `the November 2 reference manuscript` (SP), lines 2974-2978.

* `relB6b_leaf`: smooth compactly supported representatives are dense in `Planar.L2w m`.
  Mathlib gives density of `C_c^∞` representatives in `Lp ℂ 2 μ` for `μ` locally finite on `ℂ`;
  composing with the real-linear homeomorphism `ℂ ≃ ℝ × ℝ` gives `Φ` on `ℝ × ℝ`.
* `relB6a_leaf`: for `W` with a smooth compactly supported representative `Φ`, `τ ↦ A_rel τ W` is
  a.e. strongly measurable on `[0, B]`.  The pin `IsDampedComplBlockInt` identifies
  `A_rel τ W` with `cellZeroExt d(r) (movDampedComplInt κ P tr r Φ)`, `r = ageAt ν t₁ τ`; this is
  jointly measurable in `(τ, z)` (`RelIntA.measurable_movDampedComplInt_joint`), and a jointly
  measurable representative gives strong measurability of the `L²`-valued map
  (`RelIntA.stronglyMeasurable_Lp_of_jointly`).  The ingredients of the joint measurability need
  `d(r) ≥ 1` (from `b ≥ 1`), `det G(d(r)) ≠ 0` (from `PerFrameFacts`) and the explicit moving heat
  formula `HeatFormula κ ν r`, proved here for every age with invertible Gram matrix
  (`relB6_heatFormula_of_det`; the drafted `heatFormula_of` needed `d(r)` large).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa
namespace RelRegularityOrg

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub.OrgSplit
  BlockPropagatorInteriorSub.OrgSplit.RelIntA ComplFreeRateSub.Leaf4Aux

theorem relB6b_leaf : RelB6b := by
  intro m hm
  have hloc : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (UnforcedLeray.B0008.wMeasure m))
  have hD : Dense {f : Planar.L2w m | ∃ g : ℂ → ℂ, ⇑f =ᵐ[Planar.wMeasure m] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (μ := Planar.wMeasure m) (E := ℂ) (F := ℂ)
      (p := 2) (by norm_num)
  refine Dense.mono ?_ hD
  rintro W ⟨g, hWg, hgc, hgs⟩
  let e : (ℝ × ℝ) ≃L[ℝ] ℂ := Complex.equivRealProdCLM.symm
  refine ⟨fun p => g (e p), hgs.comp e.contDiff, hgc.comp_homeomorph e.toHomeomorph, ?_⟩
  have hae : ⇑W =ᵐ[volume] g := (Planar.volume_ac m).ae_le hWg
  refine hae.trans (Filter.Eventually.of_forall fun z => ?_)
  congr 1

/-- Entries of the inverse of the `2 × 2` Gram matrix are differentiable in the cell length
wherever the Gram entries are and the determinant does not vanish. -/
theorem relB6_hasDerivAt_perGram_inv {κ : PlanarFrameKernels} {d : ℝ}
    {g : Fin 2 → Fin 2 → ℂ}
    (hG : ∀ p q : Fin 2, HasDerivAt (fun d' => perGram κ d' p q) (g p q) d)
    (hdet : (perGram κ d).det ≠ 0) (i j : Fin 2) :
    ∃ g' : ℂ, HasDerivAt (fun d' => (perGram κ d')⁻¹ i j) g' d := by
  have hfun : (fun d' => (perGram κ d')⁻¹ i j) =
      fun d' => ((perGram κ d').det)⁻¹ * (perGram κ d').adjugate i j := by
    funext d'
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  have hD : ∀ p q : Fin 2, DifferentiableAt ℝ (fun d' => perGram κ d' p q) d :=
    fun p q => (hG p q).differentiableAt
  have hdetD : DifferentiableAt ℝ (fun d' => (perGram κ d').det) d := by
    simp only [Matrix.det_fin_two]
    exact ((hD 0 0).mul (hD 1 1)).sub ((hD 0 1).mul (hD 1 0))
  have hadjD : DifferentiableAt ℝ (fun d' => (perGram κ d').adjugate i j) d := by
    simp only [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hD 1 1
    · exact (hD 0 1).neg
    · exact (hD 1 0).neg
    · exact hD 0 0
  have hdiff : DifferentiableAt ℝ (fun d' => (perGram κ d')⁻¹ i j) d := by
    rw [hfun]
    exact (hdetD.inv hdet).mul hadjD
  exact ⟨_, hdiff.hasDerivAt⟩

/-- The explicit moving heat formula `HeatFormula κ ν r` at every age whose Gram matrix is
invertible (the derivative of the Gram inverse exists there; SP 2905-2912). -/
theorem relB6_heatFormula_of_det (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r)
    (hdet : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0) :
    HeatFormula κ ν r := by
  obtain ⟨hCD, C, _hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨C_G, _hCG, hGd⟩ := ComplCouplingHeat.hasDerivAt_perGram_and_bound κ hCD h1
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hd0 : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha)
  intro i y
  have hinv : ∀ j : Fin 2, ∃ g' : ℂ, HasDerivAt (fun d' => (perGram κ d')⁻¹ i j) g'
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) :=
    fun j => relB6_hasDerivAt_perGram_inv (fun p q => (hGd hd0 p q).1) hdet i j
  choose g' hg' using hinv
  have hG_ex : ∀ j : Fin 2, ∃ G' : ℂ, HasDerivWithinAt
      (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j) G' (Ici r) r :=
    fun j => ⟨_, (DirectHeatDecomp.hasDerivAt_perGram_inv_comp_cellLen κ hν hr i j
      (hg' j)).hasDerivWithinAt⟩
  choose G_inv' hG_der using hG_ex
  have ht := fun j => ComplCouplingHeat.translate_jet2_bounds (h0 j) (h1 j) (h2 j)
  have h := ComplCouplingHeat.movLamDualHeat_split_of κ hν hr i hCD (fun j => (ht j).1)
    (fun j => (ht j).2.1) (fun j => (ht j).2.2) hG_der y
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hG_der j).derivWithin (uniqueDiffWithinAt_Ici r)]

/-- `RelB6a` (SP 2974-2978): strong measurability on `[0, B]` of `τ ↦ A_rel τ W` for `W` with a
smooth compactly supported representative. -/
theorem relB6a_leaf (κ : PlanarFrameKernels) : RelB6a κ := by
  intro P m K B b ν tr t₁ t₂ ctx A_rel hA W hW
  obtain ⟨hκ, _hP, _hm, hB, hb, hν, hF, _htr, ht₁, h12, hbt, hBdef⟩ := ctx
  obtain ⟨Φ, hΦs, hΦc, hWΦ⟩ := hW
  have hr0 : ∀ r ∈ Icc t₁ t₂, 0 ≤ r := fun r hr => ht₁.trans hr.1
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt.trans (theta_anti hν (hr0 r hr) hr.2)
  have hν1 : ν ≤ 1 := by
    have ht₂ : 0 ≤ t₂ := ht₁.trans h12
    have h1 : 1 ≤ clockTheta ν t₂ := hb.trans hbt
    have h3 : 1 ≤ clockA ν t₂ := one_le_clockA hν.le ht₂
    have hpos : 0 < ν * clockA ν t₂ := mul_pos hν (lt_of_lt_of_le zero_lt_one h3)
    unfold clockTheta at h1
    have h2 : ν * clockA ν t₂ ≤ 1 := (one_le_inv₀ hpos).1 h1
    nlinarith
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    le_cellLen_of hν hν1 (hr0 r hr) zero_le_one (by rw [one_pow]; exact hb) (hbr r hr)
  have hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
    intro r hr h0
    have h := hF.1 r (hr0 r hr) (hbr r hr) 0 0
    have hinv : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero, not_not]; exact h0)
    have hz : ∀ x, perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 x = 0 := fun x => by
      unfold perLam
      rw [hinv]
      simp
    simp only [hz, zero_mul, integral_zero] at h
    exact zero_ne_one h
  have hform : ∀ r ∈ Icc t₁ t₂, HeatFormula κ ν r := fun r hr =>
    relB6_heatFormula_of_det κ hκ hν (hr0 r hr) (hdet r hr)
  -- the clamped age along the block
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ → ℝ, ρ = fun τ => ageAt ν t₁ (clampB B τ) := ⟨_, rfl⟩
  have hρ : ∀ τ, ρ τ ∈ Icc t₁ t₂ := fun τ => by
    rw [hρdef]
    exact VariationOfConstantsSub.ageAt_mem_Icc hν ht₁ h12 hBdef
      ⟨clampB_nonneg _ _, clampB_le B τ hB.le⟩
  have hρm : Measurable ρ := by
    rw [hρdef]
    unfold ageAt FrameStableSub.moveAgeOfZ clampB
    fun_prop
  have hΦm : Measurable Φ := hΦs.continuous.measurable
  have : SFinite (Planar.wMeasure m) := by
    unfold Planar.wMeasure
    infer_instance
  have hG := measurable_cellZeroExt_joint (dRho ν t₁ t₂) (continuous_dRho hν ht₁).measurable
    (fun r => movDampedComplInt κ P tr (rho t₁ t₂ r) Φ)
    (measurable_movDampedComplInt_joint hκ P hν ht₁ h12 hd1 hdet hform tr hΦm)
  have hmap : Measurable (fun p : ℝ × ℂ => ((ρ p.1, cToPlane p.2) : ℝ × (ℝ × ℝ))) :=
    (hρm.comp measurable_fst).prodMk (measurable_cToPlane.comp measurable_snd)
  have heq : Function.uncurry (fun (τ : ℝ) (z : ℂ) =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ρ τ)))
          (movDampedComplInt κ P tr (ρ τ) Φ) (cToPlane z)) =
      (fun q : ℝ × (ℝ × ℝ) => cellZeroExt (dRho ν t₁ t₂ q.1)
        (movDampedComplInt κ P tr (rho t₁ t₂ q.1) Φ) q.2) ∘
      (fun p : ℝ × ℂ => ((ρ p.1, cToPlane p.2) : ℝ × (ℝ × ℝ))) := by
    funext p
    show cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ρ p.1)))
        (movDampedComplInt κ P tr (ρ p.1) Φ) (cToPlane p.2) =
      cellZeroExt (dRho ν t₁ t₂ (ρ p.1))
        (movDampedComplInt κ P tr (rho t₁ t₂ (ρ p.1)) Φ) (cToPlane p.2)
    unfold dRho
    rw [rho_eq (hρ p.1)]
  have hFm : Measurable (Function.uncurry (fun (τ : ℝ) (z : ℂ) =>
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ρ τ)))
        (movDampedComplInt κ P tr (ρ τ) Φ) (cToPlane z))) := by
    rw [heq]
    exact hG.comp hmap
  have hrep : ∀ τ : ℝ, ((A_rel (clampB B τ) W : Planar.L2w m) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      (fun z : ℂ => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ρ τ)))
        (movDampedComplInt κ P tr (ρ τ) Φ) (cToPlane z)) := by
    intro τ
    have hτ : clampB B τ ∈ Icc (0 : ℝ) B := ⟨clampB_nonneg _ _, clampB_le B τ hB.le⟩
    have h := hA (clampB B τ) hτ Φ hΦs hΦc W hWΦ
    have hρτ : ρ τ = ageAt ν t₁ (clampB B τ) := by rw [hρdef]
    rw [hρτ]
    exact (Planar.wMeasure_ac m).ae_le h
  have hSM := stronglyMeasurable_Lp_of_jointly
    (fun (τ : ℝ) (z : ℂ) => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ρ τ)))
      (movDampedComplInt κ P tr (ρ τ) Φ) (cToPlane z)) hFm
    (fun τ => A_rel (clampB B τ) W) hrep
  refine hSM.aestronglyMeasurable.congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun τ hτ => ?_
  have hclamp : clampB B τ = τ := by
    unfold clampB
    rw [min_eq_left hτ.2, max_eq_right hτ.1]
  simp only [hclamp]

/-- **Leaf `RelB6`** (`PartIII-a:T21/c3/2/1/2/2/4`). -/
theorem relB6_leaf (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.RelRegularityOrg.RelB6 κ :=
  ⟨relB6a_leaf κ, relB6b_leaf⟩

end RelRegularityOrg
end UnforcedLeray.Short.IIIa
