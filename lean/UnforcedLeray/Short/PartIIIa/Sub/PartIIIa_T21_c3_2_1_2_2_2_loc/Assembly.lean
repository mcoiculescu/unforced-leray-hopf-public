import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.CylJoint
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.Ident
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.Dense

/-!
# Assembly of the local dense continuity of `F_rel` (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2941-2970.  On the dense class of
smooth compactly supported real fields vanishing near the boundary lines of the cell `d(s₀)`, the
pinned relative free evolution is, near `p₀`,
`F_rel(τ,σ) W = N(s,t)⁻¹ (J_{1/a_t} ⟦ω_s(t)⟧ + J_{(d_t/d_s)^2} E)`, with `ω_s` the free cylinder flow
from the rescaled cell restriction of `W` at the start age `s` and `E` the fixed exterior field.
Each factor is continuous: the clocks, the joint dilation (`tendsto_dilW'_joint`), and the free
cylinder flow in (start age, time) (`cyl_joint_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.RelB4locAux

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsMildSub
open UnforcedLeray.Blueprint.Planar

/-! ## Clocks -/

theorem ageAt_props {ν t₁ t₂ B : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂)
    (hBz : movingZ ν t₂ - movingZ ν t₁ = B) {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτ : τ ≤ B) :
    t₁ ≤ ageAt ν t₁ σ ∧ ageAt ν t₁ σ ≤ ageAt ν t₁ τ ∧ ageAt ν t₁ τ ≤ t₂ := by
  have hz1 : 0 ≤ movingZ ν t₁ := FrameStableSub.movingZ_nonneg hν ht₁
  have hlt : ν * movingZ ν t₂ < 1 := FrameStableSub.nu_mul_movingZ_lt_one hν (ht₁.trans ht₁₂)
  have hzB : ν * (movingZ ν t₁ + B) < 1 := by rw [← hBz]; simpa using hlt
  have hzτ : ν * (movingZ ν t₁ + τ) < 1 := by nlinarith
  have hzσ : ν * (movingZ ν t₁ + σ) < 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h := FrameStableSub.moveAgeOfZ_mono hν (by linarith : 0 ≤ movingZ ν t₁ + 0) hzσ
      (by linarith : movingZ ν t₁ + 0 ≤ movingZ ν t₁ + σ)
    rw [show FrameStableSub.moveAgeOfZ ν (movingZ ν t₁ + 0) = ageAt ν t₁ 0 from rfl,
      ageAt_zero hν ht₁] at h
    exact h
  · exact FrameStableSub.moveAgeOfZ_mono hν (by linarith) hzτ (by linarith)
  · have h := FrameStableSub.moveAgeOfZ_mono hν (by linarith : 0 ≤ movingZ ν t₁ + τ) hzB
      (by linarith : movingZ ν t₁ + τ ≤ movingZ ν t₁ + B)
    rw [show FrameStableSub.moveAgeOfZ ν (movingZ ν t₁ + B) = ageAt ν t₁ B from rfl,
      ageAt_eq_of_movingZ_sub hν (ht₁.trans ht₁₂) hBz] at h
    exact h

theorem continuousAt_ageAt {ν t₁ τ : ℝ} (h : ν * (movingZ ν t₁ + τ) < 1) :
    ContinuousAt (ageAt ν t₁) τ := by
  unfold ageAt FrameStableSub.moveAgeOfZ
  exact (continuousAt_const.add continuousAt_id).div
    (continuousAt_const.sub (continuousAt_const.mul (continuousAt_const.add continuousAt_id)))
    (by linarith)

theorem continuousAt_clockN_comp {X : Type*} [TopologicalSpace X] (P : PlanarData) {ν : ℝ}
    (hν : 0 < ν) {u v : X → ℝ} {x : X} (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hu0 : 0 ≤ u x) (hv0 : 0 ≤ v x) :
    ContinuousAt (fun y => clockN P ν (u y) (v y)) x := by
  have hθ : ∀ {w : X → ℝ}, ContinuousAt w x → 0 ≤ w x →
      ContinuousAt (fun y => clockTheta ν (w y)) x ∧ 0 < clockTheta ν (w x) := by
    intro w hw hw0
    have hpos : 0 < ν * (1 + ν * w x) := by positivity
    refine ⟨?_, by unfold clockTheta clockA; positivity⟩
    unfold clockTheta clockA
    exact (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul hw))).inv₀
      hpos.ne'
  obtain ⟨hθu, hθu0⟩ := hθ hu hu0
  obtain ⟨hθv, hθv0⟩ := hθ hv hv0
  unfold clockN
  exact (continuousAt_const.mul (hθu.sub hθv)).rexp.mul
    ((hθu.div hθv hθv0.ne').rpow_const (Or.inl (div_pos hθu0 hθv0).ne'))

theorem clockN_pos (P : PlanarData) {ν s t : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < clockN P ν s t := by
  have h1 : 0 < clockTheta ν s := by unfold clockTheta clockA; positivity
  have h2 : 0 < clockTheta ν t := by unfold clockTheta clockA; positivity
  unfold clockN
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (div_pos h1 h2) _)

theorem continuousAt_cellLen_comp {X : Type*} [TopologicalSpace X] {c ν : ℝ} {u : X → ℝ}
    {x : X} (hu : ContinuousAt u x) (hpos : 0 < clockA ν (u x)) :
    ContinuousAt (fun y => cellLen c (clockA ν (u y))) x := by
  unfold cellLen clockA
  unfold clockA at hpos
  exact continuousAt_const.div
    (Real.continuous_sqrt.continuousAt.comp (continuousAt_const.add (continuousAt_const.mul hu)))
    (Real.sqrt_pos.2 hpos).ne'

/-! ## The exterior field and the identification -/

/-- The field `Φ` outside the cell `d₀`. -/
def eFun (d₀ : ℝ) (Φr : ℂ → ℝ) : ℂ → ℂ :=
  (cToPlane ⁻¹' B0579.cell d₀)ᶜ.indicator (fun z => ((Φr z : ℝ) : ℂ))

theorem memLp_eFun {m d₀ : ℝ} {Φr : ℂ → ℝ} (h : MemLp (fun z => ((Φr z : ℝ) : ℂ)) 2 (Planar.wMeasure m)) :
    MemLp (eFun d₀ Φr) 2 (Planar.wMeasure m) :=
  h.indicator (measurable_cToPlane (B0579.measurableSet_cell d₀)).compl

theorem cell_agree {d d₀ δ : ℝ} (hδ : 0 < δ) (hd : |d - d₀| < δ / 2) {Φr : ℂ → ℝ}
    (hv : ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φr z = 0) {w : ℂ}
    (hw : Φr w ≠ 0) : cToPlane w ∈ B0579.cell d ↔ cToPlane w ∈ B0579.cell d₀ := by
  have hd' := abs_lt.1 hd
  have hre : ¬ (d₀ / 2 - δ < |w.re| ∧ |w.re| < d₀ / 2 + δ) := fun h => hw (hv w h.1 h.2)
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, cToPlane]
  rcases le_or_gt |w.re| (d₀ / 2 - δ) with h1 | h1
  · have h1' := abs_le.1 h1
    exact ⟨fun _ => ⟨by linarith, by linarith⟩, fun _ => ⟨by linarith, by linarith⟩⟩
  · have h2 : d₀ / 2 + δ ≤ |w.re| := by
      by_contra h; exact hre ⟨h1, lt_of_not_ge h⟩
    rcases le_or_gt 0 w.re with h3 | h3
    · rw [abs_of_nonneg h3] at h2
      exact ⟨fun h => absurd h.2 (by linarith), fun h => absurd h.2 (by linarith)⟩
    · rw [abs_of_neg h3] at h2
      exact ⟨fun h => absurd h.1 (by linarith), fun h => absurd h.1 (by linarith)⟩

/-- Identification of the pinned value with the planar dilation expression. -/
theorem ident_eq {m c d₀ δ : ℝ} (hm1 : 1 < m) (hc : 0 < c) {a_s a_t N : ℝ} (has : 0 < a_s)
    (hat : 0 < a_t) (hδ : 0 < δ) (hd : |cellLen c a_s - d₀| < δ / 2) {Φr : ℂ → ℝ}
    (hv : ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φr z = 0)
    (W : Planar.L2w m) (hW : ⇑W =ᵐ[Planar.wMeasure m] fun z => ((Φr z : ℝ) : ℂ))
    (wf : ℝ × ℝ → ℝ) (hwf : MemLp wf 2 (B0579.cellMeasure c m))
    (E : Planar.L2w m) (hE : ⇑E =ᵐ[Planar.wMeasure m] eFun d₀ Φr) (V : Planar.L2w m)
    (hV : ⇑V =ᵐ[volume] fun z => ((N : ℂ)⁻¹) * periodizedExt (cellLen c a_s) (cellLen c a_t)
      (JscaleInv a_t (fun x => ((wf x : ℝ) : ℂ))) (fun y => (W : ℂ → ℂ) (planeToC y))
      (cToPlane z)) :
    V = ((N : ℂ)⁻¹) • (dilW' hm1 a_t⁻¹ (liftC c m wf) +
      dilW' hm1 ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹ E) := by
  have hds : 0 < cellLen c a_s := div_pos hc (Real.sqrt_pos.2 has)
  have hdt : 0 < cellLen c a_t := div_pos hc (Real.sqrt_pos.2 hat)
  have hα : 0 < a_t⁻¹ := inv_pos.2 hat
  have hβ : 0 < ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹ := by positivity
  rw [dilW'_of_pos hm1 hα, dilW'_of_pos hm1 hβ]
  have heS : (fun w => (W : ℂ → ℂ) w -
      cellZeroExt (cellLen c a_s) (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane w))
        =ᵐ[Planar.wMeasure m] eFun d₀ Φr := by
    filter_upwards [hW] with w hw
    simp only [cellZeroExt, eFun, hw]
    by_cases h0 : Φr w = 0
    · have hE0 : (cToPlane ⁻¹' B0579.cell d₀)ᶜ.indicator (fun z => ((Φr z : ℝ) : ℂ)) w = 0 :=
        Set.indicator_apply_eq_zero.2 (fun _ => by simp [h0])
      rw [hE0]
      by_cases hin : cToPlane w ∈ B0579.cell (cellLen c a_s)
      · rw [indicator_of_mem hin]; simp [planeToC_cToPlane, hw, h0]
      · rw [indicator_of_notMem hin]; simp [h0]
    · have hag := cell_agree hδ hd hv h0
      by_cases hin : cToPlane w ∈ B0579.cell d₀
      · rw [indicator_of_mem (hag.2 hin),
          indicator_of_notMem (show w ∉ (cToPlane ⁻¹' B0579.cell d₀)ᶜ from fun h => h hin)]
        simp [planeToC_cToPlane, hw]
      · rw [indicator_of_notMem (fun h => hin (hag.1 h)),
          indicator_of_mem (show w ∈ (cToPlane ⁻¹' B0579.cell d₀)ᶜ from hin)]
        simp
  apply Lp.ext
  filter_upwards [(Planar.wMeasure_ac m).ae_le hV,
    Lp.coeFn_smul ((N : ℂ)⁻¹) (Planar.dilW hm1 hα (liftC c m wf) + Planar.dilW hm1 hβ E),
    Lp.coeFn_add (Planar.dilW hm1 hα (liftC c m wf)) (Planar.dilW hm1 hβ E),
    Planar.coeFn_dilW hm1 hα (liftC c m wf), Planar.coeFn_dilW hm1 hβ E,
    Planar.dilWFun_congr hα (coeFn_liftC hwf), Planar.dilWFun_congr hβ hE,
    Planar.dilWFun_congr hβ heS] with z h1 h2 h3 h4 h5 h6 h7 h8
  have h4' : (Planar.dilW hm1 hα (liftC c m wf) : ℂ → ℂ) z =
      Planar.dilWFun a_t⁻¹ (liftFun c wf) z := h4.trans h6
  have h5' : (Planar.dilW hm1 hβ E : ℂ → ℂ) z =
      Planar.dilWFun ((cellLen c a_s / cellLen c a_t) ^ 2)⁻¹ (eFun d₀ Φr) z := h5.trans h7
  rw [h1, h2, Pi.smul_apply, h3, Pi.add_apply, h4', h5', smul_eq_mul]
  congr 1
  simp only [periodizedExt]
  rw [cellZeroExt_JscaleInv_eq hc hat wf z, extDil_eq_dilWFun hds hdt (W : ℂ → ℂ) z, h8]

/-- `X_{m,c}` convergence of the rescaled data from the strong continuity of the dilations. -/
theorem fData_tendsto {m c : ℝ} (hm1 : 1 < m) (hc : 0 < c) {Φr : ℂ → ℝ} (W : Planar.L2w m)
    (hW : ⇑W =ᵐ[Planar.wMeasure m] fun z => ((Φr z : ℝ) : ℂ)) {a₀ : ℝ} (ha₀ : 0 < a₀)
    {ι : Type*} {l : Filter ι} {a : ι → ℝ} (ha : Tendsto a l (𝓝 a₀))
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fData c Φr (a i) - fData c Φr a₀)
      (B0579.cellMeasure c m)) :
    Tendsto (fun i => eLpNorm (fData c Φr (a i) - fData c Φr a₀) 2 (B0579.cellMeasure c m)) l
      (𝓝 0) := by
  have hpos : ∀ᶠ i in l, 0 < a i := ha.eventually (Ioi_mem_nhds ha₀)
  have hD : Tendsto (fun i => ENNReal.ofReal ‖dilW' hm1 (a i) W - dilW' hm1 a₀ W‖) l (𝓝 0) := by
    have h := tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_dilW' hm1 W ha₀).comp ha)
    have h' := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rwa [ENNReal.ofReal_zero] at h'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hpos, hmeas] with i hi hm'
  rw [← eLpNorm_liftFun hm']
  have hae : ⇑(dilW' hm1 (a i) W - dilW' hm1 a₀ W) =ᵐ[Planar.wMeasure m]
      fun z => Planar.dilWFun (a i) (fun w => ((Φr w : ℝ) : ℂ)) z -
        Planar.dilWFun a₀ (fun w => ((Φr w : ℝ) : ℂ)) z := by
    rw [dilW'_of_pos hm1 hi, dilW'_of_pos hm1 ha₀]
    filter_upwards [Lp.coeFn_sub (Planar.dilW hm1 hi W) (Planar.dilW hm1 ha₀ W),
      Planar.coeFn_dilW hm1 hi W, Planar.coeFn_dilW hm1 ha₀ W, Planar.dilWFun_congr hi hW,
      Planar.dilWFun_congr ha₀ hW] with z h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, h3]
    exact congrArg₂ (· - ·) h4 h5
  calc eLpNorm (liftFun c (fData c Φr (a i) - fData c Φr a₀)) 2 (Planar.wMeasure m)
      ≤ eLpNorm (fun z => Planar.dilWFun (a i) (fun w => ((Φr w : ℝ) : ℂ)) z -
          Planar.dilWFun a₀ (fun w => ((Φr w : ℝ) : ℂ)) z) 2 (Planar.wMeasure m) :=
        eLpNorm_mono (fun z => norm_liftFun_fData_sub_le hc Φr (a i) a₀ z)
    _ = eLpNorm ⇑(dilW' hm1 (a i) W - dilW' hm1 a₀ W) 2 (Planar.wMeasure m) :=
        (eLpNorm_congr_ae hae).symm
    _ = ENNReal.ofReal ‖dilW' hm1 (a i) W - dilW' hm1 a₀ W‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

end UnforcedLeray.Short.IIIa.RelB4locAux
