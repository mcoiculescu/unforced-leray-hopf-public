import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiMajRotInv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PsiMajPeriodic

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4/2`: measurability, rotation invariance and periodicity of `Ψ_s`

Source `the November 2 reference manuscript` 4178-4186, 5585-5593.
The stream kernel `ϱ(y)^{-2}(ϱ(y)² + (y₂ - λz₂)²)^{-1}` depends on `y` only through `ϱ(y)` and `y₂`,
and on `z` through the gap `ϱ z < θϱ y` and the source weight; the source weight is periodic in
the phase.  Proves `PsiSMeasurable`, `PsiSRotInv`, `PsiSPeriodic` and hence `psiSProps`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore (srcW omega2 ybin)

/-- Generic measurability of the stream kernel `ofReal((a² (a² + (b - c)²))⁻¹)`. -/
theorem psiS_kernel_gen {α : Type*} [MeasurableSpace α] (a b c : α → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun x => ENNReal.ofReal ((a x ^ 2 * (a x ^ 2 + (b x - c x) ^ 2))⁻¹)) := by
  have hden : Measurable (fun x => a x ^ 2 * (a x ^ 2 + (b x - c x) ^ 2)) :=
    (ha.pow_const 2).mul ((ha.pow_const 2).add ((hb.sub hc).pow_const 2))
  exact ENNReal.measurable_ofReal.comp hden.inv

/-- The integrand of `Ψ_s` as one measurable function of `(((τ, y), l), z)`. -/
theorem psiS_integrand_measurable (R c θ : ℝ) (G : Chart → ℝ≥0∞) (hG : Measurable G) :
    Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      if ϱ q.2 < θ * ϱ q.1.1.2 then
        ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹) *
          srcW R c G (q.1.1.1 + 2 * Real.log q.1.2) q.2
      else 0) := by
  have hy : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hl : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hz : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.2) := measurable_snd
  have ha : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => ϱ q.1.1.2) :=
    measurable_ϱ.comp hy
  have hb : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.2 2) :=
    (measurable_coord 2).comp hy
  have hc : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.2 * q.2 2) :=
    hl.mul ((measurable_coord 2).comp hz)
  have hK : Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹)) :=
    psiS_kernel_gen _ _ _ ha hb hc
  have h1 : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.1 + 2 * Real.log q.1.2) := by
    have a1 : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    have a2 : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => 2 * Real.log q.1.2) :=
      measurable_const.mul (Real.measurable_log.comp (measurable_snd.comp measurable_fst))
    exact a1.add a2
  have hφ : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
    h1.prodMk measurable_snd
  have hs : Measurable (fun a : ℝ × Space => srcW R c G a.1 a.2) := WYCore.measurable_srcW R c hG
  have hSN : Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      srcW R c G (q.1.1.1 + 2 * Real.log q.1.2) q.2) := by
    have hcomp := hs.comp hφ
    exact hcomp
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_lt (measurable_ϱ.comp measurable_snd)
      (measurable_const.mul (measurable_ϱ.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  · exact hK.mul hSN
  · exact measurable_const

/-- **`PsiSMeasurable`**: joint measurability of `Ψ_s` in `(τ, y)`. -/
theorem psiSMeasurable : PsiSMeasurable := by
  intro R c θ G hG
  obtain ⟨H, hHdef⟩ : ∃ H : ((ℝ × Space) × ℝ) × Space → ℝ≥0∞, H = fun q =>
      if ϱ q.2 < θ * ϱ q.1.1.2 then
        ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹) *
          srcW R c G (q.1.1.1 + 2 * Real.log q.1.2) q.2
      else 0 := ⟨_, rfl⟩
  have hH : Measurable H := by
    rw [hHdef]
    exact psiS_integrand_measurable R c θ G hG
  have hS : ∀ x : ℝ × Space, MeasurableSet {z : Space | ϱ z < θ * ϱ x.2} :=
    fun x => measurableSet_lt measurable_ϱ measurable_const
  have hfun : (fun x : ℝ × Space => psiMajS R c θ G x.1 x.2) =
      fun x => ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, H ((x, l), z) := by
    funext x
    unfold psiMajS
    refine lintegral_congr fun l => ?_
    rw [← lintegral_indicator (hS x)]
    refine lintegral_congr fun z => ?_
    simp [hHdef, Set.indicator_apply]
  show Measurable (fun x : ℝ × Space => psiMajS R c θ G x.1 x.2)
  rw [hfun]
  have g1 : Measurable (fun a : (ℝ × Space) × ℝ => ∫⁻ z, H (a, z)) :=
    hH.lintegral_prod_right'
  exact g1.lintegral_prod_right'

/-- **`PsiSRotInv`**: `Ψ_s` is invariant under rotation about the vertical axis. -/
theorem psiSRotInv : PsiSRotInv := by
  intro R c θ G α τ y
  have hfix : FixesAxis (Axi.rotZ α) := fixesAxis_rotZ α
  have hϱ : ∀ w : Space, ϱ (Axi.rotZ α w) = ϱ w := fun w => ϱ_map hfix w
  have h2 : ∀ w : Space, (Axi.rotZ α w) 2 = w 2 := fun w => apply_two_map hfix w
  have hemb : MeasurableEmbedding (⇑(Axi.rotZ α)) :=
    (Axi.rotZ α).toHomeomorph.measurableEmbedding
  have hmp : MeasurePreserving (⇑(Axi.rotZ α)) := (Axi.rotZ α).measurePreserving
  have hsrc : ∀ (σ : ℝ) (z : Space), srcW R c G σ (Axi.rotZ α z) = srcW R c G σ z := by
    intro σ z
    have hR : NearInst.hRad (Axi.rotZ α z) = NearInst.hRad z := hϱ z
    have hc : NearInst.chartOf R c (Axi.rotZ α z) σ = NearInst.chartOf R c z σ := by
      unfold NearInst.chartOf
      rw [hR, h2 z]
    have ha : age R (Axi.rotZ α z) = age R z := by
      unfold age
      rw [hϱ z]
    unfold srcW
    rw [ha, hc]
  have hK : ∀ (l : ℝ) (z : Space),
      ENNReal.ofReal ((ϱ (Axi.rotZ α y) ^ 2 *
          (ϱ (Axi.rotZ α y) ^ 2 + ((Axi.rotZ α y) 2 - l * (Axi.rotZ α z) 2) ^ 2))⁻¹) =
        ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - l * z 2) ^ 2))⁻¹) := by
    intro l z
    simp only [hϱ, h2]
  unfold psiMajS
  refine lintegral_congr fun l => ?_
  have hS1 : MeasurableSet {z : Space | ϱ z < θ * ϱ (Axi.rotZ α y)} :=
    measurableSet_lt measurable_ϱ measurable_const
  have hS2 : MeasurableSet {z : Space | ϱ z < θ * ϱ y} :=
    measurableSet_lt measurable_ϱ measurable_const
  rw [← lintegral_indicator hS1, ← lintegral_indicator hS2]
  refine Eq.trans (hmp.lintegral_comp_emb hemb _).symm ?_
  refine lintegral_congr fun z => ?_
  by_cases h : ϱ z < θ * ϱ y
  · have h' : ϱ (Axi.rotZ α z) < θ * ϱ (Axi.rotZ α y) := by
      rw [hϱ, hϱ]
      exact h
    rw [Set.indicator_of_mem (show Axi.rotZ α z ∈ {z : Space | ϱ z < θ * ϱ (Axi.rotZ α y)} from h'),
      Set.indicator_of_mem (show z ∈ {z : Space | ϱ z < θ * ϱ y} from h)]
    simp only [hK, hsrc]
  · have h' : ¬ ϱ (Axi.rotZ α z) < θ * ϱ (Axi.rotZ α y) := by
      rw [hϱ, hϱ]
      exact h
    rw [Set.indicator_of_notMem (show Axi.rotZ α z ∉ {z : Space | ϱ z < θ * ϱ (Axi.rotZ α y)} from h'),
      Set.indicator_of_notMem (show z ∉ {z : Space | ϱ z < θ * ϱ y} from h)]

/-- **`PsiSPeriodic`**: `Ψ_s` is `2c/R`-periodic in the phase. -/
theorem psiSPeriodic : PsiSPeriodic := by
  intro R c θ G hR hc y τ
  show psiMajS R c θ G (τ + 2 * c / R) y = psiMajS R c θ G τ y
  unfold psiMajS
  refine lintegral_congr fun l => lintegral_congr fun z => ?_
  rw [show τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R by ring,
    WYCore.srcW_add_period R c hR hc G]

/-- The three measurability, rotation and periodicity leaves of `Ψ_s`. -/
theorem psiSProps : PsiSMeasurable ∧ PsiSRotInv ∧ PsiSPeriodic :=
  ⟨psiSMeasurable, psiSRotInv, psiSPeriodic⟩

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
