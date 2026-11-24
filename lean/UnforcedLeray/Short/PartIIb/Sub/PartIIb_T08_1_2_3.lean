import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Part II-b, leaf `PartII-b:T08/1/2/3`: integration by parts for the drift transpose

Source of record: `the November 2 reference manuscript`, lines 1912-1915
(`𝒯 = ∂_τ - y·∇/2`, `div y = 3`).

Proved here: `driftIBP_of_phase` (`DriftIBP`), via
* `phaseInt_driftT_zero`: `⟨𝒯ᵗ f⟩ = 0` for a scalar phase test `f`
  (`∫ ∂_τ f = 0` by periodicity, `∫ y·∇f = -3 ∫ f` by spatial integration by parts),
* the product rule for `dotL`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- A continuous function with bounded `y`-support. -/
def DIGood (f : ℝ × Space → ℂ) : Prop :=
  Continuous f ∧ ∃ R : ℝ, ∀ t y, R < ‖y‖ → f (t, y) = 0

theorem DIGood.of_phaseTest {P : ℝ} {f : ℝ × Space → ℂ} (h : IsPhaseTest P f) : DIGood f :=
  ⟨h.continuous, h.bounded_support⟩

theorem DIGood.add {f g : ℝ × Space → ℂ} (hf : DIGood f) (hg : DIGood g) :
    DIGood (fun p => f p + g p) := by
  obtain ⟨R, hR⟩ := hf.2
  obtain ⟨S, hS⟩ := hg.2
  exact ⟨hf.1.add hg.1, max R S, fun t y hy => by
    simp [hR t y (lt_of_le_of_lt (le_max_left _ _) hy),
      hS t y (lt_of_le_of_lt (le_max_right _ _) hy)]⟩

theorem DIGood.smul {f : ℝ × Space → ℂ} (hf : DIGood f) (c : ℝ) :
    DIGood (fun p => c • f p) := by
  obtain ⟨R, hR⟩ := hf.2
  exact ⟨hf.1.const_smul c, R, fun t y hy => by simp [hR t y hy]⟩

theorem DIGood.slice_integrable {f : ℝ × Space → ℂ} (hf : DIGood f) (t : ℝ) :
    Integrable (fun y : Space => f (t, y)) := by
  obtain ⟨R, hR⟩ := hf.2
  have hc : Continuous fun y : Space => f (t, y) := hf.1.comp (by fun_prop)
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
      (fun y hy => hR t y (by simpa [mem_closedBall, dist_zero_right] using hy)))

theorem DIGood.prod_integrable {f : ℝ × Space → ℂ} (hf : DIGood f) (a b : ℝ) :
    Integrable f ((volume.restrict (Ioc a b)).prod (volume : Measure Space)) := by
  obtain ⟨R, hR⟩ := hf.2
  have hsupp : Function.support f ⊆ (univ : Set ℝ) ×ˢ (closedBall (0 : Space) R) := by
    intro p hp
    rcases p with ⟨t, y⟩
    refine ⟨mem_univ _, ?_⟩
    by_contra hy
    apply hp
    exact hR t y (by simpa [mem_closedBall, dist_zero_right] using hy)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  unfold IntegrableOn
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hK : IsCompact (Icc a b ×ˢ (closedBall (0 : Space) R)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have h1 : IntegrableOn f (Icc a b ×ˢ (closedBall (0 : Space) R)) volume :=
    hf.1.continuousOn.integrableOn_compact hK
  exact h1.mono_set (prod_mono Ioc_subset_Icc_self subset_rfl)

theorem DIGood.outer_integrable {f : ℝ × Space → ℂ} (hf : DIGood f) (a b : ℝ) :
    Integrable (fun t => ∫ y : Space, f (t, y)) (volume.restrict (Ioc a b)) :=
  (hf.prod_integrable a b).integral_prod_left

theorem phaseInt_add {P : ℝ} {f g : ℝ × Space → ℂ} (hf : DIGood f) (hg : DIGood g) :
    phaseInt P (fun p => f p + g p) = phaseInt P f + phaseInt P g := by
  unfold phaseInt
  rw [← smul_add, ← integral_add (hf.outer_integrable 0 P) (hg.outer_integrable 0 P)]
  congr 2
  funext t
  exact integral_add (hf.slice_integrable t) (hg.slice_integrable t)

theorem phaseInt_smul {P : ℝ} {f : ℝ × Space → ℂ} (c : ℝ) :
    phaseInt P (fun p => c • f p) = c • phaseInt P f := by
  unfold phaseInt
  simp only [integral_smul]
  rw [smul_comm]

/-- Time derivative of a phase test integrates to zero over a period. -/
theorem int_dτ_zero {P : ℝ} (hP : 0 < P) {h : ℝ × Space → ℂ} (hh : IsPhaseTest P h) :
    ∫ t in Ioc 0 P, ∫ y : Space, dτ h (t, y) = 0 := by
  have hG : DIGood (dτ h) := DIGood.of_phaseTest hh.dτ
  rw [integral_integral_swap (f := fun t y => dτ h (t, y)) (hG.prod_integrable 0 P)]
  have : ∀ y : Space, ∫ t in Ioc 0 P, dτ h (t, y) = 0 := by
    intro y
    rw [← intervalIntegral.integral_of_le hP.le]
    have hd : ∀ t, HasDerivAt (fun s => h (s, y)) (dτ h (t, y)) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1, 0) : ℝ × Space) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
      have h2 : HasFDerivAt h (fderiv ℝ h (t, y)) (t, y) :=
        ((hh.smooth.differentiable (by simp)) (t, y)).hasFDerivAt
      exact h2.comp_hasDerivAt t h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)]
    · have := hh.periodic 0 y
      simp only [zero_add] at this
      simp [this]
    · exact (hG.1.comp (by fun_prop : Continuous fun s : ℝ => ((s, y) : ℝ × Space))).intervalIntegrable _ _
  simp [this]

theorem dy_slice {f : ℝ × Space → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (y : Space) (j : Fin 3) :
    fderiv ℝ (fun z : Space => f (t, z)) y (coordinateVector j) = dy j f (t, y) := by
  have h1 : HasFDerivAt (fun z : Space => ((t, z) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h2 : HasFDerivAt f (fderiv ℝ f (t, y)) (t, y) :=
    ((hf.differentiable (by simp)) (t, y)).hasFDerivAt
  have h3 := (h2.comp y h1).fderiv
  have h4 : (fun z : Space => f (t, z)) = f ∘ Prod.mk t := rfl
  rw [h4, h3]
  simp [dy]

theorem DIGood.coord_smul_dy {P : ℝ} {f : ℝ × Space → ℂ} (hf : IsPhaseTest P f) (j : Fin 3) :
    DIGood (fun p => (p.2 j) • dy j f p) := by
  obtain ⟨R, hR⟩ := (hf.dy j).bounded_support
  refine ⟨((contDiff_coord j).continuous.comp continuous_snd).smul (hf.dy j).continuous, R,
    fun t y hy => ?_⟩
  simp [hR t y hy]

/-- `∫ y·∇f = -3 ∫ f` on each slice. -/
theorem int_radialT {P : ℝ} {f : ℝ × Space → ℂ} (hf : IsPhaseTest P f) (t : ℝ) :
    ∫ y : Space, radialT f (t, y) = -3 * ∫ y : Space, f (t, y) := by
  have hj : ∀ j : Fin 3, ∫ y : Space, (y j) • dy j f (t, y) = -∫ y : Space, f (t, y) := by
    intro j
    have hsl : Differentiable ℝ (fun z : Space => f (t, z)) :=
      (hf.smooth.differentiable (by simp)).comp (by fun_prop)
    have hcoord : Differentiable ℝ (fun y : Space => y j) :=
      (contDiff_coord j).differentiable (by simp)
    have hfi := (DIGood.of_phaseTest hf).slice_integrable t
    have hsd : ∀ y : Space, fderiv ℝ (fun y : Space => y j) y (coordinateVector j) = 1 := by
      intro y
      have := congrFun (sd_coord j j) y
      simpa [sd] using this
    have hib := (DIGood.coord_smul_dy hf j).slice_integrable t
    have := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := (volume : Measure Space)) (f := fun y : Space => y j)
      (g := fun z : Space => f (t, z)) (v := coordinateVector j)
      (by simpa [hsd] using hfi)
      (by simpa [dy_slice hf.smooth] using hib)
      (by
        obtain ⟨R, hR⟩ := hf.bounded_support
        have hc : Continuous fun y : Space => (y j) • f (t, y) :=
          ((contDiff_coord j).continuous).smul (hf.continuous.comp (by fun_prop))
        exact hc.integrable_of_hasCompactSupport
          (HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
            (fun y hy => by
              simp [hR t y (by simpa [mem_closedBall, dist_zero_right] using hy)])))
      (fun y _ => hcoord y) (fun y _ => hsl y)
    simpa [dy_slice hf.smooth, hsd] using this
  have hsum : ∫ y : Space, radialT f (t, y) = ∑ j : Fin 3, ∫ y : Space, (y j) • dy j f (t, y) := by
    unfold radialT
    exact integral_finsetSum _ fun j _ => (DIGood.coord_smul_dy hf j).slice_integrable t
  rw [hsum, Finset.sum_congr rfl (fun j _ => hj j)]
  simp [Finset.sum_const]

theorem phaseInt_driftT_zero {P : ℝ} (hP : 0 < P) {f : ℝ × Space → ℂ} (hf : IsPhaseTest P f) :
    phaseInt P (driftT f) = 0 := by
  have h1 : DIGood (dτ f) := DIGood.of_phaseTest hf.dτ
  have h2 : DIGood (radialT f) := DIGood.of_phaseTest hf.radialT
  have h3 : DIGood f := DIGood.of_phaseTest hf
  have hd : driftT f = fun p => ((-1 : ℝ) • dτ f p + (1 / 2 : ℝ) • radialT f p) +
      (3 / 2 : ℝ) • f p := by
    funext p; simp [driftT]
  have hI : phaseInt P (dτ f) = 0 := by
    unfold phaseInt; rw [int_dτ_zero hP hf]; simp
  have hR : phaseInt P (radialT f) = -3 * phaseInt P f := by
    unfold phaseInt
    have : (fun t => ∫ y : Space, radialT f (t, y)) = fun t => -3 * ∫ y : Space, f (t, y) :=
      funext fun t => int_radialT hf t
    rw [this, integral_const_mul]
    simp [smul_neg]
    ring
  rw [hd, phaseInt_add ((h1.smul _).add (h2.smul _)) (h3.smul _),
    phaseInt_add (h1.smul _) (h2.smul _), phaseInt_smul, phaseInt_smul, phaseInt_smul, hI, hR]
  simp only [Complex.real_smul, mul_zero, zero_add]
  push_cast
  ring

theorem dotL_smul_left (c : ℝ) (a b : CVec3) : dotL (c • a) b = c • dotL a b := by
  simp [dotL_apply, Finset.smul_sum, smul_mul_assoc]

theorem dotL_smul_right (c : ℝ) (a b : CVec3) : dotL a (c • b) = c • dotL a b := by
  simp [dotL_apply, Finset.smul_sum, mul_smul_comm]

theorem fderiv_dotL {Φ u : ℝ × Space → CVec3} {p : ℝ × Space} (hΦ : DifferentiableAt ℝ Φ p)
    (hu : DifferentiableAt ℝ u p) (v : ℝ × Space) :
    fderiv ℝ (fun q => dotL (Φ q) (u q)) p v =
      dotL (fderiv ℝ Φ p v) (u p) + dotL (Φ p) (fderiv ℝ u p v) := by
  let pr : Fin 3 → CVec3 →L[ℝ] ℂ := fun i =>
    (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ
  have hΦi : ∀ i, HasFDerivAt (fun q => Φ q i) ((pr i).comp (fderiv ℝ Φ p)) p :=
    fun i => (pr i).hasFDerivAt.comp p hΦ.hasFDerivAt
  have hui : ∀ i, HasFDerivAt (fun q => u q i) ((pr i).comp (fderiv ℝ u p)) p :=
    fun i => (pr i).hasFDerivAt.comp p hu.hasFDerivAt
  have hsum : HasFDerivAt (fun q => ∑ i, Φ q i * u q i)
      (∑ i, (Φ p i • (pr i).comp (fderiv ℝ u p) + u p i • (pr i).comp (fderiv ℝ Φ p))) p :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hΦi i).mul (hui i))
  have hf : (fun q => dotL (Φ q) (u q)) = fun q => ∑ i, Φ q i * u q i :=
    funext fun q => dotL_apply _ _
  rw [hf, hsum.fderiv]
  simp [dotL_apply, pr, Finset.sum_add_distrib, mul_comm]
  exact add_comm _ _

theorem dotL_phaseTest {P : ℝ} {Φ w : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (hw : IsPhaseTest P w) : IsPhaseTest P (fun q => dotL (Φ q) (w q)) where
  smooth := by
    have hf : (fun q => dotL (Φ q) (w q)) = fun q => ∑ i, Φ q i * w q i :=
      funext fun q => dotL_apply _ _
    rw [hf]
    refine ContDiff.sum fun i _ => ?_
    have hpr : ∀ i, ContDiff ℝ ∞ (fun q => Φ q i) := fun i =>
      ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hΦ.smooth
    have hpr' : ∀ i, ContDiff ℝ ∞ (fun q => w q i) := fun i =>
      ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hw.smooth
    exact (hpr i).mul (hpr' i)
  periodic τ y := by simp [hΦ.periodic, hw.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

theorem dτ_dotL {Φ u : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (hu : ContDiff ℝ ∞ u)
    (p : ℝ × Space) :
    dτ (fun q => dotL (Φ q) (u q)) p = dotL (dτ Φ p) (u p) + dotL (Φ p) (dτ u p) :=
  fderiv_dotL (hΦ.differentiable (by simp) p) (hu.differentiable (by simp) p) _

theorem dy_dotL {Φ u : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (hu : ContDiff ℝ ∞ u)
    (j : Fin 3) (p : ℝ × Space) :
    dy j (fun q => dotL (Φ q) (u q)) p = dotL (dy j Φ p) (u p) + dotL (Φ p) (dy j u p) :=
  fderiv_dotL (hΦ.differentiable (by simp) p) (hu.differentiable (by simp) p) _

theorem radialT_dotL {Φ u : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (hu : ContDiff ℝ ∞ u)
    (p : ℝ × Space) :
    radialT (fun q => dotL (Φ q) (u q)) p =
      dotL (radialT Φ p) (u p) + dotL (Φ p) (radialT u p) := by
  unfold radialT
  simp only [dy_dotL hΦ hu, smul_add, Finset.sum_add_distrib, map_sum,
    ContinuousLinearMap.sum_apply, dotL_smul_left, dotL_smul_right]

theorem driftIBP_of_phase : DriftIBP := by
  intro P Φ u hP hΦ hu
  have hw : IsPhaseTest P (fun p => dτ u p - (1 / 2 : ℝ) • radialT u p) :=
    hu.dτ.sub (hu.radialT.const_smul (1 / 2 : ℝ))
  have hf := dotL_phaseTest hΦ hu
  have hg := dotL_phaseTest hΦ hw
  unfold pairF
  have key : (fun x => dotL (driftT Φ x) (u x)) = fun x =>
      dotL (Φ x) (dτ u x - (1 / 2 : ℝ) • radialT u x) +
        driftT (fun q => dotL (Φ q) (u q)) x := by
    funext x
    have h1 := dτ_dotL hΦ.smooth hu.smooth x
    have h2 := radialT_dotL hΦ.smooth hu.smooth x
    simp only [driftT, h1, h2, map_add, map_neg, map_sub, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, dotL_smul_left, dotL_smul_right]
    module
  rw [key, phaseInt_add (DIGood.of_phaseTest hg) (DIGood.of_phaseTest hf.driftT),
    phaseInt_driftT_zero hP hf, add_zero]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.driftIBP_of_phase
