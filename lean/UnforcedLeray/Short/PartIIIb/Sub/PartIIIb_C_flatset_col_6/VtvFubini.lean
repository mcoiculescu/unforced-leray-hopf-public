import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.FlatIntegrandBound
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.FlatOrthSwap.Integ

/-!
# `VtvFubini`: integrability and Fubini of the forced integrand against a flat test

Source of record: `the November 2 reference manuscript`, lines 3511-3514 (the
tested forced equation), 3427-3440 (flat test supported in `s ∈ [s₁,s₂]`, `|η| ≤ R`).

The forced integrand vanishes off `K = [s₁,s₂] × (cell ∩ {|η| ≤ R})`, and on `K` it is a finite sum
of (continuous on the compact box) coefficients times `b_i` (an `L¹(K)` function by `energyLoc`)
or `f_i` (`L²` on the age band by the hypothesis, hence `L¹` on the finite-measure `K`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa

/-- The stress tensor `-(v⊗b + b⊗v)` of the train coefficient. -/
def vtvF (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
  fun p i j => -((vel p.1 p.2 i : ℂ) * b p j + b p i * (vel p.1 p.2 j : ℂ))

theorem vtv_flat_vel_eq (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν μ vel (fun _ _ _ => 0) b Φ p =
      flatIntegrand ν μ (fun _ _ _ => 0) (vtvF vel b) b Φ p := by
  simp only [flatIntegrand, vtvF]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem vtv_trainVel_cont {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ((trainVel tr p.1 p.2 i : ℝ) : ℂ))
      {p : ℝ × (ℝ × ℝ) | 0 ≤ p.1} := by
  have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) {p | 0 ≤ p.1} := by
    refine tr.isTrain.smooth_v.continuousOn.mono ?_
    intro p hp
    exact ⟨hp, mem_univ _⟩
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 i) {p | 0 ≤ p.1} :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn h2
  have h3 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => trainVel tr p.1 p.2 i) {p | 0 ≤ p.1} := by
    refine hcont.congr ?_
    intro p hp
    simp only [trainVel]
    exact if_pos hp
  exact Complex.continuous_ofReal.comp_continuousOn h3

/-- The pointwise representation of the forced integrand as coefficients times `b`, `f`. -/
theorem vtv_rep {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (ν : ℝ) (μ : ℂ)
    (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) (f b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) :
    forcedIntegrand ν μ vel f b Φ p =
      ∑ i : Fin 2, ((-(fibP1 Φ p i)) * b p i + ((μ / (p.1 : ℂ)) * fibP0 Φ p i) * b p i +
        (-(ν : ℂ) * fibP2 Φ p i) * b p i +
        ∑ j : Fin 2, ((-((vel p.1 p.2 i : ℂ) * fibP3 Φ p i j)) * b p j +
          (-((vel p.1 p.2 j : ℂ) * fibP3 Φ p i j)) * b p i) +
        (-(fibP0 Φ p i)) * f p i) := by
  unfold forcedIntegrand
  rw [vtv_flat_vel_eq, fib_rep hΦ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hin : ∑ j : Fin 2, vtvF vel b p i j * fibP3 Φ p i j =
      ∑ j : Fin 2, ((-((vel p.1 p.2 i : ℂ) * fibP3 Φ p i j)) * b p j +
          (-((vel p.1 p.2 j : ℂ) * fibP3 Φ p i j)) * b p i) :=
    Finset.sum_congr rfl fun j _ => by simp only [vtvF]; ring
  have h0 : fibP0 Φ p i = ((Φ p.1 p.2 i : ℝ) : ℂ) := rfl
  rw [hin, h0]
  ring

theorem vtv_zero_outside {c s1 s2 R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) (ν : ℝ) (μ : ℂ)
    (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) (f b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ))
    (hp : p ∈ cwV s1 s2 R) : forcedIntegrand ν μ vel f b Φ p = 0 := by
  unfold forcedIntegrand
  rw [vtv_flat_vel_eq, fib_rep_zero hΦ hsupp ν μ (vtvF vel b) b p hp]
  rw [mem_cwV] at hp
  simp [hsupp p.1 p.2 _ hp]

theorem vtvFubini : VtvFubini := by
  intro ν c μ tr ω g b G f H Φ hΦ
  obtain ⟨hν, hc, hBUC, hE, hBS, hf, hcurl, hid, _hOmInt⟩ := H
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  set K : Set (ℝ × (ℝ × ℝ)) := fibK1 c s1 s2 R with hKdef
  have hKm : MeasurableSet K := fibK1_measurable c s1 s2 R
  have hKc : IsCompact (Icc s1 s2 ×ˢ B0579.box c R) :=
    isCompact_Icc.prod (B0579.isCompact_box c R)
  have hKsub : K ⊆ Icc s1 s2 ×ˢ B0579.box c R := fibK1_subset_Kc c s1 s2 R
  have hKfin : volume K ≠ ⊤ :=
    ((measure_mono hKsub).trans_lt hKc.measure_lt_top).ne
  -- `b ∈ L¹(K)`
  have hbK : ∀ i, IntegrableOn (fun p => b p i) K := by
    intro i
    refine FOS.integrableOn_comp_vnorm2 hKfin hE.measurable ?_ i
    set s2' : ℝ := max s2 (s1 + 1) with hs2'
    have hlt : s1 < s2' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hen := hE.energyLoc s1 s2' hs1 hlt
    have hKsub2 : K ⊆ Icc s1 s2' ×ˢ B0579.cell c := by
      intro p hp
      obtain ⟨⟨h1, h2⟩, hq, _⟩ := fibK1_mem.1 hp
      exact ⟨⟨h1, h2.trans (le_max_left _ _)⟩, hq, mem_univ _⟩
    refine lt_of_le_of_lt ?_ hen
    refine (lintegral_mono fun p => ?_).trans (lintegral_mono_set hKsub2)
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (tnorm2 (G p))])
  -- `f ∈ L¹(K)`: `f ∈ L²` on the band, `K` has finite measure
  have hfK : ∀ i, IntegrableOn (fun p => f p i) K := by
    intro i
    have hKband : K ⊆ Icc s1 s2 ×ˢ B0579.cell c := by
      intro p hp
      obtain ⟨hs, hq, _⟩ := fibK1_mem.1 hp
      exact ⟨⟨hs.1, hs.2⟩, hq, mem_univ _⟩
    have : IsFiniteMeasure ((volume : Measure (ℝ × (ℝ × ℝ))).restrict K) :=
      isFiniteMeasure_restrict.2 hKfin
    exact ((hf s1 s2 hs1 i).mono_measure (Measure.restrict_mono hKband le_rfl)).integrable
      one_le_two
  have key : ∀ (a u : ℝ × (ℝ × ℝ) → ℂ),
      ContinuousOn a (Icc s1 s2 ×ˢ B0579.box c R) → IntegrableOn u K →
      IntegrableOn (fun p => a p * u p) K := fun a u ha hu =>
    IntegrableOn.continuousOn_mul_of_subset ha hu hKc hKm hKsub
  have hpos : ∀ p ∈ Icc s1 s2 ×ˢ B0579.box c R, s1 ≤ p.1 := fun p hp => hp.1.1
  have hsub0 : Icc s1 s2 ×ˢ B0579.box c R ⊆ {p : ℝ × (ℝ × ℝ) | 0 ≤ p.1} :=
    fun p hp => (hs1.le.trans (hpos p hp))
  have hP0 : ∀ i, Continuous fun p => fibP0 Φ p i := fun i =>
    (continuous_apply i).comp (fibP0_continuous hΦ)
  have hP1 : ∀ i, Continuous fun p => fibP1 Φ p i := fun i =>
    (continuous_apply i).comp (fibP1_continuous hΦ)
  have hP2 : ∀ i, Continuous fun p => fibP2 Φ p i := fun i =>
    (continuous_apply i).comp (fibP2_continuous hΦ)
  have hP3 : ∀ i j, Continuous fun p => fibP3 Φ p i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp (fibP3_continuous hΦ))
  have hmu : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => μ / ((p.1 : ℝ) : ℂ))
      (Icc s1 s2 ×ˢ B0579.box c R) := by
    refine continuousOn_const.div (Complex.continuous_ofReal.comp continuous_fst).continuousOn ?_
    intro p hp
    exact Complex.ofReal_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hs1 (hpos p hp)))
  have hgK : IntegrableOn (forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ) K := by
    have hfun : forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ = fun p =>
        ∑ i : Fin 2, ((-(fibP1 Φ p i)) * b p i + ((μ / (p.1 : ℂ)) * fibP0 Φ p i) * b p i +
          (-(ν : ℂ) * fibP2 Φ p i) * b p i +
          ∑ j : Fin 2, ((-((trainVel tr p.1 p.2 i : ℂ) * fibP3 Φ p i j)) * b p j +
            (-((trainVel tr p.1 p.2 j : ℂ) * fibP3 Φ p i j)) * b p i) +
          (-(fibP0 Φ p i)) * f p i) := funext fun p => vtv_rep hΦ ν _ _ f b p
    rw [hfun]
    refine integrable_finsetSum _ fun i _ => ?_
    refine ((((key _ _ (hP1 i).neg.continuousOn (hbK i)).add
      (key _ _ (hmu.mul (hP0 i).continuousOn) (hbK i))).add
      (key _ _ (continuousOn_const.mul (hP2 i).continuousOn) (hbK i))).add ?_).add
      (key _ _ (hP0 i).neg.continuousOn (hfK i))
    refine integrable_finsetSum _ fun j _ => ?_
    refine (key _ _ ?_ (hbK j)).add (key _ _ ?_ (hbK i))
    · exact ((vtv_trainVel_cont tr i).mono hsub0).mul (hP3 i j).continuousOn |>.neg
    · exact ((vtv_trainVel_cont tr j).mono hsub0).mul (hP3 i j).continuousOn |>.neg
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hint : IntegrableOn (forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
    refine hgK.of_forall_sdiff_eq_zero hS ?_
    intro p hp
    exact vtv_zero_outside hΦ hsupp ν _ _ f b p (fib_outside hp.1 hp.2)
  refine ⟨hint, ?_⟩
  have hprod : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  unfold IntegrableOn at hint
  rw [hprod] at hint
  show ∫ p, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b Φ p
      ∂((volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) = _
  rw [hprod]
  exact integral_prod _ hint

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
