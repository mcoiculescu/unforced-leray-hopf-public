import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.FluctVelSliceBound.Calc

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1/1`: `velJointJetsFixed`

Source `the November 2 reference manuscript`
427-435: joint jets of `v` of order `≤ 2` are bounded at fixed parameters, from the mixed
age/spatial jets (`trainJetsBoundedFixed`, `ρ = 2`, so `c = ν⁻²`) and `jointFromAgeJets`
(real-valued), applied to the two coordinates of the vector field.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

private theorem vj_norm_le (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1),
    mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 1))]

private theorem vj_iteratedFDeriv_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → EuclideanSpace ℝ (Fin 2)) (i : ℕ) (y : X) (hG : ContDiffAt ℝ ∞ G y) :
    ‖iteratedFDeriv ℝ i G y‖ ≤
      ‖iteratedFDeriv ℝ i (fun x => G x 0) y‖ + ‖iteratedFDeriv ℝ i (fun x => G x 1) y‖ := by
  have hcomp : ∀ (k : Fin 2) (m : Fin i → X),
      iteratedFDeriv ℝ i (fun x => G x k) y m = (iteratedFDeriv ℝ i G y m) k := by
    intro k m
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) hG (i := i)
      (by exact_mod_cast le_top)
    have h' : iteratedFDeriv ℝ i (fun x => G x k) y =
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ i G y) := h
    rw [h']
    rfl
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  have hv := vj_norm_le (iteratedFDeriv ℝ i G y m)
  have h0 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ i (fun x => G x 0) y) m
  have h1 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ i (fun x => G x 1) y) m
  rw [← hcomp 0 m, ← hcomp 1 m] at hv
  rw [add_mul]
  linarith [h0, h1, hv]

private theorem vj_joint (i : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℝ → Plane → EuclideanSpace ℝ (Fin 2),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2) y‖ ≤
        K * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ := by
  have hJ : UnforcedLeray.Short.PartI.JointFromAgeJets :=
    UnforcedLeray.Short.PartI.jointFromAgeJets
  obtain ⟨K, hK0, hK⟩ := hJ i
  refine ⟨2 * K, by positivity, fun G hG y hy => ?_⟩
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hGy : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) y :=
    hG.contDiffAt (hU.mem_nhds ⟨hy, mem_univ _⟩)
  have hcomp : ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2) y‖ ≤
      ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2 0) y‖ +
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2 1) y‖ :=
    vj_iteratedFDeriv_le _ i y hGy
  have hc0 : ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2 0) y‖ ≤
      K * ∑ ℓ ∈ Finset.range (i + 1),
        ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) (fun r z => G r z 0) y.1 y.2‖ :=
    hK (fun r z => G r z 0) ((contDiffOn_piLp 2).1 hG 0) y hy
  have hc1 : ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2 1) y‖ ≤
      K * ∑ ℓ ∈ Finset.range (i + 1),
        ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) (fun r z => G r z 1) y.1 y.2‖ :=
    hK (fun r z => G r z 1) ((contDiffOn_piLp 2).1 hG 1) y hy
  have hage : ∀ k : Fin 2, ∀ ℓ ∈ Finset.range (i + 1),
      ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) (fun r z => G r z k) y.1 y.2‖ ≤
        ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ := by
    intro k ℓ _
    exact UnforcedLeray.Short.PartIIa.fvs_ageJet_proj_le hG k (fun r z => G r z k)
      (fun _ _ _ => rfl) (i := i - ℓ) (l := ℓ) hy y.2
  have hS0 : K * ∑ ℓ ∈ Finset.range (i + 1),
      ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) (fun r z => G r z 0) y.1 y.2‖ ≤
        K * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ hℓ => hage 0 ℓ hℓ) hK0
  have hS1 : K * ∑ ℓ ∈ Finset.range (i + 1),
      ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) (fun r z => G r z 1) y.1 y.2‖ ≤
        K * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ hℓ => hage 1 ℓ hℓ) hK0
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2) y‖
      ≤ _ := hcomp
    _ ≤ _ := add_le_add hc0 hc1
    _ ≤ _ := add_le_add hS0 hS1
    _ = 2 * K * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ := by
      ring

/-- **Joint jets of the velocity** (SP 427-435 at fixed parameters, `ρ = 2`: `c = ν⁻²`): for a BUC
train with `ν ≤ ν₀` and each order `l ≤ 2` the full derivative of `(s, z) ↦ v s z` in
`(s, q, η)` is bounded on `s > 0`. -/
theorem velJointJetsFixed : VelJointJetsFixed := by
  have h : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed :=
    UnforcedLeray.Short.PartI.trainJetsBoundedFixed
  obtain ⟨ν₀, hν₀, H⟩ := h 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν c hν hνν₀ hc tr hbuc => ?_⟩
  have hcp : UnforcedLeray.Short.PartI.trainPeriod 2 ν = c := by
    rw [hc, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg hν.le, Real.rpow_two]
  subst hcp
  have hMex : ∀ ℓ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.v s z‖ ≤ M :=
    fun ℓ j => H ν hν hνν₀ tr hbuc ℓ j
  choose M hM using hMex
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)
  choose K hK0 hK using vj_joint
  refine ⟨∑ l ∈ Finset.range 3, K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)|, ?_⟩
  intro l hl y hy
  have hl3 : l ∈ Finset.range 3 := Finset.mem_range.2 (by omega)
  calc ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖
      ≤ K l * ∑ ℓ ∈ Finset.range (l + 1),
          ‖UnforcedLeray.Short.PartI.ageJet ℓ (l - ℓ) tr.v y.1 y.2‖ :=
        hK l tr.v hsm y hy
    _ ≤ K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ =>
          (hM ℓ (l - ℓ) y.1 hy y.2).trans (le_abs_self _)) (hK0 l)
    _ ≤ ∑ l ∈ Finset.range 3, K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)| :=
        Finset.single_le_sum (f := fun l => K l * ∑ ℓ ∈ Finset.range (l + 1), |M ℓ (l - ℓ)|)
          (fun l' _ => mul_nonneg (hK0 l') (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hl3

end UnforcedLeray.Short.PartIIIb.Concrete
