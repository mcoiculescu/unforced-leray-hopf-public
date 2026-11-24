import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/1/4`: a.e. identification of `A + E` with the smooth field

Target: `AdvDivSmoothAe` (`Sub/PartI_T02_1_4_4_1_5_1_1.lean`), source lines 261-288 and 3594-3625.

If `w ∈ H^5` is a.e. the smooth periodic field `u`, then `w = ofCylSmooth u`, its weak
derivatives are the classical ones, and `A + E` is a.e. `(u·∇)u + (div u) u`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem advDivSmoothAe : AdvDivSmoothAe := by
  intro c w A E u hus hwu hA hE
  rcases le_or_gt c 0 with hc0 | hc
  · have hcell0 : Cyl.cellμ c = 0 := by
      unfold Cyl.cellμ Cyl.cell
      rw [Set.Ico_eq_empty (not_lt.mpr (by linarith)), Set.empty_prod, Measure.restrict_empty]
    rw [hcell0, MeasureTheory.ae_zero]
    exact Filter.eventually_bot
  have hwu' : hVal w =ᵐ[Cyl.cellμ c] u := by
    rwa [Cyl.cylinder_μ_eq] at hwu
  -- the smooth representative of `w`
  have hwfun : w = Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
      (k := 5) (p := 2) hc u hus := by
    apply hVal_ext
    have hv0 := Sob.W.value_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
      (k := 5) (p := 2) hc u hus
    exact hwu'.trans (hv0.filter_mono (ae_cell_le c)).symm
  -- classical derivatives of the smooth representative
  have hcore : ∀ i : Fin 2, ∀ᵐ z ∂(Cyl.cellμ c),
      hVal (Sob.W.partialDeriv (k := 4) i
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
          (k := 5) (p := 2) hc u hus)) z = fderiv ℝ u z (Sob.cylDir i) := by
    intro i
    have hv := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
      (k := 5) (p := 2) hc u hus (Sob.Idx.cons i (Sob.Idx.zero : Sob.Idx 2 4))
    filter_upwards [hv.filter_mono (ae_cell_le c)] with z hz
    exact hz.trans (by rfl)
  have hpd : ∀ᵐ z ∂(Cyl.cellμ c), ∀ i : Fin 2,
      hVal (Sob.W.partialDeriv (k := 4) i w) z = fderiv ℝ u z (Sob.cylDir i) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hcore i] with z hz
    rw [hwfun]
    exact hz
  have hpr : ∀ᵐ z ∂(Cyl.cellμ c), ∀ i : Fin 2,
      hVal (Sob.W.partialDeriv (k := 3) i
        (Sob.W.restrict (by norm_num : 4 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 4)) z =
        fderiv ℝ u z (Sob.cylDir i) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hcore i] with z hz
    rw [hwfun]
    exact hz
  have hdiff : Differentiable ℝ u := hus.smooth.differentiable (by simp)
  have hcoord : ∀ (x : Plane) (k : Fin 2) (v : Plane),
      fderiv ℝ (fun y => u y k) x v = fderiv ℝ u x v k := by
    intro x k v
    have h := (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp x (hdiff x).hasFDerivAt
    rw [show (fun y => u y k) = (EuclideanSpace.proj k : Cyl.Vec2 →L[ℝ] ℝ) ∘ u from rfl, h.fderiv]
    rfl
  have hd0 : Differentiable ℝ (fun x => u x 0) := fun x =>
    (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).differentiableAt.comp x (hdiff x)
  have hd1 : Differentiable ℝ (fun x => u x 1) := fun x =>
    (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).differentiableAt.comp x (hdiff x)
  have hr : ∀ᵐ z ∂(Cyl.cellμ c),
      hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z = u z := hwu'
  have hsum := hVal_add A E
  filter_upwards [hsum, hA, hE, hwu', hr, hpd, hpr] with z h1 h2 h3 h4 h5 h6 h7
  simp only [Pi.add_apply] at h1
  rw [h1]
  simp only [h2, h3, h4, h5, h7, h6]
  simp only [Train.advection, Cyl.divergence, Cyl.partialQ_eq_fderiv hd0,
    Cyl.partialEta_eq_fderiv hd0, Cyl.partialQ_eq_fderiv hd1, Cyl.partialEta_eq_fderiv hd1,
    hcoord z]
  ext k
  fin_cases k <;> simp [Sob.cylDir, Fin.sum_univ_two]

end UnforcedLeray.Short.PartI
