import UnforcedLeray.Lib.TrainB.GraphProduct
import UnforcedLeray.Lib.SobolevC.CylDensity

/-!
# Smooth density and subtraction identities in cylinder H³

These are the concrete completion inputs for extending the smooth product estimate to weak H³.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology BoundedContinuousFunction

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

abbrev ScalarH3 (c : ℝ) := UnforcedLeray.Cyl.H ℝ ℝ c 0 3

/-- Smooth cylinder fields are closed under addition. -/
theorem isCylSmooth_add {c : ℝ} {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Sob.IsCylSmooth c (f + g) := by
  obtain ⟨Rf, hfbd⟩ := hf.bounded
  obtain ⟨Rg, hgbd⟩ := hg.bounded
  refine ⟨hf.smooth.add hg.smooth, ?_, ?_⟩
  · intro z
    simp only [Pi.add_apply]
    rw [hf.periodic, hg.periodic]
  · refine ⟨max Rf Rg, ?_⟩
    intro z hz
    have hRf : Rf < |z.2| := lt_of_le_of_lt (le_max_left _ _) hz
    have hRg : Rg < |z.2| := lt_of_le_of_lt (le_max_right _ _) hz
    simp [hfbd z hRf, hgbd z hRg]

/-- The smooth Sobolev construction respects addition in H³. -/
theorem ofCylSmooth3_add_eq {c : ℝ} (hc : 0 < c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (f + g) (isCylSmooth_add hf hg) =
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf +
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg := by
  have hmap := map_add (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2)
    (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf)
    (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg)
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc (f + g) (isCylSmooth_add hf hg),
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc f hf,
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc g hg,
    Lp.coeFn_add (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
      (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf))
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg))] with z hsum hfz hgz hadd
  have hmapz := congrArg (fun u : Lp ℝ 2
    (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => u z) hmap
  simp only [Pi.add_apply] at hadd
  rw [hmapz, hsum, hadd, hfz, hgz]
  rfl

/-- The smooth Sobolev representative construction respects subtraction in H³. -/
theorem ofCylSmooth3_sub_eq {c : ℝ} (hc : 0 < c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (f - g)
        (UnforcedLeray.TrainB.isCylSmooth_sub hf hg) =
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf -
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg := by
  have hmap := map_sub (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2)
    (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf)
    (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg)
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc (f - g)
        (UnforcedLeray.TrainB.isCylSmooth_sub hf hg),
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc f hf,
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc g hg,
    Lp.coeFn_sub (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
      (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf))
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg))] with z hfg hfz hgz hsub
  have hmapz := congrArg (fun u : Lp ℝ 2
    (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => u z) hmap
  simp only [Pi.sub_apply] at hsub
  rw [hmapz, hfg, hsub, hfz, hgz]
  rfl

/-- The H³ smooth-field construction depends only on the underlying field, not on its proof. -/
theorem ofCylSmooth3_congr {c : ℝ} (hc : 0 < c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (hfg : f = g) :
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf =
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg := by
  subst g
  congr 1

/-- The smooth quadratic product difference splits into two genuine product fields in H³. -/
theorem ofCylSmooth3_product_difference {c : ℝ} (hc : 0 < c)
    {f₁ f₂ g₁ g₂ : Plane → ℝ}
    (hf₁ : UnforcedLeray.Sob.IsCylSmooth c f₁) (hf₂ : UnforcedLeray.Sob.IsCylSmooth c f₂)
    (hg₁ : UnforcedLeray.Sob.IsCylSmooth c g₁) (hg₂ : UnforcedLeray.Sob.IsCylSmooth c g₂) :
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
      (fun z => f₁ z * g₁ z - f₂ z * g₂ z)
      (UnforcedLeray.TrainB.isCylSmooth_sub (UnforcedLeray.TrainB.IsCylSmooth.mul hf₁ hg₁)
        (UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ hg₂)) =
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
      (fun z => (f₁ z - f₂ z) * g₁ z)
      (UnforcedLeray.TrainB.IsCylSmooth.mul (UnforcedLeray.TrainB.isCylSmooth_sub hf₁ hf₂) hg₁) +
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
      (fun z => f₂ z * (g₁ z - g₂ z))
      (UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ (UnforcedLeray.TrainB.isCylSmooth_sub hg₁ hg₂)) := by
  let hA := UnforcedLeray.TrainB.IsCylSmooth.mul (UnforcedLeray.TrainB.isCylSmooth_sub hf₁ hf₂) hg₁
  let hB := UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ (UnforcedLeray.TrainB.isCylSmooth_sub hg₁ hg₂)
  let hsum := UnforcedLeray.TrainB.isCylSmooth_add hA hB
  have hfield : (fun z => f₁ z * g₁ z - f₂ z * g₂ z) =
      (fun z => (f₁ z - f₂ z) * g₁ z + f₂ z * (g₁ z - g₂ z)) := by
    funext z
    ring
  calc
    _ = UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
        (fun z => f₁ z * g₁ z - f₂ z * g₂ z)
        (UnforcedLeray.TrainB.isCylSmooth_sub (UnforcedLeray.TrainB.IsCylSmooth.mul hf₁ hg₁)
          (UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ hg₂)) := rfl
    _ = UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
        (fun z => (f₁ z - f₂ z) * g₁ z + f₂ z * (g₁ z - g₂ z)) hsum := by
      exact ofCylSmooth3_congr hc _ _ hfield
    _ = UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
          (fun z => (f₁ z - f₂ z) * g₁ z) hA +
        UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
          (fun z => f₂ z * (g₁ z - g₂ z)) hB := ofCylSmooth3_add_eq hc hA hB

/-- Smooth quadratic products satisfy the difference estimate required for completion. -/
theorem smooth_h3_product_difference_norm {c : ℝ} (hc1 : 1 ≤ c) {f₁ f₂ g₁ g₂ : Plane → ℝ}
    (hf₁ : UnforcedLeray.Sob.IsCylSmooth c f₁) (hf₂ : UnforcedLeray.Sob.IsCylSmooth c f₂)
    (hg₁ : UnforcedLeray.Sob.IsCylSmooth c g₁) (hg₂ : UnforcedLeray.Sob.IsCylSmooth c g₂) :
    ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1])
        (fun z => f₁ z * g₁ z) (UnforcedLeray.TrainB.IsCylSmooth.mul hf₁ hg₁) -
      UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1])
        (fun z => f₂ z * g₂ z) (UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ hg₂)‖ ≤
      384 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) (fun z => f₁ z - f₂ z)
        (UnforcedLeray.TrainB.isCylSmooth_sub hf₁ hf₂)‖ *
        ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) g₁ hg₁‖ +
      384 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) f₂ hf₂‖ *
        ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) (fun z => g₁ z - g₂ z)
          (UnforcedLeray.TrainB.isCylSmooth_sub hg₁ hg₂)‖ := by
  have hc : 0 < c := by linarith [hc1]
  let p₁ := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (fun z => f₁ z * g₁ z) (UnforcedLeray.TrainB.IsCylSmooth.mul hf₁ hg₁)
  let p₂ := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (fun z => f₂ z * g₂ z) (UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ hg₂)
  have hprod₁ := UnforcedLeray.TrainB.IsCylSmooth.mul hf₁ hg₁
  have hprod₂ := UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ hg₂
  have hsub := UnforcedLeray.TrainB.isCylSmooth_sub hprod₁ hprod₂
  have hfield : (fun z => f₁ z * g₁ z - f₂ z * g₂ z) =
      (fun z => f₁ z * g₁ z) - (fun z => f₂ z * g₂ z) := by
    funext z
    rfl
  have hpointSmooth : UnforcedLeray.Sob.IsCylSmooth c
      (fun z => f₁ z * g₁ z - f₂ z * g₂ z) := by
    rw [hfield]
    exact hsub
  have hsubW := ofCylSmooth3_congr hc hpointSmooth hsub hfield
  have hdiff : UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
      (fun z => f₁ z * g₁ z - f₂ z * g₂ z) hpointSmooth = p₁ - p₂ := by
    calc
      _ = UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
          ((fun z => f₁ z * g₁ z) - (fun z => f₂ z * g₂ z)) hsub := hsubW
      _ = p₁ - p₂ := ofCylSmooth3_sub_eq hc hprod₁ hprod₂
  have hsplit := ofCylSmooth3_product_difference hc hf₁ hf₂ hg₁ hg₂
  change ‖p₁ - p₂‖ ≤ _
  rw [← hdiff, hsplit]
  calc
    ‖(UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
          (fun z => (f₁ z - f₂ z) * g₁ z)
          (UnforcedLeray.TrainB.IsCylSmooth.mul (UnforcedLeray.TrainB.isCylSmooth_sub hf₁ hf₂) hg₁)) +
      UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc
          (fun z => f₂ z * (g₁ z - g₂ z))
          (UnforcedLeray.TrainB.IsCylSmooth.mul hf₂ (UnforcedLeray.TrainB.isCylSmooth_sub hg₁ hg₂))‖ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add
      (smooth_h3_scalar_mul_norm_explicit hc1 (UnforcedLeray.TrainB.isCylSmooth_sub hf₁ hf₂) hg₁)
      (smooth_h3_scalar_mul_norm_explicit hc1 hf₂ (UnforcedLeray.TrainB.isCylSmooth_sub hg₁ hg₂))

#print axioms UnforcedLeray.TrainB.ofCylSmooth3_congr
#print axioms UnforcedLeray.TrainB.ofCylSmooth3_product_difference
#print axioms UnforcedLeray.TrainB.smooth_h3_product_difference_norm

/-- Every order-three Sobolev class admits smooth periodic compact-axial approximants. -/
theorem exists_smoothH3_sequence {c : ℝ} (hc : 0 < c) (x : ScalarH3 c) :
    ∃ y : ℕ → ScalarH3 c, ∃ f : ℕ → Plane → ℝ,
      ∃ hf : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (f n),
      (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        hc (f n) (hf n)) ∧
      Tendsto y atTop (𝓝 x) := by
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ)
    (k := 3) (p := 2) hc (by norm_num) x
  choose f hf hrep using hy
  refine ⟨y, f, hf, ?_, hlim⟩
  intro n
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have hrepW := (UnforcedLeray.Sob.ae_eq_wμ_iff (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
  filter_upwards [hrepW,
    UnforcedLeray.Sob.W.value_ofCylSmooth (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc (f n) (hf n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

#print axioms UnforcedLeray.TrainB.isCylSmooth_add
#print axioms UnforcedLeray.TrainB.ofCylSmooth3_add_eq
#print axioms UnforcedLeray.TrainB.ofCylSmooth3_sub_eq
#print axioms UnforcedLeray.TrainB.exists_smoothH3_sequence

/-- Forgetting the highest derivative level gives the canonical continuous H³-to-H² map. -/
def forgetH3toH2 {c : ℝ} : ScalarH3 c →L[ℝ] ScalarH2 c :=
  UnforcedLeray.Sob.W.restrict (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ) (p := 2)
    (by norm_num)

/-- The restriction map agrees with the lower-order smooth construction. -/
theorem forgetH3toH2_ofCylSmooth {c : ℝ} (hc : 0 < c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) :
    forgetH3toH2 (UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2) hc f hf) =
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 2) (p := 2) hc f hf := by
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) hc f hf,
    UnforcedLeray.Sob.W.value_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) hc f hf] with z h2 h3
  simpa only [forgetH3toH2, UnforcedLeray.Sob.W.value_restrict] using h3.trans h2.symm

/-- An H³ smooth approximating sequence has bounded continuous representatives converging
uniformly to a representative of the limiting H³ value. -/
theorem exists_h3_uniform_representative_sequence {c : ℝ} (hc1 : 1 ≤ c)
    (x : ScalarH3 c) :
    ∃ xseq : ℕ → ScalarH3 c, ∃ f : ℕ → Plane → ℝ,
      ∃ hf : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (f n),
      ∃ F : Plane →ᵇ ℝ, ∃ Fseq : ℕ → Plane →ᵇ ℝ,
      (∀ n, xseq n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith [hc1]) (f n) (hf n)) ∧
      (∀ n z, Fseq n z = f n z) ∧ Tendsto Fseq atTop (𝓝 F) ∧
      (F : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) ∧
      Tendsto xseq atTop (𝓝 x) := by
  obtain ⟨xseq, f, hf, hxrep, hxlim⟩ := exists_smoothH3_sequence
    (c := c) (by linarith [hc1]) x
  let x2 := forgetH3toH2 x
  let x2seq : ℕ → ScalarH2 c := fun n => forgetH3toH2 (xseq n)
  have hx2rep (n : ℕ) : x2seq n = UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 2) (p := 2)
      (by linarith [hc1]) (f n) (hf n) := by
    change forgetH3toH2 (xseq n) = _
    rw [hxrep n]
    exact forgetH3toH2_ofCylSmooth (by linarith [hc1]) (hf n)
  have hx2lim : Tendsto x2seq atTop (𝓝 x2) :=
    (forgetH3toH2.continuous.tendsto x).comp hxlim
  obtain ⟨Fseq, hFseq, hFc⟩ := smooth_density_bcf_cauchy hc1
    (by linarith [hc1]) x2 x2seq f hf hx2rep hx2lim
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hFc
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2
  let μ := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
  have hLp : Tendsto (fun n => V (x2seq n)) atTop (𝓝 (V x2)) :=
    (V.continuous.tendsto x2).comp hx2lim
  have hmeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, hns, hconv⟩ := hmeasure.exists_seq_tendsto_ae
  have hrep (n : ℕ) : (Fseq n : Plane → ℝ) =ᵐ[μ] (V (x2seq n)) := by
    rw [hx2rep n]
    filter_upwards [UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 2) (p := 2) (by linarith [hc1]) (f n) (hf n)] with z hz
    exact (hFseq n z).trans hz.symm
  have hrepAll : ∀ᵐ z ∂μ, ∀ n, Fseq n z = V (x2seq n) z := by
    rw [ae_all_iff]
    intro n
    exact hrep n
  have hFpoint (z : Plane) : Tendsto (fun n => Fseq n z) atTop (𝓝 (F z)) :=
    ((continuous_eval_const z).tendsto F).comp hF
  have hlimitAE : (F : Plane → ℝ) =ᵐ[μ] (V x2) := by
    filter_upwards [hconv, hrepAll] with z hzconv hzrep
    have hzF : Tendsto (fun k => Fseq (ns k) z) atTop (𝓝 (F z)) :=
      (hFpoint z).comp hns.tendsto_atTop
    have hzF' := hzF.congr' (Eventually.of_forall fun k => hzrep (ns k))
    exact tendsto_nhds_unique hzF' hzconv
  have hrestrictValue : V x2 =
      UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x := by
    change UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 2 2
      (UnforcedLeray.Sob.W.restrict (h := by norm_num) x) = _
    exact UnforcedLeray.Sob.W.value_restrict (h := by norm_num) x
  have hvalueAE : (V x2 : Plane → ℝ) =ᵐ[μ]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) := by
    filter_upwards [] with z
    exact congrArg (fun u : Lp ℝ 2 μ => u z) hrestrictValue
  refine ⟨xseq, f, hf, F, Fseq, hxrep, hFseq, hF, ?_, hxlim⟩
  simpa [μ, scalarH2_measure_eq_cell] using hlimitAE.trans hvalueAE

/-- The products of smooth H³ approximants are Cauchy in the actual H³ graph norm.
The proof uses the uniform smooth difference estimate, boundedness of both convergent input
sequences, and completeness of the Sobolev graph. -/
theorem exists_smooth_h3_product_limit {c : ℝ} (hc1 : 1 ≤ c)
    (x y : ScalarH3 c) :
    ∃ z : ScalarH3 c, ∃ xseq yseq : ℕ → ScalarH3 c,
      ∃ f g : ℕ → Plane → ℝ,
      ∃ hf : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (f n),
      ∃ hg : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (g n),
      ∃ pseq : ℕ → ScalarH3 c,
      (∀ n, pseq n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith [hc1]) (fun z => f n z * g n z)
        (UnforcedLeray.TrainB.IsCylSmooth.mul (hf n) (hg n))) ∧
      (∀ n, xseq n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith [hc1]) (f n) (hf n)) ∧
      (∀ n, yseq n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith [hc1]) (g n) (hg n)) ∧
      Tendsto xseq atTop (𝓝 x) ∧ Tendsto yseq atTop (𝓝 y) ∧
      Tendsto pseq atTop (𝓝 z) ∧
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 z : Plane → ℝ) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
        (fun q => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) q *
          (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 y) q) ∧
      ‖z‖ ≤ 384 * ‖x‖ * ‖y‖ := by
  obtain ⟨xseq, f, hf, F, Fseq, hxrep, hFseq, hF, hFae, hxlim⟩ :=
    exists_h3_uniform_representative_sequence hc1 x
  obtain ⟨yseq, g, hg, G, Gseq, hyrep, hGseq, hG, hGae, hylim⟩ :=
    exists_h3_uniform_representative_sequence hc1 y
  let pseq : ℕ → ScalarH3 c := fun n =>
    UnforcedLeray.Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (k := 3) (p := 2) (by linarith [hc1])
      (fun z => f n z * g n z) (UnforcedLeray.TrainB.IsCylSmooth.mul (hf n) (hg n))
  obtain ⟨Cx, hCx⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hxlim)
  obtain ⟨Cy, hCy⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hylim)
  have hCx0 : 0 ≤ Cx := le_trans (norm_nonneg (xseq 0)) (hCx _ ⟨0, rfl⟩)
  have hCy0 : 0 ≤ Cy := le_trans (norm_nonneg (yseq 0)) (hCy _ ⟨0, rfl⟩)
  have hCauchy : CauchySeq pseq := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ : ℝ := ε / (384 * (Cx + Cy + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨Nx, hNx⟩ := (Metric.cauchySeq_iff.mp hxlim.cauchySeq) δ hδ
    obtain ⟨Ny, hNy⟩ := (Metric.cauchySeq_iff.mp hylim.cauchySeq) δ hδ
    refine ⟨max Nx Ny, ?_⟩
    intro m hm n hn
    have hxm : Nx ≤ m := le_trans (le_max_left _ _) hm
    have hyn : Ny ≤ n := le_trans (le_max_right _ _) hn
    have hxn : Nx ≤ n := le_trans (le_max_left _ _) hn
    have hym : Ny ≤ m := le_trans (le_max_right _ _) hm
    have hdx : dist (xseq m) (xseq n) < δ := hNx m hxm n hxn
    have hdy : dist (yseq m) (yseq n) < δ := hNy m hym n hyn
    have hdiff := smooth_h3_product_difference_norm hc1 (hf m) (hf n) (hg m) (hg n)
    have hfxsmooth := UnforcedLeray.TrainB.isCylSmooth_sub (hf m) (hf n)
    have hgysmooth := UnforcedLeray.TrainB.isCylSmooth_sub (hg m) (hg n)
    have hfxdiff : UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith [hc1]) (fun z => f m z - f n z) hfxsmooth = xseq m - xseq n := by
      calc
        _ = UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
            (by linarith [hc1]) (f m) (hf m) -
          UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
            (by linarith [hc1]) (f n) (hf n) :=
              ofCylSmooth3_sub_eq (by linarith [hc1]) (hf m) (hf n)
        _ = xseq m - xseq n := by rw [← hxrep m, ← hxrep n]
    have hgydiff : UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith [hc1]) (fun z => g m z - g n z) hgysmooth = yseq m - yseq n := by
      calc
        _ = UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
            (by linarith [hc1]) (g m) (hg m) -
          UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
            (by linarith [hc1]) (g n) (hg n) :=
              ofCylSmooth3_sub_eq (by linarith [hc1]) (hg m) (hg n)
        _ = yseq m - yseq n := by rw [← hyrep m, ← hyrep n]
    rw [hfxdiff, hgydiff, (hyrep m).symm, (hxrep n).symm] at hdiff
    change ‖pseq m - pseq n‖ ≤ _ at hdiff
    have hboundm : ‖yseq m‖ ≤ Cy := hCy _ (Set.mem_range_self m)
    have hboundn : ‖xseq n‖ ≤ Cx := hCx _ (Set.mem_range_self n)
    have hdx' : ‖xseq m - xseq n‖ < δ := by simpa [dist_eq_norm] using hdx
    have hdy' : ‖yseq m - yseq n‖ < δ := by simpa [dist_eq_norm] using hdy
    have hestimate : dist (pseq m) (pseq n) ≤
        384 * ‖xseq m - xseq n‖ * ‖yseq m‖ +
        384 * ‖xseq n‖ * ‖yseq m - yseq n‖ := by
      rw [dist_eq_norm]
      exact hdiff
    have hp : dist (pseq m) (pseq n) < ε := by
      calc
        dist (pseq m) (pseq n) ≤
            384 * ‖xseq m - xseq n‖ * ‖yseq m‖ +
            384 * ‖xseq n‖ * ‖yseq m - yseq n‖ := hestimate
        _ ≤ 384 * δ * Cy + 384 * Cx * δ := by
          gcongr
        _ = 384 * (Cx + Cy) * δ := by dsimp [δ]; ring
        _ < ε := by
          have hden : 0 < 384 * (Cx + Cy + 1) := by positivity
          have hfac : 384 * (Cx + Cy) < 384 * (Cx + Cy + 1) := by nlinarith
          have hratio : 0 < ε / (384 * (Cx + Cy + 1)) := div_pos hε hden
          have hmul := mul_lt_mul_of_pos_right hfac hratio
          calc
            384 * (Cx + Cy) * (ε / (384 * (Cx + Cy + 1))) <
                384 * (Cx + Cy + 1) * (ε / (384 * (Cx + Cy + 1))) := hmul
            _ = ε := by field_simp
    exact hp
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hboundP : ∀ n, ‖pseq n‖ ≤ 384 * ‖xseq n‖ * ‖yseq n‖ := by
    intro n
    change ‖UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
      (by linarith [hc1]) (fun z => f n z * g n z)
      (UnforcedLeray.TrainB.IsCylSmooth.mul (hf n) (hg n))‖ ≤ _
    rw [hxrep n, hyrep n]
    exact smooth_h3_scalar_mul_norm_explicit hc1 (hf n) (hg n)
  have hnormP : Tendsto (fun n => ‖pseq n‖) atTop (𝓝 ‖z‖) :=
    (continuous_norm.tendsto z).comp hz
  have hnormInputs : Tendsto (fun n => 384 * ‖xseq n‖ * ‖yseq n‖) atTop
      (𝓝 (384 * ‖x‖ * ‖y‖)) := by
    simpa [mul_assoc] using (hxlim.norm.mul hylim.norm).const_mul 384
  have hzbound : ‖z‖ ≤ 384 * ‖x‖ * ‖y‖ :=
    le_of_tendsto_of_tendsto hnormP hnormInputs (Eventually.of_forall hboundP)
  let V3 := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
  let μ := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
  have hpLp : Tendsto (fun n => V3 (pseq n)) atTop (𝓝 (V3 z)) :=
    (V3.continuous.tendsto z).comp hz
  have hpMeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hpLp
  obtain ⟨ns, hns, hpconv⟩ := hpMeasure.exists_seq_tendsto_ae
  have hpRep (n : ℕ) : (fun q => (Fseq n * Gseq n) q) =ᵐ[μ] (V3 (pseq n)) := by
    have hval := UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2) (by linarith [hc1])
      (fun q => f n q * g n q) (UnforcedLeray.TrainB.IsCylSmooth.mul (hf n) (hg n))
    filter_upwards [hval] with q hq
    change Fseq n q * Gseq n q = V3 (pseq n) q
    rw [hFseq n q, hGseq n q]
    exact hq.symm
  have hpRepAll : ∀ᵐ q ∂μ, ∀ n, (Fseq n * Gseq n) q = V3 (pseq n) q := by
    rw [ae_all_iff]
    intro n
    exact hpRep n
  have hFG : Tendsto (fun n => Fseq n * Gseq n) atTop (𝓝 (F * G)) := hF.mul hG
  have hpAE : (V3 z : Plane → ℝ) =ᵐ[μ] (fun q => (F * G) q) := by
    filter_upwards [hpconv, hpRepAll] with q hconv hrep
    have hFGq : Tendsto (fun n => (Fseq n * Gseq n) q) atTop (𝓝 ((F * G) q)) :=
      ((continuous_eval_const q).tendsto (F * G)).comp hFG
    have hFGqsub := hFGq.comp hns.tendsto_atTop
    have hFGq' := hFGqsub.congr' (Filter.Eventually.of_forall fun k => hrep (ns k))
    exact tendsto_nhds_unique hconv hFGq'
  have hxAE : (F : Plane → ℝ) =ᵐ[μ] (V3 x) := by
    simpa [μ, scalarH2_measure_eq_cell] using hFae
  have hyAE : (G : Plane → ℝ) =ᵐ[μ] (V3 y) := by
    simpa [μ, scalarH2_measure_eq_cell] using hGae
  have hproductAE : (V3 z : Plane → ℝ) =ᵐ[μ]
      (fun q => V3 x q * V3 y q) := by
    filter_upwards [hpAE, hxAE, hyAE] with q hz hx hy
    calc
      V3 z q = (F * G) q := hz
      _ = F q * G q := rfl
      _ = V3 x q * V3 y q := by
        change F q * G q = V3 x q * V3 y q
        exact congrArg₂ (· * ·) hx hy
  have hproductCell : (V3 z : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun q => V3 x q * V3 y q) := by
    simpa [μ, scalarH2_measure_eq_cell] using hproductAE
  exact ⟨z, xseq, yseq, f, g, hf, hg, pseq, (fun n => rfl), hxrep, hyrep, hxlim, hylim,
    by simpa [pseq] using hz, hproductCell, hzbound⟩

/-- The completed weak H³ product exists as an actual graph element, with its value equal
almost everywhere to the pointwise product and with the sharp-in-this-proof 384 bound. -/
theorem exists_scalarH3_product {c : ℝ} (hc1 : 1 ≤ c) (x y : ScalarH3 c) :
    ∃ z : ScalarH3 c,
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 z : Plane → ℝ) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
        (fun q => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) q *
          (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 y) q) ∧
      ‖z‖ ≤ 384 * ‖x‖ * ‖y‖ := by
  obtain ⟨z, xseq, yseq, f, g, hf, hg, pseq, hpseq, hxrep, hyrep, hxlim, hylim,
      hplim, hvalue, hbound⟩ := exists_smooth_h3_product_limit hc1 x y
  exact ⟨z, hvalue, hbound⟩

/-- The scalar weak H³ product, selected from the concrete existence theorem. -/
noncomputable def scalarH3Mul {c : ℝ} (hc1 : 1 ≤ c) (x y : ScalarH3 c) : ScalarH3 c :=
  Classical.choose (exists_scalarH3_product hc1 x y)

theorem scalarH3Mul_value_ae {c : ℝ} (hc1 : 1 ≤ c) (x y : ScalarH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (scalarH3Mul hc1 x y) : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
      (fun q => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) q *
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 y) q) := by
  exact (Classical.choose_spec (exists_scalarH3_product hc1 x y)).1

theorem scalarH3Mul_norm_le {c : ℝ} (hc1 : 1 ≤ c) (x y : ScalarH3 c) :
    ‖scalarH3Mul hc1 x y‖ ≤ 384 * ‖x‖ * ‖y‖ :=
  (Classical.choose_spec (exists_scalarH3_product hc1 x y)).2

/-- Equality of H³ classes follows from a.e. equality of their values on the centered cell. -/
theorem scalarH3_eq_of_value_ae {c : ℝ} {u v : ScalarH3 c}
    (h : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 u : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 v : Plane → ℝ)) : u = v := by
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have h' : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 u : Plane → ℝ) =ᵐ[
        UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 v : Plane → ℝ) :=
    (congrArg (fun μ : Measure Plane =>
      ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 u : Plane → ℝ) =ᵐ[μ]
       (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 v : Plane → ℝ)))
      (scalarH2_measure_eq_cell c).symm).mp h
  exact h'

/-- The value map respects addition as an a.e. equality of representatives. -/
theorem scalarH3_value_add_ae {c : ℝ} (u v : ScalarH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (u + v) : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
      (fun q => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 u) q +
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 v) q) := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
  have hmap := congrArg (fun f : Lp ℝ 2 (UnforcedLeray.Sob.wμ
      (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) =>
      (f : Plane → ℝ)) (map_add V u v)
  have hLp : (V (u + v) : Plane → ℝ) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun q => (V u : Plane → ℝ) q + (V v : Plane → ℝ) q) := by
    filter_upwards [Lp.coeFn_add (V u) (V v)] with q hq
    exact congrArg (fun f : Plane → ℝ => f q) hmap |>.trans hq
  exact (congrArg (fun μ : Measure Plane =>
    ((V (u + v) : Plane → ℝ) =ᵐ[μ]
      (fun q => (V u : Plane → ℝ) q + (V v : Plane → ℝ) q)))
    (scalarH2_measure_eq_cell c)).mp hLp

/-- The value map respects scalar multiplication as an a.e. equality of representatives. -/
theorem scalarH3_value_smul_ae {c : ℝ} (a : ℝ) (u : ScalarH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (a • u) : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
      (fun q => a • (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 u) q) := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
  have hmap := congrArg (fun f : Lp ℝ 2 (UnforcedLeray.Sob.wμ
      (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) =>
      (f : Plane → ℝ)) (map_smul V a u)
  have hLp : (V (a • u) : Plane → ℝ) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun q => a • (V u : Plane → ℝ) q) := by
    filter_upwards [Lp.coeFn_smul a (V u)] with q hq
    exact congrArg (fun f : Plane → ℝ => f q) hmap |>.trans hq
  exact (congrArg (fun μ : Measure Plane =>
    ((V (a • u) : Plane → ℝ) =ᵐ[μ] (fun q => a • (V u : Plane → ℝ) q)))
    (scalarH2_measure_eq_cell c)).mp hLp

theorem scalarH3Mul_add_left {c : ℝ} (hc1 : 1 ≤ c) (x₁ x₂ y : ScalarH3 c) :
    scalarH3Mul hc1 (x₁ + x₂) y = scalarH3Mul hc1 x₁ y + scalarH3Mul hc1 x₂ y := by
  apply scalarH3_eq_of_value_ae
  have h0 := scalarH3Mul_value_ae hc1 (x₁ + x₂) y
  have h1 := scalarH3Mul_value_ae hc1 x₁ y
  have h2 := scalarH3Mul_value_ae hc1 x₂ y
  have hi := scalarH3_value_add_ae x₁ x₂
  have ho := scalarH3_value_add_ae (scalarH3Mul hc1 x₁ y) (scalarH3Mul hc1 x₂ y)
  filter_upwards [h0, h1, h2, hi, ho] with q h0 h1 h2 hi ho
  rw [h0, hi, ho, h1, h2]
  ring

theorem scalarH3Mul_smul_left {c : ℝ} (hc1 : 1 ≤ c) (a : ℝ) (x y : ScalarH3 c) :
    scalarH3Mul hc1 (a • x) y = a • scalarH3Mul hc1 x y := by
  apply scalarH3_eq_of_value_ae
  have h0 := scalarH3Mul_value_ae hc1 (a • x) y
  have h1 := scalarH3Mul_value_ae hc1 x y
  have hi := scalarH3_value_smul_ae a x
  have ho := scalarH3_value_smul_ae a (scalarH3Mul hc1 x y)
  filter_upwards [h0, h1, hi, ho] with q h0 h1 hi ho
  rw [h0, hi, ho, h1]
  simp only [smul_eq_mul]
  ring

theorem scalarH3Mul_add_right {c : ℝ} (hc1 : 1 ≤ c) (x y₁ y₂ : ScalarH3 c) :
    scalarH3Mul hc1 x (y₁ + y₂) = scalarH3Mul hc1 x y₁ + scalarH3Mul hc1 x y₂ := by
  apply scalarH3_eq_of_value_ae
  have h0 := scalarH3Mul_value_ae hc1 x (y₁ + y₂)
  have h1 := scalarH3Mul_value_ae hc1 x y₁
  have h2 := scalarH3Mul_value_ae hc1 x y₂
  have hi := scalarH3_value_add_ae y₁ y₂
  have ho := scalarH3_value_add_ae (scalarH3Mul hc1 x y₁) (scalarH3Mul hc1 x y₂)
  filter_upwards [h0, h1, h2, hi, ho] with q h0 h1 h2 hi ho
  rw [h0, hi, ho, h1, h2]
  ring

theorem scalarH3Mul_smul_right {c : ℝ} (hc1 : 1 ≤ c) (a : ℝ) (x y : ScalarH3 c) :
    scalarH3Mul hc1 x (a • y) = a • scalarH3Mul hc1 x y := by
  apply scalarH3_eq_of_value_ae
  have h0 := scalarH3Mul_value_ae hc1 x (a • y)
  have h1 := scalarH3Mul_value_ae hc1 x y
  have hi := scalarH3_value_smul_ae a y
  have ho := scalarH3_value_smul_ae a (scalarH3Mul hc1 x y)
  filter_upwards [h0, h1, hi, ho] with q h0 h1 hi ho
  rw [h0, hi, ho, h1]
  simp only [smul_eq_mul]
  ring

/-- The weak scalar H³ product is a genuine bounded bilinear map, with the coefficient retained
from the ordered-word graph estimate. -/
def scalarH3Bilinear {c : ℝ} (hc1 : 1 ≤ c) :
    ScalarH3 c →L[ℝ] ScalarH3 c →L[ℝ] ScalarH3 c :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (scalarH3Mul hc1)
      (fun x₁ x₂ y => scalarH3Mul_add_left hc1 x₁ x₂ y)
      (fun a x y => scalarH3Mul_smul_left hc1 a x y)
      (fun x y₁ y₂ => scalarH3Mul_add_right hc1 x y₁ y₂)
      (fun a x y => scalarH3Mul_smul_right hc1 a x y))
    384 (fun x y => by simpa using scalarH3Mul_norm_le hc1 x y)

#print axioms UnforcedLeray.TrainB.scalarH3Bilinear

#print axioms UnforcedLeray.TrainB.exists_smooth_h3_product_limit
#print axioms UnforcedLeray.TrainB.exists_scalarH3_product
#print axioms UnforcedLeray.TrainB.scalarH3Mul_value_ae
#print axioms UnforcedLeray.TrainB.forgetH3toH2_ofCylSmooth
#print axioms UnforcedLeray.TrainB.exists_h3_uniform_representative_sequence


end UnforcedLeray.TrainB
