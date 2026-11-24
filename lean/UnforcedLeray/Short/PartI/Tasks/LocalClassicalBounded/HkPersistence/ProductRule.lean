import UnforcedLeray.Short.PartI.Sub.T02_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.TensorRule
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.OrbitDeriv

/-!
# Part I, task `PartI:T02/1/2/3`: product rule for the polarised Duhamel map (conditional)

Target `bilDuhamelDerivative : BilDuhamelDerivative` (`Short/PartI/Sub/T02_1_2.lean`).
Source of record: `the November 2 reference manuscript`, lines 261-288.

The target is reduced to two explicit leaves:

* `BdpTensorProductRule` (ingredient (i)): the weak product rule for `tensorH3Bilinear` on the
  periodic cylinder.
* `BdpOrbitWeakDeriv` (ingredient (ii)): the weak `∂_j`-derivative commutes with the age-`θ` map
  `G ↦ P₀ e^{θΔ} div G` on tensor `H³` elements.

Proved here, with neither leaf used inside a proof of a helper: the weak derivative of a Bochner
integral of `H³`-valued integrands (`bdp_hasWeakDeriv_integral`), the additivity of the orbit
(`bdp_orb_add`), the unfolding of `bilDuhamel` at a time (`bdp_bilDuhamel_apply`), and the
assembly `bilDuhamelDerivative_of`. The target is `bilDuhamelDerivative_of` applied to the two
leaves.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-! ### The two analytic leaves -/

/-- **Leaf (i)** (weak product rule on the periodic cylinder): if `x, y ∈ H³` have weak
`∂_j`-derivatives `x', y' ∈ H³`, then `x ⊗ y` has the weak `∂_j`-derivative `x' ⊗ y + x ⊗ y'`. -/
def BdpTensorProductRule : Prop :=
  ∀ (c : ℝ) (hc1 : 1 ≤ c) (j : Fin 2) (x x' y y' : VectorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → Vec) (Cyl.H.val y' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (tensorH3Bilinear hc1 x y) : Plane → TensorVal)
      (Cyl.H.val (tensorH3Bilinear hc1 x' y + tensorH3Bilinear hc1 x y') : Plane → TensorVal)

/-- **Leaf (ii)** (`∂_j` commutes with the projected heat-divergence orbit): for each age `θ > 0`
the map `G ↦ P₀ e^{θΔ} div G` on tensor `H³` elements carries weak `∂_j`-derivative pairs to
weak `∂_j`-derivative pairs. -/
def BdpOrbitWeakDeriv : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (θ : ℝ) (_hθ : 0 < θ) (j : Fin 2) (G G' : TensorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val G : Plane → TensorVal) (Cyl.H.val G' : Plane → TensorVal) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (P0H3CLM hc (actualHeatDivH3Orbit hc G θ)) : Plane → Vec)
      (Cyl.H.val (P0H3CLM hc (actualHeatDivH3Orbit hc G' θ)) : Plane → Vec)

/-! ### Weak derivatives of Bochner integrals -/

/-- The pairing of a Bochner integral in `H³` with a compactly bounded test is the integral of the
pairings. -/
theorem bdp_pair_integral {c : ℝ} {ψ : Plane → ℝ}
    (hψ : Sob.CompactlyBounded (Sob.cylinder c).μ ψ)
    {S : Set ℝ} {f : ℝ → VectorH3 c} (hf : Integrable f (volume.restrict S)) :
    ∫ x, ψ x • (Cyl.H.val (∫ r in S, f r) : Plane → Vec) x ∂(Sob.cylinder c).μ =
      ∫ r in S, ∫ x, ψ x • (Cyl.H.val (f r) : Plane → Vec) x ∂(Sob.cylinder c).μ := by
  have hV : Cyl.H.val (∫ r in S, f r) = ∫ r in S, Cyl.H.val (f r) :=
    (ContinuousLinearMap.integral_comp_comm (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2) hf).symm
  have hvi : Integrable (fun r => Cyl.H.val (f r)) (volume.restrict S) :=
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2).integrable_comp hf
  have hpair : ∀ g : VectorH3 c,
      ∫ x, ψ x • (Cyl.H.val g : Plane → Vec) x ∂(Sob.cylinder c).μ =
        Sob.testPair (𝕜 := ℝ) (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) 2 ψ hψ (Cyl.H.val g) :=
    fun g => (Sob.testPair_apply (𝕜 := ℝ) 2 ψ hψ (Cyl.H.val g)).symm
  rw [hpair, hV, ← ContinuousLinearMap.integral_comp_comm (Sob.testPair (𝕜 := ℝ) (Sob.cylinder c).μ
    (Cyl.ρwW c ^ (0 : ℝ)) 2 ψ hψ) hvi]
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  exact (hpair (f r)).symm

/-- **Weak derivative of a Bochner integral** in `H³`: if the integrands have weak `∂_j`-derivatives
pointwise on `S`, the integral has the integral of the derivatives as weak `∂_j`-derivative. -/
theorem bdp_hasWeakDeriv_integral {c : ℝ} (j : Fin 2) {S : Set ℝ} (hS : MeasurableSet S)
    {f g : ℝ → VectorH3 c} (hf : Integrable f (volume.restrict S))
    (hg : Integrable g (volume.restrict S))
    (hw : ∀ r ∈ S, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (f r) : Plane → Vec) (Cyl.H.val (g r) : Plane → Vec)) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (∫ r in S, f r) : Plane → Vec) (Cyl.H.val (∫ r in S, g r) : Plane → Vec) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact Sob.integrable_smul_of_memLp
      (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ [(Sob.cylinder c).dir j]))
      (Lp.memLp _)
  · exact Sob.integrable_smul_of_memLp (Sob.CompactlyBounded.of_adm hφ) (Lp.memLp _)
  · rw [bdp_pair_integral
        (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ [(Sob.cylinder c).dir j]))
        hf,
      bdp_pair_integral (Sob.CompactlyBounded.of_adm hφ) hg, ← integral_smul]
    refine setIntegral_congr_fun hS (fun r hr => ?_)
    exact (hw r hr).identity φ hφ

/-- The negative of the value of an `H³` element is the value of its negative, almost everywhere. -/
theorem bdp_coe_neg_ae {c : ℝ} (x : VectorH3 c) :
    -(Cyl.H.val x : Plane → Vec) =ᵐ[(Sob.cylinder c).μ] (Cyl.H.val (-x) : Plane → Vec) := by
  have h := (Lp.coeFn_neg (Cyl.H.val x)).symm
  have e : Cyl.H.val (-x) = -Cyl.H.val x :=
    map_neg (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2) x
  rw [e]
  exact (Sob.ae_eq_wμ_iff _ _).mp h

/-! ### The projected heat-divergence orbit -/

/-- The age-`θ` orbit is additive in the tensor argument for `θ > 0`. -/
theorem bdp_P0_orbit_add {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (G H : TensorH3 c) :
    P0H3CLM hc (actualHeatDivH3Orbit hc (G + H) θ) =
      P0H3CLM hc (actualHeatDivH3Orbit hc G θ) + P0H3CLM hc (actualHeatDivH3Orbit hc H θ) := by
  simp only [actualHeatDivH3Orbit, dif_pos hθ, map_add]

/-- The projected Duhamel orbit is additive in the tensor path at each positive age. -/
theorem bdp_orb_add {c ν s : ℝ} (hc : 0 < c) (F G : ℝ → TensorH3 c) (r : ℝ)
    (hθ : 0 < ν * (s - r)) :
    projectedHeatDuhamelOrbit (ν := ν) (s := s) hc (fun q => F q + G q) r =
      projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F r +
        projectedHeatDuhamelOrbit (ν := ν) (s := s) hc G r :=
  bdp_P0_orbit_add hc hθ (F r) (G r)

/-- The projected Duhamel orbit of a bounded continuous tensor path is integrable on `(0, s)`
(the empty interval is trivial). -/
theorem bdp_integrable_orb {c ν s M : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (F : ContinuousMap ℝ (TensorH3 c)) (hbound : ∀ r ∈ Ioo (0 : ℝ) s, ‖F r‖ ≤ M) :
    Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F)
      (volume.restrict (Ioo (0 : ℝ) s)) := by
  rcases lt_or_ge 0 s with hs | hs
  · exact integrableOn_projectedHeatDuhamelOrbit hc hν hs F hbound
  · rw [Ioo_eq_empty (not_lt.mpr hs), Measure.restrict_empty]
    exact integrable_zero_measure

/-! ### The stress path of two `H³`-valued paths -/

/-- The tensor stress path `r ↦ a(r) ⊗ b(r)` of two `MPath`s, extended by constants. -/
def bdpStress {c T : ℝ} (hc1 : 1 ≤ c) (hT : 0 ≤ T) (x y : MPath c T) :
    ContinuousMap ℝ (TensorH3 c) :=
  bilStressPath hc1 (extendCompactPath hT x) (extendCompactPath hT y)

/-- The stress path has the uniform bound `1536 ‖x‖ ‖y‖`. -/
theorem bdp_norm_stress_le {c T : ℝ} (hc1 : 1 ≤ c) (hT : 0 ≤ T) (x y : MPath c T) (r : ℝ) :
    ‖bdpStress hc1 hT x y r‖ ≤ 1536 * ‖x‖ * ‖y‖ := by
  change ‖tensorH3Bilinear hc1 (extendCompactPath hT x r) (extendCompactPath hT y r)‖ ≤ _
  calc _ ≤ 1536 * ‖extendCompactPath hT x r‖ * ‖extendCompactPath hT y r‖ :=
        norm_tensorH3Bilinear_apply_le hc1 _ _
    _ ≤ 1536 * ‖x‖ * ‖y‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_extendCompactPath_le hT x r) (by norm_num))
          (norm_extendCompactPath_le hT y r) (norm_nonneg _)
          (mul_nonneg (by norm_num) (norm_nonneg _))

/-- Unfolding the polarised Duhamel map at a time is the negated Bochner integral of the orbit of
the stress path over `(0, t)`. -/
theorem bdp_bilDuhamel_apply {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (x y : MPath c T) (t : Icc (0 : ℝ) T) :
    bilDuhamel hc hc1 hν hT x y t =
      -(∫ r in Ioo (0 : ℝ) (t : ℝ),
        projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc (bdpStress hc1 hT x y) r) :=
  rfl

/-- Pointwise product rule for the stress path, using the paths' derivative paths on `[0,T]`. -/
theorem bdp_stress_deriv {c T : ℝ} (hP : BdpTensorProductRule) (hc1 : 1 ≤ c) (j : Fin 2)
    (hT0 : 0 ≤ T) (a a' b b' : MPath c T)
    (ha : HasDerivPath c T j a a') (hb : HasDerivPath c T j b b') (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) T) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (bdpStress hc1 hT0 a b r) : Plane → TensorVal)
      (Cyl.H.val ((bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b') r) : Plane → TensorVal) := by
  have ea : extendCompactPath hT0 a r = a ⟨r, hr⟩ := extendCompactPath_apply_of_mem hT0 a hr
  have eb : extendCompactPath hT0 b r = b ⟨r, hr⟩ := extendCompactPath_apply_of_mem hT0 b hr
  have ea' : extendCompactPath hT0 a' r = a' ⟨r, hr⟩ := extendCompactPath_apply_of_mem hT0 a' hr
  have eb' : extendCompactPath hT0 b' r = b' ⟨r, hr⟩ := extendCompactPath_apply_of_mem hT0 b' hr
  show Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (tensorH3Bilinear hc1 (extendCompactPath hT0 a r)
        (extendCompactPath hT0 b r)) : Plane → TensorVal)
      (Cyl.H.val (tensorH3Bilinear hc1 (extendCompactPath hT0 a' r)
        (extendCompactPath hT0 b r) + tensorH3Bilinear hc1 (extendCompactPath hT0 a r)
        (extendCompactPath hT0 b' r)) : Plane → TensorVal)
  rw [ea, eb, ea', eb']
  exact hP c hc1 j _ _ _ _ (ha ⟨r, hr⟩) (hb ⟨r, hr⟩)

/-! ### Assembly: the target from the two leaves -/

/-- **The product rule for the polarised Duhamel map** (`BilDuhamelDerivative`), from the two
leaves `BdpTensorProductRule` and `BdpOrbitWeakDeriv`. -/
theorem bilDuhamelDerivative_of (hP : BdpTensorProductRule) (hO : BdpOrbitWeakDeriv) :
    BilDuhamelDerivative := by
  intro ν c T hν hc hc1 hT j a a' b b' ha hb t
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hsT : (t : ℝ) ≤ T := t.2.2
  have hS : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ), r ∈ Icc (0 : ℝ) T :=
    fun r hr => ⟨hr.1.le, hr.2.le.trans hsT⟩
  have hw0 : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ),
      Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
        (Cyl.H.val (bdpStress hc1 hT0 a b r) : Plane → TensorVal)
        (Cyl.H.val ((bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b') r) : Plane → TensorVal) :=
    fun r hr => bdp_stress_deriv hP hc1 j hT0 a a' b b' ha hb r (hS r hr)
  have hO' : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ),
      Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
        (Cyl.H.val (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
          (bdpStress hc1 hT0 a b) r) : Plane → Vec)
        (Cyl.H.val (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
          (bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b') r) : Plane → Vec) :=
    fun r hr => hO c hc (ν * ((t : ℝ) - r)) (mul_pos hν (sub_pos.2 hr.2)) j _ _ (hw0 r hr)
  have hI0 : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
      (bdpStress hc1 hT0 a b)) (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
    bdp_integrable_orb hc hν (bdpStress hc1 hT0 a b) (M := 1536 * ‖a‖ * ‖b‖)
      (fun r _ => bdp_norm_stress_le hc1 hT0 a b r)
  have hI1 : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
      (bdpStress hc1 hT0 a' b)) (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
    bdp_integrable_orb hc hν (bdpStress hc1 hT0 a' b) (M := 1536 * ‖a'‖ * ‖b‖)
      (fun r _ => bdp_norm_stress_le hc1 hT0 a' b r)
  have hI2 : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
      (bdpStress hc1 hT0 a b')) (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
    bdp_integrable_orb hc hν (bdpStress hc1 hT0 a b') (M := 1536 * ‖a‖ * ‖b'‖)
      (fun r _ => bdp_norm_stress_le hc1 hT0 a b' r)
  have hI3 : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
      (bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b'))
      (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
    bdp_integrable_orb hc hν (bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b')
      (M := 1536 * ‖a'‖ * ‖b‖ + 1536 * ‖a‖ * ‖b'‖) (fun r _ =>
        (norm_add_le (bdpStress hc1 hT0 a' b r) (bdpStress hc1 hT0 a b' r)).trans
          (add_le_add (bdp_norm_stress_le hc1 hT0 a' b r) (bdp_norm_stress_le hc1 hT0 a b' r)))
  have hsplit : ∫ r in Ioo (0 : ℝ) (t : ℝ), projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
        (bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b') r =
      (∫ r in Ioo (0 : ℝ) (t : ℝ), projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
        (bdpStress hc1 hT0 a' b) r) +
      ∫ r in Ioo (0 : ℝ) (t : ℝ), projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
        (bdpStress hc1 hT0 a b') r := by
    rw [← integral_add hI1 hI2]
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    exact bdp_orb_add hc _ _ r (mul_pos hν (sub_pos.2 hr.2))
  have hD := bdp_hasWeakDeriv_integral j measurableSet_Ioo hI0 hI3 hO'
  have hR : (bilDuhamel hc hc1 hν hT.le a' b + bilDuhamel hc hc1 hν hT.le a b') t =
      -(∫ r in Ioo (0 : ℝ) (t : ℝ), projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc
        (bdpStress hc1 hT0 a' b + bdpStress hc1 hT0 a b') r) := by
    rw [ContinuousMap.add_apply, bdp_bilDuhamel_apply, bdp_bilDuhamel_apply, hsplit, neg_add]
  rw [bdp_bilDuhamel_apply hc hc1 hν hT.le a b t, hR]
  exact (hD.neg).congr_ae (bdp_coe_neg_ae _) (bdp_coe_neg_ae _)

/-! ### Target: the product rule for the polarised Duhamel map -/

/-- **The product rule for the polarised Duhamel map** (`BilDuhamelDerivative`), from the
weak product rule `bdp_tensorProductRule` (ingredient (i)) and the orbit derivative
`bdp_orbitWeakDeriv` (ingredient (ii)). -/
theorem bilDuhamelDerivative : BilDuhamelDerivative :=
  bilDuhamelDerivative_of bdp_tensorProductRule bdp_orbitWeakDeriv

end UnforcedLeray.Short.PartI
