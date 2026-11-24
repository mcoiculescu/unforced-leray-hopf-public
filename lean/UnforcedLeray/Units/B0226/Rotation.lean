import UnforcedLeray.Units.B0226.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-!
# B0226, part 6: rotations about the axis and the angular averaging identity

Blueprint unit B0226, `paper/main.tex` lines 3394–3402, proof outline ("for the distributional
version, pair with axisymmetric test functions"). This file supplies the angular averaging used
to reduce the divergence pairing of an axisymmetric field against an arbitrary test of
`ℝ³ × period` to pairings against axisymmetric tests (file `B0226/AxisTests.lean`).

* `rotPt θ r z = (r cos θ, r sin θ, z)`: the point with cylindrical coordinates `(r, θ, z)`;
  every point is of this form with `r = radius x` (`exists_rotPt_eq`).
* `rotZ α`: the rotation by `α` about the axis, a linear isometry of `ℝ³`;
  `rotZ α (rotPt β r z) = rotPt (α + β) r z` (`rotZ_rotPt`).
* `integral_eq_rotPt_average` (the averaging identity): for `G` measurable and integrable on one
  period of `ℝ³ × ℝ`,
  `∫ G dx dτ = (2π)⁻¹ ∫_{(0,2π]} ∫ G(rotPt θ (radius x) x₃, τ) dx dτ dθ`.
  Proof: rotations preserve the measure, so `2π ∫ G = ∫_α ∫ G(R_α x, τ)`; Fubini; for fixed
  `x = rotPt β r z` the inner `α`-integral of `G(R_α x)` equals the `θ`-integral of
  `G(rotPt θ r z)` by `2π`-periodicity; Fubini again.

The periodic shift lemmas `setLIntegral_Ioc_add_periodic`, `setIntegral_Ioc_add_periodic` follow
Mathlib's `Function.Periodic.intervalIntegral_add_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Function
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-! ### Periodic shifts on one period -/

theorem setLIntegral_Ioc_add_periodic {f : ℝ → ℝ≥0∞} {T : ℝ} (hT : 0 < T) (hf : Periodic f T)
    (β : ℝ) : ∫⁻ α in Ioc 0 T, f (α + β) = ∫⁻ θ in Ioc 0 T, f θ := by
  have h1 : ∫⁻ α in Ioc 0 T, f (α + β) = ∫⁻ θ in Ioc β (β + T), f θ := by
    have := (measurePreserving_add_right (volume : Measure ℝ) β).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight β) f (Ioc β (β + T))
    rwa [preimage_add_const_Ioc, sub_self, add_sub_cancel_left] at this
  rw [h1]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  have h2 := IsAddFundamentalDomain.setLIntegral_eq (isAddFundamentalDomain_Ioc hT β)
    (isAddFundamentalDomain_Ioc hT 0) f hf.map_vadd_zmultiples
  rwa [zero_add] at h2

theorem setIntegral_Ioc_add_periodic {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : Periodic f T)
    (β : ℝ) : ∫ α in Ioc 0 T, f (α + β) = ∫ θ in Ioc 0 T, f θ := by
  have h1 : ∫ α in Ioc 0 T, f (α + β) = ∫ θ in Ioc β (β + T), f θ := by
    have := (measurePreserving_add_right (volume : Measure ℝ) β).setIntegral_preimage_emb
      (measurableEmbedding_addRight β) f (Ioc β (β + T))
    rwa [preimage_add_const_Ioc, sub_self, add_sub_cancel_left] at this
  rw [h1]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  have h2 := IsAddFundamentalDomain.setIntegral_eq (isAddFundamentalDomain_Ioc hT β)
    (isAddFundamentalDomain_Ioc hT 0) hf.map_vadd_zmultiples
  rwa [zero_add] at h2

/-! ### Cylindrical points and rotations about the axis -/

/-- The point with cylindrical coordinates `(r, θ, z)`: `(r cos θ, r sin θ, z)`. -/
def rotPt (θ r z : ℝ) : Space := !₂[r * cos θ, r * sin θ, z]

@[simp] theorem rotPt_apply_zero (θ r z : ℝ) : rotPt θ r z 0 = r * cos θ := rfl
@[simp] theorem rotPt_apply_one (θ r z : ℝ) : rotPt θ r z 1 = r * sin θ := rfl
@[simp] theorem rotPt_apply_two (θ r z : ℝ) : rotPt θ r z 2 = z := rfl

theorem space_eq_comb (v : Space) :
    v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 + v 2 • coordinateVector 2 := by
  ext i
  fin_cases i <;> simp [coordinateVector]

theorem rotPt_eq_comb (θ r z : ℝ) :
    rotPt θ r z = (r * cos θ) • coordinateVector 0 + (r * sin θ) • coordinateVector 1 +
      z • coordinateVector 2 :=
  space_eq_comb _

theorem rotPt_add_two_pi (θ r z : ℝ) : rotPt (θ + 2 * π) r z = rotPt θ r z := by
  simp only [rotPt, cos_add_two_pi, sin_add_two_pi]

theorem axisSq_rotPt (θ r z : ℝ) : rotPt θ r z 0 ^ 2 + rotPt θ r z 1 ^ 2 = r ^ 2 := by
  simp only [rotPt_apply_zero, rotPt_apply_one]
  linear_combination r ^ 2 * sin_sq_add_cos_sq θ

theorem radius_rotPt {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : radius (rotPt θ r z) = r := by
  rw [radius, axisSq_rotPt, Real.sqrt_sq hr]

theorem exists_rotPt_eq (x : Space) : ∃ β : ℝ, rotPt β (radius x) (x 2) = x := by
  let w : ℂ := ⟨x 0, x 1⟩
  refine ⟨Complex.arg w, ?_⟩
  have hn : ‖w‖ = radius x := by
    rw [Complex.norm_def, Complex.normSq_mk, radius]
    congr 1
    ring
  have h0 := Complex.norm_mul_cos_arg w
  have h1 := Complex.norm_mul_sin_arg w
  rw [hn] at h0 h1
  have e0 : rotPt (Complex.arg w) (radius x) (x 2) 0 = x 0 := h0
  have e1 : rotPt (Complex.arg w) (radius x) (x 2) 1 = x 1 := h1
  have e2 : rotPt (Complex.arg w) (radius x) (x 2) 2 = x 2 := rfl
  ext i
  fin_cases i
  exacts [e0, e1, e2]

/-- The rotation by `α` about the axis, as a map. -/
def rotFun (α : ℝ) (x : Space) : Space :=
  !₂[cos α * x 0 - sin α * x 1, sin α * x 0 + cos α * x 1, x 2]

@[simp] theorem rotFun_apply_zero (α : ℝ) (x : Space) :
    rotFun α x 0 = cos α * x 0 - sin α * x 1 := rfl
@[simp] theorem rotFun_apply_one (α : ℝ) (x : Space) :
    rotFun α x 1 = sin α * x 0 + cos α * x 1 := rfl
@[simp] theorem rotFun_apply_two (α : ℝ) (x : Space) : rotFun α x 2 = x 2 := rfl

theorem rotFun_inv (α : ℝ) (x : Space) : rotFun (-α) (rotFun α x) = x := by
  have e0 : rotFun (-α) (rotFun α x) 0 = x 0 := by
    simp only [rotFun_apply_zero, rotFun_apply_one, cos_neg, sin_neg]
    linear_combination x 0 * sin_sq_add_cos_sq α
  have e1 : rotFun (-α) (rotFun α x) 1 = x 1 := by
    simp only [rotFun_apply_zero, rotFun_apply_one, cos_neg, sin_neg]
    linear_combination x 1 * sin_sq_add_cos_sq α
  have e2 : rotFun (-α) (rotFun α x) 2 = x 2 := rfl
  ext i
  fin_cases i
  exacts [e0, e1, e2]

theorem rotFun_add (α : ℝ) (x y : Space) : rotFun α (x + y) = rotFun α x + rotFun α y := by
  have e0 : rotFun α (x + y) 0 = (rotFun α x + rotFun α y) 0 := by
    simp only [rotFun_apply_zero, PiLp.add_apply]
    ring
  have e1 : rotFun α (x + y) 1 = (rotFun α x + rotFun α y) 1 := by
    simp only [rotFun_apply_one, PiLp.add_apply]
    ring
  have e2 : rotFun α (x + y) 2 = (rotFun α x + rotFun α y) 2 := by
    simp only [rotFun_apply_two, PiLp.add_apply]
  ext i
  fin_cases i
  exacts [e0, e1, e2]

theorem rotFun_smul (α a : ℝ) (x : Space) : rotFun α (a • x) = a • rotFun α x := by
  have e0 : rotFun α (a • x) 0 = (a • rotFun α x) 0 := by
    simp only [rotFun_apply_zero, PiLp.smul_apply, smul_eq_mul]
    ring
  have e1 : rotFun α (a • x) 1 = (a • rotFun α x) 1 := by
    simp only [rotFun_apply_one, PiLp.smul_apply, smul_eq_mul]
    ring
  have e2 : rotFun α (a • x) 2 = (a • rotFun α x) 2 := by
    simp only [rotFun_apply_two, PiLp.smul_apply, smul_eq_mul]
  ext i
  fin_cases i
  exacts [e0, e1, e2]

theorem norm_rotFun (α : ℝ) (x : Space) : ‖rotFun α x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [rotFun_apply_zero, rotFun_apply_one, rotFun_apply_two]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * sin_sq_add_cos_sq α

/-- The rotation `R_α` by `α` about the axis, a linear isometry of `ℝ³` fixing `e₃`. -/
def rotZ (α : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotFun α
  invFun := rotFun (-α)
  map_add' := rotFun_add α
  map_smul' := rotFun_smul α
  left_inv := rotFun_inv α
  right_inv x := by
    have h := rotFun_inv (-α) x
    rwa [neg_neg] at h
  norm_map' := norm_rotFun α

theorem rotZ_apply (α : ℝ) (x : Space) : rotZ α x = rotFun α x := rfl

theorem rotZ_rotPt (α β r z : ℝ) : rotZ α (rotPt β r z) = rotPt (α + β) r z := by
  have e0 : rotZ α (rotPt β r z) 0 = rotPt (α + β) r z 0 := by
    simp only [rotZ_apply, rotFun_apply_zero, rotPt_apply_zero, rotPt_apply_one, cos_add]
    ring
  have e1 : rotZ α (rotPt β r z) 1 = rotPt (α + β) r z 1 := by
    simp only [rotZ_apply, rotFun_apply_one, rotPt_apply_zero, rotPt_apply_one, sin_add]
    ring
  have e2 : rotZ α (rotPt β r z) 2 = rotPt (α + β) r z 2 := rfl
  ext i
  fin_cases i
  exacts [e0, e1, e2]

theorem rotFun_eq_comb (α : ℝ) (x : Space) :
    rotFun α x = (cos α * x 0 - sin α * x 1) • coordinateVector 0 +
      (sin α * x 0 + cos α * x 1) • coordinateVector 1 + x 2 • coordinateVector 2 :=
  space_eq_comb _

theorem continuous_rotZ_param :
    Continuous fun p : ℝ × (Space × ℝ) => ((rotZ p.1 p.2.1, p.2.2) : Space × ℝ) := by
  have h : (fun p : ℝ × (Space × ℝ) => ((rotZ p.1 p.2.1, p.2.2) : Space × ℝ)) =
      fun p => ((cos p.1 * p.2.1 0 - sin p.1 * p.2.1 1) • coordinateVector 0 +
        (sin p.1 * p.2.1 0 + cos p.1 * p.2.1 1) • coordinateVector 1 +
          p.2.1 2 • coordinateVector 2, p.2.2) := by
    funext p
    rw [rotZ_apply, rotFun_eq_comb]
  rw [h]
  fun_prop

theorem continuous_rotPt_param :
    Continuous fun p : ℝ × (Space × ℝ) =>
      ((rotPt p.1 (radius p.2.1) (p.2.1 2), p.2.2) : Space × ℝ) := by
  have h : (fun p : ℝ × (Space × ℝ) =>
      ((rotPt p.1 (radius p.2.1) (p.2.1 2), p.2.2) : Space × ℝ)) =
      fun p => ((radius p.2.1 * cos p.1) • coordinateVector 0 +
        (radius p.2.1 * sin p.1) • coordinateVector 1 + p.2.1 2 • coordinateVector 2,
          p.2.2) := by
    funext p
    rw [rotPt_eq_comb]
  rw [h]
  have hr : Continuous radius := continuous_radius
  fun_prop

/-! ### Rotations preserve the measure of one period -/

/-- `(x, τ) ↦ (R_α x, τ)` as a homeomorphism. -/
def rotProd (α : ℝ) : (Space × ℝ) ≃ₜ (Space × ℝ) :=
  (rotZ α).toHomeomorph.prodCongr (Homeomorph.refl ℝ)

theorem rotProd_apply (α : ℝ) (y : Space × ℝ) : rotProd α y = (rotZ α y.1, y.2) := rfl

theorem measurePreserving_rotProd (α ε c : ℝ) :
    MeasurePreserving (rotProd α) (physMeasure ε c) (physMeasure ε c) := by
  have h : MeasurePreserving (rotProd α) (volume : Measure (Space × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact (rotZ α).measurePreserving.prod (MeasurePreserving.id volume)
  have hpre : (rotProd α) ⁻¹' physDomain ε c = physDomain ε c := by
    ext y
    simp [rotProd_apply, physDomain]
  have h2 := h.restrict_preimage (measurableSet_physDomain ε c)
  rwa [hpre] at h2

theorem integral_comp_rotZ (α ε c : ℝ) (G : Space × ℝ → ℝ) :
    ∫ y, G (rotZ α y.1, y.2) ∂physMeasure ε c = ∫ y, G y ∂physMeasure ε c :=
  (measurePreserving_rotProd α ε c).integral_comp (rotProd α).measurableEmbedding G

theorem lintegral_comp_rotZ (α ε c : ℝ) (G : Space × ℝ → ℝ≥0∞) :
    ∫⁻ y, G (rotZ α y.1, y.2) ∂physMeasure ε c = ∫⁻ y, G y ∂physMeasure ε c :=
  (measurePreserving_rotProd α ε c).lintegral_comp_emb (rotProd α).measurableEmbedding G

/-! ### The averaging identity -/

/-- For fixed `y`, rotating `y` by `α` is the cylindrical point at angle `α + β`. -/
theorem exists_rotZ_eq (y : Space × ℝ) :
    ∃ β : ℝ, ∀ α : ℝ, ((rotZ α y.1, y.2) : Space × ℝ) =
      (rotPt (α + β) (radius y.1) (y.1 2), y.2) := by
  obtain ⟨β, hβ⟩ := exists_rotPt_eq y.1
  refine ⟨β, fun α => ?_⟩
  conv_lhs => rw [← hβ]
  rw [rotZ_rotPt]

theorem periodic_rotPt_param {X : Type*} (F : Space × ℝ → X) (y : Space × ℝ) :
    Periodic (fun θ => F (rotPt θ (radius y.1) (y.1 2), y.2)) (2 * π) := fun θ => by
  simp only [rotPt_add_two_pi]

/-- **Angular averaging.** For `G` measurable and integrable on one period,
`∫ G dx dτ = (2π)⁻¹ ∫_{(0,2π]} ∫ G(rotPt θ (radius x) x₃, τ) dx dτ dθ`. -/
theorem integral_eq_rotPt_average {ε c : ℝ} {G : Space × ℝ → ℝ} (hGm : Measurable G)
    (hG : Integrable G (physMeasure ε c)) :
    ∫ y, G y ∂physMeasure ε c = (2 * π)⁻¹ *
      ∫ θ in Ioc 0 (2 * π), ∫ y, G (rotPt θ (radius y.1) (y.1 2), y.2) ∂physMeasure ε c := by
  set μ := physMeasure ε c with hμ
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hν
  have hT : 0 < 2 * π := by positivity
  have : SFinite μ := by
    rw [hμ, physMeasure]
    infer_instance
  set Ga : ℝ × (Space × ℝ) → ℝ := fun p => G (rotZ p.1 p.2.1, p.2.2) with hGa
  set Gt : ℝ × (Space × ℝ) → ℝ := fun p => G (rotPt p.1 (radius p.2.1) (p.2.1 2), p.2.2)
    with hGt
  have hGam : Measurable Ga := hGm.comp continuous_rotZ_param.measurable
  have hGtm : Measurable Gt := hGm.comp continuous_rotPt_param.measurable
  -- pointwise periodic shift, for every `y`
  have hc : ∀ y : Space × ℝ, ∫ α in Ioc 0 (2 * π), Ga (α, y) =
      ∫ θ in Ioc 0 (2 * π), Gt (θ, y) := by
    intro y
    obtain ⟨β, hβ⟩ := exists_rotZ_eq y
    simp only [hGa, hGt, hβ]
    exact setIntegral_Ioc_add_periodic hT (periodic_rotPt_param G y) β
  have hc' : ∀ y : Space × ℝ, ∫⁻ α in Ioc 0 (2 * π), ‖Ga (α, y)‖ₑ =
      ∫⁻ θ in Ioc 0 (2 * π), ‖Gt (θ, y)‖ₑ := by
    intro y
    obtain ⟨β, hβ⟩ := exists_rotZ_eq y
    simp only [hGa, hGt, hβ]
    exact setLIntegral_Ioc_add_periodic hT
      (periodic_rotPt_param (fun y => ‖G y‖ₑ) y) β
  -- integrability of `Ga` and `Gt` on `(0,2π] × period`
  have hGa_lint : ∫⁻ p, ‖Ga p‖ₑ ∂(ν.prod μ) < ∞ := by
    rw [lintegral_prod _ hGam.enorm.aemeasurable]
    have h1 : ∀ α : ℝ, ∫⁻ y, ‖Ga (α, y)‖ₑ ∂μ = ∫⁻ y, ‖G y‖ₑ ∂μ := fun α =>
      lintegral_comp_rotZ α ε c (fun y => ‖G y‖ₑ)
    simp_rw [h1]
    rw [lintegral_const, hν, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc]
    exact ENNReal.mul_lt_top hG.2 ENNReal.ofReal_lt_top
  have hGa_int : Integrable Ga (ν.prod μ) := ⟨hGam.aestronglyMeasurable, hGa_lint⟩
  have hGt_int : Integrable Gt (ν.prod μ) := by
    refine ⟨hGtm.aestronglyMeasurable, ?_⟩
    have e1 : ∫⁻ p, ‖Gt p‖ₑ ∂(ν.prod μ) = ∫⁻ p, ‖Ga p‖ₑ ∂(ν.prod μ) := by
      rw [lintegral_prod_symm _ hGtm.enorm.aemeasurable,
        lintegral_prod_symm _ hGam.enorm.aemeasurable]
      exact lintegral_congr fun y => (hc' y).symm
    change ∫⁻ p, ‖Gt p‖ₑ ∂(ν.prod μ) < ∞
    rw [e1]
    exact hGa_lint
  -- the main computation
  have ha : ∀ α : ℝ, ∫ y, Ga (α, y) ∂μ = ∫ y, G y ∂μ := fun α => integral_comp_rotZ α ε c G
  have key : (2 * π) * ∫ y, G y ∂μ = ∫ θ in Ioc 0 (2 * π), ∫ y, Gt (θ, y) ∂μ := by
    calc (2 * π) * ∫ y, G y ∂μ = ∫ α in Ioc 0 (2 * π), ∫ y, Ga (α, y) ∂μ := by
          simp_rw [ha]
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hT.le, sub_zero]
      _ = ∫ y, (∫ α in Ioc 0 (2 * π), Ga (α, y)) ∂μ :=
          integral_integral_swap (f := fun α y => Ga (α, y)) hGa_int
      _ = ∫ y, (∫ θ in Ioc 0 (2 * π), Gt (θ, y)) ∂μ := integral_congr_ae (ae_of_all _ hc)
      _ = ∫ θ in Ioc 0 (2 * π), ∫ y, Gt (θ, y) ∂μ :=
          (integral_integral_swap (f := fun θ y => Gt (θ, y)) hGt_int).symm
  rw [← key, ← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]

end UnforcedLeray.B0226
