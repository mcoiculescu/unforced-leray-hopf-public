import UnforcedLeray.Loc.L13PhysicalRemainder.WeakStrong

/-!
# Step L13, helpers: continuity, rates and symmetry of the physical fields

Support for `Loc/L13PhysicalRemainder.lean` (step L13 `PhysicalRemainderStep`,
`paper/main.tex` lines 525–547, blueprint units B1025, B1026, B1028, B1029).

* continuity on `(0, e^{τ₀}]` of `ρ(t) = D(-log t)R(log t)` in `H²` and of
  `N(t) = t⁻¹D(-log t)F(log t)` in `L²`, for `τ₀ ≤ 0` (so `-log t ≥ 0`);
* the rates of line 540: `‖ρ(t)‖₂ ≤ t^{1/4} ‖R(log t)‖_{H²}` and
  `∑ᵢ ‖∂ᵢρ(t)‖₂² ≤ t^{-1/2} ‖R(log t)‖²_{H²}` (line 537: the `L²` norm scales like `t^{1/4}`,
  the gradient like `t^{-1/4}`);
* `𝒪`-invariance of `L²` classes is a linear condition (the rotation operator `rotL2` is

* the heat profile: linearity under the absolute convergence of the heat integrals, and
  `e^{htΔ}u₀ = t^{-1/2} H_h[u₀](·/√t, log t)` (lines 159–163, 446, 528);
* the expansion of `(A+B+C)⊗(A+B+C)` into the tensors of lines 464–466;
* continuity of the phase fields `e^{βτ}w(τ)` of `𝒵_β(τ₀)` and `𝒳_β(τ₀)` on `(-∞, τ₀]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology BoundedContinuousFunction

namespace UnforcedLeray.Blueprint.L13

open SobolevGraph
open UnforcedLeray.Loc.L02 (dil dilH2 coeFn_dil norm_dil_apply_le dil_mem_solenoidal)

/-! ## Continuity -/

/-- `x ↦ D(p(x)) g(x)` is continuous along continuous `p ≥ 0` and `g`. -/
theorem continuousOn_dil_comp {α : Type*} [TopologicalSpace α] {S : Set α} {p : α → ℝ}
    (hp : ContinuousOn p S) (hpS : ∀ x ∈ S, 0 ≤ p x) {g : α → L2Space}
    (hg : ContinuousOn g S) : ContinuousOn (fun x => dil (p x) (g x)) S := by
  intro x₀ hx₀
  have hstrong : Tendsto (fun x => dil (p x) (g x₀)) (𝓝[S] x₀) (𝓝 (dil (p x₀) (g x₀))) := by
    have h1 : ContinuousWithinAt (fun s => dil s (g x₀)) (Ici 0) (p x₀) :=
      (Loc.L02.continuousOn_freeL2 le_rfl (g x₀)) (p x₀) (hpS x₀ hx₀)
    exact h1.comp (hp x₀ hx₀) (fun x hx => hpS x hx)
  have hg0 : Tendsto (fun x => ‖g x - g x₀‖) (𝓝[S] x₀) (𝓝 0) := by
    have := ((hg x₀ hx₀).tendsto.sub_const (g x₀)).norm
    simpa using this
  have hsmall : Tendsto (fun x => dil (p x) (g x) - dil (p x) (g x₀)) (𝓝[S] x₀) (𝓝 0) := by
    apply squeeze_zero_norm' _ hg0
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [← map_sub]
    have hs0 : 0 ≤ p x := hpS x hx
    calc ‖dil (p x) (g x - g x₀)‖ ≤ Real.exp (-(p x / 4)) * ‖g x - g x₀‖ :=
          norm_dil_apply_le _ _
      _ ≤ 1 * ‖g x - g x₀‖ := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = ‖g x - g x₀‖ := one_mul _
  have := hsmall.add hstrong
  simp only [sub_add_cancel, zero_add] at this
  exact this

theorem log_mem_Iic {τ₀ t : ℝ} (ht : t ∈ Ioc 0 (Real.exp τ₀)) : Real.log t ≤ τ₀ := by
  have := Real.log_le_log ht.1 ht.2
  rwa [Real.log_exp] at this

theorem neg_log_nonneg {τ₀ t : ℝ} (hτ₀ : τ₀ ≤ 0) (ht : t ∈ Ioc 0 (Real.exp τ₀)) :
    0 ≤ -Real.log t := by
  have := log_mem_Iic ht
  linarith

theorem continuousOn_log_Ioc (τ₀ : ℝ) : ContinuousOn Real.log (Ioc 0 (Real.exp τ₀)) :=
  Real.continuousOn_log.mono (fun t ht => ne_of_gt ht.1)

/-- Continuity of `ρ(t) = D(-log t) R(log t)` in `H²` on `(0, e^{τ₀}]`. -/
theorem continuousOn_physicalOf {R : ℝ → H2} {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0)
    (hR : ContinuousOn R (Iic τ₀)) :
    ContinuousOn (physicalOf R) (Ioc 0 (Real.exp τ₀)) := by
  have hlog := continuousOn_log_Ioc τ₀
  have hmaps : MapsTo Real.log (Ioc 0 (Real.exp τ₀)) (Iic τ₀) := fun t ht => log_mem_Iic ht
  have hRc : ContinuousOn (fun t => R (Real.log t)) (Ioc 0 (Real.exp τ₀)) := hR.comp hlog hmaps
  have hp : ContinuousOn (fun t => -Real.log t) (Ioc 0 (Real.exp τ₀)) := hlog.neg
  have hpS : ∀ t ∈ Ioc 0 (Real.exp τ₀), 0 ≤ -Real.log t := fun t ht => neg_log_nonneg hτ₀ ht
  rw [H2.continuousOn_iff_components]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · exact continuousOn_dil_comp hp hpS (H2.valueCLM.continuous.comp_continuousOn hRc)
  · have h1 := continuousOn_dil_comp hp hpS ((H2.firstCLM i).continuous.comp_continuousOn hRc)
    have h2 := ((Real.continuous_exp.comp_continuousOn (hp.div_const 2))).smul h1
    refine h2.congr (fun t _ => ?_)
    simp only [physicalOf, dilH2_first]
    rfl
  · have h1 := continuousOn_dil_comp hp hpS
      ((H2.secondCLM i j).continuous.comp_continuousOn hRc)
    have h2 := (Real.continuous_exp.comp_continuousOn hp).smul h1
    refine h2.congr (fun t _ => ?_)
    simp only [physicalOf, dilH2_second]
    rfl

/-- Continuity of `N(t) = t⁻¹ D(-log t) F(log t)` in `L²` on `(0, e^{τ₀}]`. -/
theorem continuousOn_physicalForcing {F : ℝ → L2Space} {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0)
    (hF : ContinuousOn F (Iic τ₀)) :
    ContinuousOn (physicalForcing F) (Ioc 0 (Real.exp τ₀)) := by
  have hlog := continuousOn_log_Ioc τ₀
  have hmaps : MapsTo Real.log (Ioc 0 (Real.exp τ₀)) (Iic τ₀) := fun t ht => log_mem_Iic ht
  have hFc : ContinuousOn (fun t => F (Real.log t)) (Ioc 0 (Real.exp τ₀)) := hF.comp hlog hmaps
  have h1 := continuousOn_dil_comp hlog.neg (fun t ht => neg_log_nonneg hτ₀ ht) hFc
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Ioc 0 (Real.exp τ₀)) :=
    continuousOn_inv₀.mono (fun t ht => ne_of_gt ht.1)
  exact hinv.smul h1

/-! ## The rates of line 540 -/

theorem exp_neg_log_div (t a : ℝ) (ht : 0 < t) :
    Real.exp (-Real.log t * a) = t ^ (-a) := by
  rw [Real.rpow_def_of_pos ht]
  ring_nf

theorem norm_physicalOf_value_le (R : ℝ → H2) {t : ℝ} (ht : 0 < t) :
    ‖(physicalOf R t).value‖ ≤ t ^ (1 / 4 : ℝ) * ‖R (Real.log t)‖ := by
  simp only [physicalOf, dilH2_value]
  calc ‖dil (-Real.log t) (R (Real.log t)).value‖
      ≤ Real.exp (-(-Real.log t / 4)) * ‖(R (Real.log t)).value‖ := norm_dil_apply_le _ _
    _ ≤ Real.exp (-(-Real.log t / 4)) * ‖R (Real.log t)‖ := by
        gcongr
        exact norm_value_le_H2 _
    _ = t ^ (1 / 4 : ℝ) * ‖R (Real.log t)‖ := by
        congr 1
        rw [Real.rpow_def_of_pos ht]
        ring_nf

theorem sum_sq_first_physicalOf_le (R : ℝ → H2) {t : ℝ} (ht : 0 < t) :
    ∑ i : Fin 3, ‖(physicalOf R t).first i‖ ^ 2 ≤
      t ^ (-(1 / 2 : ℝ)) * ‖R (Real.log t)‖ ^ 2 := by
  set s := -Real.log t with hs
  set G := R (Real.log t)
  have hfirst : ∀ i, ‖(physicalOf R t).first i‖ ≤ Real.exp (s / 4) * ‖G.first i‖ := by
    intro i
    simp only [physicalOf, dilH2_first, ← hs]
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (s / 2) * ‖dil s (G.first i)‖
        ≤ Real.exp (s / 2) * (Real.exp (-(s / 4)) * ‖G.first i‖) := by
          gcongr
          exact norm_dil_apply_le _ _
      _ = Real.exp (s / 4) * ‖G.first i‖ := by
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
  have hsq : ∀ i, ‖(physicalOf R t).first i‖ ^ 2 ≤ Real.exp (s / 2) * ‖G.first i‖ ^ 2 := by
    intro i
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hfirst i) 2
    calc ‖(physicalOf R t).first i‖ ^ 2 ≤ (Real.exp (s / 4) * ‖G.first i‖) ^ 2 := h1
      _ = Real.exp (s / 2) * ‖G.first i‖ ^ 2 := by
          rw [mul_pow, sq (Real.exp (s / 4)), ← Real.exp_add]
          ring_nf
  have hG : ∑ i : Fin 3, ‖G.first i‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    have h := H2.norm_sq G
    have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖G.second i j‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    nlinarith [sq_nonneg ‖G.value‖]
  calc ∑ i : Fin 3, ‖(physicalOf R t).first i‖ ^ 2
      ≤ ∑ i : Fin 3, Real.exp (s / 2) * ‖G.first i‖ ^ 2 := Finset.sum_le_sum (fun i _ => hsq i)
    _ = Real.exp (s / 2) * ∑ i : Fin 3, ‖G.first i‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ Real.exp (s / 2) * ‖G‖ ^ 2 := by gcongr
    _ = t ^ (-(1 / 2 : ℝ)) * ‖G‖ ^ 2 := by
        congr 1
        rw [hs, Real.rpow_def_of_pos ht]
        ring_nf

/-! ## `𝒪`-invariance of `L²` classes (rotation copied from `Loc/L04ModeRegularity.lean`) -/

/-- `F ↦ g F(g⁻¹ ·)` on `L²(ℝ³;ℝ³)`. -/
def rotL2 (g : Space ≃ₗᵢ[ℝ] Space) : L2Space →L[ℝ] L2Space :=
  (g.toLinearIsometry.toContinuousLinearMap.compLpL 2 volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (g.symm : Space → Space)
      g.symm.measurePreserving).toContinuousLinearMap

theorem rotL2_ae (g : Space ≃ₗᵢ[ℝ] Space) (F : L2Space) :
    (rotL2 g F : SpatialField) =ᵐ[volume] rotateField g (F : SpatialField) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := volume) (p := 2)
    g.toLinearIsometry.toContinuousLinearMap
    (Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F)
  have h2 := Lp.coeFn_compMeasurePreserving F g.symm.measurePreserving
  have h3 : (fun x => g.toLinearIsometry.toContinuousLinearMap
      ((Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F) x))
        =ᵐ[volume] rotateField g (F : SpatialField) := by
    filter_upwards [h2] with x hx
    simp only [rotateField, hx, Function.comp_apply]
    rfl
  exact h1.trans h3

theorem isAxisymmetricNoSwirl_iff_rotL2 (F : L2Space) :
    IsAxisymmetricNoSwirl (F : SpatialField) ↔ ∀ g, FixesAxis g → rotL2 g F = F := by
  constructor
  · intro h g hg
    exact Lp.ext ((rotL2_ae g F).trans (h g hg))
  · intro h g hg
    have := (rotL2_ae g F).symm
    rw [h g hg] at this
    exact this

theorem isAxisymmetricNoSwirl_add {F G : L2Space} (hF : IsAxisymmetricNoSwirl (F : SpatialField))
    (hG : IsAxisymmetricNoSwirl (G : SpatialField)) :
    IsAxisymmetricNoSwirl ((F + G : L2Space) : SpatialField) := by
  rw [isAxisymmetricNoSwirl_iff_rotL2] at hF hG ⊢
  intro g hg
  rw [map_add, hF g hg, hG g hg]

theorem isAxisymmetricNoSwirl_smul (a : ℝ) {F : L2Space}
    (hF : IsAxisymmetricNoSwirl (F : SpatialField)) :
    IsAxisymmetricNoSwirl ((a • F : L2Space) : SpatialField) := by
  rw [isAxisymmetricNoSwirl_iff_rotL2] at hF ⊢
  intro g hg
  rw [map_smul, hF g hg]

/-! ## The heat profile -/

/-- `H_h[u+v] = H_h[u] + H_h[v]` when the heat integrals converge. -/
theorem heatProfile_add {h τ : ℝ} {u v : SpatialField}
    (hu : ∀ x, Integrable (fun z : Space => Heat.kernel (h * Real.exp τ) z • u (x - z)))
    (hv : ∀ x, Integrable (fun z : Space => Heat.kernel (h * Real.exp τ) z • v (x - z))) :
    heatProfile h (u + v) τ = heatProfile h u τ + heatProfile h v τ := by
  funext y
  simp only [heatProfile_apply, Pi.add_apply, smul_add]
  rw [integral_add (hu _) (hv _), smul_add]

/-- `e^{htΔ}u = t^{-1/2} H_h[u](·/√t, log t)` (lines 446, 528). -/
theorem flow_eq_spatialScale_heatProfile {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (u : SpatialField) :
    Heat.flow u (h * t) = SpatialScaling.spatialScale (Real.exp (-Real.log t / 2))
      (Real.exp (-Real.log t / 2)) (heatProfile h u (Real.log t)) := by
  rw [Heat.flow_pos u (mul_pos hh ht)]
  funext x
  simp only [SpatialScaling.spatialScale, heatProfile]
  have e1 : Real.exp (-Real.log t / 2) * Real.exp (Real.log t / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have e2 : Real.exp (Real.log t / 2) * Real.exp (-Real.log t / 2) = 1 := by
    rw [mul_comm, e1]
  rw [smul_smul, e1, one_smul, smul_smul, e2, one_smul, Real.exp_log ht]

/-! ## Tensor expansion -/

/-- `(A+B+C)⊗(A+B+C) = A⊗A + (A⊗B + B⊗A + B⊗B) + (A⊗C + C⊗A) + (B⊗C + C⊗B) + C⊗C`. -/
theorem tensorColumns_add3 (A B C : SpatialField) (j : Fin 3) :
    tensorColumns (A + B + C) (A + B + C) j =
      addColumns (addColumns (addColumns (addColumns (tensorColumns A A)
        (addColumns (symTensorColumns A B) (tensorColumns B B))) (symTensorColumns A C))
        (symTensorColumns B C)) (tensorColumns C C) j := by
  funext y
  simp only [tensorColumns, symTensorColumns, addColumns, Pi.add_apply, PiLp.add_apply,
    add_smul, smul_add]
  abel

/-! ## Phase fields of the weighted spaces -/

theorem continuousOn_unweight {τ₀ : ℝ} (β : ℝ) (w : WeightedZ τ₀) :
    ContinuousOn (unweight β w) (Iic τ₀) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (fun x : Iic τ₀ => Real.exp (β * (x : ℝ)) • w x) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      (show Iic τ₀ →ᵇ Z from w).continuous
  refine hc.congr (fun x => ?_)
  simp only [Set.restrict_apply]
  rw [unweight_of_le β w x.2]

theorem continuousOn_unweightX {τ₀ : ℝ} (β : ℝ) (F : WeightedX τ₀) :
    ContinuousOn (unweightX β F) (Iic τ₀) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (fun x : Iic τ₀ => Real.exp (β * (x : ℝ)) • F x) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      (show Iic τ₀ →ᵇ X from F).continuous
  refine hc.congr (fun x => ?_)
  simp only [Set.restrict_apply, unweightX]
  rw [dif_pos (show (x : ℝ) ≤ τ₀ from x.2)]

end UnforcedLeray.Blueprint.L13
