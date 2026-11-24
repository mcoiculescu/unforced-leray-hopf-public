import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_4

/-!
# Bilinearity of the transpose convection pairing (`PartII-b:Q1` helper)

Source of record: `the November 2 reference manuscript`, lines 2503-2518
("the quadratic terms in `w + E_εα` and their polarized differences").

For a phase test `Φ` and a.e. bounded fields `u, v`, the pairing `⟪(u·∇)Φ, v⟫` is a genuine
(Lebesgue) integral over one phase cell (`integrable_advT_pair`), so it is additive and
homogeneous in `u` and in `v` up to null sets.  The state map `z ↦ p.uOf z = e + w` is linear up
to null sets (`uOf_add_ae`, `uOf_smul_ae`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.QuadLeaf

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412

/-- The phase measure `dτ dy` on `(0, P] × ℝ³`. -/
abbrev cellμ (P : ℝ) : Measure (ℝ × Space) :=
  ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)

theorem restrict_phaseCell_eq (P : ℝ) :
    (volume : Measure (ℝ × Space)).restrict (phaseCell P) = cellμ P := by
  simpa [cellμ, phaseCell, Measure.volume_eq_prod] using
    (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
      (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm

theorem cellμ_ac (P : ℝ) : cellμ P ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod Measure.restrict_le_self.absolutelyContinuous
    (le_refl (volume : Measure Space)).absolutelyContinuous

/-- A continuous field with uniformly bounded spatial support is integrable on the phase cell. -/
theorem integrable_cell_of_continuous {E : Type*} [NormedAddCommGroup E] {G : ℝ × Space → E}
    (hG : Continuous G) {R : ℝ} (hR : ∀ t y, R < ‖y‖ → G (t, y) = 0) (P : ℝ) :
    Integrable G (cellμ P) := by
  rw [← restrict_phaseCell_eq]
  show IntegrableOn G (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))
  have hK : IntegrableOn G (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    hG.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))
  refine hK.of_forall_sdiff_eq_zero (measurableSet_Ioc.prod MeasurableSet.univ) ?_
  rintro ⟨t, y⟩ ⟨⟨ht, -⟩, hnot⟩
  refine hR t y ?_
  by_contra hy
  exact hnot ⟨Ioc_subset_Icc_self ht, by
    simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hy⟩

/-- `‖(u·∇)Φ‖ ≤ ‖u‖ ∑ₖ ‖∂ₖΦ‖` pointwise. -/
theorem norm_advT_le (u Φ : ℝ × Space → CVec3) (x : ℝ × Space) :
    ‖advT u Φ x‖ ≤ ‖u x‖ * ∑ k : Fin 3, ‖dy k Φ x‖ := by
  unfold advT
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (u x) k) (norm_nonneg _)

theorem aestronglyMeasurable_advT {μ : Measure (ℝ × Space)} {u Φ : ℝ × Space → CVec3}
    (hu : AEStronglyMeasurable u μ) (hΦ : Continuous Φ) (hdΦ : ∀ k, Continuous (dy k Φ)) :
    AEStronglyMeasurable (advT u Φ) μ := by
  have : advT u Φ = fun x => ∑ k : Fin 3, u x k • dy k Φ x := rfl
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  have hk : AEStronglyMeasurable (fun x => u x k) μ :=
    (EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hu
  exact hk.smul (hdΦ k).aestronglyMeasurable

/-- The transpose convection pairing of two a.e. bounded fields against a phase test is
integrable on one phase cell. -/
theorem integrable_advT_pair {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {u v : ℝ × Space → CVec3} (hu : AEStronglyMeasurable u (cellμ P))
    (hv : AEStronglyMeasurable v (cellμ P)) {M N : ℝ}
    (hM : ∀ᵐ x ∂(cellμ P), ‖u x‖ ≤ M) (hN : ∀ᵐ x ∂(cellμ P), ‖v x‖ ≤ N) :
    Integrable (fun x => dotL (advT u Φ x) (v x)) (cellμ P) := by
  have hdk : ∀ k : Fin 3, Integrable (fun x => ‖dy k Φ x‖) (cellμ P) := by
    intro k
    obtain ⟨R, hR⟩ := (hΦ.dy k).bounded_support
    refine integrable_cell_of_continuous (hΦ.dy k).continuous.norm (R := R) ?_ P
    intro t y hy
    simp [hR t y hy]
  have hsum : Integrable (fun x => ∑ k : Fin 3, ‖dy k Φ x‖) (cellμ P) :=
    integrable_finsetSum _ fun k _ => hdk k
  have hmeas : AEStronglyMeasurable (fun x => dotL (advT u Φ x) (v x)) (cellμ P) :=
    dotL.aestronglyMeasurable_comp₂
      (aestronglyMeasurable_advT hu hΦ.continuous fun k => (hΦ.dy k).continuous) hv
  refine (hsum.const_mul (‖dotL‖ * M * N)).mono' hmeas ?_
  filter_upwards [hM, hN] with x hMx hNx
  have hA := norm_advT_le u Φ x
  have hS : 0 ≤ ∑ k : Fin 3, ‖dy k Φ x‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hMx
  calc ‖dotL (advT u Φ x) (v x)‖
      ≤ ‖dotL‖ * ‖advT u Φ x‖ * ‖v x‖ := dotL.le_opNorm₂ _ _
    _ ≤ ‖dotL‖ * (M * ∑ k : Fin 3, ‖dy k Φ x‖) * N := by
        gcongr
        exact hA.trans (mul_le_mul_of_nonneg_right hMx hS)
    _ = ‖dotL‖ * M * N * ∑ k : Fin 3, ‖dy k Φ x‖ := by ring

/-- `pairF` only sees the a.e. classes of both arguments. -/
theorem pairF_congr_ae2 (P : ℝ) {Φ Φ' u u' : ℝ × Space → CVec3} (hΦ : Φ =ᵐ[volume] Φ')
    (hu : u =ᵐ[volume] u') : pairF P Φ u = pairF P Φ' u' := by
  unfold pairF phaseInt
  congr 1
  have h' : ∀ᵐ x : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      Φ x = Φ' x ∧ u x = u' x := by
    rw [← Measure.volume_eq_prod]
    filter_upwards [hΦ, hu] with x h1 h2 using ⟨h1, h2⟩
  have h2 := Measure.ae_ae_of_ae_prod h'
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [h2] with t ht _
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  simp only [hy.1, hy.2]

theorem advT_congr_ae {u u' : ℝ × Space → CVec3} (h : u =ᵐ[volume] u') (Φ : ℝ × Space → CVec3) :
    advT u Φ =ᵐ[volume] advT u' Φ := by
  filter_upwards [h] with x hx
  simp only [advT, hx]

theorem pairF_smul_left (P : ℝ) (c : ℂ) (Φ u : ℝ × Space → CVec3) :
    pairF P (fun x => c • Φ x) u = c * pairF P Φ u := by
  unfold pairF phaseInt
  have h : ∀ x : ℝ × Space, dotL (c • Φ x) (u x) = c * dotL (Φ x) (u x) := fun x => by
    simp [map_smul]
  simp only [h, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem pairF_smul_right (P : ℝ) (c : ℂ) (Φ u : ℝ × Space → CVec3) :
    pairF P Φ (fun x => c • u x) = c * pairF P Φ u := by
  unfold pairF phaseInt
  have h : ∀ x : ℝ × Space, dotL (Φ x) (c • u x) = c * dotL (Φ x) (u x) := fun x => by
    simp [map_smul]
  simp only [h, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

/-- Additivity of `-⟪(u·∇)Φ, v⟫` in the advecting field, up to null sets. -/
theorem pairF_advT_add_left {P : ℝ} [Fact (0 < P)] (Φ : ℝ × Space → CVec3)
    {u₁ u₂ u₁₂ v : ℝ × Space → CVec3} (h12 : u₁₂ =ᵐ[volume] fun x => u₁ x + u₂ x)
    (hI1 : Integrable (fun x => dotL (advT u₁ Φ x) (v x)) (cellμ P))
    (hI2 : Integrable (fun x => dotL (advT u₂ Φ x) (v x)) (cellμ P)) :
    -pairF P (advT u₁₂ Φ) v = -pairF P (advT u₁ Φ) v + -pairF P (advT u₂ Φ) v := by
  have hA : advT u₁₂ Φ =ᵐ[volume] fun x => advT u₁ Φ x + advT u₂ Φ x := by
    filter_upwards [h12] with x hx
    simp only [advT, hx, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  rw [← restrict_phaseCell_eq] at hI1 hI2
  have hI12 : Integrable (fun x => dotL (advT u₁ Φ x + advT u₂ Φ x) (v x))
      ((volume : Measure (ℝ × Space)).restrict (phaseCell P)) :=
    (hI1.add hI2).congr (Eventually.of_forall fun x => by
      simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_apply])
  rw [pairF_congr_ae2 P hA (EventuallyEq.refl _ _),
    pairF_add_left_of_integrable hI1 hI2 hI12, neg_add]

/-- Additivity of `-⟪(u·∇)Φ, v⟫` in the advected field, up to null sets. -/
theorem pairF_advT_add_right {P : ℝ} [Fact (0 < P)] (Φ : ℝ × Space → CVec3)
    {u v₁ v₂ v₁₂ : ℝ × Space → CVec3} (h12 : v₁₂ =ᵐ[volume] fun x => v₁ x + v₂ x)
    (hI1 : Integrable (fun x => dotL (advT u Φ x) (v₁ x)) (cellμ P))
    (hI2 : Integrable (fun x => dotL (advT u Φ x) (v₂ x)) (cellμ P)) :
    -pairF P (advT u Φ) v₁₂ = -pairF P (advT u Φ) v₁ + -pairF P (advT u Φ) v₂ := by
  rw [← restrict_phaseCell_eq] at hI1 hI2
  have hI12 : Integrable (fun x => dotL (advT u Φ x) (v₁ x + v₂ x))
      ((volume : Measure (ℝ × Space)).restrict (phaseCell P)) :=
    (hI1.add hI2).congr (Eventually.of_forall fun x => by
      simp only [Pi.add_apply, map_add])
  rw [pairF_congr_ae2 P (EventuallyEq.refl _ _) h12,
    pairF_add_right_of_integrable hI1 hI2 hI12, neg_add]

/-- Real homogeneity of `-⟪(u·∇)Φ, v⟫` in the advecting field, up to null sets. -/
theorem pairF_advT_smul_left (P : ℝ) (Φ : ℝ × Space → CVec3) (a : ℝ)
    {u ua v : ℝ × Space → CVec3} (ha : ua =ᵐ[volume] fun x => (a : ℂ) • u x) :
    -pairF P (advT ua Φ) v = (a : ℂ) * (-pairF P (advT u Φ) v) := by
  have hA : advT ua Φ =ᵐ[volume] fun x => (a : ℂ) • advT u Φ x := by
    filter_upwards [ha] with x hx
    simp only [advT, hx, PiLp.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  rw [pairF_congr_ae2 P hA (EventuallyEq.refl _ _), pairF_smul_left]
  ring

/-- Real homogeneity of `-⟪(u·∇)Φ, v⟫` in the advected field, up to null sets. -/
theorem pairF_advT_smul_right (P : ℝ) (Φ : ℝ × Space → CVec3) (a : ℝ)
    {u v va : ℝ × Space → CVec3} (ha : va =ᵐ[volume] fun x => (a : ℂ) • v x) :
    -pairF P (advT u Φ) va = (a : ℂ) * (-pairF P (advT u Φ) v) := by
  rw [pairF_congr_ae2 P (EventuallyEq.refl _ _) ha, pairF_smul_right]
  ring

/-! ## Linearity of the state field `p.uOf` up to null sets -/

theorem realC_add' (a b : Space) : realC (a + b) = realC a + realC b := by
  ext i
  simp [realC_apply]

theorem realC_smul' (c : ℝ) (a : Space) : realC (c • a) = (c : ℂ) • realC a := by
  ext i
  simp [realC_apply]

theorem coord_add (p : Params) (z₁ z₂ : p.Z) (i : Fin 2) :
    p.coord (z₁ + z₂) i = p.coord z₁ i + p.coord z₂ i := by
  simp only [Params.coord, Submodule.coe_add, map_add, PiLp.add_apply, mul_add]

theorem coord_smul (p : Params) (a : ℝ) (z : p.Z) (i : Fin 2) :
    p.coord (a • z) i = a * p.coord z i := by
  simp only [Params.coord, Submodule.coe_smul, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

theorem eFun_coord_add (p : Params) (z₁ z₂ : p.Z) (x : ℝ × Space) :
    p.eFun (p.coord (z₁ + z₂)) x = p.eFun (p.coord z₁) x + p.eFun (p.coord z₂) x := by
  simp only [Params.eFun, coord_add, add_smul, Finset.sum_add_distrib, realC_add']

theorem eFun_coord_smul (p : Params) (a : ℝ) (z : p.Z) (x : ℝ × Space) :
    p.eFun (p.coord (a • z)) x = (a : ℂ) • p.eFun (p.coord z) x := by
  simp only [Params.eFun, coord_smul, mul_smul, ← Finset.smul_sum, realC_smul']

theorem wOf_add (p : Params) (z₁ z₂ : p.Z) : p.wOf (z₁ + z₂) = p.wOf z₁ + p.wOf z₂ := by
  simp only [Params.wOf, Submodule.coe_add, map_add]

theorem wOf_smul (p : Params) (a : ℝ) (z : p.Z) : p.wOf (a • z) = a • p.wOf z := by
  simp only [Params.wOf, Submodule.coe_smul, map_smul]

theorem uOf_add_ae (p : Params) (z₁ z₂ : p.Z) :
    p.uOf (z₁ + z₂) =ᵐ[volume] fun x => p.uOf z₁ x + p.uOf z₂ x := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  filter_upwards [BLRepLinAux.rep_add_ae (p.wOf z₁) (p.wOf z₂)] with x hx
  simp only [Params.uOf, eFun_coord_add, wOf_add, hx]
  abel

theorem uOf_smul_ae (p : Params) (a : ℝ) (z : p.Z) :
    p.uOf (a • z) =ᵐ[volume] fun x => (a : ℂ) • p.uOf z x := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  filter_upwards [BLRepLinAux.rep_smul_ae a (p.wOf z)] with x hx
  simp only [Params.uOf, eFun_coord_smul, wOf_smul, hx, smul_add, Complex.coe_smul]

end UnforcedLeray.Short.IIb.QuadLeaf
