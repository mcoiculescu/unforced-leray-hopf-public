import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

/-!
# Part III-a: differentiation of the cell pairing in the age (`adjWDtDeriv`)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058.

For a jointly smooth `φ` and a cylinder test `ψ` (band `|η| ≤ R`), the pairing
`r ↦ ∫_cell φ(r) ψ` is differentiated under the integral on a neighbourhood of `ρ`: the integrand
`∂_rφ(r) ψ` is continuous on the compact set `[ρ-ε, ρ+ε] × ([-c/2,c/2] × [-R,R])`, and vanishes
outside it, so it is bounded there by a constant times `|ψ|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- The classical time derivative of a jointly smooth field is the derivative of its slice. -/
lemma ladDt_hasDerivAt {t s : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) {ρ : ℝ}
    (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) :
    HasDerivAt (fun r => ψ r x) (ladDt ψ ρ x) ρ := by
  have hmem : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨Ioo_subset_Ico_self hρ, mem_univ _⟩
  have hnhds : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 ((ρ, x) : ℝ × (ℝ × ℝ)) :=
    prod_mem_nhds (Ico_mem_nhds hρ.1 hρ.2) univ_mem
  have h1 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) (ρ, x)) (ρ, x) :=
    (((hj _ hmem).differentiableWithinAt (by simp)).hasFDerivWithinAt).hasFDerivAt hnhds
  have hι : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
  rw [ladDt_eq_fderivWithin hj hρ x]
  exact h1.comp_hasDerivAt ρ hι

/-- **Leaf** `adjWDtDeriv` (SP 3052-3058): `d/dr ∫_cell φ(r) ψ = ∫_cell ∂_rφ(ρ) ψ` at `ρ ∈ (t,s)`. -/
theorem adjWDtDeriv (m : ℝ) : AdjWDtDeriv m := by
  intro ν c tr t s g φ hctx ρ hρ ψ hψ
  obtain ⟨_, hc, _, _, _, hA, hj⟩ := hctx
  obtain ⟨R, hR⟩ := hψ.band
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hρ.1 hρ.2)
  have hs0nhds : Metric.ball ρ (ε / 2) ∈ 𝓝 ρ := Metric.ball_mem_nhds ρ (by linarith)
  have hIcc : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), r ∈ Ioo t s := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hball2 : ∀ r ∈ Metric.ball ρ (ε / 2), r ∈ Icc (ρ - ε / 2) (ρ + ε / 2) := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  -- continuity of the derivative in the strip and a bound on the compact set
  have hJc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) p
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ico t s ×ˢ univ) :=
    (hj.fderivWithin (adjStrip_uniqueDiff t s) (m := ∞) (by simp)).continuousOn.clm_apply
      continuousOn_const
  have hKc : IsCompact (Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) ⊆
      Ico t s ×ˢ univ := by
    intro p hp
    exact ⟨Ioo_subset_Ico_self (hIcc p.1 hp.1), mem_univ _⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hJc.mono hKsub)
  have hLD : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), ∀ x : ℝ × ℝ, x.1 ∈ Icc (-(c / 2)) (c / 2) →
      x.2 ∈ Icc (-R) R → ‖ladDt φ r x‖ ≤ M := by
    intro r hr x hx1 hx2
    rw [ladDt_eq_fderivWithin hj (hIcc r hr) x]
    exact hM (r, x) ⟨hr, hx1, hx2⟩
  have hcellsub : ∀ x : ℝ × ℝ, x ∈ B0579.cell c → x.1 ∈ Icc (-(c / 2)) (c / 2) := by
    intro x hx
    have hx' := Set.mem_prod.1 hx
    exact ⟨hx'.1.1, hx'.1.2.le⟩
  have hcont : ∀ r ∈ Ioo t s, Continuous (fun x : ℝ × ℝ => φ r x * ((ψ x : ℝ) : ℂ)) := fun r hr =>
    (adjContDiff_slice hj (Ioo_subset_Ico_self hr)).continuous.mul
      (Complex.continuous_ofReal.comp hψ.continuous)
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  -- the integrability at `ρ`
  have hvan : UnforcedLeray.Cyl.VanishesOutside R (fun x => φ ρ x * ((ψ x : ℝ) : ℂ)) :=
    fun x hx => by simp [hR x hx]
  have hF_int : Integrable (fun x => φ ρ x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := by
    rw [← IntegrableOn, hcell]
    exact hvan.integrableOn_cell (hcont ρ hρ) c
  have hF'_meas : AEStronglyMeasurable (fun x => ladDt φ ρ x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    ((continuous_ladDt hj hρ).mul (Complex.continuous_ofReal.comp hψ.continuous)).aestronglyMeasurable
  have hbound_int : Integrable (fun x => M * ‖ψ x‖) (volume.restrict (B0579.cell c)) :=
    Integrable.const_mul (Integrable.norm hψ.integrableOn) M
  have h_bound : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ r ∈ Metric.ball ρ (ε / 2),
      ‖ladDt φ r a * ((ψ a : ℝ) : ℂ)‖ ≤ M * ‖ψ a‖ := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (Filter.Eventually.of_forall fun a ha r hr => ?_)
    by_cases hA2 : |a.2| ≤ R
    · have h1 := hLD r (hball2 r hr) a (hcellsub a ha) (abs_le.1 hA2)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · have h0 : ψ a = 0 := hR a (not_le.1 hA2)
      simp [h0]
  have h_diff : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ r ∈ Metric.ball ρ (ε / 2),
      HasDerivAt (fun r => φ r a * ((ψ a : ℝ) : ℂ)) (ladDt φ r a * ((ψ a : ℝ) : ℂ)) r := by
    refine Filter.Eventually.of_forall fun a r hr => ?_
    exact (ladDt_hasDerivAt hj (hIcc r (hball2 r hr)) a).mul_const _
  have hF_meas : ∀ᶠ r in 𝓝 ρ, AEStronglyMeasurable (fun x => φ r x * ((ψ x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2) fun r hr => (hcont r hr).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs0nhds hF_meas hF_int hF'_meas
    h_bound hbound_int h_diff).2

end UnforcedLeray.Short.IIIa
