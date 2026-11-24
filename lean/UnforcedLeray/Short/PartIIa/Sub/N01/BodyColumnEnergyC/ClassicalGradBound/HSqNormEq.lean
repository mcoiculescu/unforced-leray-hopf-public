import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1

/-!
# `HSqNormEq` (G4)

Source `the November 2 reference manuscript`
line 3307: `𝓗 = L²(s^{-3/2} ds dq dη)` on `s>0, q ∈ (0,c], η ∈ ℝ`; `c`-periodicity in `q` moves the
`q`-cell `(0,c]` to `[-c/2,c/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

theorem hsq_cell_swap {c : ℝ} (hc : 0 < c) (φ : ℝ × ℝ → ℝ≥0∞) (hm : Measurable φ)
    (hper : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x) :
    ∫⁻ x in Ioc 0 c ×ˢ (univ : Set ℝ), φ x = ∫⁻ x in UnforcedLeray.B0579.cell c, φ x := by
  have e1 : ∀ s : Set ℝ, (volume : Measure (ℝ × ℝ)).restrict (s ×ˢ (univ : Set ℝ)) =
      (volume.restrict s).prod (volume.restrict univ) := by
    intro s; rw [Measure.volume_eq_prod, Measure.prod_restrict]
  unfold UnforcedLeray.B0579.cell
  rw [e1, e1, lintegral_prod _ hm.aemeasurable, lintegral_prod _ hm.aemeasurable]
  set ψ : ℝ → ℝ≥0∞ := fun q => ∫⁻ η, φ (q, η) ∂(volume.restrict univ) with hψ
  have hp : Function.Periodic ψ c := fun q => by
    simp only [hψ]; exact lintegral_congr fun η => hper (q, η)
  have := UnforcedLeray.Axi.lintegral_periodic_affine hc one_pos ψ hp 0
  simpa only [div_one, one_mul, add_zero, inv_one, ENNReal.ofReal_one, neg_div] using this

theorem hSqNormEq : UnforcedLeray.Short.PartIIa.N01.HSqNormEq := by
  intro c hc g F hF hgF
  have hFm : Measurable F := hF.1.continuous.measurable
  have hFi : ∀ i : Fin 2, Measurable fun p => F p i := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp hF.1.continuous).measurable
  have h1 : ENNReal.ofReal (‖g‖ ^ 2) = ∫⁻ p, ‖(g : Profile → MeridC) p‖ₑ ^ 2 ∂(measureH c) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h2 : ∫⁻ p, ‖(g : Profile → MeridC) p‖ₑ ^ 2 ∂(measureH c) =
      ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(measureH c) :=
    lintegral_congr_ae (hgF.mono fun p hp => by simp only [hp])
  have hsum : ∀ p, ‖F p‖ₑ ^ 2 = ∑ i : Fin 2, ‖F p i‖ₑ ^ 2 := by
    intro p
    have := EuclideanSpace.norm_sq_eq (F p)
    have h3 : ENNReal.ofReal (‖F p‖ ^ 2) = ∑ i : Fin 2, ENNReal.ofReal (‖F p i‖ ^ 2) := by
      rw [this, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h4 : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(measureH c) =
      ∑ i : Fin 2, ∫⁻ p in UnforcedLeray.B0220.cell c,
        UnforcedLeray.B0220.weightH p * ‖F p i‖ₑ ^ 2 := by
    unfold UnforcedLeray.B0220.measureH UnforcedLeray.B0220.cellMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH
      (by fun_prop)]
    simp only [Pi.mul_apply, hsum, Finset.mul_sum]
    rw [lintegral_finsetSum]
    intro i _
    exact UnforcedLeray.B0220.measurable_weightH.mul ((hFi i).enorm.pow_const 2)
  rw [h1, h2, h4]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfm : Measurable fun p : Profile => ‖F p i‖ₑ ^ 2 :=
    (hFi i).enorm.pow_const 2
  unfold UnforcedLeray.B0220.cell
  have e : (volume : Measure Profile).restrict (Ioi 0 ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ))) =
      (volume.restrict (Ioi (0 : ℝ))).prod
        ((volume : Measure (ℝ × ℝ)).restrict (Ioc 0 c ×ˢ (univ : Set ℝ))) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod, Measure.prod_restrict]
  have hmeas : Measurable fun p : Profile => UnforcedLeray.B0220.weightH p * ‖F p i‖ₑ ^ 2 :=
    UnforcedLeray.B0220.measurable_weightH.mul hfm
  rw [e, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun σ => ?_
  have hsm : Measurable fun x : ℝ × ℝ => ‖F (σ, x) i‖ₑ ^ 2 :=
    hfm.comp measurable_prodMk_left
  have hw : UnforcedLeray.B0220.weightH (σ, (0, 0)) = ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) := rfl
  simp only [UnforcedLeray.B0220.weightH]
  rw [lintegral_const_mul _ hsm]
  congr 1
  refine hsq_cell_swap hc _ hsm fun x => ?_
  simp only
  have := hF.2.1 (σ, x)
  simp only at this
  rw [this]

end UnforcedLeray.Short.PartIIa.N01
