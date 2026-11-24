import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice.SlabInt

/-!
# Real part of a product-test pairing (helper of `bgContRepWeakSlice`)

For a phase test `Φ(τ, y) = χ(τ) ψ(y) e_k` and `w ∈ Y_{q₀}`, `Re ⟪Φ, w⟫ = P⁻¹ ∫₀ᴾ χ(τ) ∫ ψ (contRep w)_k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem re_phasePair_prod {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (χ : ℝ → ℝ) (ψ : Space → ℝ) (k : Fin 3)
    (hΦeq : ∀ p : ℝ × Space, Φ p = ((χ p.1 * ψ p.2 : ℝ) : ℂ) • EuclideanSpace.single k (1 : ℂ)) :
    (phasePair P UnforcedLeray.B0412.q0E Φ w).re =
      P⁻¹ * ∫ t in Ioc (0 : ℝ) P, ∫ y, χ t * ψ y * contRep w t y k := by
  rw [phasePair_eq_pairF_rep_of_sliceTest (hΦ.isSliceTest _) w]
  unfold pairF phaseInt
  set μS := ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) with hμS
  have hint := integrable_dotL_rep_slab w hΦ
  have hf : ∀ z : ℝ × Space, dotL (Φ z) (rep w z.1 z.2) =
      ((χ z.1 * ψ z.2 : ℝ) : ℂ) * rep w z.1 z.2 k := by
    intro z
    rw [hΦeq z, dotL_apply]
    simp [Finset.sum_apply, EuclideanSpace.single_apply, Pi.single_apply]
  rw [← integral_prod (fun z : ℝ × Space => dotL (Φ z) (rep w z.1 z.2)) hint]
  rw [Complex.smul_re, smul_eq_mul]
  congr 1
  have hre : (∫ z, dotL (Φ z) (rep w z.1 z.2) ∂μS).re =
      ∫ z, (dotL (Φ z) (rep w z.1 z.2)).re ∂μS := by
    have := integral_re hint
    simpa using this.symm
  rw [hre]
  have hae : ∀ᵐ z ∂μS, (dotL (Φ z) (rep w z.1 z.2)).re = χ z.1 * ψ z.2 * contRep w z.1 z.2 k := by
    have h0 : ∀ᵐ z ∂μS, contRep w z.1 z.2 = reP (rep w z.1 z.2) := by
      rw [hμS, slab_eq_restrict]
      exact ae_restrict_of_ae (contRep_ae w)
    filter_upwards [h0] with z hz
    rw [hf z, hz]
    simp [reP]
  have hint2 : Integrable (fun z : ℝ × Space => χ z.1 * ψ z.2 * contRep w z.1 z.2 k) μS :=
    (hint.re).congr hae
  rw [integral_congr_ae hae, integral_prod _ hint2]

end UnforcedLeray.Short.PartIIIb.Concrete
