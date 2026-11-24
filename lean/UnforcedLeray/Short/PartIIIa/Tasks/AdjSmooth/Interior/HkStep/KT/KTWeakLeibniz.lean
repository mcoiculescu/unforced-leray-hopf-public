import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTTestInt

/-!
# `KTWeakLeibniz`: the weak Leibniz rule against a smooth periodic bounded factor

Source: `the November 2 reference manuscript` lines 3052-3058.
For a test `ψ`, the product `b ψ` is again a cylinder test, and
`∂_k (b ψ) = b ∂_k ψ + ψ ∂_k b`.  Integrability of the terms `f b ∂_k ψ` and `f (∂_k b) ψ` comes from
`ktTestInt` (applied to the test `b ∂_k ψ`, respectively to `ψ` times a bounded continuous factor).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray
open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- A smooth, `c`-periodic factor times a cylinder test is a cylinder test. -/
theorem ktWL_isCylTest_mul {c : ℝ} {φ b : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    (hb : ContDiff ℝ ∞ b) (hbp : ∀ x : ℝ × ℝ, b (x.1 + c, x.2) = b x) :
    B0579.IsCylTest c (fun x => b x * φ x) where
  smooth := hb.mul hφ.smooth
  periodic x := by simp only [hbp x, hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

theorem ktWeakLeibniz : UnforcedLeray.Short.IIIa.KTWeakLeibniz := by
  intro m c hc k f g b hb hbp hbd hfg hf hg
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨hfg1, hfg2⟩ := hfg
  unfold UnforcedLeray.Short.IIIa.HasWeakCellDerivC
  have hbdiff : Differentiable ℝ b := hb.differentiable (by simp)
  have hpd0 : Continuous (B0579.pd k b) := by
    unfold B0579.pd
    exact ((contDiff_infty_iff_fderiv.1 hb).2).continuous.clm_apply continuous_const
  have hbound : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ‖((B0579.pd k b x : ℝ) : ℂ)‖ ≤ M :=
    Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hM x).2
  have hmeas : AEStronglyMeasurable (fun x => ((B0579.pd k b x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    (Complex.continuous_ofReal.comp hpd0).aestronglyMeasurable
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · -- integrability of the two terms
    have hψ1 := ktWL_isCylTest_mul hψ hb hbp
    have hψb := ktWL_isCylTest_mul (hψ.pd k) hb hbp
    have hI0 : IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell c) :=
      ktTestInt c m hc f hf ψ hψ
    have hI1 : IntegrableOn (fun x => f x * ((B0579.pd k b x * ψ x : ℝ) : ℂ))
        (B0579.cell c) := by
      refine Integrable.congr (Integrable.bdd_mul (c := M) hI0 hmeas hbound)
        (Filter.Eventually.of_forall fun x => ?_)
      push_cast
      ring
    have hI2 : IntegrableOn (fun x => f x * ((b x * B0579.pd k ψ x : ℝ) : ℂ))
        (B0579.cell c) :=
      ktTestInt c m hc f hf _ hψb
    have hR : IntegrableOn (fun x => g x * ((b x * ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      (hfg1 _ hψ1).2
    constructor
    · show IntegrableOn (fun x => f x * (b x : ℂ) * (B0579.pd k ψ x : ℂ)) (B0579.cell c)
      refine Integrable.congr hI2 (Filter.Eventually.of_forall fun x => ?_)
      push_cast
      ring
    · show IntegrableOn (fun x => (g x * (b x : ℂ) + f x * (B0579.pd k b x : ℂ)) * (ψ x : ℂ))
        (B0579.cell c)
      refine Integrable.congr (Integrable.add hR hI1) (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      push_cast
      ring
  · -- the integral identity
    have hψ1 := ktWL_isCylTest_mul hψ hb hbp
    have hψb := ktWL_isCylTest_mul (hψ.pd k) hb hbp
    have hI0 : IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell c) :=
      ktTestInt c m hc f hf ψ hψ
    have hI1 : IntegrableOn (fun x => f x * ((B0579.pd k b x * ψ x : ℝ) : ℂ))
        (B0579.cell c) := by
      refine Integrable.congr (Integrable.bdd_mul (c := M) hI0 hmeas hbound)
        (Filter.Eventually.of_forall fun x => ?_)
      push_cast
      ring
    have hI2 : IntegrableOn (fun x => f x * ((b x * B0579.pd k ψ x : ℝ) : ℂ))
        (B0579.cell c) :=
      ktTestInt c m hc f hf _ hψb
    have hR : IntegrableOn (fun x => g x * ((b x * ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      (hfg1 _ hψ1).2
    have H2 : ∫ x in B0579.cell c, f x * ((B0579.pd k (fun y => b y * ψ y) x : ℝ) : ℂ) =
        -∫ x in B0579.cell c, g x * ((b x * ψ x : ℝ) : ℂ) :=
      hfg2 _ hψ1
    have key : ∫ x in B0579.cell c, f x * ((B0579.pd k (fun y => b y * ψ y) x : ℝ) : ℂ) =
        (∫ x in B0579.cell c, f x * ((B0579.pd k b x * ψ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, f x * ((b x * B0579.pd k ψ x : ℝ) : ℂ) := by
      rw [← integral_add hI1 hI2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [B0579.pd_mul hbdiff hψ.differentiable k x]
      push_cast
      ring
    have e2 : ∫ x in B0579.cell c, f x * (b x : ℂ) * (B0579.pd k ψ x : ℂ) =
        ∫ x in B0579.cell c, f x * ((b x * B0579.pd k ψ x : ℝ) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by push_cast; ring)
    have e3 : ∫ x in B0579.cell c, (g x * (b x : ℂ) + f x * (B0579.pd k b x : ℂ)) * (ψ x : ℂ) =
        (∫ x in B0579.cell c, g x * ((b x * ψ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, f x * ((B0579.pd k b x * ψ x : ℝ) : ℂ) := by
      rw [← integral_add hR hI1]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by push_cast; ring)
    show ∫ x in B0579.cell c, f x * (b x : ℂ) * (B0579.pd k ψ x : ℂ) =
      -∫ x in B0579.cell c, (g x * (b x : ℂ) + f x * (B0579.pd k b x : ℂ)) * (ψ x : ℂ)
    rw [e2, e3]
    linear_combination H2 - key
