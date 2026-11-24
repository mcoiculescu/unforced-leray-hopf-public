import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Short.PartI.Tasks.CanonicalBranchProof
import UnforcedLeray.Short.PartI.Tasks.QuadrupoleMellinIntegrable
import UnforcedLeray.Short.PartI.Tasks.MellinHolomorphic
import Mathlib.Analysis.MellinInversion

/-!
# `PartI:C14`: `canonicalMellin_proof : CanonicalMellin`

Source of record: `the November 2 reference manuscript`
lines 1155-1174 (Corollary `short-mellin`).

Proof outline.
* Uniqueness (`CanonicalBranch`, proved in `CanonicalBranchProof`) identifies the given `V` with
  the canonical branch `V0` on `(0,∞)`, so the bound near `0` transfers to `V`.
* Integrability and holomorphy come from `mellin_integrable` (C12) and `mellin_analyticOnNhd`
  (C13), applied to the continuous-on-`(0,∞)` integrand `m θ = 𝔐(V θ)` with the indicator of `(0,∞)`.
* Nonvanishing: if `𝒥 ≡ 0` on `Re μ > -3/2`, the Mellin transform of `m` vanishes on `Re s = 3/2`,
  so by Mellin inversion (`mellinInv_mellin_eq`) `m = 0` on `(0,∞)`; the asymptotic
  `e^{λθ}θ^κV(θ) → q` then forces `𝔐(q) = 0`, contradicting `𝔐(q) ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

/-- **Task PartI:C14**: the nontrivial full-age Mellin output (lines 1155-1174). -/
theorem canonicalMellin_proof : CanonicalMellin := by
  intro lam q ℓ hs hq hMq V hV hA
  have hre : 0 < lam.re := hs.re_pos
  obtain ⟨V0, hV0, hA0, hb0, hu0, -⟩ := canonicalBranch_proof lam q ℓ hs hq
  have hVeq : ∀ θ : ℝ, 0 < θ → V θ = V0 θ := fun θ hθ => hu0 V hV hA θ hθ
  have hbV : ∃ C : ℝ, ∀ θ ∈ Set.Ioc (0 : ℝ) 1, ‖V θ‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb0
    exact ⟨C, fun θ hθ => by rw [hVeq θ hθ.1]; exact hC θ hθ.1 hθ.2⟩
  have hint := mellin_integrable hV hA hbV hMq hre
  refine ⟨hint, ?_, ?_⟩
  · -- holomorphy on `Re μ > -3/2`
    have hVc : ContinuousOn V (Ioi (0 : ℝ)) := hV.smooth.continuousOn
    have hcont : Continuous (fun x : B0010.XG => inner ℂ QMI.quadElt x) :=
      continuous_const.inner continuous_id
    have hmc : ContinuousOn (fun θ : ℝ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ))
        (Ioi (0 : ℝ)) := by
      have hfun : (fun θ : ℝ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)) =
          fun θ => inner ℂ QMI.quadElt (V θ) := by
        funext θ
        exact QMI.quadrupole_eq_inner (V θ)
      rw [hfun]
      exact hcont.comp_continuousOn hVc
    have hind : ∀ μ : ℂ, -(3 / 2) < μ.re → IntegrableOn
        (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2) *
          (Ioi (0 : ℝ)).indicator (fun θ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)) θ)
        (Ioi 0) := by
      intro μ hμ
      refine (hint μ hμ).congr_fun (fun θ hθ => ?_) measurableSet_Ioi
      simp only [Set.indicator_of_mem (show θ ∈ Ioi (0 : ℝ) from hθ)]
    have hmeas : AEStronglyMeasurable
        ((Ioi (0 : ℝ)).indicator (fun θ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ))) volume :=
      (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2 (hmc.aestronglyMeasurable measurableSet_Ioi)
    have key := mellin_analyticOnNhd hind hmeas
    have heq : mellinJ V = fun μ : ℂ => ∫ θ in Ioi (0 : ℝ),
        (θ : ℂ) ^ (μ + 1 / 2) *
          (Ioi (0 : ℝ)).indicator (fun θ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)) θ := by
      funext μ
      unfold mellinJ
      refine setIntegral_congr_fun measurableSet_Ioi (fun θ hθ => ?_)
      simp only [Set.indicator_of_mem (show θ ∈ Ioi (0 : ℝ) from hθ)]
    rw [heq]
    exact key
  · -- nonvanishing
    by_contra hcon
    push_neg at hcon
    set mfun : ℝ → ℂ := fun θ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ) with hmfun
    have hmc : ContinuousOn mfun (Ioi (0 : ℝ)) := by
      have hVc : ContinuousOn V (Ioi (0 : ℝ)) := hV.smooth.continuousOn
      have hcont : Continuous (fun x : B0010.XG => inner ℂ QMI.quadElt x) :=
        continuous_const.inner continuous_id
      have hfun : mfun = fun θ => inner ℂ QMI.quadElt (V θ) := by
        funext θ
        exact QMI.quadrupole_eq_inner (V θ)
      rw [hfun]
      exact hcont.comp_continuousOn hVc
    -- the Mellin transform of `mfun` vanishes on the line `Re s = 3/2`
    have hmel : ∀ s : ℂ, s.re = 3 / 2 → mellin mfun s = 0 := by
      intro s hs'
      have h1 := hcon (s - 3 / 2) (by rw [Complex.sub_re, hs']; norm_num)
      have h2 : mellin mfun s = mellinJ V (s - 3 / 2) := by
        unfold mellin mellinJ
        refine setIntegral_congr_fun measurableSet_Ioi (fun θ _ => ?_)
        simp only [smul_eq_mul, hmfun]
        rw [show s - 3 / 2 + 1 / 2 = s - 1 by ring]
      rw [h2]
      exact h1
    have hcv : MellinConvergent mfun ((3 / 2 : ℝ) : ℂ) := by
      unfold MellinConvergent
      have h0 := hint 0 (by norm_num)
      refine h0.congr_fun (fun θ _ => ?_) measurableSet_Ioi
      have e : ((3 / 2 : ℝ) : ℂ) - 1 = (0 : ℂ) + 1 / 2 := by push_cast; ring
      simp only [smul_eq_mul, hmfun, e]
    have hvert : Complex.VerticalIntegrable (mellin mfun) (3 / 2 : ℝ) := by
      have hz : (fun y : ℝ => mellin mfun (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
          fun _ => 0 := by
        funext y
        exact hmel _ (by simp)
      unfold Complex.VerticalIntegrable
      rw [hz]
      exact integrable_zero _ _ _
    have hfx : ∀ x : ℝ, 0 < x → ContinuousAt mfun x :=
      fun x hx => hmc.continuousAt (Ioi_mem_nhds hx)
    have hzero : ∀ x : ℝ, 0 < x → mfun x = 0 := by
      intro x hx
      have key : mellinInv (3 / 2 : ℝ) (mellin mfun) x = 0 := by
        unfold mellinInv
        have hz0 : ∀ y : ℝ, mellin mfun (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0 :=
          fun y => hmel _ (by simp)
        simp only [hz0, smul_zero, integral_zero]
      rw [mellinInv_mellin_eq (3 / 2 : ℝ) mfun hx hcv hvert (hfx x hx)] at key
      exact key
    -- the asymptotic forces `𝔐(q) = 0`
    obtain ⟨C, b, hb, hAsy⟩ := hA
    have hC0 : 0 ≤ C := by
      have h0 := (norm_nonneg _).trans (hAsy b le_rfl)
      by_contra hneg
      push_neg at hneg
      have : C / b < 0 := div_neg_of_neg_of_pos hneg hb
      linarith
    have hbound : ∀ T : ℝ, b ≤ T →
        ‖Blueprint.Planar.quadrupole (q : ℝ → ℂ)‖ ≤ ‖QMI.quadElt‖ * (C / T) := by
      intro T hT
      have hTpos : 0 < T := lt_of_lt_of_le hb hT
      have hw0 : Blueprint.Planar.quadrupole (V T : ℝ → ℂ) = 0 := hzero T hTpos
      have hw1 : inner ℂ QMI.quadElt (V T) = 0 := by
        rw [← QMI.quadrupole_eq_inner]
        exact hw0
      have hwq : inner ℂ QMI.quadElt
          (Complex.exp (lam * T) • (T : ℂ) ^ (seedKappa ℓ q hq) • V T) = 0 := by
        rw [inner_smul_right, inner_smul_right, hw1, mul_zero, mul_zero]
      have hc : Blueprint.Planar.quadrupole (q : ℝ → ℂ) =
          inner ℂ QMI.quadElt (q - Complex.exp (lam * T) • (T : ℂ) ^ (seedKappa ℓ q hq) • V T) := by
        rw [QMI.quadrupole_eq_inner, inner_sub_right, hwq, sub_zero]
      rw [hc]
      calc ‖inner ℂ QMI.quadElt (q - Complex.exp (lam * T) • (T : ℂ) ^ (seedKappa ℓ q hq) • V T)‖
          ≤ ‖QMI.quadElt‖ * ‖q - Complex.exp (lam * T) • (T : ℂ) ^ (seedKappa ℓ q hq) • V T‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖QMI.quadElt‖ * (C / T) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            rw [norm_sub_rev]
            exact hAsy T hT
    have hcpos : 0 < ‖Blueprint.Planar.quadrupole (q : ℝ → ℂ)‖ := norm_pos_iff.2 hMq
    set c := ‖Blueprint.Planar.quadrupole (q : ℝ → ℂ)‖ with hcdef
    set A := ‖QMI.quadElt‖ with hAdef
    have hA0' : 0 ≤ A := norm_nonneg _
    have hAC : 0 ≤ A * C / c := div_nonneg (mul_nonneg hA0' hC0) hcpos.le
    set T : ℝ := b + A * C / c with hTdef
    have hTb : b ≤ T := by rw [hTdef]; linarith
    have hTpos : 0 < T := lt_of_lt_of_le hb hTb
    have h1 := hbound T hTb
    have h2 : c * T ≤ A * C := by
      have h3 := mul_le_mul_of_nonneg_right h1 hTpos.le
      rw [mul_assoc, div_mul_cancel₀ _ hTpos.ne'] at h3
      exact h3
    have h4 : c * T = c * b + A * C := by
      rw [hTdef]
      field_simp
    have hcb : 0 < c * b := mul_pos hcpos hb
    linarith

end UnforcedLeray.Short.PartI
