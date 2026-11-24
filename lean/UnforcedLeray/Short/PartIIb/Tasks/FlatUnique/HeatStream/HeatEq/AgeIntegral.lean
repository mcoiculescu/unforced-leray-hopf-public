import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq.IbpKernel

/-!
# Part II-b, helper for leaf `PartII-b:T11/3/4` (`HeatConvEq`): the age derivative as a heat flow

Source of record: `the November 2 reference manuscript`, line 1924 and lines
1923-1927. The `η`-direction integration by parts (`hce_ibp_snd`) is the mirror of `hce_ibp_fst`
in `IbpKernel.lean`; `hce_age_integral` splits `∂_θ K = ∂_q² K + ∂_η² K` and transfers both
second derivatives to `ζ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem hce_ibp_snd {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * etaDer (etaDer ζ) (z - w) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hζd : Differentiable ℝ ζ := hζ.smooth.differentiable (by simp)
  have hζc : Continuous ζ := hζ.smooth.continuous
  have hEN : NiceStream c (etaDer ζ) := (niceStreamClosure c ζ ζ 0 hζ hζ).2.1
  have hEd : Differentiable ℝ (etaDer ζ) := hEN.smooth.differentiable (by simp)
  have hEc : Continuous (etaDer ζ) := hEN.smooth.continuous
  have hEEN : NiceStream c (etaDer (etaDer ζ)) :=
    (niceStreamClosure c (etaDer ζ) (etaDer ζ) 0 hEN hEN).2.1
  have hEEc : Continuous (etaDer (etaDer ζ)) := hEEN.smooth.continuous
  have hsub : Differentiable ℝ (fun w : ℝ × ℝ => z - w) :=
    (differentiable_const z).sub differentiable_id
  have hsubc : Continuous (fun w : ℝ × ℝ => z - w) := continuous_const.sub continuous_id
  obtain ⟨B, hB⟩ := hce_abs_zeta_le hc hζ
  obtain ⟨M, hM⟩ := hce_abs_fderiv_le hc hζ ((0 : ℝ), (1 : ℝ))
  obtain ⟨N, hN⟩ := hce_abs_fderiv_le hc hEN ((0 : ℝ), (1 : ℝ))
  have hG1d : Differentiable ℝ (fun w : ℝ × ℝ => ζ (z - w)) := hζd.comp hsub
  have hEzd : Differentiable ℝ (fun w : ℝ × ℝ => etaDer ζ (z - w)) := hEd.comp hsub
  have hG1c : Continuous (fun w : ℝ × ℝ => ζ (z - w)) := hζc.comp hsubc
  have hEzc : Continuous (fun w : ℝ × ℝ => etaDer ζ (z - w)) := hEc.comp hsubc
  have hEEzc : Continuous (fun w : ℝ × ℝ => etaDer (etaDer ζ) (z - w)) := hEEc.comp hsubc
  have hGder : ∀ x : ℝ × ℝ,
      fderiv ℝ (fun w : ℝ × ℝ => ζ (z - w)) x ((0 : ℝ), (1 : ℝ)) = -(etaDer ζ (z - x)) :=
    fun x => hce_fderiv_sub hζd z _ x
  have hEder : ∀ x : ℝ × ℝ,
      fderiv ℝ (fun w : ℝ × ℝ => etaDer ζ (z - w)) x ((0 : ℝ), (1 : ℝ)) =
        -(etaDer (etaDer ζ) (z - x)) :=
    fun x => hce_fderiv_sub hEd z _ x
  -- first integration by parts: `f = ∂_η K` against `g = ζ(z - ·)`
  have hI1a : Integrable (fun x : ℝ × ℝ =>
      fderiv ℝ (hceD2 θ) x ((0 : ℝ), (1 : ℝ)) * ζ (z - x)) :=
    (hce_int_A2 hθ hc hζ z).congr (ae_of_all _ fun x => by
      dsimp only
      rw [hce_fderiv_D2_snd hθ0])
  have hI1b : Integrable (fun x : ℝ × ℝ =>
      hceD2 θ x * fderiv ℝ (fun w : ℝ × ℝ => ζ (z - w)) x ((0 : ℝ), (1 : ℝ))) :=
    (hce_int_D2 hθ (c := fun w : ℝ × ℝ => -(etaDer ζ (z - w))) hEzc.neg
      (fun w => by rw [abs_neg]; exact hM (z - w))).congr (ae_of_all _ fun x => by
        dsimp only
        rw [hGder x])
  have hI1c : Integrable (fun x : ℝ × ℝ => hceD2 θ x * ζ (z - x)) :=
    hce_int_D2 hθ hG1c (fun w => hB (z - w))
  have ibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := hceD2 θ) (g := fun w : ℝ × ℝ => ζ (z - w)) (v := ((0 : ℝ), (1 : ℝ)))
    hI1a hI1b hI1c (fun x _ => (hceD2_diff hθ0) x) (fun x _ => hG1d x)
  have eL1 : ∫ x : ℝ × ℝ, hceD2 θ x * fderiv ℝ (fun w : ℝ × ℝ => ζ (z - w)) x
      ((0 : ℝ), (1 : ℝ)) = -∫ x : ℝ × ℝ, hceD2 θ x * etaDer ζ (z - x) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hGder x]
    ring
  have eR1 : ∫ x : ℝ × ℝ, fderiv ℝ (hceD2 θ) x ((0 : ℝ), (1 : ℝ)) * ζ (z - x) =
      ∫ x : ℝ × ℝ, (x.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0284.heatKernel2 θ x * ζ (z - x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hce_fderiv_D2_snd hθ0]
  have key1 : ∫ x : ℝ × ℝ, hceD2 θ x * etaDer ζ (z - x) =
      ∫ x : ℝ × ℝ, (x.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0284.heatKernel2 θ x * ζ (z - x) := by
    rw [eL1, eR1] at ibp1
    linarith
  -- second integration by parts: `f = K` against `g = ∂_η ζ(z - ·)`
  have hI2a : Integrable (fun x : ℝ × ℝ =>
      fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) x ((0 : ℝ), (1 : ℝ)) * etaDer ζ (z - x)) :=
    (hce_int_D2 hθ hEzc (fun w => hM (z - w))).congr (ae_of_all _ fun x => by
      dsimp only
      rw [hce_fderiv_K_snd hθ0])
  have hI2b : Integrable (fun x : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ x *
        fderiv ℝ (fun w : ℝ × ℝ => etaDer ζ (z - w)) x ((0 : ℝ), (1 : ℝ))) :=
    (hce_int_K hθ (c := fun w : ℝ × ℝ => -(etaDer (etaDer ζ) (z - w))) hEEzc.neg
      (fun w => by rw [abs_neg]; exact hN (z - w))).congr (ae_of_all _ fun x => by
        dsimp only
        rw [hEder x])
  have hI2c : Integrable (fun x : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ x * etaDer ζ (z - x)) :=
    hce_int_K hθ hEzc (fun w => hM (z - w))
  have ibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := UnforcedLeray.B0284.heatKernel2 θ) (g := fun w : ℝ × ℝ => etaDer ζ (z - w))
    (v := ((0 : ℝ), (1 : ℝ))) hI2a hI2b hI2c
    (fun x _ => (hce_K_diff hθ0) x) (fun x _ => hEzd x)
  have eL2 : ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ x *
      fderiv ℝ (fun w : ℝ × ℝ => etaDer ζ (z - w)) x ((0 : ℝ), (1 : ℝ)) =
      -∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ x * etaDer (etaDer ζ) (z - x) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hEder x]
    ring
  have eR2 : ∫ x : ℝ × ℝ, fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) x
      ((0 : ℝ), (1 : ℝ)) * etaDer ζ (z - x) =
      ∫ x : ℝ × ℝ, hceD2 θ x * etaDer ζ (z - x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hce_fderiv_K_snd hθ0]
  have key2 : ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ x * etaDer (etaDer ζ) (z - x) =
      ∫ x : ℝ × ℝ, hceD2 θ x * etaDer ζ (z - x) := by
    rw [eL2, eR2] at ibp2
    linarith
  linarith

/-- The age derivative of the planar Gaussian against a nice stream is the sum of the Gaussian
against `∂_q²ζ` and `∂_η²ζ`. -/
theorem hce_age_integral {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ζ (z - w) =
      (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * qDer (qDer ζ) (z - w)) +
        ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * etaDer (etaDer ζ) (z - w) := by
  have hpt : (fun w : ℝ × ℝ => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w *
        ζ (z - w)) =
      fun w : ℝ × ℝ => (w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
          UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w) +
        (w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
          UnforcedLeray.B0284.heatKernel2 θ w * ζ (z - w) := by
    funext w
    unfold UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative
    ring
  rw [hpt, integral_add (hce_int_A1 hθ hc hζ z) (hce_int_A2 hθ hc hζ z),
    hce_ibp_fst hθ hc hζ z, hce_ibp_snd hθ hc hζ z]

end UnforcedLeray.Short.IIb
