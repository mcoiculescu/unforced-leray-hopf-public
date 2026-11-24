import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Smoothing
import UnforcedLeray.Loc.L01Coefficient.HeatPeriodic
import UnforcedLeray.Lib.Kernels.GaussDeriv

/-!
# `HeatProfileRegularity` helper: the heat profile as a fixed-time heat smoothing

Helper module of `Loc/Hyp/HeatProfileRegularity.lean` (hypothesis `HeatProfileRegularity`,
infrastructure INF04, blueprint unit B0710; `paper/main.tex` lines 159–163 and 274–281).

The heat profile of lines 159–163 is
`H_h[u](y, τ) = e^{τ/2} [e^{h e^τ Δ} u](e^{τ/2} y)` (`Blueprint.heatProfile`). The change of
variables `z = e^{τ/2} w` in the heat integral (Gaussian scaling, as in
`L01.heat_integral_scale`, but with no self-similarity law) moves all the phase dependence
into the datum:
`H_h[u](·, τ) = e^{hΔ} u_τ`, `u_τ(x) = e^{τ/2} u(e^{τ/2} x)` (`heatProfile_eq_average`).

The family `u_τ` satisfies the bounds of lines 152–156 with the constants of `u`
(`invDist_dil`), and differences satisfy them with a constant `3C|σ - τ|` (`invDist_dil_sub`,
mean value theorem in the phase, using one more derivative of `u`: `k ≤ 4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ContDiff Topology

namespace UnforcedLeray.HeatProfileReg

/-- The rescaled datum `u_τ(x) = e^{τ/2} u(e^{τ/2} x)`. -/
def dil (τ : ℝ) (u : SpatialField) : SpatialField :=
  fun x => Real.exp (τ / 2) • u (Real.exp (τ / 2) • x)

/-- **The heat profile at phase `τ` is the heat smoothing at the fixed time `h` of `u_τ`**
(tex lines 159–163): `H_h[u](·, τ) = e^{hΔ}u_τ`. This holds for every `u` (both sides are
Bochner integrals related by a linear change of variables). -/
theorem heatProfile_eq_average {h : ℝ} (hh : 0 < h) (u : SpatialField) (τ : ℝ) :
    Blueprint.heatProfile h u τ = Heat.average h (dil τ u) := by
  funext y
  have hlam : 0 < Real.exp (τ / 2) := Real.exp_pos _
  have htime : h * Real.exp τ = Real.exp (τ / 2) ^ 2 * h := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (τ / 2) = τ by push_cast; ring, mul_comm]
  rw [Blueprint.heatProfile_apply, htime]
  have hr : Real.exp (τ / 2) ^ (-((3 : ℕ) : ℝ)) = (Real.exp (τ / 2) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hlam.le, Real.rpow_natCast]
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have h1 := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space)
    (fun z : Space => Heat.kernel (Real.exp (τ / 2) ^ 2 * h) z • u (Real.exp (τ / 2) • y - z))
    (Real.exp (τ / 2))
  rw [hfin] at h1
  have h2 : (fun w : Space => Heat.kernel (Real.exp (τ / 2) ^ 2 * h) (Real.exp (τ / 2) • w) •
      u (Real.exp (τ / 2) • y - Real.exp (τ / 2) • w)) =ᵐ[volume]
      fun w => (Real.exp (τ / 2) ^ 3)⁻¹ • (Heat.kernel h w • u (Real.exp (τ / 2) • (y - w))) := by
    filter_upwards with w
    rw [← smul_sub, ← Gaussian.gaussKernel_three_eq, Gaussian.gaussKernel_scale hlam hh, hr,
      smul_smul]
  rw [integral_congr_ae h2, integral_smul, abs_of_pos (inv_pos.mpr (pow_pos hlam 3))] at h1
  have h3 := (smul_right_injective Space (inv_ne_zero (pow_pos hlam 3).ne')) h1.symm
  rw [h3]
  simp only [Heat.average, dil]
  rw [← integral_smul]
  congr 1
  funext w
  exact smul_comm _ _ _

theorem dil_contDiffOn {u : SpatialField} (hu : ContDiffOn ℝ ∞ u {0}ᶜ) (τ : ℝ) :
    ContDiffOn ℝ ∞ (dil τ u) {0}ᶜ := by
  have hlam : Real.exp (τ / 2) ≠ 0 := (Real.exp_pos _).ne'
  have h1 : ContDiffOn ℝ ∞ (fun x : Space => u (Real.exp (τ / 2) • x)) {0}ᶜ :=
    hu.comp (contDiff_const_smul _).contDiffOn (fun x hx => smul_ne_zero hlam hx)
  exact h1.const_smul _

/-- `u_τ` satisfies the bounds of `u` (lines 152–156 are scale invariant). -/
theorem invDist_dil {u : SpatialField} (hu : ContDiffOn ℝ ∞ u {0}ᶜ) {C : ℝ}
    (hC : ∀ k : ℕ, k ≤ 3 → ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ k u x‖ ≤ C / ‖x‖ ^ (k + 1))
    (τ : ℝ) : InvDist (dil τ u) C where
  smooth := dil_contDiffOn hu τ
  bound := by
    intro k hk x hx
    have hl : 0 < Real.exp (τ / 2) := Real.exp_pos _
    have hx' : Real.exp (τ / 2) • x ≠ 0 := smul_ne_zero hl.ne' hx
    have hb := hC k hk _ hx'
    rw [norm_smul, Real.norm_of_nonneg hl.le, mul_pow] at hb
    show ‖iteratedFDeriv ℝ k (fun x => Real.exp (τ / 2) • u (Real.exp (τ / 2) • x)) x‖ ≤ _
    rw [Kernels.iteratedFDeriv_comp_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
    have he : Real.exp (τ / 2) * Real.exp (τ / 2) ^ k = Real.exp (τ / 2) ^ (k + 1) :=
      (pow_succ' _ _).symm
    calc Real.exp (τ / 2) * Real.exp (τ / 2) ^ k * ‖iteratedFDeriv ℝ k u (Real.exp (τ / 2) • x)‖
        ≤ Real.exp (τ / 2) * Real.exp (τ / 2) ^ k *
          (C / (Real.exp (τ / 2) ^ (k + 1) * ‖x‖ ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / ‖x‖ ^ (k + 1) := by
          rw [he, mul_div_assoc', mul_div_mul_left C _ (pow_pos hl _).ne']

/-- The phase-derivative estimate behind `invDist_dil_sub`. -/
theorem phase_deriv_bound {u : SpatialField} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k : ℕ, k ≤ 4 → ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ k u x‖ ≤ C / ‖x‖ ^ (k + 1))
    {k : ℕ} (hk : k ≤ 3) {x : Space} (hx : x ≠ 0) {l : ℝ} (hl : 0 < l) :
    ‖(l * l ^ k) • fderiv ℝ (iteratedFDeriv ℝ k u) (l • x) ((l * (1 / 2)) • x) +
        ((l * l ^ k) * (((k : ℝ) + 1) * (1 / 2))) • iteratedFDeriv ℝ k u (l • x)‖ ≤
      3 * C / ‖x‖ ^ (k + 1) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hl0 : l ≠ 0 := hl.ne'
  have hx0 : ‖x‖ ≠ 0 := hxn.ne'
  have hz : l • x ≠ 0 := smul_ne_zero hl0 hx
  have hzn : ‖l • x‖ = l * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hl.le]
  have h1 : ‖fderiv ℝ (iteratedFDeriv ℝ k u) (l • x)‖ ≤ C / (l * ‖x‖) ^ (k + 1 + 1) := by
    rw [norm_fderiv_iteratedFDeriv, ← hzn]; exact hC (k + 1) (by omega) _ hz
  have h2 : ‖iteratedFDeriv ℝ k u (l • x)‖ ≤ C / (l * ‖x‖) ^ (k + 1) := by
    rw [← hzn]; exact hC k (by omega) _ hz
  have hA : ‖(l * l ^ k) • fderiv ℝ (iteratedFDeriv ℝ k u) (l • x) ((l * (1 / 2)) • x)‖ ≤
      C / 2 / ‖x‖ ^ (k + 1) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc l * l ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ k u) (l • x) ((l * (1 / 2)) • x)‖
        ≤ l * l ^ k * (‖fderiv ℝ (iteratedFDeriv ℝ k u) (l • x)‖ * ‖(l * (1 / 2)) • x‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
      _ = l * l ^ k * (‖fderiv ℝ (iteratedFDeriv ℝ k u) (l • x)‖ * ((l * (1 / 2)) * ‖x‖)) := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ l * l ^ k * (C / (l * ‖x‖) ^ (k + 1 + 1) * ((l * (1 / 2)) * ‖x‖)) := by
          gcongr
      _ = C / 2 / ‖x‖ ^ (k + 1) := by
          field_simp
          ring
  have hB : ‖((l * l ^ k) * (((k : ℝ) + 1) * (1 / 2))) • iteratedFDeriv ℝ k u (l • x)‖ ≤
      ((k : ℝ) + 1) / 2 * C / ‖x‖ ^ (k + 1) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc l * l ^ k * (((k : ℝ) + 1) * (1 / 2)) * ‖iteratedFDeriv ℝ k u (l • x)‖
        ≤ l * l ^ k * (((k : ℝ) + 1) * (1 / 2)) * (C / (l * ‖x‖) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((k : ℝ) + 1) / 2 * C / ‖x‖ ^ (k + 1) := by
          field_simp
          ring
  refine (norm_add_le _ _).trans ((add_le_add hA hB).trans ?_)
  have hk' : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hr : 0 < ‖x‖ ^ (k + 1) := pow_pos hxn _
  rw [← add_div, div_le_div_iff_of_pos_right hr]
  nlinarith [mul_nonneg (sub_nonneg.2 hk') hC0]

/-- **Lipschitz dependence of `u_τ` on the phase**: `u_σ - u_τ` satisfies the bounds of lines
152–156 for `k ≤ 3` with constant `3C|σ - τ|`, where `C` bounds `u` for `k ≤ 4`. -/
theorem invDist_dil_sub {u : SpatialField} (hu : ContDiffOn ℝ ∞ u {0}ᶜ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k : ℕ, k ≤ 4 → ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ k u x‖ ≤ C / ‖x‖ ^ (k + 1))
    (σ τ : ℝ) : InvDist (dil σ u - dil τ u) (3 * C * |σ - τ|) where
  smooth := (dil_contDiffOn hu σ).sub (dil_contDiffOn hu τ)
  bound := by
    intro k hk x hx
    have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
    have hxs : ({0}ᶜ : Set Space) ∈ 𝓝 x := hopen.mem_nhds hx
    rw [iteratedFDeriv_sub_apply
      (((dil_contDiffOn hu σ).contDiffAt hxs).of_le (by exact_mod_cast le_top))
      (((dil_contDiffOn hu τ).contDiffAt hxs).of_le (by exact_mod_cast le_top))]
    have hE : ∀ s : ℝ,
        Real.exp (((k : ℝ) + 1) * (s / 2)) = Real.exp (s / 2) * Real.exp (s / 2) ^ k := by
      intro s
      rw [← pow_succ', ← Real.exp_nat_mul, Nat.cast_succ]
    have hφeq : ∀ s : ℝ, iteratedFDeriv ℝ k (dil s u) x =
        Real.exp (((k : ℝ) + 1) * (s / 2)) • iteratedFDeriv ℝ k u (Real.exp (s / 2) • x) := by
      intro s
      show iteratedFDeriv ℝ k (fun x => Real.exp (s / 2) • u (Real.exp (s / 2) • x)) x = _
      rw [Kernels.iteratedFDeriv_comp_smul, hE]
    have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (((k : ℝ) + 1) * (s / 2)) •
          iteratedFDeriv ℝ k u (Real.exp (s / 2) • x))
        (Real.exp (((k : ℝ) + 1) * (s / 2)) •
            fderiv ℝ (iteratedFDeriv ℝ k u) (Real.exp (s / 2) • x)
              ((Real.exp (s / 2) * (1 / 2)) • x) +
          (Real.exp (((k : ℝ) + 1) * (s / 2)) * (((k : ℝ) + 1) * (1 / 2))) •
            iteratedFDeriv ℝ k u (Real.exp (s / 2) • x)) s := by
      intro s
      have hz : Real.exp (s / 2) • x ≠ 0 := smul_ne_zero (Real.exp_pos _).ne' hx
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) (Real.exp (s / 2) • x) :=
        ((hu.contDiffAt (hopen.mem_nhds hz)).iteratedFDeriv_right (m := 1) (i := k)
          (by exact_mod_cast le_top)).differentiableAt one_ne_zero
      have hℓ : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (s / 2) * (1 / 2)) s :=
        ((hasDerivAt_id' s).div_const 2).exp
      have hin : HasDerivAt (fun s : ℝ => Real.exp (s / 2) • x)
          ((Real.exp (s / 2) * (1 / 2)) • x) s := hℓ.smul_const x
      have hg := hdiff.hasFDerivAt.comp_hasDerivAt s hin
      have hc : HasDerivAt (fun s : ℝ => Real.exp (((k : ℝ) + 1) * (s / 2)))
          (Real.exp (((k : ℝ) + 1) * (s / 2)) * (((k : ℝ) + 1) * (1 / 2))) s :=
        (((hasDerivAt_id' s).div_const 2).const_mul ((k : ℝ) + 1)).exp
      exact hc.smul hg
    have hbound : ∀ s : ℝ, ‖Real.exp (((k : ℝ) + 1) * (s / 2)) •
            fderiv ℝ (iteratedFDeriv ℝ k u) (Real.exp (s / 2) • x)
              ((Real.exp (s / 2) * (1 / 2)) • x) +
          (Real.exp (((k : ℝ) + 1) * (s / 2)) * (((k : ℝ) + 1) * (1 / 2))) •
            iteratedFDeriv ℝ k u (Real.exp (s / 2) • x)‖ ≤ 3 * C / ‖x‖ ^ (k + 1) := by
      intro s
      rw [hE s]
      exact phase_deriv_bound hC0 hC hk hx (Real.exp_pos _)
    have hmv := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => hbound s) (mem_univ τ) (mem_univ σ)
    rw [hφeq σ, hφeq τ]
    refine hmv.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs]
    ring

/-- One constant for the bounds of lines 152–156, `k ≤ 4`. -/
theorem uniform_bound {u : SpatialField}
    (hu : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ * ‖x‖ ^ (k + 1) ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≤ 4 → ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ ≤ C / ‖x‖ ^ (k + 1) := by
  choose C hC using hu
  refine ⟨∑ j : Fin 5, |C j (Nat.lt_succ_iff.mp j.isLt)|,
    Finset.sum_nonneg fun j _ => abs_nonneg _, fun k hk x hx => ?_⟩
  have hle : |C k hk| ≤ ∑ j : Fin 5, |C j (Nat.lt_succ_iff.mp j.isLt)| :=
    Finset.single_le_sum (f := fun j : Fin 5 => |C j (Nat.lt_succ_iff.mp j.isLt)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ ⟨k, by omega⟩)
  rw [le_div_iff₀ (pow_pos (norm_pos_iff.2 hx) _)]
  exact (hC k hk x hx).trans ((le_abs_self _).trans hle)

/-- Heat smoothing is linear on fields with convergent heat integrals. -/
theorem average_sub {h : ℝ} (hh : 0 < h) {b₁ b₂ : SpatialField} {ε₁ ε₂ : ℝ}
    (h₁ : InvDist b₁ ε₁) (h₂ : InvDist b₂ ε₂) :
    Heat.average h (b₁ - b₂) = Heat.average h b₁ - Heat.average h b₂ := by
  funext y
  simp only [Heat.average, Pi.sub_apply, smul_sub]
  exact integral_sub (heat_integrand_integrable hh h₁ y) (heat_integrand_integrable hh h₂ y)

end UnforcedLeray.HeatProfileReg
