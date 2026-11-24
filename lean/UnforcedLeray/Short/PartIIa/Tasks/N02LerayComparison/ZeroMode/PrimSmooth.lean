import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.ClosedParamIntegral

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1730 ("Take the
corresponding primitives to vanish at `η = 0`"). Prop: `ZeroPrimSmooth` (`Sub/N02_3.lean`).

Plan.
1. Rescale `[0, η]` to `[0, 1]`: `zPrimC g p = ∫ t in 0..1, p_η • g(p_s, p_q, p_η t)`.
2. The integrand `(x, t) ↦ x_η • g(x_s, x_q, x_η t)` is `C^∞` on `Profile × ℝ`, so the parametric
   integral is `C^∞` on the closed convex set `univ` (`contDiffOn_integral_closed`).
3. `∂_η (zPrimC g) = g` by the fundamental theorem of calculus along the `η`-line. No band
   hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroPrimSmoothAux

/-- The rescaled integrand `y ↦ y_η • g(y_s, y_q, y_η t)` on `Profile × ℝ` is `C^∞`. -/
lemma scaled_contDiff {g : Profile → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun y : Profile × ℝ => y.1.2.2 • g (y.1.1, y.1.2.1, y.1.2.2 * y.2)) := by
  have h1 : ContDiff ℝ ∞ (fun y : Profile × ℝ => y.1.2.2) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun y : Profile × ℝ => g (y.1.1, y.1.2.1, y.1.2.2 * y.2)) := by
    refine hg.comp ?_
    fun_prop
  exact h1.smul h2

/-- Rescaling: `zPrimC g w = ∫ t in 0..1, w_η • g(w_s, w_q, w_η t)`. -/
lemma zPrimC_eq (g : Profile → ℂ) :
    zPrimC g = fun w : Profile => ∫ t in (0 : ℝ)..1, w.2.2 • g (w.1, w.2.1, w.2.2 * t) := by
  funext w
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun t : ℝ => g (w.1, w.2.1, t)) w.2.2
  simp only [mul_zero, mul_one] at h
  show (∫ t in (0 : ℝ)..w.2.2, g (w.1, w.2.1, t))
    = ∫ t in (0 : ℝ)..1, w.2.2 • g (w.1, w.2.1, w.2.2 * t)
  rw [intervalIntegral.integral_smul]
  exact h.symm

/-- The primitive `zPrimC g` is `C^∞` on the whole profile space. -/
lemma zPrimC_contDiff {g : Profile → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (zPrimC g) := by
  rw [zPrimC_eq g, ← contDiffOn_univ]
  refine contDiffOn_infty.mpr fun n => ?_
  have hG : ContDiffOn ℝ (n : ℕ∞ω)
      (fun y : Profile × ℝ => y.1.2.2 • g (y.1.1, y.1.2.1, y.1.2.2 * y.2))
      (univ ×ˢ Icc (0 : ℝ) 1) :=
    ((scaled_contDiff hg).of_le (by exact_mod_cast le_top)).contDiffOn
  exact UnforcedLeray.Short.PartI.ClosedParamIntegral.contDiffOn_integral_closed
    isClosed_univ convex_univ uniqueDiffOn_univ n ℂ
    (fun (w : Profile) (t : ℝ) => w.2.2 • g (w.1, w.2.1, w.2.2 * t)) hG

/-- The `η`-derivative of the primitive is the integrand: `∂_η (zPrimC g) = g`. -/
lemma pdEta_zPrimC {g : Profile → ℂ} (hg : ContDiff ℝ ∞ g) (p : Profile) :
    pdEta (zPrimC g) p = g p := by
  have hc : Continuous fun t : ℝ => g (p.1, p.2.1, t) :=
    hg.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  -- the fundamental theorem of calculus along the `η`-line
  have hFTC : HasDerivAt (fun η : ℝ => ∫ t in (0 : ℝ)..η, g (p.1, p.2.1, t))
      (g (p.1, p.2.1, p.2.2)) p.2.2 :=
    (hc.integral_hasStrictDerivAt 0 p.2.2).hasDerivAt
  have hl : HasDerivAt (fun η : ℝ => ((p.1, p.2.1, η) : Profile))
      ((0 : ℝ), (0 : ℝ), (1 : ℝ)) p.2.2 := by
    have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun η : ℝ => η) (1 : ℝ) p.2.2 := by apply hasDerivAt_id'
    exact h1.prodMk (h2.prodMk h3)
  have hdiff : Differentiable ℝ (zPrimC g) :=
    (zPrimC_contDiff hg).differentiable (by simp)
  have hF : HasFDerivAt (zPrimC g) (fderiv ℝ (zPrimC g) p) p := (hdiff p).hasFDerivAt
  have hcomp : HasDerivAt (zPrimC g ∘ fun η : ℝ => ((p.1, p.2.1, η) : Profile))
      (fderiv ℝ (zPrimC g) p ((0 : ℝ), (0 : ℝ), (1 : ℝ))) p.2.2 :=
    hF.comp_hasDerivAt p.2.2 hl
  have hval : HasDerivAt (zPrimC g ∘ fun η : ℝ => ((p.1, p.2.1, η) : Profile))
      (g p) p.2.2 := hFTC
  exact hcomp.unique hval

end ZeroPrimSmoothAux

/-- **L1a (primitive: smoothness), proved.** For a smooth band function `g`, the primitive `zPrimC g`
is smooth and `∂_η (zPrimC g) = g`. The band hypothesis is not used. -/
theorem zeroPrimSmooth : ZeroPrimSmooth := by
  intro g hg _
  exact ⟨ZeroPrimSmoothAux.zPrimC_contDiff hg, fun p => ZeroPrimSmoothAux.pdEta_zPrimC hg p⟩

end UnforcedLeray.Short.PartIIa
