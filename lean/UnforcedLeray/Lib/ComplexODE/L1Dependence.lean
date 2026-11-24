import UnforcedLeray.Lib.ComplexODE.NeutralSolution
import NonUniqueEuler.P.Infra.ODE.Gronwall
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# L¹ dependence of linear ODE solutions on the coefficient (copy of two drafts)

Verbatim copy, for compilation inside `Lib/ComplexODE`, of the uncompiled drafts


(2026-10-26). The drafts are not edited; do not import them together with this module.
Scoping note `INF10-INF12-INF18-Planar.md` §5, target O3 input.

The estimates concern genuine solutions and their genuine first derivatives on a closed
interval. The perturbation is measured by the integral of its norm.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace UnforcedLeray.Rayleigh.Evans

/-- The interval-continuous version of the estimate, obtained from the
vendored integral Gronwall theorem after subtracting the initial bound. -/
theorem integral_gronwall_of_continuousOn
    {g e : ℝ → ℝ} {a b ε : ℝ}
    (he : ContinuousOn e (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg_nonneg : ∀ s ∈ Icc a b, 0 ≤ g s) (hε : 0 ≤ ε)
    (hineq : ∀ s ∈ Icc a b,
      e s ≤ ε + ∫ r in a..s, g r * e r) :
    ∀ t ∈ Icc a b, e t ≤ ε * Real.exp (∫ r in a..t, g r) := by
  have hcancel (s : ℝ) : ε + (e s - ε) = e s := by ring
  have h := NonUniqueEuler.LinODE.int_gronwall
    (u := fun s => e s - ε) (b := g) (c := ε)
    (he.sub continuousOn_const) hg hg_nonneg hε
    (fun s hs => by
      simpa only [hcancel] using (sub_le_iff_le_add'.mpr (hineq s hs)))
  simpa only [hcancel] using h

end UnforcedLeray.Rayleigh.Evans

noncomputable section
open Set Filter MeasureTheory Topology
namespace UnforcedLeray.Rayleigh.Evans
open NonUniqueEuler.LinODE

/-- An integral perturbation estimate for genuine solutions with the same initial data.
The pair carries its standard maximum norm. Only the reference first component
needs a uniform bound. -/
theorem norm_sub_le_integral_of_isSolOn
    {a b B : ℝ} {V₁ V₀ f₁ g₁ f₀ g₀ : ℝ → ℂ}
    (hab : a ≤ b) (hV₁ : ContinuousOn V₁ (Icc a b))
    (hV₀ : ContinuousOn V₀ (Icc a b))
    (h₁ : IsSolOn V₁ (Icc a b) f₁ g₁)
    (h₀ : IsSolOn V₀ (Icc a b) f₀ g₀)
    (hf : f₁ a = f₀ a) (hg : g₁ a = g₀ a)
    (hB : ∀ t ∈ Icc a b, ‖f₀ t‖ ≤ B) :
    ∀ t ∈ Icc a b,
      ‖(f₁ t - f₀ t, g₁ t - g₀ t)‖ ≤
        (B * ∫ s in a..b, ‖V₁ s - V₀ s‖) *
          Real.exp ((b - a) + ∫ s in a..b, ‖V₁ s‖) := by
  let z : ℝ → ℂ × ℂ := fun t => (f₁ t - f₀ t, g₁ t - g₀ t)
  let z' : ℝ → ℂ × ℂ := fun t => (g₁ t - g₀ t, V₁ t * f₁ t - V₀ t * f₀ t)
  let e : ℝ → ℝ := fun t => ‖z t‖
  let k : ℝ → ℝ := fun t => 1 + ‖V₁ t‖
  let q : ℝ → ℝ := fun t => ‖V₁ t - V₀ t‖
  let ε : ℝ := B * ∫ s in a..b, q s
  have hz : ContinuousOn z (Icc a b) :=
    (h₁.continuousOn.sub h₀.continuousOn).prodMk
      (h₁.continuousOn'.sub h₀.continuousOn')
  have hz' : ContinuousOn z' (Icc a b) :=
    (h₁.continuousOn'.sub h₀.continuousOn').prodMk
      ((hV₁.mul h₁.continuousOn).sub (hV₀.mul h₀.continuousOn))
  have he : ContinuousOn e (Icc a b) := hz.norm
  have hk : ContinuousOn k (Icc a b) := continuousOn_const.add hV₁.norm
  have hq : ContinuousOn q (Icc a b) := (hV₁.sub hV₀).norm
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  have hk0 (t : ℝ) : 0 ≤ k t := by dsimp [k]; positivity
  have hq0 (t : ℝ) : 0 ≤ q t := norm_nonneg _
  have hε0 : 0 ≤ ε := mul_nonneg hB0
    (intervalIntegral.integral_nonneg_of_forall hab hq0)
  have hza : z a = 0 := by simp [z, hf, hg]
  have hdz (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt z (z' t) t :=
    (((h₁.hasDerivWithinAt t (Ioo_subset_Icc_self ht)).sub
      (h₀.hasDerivWithinAt t (Ioo_subset_Icc_self ht))).prodMk
      ((h₁.hasDerivWithinAt' t (Ioo_subset_Icc_self ht)).sub
        (h₀.hasDerivWithinAt' t (Ioo_subset_Icc_self ht)))).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      ‖z' t‖ ≤ k t * e t + B * q t := by
    have hid : z' t = ((z t).2, V₁ t * (z t).1 + (V₁ t - V₀ t) * f₀ t) := by
      dsimp [z, z']; congr 1; ring
    rw [hid]
    apply GronwallAux.norm_deriv_pair_le (by dsimp [k]; linarith [norm_nonneg (V₁ t)])
      (mul_nonneg hB0 (hq0 t))
    · dsimp [k]; linarith [norm_nonneg (V₁ t)]
    · rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB t ht) (hq0 t)
  have hint (t : ℝ) (ht : t ∈ Icc a b) :
      e t ≤ ε + ∫ s in a..t, k s * e s := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hzt : (∫ s in a..t, z' s) = z t := by
      simpa [hza] using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hz.mono hsub) (fun s hs => hdz s ⟨hs.1, hs.2.trans_le ht.2⟩)
        ((hz'.mono hsub).intervalIntegrable_of_Icc ht.1)
    have hqi : (∫ s in a..t, q s) ≤ ∫ s in a..b, q s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (ae_of_all _ hq0) (hq.intervalIntegrable_of_Icc hab)
    calc
      e t = ‖∫ s in a..t, z' s‖ := by rw [hzt]
      _ ≤ ∫ s in a..t, ‖z' s‖ := intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t, k s * e s + B * q s :=
        intervalIntegral.integral_mono_on ht.1
          ((hz'.norm.mono hsub).intervalIntegrable_of_Icc ht.1)
          ((((hk.mul he).add (continuousOn_const.mul hq)).mono hsub).intervalIntegrable_of_Icc ht.1)
          (fun s hs => hbound s (hsub hs))
      _ = (∫ s in a..t, k s * e s) + B * ∫ s in a..t, q s := by
        rw [intervalIntegral.integral_add (f := fun s => k s * e s) (g := fun s => B * q s)
          (((hk.mul he).mono hsub).intervalIntegrable_of_Icc ht.1)
          (((continuousOn_const.mul hq).mono hsub).intervalIntegrable_of_Icc ht.1),
          intervalIntegral.integral_const_mul]
      _ ≤ ε + ∫ s in a..t, k s * e s := by
        dsimp [ε]; linarith [mul_le_mul_of_nonneg_left hqi hB0]
  have hgr := integral_gronwall_of_continuousOn he hk (fun t _ => hk0 t) hε0 hint
  intro t ht
  have hki : (∫ s in a..t, k s) ≤ ∫ s in a..b, k s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ hk0) (hk.intervalIntegrable_of_Icc hab)
  have hkeq : (∫ s in a..b, k s) = (b - a) + ∫ s in a..b, ‖V₁ s‖ := by
    dsimp [k]
    rw [intervalIntegral.integral_add
      (continuous_const.intervalIntegrable a b) (hV₁.norm.intervalIntegrable_of_Icc hab)]
    simp
  exact (hgr t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hki.trans_eq hkeq)) hε0)

/-- Integral convergence of continuous coefficients gives uniform convergence of
both genuine solution components on the closed interval. A uniform integral
bound for the coefficients follows from their integral convergence. -/
theorem tendstoUniformlyOn_of_integral_coefficient_convergence
    {ι : Type*} {l : Filter ι} {a b : ℝ}
    {V : ι → ℝ → ℂ} {V₀ f₀ g₀ : ℝ → ℂ} {f g : ι → ℝ → ℂ}
    (hab : a ≤ b) (hV : ∀ᶠ i in l, ContinuousOn (V i) (Icc a b))
    (hV₀ : ContinuousOn V₀ (Icc a b))
    (hsol : ∀ᶠ i in l, IsSolOn (V i) (Icc a b) (f i) (g i))
    (hsol₀ : IsSolOn V₀ (Icc a b) f₀ g₀)
    (hf : ∀ᶠ i in l, f i a = f₀ a) (hg : ∀ᶠ i in l, g i a = g₀ a)
    (hL1 : Tendsto (fun i => ∫ t in a..b, ‖V i t - V₀ t‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun i t => (f i t, g i t)) (fun t => (f₀ t, g₀ t))
      l (Icc a b) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hsol₀.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  let D : ι → ℝ := fun i => ∫ t in a..b, ‖V i t - V₀ t‖
  let M : ℝ := ∫ t in a..b, ‖V₀ t‖
  have hD0 (i : ι) : 0 ≤ D i :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => norm_nonneg _)
  have hmass (i : ι) (hVi : ContinuousOn (V i) (Icc a b)) : (∫ t in a..b, ‖V i t‖) ≤ D i + M := by
    calc
      (∫ t in a..b, ‖V i t‖) ≤ ∫ t in a..b, ‖V i t - V₀ t‖ + ‖V₀ t‖ :=
        intervalIntegral.integral_mono_on hab
          (hVi.norm.intervalIntegrable_of_Icc hab)
          (((hVi.sub hV₀).norm.add hV₀.norm).intervalIntegrable_of_Icc hab)
          (fun t _ => norm_le_norm_sub_add _ _)
      _ = D i + M := intervalIntegral.integral_add
        ((hVi.sub hV₀).norm.intervalIntegrable_of_Icc hab)
        (hV₀.norm.intervalIntegrable_of_Icc hab)
  have hscaled : Tendsto
      (fun i => (B * D i) * Real.exp ((b - a) + (1 + M))) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hL1.const_mul B).mul_const (Real.exp ((b - a) + (1 + M)))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ i in l, (B * D i) * Real.exp ((b - a) + (1 + M)) < ε :=
    hscaled.eventually (Iio_mem_nhds hε)
  have hunit : ∀ᶠ i in l, D i < 1 := hL1.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hsmall, hunit, hV, hsol, hf, hg] with i hi hiunit hVi hsoli hfi hgi
  intro t ht
  rw [dist_comm, dist_eq_norm]
  change ‖(f i t - f₀ t, g i t - g₀ t)‖ < ε
  have hest := norm_sub_le_integral_of_isSolOn hab hVi hV₀
    hsoli hsol₀ hfi hgi hB t ht
  have hexp : Real.exp ((b - a) + ∫ s in a..b, ‖V i s‖) ≤
      Real.exp ((b - a) + (1 + M)) :=
    Real.exp_le_exp.mpr (by linarith [hmass i hVi])
  exact (hest.trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg hB0 (hD0 i)))).trans_lt hi

/-- The chosen, actual global ODE solution is continuous in the integral norm of
the coefficient on every fixed finite interval, for fixed initial data. -/
theorem sol_tendstoUniformlyOn_of_integral_coefficients
    {ι : Type*} {l : Filter ι} {a b : ℝ} {V : ι → ℝ → ℂ} {V₀ : ℝ → ℂ}
    (hab : a ≤ b) (hV : ∀ᶠ i in l, Continuous (V i)) (hV₀ : Continuous V₀)
    (y₀ : ℂ × ℂ)
    (hL1 : Tendsto (fun i => ∫ t in a..b, ‖V i t - V₀ t‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun i => sol (V i) a y₀) (sol V₀ a y₀) l (Icc a b) := by
  have hspec₀ := sol_spec hV₀ a y₀
  simpa only [Prod.mk.eta] using
    tendstoUniformlyOn_of_integral_coefficient_convergence hab
      (hV.mono fun i hi => hi.continuousOn) hV₀.continuousOn
      (hV.mono fun i hi => (sol_spec hi a y₀).1.mono (subset_univ _))
      (hspec₀.1.mono (subset_univ _))
      (hV.mono fun i hi => congrArg Prod.fst ((sol_spec hi a y₀).2.trans hspec₀.2.symm))
      (hV.mono fun i hi => congrArg Prod.snd ((sol_spec hi a y₀).2.trans hspec₀.2.symm)) hL1

/-- Upper-half-plane Gaussian Rayleigh pairs converge to a genuine normalized
solution for any continuous limiting coefficient, once integral convergence of
the actual Gaussian coefficient has been established. This statement does not
assume or assert that a singular critical coefficient has that convergence. -/
theorem normalizedPair_tendstoUniformlyOn_of_integral_coefficients
    {ι : Type*} {l : Filter ι} {a b α : ℝ} {c : ι → ℂ} {V₀ : ℝ → ℂ}
    (hab : a ≤ b) (hc : ∀ᶠ i in l, 0 < (c i).im) (hV₀ : Continuous V₀)
    (hL1 : Tendsto
      (fun i => ∫ t in a..b, ‖rayleighPotential α t (c i) - V₀ t‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun i => normalizedPair α a (c i))
      (sol V₀ a (0, 1)) l (Icc a b) :=
  sol_tendstoUniformlyOn_of_integral_coefficients hab
    (hc.mono fun i hi => continuous_rayleighPotential α hi) hV₀ (0, 1) hL1

/-- In particular, the actual Evans endpoint value converges to the endpoint
value of the actual normalized solution for the limiting coefficient. -/
theorem evansFunction_tendsto_of_integral_coefficients
    {ι : Type*} {l : Filter ι} {a b α : ℝ} {c : ι → ℂ} {V₀ : ℝ → ℂ}
    (hab : a ≤ b) (hc : ∀ᶠ i in l, 0 < (c i).im) (hV₀ : Continuous V₀)
    (hL1 : Tendsto
      (fun i => ∫ t in a..b, ‖rayleighPotential α t (c i) - V₀ t‖) l (𝓝 0)) :
    Tendsto (fun i => evansFunction α a b (c i)) l (𝓝 ((sol V₀ a (0, 1) b).1)) :=
  (continuous_fst.tendsto _).comp
    ((normalizedPair_tendstoUniformlyOn_of_integral_coefficients hab hc hV₀ hL1).tendsto_at
      ⟨hab, le_rfl⟩)

end UnforcedLeray.Rayleigh.Evans
