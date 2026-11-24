import UnforcedLeray.Lib.ComplexODEB.Energy
import UnforcedLeray.Analysis.Rayleigh.IntervalHolder
import NonUniqueEuler.P.Infra.ODE.Existence
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# B0034 helper: normalized unstable Dirichlet modes and their uniform bounds

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of the continuation behind B0034 (`paper/main.tex`, lines 1012–1048: the
normalization `‖F_N‖_{L²} = 1` and the bounds `st18-t00036` without `1/Im c`, here at a
real wavenumber `β`). An upper-half-plane zero of `evansFunction β a b` gives a mode
`u` with `u(a) = u(b) = 0`, `∫ |u|² = 1`, `u'' = V u` and `∫ |u''|² ≤ 2β⁴ + 128`
(`exists_normalizedDirichlet`). Consequently `u'` is uniformly bounded and
`1/2`-Hölder on `[a, b]` (`NormalizedDirichlet.holder`, `NormalizedDirichlet.sup`).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Sturm
open UnforcedLeray.GaussianPotential

/-- A normalized unstable Dirichlet mode at wavenumber `β` and speed `c`. -/
structure NormalizedDirichlet (a b β : ℝ) (c : ℂ) (u u' : ℝ → ℂ) : Prop where
  hasDeriv : ∀ t, HasDerivAt u (u' t) t
  hasDeriv' : ∀ t, HasDerivAt u' (rayleighPotential β t c * u t) t
  smooth' : ContDiff ℝ 1 u'
  left : u a = 0
  right : u b = 0
  mass : (∫ t in a..b, ‖u t‖ ^ 2) = 1
  energy : (∫ t in a..b, ‖rayleighPotential β t c * u t‖ ^ 2) ≤ 2 * β ^ 4 + 128

theorem exists_normalizedDirichlet {a b β : ℝ} (hab : a < b) {c : ℂ} (hc : 0 < c.im)
    (hz : evansFunction β a b c = 0) : ∃ u u', NormalizedDirichlet a b β c u u' := by
  set F := normalizedF β a c with hF
  set F' := normalizedDerivative β a c with hF'
  have hFd : ∀ t, HasDerivAt F (F' t) t := hasDerivAt_normalizedF β a hc
  have hF'd : ∀ t, HasDerivAt F' (rayleighPotential β t c * F t) t :=
    hasDerivAt_normalizedDerivative β a hc
  have hFc : Continuous F := (normalizedF_smooth β a hc).continuous
  have hF'c : Continuous F' := (normalizedDerivative_smooth β a hc).continuous
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ t in a..b, ‖F t‖ ^ 2 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by
    rw [hm]; exact intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    exfalso
    have hz0 : ∀ t ∈ Ioo a b, ‖F t‖ = 0 :=
      eq_zero_of_integral_sq_eq_zero hFc.norm.continuousOn (by rw [← hm, h])
    have hd0 : ∀ t ∈ Ioo a b, F' t = 0 := by
      intro t ht
      have hloc : F =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact norm_eq_zero.mp (hz0 s hs)
      exact (hFd t).unique ((hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hloc)
    have hlim : Tendsto F' (𝓝[>] a) (𝓝 (F' a)) :=
      hF'c.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim0 : Tendsto F' (𝓝[>] a) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact (hd0 t ht).symm
    have := tendsto_nhds_unique hlim hlim0
    rw [hF', normalizedDerivative_initial β a hc] at this
    exact one_ne_zero this
  set n : ℝ := Real.sqrt m with hn
  have hnpos : 0 < n := Real.sqrt_pos.mpr hmpos
  set κ : ℂ := ((1 / n : ℝ) : ℂ) with hκ
  have hnκ : ‖κ‖ ^ 2 * m = 1 := by
    rw [hκ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), div_pow,
      one_pow, hn, Real.sq_sqrt hm0]
    field_simp
  refine ⟨fun t => κ * F t, fun t => κ * F' t, ⟨fun t => (hFd t).const_mul κ,
    fun t => ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have := (hF'd t).const_mul κ
    refine this.congr_deriv ?_
    ring
  · exact contDiff_const.mul ((normalizedDerivative_smooth β a hc).of_le
      (by exact_mod_cast le_top))
  · show κ * F a = 0
    rw [show F a = 0 from normalizedF_initial β a hc, mul_zero]
  · show κ * F b = 0
    rw [show F b = evansFunction β a b c from rfl, hz, mul_zero]
  · have : (fun t => ‖κ * F t‖ ^ 2) = fun t => ‖κ‖ ^ 2 * ‖F t‖ ^ 2 := by
      funext t; rw [norm_mul, mul_pow]
    rw [this, intervalIntegral.integral_const_mul, ← hm, hnκ]
  · have hE := energy_bound hab.le hc hz
    have : (fun t => ‖rayleighPotential β t c * (κ * F t)‖ ^ 2) =
        fun t => ‖κ‖ ^ 2 * ‖rayleighPotential β t c * F t‖ ^ 2 := by
      funext t; rw [mul_left_comm, norm_mul, mul_pow]
    rw [this, intervalIntegral.integral_const_mul]
    calc ‖κ‖ ^ 2 * (∫ t in a..b, ‖rayleighPotential β t c * F t‖ ^ 2)
        ≤ ‖κ‖ ^ 2 * ((2 * β ^ 4 + 128) * m) := by
          rw [hm]; exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)
      _ = 2 * β ^ 4 + 128 := by rw [mul_left_comm, hnκ, mul_one]

namespace NormalizedDirichlet

variable {a b β : ℝ} {c : ℂ} {u u' : ℝ → ℂ}

/-- `1/2`-Hölder bound for `u'` on `[a, b]`. -/
theorem holder (h : NormalizedDirichlet a b β c u u') (hab : a ≤ b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖u' t - u' s‖ ≤ Real.sqrt (2 * β ^ 4 + 128) * Real.sqrt |t - s| := by
  have hd : ∀ x, deriv u' x = rayleighPotential β x c * u x := fun x => (h.hasDeriv' x).deriv
  have hcont : Continuous (fun x => ‖rayleighPotential β x c * u x‖ ^ 2) :=
    (h.smooth'.continuous_deriv le_rfl |>.congr hd).norm.pow 2
  have hint : IntegrableOn (fun x => ‖rayleighPotential β x c * u x‖ ^ 2) (Ioc a b) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hsub : ∀ p q, a ≤ p → q ≤ b →
      (∫ x in Ioc p q, ‖deriv u' x‖ ^ 2) ≤ 2 * β ^ 4 + 128 := by
    intro p q hp hq
    have e : (fun x => ‖deriv u' x‖ ^ 2) = fun x => ‖rayleighPotential β x c * u x‖ ^ 2 :=
      funext fun x => by rw [hd]
    rw [e]
    have hE : (∫ x in Ioc a b, ‖rayleighPotential β x c * u x‖ ^ 2) ≤ 2 * β ^ 4 + 128 := by
      rw [← intervalIntegral.integral_of_le hab]; exact h.energy
    refine le_trans ?_ hE
    exact setIntegral_mono_set hint (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall (Ioc_subset_Ioc hp hq))
  rcases le_total s t with hst | hst
  · have key := norm_sub_le_sqrt_derivative_mass h.smooth' hst
    rw [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm]
    exact key.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hsub s t hs.1 ht.2)) (Real.sqrt_nonneg _))
  · have key := norm_sub_le_sqrt_derivative_mass h.smooth' hst
    rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst), mul_comm]
    exact key.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hsub t s ht.1 hs.2)) (Real.sqrt_nonneg _))

/-- Uniform bound for `u'` on `[a, b]`. -/
theorem sup (h : NormalizedDirichlet a b β c u u') (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖u' t‖ ≤ 2 * (Real.sqrt (2 * β ^ 4 + 128) * Real.sqrt (b - a)) := by
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun x => (h.hasDeriv x).continuousAt
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero (f := fun x => (u x).re)
    (f' := fun x => (u' x).re) hab (Complex.continuous_re.comp huc).continuousOn
    (by simp [h.left, h.right]) (fun x _ => hasDerivAt_re_comp (h.hasDeriv x))
  obtain ⟨η, hη, hη0⟩ := exists_hasDerivAt_eq_zero (f := fun x => (u x).im)
    (f' := fun x => (u' x).im) hab (Complex.continuous_im.comp huc).continuousOn
    (by simp [h.left, h.right]) (fun x _ => by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (h.hasDeriv x)
      exact this)
  have hlen : ∀ x ∈ Icc a b, Real.sqrt |t - x| ≤ Real.sqrt (b - a) := fun x hx =>
    Real.sqrt_le_sqrt (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hx.1, hx.2])
  have hre : |(u' t).re| ≤ Real.sqrt (2 * β ^ 4 + 128) * Real.sqrt (b - a) := by
    have h1 := h.holder hab.le (Ioo_subset_Icc_self hξ) ht
    have h2 : |(u' t).re| ≤ ‖u' t - u' ξ‖ := by
      have := Complex.abs_re_le_norm (u' t - u' ξ)
      simpa [Complex.sub_re, hξ0] using this
    exact h2.trans (h1.trans (mul_le_mul_of_nonneg_left (hlen ξ (Ioo_subset_Icc_self hξ))
      (Real.sqrt_nonneg _)))
  have him : |(u' t).im| ≤ Real.sqrt (2 * β ^ 4 + 128) * Real.sqrt (b - a) := by
    have h1 := h.holder hab.le (Ioo_subset_Icc_self hη) ht
    have h2 : |(u' t).im| ≤ ‖u' t - u' η‖ := by
      have := Complex.abs_im_le_norm (u' t - u' η)
      simpa [Complex.sub_im, hη0] using this
    exact h2.trans (h1.trans (mul_le_mul_of_nonneg_left (hlen η (Ioo_subset_Icc_self hη))
      (Real.sqrt_nonneg _)))
  calc ‖u' t‖ ≤ |(u' t).re| + |(u' t).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by linarith

end NormalizedDirichlet

end UnforcedLeray.ComplexODEB
