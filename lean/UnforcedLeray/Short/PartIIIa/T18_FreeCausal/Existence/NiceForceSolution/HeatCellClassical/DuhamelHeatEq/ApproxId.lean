import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelSmooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Tendsto

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/4` (leaf D): approximate identity

Target: `duhEqApproxId : DuhEqApproxId` (`Sub/PartIIIa_T18_2_4_1_3.lean`), i.e.
`duhPhi ν h s x r -> h (s, x)` as `r -> 0+`. Source of record:
`the November 2 reference manuscript`, lines 3427-3440.

Proof. Write `duhPhi = A(r) + B(r)` for `r > 0`, where
`A(r) = ∫ G_{νr}(z) (h(s-r, x-z) - h(s, x-z)) dz` and `B(r) = ∫ G_{νr}(z) h(s, x-z) dz`.
* `‖A(r)‖ ≤ K₁ |r|` by the mean value theorem in the time variable (`K₁` bounds `D h`) and unit
  mass of `G_{νr}`.
* `B(r) → h(s, x)` by the spatial approximate identity `tendsto_heatConv_nhds` (real and imaginary
  parts separately).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Time-Lipschitz bound for a smooth source with bounded first derivatives. -/
theorem duhAI_time_lip {h : ℝ × (ℝ × ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) {K : ℝ}
    (hK : ∀ q, ‖iteratedFDeriv ℝ 1 h q‖ ≤ K) (s r : ℝ) (y : ℝ × ℝ) :
    ‖h (s - r, y) - h (s, y)‖ ≤ K * |r| := by
  have hdiff : Differentiable ℝ h := hh.differentiable (by simp)
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => h (t, y)) (fderiv ℝ h (t, y) (1, 0)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : ℝ × ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact (hdiff (t, y)).hasFDerivAt.comp_hasDerivAt t h1
  have hfd : ∀ q, ‖fderiv ℝ h q‖ ≤ K := fun q => by
    rw [← norm_iteratedFDeriv_one]; exact hK q
  have hone : ‖((1 : ℝ), (0 : ℝ × ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have hbound : ∀ t ∈ (univ : Set ℝ), ‖deriv (fun t : ℝ => h (t, y)) t‖ ≤ K := by
    intro t _
    rw [(hd t).deriv]
    calc ‖fderiv ℝ h (t, y) (1, 0)‖ ≤ ‖fderiv ℝ h (t, y)‖ * ‖((1 : ℝ), (0 : ℝ × ℝ))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * 1 := mul_le_mul (hfd (t, y)) hone (norm_nonneg _) ((norm_nonneg _).trans (hfd (t, y)))
      _ = K := mul_one K
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun t : ℝ => h (t, y)) (s := univ)
    (fun t _ => (hd t).differentiableAt) hbound convex_univ (mem_univ s) (mem_univ (s - r))
  have e : ‖s - r - s‖ = |r| := by
    rw [show s - r - s = -r by ring, norm_neg, Real.norm_eq_abs]
  rw [e] at key
  exact key

/-- Integrability of a real kernel times a bounded continuous complex function. -/
theorem duhAI_intC {g : ℝ × ℝ → ℝ} (hg : Integrable g) {φ : ℝ × ℝ → ℂ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ z, ‖φ z‖ ≤ M) : Integrable (fun z => ((g z : ℝ) : ℂ) * φ z) := by
  refine Integrable.mono' (hg.norm.mul_const M) ?_ (ae_of_all _ fun z => ?_)
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).mul
      hφ.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _)

/-- Integrability of a real kernel times a bounded continuous real function. -/
theorem duhAI_intR {g φ : ℝ × ℝ → ℝ} (hg : Integrable g) (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ z, ‖φ z‖ ≤ M) : Integrable (fun z => g z * φ z) := by
  refine Integrable.mono' (hg.norm.mul_const M)
    (hg.aestronglyMeasurable.mul hφ.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _)

theorem duhEqApproxId : UnforcedLeray.Short.IIIa.DuhEqApproxId := by
  unfold DuhEqApproxId
  intro c ν h hc hν hh s x
  have hcont : Continuous h := hh.1.continuous
  obtain ⟨K0, hK0⟩ := duhSm_bound hc hh 0
  obtain ⟨K1, hK1⟩ := duhSm_bound hc hh 1
  have hM0 : ∀ q, ‖h q‖ ≤ K0 := fun q => by simpa only [norm_iteratedFDeriv_zero] using hK0 q
  have key : ∀ r, duhPhi ν h s x r =
      ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s - r, x - z) :=
    fun r => rfl
  set f1 : ℝ × ℝ → ℝ := fun y => (h (s, y)).re with hf1
  set f2 : ℝ × ℝ → ℝ := fun y => (h (s, y)).im with hf2
  have hsl : Continuous fun y : ℝ × ℝ => h (s, y) := hcont.comp (by fun_prop)
  have hf1c : Continuous f1 := Complex.continuous_re.comp hsl
  have hf2c : Continuous f2 := Complex.continuous_im.comp hsl
  have hf1b : ∀ z, ‖f1 z‖ ≤ K0 := fun z => (by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM0 _))
  have hf2b : ∀ z, ‖f2 z‖ ≤ K0 := fun z => (by rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans (hM0 _))
  have hT1 := UnforcedLeray.Short.IIb.TendstoMain.tendsto_heatConv_nhds hf1c hf1b x
  have hT2 := UnforcedLeray.Short.IIb.TendstoMain.tendsto_heatConv_nhds hf2c hf2b x
  have hνr : Tendsto (fun r : ℝ => ν * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun r : ℝ => ν * r) (𝓝 0) (𝓝 (ν * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hν hr
  -- the spatial part at fixed time `s` in complex form
  have hBeq : ∀ r : ℝ, 0 < r →
      ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s, x - z)
        = (((∫ z : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * r) z * f1 (x - z) : ℝ)) : ℂ)
          + (((∫ z : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * r) z * f2 (x - z) : ℝ)) : ℂ)
            * Complex.I := by
    intro r hr
    have hθ : 0 < ν * r := mul_pos hν hr
    have hG := UnforcedLeray.B0284.integrable_heatKernel2 hθ
    have hxz1 : Continuous fun z : ℝ × ℝ => f1 (x - z) := hf1c.comp (by fun_prop)
    have hxz2 : Continuous fun z : ℝ × ℝ => f2 (x - z) := hf2c.comp (by fun_prop)
    have hf1i := duhAI_intR hG hxz1 (M := K0) (fun z => hf1b _)
    have hf2i := duhAI_intR hG hxz2 (M := K0) (fun z => hf2b _)
    have hpt : ∀ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s, x - z)
        = (((UnforcedLeray.B0284.heatKernel2 (ν * r) z * f1 (x - z) : ℝ)) : ℂ)
          + (((UnforcedLeray.B0284.heatKernel2 (ν * r) z * f2 (x - z) : ℝ)) : ℂ) * Complex.I := by
      intro z
      have e := Complex.re_add_im (h (s, x - z))
      simp only [hf1, hf2]
      conv_lhs => rw [← e]
      push_cast
      ring
    have j1 : Integrable (fun z : ℝ × ℝ =>
        (((UnforcedLeray.B0284.heatKernel2 (ν * r) z * f1 (x - z) : ℝ)) : ℂ)) := hf1i.ofReal
    have j2 : Integrable (fun z : ℝ × ℝ =>
        (((UnforcedLeray.B0284.heatKernel2 (ν * r) z * f2 (x - z) : ℝ)) : ℂ) * Complex.I) :=
      hf2i.ofReal.mul_const Complex.I
    simp_rw [hpt]
    rw [integral_add j1 j2, integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
  -- the time-shift part is `O(r)`
  have hlin : Tendsto (fun r : ℝ => K1 * |r|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => K1 * |r|) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun r : ℝ => K1 * |r| := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hAbd : ∀ r : ℝ, 0 < r →
      ‖∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        (h (s - r, x - z) - h (s, x - z))‖ ≤ K1 * |r| := by
    intro r hr
    have hθ : 0 < ν * r := mul_pos hν hr
    have hI := (UnforcedLeray.B0284.integrable_heatKernel2 hθ).const_mul (K1 * |r|)
    calc _ ≤ ∫ z : ℝ × ℝ, K1 * |r| * UnforcedLeray.B0284.heatKernel2 (ν * r) z := by
          refine norm_integral_le_of_norm_le hI (ae_of_all _ fun z => ?_)
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ z)]
          calc _ ≤ UnforcedLeray.B0284.heatKernel2 (ν * r) z * (K1 * |r|) :=
                mul_le_mul_of_nonneg_left (duhAI_time_lip hh.1 hK1 s r (x - z))
                  (UnforcedLeray.B0284.heatKernel2_nonneg hθ z)
            _ = K1 * |r| * UnforcedLeray.B0284.heatKernel2 (ν * r) z := by ring
      _ = K1 * |r| := by
          rw [integral_const_mul, UnforcedLeray.B0284.integral_heatKernel2 hθ, mul_one]
  have hA0 : Tendsto (fun r : ℝ => ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
      (h (s - r, x - z) - h (s, x - z))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [self_mem_nhdsWithin] with r hr using hAbd r hr
  -- the spatial part tends to `h (s, x)`
  have hEq : ((f1 x : ℝ) : ℂ) + ((f2 x : ℝ) : ℂ) * Complex.I = h (s, x) := by
    simp only [hf1, hf2]
    exact Complex.re_add_im _
  have hR1 := (Complex.continuous_ofReal.tendsto (f1 x)).comp (hT1.comp hνr)
  have hR2 := (Complex.continuous_ofReal.tendsto (f2 x)).comp (hT2.comp hνr)
  have hlim := hR1.add (hR2.mul_const Complex.I)
  have hB : Tendsto (fun r : ℝ => ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s, x - z))
      (𝓝[>] (0 : ℝ)) (𝓝 (h (s, x))) := by
    rw [← hEq]
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hBeq r hr).symm
  -- splitting `duhPhi` into the two parts for `r > 0`
  have hsplit : ∀ r : ℝ, 0 < r → duhPhi ν h s x r =
      (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        (h (s - r, x - z) - h (s, x - z)))
      + ∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) * h (s, x - z) := by
    intro r hr
    have hθ : 0 < ν * r := mul_pos hν hr
    have hG := UnforcedLeray.B0284.integrable_heatKernel2 hθ
    have hc1 : Continuous fun z : ℝ × ℝ => h (s - r, x - z) := hcont.comp (by fun_prop)
    have hc2 : Continuous fun z : ℝ × ℝ => h (s, x - z) := hcont.comp (by fun_prop)
    have i1 : Integrable (fun z : ℝ × ℝ => ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        (h (s - r, x - z) - h (s, x - z))) := duhAI_intC hG (hc1.sub hc2) (M := K0 + K0) (fun z => by
      show ‖h (s - r, x - z) - h (s, x - z)‖ ≤ K0 + K0
      have h1 := norm_sub_le (h (s - r, x - z)) (h (s, x - z))
      have h2 := hM0 (s - r, x - z)
      have h3 := hM0 (s, x - z)
      linarith)
    have i2 := duhAI_intC hG hc2 (M := K0) (fun z => by
      show ‖h (s, x - z)‖ ≤ K0
      exact hM0 _)
    rw [key r, ← integral_add i1 i2]
    congr 1
    funext z
    ring
  have hfin := hA0.add hB
  rw [zero_add] at hfin
  apply hfin.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hsplit r hr).symm

end UnforcedLeray.Short.IIIa
