import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.FlowMeas
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_3

/-!
# Leaf (d) of `PartIII-a:T21/c3/3/1/1`, part 2: joint measurability tools

Joint measurability in `(r, y)` of derivatives of parametrised families, of the cylinder
Biot-Savart kernel in its period, and of the periodised sums `perSum (d r) f y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf4Aux

/-- Joint measurability of directional derivatives of a jointly measurable family of
differentiable functions. -/
lemma measurable_fderiv_apply_param {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (g : ℝ → ℝ × ℝ → F)
    (hg : Measurable (fun p : ℝ × (ℝ × ℝ) => g p.1 p.2))
    (hd : ∀ r y, DifferentiableAt ℝ (g r) y) (v : ℝ × ℝ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (g p.1) p.2 v) := by
  have hlim : ∀ p : ℝ × (ℝ × ℝ), Tendsto
      (fun n : ℕ => (((n : ℝ) + 1) : ℝ) • (g p.1 (p.2 + (((n : ℝ) + 1)⁻¹) • v) - g p.1 p.2))
      atTop (𝓝 (fderiv ℝ (g p.1) p.2 v)) := by
    intro p
    have h1 : HasDerivAt (fun t : ℝ => p.2 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.2
    have h2 : HasDerivAt (fun t : ℝ => g p.1 (p.2 + t • v)) (fderiv ℝ (g p.1) (p.2 + (0 : ℝ) • v) v) 0 :=
      (by simpa using (hd p.1 p.2).hasFDerivAt : HasFDerivAt (g p.1) (fderiv ℝ (g p.1) (p.2 + (0 : ℝ) • v)) (p.2 + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h1
    have h3 := hasDerivAt_iff_tendsto_slope_zero.1 h2
    have h4 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), Eventually.of_forall fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff]
      positivity
    have h5 := h3.comp h4
    simpa [Function.comp_def, inv_inv] using h5
  refine measurable_of_tendsto_metrizable (fun n : ℕ => ?_) (tendsto_pi_nhds.2 hlim)
  have hm1 : Measurable (fun p : ℝ × (ℝ × ℝ) => g p.1 (p.2 + (((n : ℝ) + 1)⁻¹) • v)) :=
    hg.comp (measurable_fst.prodMk (measurable_snd.add_const _))
  exact (hm1.sub hg).const_smul ((((n : ℝ) + 1) : ℝ))


/-- Clamping of the age to `[t₁, t₂]`. -/
def rho (t₁ t₂ r : ℝ) : ℝ := max t₁ (min r t₂)

lemma continuous_rho (t₁ t₂ : ℝ) : Continuous (rho t₁ t₂) := by
  unfold rho; fun_prop

lemma rho_mem {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (r : ℝ) : rho t₁ t₂ r ∈ Icc t₁ t₂ := by
  unfold rho
  exact ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

lemma rho_eq {t₁ t₂ r : ℝ} (h : r ∈ Icc t₁ t₂) : rho t₁ t₂ r = r := by
  unfold rho
  rw [min_eq_left h.2, max_eq_right h.1]

/-- Joint measurability of the periodised sums `perSum (d(r)) f y` (with `r` clamped). -/
lemma measurable_perSum_joint {f : ℝ × ℝ → ℂ} (hf : Continuous f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    {ν t₁ t₂ c : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen c (clockA ν r)) :
    Measurable (fun p : ℝ × (ℝ × ℝ) =>
      perSum (cellLen c (clockA ν (rho t₁ t₂ p.1))) f p.2) := by
  set G : ℝ → ℝ × ℝ → ℂ := fun r x =>
    perSum (cellLen c (clockA ν (rho t₁ t₂ r))) f
      (x.1 / Real.sqrt (clockA ν (rho t₁ t₂ r)), x.2 / Real.sqrt (clockA ν (rho t₁ t₂ r))) with hG
  have hGcont : ∀ x, Continuous (fun r => G r x) := fun x =>
    (FlowMeas.continuousOn_perSum_scaled hf hC0 hC hν ht hd1 x).comp_continuous
      (continuous_rho t₁ t₂) (rho_mem hts)
  have hGm : ∀ r, Measurable (G r) := by
    intro r
    have hd : cellLen c (clockA ν (rho t₁ t₂ r)) ≠ 0 := by
      have := hd1 _ (rho_mem hts r)
      linarith
    exact ((FrameCont.perSum_continuous hf hC hd).comp
      ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _))).measurable
  have hU := measurable_uncurry_of_continuous_of_measurable hGcont hGm
  have hs : Measurable (fun r : ℝ => Real.sqrt (clockA ν (rho t₁ t₂ r))) := by
    have : Continuous (fun r : ℝ => Real.sqrt (clockA ν (rho t₁ t₂ r))) := by
      unfold clockA; have := continuous_rho t₁ t₂; fun_prop
    exact this.measurable
  have hs1 : Measurable (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (clockA ν (rho t₁ t₂ p.1))) :=
    hs.comp measurable_fst
  have hmap : Measurable (fun p : ℝ × (ℝ × ℝ) => (p.1,
      (Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.1,
        Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.2))) := by fun_prop
  have heq : (fun p : ℝ × (ℝ × ℝ) =>
      perSum (cellLen c (clockA ν (rho t₁ t₂ p.1))) f p.2) =
      fun p => Function.uncurry G (p.1, (Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.1,
        Real.sqrt (clockA ν (rho t₁ t₂ p.1)) * p.2.2)) := by
    funext p
    have hpos : Real.sqrt (clockA ν (rho t₁ t₂ p.1)) ≠ 0 := by
      have h1 := hd1 _ (rho_mem hts p.1)
      have : 1 ≤ clockA ν (rho t₁ t₂ p.1) := by
        have := rho_mem hts p.1
        exact one_le_clockA hν.le (ht.trans this.1)
      exact (Real.sqrt_pos.2 (by linarith)).ne'
    simp only [Function.uncurry, hG, mul_div_cancel_left₀ _ hpos]
  rw [heq]
  exact hU.comp hmap

end Leaf4Aux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
