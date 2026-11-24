import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Young's inequality in time, frequency by frequency (INF02 T6, BP-A)


"`‖k_ξ‖_{L¹(dt)} ≤ 1`, Young's inequality in `t`, Fubini and Plancherel in `x` give
`‖∂_{ij}u‖_{L²(ℝ^{1+d})} ≤ ‖f‖₂`". Manuscript: the `q = 2` case of eq:free-stress-11
(`paper/main.tex` lines 7447–7477, blueprint unit B0423).

`lintegral_time_conv_le`: for measurable `F, G : ℝ × E → ℝ≥0∞` and a measurable kernel
`k : ℝ → E → ℝ≥0∞` with `∫_0^∞ k(r, ξ) dr ≤ c` for every `ξ`,
`∫_t ∫_{r>0} ∫_ξ k(r,ξ) F(t-r,ξ) G(t,ξ) ≤ c ‖F‖_{L²} ‖G‖_{L²}`.
All integrals are lower Lebesgue integrals, so no integrability hypothesis is needed.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [SFinite μ]

theorem lintegral_mul_le_sqrt (ν' : Measure ℝ) {f g : ℝ → ℝ≥0∞} (hf : AEMeasurable f ν')
    (hg : AEMeasurable g ν') :
    ∫⁻ t, f t * g t ∂ν' ≤ (∫⁻ t, f t ^ (2 : ℝ) ∂ν') ^ (1 / 2 : ℝ) *
      (∫⁻ t, g t ^ (2 : ℝ) ∂ν') ^ (1 / 2 : ℝ) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq ν' Real.HolderConjugate.two_two hf hg

/-- **Young in time, frequency by frequency.** -/
theorem lintegral_time_conv_le {F G : ℝ × E → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    {k : ℝ → E → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {c : ℝ≥0∞}
    (hkc : ∀ ξ, ∫⁻ r in Ioi 0, k r ξ ≤ c) :
    ∫⁻ t, ∫⁻ r in Ioi 0, (∫⁻ ξ, k r ξ * F (t - r, ξ) * G (t, ξ) ∂μ) ≤
      c * (∫⁻ p, F p ^ (2 : ℝ) ∂(volume.prod μ)) ^ (1 / 2 : ℝ) *
        (∫⁻ p, G p ^ (2 : ℝ) ∂(volume.prod μ)) ^ (1 / 2 : ℝ) := by
  -- measurability of the integrand in all three variables
  have hint : Measurable fun q : ℝ × (ℝ × E) => k q.2.1 q.2.2 * F (q.1 - q.2.1, q.2.2) *
      G (q.1, q.2.2) := by
    have h1 : Measurable fun q : ℝ × (ℝ × E) => k q.2.1 q.2.2 :=
      hk.comp (measurable_snd.fst.prodMk measurable_snd.snd)
    have h2 : Measurable fun q : ℝ × (ℝ × E) => F (q.1 - q.2.1, q.2.2) :=
      hF.comp ((measurable_fst.sub measurable_snd.fst).prodMk measurable_snd.snd)
    have h3 : Measurable fun q : ℝ × (ℝ × E) => G (q.1, q.2.2) :=
      hG.comp (measurable_fst.prodMk measurable_snd.snd)
    exact (h1.mul h2).mul h3
  -- step 1: for each `t`, swap `r` and `ξ`
  have step1 : ∀ t, ∫⁻ r in Ioi 0, (∫⁻ ξ, k r ξ * F (t - r, ξ) * G (t, ξ) ∂μ) =
      ∫⁻ ξ, (∫⁻ r in Ioi 0, k r ξ * F (t - r, ξ) * G (t, ξ)) ∂μ := by
    intro t
    refine lintegral_lintegral_swap ?_
    exact (hint.comp (measurable_const.prodMk measurable_id)).aemeasurable
  simp_rw [step1]
  -- step 2: swap `t` and `ξ`
  have hmeas2 : Measurable fun p : ℝ × E =>
      ∫⁻ r in Ioi 0, k r p.2 * F (p.1 - r, p.2) * G (p.1, p.2) := by
    have : Measurable fun q : (ℝ × E) × ℝ => k q.2 q.1.2 * F (q.1.1 - q.2, q.1.2) *
        G (q.1.1, q.1.2) :=
      hint.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  -- the two `L²` profiles
  have hFm2 : Measurable fun ξ : E => (∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    ((hF.pow_const _).lintegral_prod_left').pow_const _
  have hGm2 : Measurable fun ξ : E => (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    ((hG.pow_const _).lintegral_prod_left').pow_const _
  -- step 3: for each `ξ`
  have step3 : ∀ ξ, ∫⁻ t, ∫⁻ r in Ioi 0, k r ξ * F (t - r, ξ) * G (t, ξ) ≤
      c * ((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
    intro ξ
    have hm : Measurable fun q : ℝ × ℝ => k q.2 ξ * F (q.1 - q.2, ξ) * G (q.1, ξ) :=
      hint.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
    rw [lintegral_lintegral_swap hm.aemeasurable]
    have hinner : ∀ r, ∫⁻ t, k r ξ * F (t - r, ξ) * G (t, ξ) ≤
        k r ξ * ((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
      intro r
      have hFm : Measurable fun t : ℝ => F (t - r, ξ) :=
        hF.comp ((measurable_id.sub measurable_const).prodMk measurable_const)
      have hGm : Measurable fun t : ℝ => G (t, ξ) := hG.comp (measurable_id.prodMk measurable_const)
      calc ∫⁻ t, k r ξ * F (t - r, ξ) * G (t, ξ)
          = k r ξ * ∫⁻ t, F (t - r, ξ) * G (t, ξ) := by
            simp_rw [mul_assoc]; exact lintegral_const_mul _ (hFm.mul hGm)
        _ ≤ _ := by
            gcongr
            refine (lintegral_mul_le_sqrt volume hFm.aemeasurable hGm.aemeasurable).trans
              (le_of_eq ?_)
            rw [lintegral_sub_right_eq_self (fun s => F (s, ξ) ^ (2 : ℝ)) r]
    calc ∫⁻ r in Ioi 0, ∫⁻ t, k r ξ * F (t - r, ξ) * G (t, ξ)
        ≤ ∫⁻ r in Ioi 0, k r ξ * ((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := lintegral_mono fun r => hinner r
      _ = (∫⁻ r in Ioi 0, k r ξ) * ((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
          lintegral_mul_const _ (hk.comp (measurable_id.prodMk measurable_const))
      _ ≤ _ := by gcongr; exact hkc ξ
  -- the squares of the profiles
  have hsq : ∀ (H : ℝ × E → ℝ≥0∞), Measurable H →
      ∫⁻ ξ, (((∫⁻ s, H (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ∂μ =
        ∫⁻ p, H p ^ (2 : ℝ) ∂(volume.prod μ) := by
    intro H hH
    have e : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
      rw [← ENNReal.rpow_mul]; norm_num
    simp_rw [e]
    have hm : Measurable (Function.uncurry fun (ξ : E) (s : ℝ) => H (s, ξ) ^ (2 : ℝ)) :=
      (hH.pow_const _).comp measurable_swap
    rw [lintegral_lintegral_swap hm.aemeasurable,
      lintegral_prod _ (hH.pow_const _).aemeasurable]
  calc ∫⁻ ξ, (∫⁻ t, ∫⁻ r in Ioi 0, k r ξ * F (t - r, ξ) * G (t, ξ)) ∂μ
      ≤ ∫⁻ ξ, (c * ((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) ∂μ := lintegral_mono step3
    _ = c * ∫⁻ ξ, ((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ∂μ := lintegral_const_mul _ (hFm2.mul hGm2)
    _ ≤ c * ((∫⁻ ξ, (((∫⁻ s, F (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ ξ, (((∫⁻ s, G (s, ξ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ∂μ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
          hFm2.aemeasurable hGm2.aemeasurable
    _ = _ := by rw [hsq F hF, hsq G hG, mul_assoc]

end UnforcedLeray.Parabolic
