import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.Split.Tonelli

/-!
# Split helper: the Tonelli bound (T17/1)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The slice integral `h₀(x',Y) = ∫_0^c |G(x',Y,q)| dq`. -/
def t17sH0 (c : ℝ) (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (w : (ℝ × ℝ) × ℝ) : ℝ≥0∞ :=
  ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (G w.1 w.2 q))

theorem t17s_h0_meas (c : ℝ) (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j) :
    Measurable (t17sH0 c G) := by
  have h1 : Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ => ENNReal.ofReal (tensorNorm (G p.1.1 p.1.2 p.2)) :=
    (ENNReal.measurable_ofReal.comp (t17s_meas_tn G hG)).comp
      (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ => (p.1.1, p.1.2, p.2)) (by fun_prop)
  exact h1.lintegral_prod_right'

theorem t17s_h0_le (c : ℝ) (hc : 0 < c) (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j) (w : (ℝ × ℝ) × ℝ) :
    t17sH0 c G w ≤ ENNReal.ofReal c * (ENNReal.ofReal (1 + |w.2|) *
      (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (G w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)) := by
  have hm : Measurable fun q : ℝ => tensorNorm (G w.1 w.2 q) :=
    (t17s_meas_tn G hG).comp (f := fun q : ℝ => (w.1, w.2, q)) (by fun_prop)
  have h := t17s_holder c hc _ hm (fun q => Real.sqrt_nonneg _)
  refine h.trans ?_
  gcongr
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + |w.2|) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg w.2])
  calc _ = 1 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (G w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ) := (one_mul _).symm
    _ ≤ _ := by gcongr

theorem t17s_H_finite (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j)
    (hN : thinMoment c G ≠ ⊤) :
    ∫⁻ z : Space, ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (G (ε * z 0, ε * z 1) (z 2) q)) ≠ ⊤ := by
  have hmeas := t17s_h0_meas c G hG
  have e1 : (fun z : Space => ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (G (ε * z 0, ε * z 1) (z 2) q))) =
      fun z : Space => (fun w : (ℝ × ℝ) × ℝ => t17sH0 c G ((ε * w.1.1, ε * w.1.2), w.2))
        ((z 0, z 1), z 2) := by
    funext z; rfl
  rw [e1]
  have hK : Measurable fun w : (ℝ × ℝ) × ℝ => t17sH0 c G ((ε * w.1.1, ε * w.1.2), w.2) :=
    hmeas.comp (by fun_prop)
  rw [t17s_spaceProd.lintegral_comp hK, t17s_scale ε hε _ hmeas]
  refine ENNReal.mul_ne_top (by simp) ?_
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal c * thinMoment c G) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  · unfold thinMoment
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun w => t17s_h0_le c hc G hG w

theorem t17s_srcInt (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j)
    (hper : ∀ x' Y q, G x' Y (q + c) = G x' Y q) (hN : thinMoment c G ≠ ⊤) :
    ∫⁻ τ in Ioc 0 (2 * ε * c), ∫⁻ l in Ioo (0 : ℝ) 1,
      ∫⁻ z : Space, srcNorm (thinSource ε G) (τ + 2 * Real.log l) z ≠ ⊤ := by
  have hs := t17s_meas_src ε G hG
  have hs3 : Measurable fun q : (ℝ × ℝ) × Space =>
      srcNorm (thinSource ε G) (q.1.1 + 2 * Real.log q.1.2) q.2 :=
    hs.comp (f := fun q : (ℝ × ℝ) × Space => (q.1.1 + 2 * Real.log q.1.2, q.2))
      (((measurable_fst.comp measurable_fst).add (measurable_const.mul
        (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd)
  have hF : Measurable fun q : ℝ × ℝ => ∫⁻ z : Space,
      srcNorm (thinSource ε G) (q.1 + 2 * Real.log q.2) z := hs3.lintegral_prod_right'
  rw [lintegral_lintegral_swap (μ := volume.restrict (Ioc 0 (2 * ε * c)))
    (ν := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun τ l => ∫⁻ z : Space, srcNorm (thinSource ε G) (τ + 2 * Real.log l) z) hF.aemeasurable]
  have inner : ∀ l : ℝ, ∫⁻ τ in Ioc 0 (2 * ε * c), ∫⁻ z : Space,
      srcNorm (thinSource ε G) (τ + 2 * Real.log l) z =
      ENNReal.ofReal (2 * ε) * ∫⁻ z : Space, ∫⁻ q in Ioc 0 c,
        ENNReal.ofReal (tensorNorm (G (ε * z 0, ε * z 1) (z 2) q)) := by
    intro l
    have hm2 : Measurable fun q : ℝ × Space => srcNorm (thinSource ε G) (q.1 + 2 * Real.log l) q.2 :=
      hs.comp (f := fun q : ℝ × Space => (q.1 + 2 * Real.log l, q.2))
        ((measurable_fst.add measurable_const).prodMk measurable_snd)
    rw [lintegral_lintegral_swap (μ := volume.restrict (Ioc 0 (2 * ε * c))) (ν := volume)
      (f := fun τ z => srcNorm (thinSource ε G) (τ + 2 * Real.log l) z) hm2.aemeasurable]
    simp_rw [t17s_phase_integral ε c hε hc G hper]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [inner]
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
    mul_one]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (t17s_H_finite ε c hε hc G hG hN)


theorem t17s_srcInt_ae (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (G : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => G w.1 w.2.1 w.2.2 i j)
    (hper : ∀ x' Y q, G x' Y (q + c) = G x' Y q) (hN : thinMoment c G ≠ ⊤) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * ε * c))), ∫⁻ l in Ioo (0 : ℝ) 1,
      ∫⁻ z : Space, srcNorm (thinSource ε G) (τ + 2 * Real.log l) z < ⊤ := by
  have hs := t17s_meas_src ε G hG
  have hs3 : Measurable fun q : (ℝ × ℝ) × Space =>
      srcNorm (thinSource ε G) (q.1.1 + 2 * Real.log q.1.2) q.2 :=
    hs.comp (f := fun q : (ℝ × ℝ) × Space => (q.1.1 + 2 * Real.log q.1.2, q.2))
      (((measurable_fst.comp measurable_fst).add (measurable_const.mul
        (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd)
  have hF : Measurable fun q : ℝ × ℝ => ∫⁻ z : Space,
      srcNorm (thinSource ε G) (q.1 + 2 * Real.log q.2) z := hs3.lintegral_prod_right'
  have hX : Measurable fun τ : ℝ => ∫⁻ l in Ioo (0 : ℝ) 1,
      ∫⁻ z : Space, srcNorm (thinSource ε G) (τ + 2 * Real.log l) z :=
    hF.lintegral_prod_right'
  exact ae_lt_top' hX.aemeasurable (t17s_srcInt ε c hε hc G hG hper hN)

end UnforcedLeray.Short.IIIa

end
