import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Shift.Pair

/-!
# Part II-b, leaf `PartII-b:T12/1/4/2/2` (`PPLShift`): periodicity of the weak limit

Source of record: `the November 2 reference manuscript` lines 1933-1935.
Pair `H_N(· + c) - H_N` against `ψ ∈ L²(W_M)` (the translate of `ψ` lives in `W_{M+1}`), pass to the
weak limit on `W_{M+1}` and `W_M`, and test the difference against its own conjugate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Translation by `c` in the first variable. -/
def ppShift (c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + c, z.2)

lemma measurePreserving_ppShift (c : ℝ) :
    MeasurePreserving (ppShift c) volume volume := by
  have h := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (c, 0)
  have : ppShift c = fun z : ℝ × ℝ => z + (c, 0) := by
    funext z; exact Prod.ext (by simp [ppShift]) (by simp [ppShift])
  rw [this]; exact h

lemma measurable_ppShift (c : ℝ) : Measurable (ppShift c) :=
  (measurePreserving_ppShift c).measurable

/-- Memberships `L²` for the translate `f(· + c)` on `W_M`, from `L²(W_{M+1})`. -/
lemma memLp_shift_window {c : ℝ} (hc : 0 < c) {M : ℕ} {f : ℝ × ℝ → CMerid}
    (hf : MemLp f 2 (volume.restrict (ppWindow c (M + 1)))) :
    MemLp (fun z => f (ppShift c z)) 2 (volume.restrict (ppWindow c M)) := by
  have hmp := (measurePreserving_ppShift c).restrict_preimage (measurableSet_ppWindow c (M + 1))
  have h1 : MemLp (f ∘ ppShift c) 2 (volume.restrict (ppShift c ⁻¹' ppWindow c (M + 1))) :=
    hf.comp_measurePreserving hmp
  refine h1.mono_measure (Measure.restrict_mono ?_ le_rfl)
  intro z hz
  simp only [ppWindow, ppShift, Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
  push_cast
  constructor <;> nlinarith [hz.1, hz.2]

/-- The translated test function `ψ'(w) = 1_{W_M}(w - c) ψ(w - c)`. -/
def ppTr (c : ℝ) (M : ℕ) (ψ : ℝ × ℝ → CMerid) (w : ℝ × ℝ) : CMerid :=
  (ppWindow c M).indicator ψ (w.1 - c, w.2)

lemma ppTr_support {c : ℝ} (hc : 0 < c) (M : ℕ) (ψ : ℝ × ℝ → CMerid) {w : ℝ × ℝ}
    (hw : w ∉ ppWindow c (M + 1)) : ppTr c M ψ w = 0 := by
  unfold ppTr
  apply Set.indicator_of_notMem
  intro h
  apply hw
  simp only [ppWindow, Set.mem_setOf_eq] at h ⊢
  push_cast
  constructor <;> nlinarith [h.1, h.2]

lemma memLp_ppTr {c : ℝ} (hc : 0 < c) {M : ℕ} {ψ : ℝ × ℝ → CMerid}
    (hψ : MemLp ψ 2 (volume.restrict (ppWindow c M))) :
    MemLp (ppTr c M ψ) 2 (volume.restrict (ppWindow c (M + 1))) := by
  have h0 : MemLp ((ppWindow c M).indicator ψ) 2 volume :=
    (memLp_indicator_iff_restrict (measurableSet_ppWindow c M)).2 hψ
  have hmp : MeasurePreserving (fun w : ℝ × ℝ => (w.1 - c, w.2)) volume volume := by
    have h := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (-c, 0)
    have : (fun w : ℝ × ℝ => (w.1 - c, w.2)) = fun z : ℝ × ℝ => z + (-c, 0) := by
      funext z; exact Prod.ext (by simp [sub_eq_add_neg]) (by simp)
    rw [this]; exact h
  have h1 : MemLp (ppTr c M ψ) 2 volume := h0.comp_measurePreserving hmp
  exact h1.restrict _

lemma window_shift_pairing {c : ℝ} (hc : 0 < c) (M : ℕ) (h ψ : ℝ × ℝ → CMerid) :
    ∫ z in ppWindow c (M + 1), ∑ i : Fin 2, h z i * ppTr c M ψ z i =
      ∫ z in ppWindow c M, ∑ i : Fin 2, h (ppShift c z) i * ψ z i := by
  have hW := measurableSet_ppWindow c M
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have := integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun w : ℝ × ℝ => ∑ i : Fin 2, h w i * ppTr c M ψ w i) ((c, 0) : ℝ × ℝ)
    rw [← this]
    rw [← integral_indicator hW]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have hz' : z + ((c, 0) : ℝ × ℝ) = ppShift c z :=
      Prod.ext (by simp [ppShift]) (by simp [ppShift])
    by_cases hz : z ∈ ppWindow c M
    · simp [ppTr, hz', ppShift, Set.indicator_of_mem hz]
    · simp [ppTr, hz', ppShift, Set.indicator_of_notMem hz]
  · intro w hw
    simp [ppTr_support hc M ψ hw]

lemma conjVec_conjVec (v : CMerid) : conjVec (conjVec v) = v := by
  ext i; simp [conjVec_apply]

lemma sum_mul_conj (a : CMerid) :
    ∑ i : Fin 2, a i * (conjVec a) i = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ i : Fin 2, a i * (conjVec a) i = ((‖a i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [conjVec_apply, Complex.mul_conj']; push_cast; rfl
  simp_rw [h]
  rw [← Complex.ofReal_sum, EuclideanSpace.norm_sq_eq]

theorem pplShift : UnforcedLeray.Short.IIb.PPLShift := by
  unfold PPLShift
  intro r C c F H hctx φ G hφ hG M
  obtain ⟨hr, hC, hc, hF, hF2, hP⟩ := hctx
  have hGM : MemLp G 2 (volume.restrict (ppWindow c M)) := hG.1 M
  have hGM1 : MemLp G 2 (volume.restrict (ppWindow c (M + 1))) := hG.1 (M + 1)
  have hGc : MemLp (fun z => G (ppShift c z)) 2 (volume.restrict (ppWindow c M)) :=
    memLp_shift_window hc hGM1
  -- key pairing identity
  have key : ∀ ψ : ℝ × ℝ → CMerid, MemLp ψ 2 (volume.restrict (ppWindow c M)) →
      ∫ z in ppWindow c M, ∑ i : Fin 2, G (ppShift c z) i * ψ z i =
        ∫ z in ppWindow c M, ∑ i : Fin 2, G z i * ψ z i := by
    intro ψ hψ
    have hA : Tendsto (fun N => ∫ z in ppWindow c M,
        ∑ i : Fin 2, H (φ N) (ppShift c z) i * ψ z i) atTop
        (𝓝 (∫ z in ppWindow c M, ∑ i : Fin 2, G (ppShift c z) i * ψ z i)) := by
      have h1 := hG.2 (M + 1) (ppTr c M ψ) (memLp_ppTr hc hψ)
      simp only [window_shift_pairing hc M] at h1
      exact h1
    have hB := hG.2 M ψ hψ
    -- difference tends to zero
    have hΔ : Tendsto (fun N => eLpNorm (fun z : ℝ × ℝ => H (φ N) (ppShift c z) - H (φ N) z) 2
        (volume.restrict (ppWindow c M))) atTop (𝓝 0) :=
      (hP.almostPeriodic M).comp hφ.tendsto_atTop
    have hψfin : eLpNorm ψ 2 (volume.restrict (ppWindow c M)) ≠ ⊤ := hψ.2.ne
    have he : Tendsto (fun N => eLpNorm (fun z : ℝ × ℝ => H (φ N) (ppShift c z) - H (φ N) z) 2
        (volume.restrict (ppWindow c M)) * eLpNorm ψ 2 (volume.restrict (ppWindow c M)))
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hΔ (Or.inr hψfin)
      simpa using this
    have hmemH : ∀ N, MemLp (fun z => H (φ N) (ppShift c z)) 2
        (volume.restrict (ppWindow c M)) := fun N =>
      memLp_shift_window hc (hP.memLp (φ N) (M + 1)).1
    have hmemH0 : ∀ N, MemLp (H (φ N)) 2 (volume.restrict (ppWindow c M)) := fun N =>
      (hP.memLp (φ N) M).1
    have hdiff : Tendsto (fun N => (∫ z in ppWindow c M,
        ∑ i : Fin 2, H (φ N) (ppShift c z) i * ψ z i) -
        ∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) z i * ψ z i) atTop (𝓝 0) := by
      have hbd : ∀ N, ‖(∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) (ppShift c z) i * ψ z i) -
          ∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) z i * ψ z i‖ ≤
          (eLpNorm (fun z : ℝ × ℝ => H (φ N) (ppShift c z) - H (φ N) z) 2
            (volume.restrict (ppWindow c M)) *
            eLpNorm ψ 2 (volume.restrict (ppWindow c M))).toReal := by
        intro N
        have hDm : MemLp (fun z : ℝ × ℝ => H (φ N) (ppShift c z) - H (φ N) z) 2
            (volume.restrict (ppWindow c M)) := (hmemH N).sub (hmemH0 N)
        have heq : (∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) (ppShift c z) i * ψ z i) -
            ∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) z i * ψ z i =
            ∫ z in ppWindow c M, ∑ i : Fin 2,
              (H (φ N) (ppShift c z) - H (φ N) z) i * ψ z i := by
          rw [← integral_sub (integrable_pair (hmemH N) hψ) (integrable_pair (hmemH0 N) hψ)]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          simp [sub_mul, Finset.sum_sub_distrib]
        rw [heq]
        have h3 := enorm_integral_pair_le (p := 2) (q := 2) (μ := volume.restrict (ppWindow c M))
          hDm.1 hψ.1
        have hfin : eLpNorm (fun z : ℝ × ℝ => H (φ N) (ppShift c z) - H (φ N) z) 2
            (volume.restrict (ppWindow c M)) *
            eLpNorm ψ 2 (volume.restrict (ppWindow c M)) ≠ ⊤ :=
          (ENNReal.mul_lt_top hDm.2 hψ.2).ne
        have := ENNReal.toReal_mono hfin h3
        simpa using this
      refine squeeze_zero_norm hbd ?_
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    have h2 := hA.sub hB
    exact sub_eq_zero.1 (tendsto_nhds_unique h2 hdiff)
  -- conclude with the test function conj(D)
  set D : ℝ × ℝ → CMerid := fun z => G (ppShift c z) - G z with hD
  have hDm : MemLp D 2 (volume.restrict (ppWindow c M)) := hGc.sub hGM
  have hψm : MemLp (fun z => conjVec (D z)) 2 (volume.restrict (ppWindow c M)) :=
    hDm.of_le (continuous_conjVec.comp_aestronglyMeasurable hDm.1)
      (ae_of_all _ fun z => by simp [norm_conjVec])
  have h0 := key _ hψm
  have h1 : ∫ z in ppWindow c M, ∑ i : Fin 2, D z i * (conjVec (D z)) i = 0 := by
    have heq : ∫ z in ppWindow c M, ∑ i : Fin 2, D z i * (conjVec (D z)) i =
        (∫ z in ppWindow c M, ∑ i : Fin 2, G (ppShift c z) i * (conjVec (D z)) i) -
        ∫ z in ppWindow c M, ∑ i : Fin 2, G z i * (conjVec (D z)) i := by
      rw [← integral_sub (integrable_pair hGc hψm) (integrable_pair hGM hψm)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp [hD, sub_mul, Finset.sum_sub_distrib]
    rw [heq, h0, sub_self]
  simp_rw [sum_mul_conj] at h1
  rw [integral_complex_ofReal] at h1
  have h2 : ∫ z in ppWindow c M, ‖D z‖ ^ 2 = 0 := by exact_mod_cast h1
  have hint : Integrable (fun z => ‖D z‖ ^ 2) (volume.restrict (ppWindow c M)) := by
    have := (integrable_pair hDm hψm)
    have h3 : (fun z => ∑ i : Fin 2, D z i * (conjVec (D z)) i) =
        fun z => (((‖D z‖ ^ 2 : ℝ)) : ℂ) := funext fun z => sum_mul_conj (D z)
    rw [h3] at this
    refine this.re.congr (ae_of_all _ fun z => ?_)
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  have h4 := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint).1 h2
  filter_upwards [h4] with z hz
  have : ‖D z‖ ^ 2 = 0 := hz
  have h5 : D z = 0 := norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  exact sub_eq_zero.1 h5

end UnforcedLeray.Short.IIb
