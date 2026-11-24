import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatGBSmall

/-!
# `flatXiContinuous : FlatXiContinuous` (decomposition of `PartIII-b:C/flatset/col/3`, leaf 5)

Source of record `the November 2 reference manuscript` lines 4610 (`ξ_B` as a
causal integral), 4614-4615 (`g_B = O(s^{3/2})`).

Route: `ξ_B(s) = s^{-μ} ∫_{(0,s]} t^μ 𝒰(s,t) g_B(t) dt` (`xiD_apply`).
* `g_B` is continuous on `(0,∞)` (`gBD_apply`, `H_cont`, `R_cont`), and `‖g_B(t)‖ ≤ K t^{3/2}` on
  `(0,S]` (`flatGBSmall` on `(0,1]`, compactness on `[1,S]`).
* `𝒰` is jointly continuous with a continuous vector family (`jointG_contOn`, from `jointCont`
  and `locBdd`).
* For `s` near `s₀ > 0` the integral over `(0,s]` is the integral over `(0,S]` of the indicator of
  `(0,s]`; dominated convergence (`continuousAt_of_dominated`) with bound `C K t^{μ+3/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

variable {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
  {tr : UnforcedLeray.B0140.TrainSol ν c}

/-- Joint continuity of `(s,t) ↦ 𝒰(s,t) g(t)` on `{0 < t ≤ s}` for a vector family `g`
continuous on `(0,∞)`. -/
theorem jointG_contOn (ev : TrainEvolution m tr) (g : ℝ → Xmc c m) (hg : ContinuousOn g (Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => ev.U p.1 p.2 (g p.2)) {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} := by
  rintro p0 ⟨hp0a, hp0b⟩
  unfold ContinuousWithinAt
  obtain ⟨Cb, hCb⟩ := ev.locBdd (p0.1 + 1)
  have hA : Tendsto (fun p : ℝ × ℝ => ‖g p.2 - g p0.2‖) (𝓝[{p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}] p0)
      (𝓝 0) := by
    have hc : ContinuousWithinAt (fun p : ℝ × ℝ => g p.2) {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} p0 :=
      (hg p0.2 hp0a).comp continuous_snd.continuousWithinAt (fun p hp => hp.1)
    have h : ContinuousWithinAt (fun p : ℝ × ℝ => ‖g p.2 - g p0.2‖)
        {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} p0 :=
      (hc.sub (continuousWithinAt_const (b := g p0.2))).norm
    have h' : Tendsto (fun p : ℝ × ℝ => ‖g p.2 - g p0.2‖) (𝓝[{p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}] p0)
        (𝓝 ‖g p0.2 - g p0.2‖) := h
    simpa using h'
  have hB' : Tendsto (fun p : ℝ × ℝ => ‖ev.U p.1 p.2 (g p0.2) - ev.U p0.1 p0.2 (g p0.2)‖)
      (𝓝[{p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}] p0) (𝓝 0) := by
    have hc0 : ContinuousWithinAt (fun p : ℝ × ℝ => ev.U p.1 p.2 (g p0.2))
        {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} p0 :=
      ContinuousWithinAt.mono (ev.jointCont (g p0.2) p0 ⟨hp0a.le, hp0b⟩)
        (fun p hp => ⟨hp.1.le, hp.2⟩)
    have h : ContinuousWithinAt (fun p : ℝ × ℝ => ‖ev.U p.1 p.2 (g p0.2) - ev.U p0.1 p0.2 (g p0.2)‖)
        {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} p0 :=
      (hc0.sub (continuousWithinAt_const (b := ev.U p0.1 p0.2 (g p0.2)))).norm
    have h' : Tendsto (fun p : ℝ × ℝ => ‖ev.U p.1 p.2 (g p0.2) - ev.U p0.1 p0.2 (g p0.2)‖)
        (𝓝[{p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}] p0)
        (𝓝 ‖ev.U p0.1 p0.2 (g p0.2) - ev.U p0.1 p0.2 (g p0.2)‖) := h
    simpa using h'
  have hsum := (hA.const_mul Cb).add hB'
  rw [mul_zero, zero_add] at hsum
  have hev : ∀ᶠ p in 𝓝 p0, p.1 < p0.1 + 1 :=
    (continuous_fst.tendsto p0).eventually (gt_mem_nhds (by linarith))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with p hp hpK
  obtain ⟨hpa, hpb⟩ := hpK
  have hC : ‖ev.U p.1 p.2‖ ≤ Cb := hCb p.1 p.2 hpa.le hpb hp.le
  have e : ev.U p.1 p.2 (g p.2) - ev.U p0.1 p0.2 (g p0.2)
      = ev.U p.1 p.2 (g p.2 - g p0.2)
        + (ev.U p.1 p.2 (g p0.2) - ev.U p0.1 p0.2 (g p0.2)) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

/-- `g_B` is continuous on `(0,∞)` (source 4605-4608). -/
theorem gBD_contOn (D : FlatInstData κ ν c m tr) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ContinuousOn B (Ioi 0)) : ContinuousOn (gBD D B) (Ioi 0) := by
  have hij : ∀ i j : Fin 3, ContinuousOn (fun t => B t i j) (Ioi 0) := fun i j =>
    ((continuous_id : Continuous fun M : Matrix (Fin 3) (Fin 3) ℝ => M).matrix_elem i j).comp_continuousOn hB
  have hdR : ContinuousOn (fun t => ((Bd (B t) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (((hij 0 0).sub (hij 2 2)).div_const 2)
  have heR : ContinuousOn (fun t => ((Be (B t) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (((hij 0 2).add (hij 2 0)).div_const 2)
  have hbR : ContinuousOn (fun t => ((ConcreteYF.Bbeta (B t) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (((hij 0 0).add (hij 2 2)).div_const 2)
  have hH : ContinuousOn (fun t => D.src.H t) (Ioi 0) := D.src.H_cont.continuousOn
  have hHc : ContinuousOn (fun t => conjX (D.src.H t)) (Ioi 0) :=
    continuous_conjX.comp_continuousOn hH
  have hR : ContinuousOn (fun t => D.src.R t) (Ioi 0) := D.src.R_cont.continuousOn
  have ha : ContinuousOn (fun t => -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ)
      - Complex.I * ((Be (B t) : ℝ) : ℂ))) (Ioi 0) :=
    continuousOn_const.mul (hdR.sub (continuousOn_const.mul heR))
  have hb : ContinuousOn (fun t => -(1 / 2 : ℂ) * (((Bd (B t) : ℝ) : ℂ)
      + Complex.I * ((Be (B t) : ℝ) : ℂ))) (Ioi 0) :=
    continuousOn_const.mul (hdR.add (continuousOn_const.mul heR))
  refine ContinuousOn.congr (((ha.smul hH).add (hb.smul hHc)).sub (hbR.smul hR)) ?_
  intro t _
  exact gBD_apply D B t

/-- The bound `‖g_B(t)‖ ≤ K t^{3/2}` on `(0,S]`. -/
theorem gBD_bound (D : FlatInstData κ ν c m tr)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ)
    (hbd : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ i j, |B s i j| ≤ C * s ^ (3 / 2 : ℝ))
    (hgc : ContinuousOn (gBD D B) (Ioi 0)) (S : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Ioc (0 : ℝ) S, ‖gBD D B t‖ ≤ K * t ^ (3 / 2 : ℝ) := by
  obtain ⟨C1, hC1⟩ := flatGBSmall κ ν c m tr D B C hbd
  have hcont : ContinuousOn (fun t => ‖gBD D B t‖) (Icc 1 S) :=
    (hgc.mono (fun t ht => lt_of_lt_of_le one_pos ht.1)).norm
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C1| + |C2|, by positivity, fun t ht => ?_⟩
  rcases le_or_gt t 1 with h1 | h1
  · have h := hC1 t ⟨ht.1, h1⟩
    calc ‖gBD D B t‖ ≤ C1 * t ^ (3 / 2 : ℝ) := h
      _ ≤ |C1| * t ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg ht.1.le _)
      _ ≤ (|C1| + |C2|) * t ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C2]) (Real.rpow_nonneg ht.1.le _)
  · have hA : ‖gBD D B t‖ ≤ C2 := by simpa using hC2 t ⟨h1.le, ht.2⟩
    have hge : 1 ≤ t ^ (3 / 2 : ℝ) := Real.one_le_rpow h1.le (by norm_num)
    calc ‖gBD D B t‖ ≤ C2 := hA
      _ ≤ |C2| := le_abs_self _
      _ ≤ |C2| * t ^ (3 / 2 : ℝ) := le_mul_of_one_le_right (abs_nonneg _) hge
      _ ≤ (|C1| + |C2|) * t ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) (Real.rpow_nonneg ht.1.le _)

/-- **`ξ_B` is continuous on `(0,∞)`** (source 4610, 4614-4615). -/
theorem flatXiContinuous : FlatXiContinuous := by
  intro κ ν c m hm hc tr D μ B C hμ hB hbd
  intro s0 hs0
  apply ContinuousAt.continuousWithinAt
  have hs0' : (0 : ℝ) < s0 := hs0
  have hgc : ContinuousOn (gBD D B) (Ioi 0) := gBD_contOn D B hB
  obtain ⟨K, hK0, hKb⟩ := gBD_bound D B C hbd hgc (s0 + 1)
  obtain ⟨Cs, hCs⟩ := D.ev.locBdd (s0 + 1)
  have hCs0 : 0 ≤ Cs := (norm_nonneg (D.ev.U 0 0)).trans (hCs 0 0 le_rfl le_rfl (by linarith))
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → Xmc c m, ∀ s t, G s t =
      (Ioc 0 s).indicator (fun t => ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t)) t :=
    ⟨_, fun _ _ => rfl⟩
  have hS : s0 < s0 + 1 := by linarith
  -- integrability of the dominating function
  have hint : Integrable (fun t : ℝ => (Cs * K) * t ^ (μ + 3 / 2)) (volume.restrict (Ioc 0 (s0 + 1))) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s0 + 1)
      (show -1 < μ + 3 / 2 by linarith)
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ s0 + 1)).1 h
    exact Integrable.const_mul h2 (Cs * K)
  -- measurability for the nearby parameters
  have hF_meas : ∀ᶠ s in 𝓝 s0, AEStronglyMeasurable (G s) (volume.restrict (Ioc 0 (s0 + 1))) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (μ : ℂ)) (Ioc 0 s) := fun t _ =>
      (Complex.continuousAt_ofReal_cpow_const t μ (Or.inl (by simpa using hμ))).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => D.ev.U s t (gBD D B t)) (Ioc 0 s) := by
      have hmap : ContinuousOn (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Ioc 0 s) :=
        (continuous_const.prodMk continuous_id).continuousOn
      exact (jointG_contOn D.ev (gBD D B) hgc).comp hmap (fun t ht => ⟨ht.1, ht.2⟩)
    have hfc : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) • D.ev.U s t (gBD D B t)) (Ioc 0 s) :=
      h1.smul h2
    have hGs : G s = (Ioc 0 s).indicator (fun t => ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t)) :=
      funext fun t => hG s t
    rw [hGs]
    exact (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2
      (hfc.aestronglyMeasurable measurableSet_Ioc)
  -- domination
  have hbound : ∀ᶠ s in 𝓝 s0, ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))),
      ‖G s t‖ ≤ (Cs * K) * t ^ (μ + 3 / 2) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t => fun ht => ?_)
    by_cases hts : t ≤ s
    · have htI : t ∈ Ioc 0 s := ⟨ht.1, hts⟩
      rw [hG s t, indicator_of_mem htI, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
      simp only [Complex.ofReal_re]
      have hU : ‖D.ev.U s t (gBD D B t)‖ ≤ Cs * (K * t ^ (3 / 2 : ℝ)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hCs s t ht.1.le hts hs.2.le) (hKb t ht) (norm_nonneg _) hCs0)
      calc t ^ μ * ‖D.ev.U s t (gBD D B t)‖ ≤ t ^ μ * (Cs * (K * t ^ (3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg ht.1.le _)
        _ = (Cs * K) * t ^ (μ + 3 / 2) := by rw [Real.rpow_add ht.1]; ring
    · have hnot : t ∉ Ioc 0 s := fun h => hts h.2
      rw [hG s t, indicator_of_notMem hnot, norm_zero]
      exact mul_nonneg (mul_nonneg hCs0 hK0) (Real.rpow_nonneg ht.1.le _)
  -- pointwise continuity in the parameter, for a.e. age
  have hcont_pt : ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), ContinuousAt (fun s => G s t) s0 := by
    have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), t ≠ s0 :=
      ae_restrict_of_ae (((Set.countable_singleton s0).ae_notMem volume).mono fun t ht => ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae] with t ht hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hopen : {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} ∈ 𝓝 (s0, t) := by
        apply IsOpen.mem_nhds
        · exact (isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_fst)
        · exact ⟨ht.1, hlt⟩
      have hK_nhds : {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} ∈ 𝓝 (s0, t) :=
        Filter.mem_of_superset hopen (fun p hp => ⟨hp.1, hp.2.le⟩)
      have hjc : ContinuousAt (fun p : ℝ × ℝ => D.ev.U p.1 p.2 (gBD D B p.2)) (s0, t) :=
        (jointG_contOn D.ev (gBD D B) hgc).continuousAt hK_nhds
      have hcs : ContinuousAt (fun s : ℝ => D.ev.U s t (gBD D B t)) s0 :=
        hjc.comp (f := fun s : ℝ => (s, t)) (continuous_id.prodMk continuous_const).continuousAt
      refine (hcs.const_smul ((t : ℂ) ^ (μ : ℂ))).congr ?_
      filter_upwards [eventually_gt_nhds hlt] with s hs
      rw [hG s t, indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht.1, hs.le⟩)]
      rfl
    · have hev : ∀ᶠ s in 𝓝 s0, s < t := eventually_lt_nhds hgt
      refine (continuousAt_const (y := (0 : Xmc c m))).congr ?_
      filter_upwards [hev] with s hs
      rw [hG s t, indicator_of_notMem (fun h => absurd h.2 (not_le.2 hs))]
  -- the integral over `(0,S]` is the integral over `(0,s]`
  have hcontI : ContinuousAt (fun s => ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))) s0 :=
    continuousAt_of_dominated hF_meas hbound hint hcont_pt
  have hEv : (fun s => xiD D (μ : ℂ) B s) =ᶠ[𝓝 s0]
      (fun s => ((s : ℂ) ^ (-(μ : ℂ))) • ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    have hint_eq : ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))
        = ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t) := by
      simp_rw [hG s]
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.2 (Ioc_subset_Ioc_right hs.2.le)]
    show xiD D (μ : ℂ) B s = _
    rw [xiD_apply, hint_eq]
  have hcpow : ContinuousAt (fun s : ℝ => (s : ℂ) ^ (-(μ : ℂ))) s0 :=
    Complex.continuousAt_ofReal_cpow_const s0 (-(μ : ℂ)) (Or.inr hs0'.ne')
  exact ((hcpow.smul hcontI).congr hEv.symm)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
