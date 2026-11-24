import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.BmatBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10

/-!
# `PartIII-b:C/asrc/kflat/2/1` : helper bounds for the Duhamel integrands 

Source of record: `the November 2 reference manuscript` (lines 4637-4640, 4686-4693).
This file holds the verified helper leaves: entry bounds of the Frobenius norm and the pointwise
bound `|g_B(t)| <= |B(t)|_F (2|H(t)| + |R(t)|)` (source 4605-4608).  The main theorem

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- A matrix entry is bounded by its Frobenius norm. -/
theorem duhAbsEntry_le_frob (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  have h1 : A i j ^ 2 ≤ ∑ i', ∑ j', A i' j' ^ 2 := by
    calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun k _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
            (fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc |A i j| = Real.sqrt (A i j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ frob A := Real.sqrt_le_sqrt h1

/-- A complex coefficient `-(1/2)(x - i y)` with `|x|, |y| ≤ F` has norm `≤ F`. -/
theorem duhCoef_norm_le (x y F : ℝ) (hx : |x| ≤ F) (hy : |y| ≤ F) :
    ‖-(1 / 2 : ℂ) * (((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))‖ ≤ F := by
  have h1 : ‖(((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))‖ ≤ |x| + |y| := by
    calc ‖(((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))‖
        ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * ((y : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = |x| + |y| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_neg, norm_div, norm_one, show (‖(2 : ℂ)‖ = 2) by simp]
  rw [norm_mul, h2]
  linarith

/-- The same bound for `-(1/2)(x + i y)`. -/
theorem duhCoef_norm_le' (x y F : ℝ) (hx : |x| ≤ F) (hy : |y| ≤ F) :
    ‖-(1 / 2 : ℂ) * (((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ F := by
  have h1 : ‖(((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ |x| + |y| := by
    calc ‖(((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖
        ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * ((y : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |x| + |y| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_neg, norm_div, norm_one, show (‖(2 : ℂ)‖ = 2) by simp]
  rw [norm_mul, h2]
  linarith

/-- **Pointwise bound on `g_B`.**  `‖g_B(t)‖ ≤ |B(t)|_F (2‖H(t)‖ + ‖R(t)‖)` (source 4605-4608). -/
theorem duhGBD_norm_le {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels}
    (FI : FlatInstData κ ν c m tr) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    ‖gBD FI B t‖ ≤ frob (B t) * (2 * ‖FI.src.H t‖ + ‖FI.src.R t‖) := by
  have hd : |UnforcedLeray.Short.PartIIIb.Bd (B t)| ≤ frob (B t) := by
    unfold UnforcedLeray.Short.PartIIIb.Bd
    have a1 := duhAbsEntry_le_frob (B t) 0 0
    have a2 := duhAbsEntry_le_frob (B t) 2 2
    rw [abs_div, abs_two]
    have : |B t 0 0 - B t 2 2| ≤ |B t 0 0| + |B t 2 2| := abs_sub _ _
    have hF : 0 ≤ frob (B t) := Real.sqrt_nonneg _
    linarith
  have he : |UnforcedLeray.Short.PartIIIb.Be (B t)| ≤ frob (B t) := by
    unfold UnforcedLeray.Short.PartIIIb.Be
    have a1 := duhAbsEntry_le_frob (B t) 0 2
    have a2 := duhAbsEntry_le_frob (B t) 2 0
    rw [abs_div, abs_two]
    have : |B t 0 2 + B t 2 0| ≤ |B t 0 2| + |B t 2 0| := abs_add_le _ _
    have hF : 0 ≤ frob (B t) := Real.sqrt_nonneg _
    linarith
  have hb : |UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (B t)| ≤ frob (B t) := by
    unfold UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta
    have a1 := duhAbsEntry_le_frob (B t) 0 0
    have a2 := duhAbsEntry_le_frob (B t) 2 2
    rw [abs_div, abs_two]
    have : |B t 0 0 + B t 2 2| ≤ |B t 0 0| + |B t 2 2| := abs_add_le _ _
    have hF : 0 ≤ frob (B t) := Real.sqrt_nonneg _
    linarith
  rw [gBD_apply]
  have hA := duhCoef_norm_le (UnforcedLeray.Short.PartIIIb.Bd (B t))
    (UnforcedLeray.Short.PartIIIb.Be (B t)) (frob (B t)) hd he
  have hB := duhCoef_norm_le' (UnforcedLeray.Short.PartIIIb.Bd (B t))
    (UnforcedLeray.Short.PartIIIb.Be (B t)) (frob (B t)) hd he
  have hC : ‖((UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (B t) : ℝ) : ℂ)‖ ≤ frob (B t) := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hb
  have hH := norm_nonneg (FI.src.H t)
  have hR := norm_nonneg (FI.src.R t)
  have t1 := mul_le_mul_of_nonneg_right hA hH
  have t2 := mul_le_mul_of_nonneg_right hB hH
  have t3 := mul_le_mul_of_nonneg_right hC hR
  have tri1 : ∀ (u v w : Xmc c m), ‖u + v - w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := fun u v w =>
    (norm_sub_le _ _).trans (add_le_add (norm_add_le u v) (le_refl _))
  refine (tri1 _ _ _).trans ?_
  rw [norm_smul, norm_smul, norm_smul, norm_conjX]
  linarith [t1, t2, t3, show frob (B t) * (2 * ‖FI.src.H t‖ + ‖FI.src.R t‖) =
    frob (B t) * ‖FI.src.H t‖ + frob (B t) * ‖FI.src.H t‖ + frob (B t) * ‖FI.src.R t‖ by ring]

/-- `B = 0` beyond the support `t > 1.1/ν` of the cutoff (source 4953-4958, 5063-5079). -/
theorem bmat_eq_zero_of_gt (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) {t : ℝ} (ht : 11 / 10 / ν < t) : Bmat ν μ χf A t = 0 := by
  have hev : Ay ν χf A =ᶠ[nhds t] fun _ => (0 : Mat3) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    have h1 : 11 / 10 < u * ν := (div_lt_iff₀ hν).1 hu
    have h2 : 11 / 10 ≤ ν * u := by linarith [mul_comm u ν]
    simp [Ay, hχ.zero _ h2]
  unfold Bmat
  rw [hev.deriv_eq, hev.eq_of_nhds]
  simp

/-- `𝒰(s,t)g(t)` is continuous in `t ∈ [0,s]` for a continuous curve `g`. -/
theorem evU_continuousOn_curve {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (ev : TrainEvolution m tr) (s : ℝ)
    (g : ℝ → Xmc c m) (hg : Continuous g) :
    ContinuousOn (fun t => ev.U s t (g t)) (Icc 0 s) := by
  obtain ⟨C, hC⟩ := ev.locBdd s
  have hx : ∀ x : Xmc c m, ContinuousOn (fun t => ev.U s t x) (Icc 0 s) := fun x => by
    have h1 := ev.jointCont x
    have h2 : ContinuousOn (fun t : ℝ => (s, t)) (Icc 0 s) :=
      (continuous_const.prodMk continuous_id).continuousOn
    exact h1.comp h2 (fun t ht => ⟨ht.1, ht.2⟩)
  intro t0 ht0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ t ∈ Icc 0 s, ‖ev.U s t (g t) - ev.U s t0 (g t0)‖ ≤
      max C 0 * ‖g t - g t0‖ + ‖ev.U s t (g t0) - ev.U s t0 (g t0)‖ := by
    intro t ht
    have e : ev.U s t (g t) - ev.U s t0 (g t0) =
        ev.U s t (g t - g t0) + (ev.U s t (g t0) - ev.U s t0 (g t0)) := by
      rw [map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    calc ‖ev.U s t (g t - g t0)‖ ≤ ‖ev.U s t‖ * ‖g t - g t0‖ := (ev.U s t).le_opNorm _
      _ ≤ max C 0 * ‖g t - g t0‖ :=
          mul_le_mul_of_nonneg_right ((hC s t ht.1 ht.2 le_rfl).trans (le_max_left _ _))
            (norm_nonneg _)
  have h1 : Filter.Tendsto (fun t => ‖g t - g t0‖) (nhdsWithin t0 (Icc 0 s)) (nhds 0) := by
    have := ((hg.tendsto t0).sub_const (g t0)).norm
    simp only [sub_self, norm_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun t => ‖ev.U s t (g t0) - ev.U s t0 (g t0)‖)
      (nhdsWithin t0 (Icc 0 s)) (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hx (g t0) t0 ht0)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hb) ?_
  simpa using (h1.const_mul (max C 0)).add h2

/-- Measurability of the Duhamel integrand, given measurability of the three coefficients of `B`. -/
theorem duhIntegrand_aesm {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ)
    (hd : AEStronglyMeasurable (fun t : ℝ => UnforcedLeray.Short.PartIIIb.Bd (B t))
      (volume.restrict (Ioc 0 s)))
    (he : AEStronglyMeasurable (fun t : ℝ => UnforcedLeray.Short.PartIIIb.Be (B t))
      (volume.restrict (Ioc 0 s)))
    (hb : AEStronglyMeasurable (fun t : ℝ => UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (B t))
      (volume.restrict (Ioc 0 s))) :
    AEStronglyMeasurable (DuhIntegrand FI μ B s) (volume.restrict (Ioc 0 s)) := by
  have gm : ∀ g : ℝ → Xmc (cOf ν) m, Continuous g →
      AEStronglyMeasurable (fun t : ℝ => FI.ev.U s t (g t)) (volume.restrict (Ioc 0 s)) :=
    fun g hg => ((evU_continuousOn_curve FI.ev s g hg).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  have g1 := gm _ FI.src.H_cont
  have g2 := gm _ (continuous_conjX.comp FI.src.H_cont)
  have g3 := gm _ FI.src.R_cont
  have hdC : AEStronglyMeasurable (fun t : ℝ => ((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ))
      (volume.restrict (Ioc 0 s)) := Complex.continuous_ofReal.comp_aestronglyMeasurable hd
  have heC : AEStronglyMeasurable (fun t : ℝ => ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))
      (volume.restrict (Ioc 0 s)) := Complex.continuous_ofReal.comp_aestronglyMeasurable he
  have hbC : AEStronglyMeasurable
      (fun t : ℝ => ((UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (B t) : ℝ) : ℂ))
      (volume.restrict (Ioc 0 s)) := Complex.continuous_ofReal.comp_aestronglyMeasurable hb
  have hp : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)))
      (volume.restrict (Ioc 0 s)) :=
    (Complex.measurable_ofReal.pow_const _).aestronglyMeasurable
  have ha : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      (-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ) -
        Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))))
      (volume.restrict (Ioc 0 s)) :=
    hp.mul ((aestronglyMeasurable_const.mul (hdC.sub (aestronglyMeasurable_const.mul heC))))
  have hb' : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      (-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ) +
        Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))))
      (volume.restrict (Ioc 0 s)) :=
    hp.mul ((aestronglyMeasurable_const.mul (hdC.add (aestronglyMeasurable_const.mul heC))))
  have hc : AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) *
      ((UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (B t) : ℝ) : ℂ))
      (volume.restrict (Ioc 0 s)) := hp.mul hbC
  have key : DuhIntegrand FI μ B s = fun t : ℝ =>
      (((t : ℂ) ^ (μ : ℂ)) *
        (-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ) -
          Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ)))) •
          FI.ev.U s t (FI.src.H t)
      + (((t : ℂ) ^ (μ : ℂ)) *
        (-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ) +
          Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ)))) •
          FI.ev.U s t (conjX (FI.src.H t))
      - (((t : ℂ) ^ (μ : ℂ)) *
        ((UnforcedLeray.Short.PartIIIb.ConcreteYF.Bbeta (B t) : ℝ) : ℂ)) •
          FI.ev.U s t (FI.src.R t) := by
    funext t
    simp only [DuhIntegrand, gBD_apply, map_sub, map_add, map_smul, smul_sub, smul_add,
      smul_smul]
  rw [key]
  exact ((ha.smul g1).add (hb'.smul g2)).sub (hc.smul g3)


/-- Continuity of `Mat3 → ℝ` coefficient maps applied to a measurable family. -/
theorem duhCoef_aesm {f : ℝ → Mat3} {S : Set ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    (φ : Mat3 → ℝ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun t => φ (f t)) (volume.restrict S) :=
  hφ.comp_aestronglyMeasurable hf

/-- **Leaf 1.** The Duhamel integrands of `B_{μ,ν}[A]` are integrable on `(0,s]`
(source 4637-4640, 4686-4693). -/
theorem duhIntegrable (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] :
    DuhIntegrableProp as χf m := by
  intro hχ κ ν μ hν hν1 hμ0 hμ1 tr FI A hA s
  have : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  by_cases hs : s ≤ 0
  · rw [Ioc_eq_empty (not_lt.2 hs)]
    exact integrableOn_empty
  push_neg at hs
  -- measurability of `B`
  have hAyc : ContinuousOn (Ay ν χf A) (Ioi 0) := fun t ht =>
    (ayDiffAt as χf hχ ν A hA t ht).continuousAt.continuousWithinAt
  have hBm : AEStronglyMeasurable (Bmat ν μ χf A) (volume.restrict (Ioc 0 s)) := by
    have h1 : AEStronglyMeasurable (fun t => deriv (Ay ν χf A) t) (volume.restrict (Ioc 0 s)) :=
      (measurable_deriv (Ay ν χf A)).aestronglyMeasurable
    have h2 : ContinuousOn (fun t => (μ / t) • Ay ν χf A t) (Ioi 0) :=
      ((continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)).smul hAyc)
    have h3 : AEStronglyMeasurable (fun t => (μ / t) • Ay ν χf A t)
        (volume.restrict (Ioc 0 s)) := (h2.mono (fun t (ht : t ∈ Ioc (0 : ℝ) s) => ht.1)).aestronglyMeasurable
      measurableSet_Ioc
    exact h1.add h3
  have hd := duhCoef_aesm hBm (fun M => (M 0 0 - M 2 2) / 2) (by fun_prop)
  have he := duhCoef_aesm hBm (fun M => (M 0 2 + M 2 0) / 2) (by fun_prop)
  have hb := duhCoef_aesm hBm (fun M => (M 0 0 + M 2 2) / 2) (by fun_prop)
  have hmeas := duhIntegrand_aesm FI μ (Bmat ν μ χf A) s hd he hb
  -- bound
  obtain ⟨C, hC⟩ := FI.ev.locBdd s
  obtain ⟨h1, hH⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn
    FI.src.H_cont.continuousOn
  obtain ⟨h2, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn
    FI.src.R_cont.continuousOn
  set K : ℝ := (1 + μ) * s ^ (3 / 2 : ℝ) * max (affM ν χf A) 0 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    positivity
  have hfrob : ∀ t ∈ Ioc (0 : ℝ) s, frob (Bmat ν μ χf A t) ≤ K := by
    intro t ht
    by_cases htc : t ≤ 11 / 10 / ν
    · have hb := bmatBound as χf hχ ν μ hν hμ0 A hA t ht.1 htc
      refine hb.trans ?_
      have : t ^ (3 / 2 : ℝ) ≤ s ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ht.1.le ht.2 (by norm_num)
      have hp : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.1.le _
      calc (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χf A
          ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * max (affM ν χf A) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        _ ≤ K := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left this (by linarith)) (le_max_right _ _)
    · push_neg at htc
      rw [bmat_eq_zero_of_gt χf hχ ν μ hν A htc]
      simpa [frob] using hK0
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) s)) := ⟨by simp⟩
  refine Integrable.of_bound (C := s ^ μ * max C 0 * (K * (2 * h1 + h2))) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
  have hn := duhGBD_norm_le FI (Bmat ν μ χf A) t
  have hpow : ‖((t : ℂ) ^ (μ : ℂ))‖ ≤ s ^ μ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
    exact Real.rpow_le_rpow ht.1.le ht.2 hμ0
  have hU : ‖FI.ev.U s t‖ ≤ max C 0 := (hC s t ht.1.le ht.2 le_rfl).trans (le_max_left _ _)
  have hHt : ‖FI.src.H t‖ ≤ h1 := hH t ⟨ht.1.le, ht.2⟩
  have hRt : ‖FI.src.R t‖ ≤ h2 := hR t ⟨ht.1.le, ht.2⟩
  have hg : ‖gBD FI (Bmat ν μ χf A) t‖ ≤ K * (2 * h1 + h2) := by
    refine hn.trans (mul_le_mul (hfrob t ht) (by linarith) (by positivity) hK0)
  show ‖DuhIntegrand FI μ (Bmat ν μ χf A) s t‖ ≤ _
  unfold DuhIntegrand
  rw [norm_smul]
  have hUg : ‖FI.ev.U s t (gBD FI (Bmat ν μ χf A) t)‖ ≤ max C 0 * (K * (2 * h1 + h2)) :=
    ((FI.ev.U s t).le_opNorm _).trans
      (mul_le_mul hU hg (norm_nonneg _) (le_max_right _ _))
  calc ‖((t : ℂ) ^ (μ : ℂ))‖ * ‖FI.ev.U s t (gBD FI (Bmat ν μ χf A) t)‖
      ≤ s ^ μ * (max C 0 * (K * (2 * h1 + h2))) :=
        mul_le_mul hpow hUg (norm_nonneg _) (Real.rpow_nonneg hs.le _)
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
