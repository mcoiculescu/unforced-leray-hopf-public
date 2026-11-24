import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit.OutPrimSmooth

/-!
# Phase differentiability and half-line majorant for `srcX0` (`CommDerivSplit/TimeDeriv`)

Proves for `T = IIIa.thinSource ε F` under `FarLeafOrg.ThinHyp c ρo F` and `IIIa.thinMoment c F ≠ ⊤`:
1. `thin_hasDerivAt_tau`: for `ρo / ε < ϱ y`, `t ↦ srcX0 ν μ T t y` is differentiable at `τ`
   with derivative `WithLp.toLp 2 fun i => (kerInt T (kdDh ν μ) τ y i).re`.
2. `thin_deriv_tau_bound`: for any `r > ρo / ε` and `z₀ : ℝ`, there exists `Cb ≥ 0` (independent
   of `t : ℝ` and `ρ ≥ r`) such that
   `|ρ * (deriv (fun s => srcX0 ν μ T s !₂[ρ, 0, z₀]) t) 2| ≤ Cb * (ρ - ρo / ε) ^ (-(3 / 2 : ℝ))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open YBComm FarLeafOrg UnforcedLeray.PhaseSpace

/-- Joint integrability of the `Gker` integrand for `thinSource ε F` off the old disk. -/
theorem thin_gkerIntegrable {ν ε c ρo : ℝ} {m : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo) (hm : -(1 / 4) < m.re)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) (i : Fin 3) :
    Integrable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      Gker ν m p.1 y p.2 i j k * ((IIIa.thinSource ε F (τ - p.1) p.2 j k : ℝ) : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hae : ∀ᵐ p : ℝ × Space ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), 0 < p.1 := by
    have h1 : ∀ᵐ h ∂(volume.restrict (Ioi (0 : ℝ))), 0 < h :=
      (ae_restrict_mem measurableSet_Ioi).mono fun h hh => hh
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h1
  have hr : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hP : 0 < 2 * ε * c := by positivity
  have hT := thin_isSep hε hth
  obtain ⟨δ, hδ, C, _hC0, hb⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν m (ρo / ε) (2 * ε * c) (IIIa.thinSource ε F)
      hν hm hr hP hT τ i y hy
  have hM : Integrable (sepMajorant m (IIIa.thinSource ε F) τ 0) sepRho :=
    thin_majorantIntegrable hε hc hm hth hN τ 0
  have hgI : Integrable (gkerMaj m (IIIa.thinSource ε F) τ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ⟨(gkerMaj_measurable m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT τ).aestronglyMeasurable,
      gkerMaj_lintegral_lt_top m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT τ hM⟩
  have hG : Measurable (gkerG ν m (IIIa.thinSource ε F) τ i y) :=
    gkerG_measurable ν hν m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT τ i y
  have hFG : (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      Gker ν m p.1 y p.2 i j k * ((IIIa.thinSource ε F (τ - p.1) p.2 j k : ℝ) : ℂ)) =ᵐ[
        (volume.restrict (Ioi (0 : ℝ))).prod volume]
      gkerG ν m (IIIa.thinSource ε F) τ i y := by
    filter_upwards [hae] with p hp
    have hlt : Real.exp (-p.1) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hcpos : 0 < ν * (1 - Real.exp (-p.1)) := mul_pos hν (by linarith)
    simp only [gkerG, gkerD, Gker, hcpos, ↓reduceIte, iteratedFDeriv_one_apply]
  refine Integrable.mono' (hgI.const_mul C) (hG.aestronglyMeasurable.congr hFG.symm) ?_
  filter_upwards [hae] with p hp
  have hl : Real.exp (-p.1 / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hn := hb y (Metric.mem_ball_self hδ) _ hl p.2 0 (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero] at hn
  rw [gkerSum_eq_sepPhi ν m (IIIa.thinSource ε F) τ i y p.2 p.1]
  have hc0 : 0 ≤ Real.exp (-p.1 / 2) / 2 := by positivity
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc0]
  calc Real.exp (-p.1 / 2) / 2 * ‖sepPhi ν m (IIIa.thinSource ε F) τ i (Real.exp (-p.1 / 2), p.2) y‖
      ≤ Real.exp (-p.1 / 2) / 2 *
          (C * sepMajorant m (IIIa.thinSource ε F) τ 0 (Real.exp (-p.1 / 2), p.2)) :=
        mul_le_mul_of_nonneg_left hn hc0
    _ = C * gkerMaj m (IIIa.thinSource ε F) τ p := by
        simp only [gkerMaj]
        ring

/-- The `h`-representation of `sepW` for any source `T` (without `SepMoment`). -/
theorem sepW_eq_kerInt (ν : ℝ) (m : ℂ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) (i : Fin 3) :
    IIIa.sepW ν m T y τ i = kerInt T (Gker ν m) τ y i := by
  have hsq : ∀ h : ℝ, Real.exp (-h / 2) ^ 2 = Real.exp (-h) := by
    intro h
    rw [← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have hτ : ∀ h : ℝ, τ + 2 * (-h / 2) = τ - h := fun h => by ring
  have hEP : ∀ h : ℝ, ((Real.exp (-h / 2) : ℝ) : ℂ) *
      Complex.exp ((2 * m + 2) * ((-h / 2 : ℝ) : ℂ)) = Complex.exp (-(m + 3 / 2) * (h : ℂ)) := by
    intro h
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hR : ∀ (h : ℝ) (z : Space), ∑ j : Fin 3, ∑ k : Fin 3,
      Gker ν m h y z i j k * ((T (τ - h) z j k : ℝ) : ℂ) =
      Complex.exp (-(m + 3 / 2) * (h : ℂ)) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)
          (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
          ((T (τ - h) z j k : ℝ) : ℂ) := by
    intro h z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Gker]; ring
  unfold IIIa.sepW kerInt
  rw [integral_Ioo_eq_exp_h, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  simp only [hsq h, Real.log_exp, hτ h, Complex.real_smul, cpow_exp_real_h]
  simp only [hR h]
  rw [integral_const_mul, ← hEP h]
  push_cast; ring

/-- `srcX0` for `thinSource ε F` equals `Re (kerInt Kd)` off the old disk. -/
theorem thin_X0_eq_kerInt {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) :
    srcX0 ν μ (IIIa.thinSource ε F) τ y =
      WithLp.toLp 2 fun i => (kerInt (IIIa.thinSource ε F) (Kd ν μ) τ y i).re := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have i1 := thin_gkerIntegrable hν hε hc hρo hm1 hth hN τ hy
  have i2 := thin_gkerIntegrable hν hε hc hρo hm2 hth hN τ hy
  ext i
  have hsub := kerInt_sub_of_integrable (IIIa.thinSource ε F)
    (Gker ν (μ : ℂ)) (Gker ν ((μ : ℂ) + 1)) τ y i (i1 i) (i2 i)
  show (IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) y τ i -
    IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) y τ i).re =
      (kerInt (IIIa.thinSource ε F) (Kd ν μ) τ y i).re
  rw [sepW_eq_kerInt ν (μ : ℂ) (IIIa.thinSource ε F) τ y i,
    sepW_eq_kerInt ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) τ y i]
  congr 1
  exact hsub.symm

/-- Measurability of the shifted integrands `extInt` for `thinSource ε F`. -/
theorem thin_extIntMeasurable {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hth : ThinHyp c ρo F) (y : Space) (i : Fin 3) :
    (∀ t : ℝ, AEStronglyMeasurable
      (extInt (IIIa.thinSource ε F) (Kd ν μ) t y i) (volume.prod volume)) ∧
    (∀ t : ℝ, AEStronglyMeasurable
      (extInt (IIIa.thinSource ε F) (kdDh ν μ) t y i) (volume.prod volume)) := by
  have hT := thin_isSep hε hth
  have hψm : ∀ t : ℝ, Measurable (fun p : ℝ × Space => (t - p.1, p.2)) := fun t => by fun_prop
  constructor
  · intro t
    have hW : Measurable (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
        gk ν μ i j k y q * ((IIIa.thinSource ε F (t - q.1) q.2 j k : ℝ) : ℂ)) :=
      sumT_measurable (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT t _
        fun j k => gk_measurable ν μ i j k y
    have hind : Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
        Kd ν μ q.1 y q.2 i j k * ((IIIa.thinSource ε F (t - q.1) q.2 j k : ℝ) : ℂ)) =
        Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          gk ν μ i j k y q * ((IIIa.thinSource ε F (t - q.1) q.2 j k : ℝ) : ℂ)) := by
      funext q
      by_cases hq : q ∈ Spos
      · have hq1 : 0 < q.1 := hq.1
        have key : ∀ a b d : Fin 3, gk ν μ a b d y q = Kd ν μ q.1 y q.2 a b d :=
          fun a b d => gk_eq ν hν μ a b d y q hq1
        simp only [Set.indicator_of_mem hq, key]
      · simp only [Set.indicator_of_notMem hq]
    have hfun : extInt (IIIa.thinSource ε F) (Kd ν μ) t y i =
        fun p : ℝ × Space => Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          gk ν μ i j k y q * ((IIIa.thinSource ε F (t - q.1) q.2 j k : ℝ) : ℂ)) (t - p.1, p.2) := by
      funext p
      rw [extInt_eq_ind, hind]
    rw [hfun]
    exact ((hW.indicator Spos_measurable).comp (hψm t)).aestronglyMeasurable
  · intro t
    have hpt : ∀ p : ℝ × Space, extInt (IIIa.thinSource ε F) (kdDh ν μ) t y i p =
        Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          kdDh ν μ q.1 y q.2 i j k * ((IIIa.thinSource ε F (t - q.1) q.2 j k : ℝ) : ℂ))
          (t - p.1, p.2) :=
      fun p => extInt_eq_ind (IIIa.thinSource ε F) (kdDh ν μ) t y i p
    have hlim : ∀ q : ℝ × Space,
        Tendsto (fun n : ℕ => Spos.indicator (dnq (IIIa.thinSource ε F) ν μ t y i n) q)
        atTop (𝓝 (Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          kdDh ν μ q.1 y q.2 i j k * ((IIIa.thinSource ε F (t - q.1) q.2 j k : ℝ) : ℂ)) q)) := by
      intro q
      by_cases hq : q ∈ Spos
      · have hq1 : 0 < q.1 := hq.1
        simp only [Set.indicator_of_mem hq, dnq]
        apply tendsto_finsetSum
        intro j _
        apply tendsto_finsetSum
        intro k _
        exact (gk_slope ν hν μ i j k y q hq1).mul_const _
      · simp only [Set.indicator_of_notMem hq]
        exact tendsto_const_nhds
    have hQm : ∀ n : ℕ, Measurable (fun p : ℝ × Space =>
        Spos.indicator (dnq (IIIa.thinSource ε F) ν μ t y i n) (t - p.1, p.2)) := fun n =>
      ((dnq_measurable (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT ν μ t y i n).indicator
        Spos_measurable).comp (hψm t)
    have hSM : StronglyMeasurable
        (fun p : ℝ × Space => extInt (IIIa.thinSource ε F) (kdDh ν μ) t y i p) :=
      stronglyMeasurable_of_tendsto (u := atTop)
        (f := fun n (p : ℝ × Space) =>
          Spos.indicator (dnq (IIIa.thinSource ε F) ν μ t y i n) (t - p.1, p.2))
        (g := fun p : ℝ × Space => extInt (IIIa.thinSource ε F) (kdDh ν μ) t y i p)
        (fun n => (hQm n).stronglyMeasurable)
        (tendsto_pi_nhds.2 fun (p : ℝ × Space) => by
          show Tendsto (fun n : ℕ =>
            Spos.indicator (dnq (IIIa.thinSource ε F) ν μ t y i n) (t - p.1, p.2)) atTop
            (𝓝 (extInt (IIIa.thinSource ε F) (kdDh ν μ) t y i p))
          rw [hpt p]
          exact hlim (t - p.1, p.2))
    exact hSM.aestronglyMeasurable

/-- Integrability of `extInt (thinSource ε F) (Kd ν μ) t y i` off the old disk. -/
theorem thin_extIntKdIntegrable {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    {y : Space} (hy : ρo / ε < ϱ y) (i : Fin 3) (t : ℝ) :
    Integrable (extInt (IIIa.thinSource ε F) (Kd ν μ) t y i) (volume.prod volume) := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have I1 := thin_gkerIntegrable hν hε hc hρo hm1 hth hN t hy i
  have I2 := thin_gkerIntegrable hν hε hc hρo hm2 hth hN t hy i
  set f : ℝ × Space → ℂ := fun p => ∑ j : Fin 3, ∑ k : Fin 3,
    Kd ν μ p.1 y p.2 i j k * ((IIIa.thinSource ε F (t - p.1) p.2 j k : ℝ) : ℂ) with hf
  have hsub : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine (I1.sub I2).congr (Eventually.of_forall fun p => ?_)
    simp only [hf, Kd, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hrest : (volume.restrict (Ioi (0 : ℝ))).prod volume =
      (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  set H : ℝ × Space → ℂ := (Ioi (0 : ℝ) ×ˢ (univ : Set Space)).indicator f with hH
  have hHint : Integrable H (volume.prod volume) := by
    rw [hH, integrable_indicator_iff (measurableSet_Ioi.prod MeasurableSet.univ)]
    show Integrable f ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set Space)))
    rw [← hrest]
    exact hsub
  have hψ : MeasurePreserving (fun q : ℝ × Space => (t - q.1, q.2))
      (volume.prod volume) (volume.prod volume) :=
    (volume.measurePreserving_sub_left t).prod (MeasurePreserving.id volume)
  have hemb : MeasurableEmbedding (fun q : ℝ × Space => (t - q.1, q.2)) :=
    ((Homeomorph.subLeft t).prodCongr (Homeomorph.refl Space)).measurableEmbedding
  have hpt : ∀ p : ℝ × Space,
      extInt (IIIa.thinSource ε F) (Kd ν μ) t y i p = H (t - p.1, p.2) := by
    rintro ⟨s, z⟩
    by_cases hs : s < t
    · have h1 : s ∈ Iio t := hs
      have h2 : t - s ∈ Ioi (0 : ℝ) := sub_pos.mpr hs
      rw [hH, Set.indicator_of_mem (show (t - s, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Space) from
        ⟨h2, mem_univ _⟩)]
      simp only [extInt, Set.indicator_of_mem h1, hf, sub_sub_cancel]
    · have h1 : s ∉ Iio t := fun h => hs h
      have h3 : (t - s, z) ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space) := fun h => by
        have := h.1
        simp only [mem_Ioi] at this
        linarith
      rw [hH, Set.indicator_of_notMem h3]
      simp only [extInt, Set.indicator_of_notMem h1]
  have hcomp : Integrable (fun p : ℝ × Space => H (t - p.1, p.2)) (volume.prod volume) :=
    (hψ.integrable_comp_emb hemb).mpr hHint
  exact hcomp.congr (Eventually.of_forall fun p => (hpt p).symm)

/-- Phase differentiability of `srcX0 ν μ (thinSource ε F)` off the old disk. -/
theorem thin_hasDerivAt_tau {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) :
    HasDerivAt (fun t => srcX0 ν μ (IIIa.thinSource ε F) t y)
      (WithLp.toLp 2 fun i => (kerInt (IIIa.thinSource ε F) (kdDh ν μ) τ y i).re) τ := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hr : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hP : 0 < 2 * ε * c := by positivity
  have hT := thin_isSep hε hth
  obtain ⟨C0, hC0, hU0⟩ := sepGapPointwiseUnif ν (μ : ℂ) (ρo / ε) (2 * ε * c)
    (IIIa.thinSource ε F) hν hm1 hr hP hT y hy
  set C2 : ℝ := (1 + ‖(μ : ℂ) - 1 / 2‖) * C0 + C0 * (‖y‖ / 2 + 3 * |ν|)
  have hC2n : 0 ≤ C2 := by positivity
  set t₀ : ℝ := τ + 1 with ht₀
  set K : ℝ := Real.exp (2 * μ + 3)
  have hK0 : 0 < K := Real.exp_pos _
  have hM0 : Integrable (sepMajorant (μ : ℂ) (IIIa.thinSource ε F) t₀ 0) sepRho :=
    thin_majorantIntegrable hε hc hm1 hth hN t₀ 0
  have hgI0 : Integrable (gkerMaj (μ : ℂ) (IIIa.thinSource ε F) t₀)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ⟨(gkerMaj_measurable (μ : ℂ) (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT t₀).aestronglyMeasurable,
      gkerMaj_lintegral_lt_top (μ : ℂ) (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hT t₀ hM0⟩
  set g : ℝ × Space → ℝ := fun p => C2 * K *
    (if p.1 < t₀ then gkerMaj (μ : ℂ) (IIIa.thinSource ε F) t₀ (t₀ - p.1, p.2) else 0)
  have hg : Integrable g (volume.prod volume) :=
    (gkerMajShiftIntegrable _ t₀ hgI0).const_mul (C2 * K)
  have hkd_deriv : ∀ i : Fin 3,
      HasDerivAt (fun t => kerInt (IIIa.thinSource ε F) (Kd ν μ) t y i)
        (kerInt (IIIa.thinSource ε F) (kdDh ν μ) τ y i) τ := by
    intro i
    have hlip : ∀ᵐ p ∂(volume.prod volume),
        LipschitzOnWith (Real.nnabs (g p))
          (fun t => extInt (IIIa.thinSource ε F) (Kd ν μ) t y i p) (Metric.ball τ 1) := by
      refine Eventually.of_forall fun ⟨s, z⟩ => ?_
      have hderiv : ∀ t, s < t → HasDerivAt
          (fun t' => extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z))
          (∑ j : Fin 3, ∑ k : Fin 3,
            kdE ν μ (t - s) y z i j k * ((IIIa.thinSource ε F s z j k : ℝ) : ℂ)) t := by
        intro t hst
        have hev : (fun t' => extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z)) =ᶠ[nhds t]
            fun t' => ∑ j : Fin 3, ∑ k : Fin 3,
              Kd ν μ (t' - s) y z i j k * ((IIIa.thinSource ε F s z j k : ℝ) : ℂ) := by
          filter_upwards [Ioi_mem_nhds hst] with t' ht'
          have hst' : s < t' := ht'
          simp only [extInt_apply, hst', ↓reduceIte]
        refine HasDerivAt.congr_of_eventuallyEq ?_ hev
        refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_
        exact ((kdHasDerivAt ν μ hν (t - s) (sub_pos.2 hst) y z i j k).comp_sub_const t s).mul_const _
      have hzero : ∀ t, t < s →
          HasDerivAt (fun t' => extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z)) 0 t := by
        intro t hts
        have hev : (fun t' => extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z)) =ᶠ[nhds t]
            fun _ => (0 : ℂ) := by
          filter_upwards [Iio_mem_nhds hts] with t' ht'
          have hst' : ¬ s < t' := not_lt.2 (le_of_lt ht')
          simp only [extInt_apply, hst', ↓reduceIte]
        exact (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hev
      have hfb : ∀ t', ‖extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z)‖ ≤
          (C0 * (IIIa.tensorNorm (IIIa.thinSource ε F s z) / 2)) *
            (1 - Real.exp (-(max (t' - s) 0))) := by
        intro t'
        by_cases hst : s < t'
        · have hh : 0 < t' - s := sub_pos.2 hst
          have hex : 0 ≤ 1 - Real.exp (-(t' - s)) := by
            have := Real.exp_lt_one_iff.2 (by linarith : -(t' - s) < 0); linarith
          simp only [extInt_apply, hst, ↓reduceIte, max_eq_left hh.le, kd_sum_eq,
            norm_mul, Complex.norm_real]
          rw [Real.norm_of_nonneg hex]
          have hA := sumG_bound ν μ (IIIa.thinSource ε F) y C0 hν hU0 t' (t' - s) hh z i
          rw [sub_sub_cancel] at hA
          have hG := gkerMaj_le_tensor (μ : ℂ) (IIIa.thinSource ε F) t' (t' - s) z hh.le hm1
          rw [sub_sub_cancel] at hG
          calc (1 - Real.exp (-(t' - s))) * _ ≤ (1 - Real.exp (-(t' - s))) *
                (C0 * (IIIa.tensorNorm (IIIa.thinSource ε F s z) / 2)) :=
                mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hG hC0)) hex
            _ = _ := by ring
        · simp only [extInt_apply, hst, ↓reduceIte, norm_zero]
          have : max (t' - s) 0 = 0 := max_eq_right (by linarith [not_lt.1 hst])
          rw [this]; simp
      have hcs : ContinuousAt (fun t' => extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z)) s := by
        have hfs : extInt (IIIa.thinSource ε F) (Kd ν μ) s y i (s, z) = 0 := by
          simp only [extInt_apply, lt_irrefl s, ↓reduceIte]
        have hcont : Continuous (fun t' : ℝ =>
            (C0 * (IIIa.tensorNorm (IIIa.thinSource ε F s z) / 2)) *
              (1 - Real.exp (-(max (t' - s) 0)))) := by fun_prop
        have hlim := hcont.tendsto s
        simp only [sub_self, max_self, neg_zero, Real.exp_zero, sub_self, mul_zero] at hlim
        show Filter.Tendsto _ _ (nhds (extInt (IIIa.thinSource ε F) (Kd ν μ) s y i (s, z)))
        rw [hfs, tendsto_zero_iff_norm_tendsto_zero]
        exact squeeze_zero (fun _ => norm_nonneg _) hfb hlim
      have hB0 : 0 ≤ g (s, z) := by
        refine mul_nonneg (by positivity) ?_
        split_ifs
        · exact gkerMaj_nonneg _ _ _ _
        · exact le_rfl
      rw [Real.ball_eq_Ioo]
      refine lipOffPoint (fun t' => extInt (IIIa.thinSource ε F) (Kd ν μ) t' y i (s, z))
        (fun t => if s < t then ∑ j : Fin 3, ∑ k : Fin 3, kdE ν μ (t - s) y z i j k *
          ((IIIa.thinSource ε F s z j k : ℝ) : ℂ) else 0) s (τ - 1) (τ + 1) (g (s, z))
        hB0 ?_ ?_ ?_
      · intro t _ht
        rcases lt_trichotomy t s with hts | hts | hts
        · exact (hzero t hts).continuousAt.continuousWithinAt
        · subst hts; exact hcs.continuousWithinAt
        · exact (hderiv t hts).continuousAt.continuousWithinAt
      · intro t _ht hne
        rcases lt_or_gt_of_ne hne with hts | hts
        · have hst' : ¬ s < t := not_lt.2 hts.le
          simp only [hst', ↓reduceIte]; exact hzero t hts
        · simp only [hts, ↓reduceIte]; exact hderiv t hts
      · intro t ht hne
        rcases lt_or_gt_of_ne hne with hts | hts
        · have hst' : ¬ s < t := not_lt.2 hts.le
          simp only [hst', ↓reduceIte, norm_zero]; exact hB0
        · simp only [hts, ↓reduceIte]
          have hb := kdE_bound ν μ (IIIa.thinSource ε F) y C0 hν hC0 lkerSumEq lOpBound
            sepMajorantMono hU0 t (t - s) (sub_pos.2 hts) z i
          rw [sub_sub_cancel] at hb
          have h5' := gkerMajShiftLe (μ : ℂ) (IIIa.thinSource ε F) s t t₀ z hm1 hts
            (by simp only [ht₀]; linarith [ht.2]) (by simp only [ht₀]; linarith [ht.1])
          simp only [Complex.ofReal_re] at h5'
          have hlt : s < t₀ := by simp only [ht₀]; linarith [ht.2]
          show _ ≤ C2 * K *
            (if s < t₀ then gkerMaj (μ : ℂ) (IIIa.thinSource ε F) t₀ (t₀ - s, z) else 0)
          simp only [hlt, ↓reduceIte]
          calc _ ≤ C2 * gkerMaj (μ : ℂ) (IIIa.thinSource ε F) t (t - s, z) := hb
            _ ≤ C2 * (K * gkerMaj (μ : ℂ) (IIIa.thinSource ε F) t₀ (t₀ - s, z)) :=
                mul_le_mul_of_nonneg_left h5' hC2n
            _ = _ := by ring
    have hae : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × Space)), p.1 ≠ τ := by
      have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ τ := by
        simp [ae_iff]
      exact Measure.quasiMeasurePreserving_fst.ae h1
    have hmeas := thin_extIntMeasurable (ν := ν) (μ := μ) hν hε hth y i
    have key := hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := volume.prod volume)
      (F := fun t p => extInt (IIIa.thinSource ε F) (Kd ν μ) t y i p)
      (F' := extInt (IIIa.thinSource ε F) (kdDh ν μ) τ y i)
      (bound := g) (s := Metric.ball τ 1)
      (Metric.ball_mem_nhds τ one_pos)
      (Eventually.of_forall fun t => hmeas.1 t)
      (thin_extIntKdIntegrable hν hμ hε hc hρo hth hN hy i τ)
      (hmeas.2 τ) hlip hg
      (hae.mono fun p hp => extIntPointDeriv ν μ hν (IIIa.thinSource ε F) τ y i p hp)
    have hfun : (fun t => kerInt (IIIa.thinSource ε F) (Kd ν μ) t y i) =
        fun t => -∫ p, extInt (IIIa.thinSource ε F) (Kd ν μ) t y i p ∂(volume.prod volume) := by
      funext t
      exact kerIntShift (IIIa.thinSource ε F) (Kd ν μ) t y i
        (thin_extIntKdIntegrable hν hμ hε hc hρo hth hN hy i t)
    rw [hfun, kerIntShift (IIIa.thinSource ε F) (kdDh ν μ) τ y i key.1]
    exact key.2.neg
  have hfun : (fun t => srcX0 ν μ (IIIa.thinSource ε F) t y) =
      fun t => WithLp.toLp 2 fun i => (kerInt (IIIa.thinSource ε F) (Kd ν μ) t y i).re := by
    funext t
    exact thin_X0_eq_kerInt hν hμ hε hc hρo hth hN t hy
  rw [hfun]
  have hc_re : ∀ i : Fin 3, HasDerivAt
      (fun t => (kerInt (IIIa.thinSource ε F) (Kd ν μ) t y i).re)
      (kerInt (IIIa.thinSource ε F) (kdDh ν μ) τ y i).re τ := fun i =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ (hkd_deriv i)
  have hp : HasDerivAt
      (fun t => fun i : Fin 3 => (kerInt (IIIa.thinSource ε F) (Kd ν μ) t y i).re)
      (fun i : Fin 3 => (kerInt (IIIa.thinSource ε F) (kdDh ν μ) τ y i).re) τ :=
    hasDerivAt_pi.2 hc_re
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ hp

/-- Direct radial-gap bound on `iteratedFDeriv ℝ n (sepPhi ν (μ : ℂ) T t i (l, z)) y0` for `n ≤ 2`. -/
theorem sepPhi_radial_gap_bound {ν μ P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hS : IIIa.IsSepSource P rOut T) {Cn : ℝ} (hCn0 : 0 ≤ Cn)
    (hCn : ∀ n : ℕ, n ≤ 2 → ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK t i k y) x‖ ≤ Cn * ‖x‖ ^ (-4 - (n : ℝ)))
    {y0 : Space} (hy0 : rOut < ϱ y0) (t : ℝ) (i : Fin 3)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (z : Space) {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (sepPhi ν (μ : ℂ) T t i (l, z)) y0‖ ≤
      18 * Cn * (ϱ y0 - rOut) ^ (-4 - (n : ℝ)) *
        (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t + 2 * Real.log l) z)) := by
  have hl0 : 0 < l := hl.1
  have hD : 0 < ϱ y0 - rOut := sub_pos.2 hy0
  by_cases hz : rOut < ϱ z
  · have hT : T (t + 2 * Real.log l) z = 0 := hS.support _ _ hz
    refine (L4_phi ν (μ : ℂ) T t i l z hl hν heatLerayKSmooth n hn y0).trans ?_
    have h0 : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
        ((T (t + 2 * Real.log l) z j k : ℝ) : ℂ))‖ = 0 := by
      intro j k; simp [hT]
    simp only [h0, zero_mul, Finset.sum_const_zero]
    have : 0 ≤ IIIa.tensorNorm (T (t + 2 * Real.log l) z) := Real.sqrt_nonneg _
    positivity
  · push Not at hz
    have hgap : ϱ y0 - rOut ≤ ‖y0 - l • z‖ := by
      have h1 := L4_varrho_tri y0 (l • z)
      have h2 := L4_varrho_le_norm (y0 - l • z)
      rw [L4_varrho_smul l hl0.le] at h1
      have h3 : l * ϱ z ≤ rOut := by nlinarith [ϱ_nonneg z, hl.1, hl.2]
      linarith
    have hx0 : 0 < ‖y0 - l • z‖ := lt_of_lt_of_le hD hgap
    have hx : y0 - l • z ≠ 0 := norm_pos_iff.1 hx0
    have hpow : ‖y0 - l • z‖ ^ (-4 - (n : ℝ)) ≤ (ϱ y0 - rOut) ^ (-4 - (n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hD hgap (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    refine (L4_phi ν (μ : ℂ) T t i l z hl hν heatLerayKSmooth n hn y0).trans ?_
    have hterm : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
          ((T (t + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
        ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y0 - l • z)‖ ≤
        2 * Cn * (ϱ y0 - rOut) ^ (-4 - (n : ℝ)) *
          (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t + 2 * Real.log l) z)) := by
      intro j k
      have ht : 0 < ν * (1 - l ^ 2) := by
        have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
      have hk := (hCn n hn _ hx i j _ ht).trans (mul_le_mul_of_nonneg_left hpow hCn0)
      have he : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
      have hn1 : ‖(-2 * (l : ℂ) ^ (2 * (μ : ℂ) + 2) *
            ((T (t + 2 * Real.log l) z j k : ℝ) : ℂ))‖ ≤
          2 * l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t + 2 * Real.log l) z) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
          Complex.norm_cpow_eq_rpow_re_of_pos hl0]
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Real.norm_eq_abs]
        have := L4_entry (T (t + 2 * Real.log l) z) j k
        have hp : 0 ≤ l ^ (2 * μ + 2) := by positivity
        have h2' : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2']
        nlinarith
      rw [he, mul_one]
      calc _ ≤ (2 * l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t + 2 * Real.log l) z)) *
            (Cn * (ϱ y0 - rOut) ^ (-4 - (n : ℝ))) :=
            mul_le_mul hn1 hk (norm_nonneg _)
              (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        _ = 2 * Cn * (ϱ y0 - rOut) ^ (-4 - (n : ℝ)) *
              (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t + 2 * Real.log l) z)) := by ring
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linarith

/-- Pointwise bound on the `kdDh` kernel contraction for `h > 0` and `rOut < ϱ y0`. -/
theorem kdDh_radial_gap_bound {ν μ P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hS : IIIa.IsSepSource P rOut T) {Cn : ℝ} (hCn0 : 0 ≤ Cn)
    (hCn : ∀ n : ℕ, n ≤ 2 → ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK t i k y) x‖ ≤ Cn * ‖x‖ ^ (-4 - (n : ℝ)))
    {y0 : Space} (hy0 : rOut < ϱ y0) (t : ℝ) {h : ℝ} (hh : 0 < h) (z : Space) (i : Fin 3) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, kdDh ν μ h y0 z i j k * ((T (t - h) z j k : ℝ) : ℂ)‖ ≤
      18 * Cn * ((1 + ‖(μ : ℂ) - 1 / 2‖) * (ϱ y0 - rOut) ^ (-4 : ℝ) +
        (‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) + 3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) *
        (Real.exp (-h / 2) / 2 *
          (Real.exp (-h / 2) ^ (2 * μ + 2) * IIIa.tensorNorm (T (t - h) z))) := by
  have hkd_eq : ∀ j k : Fin 3, kdDh ν μ h y0 z i j k = kdE ν μ h y0 z i j k := fun j k =>
    (kdHasDerivAt ν μ hν h hh y0 z i j k).deriv
  simp_rw [hkd_eq]
  set l : ℝ := Real.exp (-h / 2) with hl_def
  have hl : l ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hlog : t + 2 * Real.log l = t - h := by rw [hl_def, Real.log_exp]; ring
  set Mh : ℝ := (l / 2) * (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t - h) z))
  have hMh0 : 0 ≤ l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t - h) z) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hc0 : 0 ≤ l / 2 := by positivity
  have hD : 0 < ϱ y0 - rOut := sub_pos.2 hy0
  -- bound for n = 0 (Gker sum)
  have hG : ‖∑ j : Fin 3, ∑ k : Fin 3, Gker ν (μ : ℂ) h y0 z i j k * ((T (t - h) z j k : ℝ) : ℂ)‖ ≤
      18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh := by
    have hn0 := sepPhi_radial_gap_bound (μ := μ) hν hS hCn0 hCn hy0 t i hl z (n := 0) (by norm_num)
    rw [norm_iteratedFDeriv_zero, hlog] at hn0
    simp only [Nat.cast_zero, sub_zero] at hn0
    rw [gkerSum_eq_sepPhi ν (μ : ℂ) T t i y0 z h, ← hl_def, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg hc0]
    calc (l / 2) * ‖sepPhi ν (μ : ℂ) T t i (l, z) y0‖
        ≤ (l / 2) * (18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) *
            (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t - h) z))) :=
          mul_le_mul_of_nonneg_left hn0 hc0
      _ = 18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh := by ring
  -- bound for n = 1, 2 (Lker sum)
  have hL : ‖∑ j : Fin 3, ∑ k : Fin 3, Lker ν (Gker ν (μ : ℂ)) h y0 z i j k *
      ((T (t - h) z j k : ℝ) : ℂ)‖ ≤
      18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
        3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) * Mh := by
    rw [lkerSumEq ν μ hν T t h hh y0 z i, ← hl_def, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg hc0]
    have hcd : ContDiff ℝ 2 (sepPhi ν (μ : ℂ) T t i (l, z)) :=
      sepPhi_contDiff heatLerayKSmooth ν (μ : ℂ) T t i l z hν hl
    have hb := lOpBound ν _ y0 hcd
    have hn1 := sepPhi_radial_gap_bound (μ := μ) hν hS hCn0 hCn hy0 t i hl z (n := 1) (by norm_num)
    have hn2 := sepPhi_radial_gap_bound (μ := μ) hν hS hCn0 hCn hy0 t i hl z (n := 2) (by norm_num)
    rw [hlog, show (-4 - ((1 : ℕ) : ℝ)) = (-5 : ℝ) by norm_num] at hn1
    rw [hlog, show (-4 - ((2 : ℕ) : ℝ)) = (-6 : ℝ) by norm_num] at hn2
    have hLe : ‖(1 / 2 : ℂ) * fderiv ℝ (sepPhi ν (μ : ℂ) T t i (l, z)) y0 y0 +
        (ν : ℂ) * ∑ m : Fin 3, fderiv ℝ (fun y' => fderiv ℝ
          (sepPhi ν (μ : ℂ) T t i (l, z)) y' (UnforcedLeray.coordinateVector m)) y0
          (UnforcedLeray.coordinateVector m)‖ ≤
        18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
          3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) *
          (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t - h) z)) := by
      refine hb.trans ?_
      have e1 := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ ‖y0‖ / 2 by positivity)
      have e2 := mul_le_mul_of_nonneg_left hn2 (show 0 ≤ 3 * |ν| by positivity)
      linarith
    calc (l / 2) * _
        ≤ (l / 2) * (18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
            3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) *
            (l ^ (2 * μ + 2) * IIIa.tensorNorm (T (t - h) z))) :=
          mul_le_mul_of_nonneg_left hLe hc0
      _ = 18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
            3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) * Mh := by ring
  -- combine via kdE definition
  set A := ∑ j : Fin 3, ∑ k : Fin 3,
    Gker ν (μ : ℂ) h y0 z i j k * ((T (t - h) z j k : ℝ) : ℂ) with hAd
  set B := ∑ j : Fin 3, ∑ k : Fin 3,
    Lker ν (Gker ν (μ : ℂ)) h y0 z i j k * ((T (t - h) z j k : ℝ) : ℂ) with hBd
  have hsum : ∑ j : Fin 3, ∑ k : Fin 3, kdE ν μ h y0 z i j k * ((T (t - h) z j k : ℝ) : ℂ) =
      ((Real.exp (-h) : ℝ) : ℂ) * A +
        ((1 - Real.exp (-h) : ℝ) : ℂ) * (B - ((μ : ℂ) - 1 / 2) * A) := by
    simp only [kdE, hAd, hBd, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have he0 : 0 < Real.exp (-h) := Real.exp_pos _
  have he1 : Real.exp (-h) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have n1 : ‖((Real.exp (-h) : ℝ) : ℂ) * A‖ ≤ 18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg he0.le]
    calc Real.exp (-h) * ‖A‖ ≤ 1 * (18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh) :=
          mul_le_mul he1.le hG (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have n2 : ‖((1 - Real.exp (-h) : ℝ) : ℂ) * (B - ((μ : ℂ) - 1 / 2) * A)‖ ≤
      18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
        3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) * Mh +
      ‖(μ : ℂ) - 1 / 2‖ * (18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hin : ‖B - ((μ : ℂ) - 1 / 2) * A‖ ≤
        18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
          3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) * Mh +
        ‖(μ : ℂ) - 1 / 2‖ * (18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul_of_nonneg_left hG (norm_nonneg ((μ : ℂ) - 1 / 2))
      linarith
    calc (1 - Real.exp (-h)) * ‖B - ((μ : ℂ) - 1 / 2) * A‖
        ≤ 1 * (18 * Cn * ((‖y0‖ / 2) * (ϱ y0 - rOut) ^ (-5 : ℝ) +
            3 * |ν| * (ϱ y0 - rOut) ^ (-6 : ℝ)) * Mh +
          ‖(μ : ℂ) - 1 / 2‖ * (18 * Cn * (ϱ y0 - rOut) ^ (-4 : ℝ) * Mh)) :=
          mul_le_mul (by linarith) hin (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine (norm_add_le _ _).trans ?_
  linarith

/-- Uniform-in-phase `(ρ - ρo / ε) ^ (-3 / 2)` bound on `ρ * (∂_τ X₀)_z(ρ, 0, z₀)` for `ρ ≥ r > ρo / ε`. -/
theorem thin_deriv_tau_bound {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    {r : ℝ} (hrr : ρo / ε < r) (z₀ : ℝ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (t ρ : ℝ), r ≤ ρ →
      |ρ * (deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s !₂[ρ, 0, z₀]) t) 2| ≤
        Cb * (ρ - ρo / ε) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Cn, hCn0, hCn⟩ := L4_kern IIIa.sepKernelBounds
  set rOut : ℝ := ρo / ε
  have hrOut0 : 0 ≤ rOut := div_nonneg hρo hε.le
  have hr0 : 0 < r := lt_of_le_of_lt hrOut0 hrr
  set D₀ : ℝ := r - rOut
  have hD₀ : 0 < D₀ := sub_pos.2 hrr
  set κ : ℝ := r / D₀
  have hκ0 : 0 ≤ κ := by positivity
  set M_enn : ℝ≥0∞ :=
    ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * μ + 2 + 1) * c)))) *
      ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)
  have hM_lt : M_enn < ⊤ := by
    refine ENNReal.mul_lt_top ?_
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN))
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  set M : ℝ := M_enn.toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hM_eq : ENNReal.ofReal M = M_enn := ENNReal.ofReal_toReal hM_lt.ne
  set K_r : ℝ := 18 * Cn * κ *
    ((1 + ‖(μ : ℂ) - 1 / 2‖) * D₀ ^ (-(3 / 2 : ℝ)) +
      (κ / 2) * D₀ ^ (-(3 / 2 : ℝ)) +
      (|z₀| / 2) * D₀ ^ (-(5 / 2 : ℝ)) +
      3 * |ν| * D₀ ^ (-(7 / 2 : ℝ)))
  have hKr0 : 0 ≤ K_r := by positivity
  refine ⟨K_r * M, by positivity, fun t ρ hρr => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr0 hρr
  set y0 : Space := !₂[ρ, 0, z₀]
  have hϱ : ϱ y0 = ρ := tcd_varrho hρ0.le
  have hy0 : rOut < ϱ y0 := by rw [hϱ]; exact lt_of_lt_of_le hrr hρr
  set D : ℝ := ρ - rOut
  have hD : 0 < D := sub_pos.2 (lt_of_lt_of_le hrr hρr)
  have hDD₀ : D₀ ≤ D := by show r - rOut ≤ ρ - rOut; linarith
  have hρκ : ρ ≤ κ * D := by
    show ρ ≤ (r / D₀) * (ρ - rOut)
    rw [div_mul_eq_mul_div, le_div_iff₀ hD₀]
    show ρ * (r - rOut) ≤ r * (ρ - rOut)
    nlinarith
  have hd_tau := (thin_hasDerivAt_tau hν hμ hε hc hρo hth hN t hy0).deriv
  have hd2 : |(deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s y0) t) 2| ≤
      ‖kerInt (IIIa.thinSource ε F) (kdDh ν μ) t y0 2‖ := by
    rw [hd_tau]
    exact Complex.abs_re_le_norm _
  -- Bound the radial prefactor by K_r * D ^ (-3/2)
  set Φ_y : ℝ := 18 * Cn * ((1 + ‖(μ : ℂ) - 1 / 2‖) * D ^ (-4 : ℝ) +
    (‖y0‖ / 2) * D ^ (-5 : ℝ) + 3 * |ν| * D ^ (-6 : ℝ))
  have hΦ_bound : ρ * Φ_y ≤ K_r * D ^ (-(3 / 2 : ℝ)) := by
    have hnorm : ‖y0‖ ≤ κ * D + |z₀| := (tcd_norm_pt ρ z₀ hρ0.le).trans (by linarith)
    have hrpow : ∀ a b : ℝ, D ^ (a + b) = D ^ a * D ^ b := fun a b => Real.rpow_add hD a b
    have e4 : D * D ^ (-4 : ℝ) = D ^ (-(3 / 2 : ℝ)) * D ^ (-(3 / 2 : ℝ)) := by
      calc D * D ^ (-4 : ℝ) = D ^ (1 : ℝ) * D ^ (-4 : ℝ) := by rw [Real.rpow_one]
        _ = D ^ ((1 : ℝ) + (-4 : ℝ)) := (hrpow 1 (-4)).symm
        _ = D ^ (-(3 / 2 : ℝ) + -(3 / 2 : ℝ)) := by congr 1; ring
        _ = D ^ (-(3 / 2 : ℝ)) * D ^ (-(3 / 2 : ℝ)) := hrpow _ _
    have e5a : D * (D * D ^ (-5 : ℝ)) = D ^ (-(3 / 2 : ℝ)) * D ^ (-(3 / 2 : ℝ)) := by
      calc D * (D * D ^ (-5 : ℝ)) = D ^ (1 : ℝ) * (D ^ (1 : ℝ) * D ^ (-5 : ℝ)) := by
            rw [Real.rpow_one]
        _ = D ^ ((1 : ℝ) + ((1 : ℝ) + (-5 : ℝ))) := by rw [← hrpow, ← hrpow]
        _ = D ^ (-(3 / 2 : ℝ) + -(3 / 2 : ℝ)) := by congr 1; ring
        _ = D ^ (-(3 / 2 : ℝ)) * D ^ (-(3 / 2 : ℝ)) := hrpow _ _
    have e5b : D * D ^ (-5 : ℝ) = D ^ (-(3 / 2 : ℝ)) * D ^ (-(5 / 2 : ℝ)) := by
      calc D * D ^ (-5 : ℝ) = D ^ (1 : ℝ) * D ^ (-5 : ℝ) := by rw [Real.rpow_one]
        _ = D ^ ((1 : ℝ) + (-5 : ℝ)) := (hrpow 1 (-5)).symm
        _ = D ^ (-(3 / 2 : ℝ) + -(5 / 2 : ℝ)) := by congr 1; ring
        _ = D ^ (-(3 / 2 : ℝ)) * D ^ (-(5 / 2 : ℝ)) := hrpow _ _
    have e6 : D * D ^ (-6 : ℝ) = D ^ (-(3 / 2 : ℝ)) * D ^ (-(7 / 2 : ℝ)) := by
      calc D * D ^ (-6 : ℝ) = D ^ (1 : ℝ) * D ^ (-6 : ℝ) := by rw [Real.rpow_one]
        _ = D ^ ((1 : ℝ) + (-6 : ℝ)) := (hrpow 1 (-6)).symm
        _ = D ^ (-(3 / 2 : ℝ) + -(7 / 2 : ℝ)) := by congr 1; ring
        _ = D ^ (-(3 / 2 : ℝ)) * D ^ (-(7 / 2 : ℝ)) := hrpow _ _
    have d3 : D ^ (-(3 / 2 : ℝ)) ≤ D₀ ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hD₀ hDD₀ (by norm_num)
    have d5 : D ^ (-(5 / 2 : ℝ)) ≤ D₀ ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hD₀ hDD₀ (by norm_num)
    have d7 : D ^ (-(7 / 2 : ℝ)) ≤ D₀ ^ (-(7 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hD₀ hDD₀ (by norm_num)
    calc ρ * Φ_y
        ≤ (κ * D) * (18 * Cn * ((1 + ‖(μ : ℂ) - 1 / 2‖) * D ^ (-4 : ℝ) +
            ((κ * D + |z₀|) / 2) * D ^ (-5 : ℝ) + 3 * |ν| * D ^ (-6 : ℝ))) := by
          dsimp only [Φ_y]; gcongr
      _ = 18 * Cn * κ * ((1 + ‖(μ : ℂ) - 1 / 2‖) * (D * D ^ (-4 : ℝ)) +
            (κ / 2) * (D * (D * D ^ (-5 : ℝ))) +
            (|z₀| / 2) * (D * D ^ (-5 : ℝ)) +
            3 * |ν| * (D * D ^ (-6 : ℝ))) := by ring
      _ = 18 * Cn * κ * ((1 + ‖(μ : ℂ) - 1 / 2‖) * D ^ (-(3 / 2 : ℝ)) +
            (κ / 2) * D ^ (-(3 / 2 : ℝ)) +
            (|z₀| / 2) * D ^ (-(5 / 2 : ℝ)) +
            3 * |ν| * D ^ (-(7 / 2 : ℝ))) * D ^ (-(3 / 2 : ℝ)) := by
          rw [e4, e5a, e5b, e6]; ring
      _ ≤ K_r * D ^ (-(3 / 2 : ℝ)) := by
          dsimp only [K_r]; gcongr
  -- Bound ‖kerInt (thinSource ε F) (kdDh ν μ) t y0 2‖ ≤ Φ_y * M
  have hker_le : ‖kerInt (IIIa.thinSource ε F) (kdDh ν μ) t y0 2‖ ≤ Φ_y * M := by
    have hS := thin_isSep hε hth
    have hpt : ∀ h ∈ Ioi (0 : ℝ), ∀ z : Space,
        ‖∑ j : Fin 3, ∑ k : Fin 3, kdDh ν μ h y0 z 2 j k *
          ((IIIa.thinSource ε F (t - h) z j k : ℝ) : ℂ)‖ₑ ≤
        ENNReal.ofReal Φ_y *
          (ENNReal.ofReal (Real.exp (-h / 2) / 2) *
            (ENNReal.ofReal (Real.exp (-h / 2) ^ (2 * μ + 2)) *
              IIIa.srcNorm (IIIa.thinSource ε F) (t - h) z)) := by
      intro h hh z
      have hb := kdDh_radial_gap_bound (μ := μ) hν hS hCn0 hCn hy0 t hh z 2
      rw [hϱ] at hb
      rw [← ofReal_norm]
      have h1 := ENNReal.ofReal_le_ofReal hb
      have hΦ0 : 0 ≤ Φ_y := by positivity
      rw [ENNReal.ofReal_mul (p := Φ_y) hΦ0,
        ENNReal.ofReal_mul (p := Real.exp (-h / 2) / 2) (by positivity),
        ENNReal.ofReal_mul (p := Real.exp (-h / 2) ^ (2 * μ + 2)) (by positivity)] at h1
      exact h1
    -- Change of variables h ↦ l = exp(-h/2) in the lintegral
    set N_slice : ℝ → ℝ≥0∞ := fun l =>
      ENNReal.ofReal (l ^ (2 * μ + 2)) *
        ∫⁻ z : Space, IIIa.srcNorm (IIIa.thinSource ε F) (t + 2 * Real.log l) z
    have himg : (fun h : ℝ => Real.exp (-h / 2)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
      ext l
      constructor
      · rintro ⟨h, hh, rfl⟩
        refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 ?_⟩
        have : (0 : ℝ) < h := hh; linarith
      · rintro ⟨hl0, hl1⟩
        refine ⟨-2 * Real.log l, ?_, ?_⟩
        · have : Real.log l < 0 := Real.log_neg hl0 hl1
          show (0 : ℝ) < -2 * Real.log l; linarith
        · show Real.exp (-(-2 * Real.log l) / 2) = l
          rw [show -(-2 * Real.log l) / 2 = Real.log l by ring, Real.exp_log hl0]
    have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun h : ℝ => Real.exp (-h / 2))
        (Real.exp (-x / 2) * (-1 / 2)) (Ioi 0) x := by
      intro x _
      have h1 : HasDerivAt (fun h : ℝ => -h / 2) (-1 / 2) x := by
        simpa using ((hasDerivAt_id x).neg).div_const 2
      exact (h1.exp).hasDerivWithinAt
    have hinj : InjOn (fun h : ℝ => Real.exp (-h / 2)) (Ioi 0) := by
      intro a _ b _ hab
      have := Real.exp_injective hab; linarith
    have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun h : ℝ => Real.exp (-h / 2))
      (f' := fun x : ℝ => Real.exp (-x / 2) * (-1 / 2)) measurableSet_Ioi hderiv hinj N_slice
    rw [himg] at hcov
    have habs : ∀ x : ℝ, |Real.exp (-x / 2) * (-1 / 2)| = Real.exp (-x / 2) / 2 := by
      intro x
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_neg, abs_one, abs_two]; ring
    have ha : (-1 : ℝ) < 2 * μ + 2 := by linarith
    have hen : ‖kerInt (IIIa.thinSource ε F) (kdDh ν μ) t y0 2‖ₑ ≤
        ENNReal.ofReal (Φ_y * M) := by
      unfold kerInt
      rw [enorm_neg]
      calc ‖∫ h in Ioi (0 : ℝ), ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
              kdDh ν μ h y0 z 2 j k * ((IIIa.thinSource ε F (t - h) z j k : ℝ) : ℂ)‖ₑ
          ≤ ∫⁻ h in Ioi (0 : ℝ), ‖∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
              kdDh ν μ h y0 z 2 j k * ((IIIa.thinSource ε F (t - h) z j k : ℝ) : ℂ)‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ h in Ioi (0 : ℝ), ∫⁻ z : Space, ‖∑ j : Fin 3, ∑ k : Fin 3,
              kdDh ν μ h y0 z 2 j k * ((IIIa.thinSource ε F (t - h) z j k : ℝ) : ℂ)‖ₑ :=
            lintegral_mono fun h => enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ h in Ioi (0 : ℝ), ∫⁻ z : Space, ENNReal.ofReal Φ_y *
              (ENNReal.ofReal (Real.exp (-h / 2) / 2) *
                (ENNReal.ofReal (Real.exp (-h / 2) ^ (2 * μ + 2)) *
                  IIIa.srcNorm (IIIa.thinSource ε F) (t - h) z)) := by
            refine setLIntegral_mono' measurableSet_Ioi fun h hh => ?_
            exact lintegral_mono fun z => hpt h hh z
        _ = ENNReal.ofReal Φ_y *
              ∫⁻ h in Ioi (0 : ℝ),
                ENNReal.ofReal (|Real.exp (-h / 2) * (-1 / 2)|) * N_slice (Real.exp (-h / 2)) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun h => ?_
            have hlog_h : t + 2 * Real.log (Real.exp (-h / 2)) = t - h := by
              rw [Real.log_exp]; ring
            rw [habs h]
            simp only [N_slice, hlog_h]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal Φ_y * ∫⁻ l in Ioo (0 : ℝ) 1, N_slice l := by rw [← hcov]
        _ ≤ ENNReal.ofReal Φ_y * M_enn := by
            gcongr
            exact thin_total hε hc hth (2 * μ + 2) ha t
        _ = ENNReal.ofReal (Φ_y * M) := by
            rw [← hM_eq, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_norm] at hen
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hen
  rw [abs_mul, abs_of_pos hρ0]
  calc ρ * |(deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s y0) t) 2|
      ≤ ρ * (Φ_y * M) := mul_le_mul_of_nonneg_left (hd2.trans hker_le) hρ0.le
    _ = (ρ * Φ_y) * M := by ring
    _ ≤ (K_r * D ^ (-(3 / 2 : ℝ))) * M := mul_le_mul_of_nonneg_right hΦ_bound hM0
    _ = (K_r * M) * D ^ (-(3 / 2 : ℝ)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

end
