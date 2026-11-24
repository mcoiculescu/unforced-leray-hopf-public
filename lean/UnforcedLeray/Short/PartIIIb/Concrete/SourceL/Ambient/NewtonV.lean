import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV.Fker
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `newtonVRegionBound` (source 4776-4782, 4870-4900, 4917-4937)

`newtonV = ∫_{(0,1]×ℝ²} Fker` (Fubini), `Fker (t,x') y = -2 t^{2μ+2} · D³N(y - t(x',0)) : Σ_M(x')`.
The parametric-integral lemmas of `L09` (`contDiffOn_integral`, `norm_iteratedFDeriv_integral_le`)
give `C^∞` on `{|y|² > 11ν/12}` and `‖∂^n newtonV‖ ≤ ∫ ‖∂^n Fker‖ ≤ K_n π N₀ |y|^{-4-n}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Axi
open scoped Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonVGeom

/-- The parameter measure on `a = (t, x')`: Lebesgue on `(0,1] × ℝ²`. -/
abbrev mu2 : Measure (ℝ × (ℝ × ℝ)) := (volume.restrict (Ioc (0 : ℝ) 1)).prod volume

theorem ae_good : ∀ᵐ a : ℝ × (ℝ × ℝ) ∂mu2, a.1 ∈ Ioc (0 : ℝ) 1 :=
  (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := (volume : Measure (ℝ × ℝ)))).ae (ae_restrict_mem measurableSet_Ioc)

theorem frob_le_three_norm (A : Mat3) : frob A ≤ 3 * ‖A‖ := by
  unfold frob
  have h : ∑ i, ∑ j, A i j ^ 2 ≤ (3 * ‖A‖) ^ 2 := by
    calc ∑ i, ∑ j, A i j ^ 2 ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖A‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have h1 : ‖A i j‖ ≤ ‖A‖ := (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
          calc A i j ^ 2 = ‖A i j‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
            _ ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (3 * ‖A‖) ^ 2 := by simp; ring
  calc Real.sqrt (∑ i, ∑ j, A i j ^ 2) ≤ Real.sqrt ((3 * ‖A‖) ^ 2) := Real.sqrt_le_sqrt h
    _ = 3 * ‖A‖ := Real.sqrt_sq (by positivity)

theorem integrable_frob_sigma {S0 : (ℝ × ℝ) → Mat3} (h : Integrable S0) :
    Integrable (fun x' => frob (S0 x')) := by
  refine Integrable.mono' (h.norm.const_mul 3) (continuous_frob.comp_aestronglyMeasurable
    h.aestronglyMeasurable) (Eventually.of_forall fun x' => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (frob_nonneg' _)]
  exact frob_le_three_norm _

theorem continuous_embPlane : Continuous embPlane := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [embPlane] <;> fun_prop

/-- Measurability of the `n`-th jet of the integrand at a fixed point of the region. -/
theorem aesm_iter_Fker (n : ℕ) {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hS : AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') volume)
    {x : Vec3} (hx : ν * (11 / 12) < eucSq x) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (Fker c ν μ χo M a) x) mu2 := by
  classical
  set A0 : Set (ℝ × (ℝ × ℝ)) := {a | x - a.1 • embPlane a.2 ≠ 0} with hA0
  have hcontv : Continuous fun a : ℝ × (ℝ × ℝ) => x - a.1 • embPlane a.2 := by
    have := continuous_embPlane
    fun_prop
  have hA0open : IsOpen A0 := (isOpen_compl_singleton).preimage hcontv
  have hD : ContDiffOn ℝ NewtonD3.ii D3t {z : Vec3 | z ≠ 0} :=
    fun z hz => (D3t_contDiffAt hz).contDiffWithinAt
  have hopen : IsOpen {z : Vec3 | z ≠ 0} := isOpen_compl_singleton
  have hD' : ContinuousOn (iteratedFDeriv ℝ n D3t) {z : Vec3 | z ≠ 0} := by
    have h1 := hD.continuousOn_iteratedFDerivWithin (m := n)
      (by unfold NewtonD3.ii; exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))) hopen.uniqueDiffOn
    exact h1.congr (iteratedFDerivWithin_of_isOpen n hopen).symm
  have hΦ : ContinuousOn (fun a : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ n D3t (x - a.1 • embPlane a.2)) A0 :=
    hD'.comp hcontv.continuousOn (fun a ha => ha)
  have H1 : AEStronglyMeasurable (A0.piecewise
      (fun a : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ n D3t (x - a.1 • embPlane a.2))
      (fun _ => 0)) mu2 :=
    AEStronglyMeasurable.piecewise hA0open.measurableSet
      (hΦ.aestronglyMeasurable hA0open.measurableSet) aestronglyMeasurable_const
  have hS2 : AEStronglyMeasurable (fun a : ℝ × (ℝ × ℝ) => sigmaM c ν χo M a.2) mu2 :=
    hS.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (ν := (volume : Measure (ℝ × ℝ))))
  have H2 : AEStronglyMeasurable (gOp c ν μ χo M) mu2 := by
    have hs : Measurable fun a : ℝ × (ℝ × ℝ) => -2 * a.1 ^ (2 * μ + 2) := by fun_prop
    exact hs.aestronglyMeasurable.smul (continuous_Lmat.comp_aestronglyMeasurable hS2)
  have H := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Vec3) T3 Vec3
    ).aestronglyMeasurable_comp₂ H2 H1
  refine H.congr ?_
  filter_upwards [ae_good] with a ha
  have ht0 := ha.1.le
  have ht1 := ha.2
  rw [iter_Fker n hν hχ M ht0 ht1 hx]
  by_cases hz : a ∈ A0
  · simp only [Set.piecewise_eq_of_mem _ _ _ hz,
      ContinuousLinearMap.compContinuousMultilinearMapL_apply]
    rw [iteratedFDeriv_comp_sub]
  · have hnsupp : ¬ a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6 :=
      fun h => hz (shift_ne_zero hν ht0 ht1 hx h)
    have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M hnsupp
    simp only [Set.piecewise_eq_of_notMem _ _ _ hz, h0,
      ContinuousLinearMap.compContinuousMultilinearMapL_apply]
    ext m
    simp

theorem integrable_const_frob (K : ℝ) {S0 : ℝ × ℝ → Mat3} (h : Integrable S0) :
    Integrable (fun a : ℝ × (ℝ × ℝ) => K * frob (S0 a.2)) mu2 := by
  have h1 := integrable_frob_sigma h
  have := Integrable.mul_prod (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := (volume : Measure (ℝ × ℝ))) (f := fun _ => (1 : ℝ))
    (g := fun x' => K * frob (S0 x')) (integrable_const 1) (h1.const_mul K)
  simpa using this

theorem isOpen_regU (ν : ℝ) : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
  unfold eucSq
  exact isOpen_lt continuous_const (by fun_prop)

theorem locDominated_Fker {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (hμ : 0 ≤ μ) (M : Chart → Mat3) (hint : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x')) :
    UnforcedLeray.L09.LocDominated mu2 (Fker c ν μ χo M) {w | ν * (11 / 12) < eucSq w} := by
  intro n x hx
  obtain ⟨K, hK0, hK⟩ := Fker_bound n
  set R := Real.sqrt (ν * (11 / 12)) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 (by positivity)
  refine ⟨_, (isOpen_regU ν).mem_nhds hx,
    fun a => (K * R ^ (-(4 : ℝ) - n)) * frob (sigmaM c ν χo M a.2),
    integrable_const_frob _ hint, ?_⟩
  filter_upwards [ae_good] with a ha y hy
  have hy' : ν * (11 / 12) < eucSq y := hy
  have hb := hK c ν μ χo M hν hχ hμ a ha.1.le ha.2 y hy'
  have hr : R ≤ Real.sqrt (eucSq y) := Real.sqrt_le_sqrt hy'.le
  have hp : (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) ≤ R ^ (-(4 : ℝ) - n) :=
    Real.rpow_le_rpow_of_nonpos hRpos hr
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine hb.trans ?_
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  calc K * frob (sigmaM c ν χo M a.2) * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n)
      ≤ K * frob (sigmaM c ν χo M a.2) * R ^ (-(4 : ℝ) - n) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (K * R ^ (-(4 : ℝ) - n)) * frob (sigmaM c ν χo M a.2) := by ring

theorem integrable_Fker {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (hμ : 0 ≤ μ) (M : Chart → Mat3) (hint : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x'))
    {y : Vec3} (hy : ν * (11 / 12) < eucSq y) :
    Integrable (fun a => Fker c ν μ χo M a y) mu2 := by
  obtain ⟨K, hK0, hK⟩ := Fker_bound 0
  have hm := aesm_iter_Fker (μ := μ) 0 hν hχ M hint.aestronglyMeasurable hy
  have hmeas : AEStronglyMeasurable (fun a => Fker c ν μ χo M a y) mu2 := by
    have := (continuousMultilinearCurryFin0 ℝ Vec3 Vec3).continuous.comp_aestronglyMeasurable hm
    refine this.congr (Eventually.of_forall fun a => ?_)
    show (continuousMultilinearCurryFin0 ℝ Vec3 Vec3) (iteratedFDeriv ℝ 0 (Fker c ν μ χo M a) y) = _
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  refine Integrable.mono' (integrable_const_frob (K * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - (0 : ℕ)))
    hint) hmeas ?_
  filter_upwards [ae_good] with a ha
  have hb := hK c ν μ χo M hν hχ hμ a ha.1.le ha.2 y hy
  rw [norm_iteratedFDeriv_zero] at hb
  calc ‖Fker c ν μ χo M a y‖ ≤ K * frob (sigmaM c ν χo M a.2) *
        (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - (0 : ℕ)) := hb
    _ = _ := by ring

theorem Fker_apply (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (a : ℝ × (ℝ × ℝ)) (y : Vec3)
    (i : Fin 3) :
    Fker c ν μ χo M a y i = (-2 * a.1 ^ (2 * μ + 2)) *
      ∑ j, ∑ k, newtonD3 (y - a.1 • embPlane a.2) i j k * sigmaM c ν χo M a.2 j k := by
  simp only [Fker, gOp, ContinuousLinearMap.smul_apply, Pi.smul_apply, Lmat_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [D3t]
  ring

theorem newtonV_eq_integral {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (hμ : 0 ≤ μ) (M : Chart → Mat3) (hint : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x'))
    {y : Vec3} (hy : ν * (11 / 12) < eucSq y) :
    newtonV c ν μ χo M y = ∫ a, Fker c ν μ χo M a y ∂mu2 := by
  have hI := integrable_Fker hν hχ hμ M hint hy
  funext i
  have h1 : (∫ a, Fker c ν μ χo M a y ∂mu2) i = ∫ a, Fker c ν μ χo M a y i ∂mu2 := by
    have := (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integral_comp_comm hI
    simpa using this.symm
  rw [h1]
  have hI' : Integrable (fun a => Fker c ν μ χo M a y i) mu2 :=
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrable_comp hI
  rw [integral_prod _ hI']
  unfold newtonV
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Fker_apply]
  rw [integral_const_mul]
  ring

end NewtonVGeom

end UnforcedLeray.Short.PartIIIb.Concrete

namespace UnforcedLeray.Short.PartIIIb.Concrete

open NewtonVGeom in
/-- Source 4776-4782, 4870-4900, 4917-4937. -/
theorem newtonVRegionBound (χo : ℝ → ℝ) : NewtonVRegionBound χo := by
  choose K hK0 hK using NewtonVGeom.Fker_bound
  refine ⟨fun n => K n * Real.pi, ?_⟩
  intro c ν μ hc hν hχ hμ M hM
  obtain ⟨-, hint, hl1⟩ := sigmaM_l1 c ν χo hc hν hχ M hM
  have hN0 := oldN0_nonneg c ν hν M
  have hopen := isOpen_regU ν
  have hsm : ∀ᵐ a ∂mu2, ContDiffOn ℝ NewtonD3.ii (Fker c ν μ χo M a)
      {w | ν * (11 / 12) < eucSq w} := by
    filter_upwards [ae_good] with a ha
    exact contDiffOn_Fker hν hχ M ha.1.le ha.2
  have hmeas : ∀ (n : ℕ), ∀ x ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (Fker c ν μ χo M a) x) mu2 :=
    fun n x hx => aesm_iter_Fker n hν hχ M hint.aestronglyMeasurable hx
  have hdom := locDominated_Fker hν hχ hμ M hint
  have heq : ∀ y ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      newtonV c ν μ χo M y = ∫ a, Fker c ν μ χo M a y ∂mu2 :=
    fun y hy => newtonV_eq_integral hν hχ hμ M hint hy
  have hcd := UnforcedLeray.L09.contDiffOn_integral hopen hsm hmeas hdom
  have hnv : ContDiffOn ℝ NewtonD3.ii (newtonV c ν μ χo M) {w | ν * (11 / 12) < eucSq w} :=
    hcd.congr heq
  refine ⟨hnv.of_le (by simp [NewtonD3.ii]), fun m _ w hw => ?_⟩
  have hEv : newtonV c ν μ χo M =ᶠ[nhds w] fun y => ∫ a, Fker c ν μ χo M a y ∂mu2 := by
    filter_upwards [hopen.mem_nhds hw] with y hy using heq y hy
  rw [(hEv.iteratedFDeriv ℝ m).eq_of_nhds]
  refine (UnforcedLeray.L09.norm_iteratedFDeriv_integral_le hopen hsm hmeas hdom m hw).trans ?_
  set P := (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hr : ∫ a, ‖iteratedFDeriv ℝ m (Fker c ν μ χo M a) w‖ ∂mu2 ≤
      ∫ a, (K m * P) * frob (sigmaM c ν χo M a.2) ∂mu2 := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun a => norm_nonneg _)
      (integrable_const_frob _ hint) ?_
    filter_upwards [ae_good] with a ha
    have := hK m c ν μ χo M hν hχ hμ a ha.1.le ha.2 w hw
    calc _ ≤ _ := this
      _ = _ := by ring
  have hc : ∫ a, (K m * P) * frob (sigmaM c ν χo M a.2) ∂mu2 =
      K m * P * ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') := by
    have := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := (volume : Measure (ℝ × ℝ))) (fun _ => (1 : ℝ))
      (fun x' => K m * P * frob (sigmaM c ν χo M x'))
    have e1 : (fun z : ℝ × (ℝ × ℝ) => (fun _ : ℝ => (1 : ℝ)) z.1 *
        (fun x' : ℝ × ℝ => K m * P * frob (sigmaM c ν χo M x')) z.2) =
        fun a => K m * P * frob (sigmaM c ν χo M a.2) := by
      funext a; simp
    rw [e1] at this
    rw [this, integral_const_mul]
    simp
  refine hr.trans (hc.le.trans ?_)
  calc K m * P * ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x')
      ≤ K m * P * (Real.pi * oldN0 c ν M) :=
        mul_le_mul_of_nonneg_left hl1 (mul_nonneg (hK0 m) hP0)
    _ = K m * Real.pi * oldN0 c ν M * P := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
