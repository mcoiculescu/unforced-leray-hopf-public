import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonShort

/-!
# Parametric integral bound for `newtonVRem` (`PartIII-b:IIIb-D3/2/G5/2`)

Proves `newtonVRemBound_of : SigmaMFirstMoment χo → D3tDiffBound → NewtonVRemBound χo`
by expressing `newtonVRem = ∫_{(0,1]×ℝ²} FkerRem dmu2` where `FkerRem = Fker - Fker0`
and applying `L09.contDiffOn_integral` and `L09.norm_iteratedFDeriv_integral_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- First radial moment bound for `sigmaM`: `∫ |x'| |Σ_M(x')|_F dx' ≤ π N₁^χ(M)`
(source 4879-4884). -/
def SigmaMFirstMoment (χo : ℝ → ℝ) : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      Integrable (fun x' : ℝ × ℝ =>
        Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x')) ∧
      ∫ x' : ℝ × ℝ, Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x') ≤
        Real.pi * oldN1w c ν χo M

/-- Mean-value shift difference bound for `D3t` on the receiver region `{w | ν * (11/12) < eucSq w}`
against the source disk `|x'|² ≤ 5ν/6` (source 4879-4892). -/
def D3tDiffBound : Prop :=
  ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν t : ℝ) (w : Vec3) (x' : ℝ × ℝ),
    0 < ν → 0 ≤ t → t ≤ 1 → ν * (11 / 12) < eucSq w → x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
    ‖iteratedFDeriv ℝ m (fun x => NewtonVGeom.D3t (x - t • embPlane x') - NewtonVGeom.D3t x) w‖ ≤
      K * Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m)

open NewtonVGeom

/-- The zero-shift parametric integrand `gOp a (D3t y)`. -/
def Fker0 (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (a : ℝ × (ℝ × ℝ)) (y : Vec3) : Vec3 :=
  gOp c ν μ χo M a (D3t y)

/-- The remainder parametric integrand `gOp a (D3t (y - a.1 • embPlane a.2) - D3t y)`. -/
def FkerRem (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (a : ℝ × (ℝ × ℝ)) (y : Vec3) : Vec3 :=
  gOp c ν μ χo M a (D3t (y - a.1 • embPlane a.2) - D3t y)

theorem FkerRem_eq_sub (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (a : ℝ × (ℝ × ℝ)) :
    FkerRem c ν μ χo M a = Fker c ν μ χo M a - Fker0 c ν μ χo M a := by
  funext y
  simp [FkerRem, Fker, Fker0, map_sub]

theorem regU_ne_zero {ν : ℝ} (hν : 0 < ν) {y : Vec3} (hy : ν * (11 / 12) < eucSq y) : y ≠ 0 := by
  intro h0
  have : eucSq (0 : Vec3) = 0 := by simp [eucSq]
  rw [h0, this] at hy
  linarith

theorem contDiffOn_Fker0 (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) {ν' : ℝ} (hν' : 0 < ν')
    (a : ℝ × (ℝ × ℝ)) :
    ContDiffOn ℝ NewtonD3.ii (Fker0 c ν μ χo M a) {w | ν' * (11 / 12) < eucSq w} := by
  intro y hy
  exact ((D3t_contDiffAt (regU_ne_zero hν' hy)).continuousLinearMap_comp
    (gOp c ν μ χo M a)).contDiffWithinAt

theorem contDiffOn_FkerRem {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) {a : ℝ × (ℝ × ℝ)} (ht0 : 0 ≤ a.1) (ht1 : a.1 ≤ 1) :
    ContDiffOn ℝ NewtonD3.ii (FkerRem c ν μ χo M a) {w | ν * (11 / 12) < eucSq w} := by
  rw [FkerRem_eq_sub]
  exact (contDiffOn_Fker hν hχ M ht0 ht1).sub (contDiffOn_Fker0 c ν μ χo M hν a)

theorem iter_FkerRem (n : ℕ) {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) {a : ℝ × (ℝ × ℝ)} (ht0 : 0 ≤ a.1) (ht1 : a.1 ≤ 1) {y : Vec3}
    (hy : ν * (11 / 12) < eucSq y) :
    iteratedFDeriv ℝ n (FkerRem c ν μ χo M a) y =
      (gOp c ν μ χo M a).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2) - D3t x) y) := by
  by_cases h : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6
  · have hz := shift_ne_zero hν ht0 ht1 hy h
    have hy0 := regU_ne_zero hν hy
    have hcd1 : ContDiffAt ℝ NewtonD3.ii (fun x => D3t (x - a.1 • embPlane a.2)) y :=
      (D3t_contDiffAt hz).comp y (contDiffAt_id.sub contDiffAt_const)
    have hcd : ContDiffAt ℝ NewtonD3.ii (fun x => D3t (x - a.1 • embPlane a.2) - D3t x) y :=
      hcd1.sub (D3t_contDiffAt hy0)
    exact ContinuousLinearMap.iteratedFDeriv_comp_left (gOp c ν μ χo M a) hcd
      (by unfold NewtonD3.ii; exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))
  · have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M h
    have hF : FkerRem c ν μ χo M a = fun _ => 0 := by
      funext x; simp [FkerRem, h0]
    rw [hF, h0]
    ext m
    simp

theorem FkerRem_bound (hD : D3tDiffBound) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3),
      0 < ν → IsOutwardCutoff χo → 0 ≤ μ → ∀ (a : ℝ × (ℝ × ℝ)), 0 ≤ a.1 → a.1 ≤ 1 →
      ∀ y : Vec3, ν * (11 / 12) < eucSq y →
      ‖iteratedFDeriv ℝ n (FkerRem c ν μ χo M a) y‖ ≤
        K * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) *
          (Real.sqrt (eucSq y)) ^ (-(5 : ℝ) - n) := by
  obtain ⟨K, hK0, hK⟩ := hD n
  refine ⟨18 * K, by positivity, ?_⟩
  intro c ν μ χo M hν hχ hμ a ht0 ht1 y hy
  have hp : 0 ≤ (Real.sqrt (eucSq y)) ^ (-(5 : ℝ) - n) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  have hrho : 0 ≤ Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) := Real.sqrt_nonneg _
  rw [iter_FkerRem n hν hχ M ht0 ht1 hy]
  by_cases h : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6
  · refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h1 := norm_gOp_le (c := c) (ν := ν) (χo := χo) hμ M ht0 ht1
    have h2 := hK ν a.1 y a.2 hν ht0 ht1 hy h
    calc ‖gOp c ν μ χo M a‖ *
          ‖iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2) - D3t x) y‖
        ≤ (18 * frob (sigmaM c ν χo M a.2)) *
            (K * Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * (Real.sqrt (eucSq y)) ^ (-(5 : ℝ) - n)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 18 * K * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) *
            (Real.sqrt (eucSq y)) ^ (-(5 : ℝ) - n) := by ring
  · have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M h
    have hz : ∀ φ : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec3) T3,
        (0 : T3 →L[ℝ] Vec3).compContinuousMultilinearMap φ = 0 := fun φ => by ext m; simp
    rw [h0, hz, norm_zero]
    positivity

theorem aesm_iter_Fker0 (n : ℕ) {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν)
    (M : Chart → Mat3) (hS : AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') volume)
    {x : Vec3} (hx : ν * (11 / 12) < eucSq x) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (Fker0 c ν μ χo M a) x) mu2 := by
  have hx0 := regU_ne_zero hν hx
  have hS2 : AEStronglyMeasurable (fun a : ℝ × (ℝ × ℝ) => sigmaM c ν χo M a.2) mu2 :=
    hS.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (ν := (volume : Measure (ℝ × ℝ))))
  have H2 : AEStronglyMeasurable (gOp c ν μ χo M) mu2 := by
    have hs : Measurable fun a : ℝ × (ℝ × ℝ) => -2 * a.1 ^ (2 * μ + 2) := by fun_prop
    exact hs.aestronglyMeasurable.smul (continuous_Lmat.comp_aestronglyMeasurable hS2)
  have H1 : AEStronglyMeasurable (fun _ : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ n D3t x) mu2 :=
    aestronglyMeasurable_const
  have H := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Vec3) T3 Vec3
    ).aestronglyMeasurable_comp₂ H2 H1
  refine H.congr (Eventually.of_forall fun a => ?_)
  simp only [ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  exact (ContinuousLinearMap.iteratedFDeriv_comp_left (gOp c ν μ χo M a) (D3t_contDiffAt hx0)
    (by unfold NewtonD3.ii; exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))).symm

theorem aesm_iter_FkerRem (n : ℕ) {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) (hS : AEStronglyMeasurable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') volume)
    {x : Vec3} (hx : ν * (11 / 12) < eucSq x) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (FkerRem c ν μ χo M a) x) mu2 := by
  have h1 := aesm_iter_Fker (μ := μ) n hν hχ M hS hx
  have h0 := aesm_iter_Fker0 (μ := μ) n hν M hS hx
  refine (h1.sub h0).congr ?_
  filter_upwards [ae_good] with a ha
  have hUo := isOpen_regU ν
  have hc1 : ContDiffAt ℝ NewtonD3.ii (Fker c ν μ χo M a) x :=
    (contDiffOn_Fker hν hχ M ha.1.le ha.2).contDiffAt (hUo.mem_nhds hx)
  have hc0 : ContDiffAt ℝ NewtonD3.ii (Fker0 c ν μ χo M a) x :=
    (contDiffOn_Fker0 c ν μ χo M hν a).contDiffAt (hUo.mem_nhds hx)
  have hn : (n : WithTop ℕ∞) ≤ NewtonD3.ii := by
    unfold NewtonD3.ii; exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))
  rw [FkerRem_eq_sub]
  exact (iteratedFDeriv_sub_apply (hc1.of_le hn) (hc0.of_le hn)).symm

theorem integrable_const_mom (K : ℝ) {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3}
    (hmom : Integrable (fun x' : ℝ × ℝ =>
      Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x'))) :
    Integrable (fun a : ℝ × (ℝ × ℝ) =>
      K * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2))) mu2 := by
  have := Integrable.mul_prod (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := (volume : Measure (ℝ × ℝ))) (f := fun _ => (1 : ℝ))
    (g := fun x' : ℝ × ℝ => K * (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x')))
    (integrable_const 1) (hmom.const_mul K)
  simpa using this

theorem locDominated_FkerRem (hD : D3tDiffBound) {c ν μ : ℝ} {χo : ℝ → ℝ}
    (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (hμ : 0 ≤ μ) (M : Chart → Mat3)
    (hmom : Integrable (fun x' : ℝ × ℝ =>
      Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x'))) :
    UnforcedLeray.L09.LocDominated mu2 (FkerRem c ν μ χo M) {w | ν * (11 / 12) < eucSq w} := by
  intro n x hx
  obtain ⟨K, hK0, hK⟩ := FkerRem_bound hD n
  set R := Real.sqrt (ν * (11 / 12)) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 (by positivity)
  refine ⟨_, (isOpen_regU ν).mem_nhds hx,
    fun a => (K * R ^ (-(5 : ℝ) - n)) *
      (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)),
    integrable_const_mom _ hmom, ?_⟩
  filter_upwards [ae_good] with a ha y hy
  have hy' : ν * (11 / 12) < eucSq y := hy
  have hb := hK c ν μ χo M hν hχ hμ a ha.1.le ha.2 y hy'
  have hr : R ≤ Real.sqrt (eucSq y) := Real.sqrt_le_sqrt hy'.le
  have hp : (Real.sqrt (eucSq y)) ^ (-(5 : ℝ) - n) ≤ R ^ (-(5 : ℝ) - n) :=
    Real.rpow_le_rpow_of_nonpos hRpos hr
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine hb.trans ?_
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  have hrho : 0 ≤ Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) := Real.sqrt_nonneg _
  calc K * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) *
        (Real.sqrt (eucSq y)) ^ (-(5 : ℝ) - n)
      ≤ K * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) *
          R ^ (-(5 : ℝ) - n) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (K * R ^ (-(5 : ℝ) - n)) *
          (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) := by ring

theorem integrable_Fker0 {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hμ : 0 ≤ μ)
    (M : Chart → Mat3) (hint : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x'))
    {y : Vec3} (hy : ν * (11 / 12) < eucSq y) :
    Integrable (fun a => Fker0 c ν μ χo M a y) mu2 := by
  have hm := aesm_iter_Fker0 (μ := μ) 0 hν M hint.aestronglyMeasurable hy
  have hmeas : AEStronglyMeasurable (fun a => Fker0 c ν μ χo M a y) mu2 := by
    have := (continuousMultilinearCurryFin0 ℝ Vec3 Vec3).continuous.comp_aestronglyMeasurable hm
    refine this.congr (Eventually.of_forall fun a => ?_)
    show (continuousMultilinearCurryFin0 ℝ Vec3 Vec3) (iteratedFDeriv ℝ 0 (Fker0 c ν μ χo M a) y) = _
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  refine Integrable.mono' (integrable_const_frob (18 * ‖D3t y‖) hint) hmeas ?_
  filter_upwards [ae_good] with a ha
  calc ‖Fker0 c ν μ χo M a y‖
      ≤ ‖gOp c ν μ χo M a‖ * ‖D3t y‖ := (gOp c ν μ χo M a).le_opNorm (D3t y)
    _ ≤ (18 * frob (sigmaM c ν χo M a.2)) * ‖D3t y‖ :=
        mul_le_mul_of_nonneg_right (norm_gOp_le hμ M ha.1.le ha.2) (norm_nonneg _)
    _ = (18 * ‖D3t y‖) * frob (sigmaM c ν χo M a.2) := by ring

theorem newtonV0_eq_integral {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hμ : 0 ≤ μ)
    (M : Chart → Mat3) (hint : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x'))
    {y : Vec3} (hy : ν * (11 / 12) < eucSq y) :
    newtonV0 c ν μ χo M y = ∫ a, Fker0 c ν μ χo M a y ∂mu2 := by
  have hI := integrable_Fker0 (μ := μ) hν hμ M hint hy
  funext i
  have h1 : (∫ a, Fker0 c ν μ χo M a y ∂mu2) i = ∫ a, Fker0 c ν μ χo M a y i ∂mu2 := by
    have := (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integral_comp_comm hI
    simpa using this.symm
  rw [h1]
  have hprod := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := (volume : Measure (ℝ × ℝ)))
    (fun t : ℝ => -2 * t ^ (2 * μ + 2))
    (fun x' : ℝ × ℝ => Lmat (sigmaM c ν χo M x') (D3t y) i)
  have heq : (fun a : ℝ × (ℝ × ℝ) => Fker0 c ν μ χo M a y i) =
      fun a => (-2 * a.1 ^ (2 * μ + 2)) * Lmat (sigmaM c ν χo M a.2) (D3t y) i := by
    funext a
    simp [Fker0, gOp]
  rw [heq, hprod]
  unfold newtonV0 tInt
  simp only [Pi.smul_apply, smul_eq_mul, Lmat_apply]
  congr 1
  have hint_jk : ∀ j k : Fin 3, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k) := by
    intro j k
    have hrow : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j) :=
      (ContinuousLinearMap.proj j : Mat3 →L[ℝ] (Fin 3 → ℝ)).integrable_comp hint
    exact (ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).integrable_comp hrow
  have hsum1 : (∫ x' : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3, sigmaM c ν χo M x' j k * D3t y (i, j, k)) =
      ∑ j : Fin 3, ∫ x' : ℝ × ℝ, ∑ k : Fin 3, sigmaM c ν χo M x' j k * D3t y (i, j, k) :=
    integral_finset_sum _ fun j _ =>
      integrable_finset_sum _ fun k _ => (hint_jk j k).mul_const _
  rw [hsum1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finset_sum _ fun k _ => (hint_jk j k).mul_const _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const]
  rfl

theorem newtonVRem_eq_integral {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (hμ : 0 ≤ μ) (M : Chart → Mat3) (hint : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x'))
    {y : Vec3} (hy : ν * (11 / 12) < eucSq y) :
    newtonVRem c ν μ χo M y = ∫ a, FkerRem c ν μ χo M a y ∂mu2 := by
  unfold newtonVRem
  rw [newtonV_eq_integral hν hχ hμ M hint hy, newtonV0_eq_integral hν hμ M hint hy,
    ← integral_sub (integrable_Fker hν hχ hμ M hint hy) (integrable_Fker0 hν hμ M hint hy)]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  dsimp only
  rw [FkerRem_eq_sub]
  rfl

/-- Assembly of `NewtonVRemBound χo` from `SigmaMFirstMoment χo` and `D3tDiffBound`. -/
theorem newtonVRemBound_of {χo : ℝ → ℝ} (hMom : SigmaMFirstMoment χo) (hD : D3tDiffBound) :
    NewtonVRemBound χo := by
  choose K hK0 hK using FkerRem_bound hD
  refine ⟨fun n => K n * Real.pi, fun n => mul_nonneg (hK0 n) Real.pi_pos.le, ?_⟩
  intro c ν μ hc hν hχ hμ M hM
  obtain ⟨-, hint, -⟩ := sigmaM_l1W c ν χo hc hν hχ M hM
  obtain ⟨hmom, hmom_le⟩ := hMom c ν hc hν hχ M hM
  have hopen := isOpen_regU ν
  have hsm : ∀ᵐ a ∂mu2, ContDiffOn ℝ NewtonD3.ii (FkerRem c ν μ χo M a)
      {w | ν * (11 / 12) < eucSq w} := by
    filter_upwards [ae_good] with a ha
    exact contDiffOn_FkerRem hν hχ M ha.1.le ha.2
  have hmeas : ∀ (n : ℕ), ∀ x ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (FkerRem c ν μ χo M a) x) mu2 :=
    fun n x hx => aesm_iter_FkerRem n hν hχ M hint.aestronglyMeasurable hx
  have hdom := locDominated_FkerRem hD hν hχ hμ M hmom
  have heq : ∀ y ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      newtonVRem c ν μ χo M y = ∫ a, FkerRem c ν μ χo M a y ∂mu2 :=
    fun y hy => newtonVRem_eq_integral hν hχ hμ M hint hy
  have hcd := UnforcedLeray.L09.contDiffOn_integral hopen hsm hmeas hdom
  have hnv : ContDiffOn ℝ NewtonD3.ii (newtonVRem c ν μ χo M) {w | ν * (11 / 12) < eucSq w} :=
    hcd.congr heq
  refine ⟨hnv.of_le (by simp [NewtonD3.ii]), fun m _ w hw => ?_⟩
  have hEv : newtonVRem c ν μ χo M =ᶠ[nhds w] fun y => ∫ a, FkerRem c ν μ χo M a y ∂mu2 := by
    filter_upwards [hopen.mem_nhds hw] with y hy using heq y hy
  rw [(hEv.iteratedFDeriv ℝ m).eq_of_nhds]
  refine (UnforcedLeray.L09.norm_iteratedFDeriv_integral_le hopen hsm hmeas hdom m hw).trans ?_
  set P := (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hr : ∫ a, ‖iteratedFDeriv ℝ m (FkerRem c ν μ χo M a) w‖ ∂mu2 ≤
      ∫ a, (K m * P) * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) ∂mu2 := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun a => norm_nonneg _)
      (integrable_const_mom _ hmom) ?_
    filter_upwards [ae_good] with a ha
    have := hK m c ν μ χo M hν hχ hμ a ha.1.le ha.2 w hw
    calc _ ≤ _ := this
      _ = _ := by ring
  have hc' : ∫ a, (K m * P) * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) ∂mu2 =
      K m * P * ∫ x' : ℝ × ℝ, Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x') := by
    have := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := (volume : Measure (ℝ × ℝ))) (fun _ => (1 : ℝ))
      (fun x' : ℝ × ℝ => K m * P * (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x')))
    have e1 : (fun z : ℝ × (ℝ × ℝ) => (fun _ : ℝ => (1 : ℝ)) z.1 *
        (fun x' : ℝ × ℝ => K m * P * (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x'))) z.2) =
        fun a => K m * P * (Real.sqrt (a.2.1 ^ 2 + a.2.2 ^ 2) * frob (sigmaM c ν χo M a.2)) := by
      funext a; simp
    rw [e1] at this
    rw [this, integral_const_mul]
    simp
  refine hr.trans (hc'.le.trans ?_)
  calc K m * P * ∫ x' : ℝ × ℝ, Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) * frob (sigmaM c ν χo M x')
      ≤ K m * P * (Real.pi * oldN1w c ν χo M) :=
        mul_le_mul_of_nonneg_left hmom_le (mul_nonneg (hK0 m) hP0)
    _ = K m * Real.pi * oldN1w c ν χo M * P := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
