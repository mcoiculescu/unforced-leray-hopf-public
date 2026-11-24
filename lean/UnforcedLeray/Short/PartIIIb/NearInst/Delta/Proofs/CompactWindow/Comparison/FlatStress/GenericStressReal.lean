import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.DivEpsReal

/-!
# `PartIII-b:C/near/delta/8/2/3/3/1`: `GenericStressReal` (source 1675-1679)

Proof of `GenericStressReal`: a stress map `S'` of a real-preserving `T` maps real tensors to real
fields.  Route: for a real `F` take smooth tensor tests `M_n` with `‖F - M_n‖ < 1/(n+1)`
(`Masked.tensorTestDense`), replace `M_n` by its componentwise real part `Re M_n` (still a smooth
tensor test, and `‖F - Re M_n‖ ≤ ‖F - M_n‖` since `F` is a.e. real).  Then `s div_ε (Re M_n)` is
real (`Masked.smul_divEps_im`), so `S'(Re M_n) = T(s div_ε Re M_n)` is real.  The real fields form a
closed set (`Body.isRealH_iff`: fixed points of the conjugation `cjLp`), and `S'` is continuous, so
`S' F` is real.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff
open Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIa

/-! ## The componentwise real part of a tensor value -/

/-- The componentwise real part of a tensor value (as a complex vector with zero imaginary part). -/
def gsrRe (x : TensorVal) : TensorVal :=
  WithLp.toLp 2 fun i => (((x i).re : ℝ) : ℂ)

theorem gsrRe_apply (x : TensorVal) (i : Fin 4) : gsrRe x i = (((x i).re : ℝ) : ℂ) := by
  simp [gsrRe]

theorem gsrRe_zero : gsrRe 0 = 0 := by
  ext i
  simp [gsrRe_apply]

/-- `gsrRe` as a real-linear map. -/
def gsrReLin : TensorVal →ₗ[ℝ] TensorVal where
  toFun := gsrRe
  map_add' x y := by
    ext i
    simp [gsrRe_apply]
  map_smul' a x := by
    ext i
    simp [gsrRe_apply]

/-- `gsrRe` as a continuous real-linear map. -/
def gsrReL : TensorVal →L[ℝ] TensorVal :=
  LinearMap.toContinuousLinearMap gsrReLin

theorem gsrReL_apply (x : TensorVal) : gsrReL x = gsrRe x := rfl

/-- The componentwise real part of a function of the profile. -/
def gsrReFn (f : UnforcedLeray.B0220.Profile → TensorVal) : UnforcedLeray.B0220.Profile → TensorVal :=
  fun p => gsrRe (f p)

/-- The real part does not increase the norm. -/
theorem gsrRe_norm_le (x : TensorVal) : ‖gsrRe x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [gsrRe_apply, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm (x i)

/-- Complex numbers: for a real `a`, the distance to the real part of `m` is at most the distance to
`m`. -/
theorem gsr_norm_sub_re_le (a m : ℂ) (ha : a.im = 0) : ‖a - ((m.re : ℝ) : ℂ)‖ ≤ ‖a - m‖ := by
  have hm := mul_self_nonneg m.im
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, ha]
  nlinarith [hm]

/-- For a real-valued tensor `a`, the real part of `x` is at least as close to `a` as `x`. -/
theorem gsr_norm_sub_gsrRe_le (a x : TensorVal) (ha : ∀ i, (a i).im = 0) :
    ‖a - gsrRe x‖ ≤ ‖a - x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [PiLp.sub_apply, PiLp.sub_apply, gsrRe_apply]
  exact gsr_norm_sub_re_le (a i) (x i) (ha i)

/-! ## Smooth tensor tests stay tests after taking real parts -/

theorem gsrReFn_isTensorTest {c : ℝ} {M : UnforcedLeray.B0220.Profile → TensorVal}
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c M) :
    UnforcedLeray.Short.PartIIa.IsTensorTest c (gsrReFn M) where
  smooth := by
    have h : ContDiff ℝ ∞ (fun p => gsrReL (M p)) := gsrReL.contDiff.comp hM.smooth
    exact h
  periodic := by
    intro p
    show gsrRe (M (p.1, p.2.1 + c, p.2.2)) = gsrRe (M p)
    rw [hM.periodic p]
  band := by
    obtain ⟨s0, s1, L, hs0, h⟩ := hM.band
    refine ⟨s0, s1, L, hs0, fun p hp => h p (fun h0 => hp ?_)⟩
    show gsrRe (M p) = 0
    rw [h0, gsrRe_zero]

theorem gsrReFn_realValued (M : UnforcedLeray.B0220.Profile → TensorVal) (p : UnforcedLeray.B0220.Profile)
    (i : Fin 4) : (gsrReFn M p i).im = 0 := by
  simp [gsrReFn, gsrRe_apply]

/-! ## Distances -/

/-- Replacing a test by its real part does not increase the `H_T` distance to a real field. -/
theorem gsr_dist_le (c : ℝ) (F : UnforcedLeray.Short.PartIIa.HTSpace c)
    (hF : Masked.IsRealHT c F) (M : UnforcedLeray.B0220.Profile → TensorVal)
    (hM : MemLp M 2 (UnforcedLeray.Short.PartIIa.measureHT c))
    (hN : MemLp (gsrReFn M) 2 (UnforcedLeray.Short.PartIIa.measureHT c)) :
    ‖F - hN.toLp (gsrReFn M)‖ ≤ ‖F - hM.toLp M‖ := by
  have hF' : ∀ᵐ p ∂UnforcedLeray.Short.PartIIa.measureHT c, ∀ i,
      ((F : UnforcedLeray.B0220.Profile → TensorVal) p i).im = 0 := hF
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  refine eLpNorm_mono_ae ?_
  filter_upwards [Lp.coeFn_sub F (hN.toLp (gsrReFn M)), Lp.coeFn_sub F (hM.toLp M),
    hN.coeFn_toLp, hM.coeFn_toLp, hF'] with p h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4]
  exact gsr_norm_sub_gsrRe_le _ _ h5

/-! ## Closedness of the real fields -/

theorem gsr_isClosed_isRealH (c : ℝ) :
    IsClosed {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC |
      Masked.IsRealH c g} := by
  have heq : {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC |
      Masked.IsRealH c g} =
      {g | Body.cjLp (UnforcedLeray.B0220.measureH c) 2 g = g} := by
    ext g
    exact Body.isRealH_iff g
  rw [heq]
  exact isClosed_eq (Body.cjLp (UnforcedLeray.B0220.measureH c) 2).continuous continuous_id

/-! ## The main statement -/

/-- **Generic reality of stress maps** (source 1675-1679). -/
theorem genericStressReal : GenericStressReal := by
  intro c ε hc T hT S' hS F hF
  -- smooth tensor tests approximating `F`
  choose M hMtest hMl hMdist using fun n : ℕ =>
    Masked.tensorTestDense c hc F (1 / ((n : ℝ) + 1)) (by positivity)
  have hN : ∀ n, MemLp (gsrReFn (M n)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) := by
    intro n
    refine MemLp.of_le (hMl n) ?_ (Eventually.of_forall fun p => gsrRe_norm_le (M n p))
    exact (gsrReL.continuous.comp_aestronglyMeasurable (hMl n).aestronglyMeasurable)
  -- the real parts converge to `F`
  have hdist : ∀ n : ℕ, dist (F) ((hN n).toLp (gsrReFn (M n))) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    rw [dist_eq_norm]
    exact (gsr_dist_le c F hF (M n) (hMl n) (hN n)).trans (hMdist n).le
  have hlim : Tendsto (fun n : ℕ => (hN n).toLp (gsrReFn (M n))) atTop (nhds F) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]
    exact hdist n
  -- each `S'` of a real part is real
  have hmem : ∀ n : ℕ, (S' ((hN n).toLp (gsrReFn (M n)))) ∈
      {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC | Masked.IsRealH c g} := by
    intro n
    have hGmem := Masked.tensorTestDivMem c ε hc (gsrReFn (M n)) (gsrReFn_isTensorTest (hMtest n))
    have hS1 := hS (gsrReFn (M n)) (gsrReFn_isTensorTest (hMtest n))
      ((hN n).toLp (gsrReFn (M n)))
      (hGmem.toLp (fun p : UnforcedLeray.B0220.Profile =>
        ((p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (gsrReFn (M n)) p)))
      (hN n).coeFn_toLp (hGmem.coeFn_toLp)
    have hG : Masked.IsRealH c (hGmem.toLp (fun p : UnforcedLeray.B0220.Profile =>
        ((p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (gsrReFn (M n)) p))) := by
      filter_upwards [hGmem.coeFn_toLp] with p hp i
      rw [hp]
      exact Masked.smul_divEps_im ε (gsrReFn (M n)) (fun q j => gsrReFn_realValued (M n) q j) p i
    show Masked.IsRealH c (S' ((hN n).toLp (gsrReFn (M n))))
    rw [hS1]
    exact hT _ hG
  -- closedness passes the limit
  have hfinal : S' F ∈ {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC |
      Masked.IsRealH c g} :=
    (gsr_isClosed_isRealH c).mem_of_tendsto
      ((S'.continuous.tendsto F).comp hlim) (Eventually.of_forall hmem)
  exact hfinal

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
