import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Density.TestLift

/-!
# `PartIII-b:C/near/pins/5/3/2`: `SWRealDense` (smooth band tests are dense in `H_T`, source 1678)

Source `the November 2 reference manuscript`
1641-1646 (`tv4`), 1678 (completion from smooth tensors), 2676-2679 (the recentring).

Given `T ∈ H_T`, take the complex test `M₀` of `TensorTestDense` approximating `cplxT T` on the
recentred cell, and put `M := T - tvLift (tv4 T - M₀)` on the chart.  The `tv4`-components of `M`
are the real part of `M₀`, a smooth band test by `swTestLift`.  `M₀` is `c`-periodic in `q`, so
`M₀ ∘ cellPt = M₀`, and the recentring identity `CellPtHT` gives
`‖T - M‖_{H_T} ≤ K ‖tv4 T - M₀‖_{L²(ageμ)} = K c^{-1/2} ‖cplxT T - M₀‖`, with `K = ‖tvLift‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartIIIb.Concrete

/-- `tvLift` as a real-linear map. -/
def tvLiftLin : UnforcedLeray.Short.PartIIa.TensorVal →ₗ[ℝ] Ten3 where
  toFun := tvLift
  map_add' a b := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [tvLift, ten3Of]
  map_smul' r a := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [tvLift, ten3Of, Complex.smul_re, smul_eq_mul]

/-- `tvLift` as a continuous real-linear map. -/
def tvLiftL : UnforcedLeray.Short.PartIIa.TensorVal →L[ℝ] Ten3 :=
  LinearMap.toContinuousLinearMap tvLiftLin

theorem tvLiftL_apply (a : UnforcedLeray.Short.PartIIa.TensorVal) : tvLiftL a = tvLift a := rfl

/-- Real tensor dictionaries are fixed by the componentwise real part. -/
theorem testReL_tv4 (T : Ten3) : testReL (tv4 T) = tv4 T := by
  ext i
  fin_cases i <;> simp [testReL_apply, tv4]

/-- A `c`-periodic function is invariant under the recentring `cellPt`. -/
theorem qPer_cellPt {E : Type*} {c : ℝ} {M : UnforcedLeray.B0220.Profile → E}
    (hM : UnforcedLeray.B0220.QPeriodic c M) (p : UnforcedLeray.B0220.Profile) :
    M (cellPt c p) = M p := by
  obtain ⟨s, q, η⟩ := p
  show M (s, (if q < c / 2 then q else q - c), η) = M (s, q, η)
  by_cases hq : q < c / 2
  · rw [if_pos hq]
  · rw [if_neg hq]
    have h := hM (s, q - c, η)
    simp only [sub_add_cancel] at h
    exact h.symm

/-- The `L²(ageμ c (-1/2))` norm of `f` is the `L²(measureHT c)` norm of `f ∘ cellPt`, up to the
factor `c^{1/2}` (from `CellPtHT`). -/
theorem cell_eLpNorm {c : ℝ} (hc : 0 < c) (hH : Masked.CellPtHT c) {E : Type*}
    [NormedAddCommGroup E] (f : Chart → E) (hf : AEStronglyMeasurable f (ageμ c (-1 / 2))) :
    eLpNorm (fun p : UnforcedLeray.B0220.Profile => f (cellPt c p)) 2
        (UnforcedLeray.Short.PartIIa.measureHT c) =
      ENNReal.ofReal (Real.sqrt c) * eLpNorm f 2 (ageμ c (-1 / 2)) := by
  have hmeas : Measurable (cellPt c) := Masked.measurable_cellPt c
  have hf' : AEStronglyMeasurable f
      (Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c)) := by
    rw [hH]
    exact hf.smul_measure _
  have h1 := eLpNorm_map_measure (p := 2) hf' hmeas.aemeasurable
  rw [hH, eLpNorm_smul_measure_of_ne_top ENNReal.ofNat_ne_top, smul_eq_mul] at h1
  show eLpNorm (f ∘ cellPt c) 2 _ = _
  rw [← h1]
  congr 1
  rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hc.le (by norm_num)]
  norm_num

/-- The recentred test `M₀` is in `L²(ageμ c (-1/2))`. -/
theorem swM0_memLp {c : ℝ} (hc : 0 < c) (hH : Masked.CellPtHT c)
    {M0 : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal}
    (hM0t : UnforcedLeray.Short.PartIIa.IsTensorTest c M0)
    (hM0mem : MemLp M0 2 (UnforcedLeray.Short.PartIIa.measureHT c)) :
    MemLp M0 2 (ageμ c (-1 / 2)) := by
  have hmeas : Measurable M0 := hM0t.smooth.continuous.measurable
  have h := cell_eLpNorm hc hH M0 hmeas.aestronglyMeasurable
  have hfun : (fun p : UnforcedLeray.B0220.Profile => M0 (cellPt c p)) = M0 :=
    funext fun p => qPer_cellPt hM0t.periodic p
  rw [hfun] at h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have h2 : eLpNorm M0 2 (UnforcedLeray.Short.PartIIa.measureHT c) < ⊤ := hM0mem.2
  rw [h] at h2
  refine lt_top_iff_ne_top.2 fun hT => ?_
  rw [hT, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne'] at h2
  exact lt_irrefl _ h2

/-- The chart field `tv4 T - M₀`. -/
def swY (T : Chart → Ten3)
    (M0 : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal) :
    Chart → UnforcedLeray.Short.PartIIa.TensorVal :=
  fun x => tv4 (T x) - M0 x

/-- The approximant `M = T - tvLift (tv4 T - M₀)` on the chart. -/
def swM (T : Chart → Ten3)
    (M0 : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal) :
    Chart → Ten3 :=
  fun x => T x - tvLift (swY T M0 x)

/-- The `tv4`-components of `M` are the real part of `M₀`. -/
theorem swM_tv4 (T : Chart → Ten3)
    (M0 : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal) (x : Chart) :
    tv4 (swM T M0 x) = tv4 (tvLift (M0 x)) := by
  have hlin : tv4 (T x - tvLift (swY T M0 x)) = tv4 (T x) - tv4 (tvLift (swY T M0 x)) := by
    have h := map_sub Masked.tv4L (T x) (tvLift (swY T M0 x))
    simpa only [Masked.tv4L_apply] using h
  have hY : testReL (swY T M0 x) = tv4 (T x) - testReL (M0 x) := by
    unfold swY
    rw [map_sub testReL, testReL_tv4]
  unfold swM
  rw [hlin, tv4_tvLift_eq_testReL, tv4_tvLift_eq_testReL, hY]
  abel

/-- **`SWRealDense`** (source 1678): smooth band tests are dense in `H_T`. -/
theorem swRealDense : SWRealDense := by
  intro hyp c hc T η hη
  obtain ⟨-, -, hD, -, hHT, -, -⟩ := hyp
  have hH : Masked.CellPtHT c := hHT c hc
  have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hK0 : 0 ≤ ‖tvLiftL‖ := norm_nonneg _
  have hη' : 0 < η * Real.sqrt c / (‖tvLiftL‖ + 1) :=
    div_pos (mul_pos hη hs0) (by positivity)
  obtain ⟨M0, hM0t, hM0mem, hdist⟩ :=
    hD c hc (Masked.cplxT c hH T) (η * Real.sqrt c / (‖tvLiftL‖ + 1)) hη'
  have hM0c : MemLp M0 2 (ageμ c (-1 / 2)) := swM0_memLp hc hH hM0t hM0mem
  have hTf : MemLp (fun x => (T : Chart → Ten3) x) 2 (ageμ c (-1 / 2)) := Lp.memLp T
  have hTV : MemLp (fun x => tv4 ((T : Chart → Ten3) x)) 2 (ageμ c (-1 / 2)) := by
    have h := hTf.continuousLinearMap_comp Masked.tv4L
    simpa only [Masked.tv4L_apply] using h
  have hY : MemLp (swY T M0) 2 (ageμ c (-1 / 2)) := hTV.sub hM0c
  have hLY : MemLp (fun x => tvLift (swY T M0 x)) 2 (ageμ c (-1 / 2)) :=
    hY.continuousLinearMap_comp tvLiftL
  have hM : MemLp (swM T M0) 2 (ageμ c (-1 / 2)) := hTf.sub hLY
  refine ⟨swM T M0, hM, ?_, ?_⟩
  · have hfun : (fun x => tv4 (swM T M0 x)) = fun x => tv4 (tvLift (M0 x)) :=
      funext fun x => swM_tv4 T M0 x
    rw [hfun]
    exact swTestLift c M0 hM0t
  · -- the chart estimate
    have hcoe : ∀ᵐ x ∂ageμ c (-1 / 2),
        (T - hM.toLp (swM T M0)) x = tvLift (swY T M0 x) := by
      filter_upwards [Lp.coeFn_sub T (hM.toLp (swM T M0)), MemLp.coeFn_toLp hM] with x h1 h2
      rw [h1, Pi.sub_apply, h2]
      simp only [swM, sub_sub_cancel]
    have hnormLp : ‖T - hM.toLp (swM T M0)‖ =
        (eLpNorm (fun x => tvLift (swY T M0 x)) 2 (ageμ c (-1 / 2))).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
    have hmono : eLpNorm (fun x => tvLift (swY T M0 x)) 2 (ageμ c (-1 / 2)) ≤
        ENNReal.ofReal ‖tvLiftL‖ * eLpNorm (swY T M0) 2 (ageμ c (-1 / 2)) := by
      have h1 : eLpNorm (fun x => tvLift (swY T M0 x)) 2 (ageμ c (-1 / 2)) ≤
          eLpNorm (fun x => ‖tvLiftL‖ * ‖swY T M0 x‖) 2 (ageμ c (-1 / 2)) :=
        eLpNorm_mono_real fun x => tvLiftL.le_opNorm (swY T M0 x)
      have h2 := eLpNorm_const_smul (μ := ageμ c (-1 / 2)) (p := 2) ‖tvLiftL‖
        (fun x => ‖swY T M0 x‖)
      simp only [Pi.smul_def, smul_eq_mul] at h2
      rw [Real.enorm_eq_ofReal hK0, eLpNorm_norm] at h2
      exact h1.trans h2.le
    have hbound : (eLpNorm (fun x => tvLift (swY T M0 x)) 2 (ageμ c (-1 / 2))).toReal ≤
        ‖tvLiftL‖ * (eLpNorm (swY T M0) 2 (ageμ c (-1 / 2))).toReal := by
      have hne : ENNReal.ofReal ‖tvLiftL‖ * eLpNorm (swY T M0) 2 (ageμ c (-1 / 2)) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY.2.ne
      have h := ENNReal.toReal_mono hne hmono
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at h
    -- the recentring identity
    have hYc : (fun p : UnforcedLeray.B0220.Profile => swY T M0 (cellPt c p)) =ᵐ[
        UnforcedLeray.Short.PartIIa.measureHT c] ⇑(Masked.cplxT c hH T - hM0mem.toLp M0) := by
      filter_upwards [Masked.cplxT_ae c hH T, Lp.coeFn_sub (Masked.cplxT c hH T) (hM0mem.toLp M0),
        MemLp.coeFn_toLp hM0mem] with p h1 h2 h3
      rw [h2, Pi.sub_apply, h1, h3]
      simp only [swY, qPer_cellPt hM0t.periodic p]
    have hcell := cell_eLpNorm hc hH (swY T M0) hY.1
    have hD_eq : ‖Masked.cplxT c hH T - hM0mem.toLp M0‖ =
        Real.sqrt c * (eLpNorm (swY T M0) 2 (ageμ c (-1 / 2))).toReal := by
      rw [Lp.norm_def, ← eLpNorm_congr_ae hYc, hcell, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hs0.le]
    have hdist' := hdist
    rw [hD_eq, lt_div_iff₀ (by positivity)] at hdist'
    have hE0 : 0 ≤ (eLpNorm (swY T M0) 2 (ageμ c (-1 / 2))).toReal := ENNReal.toReal_nonneg
    have h8 : (eLpNorm (swY T M0) 2 (ageμ c (-1 / 2))).toReal * (‖tvLiftL‖ + 1) < η := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_le_mul_of_nonneg_left hcon hs0.le]
    calc ‖T - hM.toLp (swM T M0)‖
        = (eLpNorm (fun x => tvLift (swY T M0 x)) 2 (ageμ c (-1 / 2))).toReal := hnormLp
      _ ≤ ‖tvLiftL‖ * (eLpNorm (swY T M0) 2 (ageμ c (-1 / 2))).toReal := hbound
      _ < η := by nlinarith

end UnforcedLeray.Short.PartIIIb.NearInst
