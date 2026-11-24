import UnforcedLeray.Loc.L09CompactDatum.Datum

/-!
# L9 helper: `u_{0,h}` is solenoidal across zero

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 437–451, blueprint
units B0718, B0719). Line 451: "`u_{0,h}` is divergence free (also across `0`, since it
equals `u_dss` there)".

* `div_curl_eq_zero`: `div curl G = 0` at every point where `G` is smooth (symmetric second
  derivatives); so `div u_{0,h} = 0` pointwise off zero.
* `DSSField.isSolenoidal_of_eq_near`: a field `v`, smooth and pointwise divergence free off
  zero, integrable, and equal to `u_dss` on the punctured unit ball, is distributionally
  divergence free on `ℝ³`. Proof: with `ψ(x) = χ(2x)`, `v = ψ u_dss + w` off zero where `w` is
  globally smooth (it vanishes near zero). The solenoidality of `u_dss` across zero (the
  package field `udss_solenoidal`), tested against `ψφ`, gives
  `∫ ψ u_dss·∇φ = -∫ φ u_dss·∇ψ`; integration by parts for `w` gives
  `∫ w·∇φ = -∫ φ div w = ∫ φ u_dss·∇ψ`. The two cancel.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

/-! ## `div curl = 0` -/

theorem hasFDerivAt_curl {G : Space → Space} {x : Space}
    (hG : DifferentiableAt ℝ (fderiv ℝ G) x) :
    HasFDerivAt (curl G) (∑ j : Fin 3, (crossCLM (coordinateVector j)).comp
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector j)).comp
        (fderiv ℝ (fderiv ℝ G) x))) x := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin 3)), HasFDerivAt
      (fun y => crossProd (coordinateVector j) (fderiv ℝ G y (coordinateVector j)))
      ((crossCLM (coordinateVector j)).comp
        ((ContinuousLinearMap.apply ℝ Space (coordinateVector j)).comp
          (fderiv ℝ (fderiv ℝ G) x))) x := by
    intro j _
    have h1 := (ContinuousLinearMap.apply ℝ Space (coordinateVector j)).hasFDerivAt.comp x
      hG.hasFDerivAt
    have h2 := (crossCLM (coordinateVector j)).hasFDerivAt.comp x h1
    have hfun : (fun y => crossProd (coordinateVector j) (fderiv ℝ G y (coordinateVector j))) =
        ⇑(crossCLM (coordinateVector j)) ∘
          (⇑(ContinuousLinearMap.apply ℝ Space (coordinateVector j)) ∘ fderiv ℝ G) := by
      funext y
      simp
    rw [hfun]
    exact h2
  have hs := HasFDerivAt.sum h
  exact hs

/-- **`div curl G = 0`** where `G` is smooth. -/
theorem div_curl_eq_zero {G : Space → Space} {x : Space} (hG : ContDiffAt ℝ ∞ G x) :
    ∑ i : Fin 3, fderiv ℝ (curl G) x (coordinateVector i) i = 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ G x := hG.isSymmSndFDerivAt (by simp)
  rw [(hasFDerivAt_curl hD).fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.apply_apply, crossCLM_apply]
  exact sum_coord_sum_cross_symm
    (fun i j => fderiv ℝ (fderiv ℝ G) x (coordinateVector i) (coordinateVector j))
    (fun i j => hsymm _ _)

/-! ## The inner cutoff `ψ(x) = χ(2x)` -/

/-- `ψ(x) = χ(2x)`, equal to `1` on `|x| ≤ 1/2`. -/
def innerCutoff (x : Space) : ℝ := cutoff ((2 : ℝ) • x)

theorem innerCutoff_contDiff : ContDiff ℝ ∞ innerCutoff :=
  cutoff_contDiff.comp (contDiff_const_smul (2 : ℝ))

theorem innerCutoff_eventually_one {x : Space} (hx : ‖x‖ < 1 / 2) :
    innerCutoff =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  have hy' : ‖y‖ < 1 / 2 := hy
  show cutoff ((2 : ℝ) • y) = 1
  apply cutoff_eq_one
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

theorem innerCutoff_eq_one {x : Space} (hx : ‖x‖ < 1 / 2) : innerCutoff x = 1 :=
  (innerCutoff_eventually_one hx).self_of_nhds

theorem fderiv_innerCutoff_eq_zero {x : Space} (hx : ‖x‖ < 1 / 2) :
    fderiv ℝ innerCutoff x = 0 := by
  rw [(innerCutoff_eventually_one hx).fderiv_eq]
  simp

/-! ## The smooth remainder `w = v - ψ u` -/

/-- `w = v - ψ u` off zero, `0` near zero. -/
def remainder (v u : SpatialField) : SpatialField :=
  smoothDefect (1 / 2) (fun x => v x - innerCutoff x • u x)

variable {q : ℝ} {u v : SpatialField}

theorem remainder_vanish (hvnear : ∀ x : Space, x ≠ 0 → ‖x‖ < 1 → v x = u x) :
    ∀ x : Space, x ≠ 0 → ‖x‖ < 1 / 2 → v x - innerCutoff x • u x = 0 := by
  intro x hx hx2
  rw [hvnear x hx (by linarith), innerCutoff_eq_one hx2, one_smul, sub_self]

theorem remainder_eq (hvnear : ∀ x : Space, x ≠ 0 → ‖x‖ < 1 → v x = u x) {x : Space}
    (hx : x ≠ 0) : remainder v u x = v x - innerCutoff x • u x :=
  smoothDefect_eq (remainder_vanish hvnear) hx

namespace DSSField

theorem remainder_contDiff (hu : DSSField q u) (hvs : ContDiffOn ℝ ∞ v {0}ᶜ)
    (hvnear : ∀ x : Space, x ≠ 0 → ‖x‖ < 1 → v x = u x) : ContDiff ℝ ∞ (remainder v u) :=
  smoothDefect_contDiff (by norm_num) (remainder_vanish hvnear)
    (hvs.sub (innerCutoff_contDiff.contDiffOn.smul hu.smooth))

/-- `div w = -u·∇ψ` everywhere. -/
theorem remainder_div (hu : DSSField q u) (hvs : ContDiffOn ℝ ∞ v {0}ᶜ)
    (hvdiv : ∀ x : Space, x ≠ 0 → ∑ i : Fin 3, fderiv ℝ v x (coordinateVector i) i = 0)
    (hvnear : ∀ x : Space, x ≠ 0 → ‖x‖ < 1 → v x = u x) (x : Space) :
    ∑ i : Fin 3, fderiv ℝ (remainder v u) x (coordinateVector i) i =
      -∑ i : Fin 3, u x i * spatialTestDerivative i innerCutoff x := by
  by_cases hx : x = 0
  · have hx2 : ‖x‖ < 1 / 2 := by rw [hx, norm_zero]; norm_num
    have h1 : fderiv ℝ (remainder v u) x = 0 := by
      rw [remainder, (smoothDefect_eventually_zero hx2).fderiv_eq]
      simp
    have h2 : fderiv ℝ innerCutoff x = 0 := fderiv_innerCutoff_eq_zero hx2
    simp [h1, h2, spatialTestDerivative]
  · have hux : DifferentiableAt ℝ u x := (hu.hasFDerivAt hx).differentiableAt
    have hvx : DifferentiableAt ℝ v x :=
      (hvs.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
    have hψx : DifferentiableAt ℝ innerCutoff x := innerCutoff_contDiff.differentiable (by simp) x
    have hd : HasFDerivAt (fun y => v y - innerCutoff y • u y)
        (fderiv ℝ v x - (innerCutoff x • fderiv ℝ u x +
          (fderiv ℝ innerCutoff x).smulRight (u x))) x :=
      hvx.hasFDerivAt.sub (hψx.hasFDerivAt.smul hux.hasFDerivAt)
    have hfw : fderiv ℝ (remainder v u) x = fderiv ℝ v x - (innerCutoff x • fderiv ℝ u x +
        (fderiv ℝ innerCutoff x).smulRight (u x)) :=
      (hd.congr_of_eventuallyEq (smoothDefect_eventuallyEq (remainder_vanish hvnear) hx)).fderiv
    have hdivv := hvdiv x hx
    have hdivu := hu.div_eq_zero hx
    rw [Fin.sum_univ_three] at hdivv hdivu
    rw [hfw]
    simp only [Fin.sum_univ_three, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.sub_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, spatialTestDerivative]
    linear_combination hdivv - innerCutoff x * hdivu

/-- **Solenoidality across zero.** A field that is smooth and divergence free off zero,
integrable, and equal to `u_dss` on the punctured unit ball is distributionally divergence
free (line 451). -/
theorem isSolenoidal_of_eq_near (hu : DSSField q u) (hvs : ContDiffOn ℝ ∞ v {0}ᶜ)
    (hvdiv : ∀ x : Space, x ≠ 0 → ∑ i : Fin 3, fderiv ℝ v x (coordinateVector i) i = 0)
    (hvnear : ∀ x : Space, x ≠ 0 → ‖x‖ < 1 → v x = u x)
    (hvint : Integrable v volume) : IsSolenoidal v := by
  have hvi : ∀ φ : Space → ℝ, IsSpatialTest φ →
      Integrable (fun x => ∑ i : Fin 3, v x i * spatialTestDerivative i φ x) := by
    intro φ hφ
    refine integrable_finsetSum _ fun i _ => ?_
    obtain ⟨C, hC⟩ := (hφ.derivative i).smooth.continuous.bounded_above_of_compact_support
      (hφ.derivative i).compact
    exact ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).integrable_comp hvint).mul_bdd
      (hφ.derivative i).smooth.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  refine ⟨hvi, fun φ hφ => ?_⟩
  have hw := hu.remainder_contDiff hvs hvnear
  have hdivw := hu.remainder_div hvs hvdiv hvnear
  have hψs : ContDiff ℝ ∞ innerCutoff := innerCutoff_contDiff
  have hfd : Continuous (fderiv ℝ (remainder v u)) := hw.continuous_fderiv (by simp)
  have hDi : ∀ i : Fin 3,
      Continuous (fun x => fderiv ℝ (remainder v u) x (coordinateVector i) i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector i)).continuous.comp hfd)
  have hDw : Continuous
      (fun x => ∑ i : Fin 3, fderiv ℝ (remainder v u) x (coordinateVector i) i) :=
    continuous_finset_sum _ fun i _ => hDi i
  have hDwφ : Integrable (fun x =>
      (∑ i : Fin 3, fderiv ℝ (remainder v u) x (coordinateVector i) i) * φ x) :=
    (hDw.mul hφ.smooth.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left
  -- the remainder, by parts
  have hwi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => remainder v u z i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hw
  have hBint : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => remainder v u x i * spatialTestDerivative i φ x) := by
    intro i _
    exact ((hwi i).continuous.mul (hφ.derivative i).smooth.continuous).integrable_of_hasCompactSupport
      (hφ.derivative i).compact.mul_left
  have hDint : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => fderiv ℝ (remainder v u) x (coordinateVector i) i * φ x) := by
    intro i _
    exact ((hDi i).mul hφ.smooth.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left
  have hIBP : ∀ i : Fin 3, (∫ x, remainder v u x i * spatialTestDerivative i φ x) =
      -(∫ x, fderiv ℝ (remainder v u) x (coordinateVector i) i * φ x) := by
    intro i
    have h := PressureAnalysis.integral_partial_mul_test (hwi i) hφ i
    have hcongr : (fun x => spatialTestDerivative i (fun z => remainder v u z i) x * φ x) =
        fun x => fderiv ℝ (remainder v u) x (coordinateVector i) i * φ x := by
      funext x
      rw [spatialTestDerivative, DSSField.fderiv_coord (hw.differentiable (by simp) x)]
    rw [hcongr] at h
    rw [h, neg_neg]
  have hB : (∫ x, ∑ i : Fin 3, remainder v u x i * spatialTestDerivative i φ x) =
      -(∫ x, (∑ i : Fin 3, fderiv ℝ (remainder v u) x (coordinateVector i) i) * φ x) := by
    rw [integral_finsetSum _ hBint]
    simp_rw [hIBP]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hDint]
    simp_rw [Finset.sum_mul]
  have hBint' : Integrable
      (fun x => ∑ i : Fin 3, remainder v u x i * spatialTestDerivative i φ x) :=
    integrable_finsetSum _ hBint
  -- `ψ u_dss`, through the solenoidality of `u_dss` tested against `ψφ`
  have hT : IsSpatialTest (fun x => innerCutoff x * φ x) :=
    ⟨hψs.mul hφ.smooth, hφ.compact.mul_left⟩
  have hdT : ∀ (i : Fin 3) (x : Space),
      spatialTestDerivative i (fun x => innerCutoff x * φ x) x =
        innerCutoff x * spatialTestDerivative i φ x +
          φ x * spatialTestDerivative i innerCutoff x := by
    intro i x
    simp only [spatialTestDerivative]
    rw [fderiv_fun_mul (hψs.differentiable (by simp) x) (hφ.smooth.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsol := hu.solenoidal.identity _ hT
  have hsolint := hu.solenoidal.integrable _ hT
  have hAeq : (fun x => ∑ i : Fin 3, innerCutoff x * u x i * spatialTestDerivative i φ x) =
      fun x => (∑ i : Fin 3, u x i * spatialTestDerivative i (fun x => innerCutoff x * φ x) x) +
        (∑ i : Fin 3, fderiv ℝ (remainder v u) x (coordinateVector i) i) * φ x := by
    funext x
    rw [hdivw x]
    simp only [hdT, Fin.sum_univ_three]
    ring
  have hA : (∫ x, ∑ i : Fin 3, innerCutoff x * u x i * spatialTestDerivative i φ x) =
      ∫ x, (∑ i : Fin 3, fderiv ℝ (remainder v u) x (coordinateVector i) i) * φ x := by
    rw [hAeq, integral_add hsolint hDwφ, hsol, zero_add]
  have hAint : Integrable
      (fun x => ∑ i : Fin 3, innerCutoff x * u x i * spatialTestDerivative i φ x) := by
    rw [hAeq]
    exact hsolint.add hDwφ
  -- `v = ψ u_dss + w` off zero
  have hsplit : (fun x => ∑ i : Fin 3, v x i * spatialTestDerivative i φ x) =ᵐ[volume]
      fun x => (∑ i : Fin 3, innerCutoff x * u x i * spatialTestDerivative i φ x) +
        ∑ i : Fin 3, remainder v u x i * spatialTestDerivative i φ x := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with x hx
    have hx0 : x ≠ 0 := hx
    rw [remainder_eq hvnear hx0]
    simp only [Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [integral_congr_ae hsplit, integral_add hAint hBint', hA, hB, add_neg_cancel]

/-- `div u_{0,h} = 0` off zero. -/
theorem compactDatum_div (hu : DSSField q u) {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) {x : Space}
    (hx : x ≠ 0) :
    ∑ i : Fin 3, fderiv ℝ (compactDatum χ u) x (coordinateVector i) i = 0 :=
  div_curl_eq_zero ((hχ.contDiffOn.smul hu.potential_contDiffOn).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx))

/-- **`u_{0,h}` is solenoidal on `ℝ³`** (line 451). -/
theorem compactDatum_isSolenoidal (hu : DSSField q u) : IsSolenoidal (compactDatum cutoff u) :=
  hu.isSolenoidal_of_eq_near (hu.compactDatum_contDiffOn cutoff_contDiff)
    (fun _ hx => hu.compactDatum_div cutoff_contDiff hx)
    (fun _ hx hx1 => hu.compactDatum_eq_near hx hx1) hu.compactDatum_integrable

end DSSField

end UnforcedLeray.L09
