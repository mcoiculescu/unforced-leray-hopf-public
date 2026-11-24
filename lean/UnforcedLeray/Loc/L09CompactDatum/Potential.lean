import UnforcedLeray.Loc.L09CompactDatum.Background

/-!
# L9 helper: the homotopy potential `A_loc` and `curl A_loc = u_dss`

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 431–440, blueprint
units B0717, B0718). For a `DSSField q u`:

* `homotopyPotential_eq`: the DSS law rescales `[0, 1/q]` onto `[0, 1]`, so
  `A_loc(x) = -∫₀¹ r x × u(rx) dr = -c · x × V(x)` with `c = q/(q-1)` and
  `V(x) = ∫_{1/q}^1 s u(sx) ds` (`radialMean`). The integral defining `A_loc` converges
  absolutely (`|r x × u(rx)| ≤ ‖×‖ C`), so it is the manuscript's integral, not a junk value.
* `radialMean_contDiffOn`: `V` is smooth off zero (differentiation under the integral sign
  over the compact parameter range `[1/q, 1]`), with derivative `∫ s² Du(sx) ds`.
* `curl_homotopyPotential`: `curl A_loc = u` off zero (line 437–439). The identity
  `curl[s x × u(sx)] = -∂_s[s² u(sx)]` uses the pointwise `div u = 0`; integrating over
  `[1/q, 1]` and using the DSS law once more gives `c (1 - 1/q) u = u`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

variable {q : ℝ} {u : SpatialField}

/-- `V(x) = ∫_{1/q}^1 s u(sx) ds`. -/
def radialMean (q : ℝ) (u : SpatialField) (x : Space) : Space :=
  ∫ s in Ioc q⁻¹ 1, s • u (s • x)

/-- `c = q/(q-1)`, the sum `∑ₙ q^{-n}` of the DSS rescalings. -/
def dssConst (q : ℝ) : ℝ := q / (q - 1)

/-- The derivative of `V` at `x`: `∫_{1/q}^1 s² Du(sx) ds`. -/
def radialMeanDeriv (q : ℝ) (u : SpatialField) (x : Space) : Space →L[ℝ] Space :=
  ∫ s in Ioc q⁻¹ 1, (s * s) • fderiv ℝ u (s • x)

namespace DSSField

theorem inv_pos' (hu : DSSField q u) : 0 < q⁻¹ := inv_pos.mpr hu.pos

theorem inv_lt_one' (hu : DSSField q u) : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu.one_lt

theorem smul_ne_zero_of_pos {s : ℝ} (hs : 0 < s) {x : Space} (hx : x ≠ 0) : s • x ≠ 0 :=
  smul_ne_zero hs.ne' hx

theorem hasFDerivAt (hu : DSSField q u) {y : Space} (hy : y ≠ 0) :
    HasFDerivAt u (fderiv ℝ u y) y :=
  ((hu.smooth.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).differentiableAt
    (by simp)).hasFDerivAt

theorem continuousOn_fderiv (hu : DSSField q u) : ContinuousOn (fderiv ℝ u) {0}ᶜ :=
  hu.smooth.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by simp)

theorem continuousOn_comp_smul (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    ContinuousOn (fun s : ℝ => u (s • x)) (Ioi 0) :=
  hu.continuousOn.comp (continuous_id.smul continuous_const).continuousOn
    fun s hs => smul_ne_zero_of_pos hs hx

theorem continuousOn_fderiv_comp_smul (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    ContinuousOn (fun s : ℝ => fderiv ℝ u (s • x)) (Ioi 0) :=
  hu.continuousOn_fderiv.comp (continuous_id.smul continuous_const).continuousOn
    fun s hs => smul_ne_zero_of_pos hs hx

theorem Icc_subset_Ioi (hu : DSSField q u) : Icc q⁻¹ 1 ⊆ Ioi 0 :=
  fun _ hs => lt_of_lt_of_le hu.inv_pos' hs.1

theorem dssConst_mul (hu : DSSField q u) : dssConst q * (1 - q⁻¹) = 1 := by
  have hq0 : q ≠ 0 := hu.pos.ne'
  have h1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hu.one_lt)
  rw [dssConst, div_mul_eq_mul_div, mul_sub, mul_one, mul_inv_cancel₀ hq0, div_self h1]

/-! ### The DSS reduction of `A_loc` -/

/-- The homotopy integrand is interval integrable on `[0, b]`. -/
theorem homotopy_intervalIntegrable (hu : DSSField q u) (x : Space) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun r : ℝ => r • crossProd x (u (r • x))) volume 0 b := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  obtain ⟨C, hC⟩ := hu.bound
  have hcont : ContinuousOn (fun r : ℝ => r • crossProd x (u (r • x))) (Ioc 0 b) := by
    have h := (continuousOn_id (s := Ioc (0 : ℝ) b)).smul ((crossCLM x).continuous.comp_continuousOn
      ((hu.continuousOn_comp_smul hx).mono Ioc_subset_Ioi_self))
    refine h.congr fun r _ => ?_
    simp
  refine Integrable.mono' (integrableOn_const (C := ‖crossCLM‖ * C) measure_Ioc_lt_top.ne)
    (hcont.aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun r hr => ?_))
  have hr0 : 0 < r := hr.1
  rw [norm_smul, Real.norm_of_nonneg hr0.le]
  calc r * ‖crossProd x (u (r • x))‖ ≤ r * (‖crossCLM‖ * ‖x‖ * ‖u (r • x)‖) :=
        mul_le_mul_of_nonneg_left (norm_crossProd_le _ _) hr0.le
    _ = ‖crossCLM‖ * (‖u (r • x)‖ * ‖r • x‖) := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le]; ring
    _ ≤ ‖crossCLM‖ * C :=
        mul_le_mul_of_nonneg_left (hC _ (smul_ne_zero_of_pos hr0 hx)) (by positivity)

/-- **`A_loc = -c · x × V(x)`** (line 433), from the DSS law. -/
theorem homotopyPotential_eq (hu : DSSField q u) :
    homotopyPotential u = fun x => (-dssConst q) • crossProd x (radialMean q u x) := by
  funext x
  by_cases hx : x = 0
  · subst hx; simp [homotopyPotential]
  have hq0 : q ≠ 0 := hu.pos.ne'
  set f : ℝ → Space := fun r => r • crossProd x (u (r • x)) with hf
  have hhp : homotopyPotential u x = -∫ r in (0 : ℝ)..1, f r := rfl
  -- the rescaling `r ↦ r / q` leaves the integrand invariant
  have hself : ∀ s : ℝ, f (s / q) = f s := by
    intro s
    by_cases hs : s = 0
    · subst hs; simp [hf]
    have hsx : s • x ≠ 0 := smul_ne_zero hs hx
    simp only [hf]
    rw [show (s / q) • x = q⁻¹ • (s • x) by rw [smul_smul, div_eq_inv_mul],
      hu.dss_inv hsx, crossProd_smul_right, smul_smul, div_mul_cancel₀ s hq0]
  have hJ : (∫ r in (0 : ℝ)..1, f r) = q • ∫ r in (0 : ℝ)..q⁻¹, f r := by
    have h := intervalIntegral.integral_comp_div f (a := 0) (b := 1) hq0
    simp only [hself, zero_div, one_div] at h
    exact h
  have hi1 := hu.homotopy_intervalIntegrable x zero_le_one
  have hsub : q⁻¹ ∈ uIcc (0 : ℝ) 1 := mem_uIcc_of_le hu.inv_pos'.le hu.inv_lt_one'.le
  have hiA : IntervalIntegrable f volume 0 q⁻¹ :=
    hi1.mono_set (uIcc_subset_uIcc left_mem_uIcc hsub)
  have hiB : IntervalIntegrable f volume q⁻¹ 1 :=
    hi1.mono_set (uIcc_subset_uIcc hsub right_mem_uIcc)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hiA hiB
  -- the tail integral is `x × V(x)`
  have hVi : IntervalIntegrable (fun s : ℝ => s • u (s • x)) volume q⁻¹ 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hu.inv_lt_one'.le]
    exact continuousOn_id.smul ((hu.continuousOn_comp_smul hx).mono hu.Icc_subset_Ioi)
  have hI : (∫ r in q⁻¹..1, f r) = crossProd x (radialMean q u x) := by
    have h := (crossCLM x).intervalIntegral_comp_comm hVi
    simp only [crossCLM_apply, crossProd_smul_right] at h
    rw [radialMean, ← intervalIntegral.integral_of_le hu.inv_lt_one'.le, ← h]
  set J := ∫ r in (0 : ℝ)..1, f r
  set J₀ := ∫ r in (0 : ℝ)..q⁻¹, f r
  set I := ∫ r in q⁻¹..1, f r
  have hJ0 : J₀ = q⁻¹ • J := by rw [hJ, smul_smul, inv_mul_cancel₀ hq0, one_smul]
  have hIJ : I = (1 - q⁻¹) • J := by
    rw [sub_smul, one_smul, ← hJ0, ← hadd]; abel
  have hc : dssConst q * (1 - q⁻¹) = 1 := hu.dssConst_mul
  rw [hhp, ← hI, hIJ, smul_smul, neg_mul, hc, neg_smul, one_smul]

/-! ### Smoothness and derivative of `V` off zero -/

/-- The derivatives of `s • u(s • ·)`. -/
theorem iteratedFDeriv_radialIntegrand (n : ℕ) (s : ℝ) (x : Space) :
    iteratedFDeriv ℝ n (fun y => s • u (s • y)) x = (s * s ^ n) • iteratedFDeriv ℝ n u (s • x) :=
  Kernels.iteratedFDeriv_comp_smul n u s s x

theorem radialMean_hyps (hu : DSSField q u) :
    (∀ᵐ s ∂(volume.restrict (Ioc q⁻¹ 1)), ContDiffOn ℝ ∞ (fun y => s • u (s • y)) {0}ᶜ) ∧
    (∀ (n : ℕ), ∀ x ∈ ({0}ᶜ : Set Space), AEStronglyMeasurable
      (fun s => iteratedFDeriv ℝ n (fun y => s • u (s • y)) x) (volume.restrict (Ioc q⁻¹ 1))) ∧
    LocDominated (volume.restrict (Ioc q⁻¹ 1)) (fun s y => s • u (s • y)) {0}ᶜ := by
  have hIoc : Ioc q⁻¹ 1 ⊆ Ioi 0 := fun s hs => lt_trans hu.inv_pos' hs.1
  refine ⟨?_, ?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hIoc hs
    exact (hu.smooth.comp (contDiff_const_smul s).contDiffOn
      fun y hy => smul_ne_zero_of_pos hs0 hy).const_smul s
  · intro n x hx
    simp_rw [iteratedFDeriv_radialIntegrand]
    have hDn : ContinuousOn (iteratedFDeriv ℝ n u) {0}ᶜ :=
      ContinuousOn.continuousOn_iteratedFDeriv hu.smooth isOpen_compl_singleton
        (by exact_mod_cast le_top)
    have hc : ContinuousOn (fun s : ℝ => (s * s ^ n) • iteratedFDeriv ℝ n u (s • x)) (Ioc q⁻¹ 1) :=
      (continuousOn_id.mul (continuousOn_id.pow n)).smul (hDn.comp
        (continuous_id.smul continuous_const).continuousOn
        fun s hs => smul_ne_zero_of_pos (hIoc hs) hx)
    exact hc.aestronglyMeasurable measurableSet_Ioc
  · intro n x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set K : Set Space := {z | q⁻¹ * (‖x‖ / 2) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * ‖x‖ / 2} with hK
    have hKc : IsCompact K := by
      refine (isCompact_closedBall (0 : Space) (3 * ‖x‖ / 2)).of_isClosed_subset ?_ ?_
      · exact (isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const)
      · intro z hz; simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
    have hK0 : K ⊆ {0}ᶜ := by
      intro z hz h0
      rw [mem_singleton_iff] at h0
      have h1 := hz.1
      rw [h0, norm_zero] at h1
      have : 0 < q⁻¹ * (‖x‖ / 2) := mul_pos hu.inv_pos' (by positivity)
      linarith
    have hDn : ContinuousOn (iteratedFDeriv ℝ n u) {0}ᶜ :=
      ContinuousOn.continuousOn_iteratedFDeriv hu.smooth isOpen_compl_singleton
        (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hDn.mono hK0)
    refine ⟨Metric.closedBall x (‖x‖ / 2), Metric.closedBall_mem_nhds x (by positivity),
      fun _ => M, integrableOn_const measure_Ioc_lt_top.ne, ?_⟩
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs y hy => ?_)
    have hs0 : 0 < s := hIoc hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hy1 : ‖x‖ / 2 ≤ ‖y‖ := by
      have := norm_sub_norm_le x y
      rw [norm_sub_rev] at this
      linarith
    have hy2 : ‖y‖ ≤ 3 * ‖x‖ / 2 := by
      have := norm_le_insert' y x
      linarith
    have hsy : s • y ∈ K := by
      rw [hK, mem_setOf_eq, norm_smul, Real.norm_of_nonneg hs0.le]
      refine ⟨?_, ?_⟩
      · exact mul_le_mul hs.1.le hy1 (by positivity) hs0.le
      · calc s * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
          _ ≤ 3 * ‖x‖ / 2 := by rw [one_mul]; exact hy2
    rw [iteratedFDeriv_radialIntegrand, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hsy)
    have hs1 : s * s ^ n ≤ 1 := by
      calc s * s ^ n ≤ 1 * 1 := mul_le_mul hs.2 (pow_le_one₀ hs0.le hs.2) (by positivity)
            zero_le_one
        _ = 1 := one_mul 1
    calc s * s ^ n * ‖iteratedFDeriv ℝ n u (s • y)‖ ≤ 1 * M :=
          mul_le_mul hs1 (hM _ hsy) (norm_nonneg _) zero_le_one
      _ = M := one_mul M

/-- `V` is smooth off zero. -/
theorem radialMean_contDiffOn (hu : DSSField q u) :
    ContDiffOn ℝ ∞ (radialMean q u) {0}ᶜ := by
  obtain ⟨h1, h2, h3⟩ := hu.radialMean_hyps
  exact contDiffOn_integral isOpen_compl_singleton h1 h2 h3

theorem fderiv_radialIntegrand (hu : DSSField q u) {s : ℝ} {x : Space} (hsx : s • x ≠ 0) :
    fderiv ℝ (fun y => s • u (s • y)) x = (s * s) • fderiv ℝ u (s • x) := by
  have hd := hu.hasFDerivAt hsx
  have hl : HasFDerivAt (fun y : Space => s • y) (s • ContinuousLinearMap.id ℝ Space) x :=
    (hasFDerivAt_id x).const_smul s
  have h2 : HasFDerivAt (fun y => s • u (s • y)) ((s * s) • fderiv ℝ u (s • x)) x := by
    refine ((hd.comp x hl).const_smul s).congr_fderiv ?_
    ext1 v
    simp [smul_smul]
  exact h2.fderiv

/-- The derivative of `V` off zero. -/
theorem hasFDerivAt_radialMean (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (radialMean q u) (radialMeanDeriv q u x) x := by
  obtain ⟨h1, h2, h3⟩ := hu.radialMean_hyps
  have h := hasFDerivAt_integral_of_locDominated isOpen_compl_singleton h1 h2 h3
    (show x ∈ ({0}ᶜ : Set Space) from hx)
  have heq : (∫ s in Ioc q⁻¹ 1, fderiv ℝ (fun y => s • u (s • y)) x) = radialMeanDeriv q u x := by
    rw [radialMeanDeriv]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    exact hu.fderiv_radialIntegrand
      (smul_ne_zero_of_pos (lt_trans hu.inv_pos' hs.1) hx)
  rw [← heq]
  exact h

/-! ### `curl A_loc = u` off zero -/

theorem fderiv_homotopyPotential (hu : DSSField q u) {x : Space} (hx : x ≠ 0) (v : Space) :
    fderiv ℝ (homotopyPotential u) x v =
      (-dssConst q) • (crossProd x (radialMeanDeriv q u x v) + crossProd v (radialMean q u x)) := by
  have hV := hu.hasFDerivAt_radialMean hx
  have hB := crossCLM.hasFDerivAt_of_bilinear (hasFDerivAt_id x) hV
  have hA : HasFDerivAt (homotopyPotential u)
      ((-dssConst q) • (crossCLM.precompR Space x (radialMeanDeriv q u x) +
        crossCLM.precompL Space (ContinuousLinearMap.id ℝ Space) (radialMean q u x))) x := by
    have hfun : homotopyPotential u =
        fun y => (-dssConst q) • crossCLM y (radialMean q u y) := by
      rw [hu.homotopyPotential_eq]; funext y; rw [crossCLM_apply]
    rw [hfun]
    exact hB.const_smul (-dssConst q)
  rw [hA.fderiv]
  simp

theorem integrableOn_radial (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    IntegrableOn (fun s : ℝ => s • u (s • x)) (Ioc q⁻¹ 1) ∧
    IntegrableOn (fun s : ℝ => (s * s) • fderiv ℝ u (s • x)) (Ioc q⁻¹ 1) := by
  constructor
  · exact (continuousOn_id.smul ((hu.continuousOn_comp_smul hx).mono
      hu.Icc_subset_Ioi)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact ((continuousOn_id.mul continuousOn_id).smul ((hu.continuousOn_fderiv_comp_smul hx).mono
      hu.Icc_subset_Ioi)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- `∑ⱼ (DV(x) eⱼ)ⱼ = 0`: `V` is divergence free off zero. -/
theorem radialMeanDeriv_trace (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    ∑ j : Fin 3, radialMeanDeriv q u x (coordinateVector j) j = 0 := by
  set T : (Space →L[ℝ] Space) →L[ℝ] ℝ := ∑ j : Fin 3,
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space (coordinateVector j)) with hT
  have hTapp : ∀ M : Space →L[ℝ] Space, T M = ∑ j : Fin 3, M (coordinateVector j) j := by
    intro M; simp [hT]
  have hint := (hu.integrableOn_radial hx).2
  rw [← hTapp, radialMeanDeriv, ← T.integral_comp_comm hint]
  have hz : ∀ s ∈ Ioc q⁻¹ 1, T ((s * s) • fderiv ℝ u (s • x)) = 0 := by
    intro s hs
    rw [map_smul, hTapp, hu.div_eq_zero (smul_ne_zero_of_pos (lt_trans hu.inv_pos' hs.1) hx),
      smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioc hz, integral_zero]

/-- `∫_{1/q}^1 (2s u(sx) + s² Du(sx)x) ds = u(x) - q⁻¹ u(x)`. -/
theorem radial_ftc (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    (2 : ℝ) • radialMean q u x + radialMeanDeriv q u x x = u x - q⁻¹ • u x := by
  obtain ⟨hi1, hi2⟩ := hu.integrableOn_radial hx
  have hle : q⁻¹ ≤ 1 := hu.inv_lt_one'.le
  have e1 : (2 : ℝ) • radialMean q u x = ∫ s in Ioc q⁻¹ 1, (2 : ℝ) • (s • u (s • x)) := by
    rw [radialMean, integral_smul]
  have e2 : radialMeanDeriv q u x x = ∫ s in Ioc q⁻¹ 1, ((s * s) • fderiv ℝ u (s • x)) x := by
    rw [radialMeanDeriv, ContinuousLinearMap.integral_apply hi2]
  have hi1' : IntegrableOn (fun s : ℝ => (2 : ℝ) • (s • u (s • x))) (Ioc q⁻¹ 1) :=
    hi1.smul (2 : ℝ)
  rw [e1, e2, ← integral_add hi1' (hi2.apply_continuousLinearMap x)]
  set h' : ℝ → Space := fun s => (2 * s) • u (s • x) + (s * s) • fderiv ℝ u (s • x) x with hh'
  have hcongr : ∀ s ∈ Ioc q⁻¹ 1, (2 : ℝ) • (s • u (s • x)) + ((s * s) • fderiv ℝ u (s • x)) x =
      h' s := by
    intro s _
    simp [hh', smul_smul]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, ← intervalIntegral.integral_of_le hle]
  have hderiv : ∀ s ∈ uIcc q⁻¹ 1, HasDerivAt (fun s : ℝ => (s * s) • u (s • x)) (h' s) s := by
    intro s hs
    rw [uIcc_of_le hle] at hs
    have hs0 : 0 < s := hu.Icc_subset_Ioi hs
    have hd := hu.hasFDerivAt (smul_ne_zero_of_pos hs0 hx)
    have hl : HasDerivAt (fun s : ℝ => s • x) x s := by
      simpa using (hasDerivAt_id s).smul_const x
    have hcomp : HasDerivAt (fun s : ℝ => u (s • x)) (fderiv ℝ u (s • x) x) s :=
      hd.comp_hasDerivAt s hl
    have hsq : HasDerivAt (fun s : ℝ => s * s) (1 * s + s * 1) s :=
      (hasDerivAt_id s).mul (hasDerivAt_id s)
    refine (hsq.smul hcomp).congr_deriv ?_
    simp only [hh']
    rw [show (1 * s + s * 1) = 2 * s by ring]
    abel
  have hcont : ContinuousOn h' (uIcc q⁻¹ 1) := by
    rw [uIcc_of_le hle]
    refine ((continuousOn_const.mul continuousOn_id).smul
      ((hu.continuousOn_comp_smul hx).mono hu.Icc_subset_Ioi)).add
      ((continuousOn_id.mul continuousOn_id).smul ?_)
    exact (ContinuousLinearMap.apply ℝ Space x).continuous.comp_continuousOn
      ((hu.continuousOn_fderiv_comp_smul hx).mono hu.Icc_subset_Ioi)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [one_mul, one_smul]
  rw [hu.dss_inv hx, smul_smul, show q⁻¹ * q⁻¹ * q = q⁻¹ by rw [mul_assoc, inv_mul_cancel₀ hu.pos.ne', mul_one]]

/-- **`curl A_loc = u_dss` off zero** (lines 437–439). -/
theorem curl_homotopyPotential (hu : DSSField q u) {x : Space} (hx : x ≠ 0) :
    curl (homotopyPotential u) x = u x := by
  have hlin : ∑ j : Fin 3, x j • radialMeanDeriv q u x (coordinateVector j) =
      radialMeanDeriv q u x x := by
    simp_rw [← map_smul]
    rw [← map_sum, sum_coord_smul_basis]
  have hc : dssConst q * (1 - q⁻¹) = 1 := hu.dssConst_mul
  unfold curl
  simp_rw [hu.fderiv_homotopyPotential hx, crossProd_smul_right, crossProd_add_right]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, sum_cross_cross_family, sum_cross_cross_basis,
    hu.radialMeanDeriv_trace hx, hlin, zero_smul, zero_sub]
  have hftc := hu.radial_ftc hx
  have : -radialMeanDeriv q u x x + (-2 : ℝ) • radialMean q u x =
      -((2 : ℝ) • radialMean q u x + radialMeanDeriv q u x x) := by
    rw [neg_add, neg_smul]; abel
  rw [this, hftc, smul_neg, neg_smul, neg_neg, sub_eq_add_neg, ← neg_smul, ← one_smul ℝ (u x),
    smul_smul, ← add_smul, smul_smul]
  rw [show dssConst q * (1 + -q⁻¹ * 1) = dssConst q * (1 - q⁻¹) by ring, hc, one_smul]

end DSSField

end UnforcedLeray.L09
