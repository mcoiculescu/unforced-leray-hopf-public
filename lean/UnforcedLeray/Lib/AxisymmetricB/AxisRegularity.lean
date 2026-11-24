import UnforcedLeray.Lib.AxisymmetricB.Stream
import UnforcedLeray.Lib.Sobolev.Axis

/-!
# AX07: regularity across the axis


§5 Layer 3, target AX07 (`Axi/AxisRegularity.lean`) and bypass BP6; Wave 2 block 2J AXI1 of
`scoping/README.md`. Blueprint units served: B0200 (`eq:st18-t00202`, tex 3028–3051:
`F_R ∈ C_τ W^{1,p}(ℝ³)` for `2 ≤ p < ∞`, "weak derivatives across the axis"), B0282
(`background:eq:2.15`, tex 5197–5205), B0204 (`eq:st18-t00203`, tex 3058–3078:
`‖U_R‖_{W^{2,∞}} ≤ P`, the cylindrical term cancels on the linear radial term), the axis
argument of tex 2967–2990 (`u_r = r·smooth(r², z, t)`, `u_z = smooth(r², z, t)`), and B0687
(`background:eq:2.8`, tex 5855–5865: the datum is globally solenoidal although singular at `0`).

* `hasWeakSpatialDerivative_of_offAxis` (BP6): a field of class `C¹` off the axis with `f` and
  `∂ᵢf` in `L^p_loc(ℝ³)`, `p ≥ 2`, has its classical `∂ᵢf` as weak derivative on all of `ℝ³`
  (`Statement.HasWeakSpatialDerivative`). Proof: the cutoff `χ_m` of `Lib/Sobolev/Axis.lean`
  (`Sob.axisCut`), whose proof `HasWeakDeriv.of_bdd_off_axis` is the template here; the
  boundedness used there is replaced by Cauchy–Schwarz on the shrinking boxes:
  `(m+1) ∫_{box_m} |f| ≤ (m+1) |box_m|^{1/2} ‖f‖_{L²(box_m)} = 4√(2R) ‖f‖_{L²(box_m)} → 0`.
  This is the exact BP6 estimate `δ^{1−2/p} ‖f‖_{L^p(shell)}` at `p = 2`; `L^p_loc ⊂ L²_loc` for
  `p ≥ 2`.
* `isSolenoidal_of_point_singularity` (B0687): `C¹` off the origin, divergence free there and
  `|a(x)| ≤ C|x|⁻¹` give `IsSolenoidal a` (the drafted `PhaseSpace.isSolenoidal_of_punctured`).
* `contDiff_of_parity`, `parityField_eq_liftMer` (tex 2967–2990): `u = G(ρ², z) (y₀, y₁, 0) +
  H(ρ², z) e_z` is `C^k` on `ℝ³` when `G, H` are, and off the axis it is the lift of
  `(ρ G(ρ², z), H(ρ², z))`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Axi

theorem mem_offAxis_iff (x : Space) : x ∈ Sob.offAxis ↔ x ∉ axis := by
  simp only [Sob.offAxis, axis, mem_setOf_eq]
  tauto

theorem abs_le_of_mem_axisBox {a R : ℝ} {x : Space} (hx : x ∈ Sob.axisBox a R) :
    |x 0| ≤ a ∧ |x 1| ≤ a ∧ |x 2| ≤ R := by
  rw [Sob.axisBox, mem_preimage, mem_Icc] at hx
  obtain ⟨h1, h2⟩ := hx
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩
  · simpa using h1 0
  · simpa using h2 0
  · simpa using h1 1
  · simpa using h2 1
  · simpa using h1 2
  · simpa using h2 2

theorem norm_le_of_mem_axisBox {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) {x : Space}
    (hx : x ∈ Sob.axisBox a R) : ‖x‖ ≤ 2 * a + R := by
  obtain ⟨h0, h1, h2⟩ := abs_le_of_mem_axisBox hx
  have hsq : ‖x‖ ^ 2 ≤ (2 * a + R) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    have e0 : x 0 ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have e1 : x 1 ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have e2 : x 2 ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith [mul_nonneg ha hR, mul_nonneg ha ha]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- Cauchy–Schwarz on a set of finite measure: `(∫_s g)² ≤ |s| ∫_s g²` for `g ≥ 0`. -/
theorem sq_setIntegral_le {s : Set Space} (hs : volume s ≠ ⊤) {g : Space → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hg : MemLp g 2 (volume.restrict s)) :
    (∫ x in s, g x) ^ 2 ≤ volume.real s * ∫ x in s, g x ^ 2 := by
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs
  have h1 : MemLp (fun _ : Space => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]; exact memLp_const 1
  have h2 : MemLp g (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]; exact hg
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => zero_le_one) (ae_of_all _ hg0) h1 h2
  simp only [one_mul, integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.rpow_two, one_pow, mul_one] at H
  have hI0 : 0 ≤ ∫ x in s, g x := integral_nonneg hg0
  have hJ0 : 0 ≤ ∫ x in s, g x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hV0 : 0 ≤ volume.real s := measureReal_nonneg
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at H
  calc (∫ x in s, g x) ^ 2 ≤ (√(volume.real s) * √(∫ x in s, g x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hI0 H 2
    _ = volume.real s * ∫ x in s, g x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hV0, Real.sq_sqrt hJ0]

/-- **AX07 `hasWeakSpatialDerivative_of_offAxis`** (bypass BP6; B0200, tex 3028–3051; B0282,
tex 5197–5205). Let `f : ℝ³ → ℝ³` be `C¹` off the axis, with `f` and `∂ᵢf` (classical, off the
axis) in `L^p` of every compact set for some `p ≥ 2`. Then `∂ᵢf` is the weak `i`-th derivative
of `f` on all of `ℝ³`. -/
theorem hasWeakSpatialDerivative_of_offAxis {f : Space → Space} {p : ℝ≥0∞} (hp : 2 ≤ p)
    (hf : ContDiffOn ℝ 1 f axisᶜ)
    (hfp : ∀ K : Set Space, IsCompact K → MemLp f p (volume.restrict K)) (i : Fin 3)
    (hgp : ∀ K : Set Space, IsCompact K →
      MemLp (fun y => fderiv ℝ f y (coordinateVector i)) p (volume.restrict K)) :
    HasWeakSpatialDerivative i f (fun y => fderiv ℝ f y (coordinateVector i)) := by
  set v : Space := coordinateVector i with hv
  have hfin : ∀ K : Set Space, IsCompact K → IsFiniteMeasure (volume.restrict K) :=
    fun K hK => isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hf2 : ∀ K : Set Space, IsCompact K → MemLp f 2 (volume.restrict K) := fun K hK => by
    have := hfin K hK
    exact (hfp K hK).mono_exponent hp
  have hfl : LocallyIntegrable f volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    have := hfin K hK
    exact (hf2 K hK).integrable one_le_two
  have hgl : LocallyIntegrable (fun y => fderiv ℝ f y v) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    have := hfin K hK
    exact ((hgp K hK).mono_exponent hp).integrable one_le_two
  have hdiff : ∀ x, x ∉ axis → DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x hx).differentiableAt (isOpen_compl_axis.mem_nhds hx)
  have hmeas : AEStronglyMeasurable f volume := by
    have h1 : AEStronglyMeasurable f (volume.restrict axisᶜ) :=
      hf.continuousOn.aestronglyMeasurable isOpen_compl_axis.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := axisᶜ) ae_not_mem_axis] at h1
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact hfl.integrable_smul_left_of_hasCompactSupport
      ((hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφ.compact.fderiv_apply ℝ v)
  · exact hgl.integrable_smul_left_of_hasCompactSupport hφ.smooth.continuous hφ.compact
  have hφs : ContDiff ℝ ∞ φ := hφ.smooth
  have hφc : HasCompactSupport φ := hφ.compact
  have hcut := Sob.contDiff_axisCut
  set A : ℕ → Space := fun m => ∫ x, (fderiv ℝ φ x v * Sob.axisCut m x) • f x with hA_def
  set Bm : ℕ → Space := fun m => ∫ x, (φ x * fderiv ℝ (Sob.axisCut m) x v) • f x with hB_def
  set C : ℕ → Space := fun m => ∫ x, (φ x * Sob.axisCut m x) • fderiv ℝ f x v with hC_def
  -- integration by parts away from the axis
  have hid : ∀ m, C m = -(A m + Bm m) := by
    intro m
    have hsm : ContDiff ℝ ∞ (fun x => φ x * Sob.axisCut m x) := hφs.mul (hcut m)
    have hsc : HasCompactSupport (fun x => φ x * Sob.axisCut m x) := hφc.mul_right
    have hsupp : tsupport (fun x => φ x * Sob.axisCut m x) ⊆ axisᶜ := fun x hx =>
      (mem_offAxis_iff x).1 (Sob.tsupport_axisCut_subset m (tsupport_mul_subset_right hx))
    have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := volume) (f := fun x => φ x * Sob.axisCut m x) (g := f) (v := v)
      (hfl.integrable_smul_left_of_hasCompactSupport
        ((hsm.continuous_fderiv (by simp)).clm_apply continuous_const) (hsc.fderiv_apply ℝ v))
      (hgl.integrable_smul_left_of_hasCompactSupport hsm.continuous hsc)
      (hfl.integrable_smul_left_of_hasCompactSupport hsm.continuous hsc)
      (fun x _ => (hsm.differentiable (by simp)) x)
      (fun x hx => hdiff x (hsupp hx))
    have hprod : ∀ x, fderiv ℝ (fun y => φ y * Sob.axisCut m y) x v =
        fderiv ℝ φ x v * Sob.axisCut m x + φ x * fderiv ℝ (Sob.axisCut m) x v := by
      intro x
      have : fderiv ℝ (fun y => φ y * Sob.axisCut m y) x =
          φ x • fderiv ℝ (Sob.axisCut m) x + Sob.axisCut m x • fderiv ℝ φ x :=
        fderiv_mul ((hφs.differentiable (by simp)) x) (((hcut m).differentiable (by simp)) x)
      rw [this]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have i1 : Integrable (fun x => (fderiv ℝ φ x v * Sob.axisCut m x) • f x) volume :=
      hfl.integrable_smul_left_of_hasCompactSupport
        (((hφs.continuous_fderiv (by simp)).clm_apply continuous_const).mul (hcut m).continuous)
        ((hφc.fderiv_apply ℝ v).mul_right)
    have i2 : Integrable (fun x => (φ x * fderiv ℝ (Sob.axisCut m) x v) • f x) volume :=
      hfl.integrable_smul_left_of_hasCompactSupport
        (hφs.continuous.mul (((hcut m).continuous_fderiv (by simp)).clm_apply continuous_const))
        hφc.mul_right
    simp only [hC_def, hA_def, hB_def]
    rw [hibp, ← integral_add i1 i2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hprod, add_smul]
  -- the two dominated limits
  have hlimA : Tendsto A atTop (𝓝 (∫ x, fderiv ℝ φ x v • f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖fderiv ℝ φ x v • f x‖)
      (fun m => ((((hφs.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        (hcut m).continuous).aestronglyMeasurable).smul hmeas)
      (hfl.integrable_smul_left_of_hasCompactSupport
        ((hφs.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ v)).norm
      (fun m => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_smul, norm_smul, norm_mul]
      gcongr
      rw [Real.norm_of_nonneg (Sob.axisCut_nonneg m x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Sob.axisCut_le_one m x)
    · filter_upwards [ae_not_mem_axis] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Sob.eventually_axisCut_eq_one ((mem_offAxis_iff x).2 hx)] with m hm
      rw [hm, mul_one]
  have hlimC : Tendsto C atTop (𝓝 (∫ x, φ x • fderiv ℝ f x v)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖φ x • fderiv ℝ f x v‖)
      (fun m => ((hφs.mul (hcut m)).continuous.aestronglyMeasurable).smul
        hgl.aestronglyMeasurable)
      (hgl.integrable_smul_left_of_hasCompactSupport hφs.continuous hφc).norm
      (fun m => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_smul, norm_smul, norm_mul]
      gcongr
      rw [Real.norm_of_nonneg (Sob.axisCut_nonneg m x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Sob.axisCut_le_one m x)
    · filter_upwards [ae_not_mem_axis] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Sob.eventually_axisCut_eq_one ((mem_offAxis_iff x).2 hx)] with m hm
      rw [hm, mul_one]
  -- the commutator term tends to zero (Cauchy–Schwarz on the shrinking boxes)
  have hlimB : Tendsto Bm atTop (𝓝 0) := by
    obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_closedBall (0 : Space)).mp
      hφc.isCompact.isBounded
    set Rd := max R₀ 0 with hRd
    have hRd0 : 0 ≤ Rd := le_max_right _ _
    obtain ⟨Mφ, hMφ⟩ := hφs.continuous.bounded_above_of_compact_support hφc
    obtain ⟨B, hB0, hB⟩ := Sob.exists_bound_deriv_axisEta
    set L := 4 * B * (|v 0| + |v 1|) with hL
    have hL0 : 0 ≤ L := by positivity
    set K := max Mφ 0 * L with hK
    have hK0 : 0 ≤ K := by positivity
    set box : ℕ → Set Space := fun m => Sob.axisBox (2 / ((m : ℝ) + 1)) Rd with hbox
    set K0 : Set Space := closedBall (0 : Space) (4 + Rd) with hK0_def
    have hK0c : IsCompact K0 := isCompact_closedBall _ _
    have hbox_sub : ∀ m, box m ⊆ K0 := by
      intro m x hx
      have ha : 0 ≤ 2 / ((m : ℝ) + 1) := by positivity
      have ha2 : 2 / ((m : ℝ) + 1) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have := norm_le_of_mem_axisBox ha hRd0 hx
      rw [hK0_def, mem_closedBall, dist_zero_right]
      linarith
    have h2K0 := hf2 K0 hK0c
    have hfK0 : IntegrableOn f K0 volume := hfl.integrableOn_isCompact hK0c
    -- pointwise bound
    have hpt : ∀ m x, ‖(φ x * fderiv ℝ (Sob.axisCut m) x v) • f x‖ ≤
        (box m).indicator (fun x => K * ((m : ℝ) + 1) * ‖f x‖) x := by
      intro m x
      by_cases hφx : φ x = 0
      · simp only [hφx, zero_mul, zero_smul, norm_zero]
        exact indicator_nonneg (fun _ _ => by positivity) _
      by_cases hdx : fderiv ℝ (Sob.axisCut m) x v = 0
      · simp only [hdx, mul_zero, zero_smul, norm_zero]
        exact indicator_nonneg (fun _ _ => by positivity) _
      have hxs : x ∈ tsupport φ := subset_tsupport _ (Function.mem_support.mpr hφx)
      obtain ⟨h0, h1, hd⟩ := Sob.axisCut_deriv_bound hB0 hB m x v hdx
      have h2 : |x 2| ≤ Rd := by
        have hx := hR₀ hxs
        rw [mem_closedBall, dist_zero_right] at hx
        have := PiLp.norm_apply_le x 2
        rw [Real.norm_eq_abs] at this
        linarith [le_max_left R₀ 0]
      rw [indicator_of_mem (Sob.mem_axisBox h0 h1 h2), norm_smul, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have e1' : |φ x| ≤ Mφ := by simpa [Real.norm_eq_abs] using hMφ x
      have e1 : |φ x| ≤ max Mφ 0 := e1'.trans (le_max_left _ _)
      calc |φ x| * |fderiv ℝ (Sob.axisCut m) x v| * ‖f x‖
          ≤ max Mφ 0 * (L * ((m : ℝ) + 1)) * ‖f x‖ := by
            gcongr
        _ = K * ((m : ℝ) + 1) * ‖f x‖ := by rw [hK]; ring
    -- the box integrals
    have hbound1 : ∀ m : ℕ, ‖Bm m‖ ≤ K * ((m : ℝ) + 1) * ∫ x in box m, ‖f x‖ := by
      intro m
      have hint : Integrable ((box m).indicator (fun x => K * ((m : ℝ) + 1) * ‖f x‖)) volume :=
        (integrable_indicator_iff (Sob.measurableSet_axisBox _ _)).2
          (((hfK0.mono_set (hbox_sub m)).norm).const_mul _)
      calc ‖Bm m‖ ≤ ∫ x, (box m).indicator (fun x => K * ((m : ℝ) + 1) * ‖f x‖) x :=
            norm_integral_le_of_norm_le hint (Eventually.of_forall (hpt m))
        _ = K * ((m : ℝ) + 1) * ∫ x in box m, ‖f x‖ := by
            rw [integral_indicator (Sob.measurableSet_axisBox _ _), integral_const_mul]
    have hcs : ∀ m : ℕ, (∫ x in box m, ‖f x‖) ^ 2 ≤
        volume.real (box m) * ∫ x in box m, ‖f x‖ ^ 2 := by
      intro m
      refine sq_setIntegral_le (Sob.volume_axisBox_ne_top _ _) (fun x => norm_nonneg _) ?_
      exact (h2K0.norm).mono_measure (Measure.restrict_mono (hbox_sub m) le_rfl)
    set I : ℕ → ℝ := fun m => ∫ x in box m, ‖f x‖ ^ 2 with hI_def
    have hI0 : ∀ m, 0 ≤ I m := fun m => integral_nonneg fun x => sq_nonneg _
    have hbound2 : ∀ m : ℕ, ‖Bm m‖ ≤ √(K ^ 2 * (32 * Rd) * I m) := by
      intro m
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have ha : 0 ≤ 2 / ((m : ℝ) + 1) := by positivity
      refine Real.le_sqrt_of_sq_le ?_
      have hvol : volume.real (box m) = 32 * Rd / ((m : ℝ) + 1) ^ 2 := by
        rw [hbox, Sob.volume_axisBox ha hRd0]
        field_simp
        ring
      calc ‖Bm m‖ ^ 2 ≤ (K * ((m : ℝ) + 1) * ∫ x in box m, ‖f x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hbound1 m) 2
        _ = (K * ((m : ℝ) + 1)) ^ 2 * (∫ x in box m, ‖f x‖) ^ 2 := by ring
        _ ≤ (K * ((m : ℝ) + 1)) ^ 2 * (volume.real (box m) * I m) := by
            gcongr
            exact hcs m
        _ = K ^ 2 * (32 * Rd) * I m := by
            rw [hvol]
            field_simp
    -- `I m → 0` by dominated convergence
    have hIlim : Tendsto I atTop (𝓝 0) := by
      have hsq_meas : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) volume := hmeas.norm.pow 2
      have hdom : Integrable (K0.indicator fun x => ‖f x‖ ^ 2) volume :=
        (integrable_indicator_iff measurableSet_closedBall).2
          ((memLp_two_iff_integrable_sq_norm h2K0.1).1 h2K0)
      have hrew : I = fun m => ∫ x, (box m).indicator (fun x => ‖f x‖ ^ 2) x := by
        funext m
        rw [hI_def, integral_indicator (Sob.measurableSet_axisBox _ _)]
      rw [hrew, show (0 : ℝ) = ∫ _x : Space, (0 : ℝ) by simp]
      refine tendsto_integral_of_dominated_convergence (K0.indicator fun x => ‖f x‖ ^ 2)
        (fun m => hsq_meas.indicator (Sob.measurableSet_axisBox _ _)) hdom
        (fun m => Eventually.of_forall fun x => ?_) ?_
      · by_cases hx : x ∈ box m
        · rw [indicator_of_mem hx, indicator_of_mem (hbox_sub m hx), Real.norm_of_nonneg
            (sq_nonneg _)]
        · rw [indicator_of_notMem hx, norm_zero]
          exact indicator_nonneg (fun _ _ => sq_nonneg _) _
      · filter_upwards [ae_not_mem_axis] with x hx
        have hpos : 0 < max |x 0| |x 1| := by
          by_contra hle'
          have hle := not_lt.1 hle'
          have h0 : x 0 = 0 := abs_nonpos_iff.1 ((le_max_left _ _).trans hle)
          have h1 : x 1 = 0 := abs_nonpos_iff.1 ((le_max_right _ _).trans hle)
          exact hx ⟨h0, h1⟩
        have hdec : Tendsto (fun m : ℕ => 2 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
          have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
          rw [mul_zero] at h
          refine h.congr fun m => ?_
          ring
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [(tendsto_order.1 hdec).2 _ hpos] with m hm
        rw [indicator_of_notMem]
        intro hxm
        obtain ⟨h0, h1, -⟩ := abs_le_of_mem_axisBox hxm
        exact absurd (max_le h0 h1) (not_le.2 hm)
    have hsqrt : Tendsto (fun m => √(K ^ 2 * (32 * Rd) * I m)) atTop (𝓝 0) := by
      have h := (hIlim.const_mul (K ^ 2 * (32 * Rd))).sqrt
      rwa [mul_zero, Real.sqrt_zero] at h
    exact squeeze_zero_norm hbound2 hsqrt
  -- conclusion
  have hlim2 : Tendsto C atTop (𝓝 (-((∫ x, fderiv ℝ φ x v • f x) + 0))) := by
    have : C = fun m => -(A m + Bm m) := funext hid
    rw [this]
    exact (hlimA.add hlimB).neg
  have huniq := tendsto_nhds_unique hlimC hlim2
  rw [add_zero] at huniq
  show (∫ x, fderiv ℝ φ x v • f x) = -(∫ x, φ x • fderiv ℝ f x v)
  rw [huniq, neg_neg]

/-! ### Point singularities -/

/-- **AX07 `isSolenoidal_of_point_singularity`** (B0687, tex 5855–5865). A field that is `C¹`
and divergence free off the origin with `|a(x)| ≤ C|x|⁻¹` is distributionally solenoidal on
`ℝ³`; nothing is assumed at the origin. -/
theorem isSolenoidal_of_point_singularity {a : Space → Space} {C : ℝ}
    (ha : ContDiffOn ℝ 1 a {0}ᶜ) (hdiv : ∀ x ≠ (0 : Space), divergence a x = 0)
    (hbd : ∀ x ≠ (0 : Space), ‖a x‖ ≤ C * ‖x‖⁻¹) : IsSolenoidal a :=
  PhaseSpace.isSolenoidal_of_punctured ha hdiv hbd

/-! ### Parity form near the axis -/

/-- The field `G(ρ², z) (y₀, y₁, 0) + H(ρ², z) e_z` (tex 2967–2990: `u_r = r·smooth(r², z)`,
`u_z = smooth(r², z)`). -/
def parityField (G H : ℝ × ℝ → ℝ) (y : Space) : Space :=
  G (y 0 ^ 2 + y 1 ^ 2, y 2) • hor y + H (y 0 ^ 2 + y 1 ^ 2, y 2) • e3

/-- **AX07 `contDiff_of_parity`** (tex 2967–2990). If `G, H` are `C^k` on `ℝ²`, the field
`G(ρ², z)(y₀, y₁, 0) + H(ρ², z) e_z` is `C^k` on all of `ℝ³`, the axis included. -/
theorem contDiff_of_parity {k : WithTop ℕ∞} {G H : ℝ × ℝ → ℝ} (hG : ContDiff ℝ k G)
    (hH : ContDiff ℝ k H) : ContDiff ℝ k (parityField G H) := by
  have hm : ContDiff ℝ k (fun y : Space => (y 0 ^ 2 + y 1 ^ 2, y 2)) := by fun_prop
  exact ((hG.comp hm).smul contDiff_hor).add ((hH.comp hm).smul contDiff_const)

/-- Off the axis the parity field is the meridional lift of `(ρ G(ρ², z), H(ρ², z))`. -/
theorem parityField_eq_liftMer (G H : ℝ × ℝ → ℝ) {y : Space} (hy : y ∉ axis) :
    parityField G H y =
      liftMer (fun p => (p.1 * G (p.1 ^ 2, p.2)) • m0 + H (p.1 ^ 2, p.2) • m1) y := by
  rw [liftMer_eq_frameL, map_add, map_smul, map_smul, frameL_m0, frameL_m1, parityField,
    hor_eq_smul_eR hy, smul_smul]
  have h : (mer y).1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := ϱ_sq y
  simp only [h]
  rw [mul_comm]
  rfl

end UnforcedLeray.Axi
