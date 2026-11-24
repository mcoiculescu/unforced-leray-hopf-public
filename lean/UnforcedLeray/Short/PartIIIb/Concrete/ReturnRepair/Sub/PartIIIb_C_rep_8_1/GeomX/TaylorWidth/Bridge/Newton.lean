import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1

/-!
# `PartIII-b:C/rep/8/1/1/1/3/2/3`: the Newton bridge `NewtonBridge`

Source `the November 2 reference manuscript`
lines 4776-4791 (`V_{μ,M}`, `W^mt_{μ,M}(y) = ε^2 V_{μ,M}(ε y)`), SP 3753-3757 (`V_{μ,0}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace TWBridge

open PhasePrim

theorem tensorNorm_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ IIIa.tensorNorm M := by
  unfold IIIa.tensorNorm
  exact Real.sqrt_nonneg _

theorem entry_abs_le_tensorNorm (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ IIIa.tensorNorm M := by
  have h := IIIa.t17m_entry_sq_le M j k
  rw [IIIa.t17m_tn_sq] at h
  unfold IIIa.tensorNorm
  exact Real.abs_le_sqrt h

theorem thinMoment_meanLift_eq (c : ℝ) (hc : 0 < c) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    IIIa.thinMoment c (IIIa.meanLift G) =
      ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
        ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2)) := by
  unfold IIIa.thinMoment IIIa.meanLift
  refine lintegral_congr fun w => ?_
  congr 1
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_assoc,
    mul_comm (ENNReal.ofReal _) (ENNReal.ofReal c), ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne']
  simp only [ENNReal.ofReal_one, one_mul]
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (tensorNorm_nonneg _)]

/-- Integrability of each entry of `meanSrc` on `(ℝ × ℝ) × ℝ` when `oldN1 ≠ ⊤`. -/
theorem meanSrc_integrable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) (hN1 : oldN1 Pl K L T ≠ ⊤) (j k : Fin 3) :
    Integrable (fun w : (ℝ × ℝ) × ℝ => meanSrc Pl K L T w.1 w.2 j k) volume := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hle := thinMoment_meanSrc_le Pl K L hC0 T
  have htop : ENNReal.ofReal Real.pi * oldN1 Pl K L T < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN1)
  have hfin : IIIa.thinMoment (cOf L.ν) (IIIa.meanLift (meanSrc Pl K L T)) < ⊤ :=
    lt_of_le_of_lt hle htop
  rw [thinMoment_meanLift_eq (cOf L.ν) hc] at hfin
  have hmeas_tn : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun a _ =>
      Finset.measurable_sum _ fun b _ => (meanSrc_measurable Pl K L T a b).pow_const 2)
  have hwm : Measurable fun w : (ℝ × ℝ) × ℝ =>
      (1 + |w.2|) * IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2) :=
    (measurable_const.add (continuous_abs.measurable.comp measurable_snd)).mul hmeas_tn
  have hwint : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      (1 + |w.2|) * IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2)) volume := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hcongr : ∀ w : (ℝ × ℝ) × ℝ,
        ‖(1 + |w.2|) * IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2)‖ₑ =
          ENNReal.ofReal (1 + |w.2|) * ENNReal.ofReal (IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2)) := by
      intro w
      rw [← ofReal_norm,
        Real.norm_of_nonneg (mul_nonneg (by positivity) (tensorNorm_nonneg _)),
        ENNReal.ofReal_mul (by positivity)]
    simp_rw [hcongr]
    exact hfin
  refine Integrable.mono' hwint (meanSrc_measurable Pl K L T j k).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |meanSrc Pl K L T w.1 w.2 j k| ≤ IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2) :=
    entry_abs_le_tensorNorm _ j k
  have h2 : IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2) ≤
      (1 + |w.2|) * IIIa.tensorNorm (meanSrc Pl K L T w.1 w.2) :=
    le_mul_of_one_le_left (tensorNorm_nonneg _) (by linarith [abs_nonneg w.2])
  exact h1.trans h2

/-- The kernel factor in `sepVmu0`. -/
def kerK0 (x : Space) (l : ℝ) (i j k : Fin 3) (a : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun x' => IIIa.heatLerayK0 i j x') (x - l • (!₂[a.1, a.2, 0] : Space))
    (coordinateVector k)

theorem kerK0_measurable (x : Space) (l : ℝ) (i j k : Fin 3) :
    Measurable (kerK0 x l i j k) := by
  unfold kerK0
  have hemb : Continuous fun a : ℝ × ℝ => (!₂[a.1, a.2, 0] : Space) := by
    change Continuous fun a : ℝ × ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm (embPlane a)
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp NewtonFam.embPlane_continuous
  have hu : Measurable fun a : ℝ × ℝ => x - l • (!₂[a.1, a.2, 0] : Space) :=
    measurable_const.sub (hemb.measurable.const_smul l)
  exact (ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).continuous.measurable.comp
    ((measurable_fderiv ℝ (fun x' => IIIa.heatLerayK0 i j x')).comp hu)

theorem ofLp_shift_eq (x : Space) (l : ℝ) (a : ℝ × ℝ) :
    WithLp.ofLp (x - l • (!₂[a.1, a.2, 0] : Space)) = WithLp.ofLp x - l • embPlane a := rfl

theorem shift_space_ne_zero {x : Space} {a : ℝ × ℝ} {l Rsq : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ha : a.1 ^ 2 + a.2 ^ 2 ≤ Rsq)
    (hx : Rsq < x 0 ^ 2 + x 1 ^ 2) :
    x - l • (!₂[a.1, a.2, 0] : Space) ≠ 0 := by
  intro h0
  have h1 : WithLp.ofLp x - l • embPlane a = 0 := by
    rw [← ofLp_shift_eq, h0]
    rfl
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (Rsq + (x 0 ^ 2 + x 1 ^ 2)) / 2 := ⟨_, rfl⟩
  have haP : a.1 ^ 2 + a.2 ^ 2 < P := by rw [hP]; linarith
  have hxP : P < (WithLp.ofLp x) 0 ^ 2 + (WithLp.ofLp x) 1 ^ 2 := by
    rw [hP]; linarith
  exact NewtonFam.kernel_arg_ne_zero (WithLp.ofLp x) a l P hl0 hl1 haP hxP h1

theorem kerK0_eq_newtonD3_of_le (hK : KernelDict) {x : Space} {a : ℝ × ℝ} {l Rsq : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ha : a.1 ^ 2 + a.2 ^ 2 ≤ Rsq)
    (hx : Rsq < x 0 ^ 2 + x 1 ^ 2) (i j k : Fin 3) :
    kerK0 x l i j k a = newtonD3 (WithLp.ofLp x - l • embPlane a) i j k := by
  unfold kerK0
  have hne := shift_space_ne_zero hl0 hl1 ha hx
  exact (hK _ hne i j k).1

theorem isCompact_disc (Rsq : ℝ) : IsCompact {a : ℝ × ℝ | a.1 ^ 2 + a.2 ^ 2 ≤ Rsq} := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) (1 + max Rsq 0))
    (isClosed_le (by fun_prop) continuous_const) (fun a ha => ?_)
  have haR : a.1 ^ 2 + a.2 ^ 2 ≤ max Rsq 0 := le_trans ha (le_max_left _ _)
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  simp only [Real.norm_eq_abs, max_le_iff]
  constructor <;> nlinarith [sq_abs a.1, sq_abs a.2, sq_nonneg (|a.1| - 1),
    sq_nonneg (|a.2| - 1), sq_nonneg a.1, sq_nonneg a.2]

theorem kerK0_bounded_on_disc (hK : KernelDict) {x : Space} {l Rsq : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hx : Rsq < x 0 ^ 2 + x 1 ^ 2) (i j k : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ × ℝ, a.1 ^ 2 + a.2 ^ 2 ≤ Rsq → ‖kerK0 x l i j k a‖ ≤ B := by
  set D := {a : ℝ × ℝ | a.1 ^ 2 + a.2 ^ 2 ≤ Rsq}
  have hcont : ContinuousOn (fun a : ℝ × ℝ => newtonD3 (WithLp.ofLp x - l • embPlane a) i j k) D := by
    have hφ : Continuous fun a : ℝ × ℝ => WithLp.ofLp x - l • embPlane a :=
      continuous_const.sub (NewtonFam.embPlane_continuous.const_smul l)
    refine (newtonD3_contDiffOn i j k).continuousOn.comp hφ.continuousOn (fun a ha => ?_)
    intro h0
    apply shift_space_ne_zero hl0 hl1 ha hx
    exact WithLp.ofLp_injective 2 h0
  obtain ⟨B, hB⟩ := (isCompact_disc Rsq).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun a ha => ?_⟩
  rw [kerK0_eq_newtonD3_of_le hK hl0 hl1 ha hx i j k]
  exact (hB a ha).trans (le_max_left _ _)

theorem kerK0_mul_meanSrc_integrable (hK : KernelDict) (Pl : PlanarData) (K : ReturnConsts)
    (L : ReturnLevel) (hC0 : 0 < K.C0) (T : LStr Pl K L) (hN1 : oldN1 Pl K L T ≠ ⊤)
    {x : Space} (hx : 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1)
    (i j k : Fin 3) :
    Integrable (fun w : (ℝ × ℝ) × ℝ => kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k)
      volume := by
  obtain ⟨B, hB0, hB⟩ := kerK0_bounded_on_disc hK hl.1.le hl.2.le hx i j k
  have hm := meanSrc_integrable Pl K L hC0 T hN1 j k
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ =>
      kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k :=
    ((kerK0_measurable x l i j k).comp measurable_fst).mul (meanSrc_measurable Pl K L T j k)
  refine Integrable.mono' (hm.norm.const_mul B) hmeas.aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul]
  by_cases hw : w.1.1 ^ 2 + w.1.2 ^ 2 ≤ 5 * L.ν / 6
  · exact mul_le_mul_of_nonneg_right (hB w.1 hw) (norm_nonneg _)
  · have hw' : 5 * L.ν / 6 < w.1.1 ^ 2 + w.1.2 ^ 2 := not_le.1 hw
    have hsupp : Real.sqrt (5 * L.ν / 6) < Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) :=
      Real.sqrt_lt_sqrt (by have := L.ν_pos; positivity) hw'
    rw [meanSrc_support Pl K L T w.1 w.2 hsupp]
    simp

/-- Symmetrised contraction with `newtonD3` equals the unsymmetrised contraction, because
`newtonD3` is symmetric in its last two indices where `sigmaM` is supported. -/
theorem sum_newtonD3_symm_sigmaM (hK : KernelDict) (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3)
    (hν : 0 < ν) (hχ : IsOutwardCutoff χo) {x : Space} (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (i : Fin 3) (a : ℝ × ℝ) :
    (∑ j : Fin 3, ∑ k : Fin 3,
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
        ((sigmaM c ν χo M a j k + sigmaM c ν χo M a k j) / 2)) =
    ∑ j : Fin 3, ∑ k : Fin 3,
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k * sigmaM c ν χo M a j k := by
  by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
  · have hne : x - l • (!₂[a.1, a.2, 0] : Space) ≠ 0 :=
      shift_space_ne_zero hl.1.le hl.2.le ha.le hx
    have hsym : ∀ j k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k =
          newtonD3 (WithLp.ofLp x - l • embPlane a) i k j :=
      fun j k => (hK _ hne i j k).2
    have h10 := hsym 1 0
    have h20 := hsym 2 0
    have h21 := hsym 2 1
    simp only [Fin.sum_univ_three]
    rw [h10, h20, h21]
    ring
  · have h0 : sigmaM c ν χo M a = 0 :=
      sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
    simp [h0]

/-- For each `l ∈ (0,1)`, the `(x', Y)`-integral in `sepVmu0` collapses to the `x'`-integral in
`newtonV` (real version). -/
theorem inner_integral_real_eq (hK : KernelDict) (hS : SigmaCollapse) (Pl : PlanarData)
    (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) (T : LStr Pl K L)
    (hAzi : ThinAziZero Pl K L T) (hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T))
    (hN1 : oldN1 Pl K L T ≠ ⊤) {x : Space} (hx : 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) =
    ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
        sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k := by
  have hint : ∀ j k : Fin 3, Integrable (fun w : (ℝ × ℝ) × ℝ =>
      kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) volume :=
    fun j k => kerK0_mul_meanSrc_integrable hK Pl K L hC0 T hN1 hx hl i j k
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  have hstep1 : ∀ j : Fin 3,
      (∫ w : (ℝ × ℝ) × ℝ, ∑ k : Fin 3, kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) =
      ∑ k : Fin 3, ∫ a : ℝ × ℝ,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2) := by
    intro j
    rw [integral_finsetSum _ (fun k _ => hint j k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hprod : (∫ w : (ℝ × ℝ) × ℝ, kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) =
        ∫ a : ℝ × ℝ, kerK0 x l i j k a * ∫ Y : ℝ, meanSrc Pl K L T a Y j k := by
      have hp := MeasureTheory.integral_prod
        (fun w : (ℝ × ℝ) × ℝ => kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k) (hint j k)
      refine hp.trans (integral_congr_ae (Eventually.of_forall fun a => ?_))
      exact integral_const_mul (kerK0 x l i j k a) (fun Y => meanSrc Pl K L T a Y j k)
    rw [hprod]
    refine integral_congr_ae ?_
    filter_upwards [hS Pl K L hC0 T hAzi hOTF hN1] with a ha
    rw [ha j k]
    by_cases haD : a.1 ^ 2 + a.2 ^ 2 ≤ 5 * L.ν / 6
    · rw [kerK0_eq_newtonD3_of_le hK hl.1.le hl.2.le haD hx i j k]
    · have haD' : 5 * L.ν / 6 < a.1 ^ 2 + a.2 ^ 2 := not_le.1 haD
      have h0 : sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a = 0 :=
        sigmaM_eq_zero_of_ge (cOf L.ν) L.ν K.χo (thinRep T) L.ν_pos K.hχo a haD'.le
      simp [h0]
  simp_rw [hstep1]
  have hint_sym : ∀ j k : Fin 3, Integrable (fun a : ℝ × ℝ =>
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
        ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2)) volume := by
    intro j k
    have h1 : Integrable (fun a : ℝ × ℝ =>
        ∫ Y : ℝ, kerK0 x l i j k a * meanSrc Pl K L T a Y j k) volume :=
      (hint j k).integral_prod_left
    refine h1.congr ?_
    filter_upwards [hS Pl K L hC0 T hAzi hOTF hN1] with a ha
    rw [integral_const_mul, ha j k]
    by_cases haD : a.1 ^ 2 + a.2 ^ 2 ≤ 5 * L.ν / 6
    · rw [kerK0_eq_newtonD3_of_le hK hl.1.le hl.2.le haD hx i j k]
    · have haD' : 5 * L.ν / 6 < a.1 ^ 2 + a.2 ^ 2 := not_le.1 haD
      have h0 : sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a = 0 :=
        sigmaM_eq_zero_of_ge (cOf L.ν) L.ν K.χo (thinRep T) L.ν_pos K.hχo a haD'.le
      simp [h0]
  have hsum_int : (∑ j : Fin 3, ∑ k : Fin 3, ∫ a : ℝ × ℝ,
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
        ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2)) =
    ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
        ((sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k +
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a k j) / 2) := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint_sym j k))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint_sym j k)]
  rw [hsum_int]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact sum_newtonD3_symm_sigmaM hK (cOf L.ν) L.ν K.χo (thinRep T) L.ν_pos K.hχo hx hl i a

theorem inner_integral_eq (hK : KernelDict) (hS : SigmaCollapse) (Pl : PlanarData)
    (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) (T : LStr Pl K L)
    (hAzi : ThinAziZero Pl K L T) (hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T))
    (hN1 : oldN1 Pl K L T ≠ ⊤) {x : Space} (hx : 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ)) =
    ((∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
        sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ) := by
  have hcast : (fun w : (ℝ × ℝ) × ℝ => ∑ j : Fin 3, ∑ k : Fin 3,
      ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ)) =
    fun w : (ℝ × ℝ) × ℝ =>
      ((∑ j : Fin 3, ∑ k : Fin 3, kerK0 x l i j k w.1 * meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ) := by
    funext w
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hcast, ← inner_integral_real_eq hK hS Pl K L hC0 T hAzi hOTF hN1 hx hl i]
  exact integral_ofReal

/-- Pointwise identification `sepVmu0 (μ' : ℂ) (meanSrc T) x = ↑(newtonV ... (ofLp x))`
on the region `{5ν/6 < x₀² + x₁²}`. -/
theorem sepVmu0_eq_newtonV (hK : KernelDict) (hS : SigmaCollapse) (Pl : PlanarData)
    (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) (T : LStr Pl K L)
    (hAzi : ThinAziZero Pl K L T) (hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T))
    (hN1 : oldN1 Pl K L T ≠ ⊤) (μ' : ℝ) {x : Space} (hx : 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2)
    (i : Fin 3) :
    IIIa.sepVmu0 (μ' : ℂ) (meanSrc Pl K L T) x i =
      (newtonV (cOf L.ν) L.ν μ' K.χo (thinRep T) (WithLp.ofLp x) i : ℂ) := by
  unfold IIIa.sepVmu0 newtonV
  have hcongr : EqOn
      (fun l : ℝ => (l : ℂ) ^ (2 * (μ' : ℂ) + 2) *
        ∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
          ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ))
      (fun l : ℝ => ((l ^ (2 * μ' + 2) *
        ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
          newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
            sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ))
      (Ioo (0 : ℝ) 1) := by
    intro l hl
    dsimp only
    rw [inner_integral_eq hK hS Pl K L hC0 T hAzi hOTF hN1 hx hl i]
    have hpow : (l : ℂ) ^ (2 * (μ' : ℂ) + 2) = ((l ^ (2 * μ' + 2) : ℝ) : ℂ) := by
      have hexp : (2 * (μ' : ℂ) + 2 : ℂ) = ((2 * μ' + 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hexp, Complex.ofReal_cpow hl.1.le]
    rw [hpow, ← Complex.ofReal_mul]
  change -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ' : ℂ) + 2) *
    ∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      ((kerK0 x l i j k w.1 : ℝ) : ℂ) * ((meanSrc Pl K L T w.1 w.2 j k : ℝ) : ℂ) = _
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hor : (∫ l in Ioc (0 : ℝ) 1, ((l ^ (2 * μ' + 2) *
      ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ)) =
    ((∫ l in Ioc (0 : ℝ) 1, l ^ (2 * μ' + 2) *
      ∫ a : ℝ × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
        newtonD3 (WithLp.ofLp x - l • embPlane a) i j k *
          sigmaM (cOf L.ν) L.ν K.χo (thinRep T) a j k : ℝ) : ℂ) :=
    integral_ofReal
  rw [hor]
  push_cast
  rfl

/-- Real-to-complex embedding `Space →L[ℝ] (Fin 3 → ℂ)`, right inverse to `reMap`. -/
def ofRealSp : Space →L[ℝ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

theorem reMap_comp_ofRealSp : reMap.comp ofRealSp = ContinuousLinearMap.id ℝ Space := by
  ext u i
  simp [reMap, ofRealSp]

/-- `newtonV` pulled back to `Space → Space` via `WithLp`. -/
def newtonVSp (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ' : ℝ)
    (T : LStr Pl K L) (x : Space) : Space :=
  WithLp.toLp 2 (newtonV (cOf L.ν) L.ν μ' K.χo (thinRep T) (WithLp.ofLp x))

theorem newtonVSp_differentiableAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    {μ' : ℝ} (hμ' : 0 < μ') (T : LStr Pl K L)
    (hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T)) {xo : Space}
    (hxo : 5 * L.ν / 6 < xo 0 ^ 2 + xo 1 ^ 2) :
    DifferentiableAt ℝ (newtonVSp Pl K L μ' T) xo := by
  have hsm := newtonVSmooth (cOf L.ν) L.ν μ' K.χo (thinRep T)
    (cOf_pos L.ν_pos) L.ν_pos hμ' K.hχo hOTF
  have hmem : WithLp.ofLp xo ∈ {x : Vec3 | 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2} := hxo
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (newtonV (cOf L.ν) L.ν μ' K.χo (thinRep T)) (WithLp.ofLp xo) :=
    hsm.contDiffAt ((isOpen_newtonRegion L.ν).mem_nhds hmem)
  have hd : DifferentiableAt ℝ (newtonV (cOf L.ν) L.ν μ' K.χo (thinRep T)) (WithLp.ofLp xo) :=
    hcd.differentiableAt (by simp)
  change DifferentiableAt ℝ
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm ∘
      newtonV (cOf L.ν) L.ν μ' K.χo (thinRep T) ∘
        (EuclideanSpace.equiv (Fin 3) ℝ)) xo
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt.comp xo
    (hd.comp xo (EuclideanSpace.equiv (Fin 3) ℝ).differentiableAt)

theorem reMap_comp_fderiv_sepVmu0 (hK : KernelDict) (hS : SigmaCollapse) (Pl : PlanarData)
    (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) (T : LStr Pl K L)
    (hAzi : ThinAziZero Pl K L T) (hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T))
    (hN1 : oldN1 Pl K L T ≠ ⊤) {μ' : ℝ} (hμ' : 0 < μ') {xo : Space}
    (hxo : 5 * L.ν / 6 < xo 0 ^ 2 + xo 1 ^ 2) :
    reMap.comp (fderiv ℝ (IIIa.sepVmu0 (μ' : ℂ) (meanSrc Pl K L T)) xo) =
      fderiv ℝ (newtonVSp Pl K L μ' T) xo := by
  have hopen : IsOpen {x : Space | 5 * L.ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have hev : IIIa.sepVmu0 (μ' : ℂ) (meanSrc Pl K L T) =ᶠ[𝓝 xo]
      fun x => ofRealSp (newtonVSp Pl K L μ' T x) := by
    filter_upwards [hopen.mem_nhds hxo] with x hx
    ext i
    exact sepVmu0_eq_newtonV hK hS Pl K L hC0 T hAzi hOTF hN1 μ' hx i
  have hd : DifferentiableAt ℝ (newtonVSp Pl K L μ' T) xo :=
    newtonVSp_differentiableAt Pl K L hμ' T hOTF hxo
  have hcomp : fderiv ℝ (fun x => ofRealSp (newtonVSp Pl K L μ' T x)) xo =
      ofRealSp.comp (fderiv ℝ (newtonVSp Pl K L μ' T) xo) :=
    (ofRealSp.hasFDerivAt.comp xo hd.hasFDerivAt).fderiv
  rw [hev.fderiv_eq, hcomp, ← ContinuousLinearMap.comp_assoc, reMap_comp_ofRealSp,
    ContinuousLinearMap.id_comp]

end TWBridge

theorem newtonBridge (hK : TWBridge.KernelDict) (hS : TWBridge.SigmaCollapse) :
    TWBridge.NewtonBridge := by
  intro Pl K L μ hμ hC0 T hAzi hOTF hN1 τ xo hxo
  have hμ1 : 0 < μ + 1 := by linarith
  have h1 := TWBridge.reMap_comp_fderiv_sepVmu0 hK hS Pl K L hC0 T hAzi hOTF hN1 hμ hxo
  have h2 := TWBridge.reMap_comp_fderiv_sepVmu0 hK hS Pl K L hC0 T hAzi hOTF hN1 hμ1 hxo
  have hcast : ((μ + 1 : ℝ) : ℂ) = (μ : ℂ) + 1 := by push_cast; rfl
  rw [hcast] at h2
  rw [ContinuousLinearMap.comp_sub, h1, h2]
  have hd1 : DifferentiableAt ℝ (TWBridge.newtonVSp Pl K L μ T) xo :=
    TWBridge.newtonVSp_differentiableAt Pl K L hμ T hOTF hxo
  have hd2 : DifferentiableAt ℝ (TWBridge.newtonVSp Pl K L (μ + 1) T) xo :=
    TWBridge.newtonVSp_differentiableAt Pl K L hμ1 T hOTF hxo
  have hzMt : zMt Pl K L μ T τ = fun y : Space =>
      (L.ε ^ 2) • (TWBridge.newtonVSp Pl K L μ T (L.ε • y) -
        TWBridge.newtonVSp Pl K L (μ + 1) T (L.ε • y)) := by
    funext y
    ext i
    simp [zMt, youngW, TWBridge.newtonVSp, mul_sub]
  have hscale : L.ε • (L.ε⁻¹ • xo) = xo := by
    rw [smul_smul, mul_inv_cancel₀ L.ε_pos.ne', one_smul]
  have hsmul : HasFDerivAt (fun y : Space => L.ε • y)
      (L.ε • ContinuousLinearMap.id ℝ Space) (L.ε⁻¹ • xo) :=
    (ContinuousLinearMap.id ℝ Space).hasFDerivAt.const_smul L.ε
  have hsub : HasFDerivAt
      (fun x : Space => TWBridge.newtonVSp Pl K L μ T x - TWBridge.newtonVSp Pl K L (μ + 1) T x)
      (fderiv ℝ (TWBridge.newtonVSp Pl K L μ T) xo -
        fderiv ℝ (TWBridge.newtonVSp Pl K L (μ + 1) T) xo)
      (L.ε • (L.ε⁻¹ • xo)) := by
    rw [hscale]
    exact hd1.hasFDerivAt.sub hd2.hasFDerivAt
  have hchain := (hsub.comp (L.ε⁻¹ • xo) hsmul).const_smul (L.ε ^ 2)
  rw [hzMt]
  refine hchain.fderiv.trans ?_
  ext v i
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_smul, WithLp.ofLp_smul, WithLp.ofLp_sub,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
