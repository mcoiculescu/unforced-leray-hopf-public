import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3.L1

/-!
# Lemma 3 (`MollSliceLocInt`): local integrability of the slice defect in the phase variable

Source of record: `the November 2 reference manuscript`, lines 1415-1424 and 2531.

For fixed `n`, `y`, `c` and `j`, the function `τ ↦ mollSliceDiff (ρ n) w g j y c τ` is the `c`-th
coordinate of `Moll D (rep w τ) y - Moll (ρ n) (rep g τ) y`, where `D = ∂_j (ρ n)` is continuous
with compact support (`mollFderivApply`).  Each slice mollification is bounded by
`‖K‖_{q'} ‖rep · τ‖_{q₀}` (Hölder), and `τ ↦ ‖rep w τ‖_{q₀}` is locally integrable: it is
`P`-periodic, lies in `L^{q₀}` on one period (`phaseμ`), hence is `L^1` on one period, and so
locally integrable on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (rep)

/-- The `q₀`-norm of the slice `rep w τ` is `‖w τ‖` on the phase circle, so its `q₀`-th power is
integrable over one period `Ioc 0 P`. -/
lemma mollSlice_window {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E) :
    ∫⁻ τ in Ioc (0 : ℝ) P,
      (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume) ^ UnforcedLeray.B0412.q0E.toReal < ⊤ := by
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := Fact.out
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hNW : ∀ τ : ℝ, eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume
      = ‖w (τ : AddCircle P)‖ₑ := by
    intro τ
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae (UnforcedLeray.Cons.C03.Concrete.rep_slice w τ)
  have hAC := UnforcedLeray.PhaseSpace.lintegral_Ioc_period (P := P)
    (fun τ : AddCircle P => ‖w τ‖ₑ ^ UnforcedLeray.B0412.q0E.toReal) 0 0
  simp only [zero_add] at hAC
  have hfin : ∫⁻ τ : AddCircle P, ‖w τ‖ₑ ^ UnforcedLeray.B0412.q0E.toReal < ⊤ := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
      UnforcedLeray.PhaseSpace.lintegral_enorm_rpow_Yq w hqtop]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg (enorm_ne_top))
  simp only [hNW]
  rw [hAC]
  exact hfin

/-- The window integral of `‖rep w τ‖_{q₀}` over one period is finite. -/
lemma mollSlice_lintegral_lt_top {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E) :
    ∫⁻ τ in Ioc (0 : ℝ) P, eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume < ⊤ := by
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := Fact.out
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hr1 : 1 ≤ UnforcedLeray.B0412.q0E.toReal := by
    have := ENNReal.toReal_mono hqtop hq1
    simpa using this
  have key : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ UnforcedLeray.B0412.q0E.toReal := by
    intro x
    by_cases hx : x ≤ 1
    · exact hx.trans le_self_add
    · have hx' : 1 < x := not_le.1 hx
      have h1 : x ^ (1 : ℝ) ≤ x ^ UnforcedLeray.B0412.q0E.toReal :=
        ENNReal.rpow_le_rpow_of_exponent_le hx'.le hr1
      rw [ENNReal.rpow_one] at h1
      exact h1.trans le_add_self
  have hwin := mollSlice_window w
  have h1 : ∫⁻ _ in Ioc (0 : ℝ) P, (1 : ℝ≥0∞) < ⊤ := by
    simp
  calc ∫⁻ τ in Ioc (0 : ℝ) P, eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume
      ≤ ∫⁻ τ in Ioc (0 : ℝ) P,
          (1 + eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume ^
            UnforcedLeray.B0412.q0E.toReal) :=
        lintegral_mono fun τ => key _
    _ = (∫⁻ _ in Ioc (0 : ℝ) P, (1 : ℝ≥0∞)) + ∫⁻ τ in Ioc (0 : ℝ) P,
          eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume ^
            UnforcedLeray.B0412.q0E.toReal := lintegral_add_left measurable_const _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1, hwin⟩

/-- Measurability of the slice `q₀`-norm in the phase variable. -/
lemma mollSlice_meas {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E) :
    Measurable (fun τ : ℝ => eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume) := by
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := Fact.out
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq1)
  have e : (fun τ : ℝ => eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume) =
      fun τ => (∫⁻ y, ‖rep w τ y‖ₑ ^ UnforcedLeray.B0412.q0E.toReal
        ∂(volume : Measure UnforcedLeray.Space)) ^ (1 / UnforcedLeray.B0412.q0E.toReal) := by
    funext τ
    exact eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop
  rw [e]
  exact ((Measurable.lintegral_prod_right'
    (f := fun x : ℝ × UnforcedLeray.Space => ‖rep w x.1 x.2‖ₑ ^ UnforcedLeray.B0412.q0E.toReal)
    ((UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep w).measurable.enorm.pow_const _)).pow_const
    _)

/-- Local integrability of `τ ↦ ‖rep w τ‖_{q₀}`: periodic, integrable over one period. -/
lemma mollSlice_locInt {P : ℝ} [hP : Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E) :
    LocallyIntegrable (fun τ : ℝ => (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume).toReal)
      volume := by
  have hP0 : 0 < P := hP.out
  have hNm := mollSlice_meas w
  have hNint := mollSlice_lintegral_lt_top w
  have hint0 : IntegrableOn (fun τ : ℝ => (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume).toReal)
      (Ioc (0 : ℝ) P) volume :=
    integrable_toReal_of_lintegral_ne_top hNm.aemeasurable hNint.ne
  have hiv0 : IntervalIntegrable
      (fun τ : ℝ => (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume).toReal) volume 0 P :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hP0.le).2 hint0
  have hper : Function.Periodic
      (fun τ : ℝ => (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume).toReal) P := by
    intro τ
    have e : rep w (τ + P) = rep w τ :=
      funext fun z => UnforcedLeray.Cons.C03.Concrete.rep_add_period w τ z
    simp only [e]
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hk.isBounded
  have hiv : IntervalIntegrable
      (fun τ : ℝ => (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume).toReal) volume
      (-|R|) |R| :=
    hper.intervalIntegrable₀ hP0.ne' hiv0 (-|R|) |R|
  have hsub : k ⊆ Icc (-|R|) |R| := by
    intro x hx
    have h1 : ‖x‖ ≤ R := hR x hx
    rw [Real.norm_eq_abs] at h1
    exact abs_le.1 (h1.trans (le_abs_self R))
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [abs_nonneg R])).1 hiv).mono_set
    hsub

/-- For a continuous compactly supported kernel `L`, the slice convolution `τ ↦ Moll L (rep w τ) y`
is strongly measurable and locally integrable. -/
lemma mollSlice_moll_locInt {P : ℝ} [Fact (0 < P)] (L : UnforcedLeray.Space → ℝ)
    (hL : Continuous L) (hLc : HasCompactSupport L) (w : Yq P UnforcedLeray.B0412.q0E)
    (y : UnforcedLeray.Space) :
    StronglyMeasurable (fun τ : ℝ => Moll L (rep w τ) y) ∧
    LocallyIntegrable (fun τ : ℝ => Moll L (rep w τ) y) volume := by
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := Fact.out
  have hqHC : (conjExp UnforcedLeray.B0412.q0E).HolderConjugate UnforcedLeray.B0412.q0E :=
    conjExp_holderConjugate
  have hLmem : MemLp L (conjExp UnforcedLeray.B0412.q0E) volume :=
    hL.memLp_of_hasCompactSupport hLc
  have hpt : ∀ τ : ℝ, ‖Moll L (rep w τ) y‖ ≤
      (eLpNorm L (conjExp UnforcedLeray.B0412.q0E) volume).toReal *
        (eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume).toReal := by
    intro τ
    have hA : eLpNorm L (conjExp UnforcedLeray.B0412.q0E) volume < ⊤ := hLmem.2
    have hB : eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume < ⊤ := (memLp_rep_slice w τ).2
    have h1 : ‖Moll L (rep w τ) y‖ₑ ≤ eLpNorm L (conjExp UnforcedLeray.B0412.q0E) volume *
        eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume :=
      (UnforcedLeray.Conv.enorm_convolution_le_convAbs volume L (rep w τ) y).trans
        (UnforcedLeray.Conv.convAbs_le_eLpNorm_mul_eLpNorm volume hLmem.1
          (memLp_rep_slice w τ).1 hqHC y)
    have h2 : ENNReal.ofReal ‖Moll L (rep w τ) y‖ ≤
        eLpNorm L (conjExp UnforcedLeray.B0412.q0E) volume *
          eLpNorm (rep w τ) UnforcedLeray.B0412.q0E volume :=
      (ofReal_norm _).trans_le h1
    exact ((ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hA.ne hB.ne)).1 h2).trans_eq
      ENNReal.toReal_mul
  have hmeas : StronglyMeasurable (fun τ : ℝ => Moll L (rep w τ) y) := by
    have hf : StronglyMeasurable (fun p : ℝ × UnforcedLeray.Space => L (y - p.2) • rep w p.1 p.2) :=
      (hL.comp (continuous_const.sub continuous_snd)).stronglyMeasurable.smul
        (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep w)
    exact hf.integral_prod_right'
  refine ⟨hmeas, ((mollSlice_locInt w).smul
    (eLpNorm L (conjExp UnforcedLeray.B0412.q0E) volume).toReal).mono
    hmeas.aestronglyMeasurable (ae_of_all _ fun τ => ?_)⟩
  exact (hpt τ).trans (le_of_eq
    (Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).symm)

theorem mollSliceLocInt : MollSliceLocInt := by
  intro ρ hρ P _ w g j n y c
  obtain ⟨hdiff, hcs, -, -, -⟩ := hρ n
  set K : UnforcedLeray.Space → ℝ := ρ n with hK
  let D : UnforcedLeray.Space → ℝ := fun x => fderiv ℝ K x (EuclideanSpace.single j 1)
  have hK1 : ContDiff ℝ 1 K := hdiff.of_le (by simp)
  have hq1 : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E := Fact.out
  have hDc : Continuous D :=
    (hdiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcs : HasCompactSupport D :=
    (hcs.fderiv ℝ).comp_left
      (g := fun L : UnforcedLeray.Space →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) (by simp)
  have hfd : ∀ τ : ℝ, fderiv ℝ (Moll K (rep w τ)) y (EuclideanSpace.single j 1)
      = Moll D (rep w τ) y := fun τ =>
    mollFderivApply K hK1 hcs (rep w τ) ((memLp_rep_slice w τ).locallyIntegrable hq1)
      y (EuclideanSpace.single j 1)
  obtain ⟨hAm, hAl⟩ := mollSlice_moll_locInt D hDc hDcs w y
  obtain ⟨hBm, hBl⟩ := mollSlice_moll_locInt K hdiff.continuous hcs g y
  have hcont : Continuous (fun v : UnforcedLeray.PhaseSpace.CVec3 => v c) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) c).comp continuous_id
  have hdm : StronglyMeasurable (fun τ : ℝ => Moll D (rep w τ) y - Moll K (rep g τ) y) :=
    hAm.sub hBm
  have hdl : LocallyIntegrable (fun τ : ℝ => Moll D (rep w τ) y - Moll K (rep g τ) y) volume :=
    hAl.sub hBl
  have hsm : AEStronglyMeasurable
      (fun τ : ℝ => (Moll D (rep w τ) y - Moll K (rep g τ) y) c) volume :=
    (hcont.comp_stronglyMeasurable hdm).aestronglyMeasurable
  have heq : mollSliceDiff K w g j y c =
      fun τ : ℝ => (Moll D (rep w τ) y - Moll K (rep g τ) y) c := by
    funext τ
    unfold mollSliceDiff
    rw [hfd τ]
  rw [heq]
  exact (locallyIntegrableOn_univ.1 (LocallyIntegrableOn.norm (locallyIntegrableOn_univ.2 hdl))).mono
    hsm (ae_of_all _ fun τ => by
    rw [norm_norm]
    exact PiLp.norm_apply_le _ c)

end UnforcedLeray.Short.PartIIIb.Concrete
