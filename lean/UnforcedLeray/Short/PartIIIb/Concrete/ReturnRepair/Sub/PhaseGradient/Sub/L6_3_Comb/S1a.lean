import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `gkerIntegrable` (`PartIII-b:C/rep/2/6/3/1/1`)

Source of record: `the November 2 reference manuscript` 3603-3626 (`sep:kernel`,
`sep:resolvent`), 3631-3646.  With `l = e^{-h/2}` one has `Gker ν m h y z = e^{-(m+3/2)h} ∇K`,
and `l^{2m+2} · l = e^{-(m+3/2)h}`, so the `(h,z)`-integrand equals `-(l/2) · sepPhi ν m (l,z)`.
Domination: `sepGapPointwise` gives `|sepPhi| ≤ C · sepMajorant`, and the `h`-majorant
`(l/2) · sepMajorant (l,z)` is integrable on `(0,∞) × ℝ³` by the change of variables `dl = (l/2) dh`
applied to `sepGapMajorantIntegrable`. Measurability comes from `HeatLerayJointMeas`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The pointwise identity `∑_{jk} Gker · T = -(l/2) · sepPhi (l,z)` with `l = e^{-h/2}`. -/
theorem gkerSum_eq_sepPhi (ν : ℝ) (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (y z : Space) (h : ℝ) :
    ∑ j : Fin 3, ∑ k : Fin 3, Gker ν m h y z i j k * ((T (τ - h) z j k : ℝ) : ℂ) =
      -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * sepPhi ν m T τ i (Real.exp (-h / 2), z) y := by
  have hsq : Real.exp (-h / 2) ^ 2 = Real.exp (-h) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hτ : τ + 2 * Real.log (Real.exp (-h / 2)) = τ - h := by
    rw [Real.log_exp]
    ring
  have hpow : ((Real.exp (-h / 2) : ℝ) : ℂ) ^ (2 * m + 2) =
      Complex.exp ((2 * m + 2) * ((-h / 2 : ℝ) : ℂ)) :=
    cpow_exp_real_h _ _
  have hE : Complex.exp (-(m + 3 / 2) * (h : ℂ)) =
      ((Real.exp (-h / 2) : ℝ) : ℂ) ^ (2 * m + 2) * ((Real.exp (-h / 2) : ℝ) : ℂ) := by
    rw [hpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : ∀ (x : ℝ) (w S : ℂ), (x : ℂ) ^ w * (x : ℂ) * S =
      -((x / 2 : ℝ) : ℂ) * (-2 * (x : ℂ) ^ w * S) := by
    intro x w S
    push_cast
    ring
  have hR : ∑ j : Fin 3, ∑ k : Fin 3, Gker ν m h y z i j k * ((T (τ - h) z j k : ℝ) : ℂ) =
      Complex.exp (-(m + 3 / 2) * (h : ℂ)) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x)
          (y - Real.exp (-h / 2) • z) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
          ((T (τ - h) z j k : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Gker]
    ring
  rw [hR, hE]
  simp only [sepPhi, hsq, hτ]
  exact key _ _ _

/-- The `h`-majorant of the `Gker` integrand: `(l/2) · sepMajorant (l,z)`, `l = e^{-h/2}`. -/
def gkerMaj (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (p : ℝ × Space) : ℝ :=
  Real.exp (-p.1 / 2) / 2 * sepMajorant m T τ 0 (Real.exp (-p.1 / 2), p.2)

/-- The `l`-slice integral of the (norm of the) majorant. -/
def gkerN (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (l : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ‖sepMajorant m T τ 0 (l, z)‖ₑ

/-- The `k`-th directional derivative of `K_{ν(1-e^{-h})}^{ij}` at `y - e^{-h/2} z`, `p = (h,z)`,
set to `0` at `h = 0` (the form used to make the integrand measurable). -/
def gkerD (ν : ℝ) (i j k : Fin 3) (y : Space) (p : ℝ × Space) : ℝ :=
  (if 0 < ν * (1 - Real.exp (-p.1)) then
      iteratedFDeriv ℝ 1 (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-p.1))) i j x)
        (y - Real.exp (-p.1 / 2) • p.2)
    else 0) (fun _ => UnforcedLeray.coordinateVector k)

/-- Everywhere-defined version of the `(h,z)`-integrand `∑_{jk} Gker · T`. -/
def gkerG (ν : ℝ) (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (y : Space) (p : ℝ × Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    Complex.exp (-(m + 3 / 2) * (p.1 : ℂ)) * ((gkerD ν i j k y p : ℝ) : ℂ) *
      ((T (τ - p.1) p.2 j k : ℝ) : ℂ)

theorem gkerSepMajorant_measurable (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) :
    Measurable (sepMajorant m T τ 0) := by
  have hTij : ∀ i j : Fin 3, Measurable (fun p : ℝ × Space => T (τ + 2 * Real.log p.1) p.2 i j) :=
    fun i j => (hT.measurable i j).comp
      (by fun_prop : Measurable fun p : ℝ × Space => (τ + 2 * Real.log p.1, p.2))
  have hTN : Measurable (fun p : ℝ × Space => IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hTij i j).pow_const 2)
  unfold sepMajorant
  exact ((measurable_fst.pow_const _).mul
    ((measurable_const.add (measurable_fst.mul measurable_snd.norm)).pow_const _)).mul hTN

theorem gkerMaj_measurable (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ) :
    Measurable (gkerMaj m T τ) := by
  have hE : Measurable (fun p : ℝ × Space => (Real.exp (-p.1 / 2), p.2)) := by fun_prop
  unfold gkerMaj
  exact (by fun_prop : Measurable fun p : ℝ × Space => Real.exp (-p.1 / 2) / 2).mul
    ((gkerSepMajorant_measurable m P rOut T hT τ).comp hE)

theorem gkerMaj_lintegral_lt_top (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ)
    (hM : Integrable (sepMajorant m T τ 0) sepRho) :
    ∫⁻ p, ‖gkerMaj m T τ p‖ₑ ∂((volume.restrict (Ioi (0 : ℝ))).prod volume) < ⊤ := by
  have hMm : Measurable (sepMajorant m T τ 0) := gkerSepMajorant_measurable m P rOut T hT τ
  have hN : ∫⁻ l in Ioo (0 : ℝ) 1, gkerN m T τ l < ⊤ := by
    have hfin := hM.2
    unfold HasFiniteIntegral sepRho at hfin
    rw [lintegral_prod _ hMm.enorm.aemeasurable] at hfin
    exact hfin
  have himg : (fun h : ℝ => Real.exp (-h / 2)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext l
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.exp_lt_one_iff]
      have : (0 : ℝ) < h := hh
      linarith
    · rintro ⟨hl0, hl1⟩
      refine ⟨-2 * Real.log l, ?_, ?_⟩
      · have : Real.log l < 0 := Real.log_neg hl0 hl1
        show (0 : ℝ) < -2 * Real.log l
        linarith
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
    have := Real.exp_injective hab
    linarith
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun h : ℝ => Real.exp (-h / 2))
    (f' := fun x : ℝ => Real.exp (-x / 2) * (-1 / 2)) measurableSet_Ioi hderiv hinj
    (gkerN m T τ)
  rw [himg] at hcov
  have habs : ∀ x : ℝ, |Real.exp (-x / 2) * (-1 / 2)| = Real.exp (-x / 2) / 2 := by
    intro x
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_neg, abs_one, abs_two]
    ring
  have hmain : ∫⁻ p, ‖gkerMaj m T τ p‖ₑ ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x / 2) / 2) * gkerN m T τ (Real.exp (-x / 2)) := by
    rw [lintegral_prod _ (gkerMaj_measurable m P rOut T hT τ).enorm.aemeasurable]
    refine lintegral_congr fun h => ?_
    have hz : ∀ z : Space, ‖gkerMaj m T τ (h, z)‖ₑ =
        ENNReal.ofReal (Real.exp (-h / 2) / 2) * ‖sepMajorant m T τ 0 (Real.exp (-h / 2), z)‖ₑ := by
      intro z
      simp only [gkerMaj]
      rw [enorm_mul, Real.enorm_eq_ofReal (by positivity)]
    simp only [hz, gkerN]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hmain]
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x / 2) / 2) * gkerN m T τ (Real.exp (-x / 2))
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (|Real.exp (-x / 2) * (-1 / 2)|) *
          gkerN m T τ (Real.exp (-x / 2)) := by
        refine lintegral_congr fun x => ?_
        rw [habs x]
    _ = ∫⁻ x in Ioo (0 : ℝ) 1, gkerN m T τ x := hcov.symm
    _ < ⊤ := hN

theorem gkerG_measurable (ν : ℝ) (_hν : 0 < ν) (m : ℂ) (P rOut : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hT : IIIa.IsSepSource P rOut T) (τ : ℝ)
    (i : Fin 3) (y : Space) : Measurable (gkerG ν m T τ i y) := by
  have hJ : HeatLerayJointMeas :=
    heatLerayJointMeas_of (heatLerayScale_of heatGTailScale) heatLerayKSmooth
  have hQ : Measurable (fun p : ℝ × Space =>
      (ν * (1 - Real.exp (-p.1)), y - Real.exp (-p.1 / 2) • p.2)) := by
    fun_prop
  have hD : ∀ j k : Fin 3, Measurable (gkerD ν i j k y) := by
    intro j k
    have hS1 := (hJ i j 1 (by norm_num)).comp_measurable hQ
    have hc : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Space) ℝ =>
        A (fun _ => UnforcedLeray.coordinateVector k)) := continuous_eval_const _
    exact (hc.comp_stronglyMeasurable hS1).measurable
  unfold gkerG
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  refine ((Complex.continuous_exp.measurable.comp ?_).mul
    (Complex.measurable_ofReal.comp (hD j k))).mul (Complex.measurable_ofReal.comp ?_)
  · exact (by fun_prop : Continuous fun p : ℝ × Space => -(m + 3 / 2) * (p.1 : ℂ)).measurable
  · exact (hT.measurable j k).comp (by fun_prop : Measurable fun p : ℝ × Space => (τ - p.1, p.2))

theorem gkerIntegrable : GkerIntegrable := by
  intro ν m hν hm rOut P hr hP T hT hS τ y hy i
  have hae : ∀ᵐ p : ℝ × Space ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), 0 < p.1 := by
    have h1 : ∀ᵐ h ∂(volume.restrict (Ioi (0 : ℝ))), 0 < h :=
      (ae_restrict_mem measurableSet_Ioi).mono fun h hh => hh
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h1
  obtain ⟨ε, hε, C, hC0, hb⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν m rOut P T hν hm hr hP hT τ i y hy
  have hM : Integrable (sepMajorant m T τ 0) sepRho :=
    sepGapMajorantIntegrable m P rOut T hm hP hT hS τ 0 (by norm_num)
  have hgI : Integrable (gkerMaj m T τ) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    ⟨(gkerMaj_measurable m P rOut T hT τ).aestronglyMeasurable,
      gkerMaj_lintegral_lt_top m P rOut T hT τ hM⟩
  have hG : Measurable (gkerG ν m T τ i y) := gkerG_measurable ν hν m P rOut T hT τ i y
  have hFG : (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      Gker ν m p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)) =ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod volume]
      gkerG ν m T τ i y := by
    filter_upwards [hae] with p hp
    have hlt : Real.exp (-p.1) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hc : 0 < ν * (1 - Real.exp (-p.1)) := mul_pos hν (by linarith)
    simp only [gkerG, gkerD, Gker, if_pos hc, iteratedFDeriv_one_apply]
  refine Integrable.mono' (hgI.const_mul C) (hG.aestronglyMeasurable.congr hFG.symm) ?_
  filter_upwards [hae] with p hp
  have hl : Real.exp (-p.1 / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hn := hb y (Metric.mem_ball_self hε) _ hl p.2 0 (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero] at hn
  rw [gkerSum_eq_sepPhi ν m T τ i y p.2 p.1]
  have hc0 : 0 ≤ Real.exp (-p.1 / 2) / 2 := by positivity
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc0]
  calc Real.exp (-p.1 / 2) / 2 * ‖sepPhi ν m T τ i (Real.exp (-p.1 / 2), p.2) y‖
      ≤ Real.exp (-p.1 / 2) / 2 * (C * sepMajorant m T τ 0 (Real.exp (-p.1 / 2), p.2)) :=
        mul_le_mul_of_nonneg_left hn hc0
    _ = C * gkerMaj m T τ p := by
        simp only [gkerMaj]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
