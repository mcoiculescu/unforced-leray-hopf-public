import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KerFGker
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KdGapInt

/-!
# `kdGapMeas` (`PartIII-b:C/rep/2/6/3/3/7`, source 3603-3626, 3800-3807, 4171-4200, 5223)

Measurability in `(h,z)` of `y`-derivatives of `kerF (Kd) (h,z)`. For `h > 0` the kernel
`kerF (Kd) (h,z) y = -(l/2) (sepPhi μ (l,z) y - sepPhi (μ+1) (l,z) y)` with `l = e^{-h/2}`
(`kerFGker`), so the `n`-th derivative is `-(l/2)` times a difference of `sepPhi`-derivatives.
Those are a.e. measurable on `sepRho` (`sepPhiMeasurable`), and transfer to `mHZ` along
`(h,z) ↦ (e^{-h/2}, z)` (`cv_mHZ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Transfer of a.e. equality from `sepRho` to `mHZ` (general codomain). -/
lemma kdm_ae_transfer {β : Type*} (f g : ℝ × Space → β) (hfg : f =ᵐ[sepRho] g) :
    ∀ᵐ p ∂mHZ, f (Real.exp (-p.1 / 2), p.2) = g (Real.exp (-p.1 / 2), p.2) := by
  obtain ⟨M, hsub, hMmeas, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfg)
  have hI : Measurable (M.indicator fun _ => (1 : ℝ≥0∞)) :=
    (measurable_const (a := (1 : ℝ≥0∞))).indicator hMmeas
  have h0 := cv_mHZ (M.indicator fun _ => (1 : ℝ≥0∞)) hI
  have hR : ∫⁻ q, M.indicator (fun _ => (1 : ℝ≥0∞)) q ∂sepRho = 0 := by
    rw [lintegral_indicator_const hMmeas, hM0, mul_zero]
  have hcm : Measurable (fun p : ℝ × Space => ENNReal.ofReal (Real.exp (-p.1 / 2) / 2)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (measurable_fst.neg.div_const 2)).div_const 2)
  have hmeasL : Measurable (fun p : ℝ × Space =>
      ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) *
        M.indicator (fun _ => (1 : ℝ≥0∞)) (Real.exp (-p.1 / 2), p.2)) :=
    hcm.mul (hI.comp measurable_expPhi)
  have hae := (lintegral_eq_zero_iff hmeasL).1 (h0.trans hR)
  filter_upwards [hae] with p hp
  have hc : ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnot : (Real.exp (-p.1 / 2), p.2) ∉ M := by
    intro hmem
    have h2 := (mul_eq_zero.1 hp).resolve_left hc
    rw [Set.indicator_of_mem hmem] at h2
    exact one_ne_zero h2
  by_contra hne
  exact hnot (hsub hne)

/-- `mHZ`-a.e. `h > 0`. -/
lemma kdm_ae_pos : ∀ᵐ p ∂mHZ, 0 < p.1 := by
  have h : mHZ {p : ℝ × Space | p.1 ∉ Ioi (0 : ℝ)} = 0 := by
    have : {p : ℝ × Space | p.1 ∉ Ioi (0 : ℝ)} = (Ioi (0 : ℝ))ᶜ ×ˢ (univ : Set Space) := by
      ext p; simp
    rw [this, mHZ, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioi.compl,
      Set.compl_inter_self, measure_empty, zero_mul]
  exact measure_eq_zero_iff_ae_notMem.mp h |> fun h' => by
    filter_upwards [h'] with p hp
    simpa using hp

/-- The `h`-to-`l` form of the kernel difference: for `h` with `l = e^{-h/2}`,
`kerF (Kd) (h,z) = -(l/2) (sepPhi μ (l,z) - sepPhi (μ+1) (l,z))` as functions of `y`. -/
lemma kdm_kerF_Kd (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (p : ℝ × Space) :
    kerF T τ i (Kd ν μ) p = (((-(Real.exp (-p.1 / 2) / 2) : ℝ)) : ℂ) •
      ((fun y => sepPhi ν (μ : ℂ) T τ i (Real.exp (-p.1 / 2), p.2) y) -
        fun y => sepPhi ν ((μ : ℂ) + 1) T τ i (Real.exp (-p.1 / 2), p.2) y) := by
  funext y
  have hsplit : kerF T τ i (Kd ν μ) p y =
      kerF T τ i (Gker ν (μ : ℂ)) p y - kerF T τ i (Gker ν ((μ : ℂ) + 1)) p y := by
    simp only [kerF, Kd, sub_mul, Finset.sum_sub_distrib]
  rw [hsplit]
  have h1 := kerFGker ν (μ : ℂ) T τ i p y
  have h2 := kerFGker ν ((μ : ℂ) + 1) T τ i p y
  rw [h1, h2]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  ring

/-- For `h > 0`, the `n`-th `y`-derivative of `kerF (Kd) (h,z)` is `-(l/2)` times the difference of
the `n`-th `y`-derivatives of `sepPhi`. -/
lemma kdm_iteratedFDeriv (ν μ : ℝ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (i : Fin 3) (n : ℕ) (hn : n ≤ 2) (p : ℝ × Space) (hp : 0 < p.1) (y : Space) :
    iteratedFDeriv ℝ n (kerF T τ i (Kd ν μ) p) y =
      (((-(Real.exp (-p.1 / 2) / 2) : ℝ)) : ℂ) •
        (iteratedFDeriv ℝ n (fun y => sepPhi ν (μ : ℂ) T τ i (Real.exp (-p.1 / 2), p.2) y) y -
          iteratedFDeriv ℝ n (fun y => sepPhi ν ((μ : ℂ) + 1) T τ i (Real.exp (-p.1 / 2), p.2) y) y) := by
  have hl : Real.exp (-p.1 / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hcA : ContDiff ℝ 2 (sepPhi ν (μ : ℂ) T τ i (Real.exp (-p.1 / 2), p.2)) :=
    sepPhi_contDiff heatLerayKSmooth ν (μ : ℂ) T τ i _ _ hν hl
  have hcB : ContDiff ℝ 2 (sepPhi ν ((μ : ℂ) + 1) T τ i (Real.exp (-p.1 / 2), p.2)) :=
    sepPhi_contDiff heatLerayKSmooth ν ((μ : ℂ) + 1) T τ i _ _ hν hl
  have hnA : ContDiffAt ℝ n (fun y => sepPhi ν (μ : ℂ) T τ i (Real.exp (-p.1 / 2), p.2) y) y :=
    (hcA.of_le (by exact_mod_cast hn)).contDiffAt
  have hnB : ContDiffAt ℝ n (fun y => sepPhi ν ((μ : ℂ) + 1) T τ i (Real.exp (-p.1 / 2), p.2) y) y :=
    (hcB.of_le (by exact_mod_cast hn)).contDiffAt
  have hAB : ContDiffAt ℝ n ((fun y => sepPhi ν (μ : ℂ) T τ i (Real.exp (-p.1 / 2), p.2) y) -
      (fun y => sepPhi ν ((μ : ℂ) + 1) T τ i (Real.exp (-p.1 / 2), p.2) y)) y := hnA.sub hnB
  rw [kdm_kerF_Kd ν μ T τ i p, iteratedFDeriv_const_smul_apply hAB,
    iteratedFDeriv_sub_apply hnA hnB]

/-- **(L7)** measurability of the `y`-derivatives in `(h,z)` (source 3603-3626, 5223). -/
theorem kdGapMeas : KdGapMeas := by
  intro ν μ rOut P T hd τ i n hn y
  obtain ⟨hν, _, _, _, hS, _⟩ := hd
  have hA : AEStronglyMeasurable (fun q => iteratedFDeriv ℝ n
      (sepPhi ν (μ : ℂ) T τ i q) y) sepRho :=
    sepPhiMeasurable ν (μ : ℂ) P rOut T hν hS τ i n hn y
  have hB : AEStronglyMeasurable (fun q => iteratedFDeriv ℝ n
      (sepPhi ν ((μ : ℂ) + 1) T τ i q) y) sepRho :=
    sepPhiMeasurable ν ((μ : ℂ) + 1) P rOut T hν hS τ i n hn y
  have hsc : AEStronglyMeasurable (fun q : ℝ × Space => (((-(q.1 / 2)) : ℝ) : ℂ)) sepRho :=
    (Continuous.aestronglyMeasurable (by fun_prop))
  have hΘ : AEStronglyMeasurable (fun q : ℝ × Space =>
      (((-(q.1 / 2)) : ℝ) : ℂ) •
        (iteratedFDeriv ℝ n (sepPhi ν (μ : ℂ) T τ i q) y -
          iteratedFDeriv ℝ n (sepPhi ν ((μ : ℂ) + 1) T τ i q) y)) sepRho :=
    hsc.smul (hA.sub hB)
  have hm : AEStronglyMeasurable (fun p : ℝ × Space => hΘ.mk _ (Real.exp (-p.1 / 2), p.2)) mHZ :=
    (hΘ.stronglyMeasurable_mk.comp_measurable measurable_expPhi).aestronglyMeasurable
  refine hm.congr ?_
  filter_upwards [kdm_ae_transfer _ (hΘ.mk _) hΘ.ae_eq_mk, kdm_ae_pos] with p hp1 hp2
  rw [← hp1, kdm_iteratedFDeriv ν μ hν T τ i n hn p hp2 y]

end UnforcedLeray.Short.PartIIIb.Concrete
