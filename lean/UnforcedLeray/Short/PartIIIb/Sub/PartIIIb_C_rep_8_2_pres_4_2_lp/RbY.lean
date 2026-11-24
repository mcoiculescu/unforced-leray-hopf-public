import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.PhaseLrAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.PhaseLrMono
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.PhaseLrSlice
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Lib.Sobolev.Axis
import UnforcedLeray.Lib.AxisymmetricB.AxisRegularity
import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# `RbYBound` from the repair standing hypotheses (task `PartIII-b:C/rep/8/2/pres/4/2/lp/4`)

Source `the November 2 reference manuscript` 5134-5139 (repair bounds), 2697-2713.

Proof outline.  For a level with `rb τ = corr z` that is `C²` off the axis (`bgCorr_contDiffOn_offAxis`)
and jointly continuous (`corr_continuous`), the change density of `r_b` satisfies, off the axis,
`coefChgDens (rb τ) 0 y = ‖rb τ y‖ + Σ_j ‖∂_j rb τ y‖ + Σ_{j,l} ‖∂_j∂_l rb τ y‖`, where the
second and third sums are written as the joint-measurable pieces `pw1`, `pw2` (`measurable_fderiv_apply_offaxis`).
Minkowski (`phaseLr_add_le`) splits the phase norm into the energy term (`phaseLr_le_of_slice` with
`IsActualLevel.split.energy`), and the two derivative terms (`RepairDerivBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Calculus helpers -/

/-- A map `C²` on the open set `axisᶜ` is differentiable at off-axis points. -/
theorem rby_diff_of_contDiffOn {g : Space → Space} (h : ContDiffOn ℝ 2 g axisᶜ) {y : Space}
    (hy : y ∉ axis) : DifferentiableAt ℝ g y :=
  ((h.contDiffAt (isOpen_compl_axis.mem_nhds hy)).differentiableAt (by norm_num))

/-- The derivative of a `C²` map (off the axis) is differentiable there. -/
theorem rby_fderiv_diff_of_contDiffOn {g : Space → Space} (h : ContDiffOn ℝ 2 g axisᶜ) {y : Space}
    (hy : y ∉ axis) : DifferentiableAt ℝ (fun y' => fderiv ℝ g y') y :=
  (((h.contDiffAt (isOpen_compl_axis.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num))

/-- Derivative of `y ↦ c y e` for a differentiable CLM-valued `c`. -/
theorem rby_norm_fderiv_clm_apply_le {c : Space → (Space →L[ℝ] Space)} {y e v : Space}
    (hc : DifferentiableAt ℝ c y) :
    ‖fderiv ℝ (fun y' => c y' e) y v‖ ≤ ‖fderiv ℝ c y‖ * ‖v‖ * ‖e‖ := by
  have hu : DifferentiableAt ℝ (fun _ : Space => e) y := differentiableAt_const e
  have h : fderiv ℝ (fun y' => c y' e) y = (fderiv ℝ c y).flip e := by
    have := fderiv_clm_apply (u := fun _ : Space => e) hc hu
    simpa using this
  rw [h, ContinuousLinearMap.flip_apply]
  exact ContinuousLinearMap.le_opNorm₂ (fderiv ℝ c y) v e

theorem rby_physPd_const (c : Space) (j : Fin 3) (y : Space) : physPd (fun _ => c) j y = 0 := by
  unfold physPd
  simp [fderiv_const_apply]

theorem rby_physPd_zero (j : Fin 3) (y : Space) : physPd (0 : Space → Space) j y = 0 :=
  rby_physPd_const 0 j y

theorem rby_physPd2_zero (j l : Fin 3) (y : Space) : physPd2 (0 : Space → Space) j l y = 0 := by
  unfold physPd2
  simp only [rby_physPd_zero]
  exact rby_physPd_const 0 j y

/-! ## 2. The auxiliary off-axis fields -/

/-- `g_l(τ, y) = ∂_l f(τ, y)` off the axis, `0` on the axis. -/
def gAux (f : ℝ → Space → Space) (l : Fin 3) (τ : ℝ) (y : Space) : Space :=
  if y ∈ axis then 0 else fderiv ℝ (f τ) y (coordinateVector l)

/-- `∂_j f(x)` off the axis (as a function of the space-time point `x = (τ, y)`), `0` on the axis. -/
def pw1 (f : ℝ → Space → Space) (j : Fin 3) (x : ℝ × Space) : Space :=
  if x.2 ∈ axis then 0 else fderiv ℝ (f x.1) x.2 (coordinateVector j)

/-- `∂_j ∂_l f(x)` off the axis, `0` on the axis. -/
def pw2 (f : ℝ → Space → Space) (j l : Fin 3) (x : ℝ × Space) : Space :=
  if x.2 ∈ axis then 0 else fderiv ℝ (gAux f l x.1) x.2 (coordinateVector j)

theorem rby_meas_pw1 (f : ℝ → Space → Space) (hf : Measurable fun x : ℝ × Space => f x.1 x.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (f τ) y) (e : Space) :
    Measurable fun x : ℝ × Space => if x.2 ∈ axis then (0 : Space) else fderiv ℝ (f x.1) x.2 e :=
  measurable_fderiv_apply_offaxis (V := fun _ _ => e) hf measurable_const hd

theorem rby_fderiv_gAux_eq (f : ℝ → Space → Space) (τ : ℝ) (l : Fin 3) {y : Space} (hy : y ∉ axis) :
    fderiv ℝ (gAux f l τ) y = fderiv ℝ (fun y' => fderiv ℝ (f τ) y' (coordinateVector l)) y := by
  have heq : gAux f l τ =ᶠ[𝓝 y] (fun y' => fderiv ℝ (f τ) y' (coordinateVector l)) := by
    filter_upwards [isOpen_compl_axis.mem_nhds hy] with y' hy'
    have hy'' : y' ∉ axis := hy'
    simp only [gAux, if_neg hy'']
  exact heq.fderiv_eq

theorem rby_physPd2_eq (f : ℝ → Space → Space) (τ : ℝ) (j l : Fin 3) {y : Space} (hy : y ∉ axis) :
    physPd2 (f τ) j l y = fderiv ℝ (gAux f l τ) y (coordinateVector j) := by
  rw [rby_fderiv_gAux_eq f τ l hy]
  unfold physPd2 physPd
  rfl

theorem rby_diff_gAux (f : ℝ → Space → Space) (hC2 : ∀ τ, ContDiffOn ℝ 2 (f τ) axisᶜ) (τ : ℝ)
    (l : Fin 3) {y : Space} (hy : y ∉ axis) : DifferentiableAt ℝ (gAux f l τ) y := by
  have heq : gAux f l τ =ᶠ[𝓝 y] (fun y' => fderiv ℝ (f τ) y' (coordinateVector l)) := by
    filter_upwards [isOpen_compl_axis.mem_nhds hy] with y' hy'
    have hy'' : y' ∉ axis := hy'
    simp only [gAux, if_neg hy'']
  exact ((rby_fderiv_diff_of_contDiffOn (hC2 τ) hy).clm_apply
    (differentiableAt_const (coordinateVector l))).congr_of_eventuallyEq heq

theorem rby_meas_gAux (f : ℝ → Space → Space) (hf : Measurable fun x : ℝ × Space => f x.1 x.2)
    (hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (f τ) y) (l : Fin 3) :
    Measurable fun x : ℝ × Space => gAux f l x.1 x.2 :=
  rby_meas_pw1 f hf hd (coordinateVector l)

/-- Operator norm of the first jet assembled from the `pw1` values (`‖D f‖` off the axis). -/
def pwN1 (f : ℝ → Space → Space) (x : ℝ × Space) : ℝ := ‖jet1 fun j => pw1 f j x‖

/-- Operator norm of the second jet assembled from the `pw2` values (`‖D²f‖` off the axis). -/
def pwN2 (f : ℝ → Space → Space) (x : ℝ × Space) : ℝ := ‖jet2 fun j l => pw2 f j l x‖

theorem rby_pw1_eq (f : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    (jet1 fun j => pw1 f j (τ, y)) = fderiv ℝ (f τ) y := by
  have h1 : ∀ j : Fin 3, pw1 f j (τ, y) = fderiv ℝ (f τ) y (coordinateVector j) := fun j => by
    unfold pw1
    simp only [if_neg hy]
  simp only [h1]
  exact (eq_jet1 _).symm

theorem rby_pw2_eq (f : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    (jet2 fun j l => pw2 f j l (τ, y)) = secondJet (f τ) y := by
  have h2 : ∀ j l : Fin 3, pw2 f j l (τ, y) = physPd2 (f τ) j l y := fun j l => by
    unfold pw2
    simp only [if_neg hy]
    exact (rby_physPd2_eq f τ j l hy).symm
  simp only [h2]
  rfl

theorem rby_norm_pw1_le (f : ℝ → Space → Space) (x : ℝ × Space) :
    pwN1 f x ≤ ‖fderiv ℝ (f x.1) x.2‖ := by
  by_cases hy : x.2 ∈ axis
  · have : (fun j : Fin 3 => pw1 f j x) = fun _ => 0 := by
      funext j; simp [pw1, hy]
    unfold pwN1
    rw [this, jet1_zero, norm_zero]
    exact norm_nonneg _
  · have := rby_pw1_eq f x.1 hy
    unfold pwN1
    rw [show x = (x.1, x.2) from rfl, this]

theorem rby_norm_pw2_le (f : ℝ → Space → Space) (hC2 : ∀ τ, ContDiffOn ℝ 2 (f τ) axisᶜ)
    (x : ℝ × Space) : pwN2 f x ≤ ‖fderiv ℝ (fun y => fderiv ℝ (f x.1) y) x.2‖ := by
  by_cases hy : x.2 ∈ axis
  · have : (fun j l : Fin 3 => pw2 f j l x) = fun _ _ => 0 := by
      funext j l; simp [pw2, hy]
    unfold pwN2
    rw [this, jet2_zero]
    have h0 : ‖(0 : Space →L[ℝ] Space →L[ℝ] Space)‖ = 0 := ContinuousLinearMap.opNorm_zero
    have h1 := norm_nonneg (fderiv ℝ (fun y => fderiv ℝ (f x.1) y) x.2)
    rw [h0]; exact h1
  · have h1 := rby_pw2_eq f x.1 hy
    have h2 := secondJet_eq_fderiv (rby_fderiv_diff_of_contDiffOn (hC2 x.1) (y := x.2) hy)
    unfold pwN2
    rw [show x = (x.1, x.2) from rfl, h1, h2]

theorem rby_coefChg_eq (f : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    coefChgDens (f τ) 0 y = ‖f τ y‖ + pwN1 f (τ, y) + pwN2 f (τ, y) := by
  unfold pwN1 pwN2
  rw [rby_pw1_eq f τ hy, rby_pw2_eq f τ hy]
  unfold coefChgDens
  have e5 : fderiv ℝ (0 : Space → Space) y = 0 := by simp
  have e6 : fderiv ℝ (f τ) y - 0 = fderiv ℝ (f τ) y := by
    ext a : 1
    simp
  have e7 : secondJet (f τ) y - 0 = secondJet (f τ) y := by
    ext a b : 2
    simp
  simp only [Pi.zero_apply, sub_zero, e5, e6, secondJet_zero, e7]

/-! ## 3. Phase-norm helpers -/

theorem rby_phaseLr_congr_ae {P r : ℝ} {F G : ℝ × Space → ℝ}
    (h : ∀ t : ℝ, ∀ᵐ y ∂(volume : Measure Space), F (t, y) = G (t, y)) :
    phaseLr P r F = phaseLr P r G := by
  unfold phaseLr
  congr 2
  refine lintegral_congr fun t => lintegral_congr_ae ?_
  filter_upwards [h t] with y hy
  rw [hy]

/-! ## 4. The coefficient-change bound for a `C²`-off-axis family -/

/-- Phase-norm bound of the change density of `f τ` (with `f` jointly continuous and `C²` off the
axis), by the energy-type term `M`, the first-derivative term `M1` and the second-derivative
term `M2`. -/
theorem rby_coefChg_phaseLr_le {P : ℝ} (hP : 0 < P) {f : ℝ → Space → Space}
    (hf : Continuous fun x : ℝ × Space => f x.1 x.2)
    (hC2 : ∀ τ, ContDiffOn ℝ 2 (f τ) axisᶜ) {M M1 M2 : ℝ≥0∞}
    (hS : phaseLr P (11 / 4) (fun x => ‖f x.1 x.2‖) ≤ M)
    (hD1 : phaseLr P (11 / 4) (fun x => ‖fderiv ℝ (f x.1) x.2‖) ≤ M1)
    (hD2 : phaseLr P (11 / 4) (fun x => ‖fderiv ℝ (fun y => fderiv ℝ (f x.1) y) x.2‖) ≤ M2) :
    phaseLr P (11 / 4) (fun x => coefChgDens (f x.1) 0 x.2) ≤
      M + ENNReal.ofReal 3 * M1 + ENNReal.ofReal 9 * M2 := by
  have hdiff : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (f τ) y :=
    fun τ y hy => rby_diff_of_contDiffOn (hC2 τ) hy
  have hfm : Measurable fun x : ℝ × Space => f x.1 x.2 := hf.measurable
  have hmeasA : Measurable fun x : ℝ × Space => ‖f x.1 x.2‖ := hfm.norm
  have hmP1 : Measurable fun x : ℝ × Space => pwN1 f x := by
    have hc : Continuous fun m : Fin 3 → Space => ‖jet1 m‖ :=
      (continuous_norm (E := Space →L[ℝ] Space)).comp continuous_jet1
    refine hc.measurable.comp (measurable_pi_lambda _ fun j => ?_)
    unfold pw1
    exact rby_meas_pw1 f hfm hdiff (coordinateVector j)
  have hmP2 : Measurable fun x : ℝ × Space => pwN2 f x := by
    have hc : Continuous fun m : Fin 3 → Fin 3 → Space => ‖jet2 m‖ :=
      (continuous_norm (E := Space →L[ℝ] Space →L[ℝ] Space)).comp continuous_jet2
    refine hc.measurable.comp (measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun l => ?_)
    unfold pw2
    exact rby_meas_pw1 (gAux f l) (rby_meas_gAux f hfm hdiff l)
      (fun τ y hy => rby_diff_gAux f hC2 τ l hy) (coordinateVector j)
  have hae : ∀ᵐ y ∂(volume : Measure Space), y ∉ axis :=
    UnforcedLeray.Sob.ae_offAxis.mono fun y hy => (UnforcedLeray.Axi.mem_offAxis_iff y).1 hy
  have hEq : phaseLr P (11 / 4) (fun x => coefChgDens (f x.1) 0 x.2) =
      phaseLr P (11 / 4) (fun x => (‖f x.1 x.2‖ + pwN1 f x) + pwN2 f x) := by
    apply rby_phaseLr_congr_ae
    intro t
    filter_upwards [hae] with y hy
    rw [rby_coefChg_eq f t hy]
  have hr1 : (1 : ℝ) ≤ 11 / 4 := by norm_num
  have hr0 : (0 : ℝ) < 11 / 4 := by norm_num
  have hBpt : ∀ x : ℝ × Space, |pwN1 f x| ≤ 3 * |‖fderiv ℝ (f x.1) x.2‖| := by
    intro x
    have h := rby_norm_pw1_le f x
    have h0 : 0 ≤ pwN1 f x := norm_nonneg _
    have h2 := norm_nonneg (fderiv ℝ (f x.1) x.2)
    rw [abs_of_nonneg h0, abs_of_nonneg h2]
    linarith
  have hCpt : ∀ x : ℝ × Space, |pwN2 f x| ≤
      9 * |‖fderiv ℝ (fun y => fderiv ℝ (f x.1) y) x.2‖| := by
    intro x
    have h := rby_norm_pw2_le f hC2 x
    have h0 : 0 ≤ pwN2 f x := by
      unfold pwN2
      have h := norm_nonneg (jet2 fun j l => pw2 f j l x)
      exact h
    have h2 := norm_nonneg (fderiv ℝ (fun y => fderiv ℝ (f x.1) y) x.2)
    rw [abs_of_nonneg h0, abs_of_nonneg h2]
    linarith
  have hBM : phaseLr P (11 / 4) (fun x => pwN1 f x) ≤ ENNReal.ofReal 3 * M1 :=
    (phaseLr_mono_smul hr0 (by norm_num) hBpt).trans (mul_le_mul_of_nonneg_left hD1 (by positivity))
  have hCM : phaseLr P (11 / 4) (fun x => pwN2 f x) ≤ ENNReal.ofReal 9 * M2 :=
    (phaseLr_mono_smul hr0 (by norm_num) hCpt).trans (mul_le_mul_of_nonneg_left hD2 (by positivity))
  have hF1 : Measurable fun x : ℝ × Space => ‖f x.1 x.2‖ + pwN1 f x := hmeasA.add hmP1
  rw [hEq]
  calc phaseLr P (11 / 4) (fun x => (‖f x.1 x.2‖ + pwN1 f x) + pwN2 f x)
      ≤ phaseLr P (11 / 4) (fun x => ‖f x.1 x.2‖ + pwN1 f x) +
          phaseLr P (11 / 4) (fun x => pwN2 f x) :=
        phaseLr_add_le hP hr1 hF1 hmP2
    _ ≤ (phaseLr P (11 / 4) (fun x => ‖f x.1 x.2‖) + phaseLr P (11 / 4) (fun x => pwN1 f x))
          + phaseLr P (11 / 4) (fun x => pwN2 f x) :=
        add_le_add (phaseLr_add_le hP hr1 hmeasA hmP1) le_rfl
    _ ≤ M + ENNReal.ofReal 3 * M1 + ENNReal.ofReal 9 * M2 :=
        add_le_add (add_le_add hS hBM) hCM

/-! ## 5. The repair bound `RbYBound` -/

theorem rbYBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : RbYBound D := by
  obtain ⟨C, k, hRD⟩ := hst.repairDeriv
  have hlim : Tendsto (retNu D.Pl D.σ₀) atTop (nhds 0) := retNu_tendsto D.σ₀ hst.omega_ne
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < dm ^ 3 / 12 :=
    hlim.eventually (gt_mem_nhds (by have := hst.dm_pos; positivity))
  have hnu : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 ∧ 0 ≤ rhoRep D.K (D.level n) :=
    nuLeOneRhoNonneg D hst
  have hC0 : 0 < D.K.C0 := hst.C0_pos
  refine ⟨D.K.C0 + 12 * max C 0, max D.K.k0 k, ?_⟩
  filter_upwards [hst.actual, hnu, hsmall, hRD] with n hact hN hS hR
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have hcpos : 0 < cOf (D.level n).ν := cOf_pos hνpos
  have hP : 0 < 2 * (D.level n).ε * cOf (D.level n).ν := by positivity
  obtain ⟨z, -, hV, hrb, -⟩ := hact.split.state
  have hrbf : ∀ τ, D.rb n τ = ((D.level n).params D.Pl).corr z τ := fun τ => congrFun hrb τ
  have hP1 : ((D.level n).params D.Pl).period ≤ 1 :=
    bgCorr_period_le_one hact.regime (le_of_lt hS)
  have hcont : Continuous fun x : ℝ × Space => D.rb n x.1 x.2 := by
    have e : (fun x : ℝ × Space => D.rb n x.1 x.2) =
        fun x => ((D.level n).params D.Pl).corr z x.1 x.2 := by
      funext x
      rw [hrbf x.1]
    rw [e]
    exact UnforcedLeray.Short.IIIa.corr_continuous _ hP1 z
  have hC2 : ∀ τ, ContDiffOn ℝ 2 (D.rb n τ) axisᶜ := by
    intro τ
    rw [hrbf τ]
    refine bgCorr_contDiffOn_offAxis (V := D.V n) (pres := D.pres n) hst.planar.eigenpair
      hact.regime hN.1 rfl z hV ?_ τ
    have e : (fun τ y => D.V n τ y + ((D.level n).params D.Pl).corr z τ y) = (D.level n).U := by
      funext τ y
      simp only [ReturnLevel.U, ← hrbf τ]
      rfl
    rw [e]
    exact hact.profile
  have hEn : phaseLr (2 * (D.level n).ε * cOf (D.level n).ν) (11 / 4)
      (fun x => ‖D.rb n x.1 x.2‖) ≤ ENNReal.ofReal ((D.level n).ρb D.Pl D.K) := by
    refine phaseLr_le_of_slice (F := fun τ y => ‖D.rb n τ y‖) hP (by norm_num) _ (fun τ => ?_)
    show eLpNorm (fun y => ‖D.rb n τ y‖) (ENNReal.ofReal (11 / 4)) volume ≤ _
    rw [eLpNorm_norm]
    have h := hact.split.energy τ
    simp only [UnforcedLeray.Short.IIb.bgp] at h
    exact le_trans le_self_add h
  have hMain := rby_coefChg_phaseLr_le hP hcont hC2 hEn hR.2.1 hR.2.2
  -- constants
  have hρ0 : 0 ≤ rhoRep D.K (D.level n) := hN.2
  have ha1 : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hN.1⟩
  have ha0 : (0 : ℝ) ≤ (D.level n).ν⁻¹ := by linarith
  have hρb : (D.level n).ρb D.Pl D.K = D.K.C0 * (D.level n).ν⁻¹ ^ D.K.k0 * rhoRep D.K (D.level n) := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB rhoRep
    simp only [ReturnLevel.params]
    rw [inv_pow]
    ring
  have hρbnn : 0 ≤ (D.level n).ρb D.Pl D.K := by
    rw [hρb]
    exact mul_nonneg (mul_nonneg hC0.le (pow_nonneg ha0 _)) hρ0
  have hρle : (D.level n).ρb D.Pl D.K ≤
      D.K.C0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) := by
    rw [hρb]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 (le_max_left _ _)) hC0.le) hρ0
  have hXX : C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n) ≤
      max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) := by
    calc C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n)
        ≤ max C 0 * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg ha0 _)) hρ0
      _ ≤ max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1 (le_max_right _ _))
              (le_max_right C 0)) hρ0
  have hXp0 : 0 ≤ max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) :=
    mul_nonneg (mul_nonneg (le_max_right C 0) (pow_nonneg ha0 _)) hρ0
  have h3 : ENNReal.ofReal 3 * ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n))
      ≤ ENNReal.ofReal 3 * ENNReal.ofReal
        (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) :=
    mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hXX) (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal 3)
  have h9 : ENNReal.ofReal 9 * ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n))
      ≤ ENNReal.ofReal 9 * ENNReal.ofReal
        (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) :=
    mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hXX) (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal 9)
  have hsum1 : 0 ≤ (D.level n).ρb D.Pl D.K + 3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
      rhoRep D.K (D.level n)) := by linarith
  have hsum2 : 0 ≤ 3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) := by
    linarith
  have hsum3 : 0 ≤ 9 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) := by
    linarith
  have hfin : (D.level n).ρb D.Pl D.K + 3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
      rhoRep D.K (D.level n)) + 9 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
      rhoRep D.K (D.level n)) ≤
      (D.K.C0 + 12 * max C 0) * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) := by
    have hh : (D.level n).ρb D.Pl D.K ≤ D.K.C0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
        rhoRep D.K (D.level n) := hρle
    calc (D.level n).ρb D.Pl D.K + 3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
          rhoRep D.K (D.level n)) + 9 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
          rhoRep D.K (D.level n))
        ≤ D.K.C0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) +
          3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) +
          9 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) := by
          linarith
      _ = (D.K.C0 + 12 * max C 0) * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n) := by
          ring
  have hsplit : ENNReal.ofReal ((D.level n).ρb D.Pl D.K + 3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
      rhoRep D.K (D.level n)) + 9 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
      rhoRep D.K (D.level n))) =
      ENNReal.ofReal ((D.level n).ρb D.Pl D.K) + ENNReal.ofReal 3 *
        ENNReal.ofReal (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) +
      ENNReal.ofReal 9 *
        ENNReal.ofReal (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) := by
    rw [ENNReal.ofReal_add hsum1 hsum3, ENNReal.ofReal_add hρbnn hsum2,
      ENNReal.ofReal_mul (p := 3) (by norm_num), ENNReal.ofReal_mul (p := 9) (by norm_num)]
  calc _ ≤ ENNReal.ofReal ((D.level n).ρb D.Pl D.K) + ENNReal.ofReal 3 *
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n)) +
        ENNReal.ofReal 9 * ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n)) := hMain
    _ ≤ ENNReal.ofReal ((D.level n).ρb D.Pl D.K) + ENNReal.ofReal 3 *
        ENNReal.ofReal (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) +
        ENNReal.ofReal 9 *
        ENNReal.ofReal (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) * rhoRep D.K (D.level n)) :=
        add_le_add (add_le_add le_rfl h3) h9
    _ = ENNReal.ofReal ((D.level n).ρb D.Pl D.K + 3 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
        rhoRep D.K (D.level n)) + 9 * (max C 0 * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
        rhoRep D.K (D.level n))) := hsplit.symm
    _ ≤ ENNReal.ofReal ((D.K.C0 + 12 * max C 0) * (D.level n).ν⁻¹ ^ (max D.K.k0 k) *
        rhoRep D.K (D.level n)) := ENNReal.ofReal_le_ofReal hfin

end UnforcedLeray.Short.PartIIIb.Concrete
