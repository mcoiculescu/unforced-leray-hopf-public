import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.AgeJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.FrameJets

/-!
# Phase jets, task `PartII-b:G4/5/2/1/2/2`

Source of record: `the November 2 reference manuscript` lines 2346-2366
(phase `ξ = Rτ/2 - (R/2) log s`, `s = R²/ϱ²`).  Off the axis the phase has the explicit
gradient `Dξ(z) = R ϱ(z)⁻² (z₀ dz₀ + z₁ dz₁) = (R * age 1 z) • Lz z`, where
`Lz z = z₀ • proj₀ + z₁ • proj₁` is a linear map with `‖Lz z‖ ≤ 2 ϱ(z)` and constant norm.
`PhaseJets` then follows from the Leibniz rule on `axisᶜ` applied to the scalar `R * age 1`
(jets from `ageJets`) and to `Lz` (jets from `clm_jet_one`, `clm_jet_ge_two`), after
`‖D^{j} ξ‖ = ‖D^{j-1} (Dξ)‖` (`norm_iteratedFDeriv_fderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace PhaseJetsAux

open UnforcedLeray

/-- The coordinate projection `y ↦ y 0` as a continuous linear map. -/
def proj0 : Space →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)

/-- The coordinate projection `y ↦ y 1` as a continuous linear map. -/
def proj1 : Space →L[ℝ] ℝ := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)

/-- The linear map `z ↦ z₀ • proj₀ + z₁ • proj₁`, so that `Dϱ(z) = ϱ(z)⁻¹ • Lz z`. -/
def Lz : Space →L[ℝ] (Space →L[ℝ] ℝ) :=
  proj0.smulRight proj0 + proj1.smulRight proj1

theorem Lz_apply (z v : Space) : Lz z v = z 0 * v 0 + z 1 * v 1 := by
  simp [Lz, proj0, proj1]

theorem norm_Lz_le (z : Space) : ‖Lz z‖ ≤ 2 * Axi.ϱ z := by
  have hϱ : 0 ≤ Axi.ϱ z := Axi.ϱ_nonneg z
  have h0 : |z 0| ≤ Axi.ϱ z := by
    unfold Axi.ϱ
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 1)])
  have h1 : |z 1| ≤ Axi.ϱ z := by
    unfold Axi.ϱ
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 0)])
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv0 : ‖v 0‖ ≤ ‖v‖ := PiLp.norm_apply_le v 0
  have hv1 : ‖v 1‖ ≤ ‖v‖ := PiLp.norm_apply_le v 1
  rw [Lz_apply]
  calc ‖z 0 * v 0 + z 1 * v 1‖ ≤ ‖z 0 * v 0‖ + ‖z 1 * v 1‖ := norm_add_le _ _
    _ = |z 0| * ‖v 0‖ + |z 1| * ‖v 1‖ := by simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ Axi.ϱ z * ‖v‖ + Axi.ϱ z * ‖v‖ :=
        add_le_add (mul_le_mul h0 hv0 (norm_nonneg _) hϱ) (mul_le_mul h1 hv1 (norm_nonneg _) hϱ)
    _ = 2 * Axi.ϱ z * ‖v‖ := by ring

/-- Off the axis, the derivative of the phase is `(R ϱ⁻²) • Lz`. -/
theorem fderiv_phase_eq {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {z : Space} (hz : z ∉ Axi.axis) :
    fderiv ℝ (Axi.phase R τ) z = (R * Axi.age 1 z) • Lz z := by
  rw [(Axi.hasFDerivAt_phase hR τ hz).fderiv]
  refine ContinuousLinearMap.ext fun v => ?_
  have hρ := Axi.ϱ_ne_zero hz
  simp only [Axi.phaseD, smul_apply, Axi.ϱD_apply, Lz_apply, Axi.age, smul_eq_mul]
  field_simp

end PhaseJetsAux

/-- **Phase jets** (SP 2346-2366): `PhaseJets`, proved by Leibniz on `axisᶜ` for
`D ξ = (R * age 1) • Lz`. -/
theorem phaseJets : UnforcedLeray.Short.IIb.PhaseJets := by
  have hA : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (y : Space), y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ j (Axi.age R) y‖ ≤ C * R ^ 2 * (Axi.ϱ y)⁻¹ ^ (j + 2) := ageJets
  choose CA hCA0 hCA using hA
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = ∑ i ∈ Finset.range (m + 1), CA i := ⟨_, rfl⟩
  have hCs0 : 0 ≤ Cs := by
    rw [hCsdef]; exact Finset.sum_nonneg fun i _ => (hCA0 i).le
  have hCle : ∀ i ∈ Finset.range (m + 1), CA i ≤ Cs := fun i hi => by
    rw [hCsdef]; exact Finset.single_le_sum (f := CA) (fun k _ => (hCA0 k).le) hi
  have hC : 0 < ((m + 1 : ℕ) : ℝ) * 2 ^ m * Cs * (2 + ‖PhaseJetsAux.Lz‖) + 1 :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hCs0) (by positivity))
      one_pos
  refine ⟨((m + 1 : ℕ) : ℝ) * 2 ^ m * Cs * (2 + ‖PhaseJetsAux.Lz‖) + 1, hC, ?_⟩
  intro R τ y hR hy
  have hR0 : R ≠ 0 := hR.ne'
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hzc : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact inv_pos.2 hϱ
  have htϱ : t * Axi.ϱ y = 1 := by rw [ht]; exact inv_mul_cancel₀ hϱ.ne'
  have hφc : ContDiffOn ℝ ∞ (fun z : Space => R * Axi.age 1 z) Axi.axisᶜ :=
    contDiffOn_const.mul (ChartJetsAux.contDiffOn_age 1)
  have hLc : ContDiffOn ℝ ∞ (fun z : Space => PhaseJetsAux.Lz z) Axi.axisᶜ :=
    PhaseJetsAux.Lz.contDiff.contDiffOn
  have hEq : fderiv ℝ (Axi.phase R τ) =ᶠ[𝓝 y]
      fun z : Space => (R * Axi.age 1 z) • PhaseJetsAux.Lz z := by
    filter_upwards [hopen.mem_nhds hzc] with z hz
    exact PhaseJetsAux.fderiv_phase_eq hR0 τ hz
  -- scalar jets: `‖D^i (R * age 1) y‖ ≤ R CA_i t^(i+2)`
  have hφb : ∀ i : ℕ, ‖iteratedFDerivWithin ℝ i (fun z : Space => R * Axi.age 1 z)
      Axi.axisᶜ y‖ ≤ R * CA i * t ^ (i + 2) := by
    intro i
    have hdiff : ContDiffAt ℝ i (Axi.age 1) y :=
      ((ChartJetsAux.contDiffOn_age 1).contDiffAt (hopen.mem_nhds hzc)).of_le
        (by exact_mod_cast le_top)
    have hfun : (fun z : Space => R * Axi.age 1 z) = R • Axi.age 1 := by
      funext z; simp [Pi.smul_apply, smul_eq_mul]
    rw [iteratedFDerivWithin_of_isOpen i hopen hzc, hfun, iteratedFDeriv_const_smul_apply hdiff,
      norm_smul, Real.norm_of_nonneg hR.le]
    have h := hCA i 1 y hy
    rw [← ht] at h
    calc R * ‖iteratedFDeriv ℝ i (Axi.age 1) y‖ ≤ R * (CA i * 1 ^ 2 * t ^ (i + 2)) :=
          mul_le_mul_of_nonneg_left h hR.le
      _ = R * CA i * t ^ (i + 2) := by ring
  -- jets of `Lz`
  have hLb0 : ‖iteratedFDerivWithin ℝ 0 (⇑PhaseJetsAux.Lz) Axi.axisᶜ y‖ ≤ 2 * Axi.ϱ y := by
    rw [norm_iteratedFDerivWithin_zero]
    exact PhaseJetsAux.norm_Lz_le y
  have hLb1 : ‖iteratedFDerivWithin ℝ 1 (⇑PhaseJetsAux.Lz) Axi.axisᶜ y‖ ≤ ‖PhaseJetsAux.Lz‖ := by
    rw [iteratedFDerivWithin_of_isOpen 1 hopen hzc]
    exact SqrtFrameJetsAux.clm_jet_one PhaseJetsAux.Lz y
  have hLb2 : ∀ k : ℕ, 2 ≤ k → iteratedFDerivWithin ℝ k (⇑PhaseJetsAux.Lz) Axi.axisᶜ y = 0 := by
    intro k hk
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
    rw [iteratedFDerivWithin_of_isOpen _ hopen hzc]
    exact SqrtFrameJetsAux.clm_jet_ge_two PhaseJetsAux.Lz p y
  -- Leibniz on `axisᶜ`
  have hL : ‖iteratedFDerivWithin ℝ m (fun z : Space => (R * Axi.age 1 z) • PhaseJetsAux.Lz z)
      Axi.axisᶜ y‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (fun z : Space => R * Axi.age 1 z) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (m - i) (⇑PhaseJetsAux.Lz) Axi.axisᶜ y‖ :=
    norm_iteratedFDerivWithin_smul_le hφc hLc hopen.uniqueDiffOn hzc (by exact_mod_cast le_top)
  have hR' : 0 ≤ R := hR.le
  have hB0 : 0 ≤ (2 : ℝ) ^ m * (R * Cs * t ^ (m + 1)) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hR' hCs0) (pow_nonneg ht0.le _))
  have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ i (fun z : Space => R * Axi.age 1 z) Axi.axisᶜ y‖ *
      ‖iteratedFDerivWithin ℝ (m - i) (⇑PhaseJetsAux.Lz) Axi.axisᶜ y‖ ≤
      2 ^ m * (R * Cs * t ^ (m + 1)) * (2 + ‖PhaseJetsAux.Lz‖) := by
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_range.1 hi; omega
    have hch : (m.choose i : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m i
    have hPX : ‖iteratedFDerivWithin ℝ i (fun z : Space => R * Axi.age 1 z) Axi.axisᶜ y‖ ≤
        R * Cs * t ^ (i + 2) :=
      (hφb i).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hCle i hi) hR')
        (pow_nonneg ht0.le _))
    have hP0 : 0 ≤ ‖iteratedFDerivWithin ℝ i (fun z : Space => R * Axi.age 1 z) Axi.axisᶜ y‖ :=
      norm_nonneg _
    have hQ0 : 0 ≤ ‖iteratedFDerivWithin ℝ (m - i) (⇑PhaseJetsAux.Lz) Axi.axisᶜ y‖ :=
      norm_nonneg _
    have hgen := mul_le_mul_of_nonneg_right (mul_le_mul hch hPX hP0 (by positivity)) hQ0
    have hLnn : 0 ≤ ‖PhaseJetsAux.Lz‖ := by positivity
    by_cases h0 : i = m
    · -- the top term: `m - i = 0`
      have e : m - i = 0 := by omega
      have ht_eq : t ^ (i + 2) * Axi.ϱ y = t ^ (m + 1) := by
        rw [h0, show t ^ (m + 2) * Axi.ϱ y = t ^ (m + 1) * (t * Axi.ϱ y) by ring, htϱ, mul_one]
      rw [e] at hgen ⊢
      have hkey : (2 : ℝ) ^ m * (R * Cs * t ^ (i + 2)) * (2 * Axi.ϱ y) =
          2 ^ m * (R * Cs * t ^ (m + 1)) * 2 := by
        linear_combination ((2 : ℝ) ^ m * R * Cs * 2) * ht_eq
      have hX : 0 ≤ (2 : ℝ) ^ m * (R * Cs * t ^ (i + 2)) :=
        mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hR' hCs0) (pow_nonneg ht0.le _))
      have hBle : 2 ^ m * (R * Cs * t ^ (m + 1)) * 2 ≤
          2 ^ m * (R * Cs * t ^ (m + 1)) * (2 + ‖PhaseJetsAux.Lz‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hB0
      exact hgen.trans (((mul_le_mul_of_nonneg_left hLb0 hX).trans_eq hkey).trans hBle)
    · by_cases h1 : i + 1 = m
      · -- the term `m - i = 1`
        have e : m - i = 1 := by omega
        have e2 : i + 2 = m + 1 := by omega
        rw [e2] at hgen
        rw [e] at hgen ⊢
        have hbnd := mul_le_mul_of_nonneg_left hLb1 hB0
        have hBle : 2 ^ m * (R * Cs * t ^ (m + 1)) * ‖PhaseJetsAux.Lz‖ ≤
            2 ^ m * (R * Cs * t ^ (m + 1)) * (2 + ‖PhaseJetsAux.Lz‖) :=
          mul_le_mul_of_nonneg_left (by linarith) hB0
        exact hgen.trans (hbnd.trans hBle)
      · -- `m - i ≥ 2`: the term vanishes
        have e : 2 ≤ m - i := by omega
        rw [hLb2 (m - i) e, norm_zero, mul_zero]
        exact mul_nonneg hB0 (by positivity)
  have hsum := Finset.sum_le_card_nsmul (Finset.range (m + 1)) _ _ hterm
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  rw [← ht, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Axi.phase R τ) (x := y) (n := m),
    (hEq.iteratedFDeriv ℝ m).self_of_nhds, ← iteratedFDerivWithin_of_isOpen m hopen hzc]
  have hRt : 0 ≤ R * t ^ (m + 1) := mul_nonneg hR' (pow_nonneg ht0.le _)
  calc ‖iteratedFDerivWithin ℝ m (fun z : Space => (R * Axi.age 1 z) • PhaseJetsAux.Lz z)
        Axi.axisᶜ y‖
      ≤ _ := hL
    _ ≤ ((m + 1 : ℕ) : ℝ) * (2 ^ m * (R * Cs * t ^ (m + 1)) * (2 + ‖PhaseJetsAux.Lz‖)) := hsum
    _ = ((m + 1 : ℕ) : ℝ) * 2 ^ m * Cs * (2 + ‖PhaseJetsAux.Lz‖) * (R * t ^ (m + 1)) := by ring
    _ ≤ (((m + 1 : ℕ) : ℝ) * 2 ^ m * Cs * (2 + ‖PhaseJetsAux.Lz‖) + 1) * (R * t ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) hRt
    _ = (((m + 1 : ℕ) : ℝ) * 2 ^ m * Cs * (2 + ‖PhaseJetsAux.Lz‖) + 1) * R * t ^ (m + 1) := by
        ring

end UnforcedLeray.Short.IIb
