import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Cut3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Reg

/-!
# Regularity of the stream-cut displacement of a separated source
(source 4171-4201, 3603-3713)

Source of record: `the November 2 reference manuscript` (73 pages).

For a `P`-periodic separated source `T` supported in `ϱ ≤ r_o = R√(5ν/6)` with finite `Y₂` moment
and `X₀ = sepX0 ν μ T` axisymmetric swirl-free on the young region, the cut displacement
`X = 𝒞_y X₀ = wardStreamCut ν R χ_y X₀` satisfies the three clauses of `WardXDiff`:

* `ϱ² ≤ νR²` (`ν·age ≥ 1`): `χ_y = χ_y' = 0` on `[1, ∞)`, so `X ≡ 0` near such points (the open set
  `0 < ϱ < R√ν`, which together with the young region `ϱ > r_o` covers the complement of the axis);
* young region: `X₀` is `C^∞` in `y` (`xd_X0_top`), the primitive `Ψ_{X₀}` is `C³` (`xc_outPrim_c3`,
  `∂_rΨ = rZ_z`, `∂_zΨ = -rZ_r`), `χ_y(νR²/ϱ²)`, `χ_y'(νR²/ϱ²)ϱ⁻⁴` are `C^∞` off the axis;
  `X` is differentiable in the phase (`sepX0TauDeriv`, `tcr_outPrim_tau`, `Kd(0) = 0`) with
  `∂_τX = χ_y ∂_τX₀ + (χ_y'/ϱ)(∂_τΨ)e_z`, which is differentiable in `y` (`xd_Zd_diffOn`,
  `xd_Psid_diffOn`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xd_wsc_zero {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (Z : ℝ → Space → Space)
    (τ : ℝ) {y : Space} (hy : y ∉ axis) (hr : ϱ y ^ 2 ≤ ν * R ^ 2) :
    wardStreamCut ν R χy Z τ y = 0 := by
  have hpos : 0 < ϱ y ^ 2 := pow_pos (ϱ_pos hy) 2
  have ht : 1 ≤ ν * age R y := by
    unfold age
    rw [← mul_div_assoc, le_div_iff₀ hpos, one_mul]
    exact hr
  unfold wardStreamCut
  rw [hχy.zero _ ht, IsYoungCutoff.deriv_eq_zero hχy ht]
  simp

theorem xd_thr_lt {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
  have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  exact mul_lt_mul_of_pos_left h1 hR

theorem xd_sq_le_of_lt {ν R x : ℝ} (hν : 0 < ν) (hR : 0 < R) (hx0 : 0 ≤ x)
    (hx : x < R * Real.sqrt ν) : x ^ 2 ≤ ν * R ^ 2 := by
  have hs2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have hm := mul_le_mul hx.le hx.le hx0 (mul_nonneg hR.le (Real.sqrt_nonneg ν))
  have he : (R * Real.sqrt ν) * (R * Real.sqrt ν) = ν * R ^ 2 := by
    rw [show (R * Real.sqrt ν) * (R * Real.sqrt ν) = R ^ 2 * Real.sqrt ν ^ 2 by ring, hs2]
    ring
  nlinarith [hm, he]

section Main

variable {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {χy : ℝ → ℝ}

/-- **`WardXDiff` for the cut displacement of a separated source.** -/
theorem xd_main (hχy : IsYoungCutoff χy) (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R)
    (hP : 0 < P) (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (haxi : AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T)) (τ : ℝ) :
    ContDiffOn ℝ 3 (wardStreamCut ν R χy (sepX0 ν μ T) τ) axisᶜ ∧
      (∀ y : Space, y ∉ axis →
        DifferentiableAt ℝ (fun t => wardStreamCut ν R χy (sepX0 ν μ T) t y) τ) ∧
      DifferentiableOn ℝ (fun y => deriv (fun t => wardStreamCut ν R χy (sepX0 ν μ T) t y) τ)
        axisᶜ := by
  set rO : ℝ := R * Real.sqrt (5 * ν / 6) with hrO
  have hr0 : 0 ≤ rO := by positivity
  set Z : ℝ → Space → Space := sepX0 ν μ T with hZdef
  set W : ℝ → Space → Space := wardStreamCut ν R χy Z with hWdef
  set Zd : ℝ → Space → Space := fun t y' => deriv (fun s => Z s y') t with hZd
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hVo : IsOpen {y : Space | 0 < ϱ y ∧ ϱ y < R * Real.sqrt ν} :=
    (isOpen_lt continuous_const continuous_ϱ).inter (isOpen_lt continuous_ϱ continuous_const)
  have hthr := xd_thr_lt hν hR
  -- covering
  have hcover : ∀ y : Space, y ∉ axis → y ∈ youngOpen ν R ∨
      y ∈ {y : Space | 0 < ϱ y ∧ ϱ y < R * Real.sqrt ν} := by
    intro y hy
    by_cases h : rO < ϱ y
    · exact Or.inl h
    · exact Or.inr ⟨ϱ_pos hy, lt_of_le_of_lt (not_lt.1 h) hthr⟩
  -- vanishing on the near region
  have hV0 : ∀ t, ∀ y ∈ {y : Space | 0 < ϱ y ∧ ϱ y < R * Real.sqrt ν}, W t y = 0 := by
    intro t y hy
    have hyax : y ∉ axis := fun h => by
      have := (mem_axis_iff y).1 h
      linarith [hy.1]
    exact xd_wsc_zero hχy Z t hyax (xd_sq_le_of_lt hν hR (ϱ_nonneg y) hy.2)
  have hnotaxis : ∀ y ∈ youngOpen ν R, y ∉ axis := fun y hy => t9_not_axis hν hR hy
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1
    refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
    rcases hcover y hy with hyU | hyV
    · refine ⟨youngOpen ν R, hUo, hyU, ?_⟩
      have hZ3 : ContDiffOn ℝ 3 (Z τ) (youngOpen ν R) :=
        (xd_X0_top hν hμ hr0 hP hT hM τ).of_le (xd_le_top 3)
      have hO3 := xc_outPrim_c3 hν hR hZ3 (xd_hdr hν hμ hR hP hT hM haxi τ)
      exact (xc_wsc_c3 hχy hν hR hZ3 hO3).mono inter_subset_right
    · refine ⟨_, hVo, hyV, ?_⟩
      exact (contDiffOn_const (c := (0 : Space))).congr fun x hx => hV0 τ x hx.2
  · -- clause 2
    intro y hy
    by_cases hcase : ϱ y ^ 2 ≤ ν * R ^ 2
    · have : (fun t => W t y) = fun _ => (0 : Space) := funext fun t => xd_wsc_zero hχy Z t hy hcase
      rw [this]
      exact differentiableAt_const _
    · have hlt : ν * R ^ 2 < ϱ y ^ 2 := not_le.1 hcase
      have hyU : y ∈ youngOpen ν R := by
        show rO < ϱ y
        by_contra hcon
        have hle : ϱ y ≤ rO := not_lt.1 hcon
        have h2 : ϱ y ^ 2 ≤ rO ^ 2 := pow_le_pow_left₀ (ϱ_nonneg y) hle 2
        have hsq : rO ^ 2 = R ^ 2 * (5 * ν / 6) := by
          rw [hrO, mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith [mul_pos hν (pow_pos hR 2)]
      have hyr : rO < ϱ y := hyU
      have hZt := (tcr_hasDerivAt_tau hν hμ hr0 hP hT hM τ hyr).differentiableAt
      have hΨt := (tcr_outPrim_tau hν hμ hr0 hP hT hM τ hyr).differentiableAt
      show DifferentiableAt ℝ (fun t => wardStreamCut ν R χy Z t y) τ
      unfold wardStreamCut
      exact (hZt.const_smul (χy (ν * age R y))).add ((hΨt.const_mul _).smul_const _)
  · -- clause 3
    refine differentiableOn_of_locally_differentiableOn fun y hy => ?_
    rcases hcover y hy with hyU | hyV
    · refine ⟨youngOpen ν R, hUo, hyU, ?_⟩
      refine DifferentiableOn.mono ?_ inter_subset_right
      have hϱ1 : ContDiffOn ℝ 1 (fun y : Space => ϱ y) (youngOpen ν R) :=
        contDiffOn_ϱ.mono hnotaxis
      have hne : ∀ y ∈ youngOpen ν R, ϱ y ≠ 0 := fun y hy => by
        have hp := t9_thr_pos hν hR
        have hy' : rO < ϱ y := hy
        intro h0
        linarith
      have hage : ContDiffOn ℝ 1 (fun y : Space => age R y) (youngOpen ν R) :=
        ContDiffOn.div contDiffOn_const (hϱ1.pow 2) (fun y hy => pow_ne_zero 2 (hne y hy))
      have hνage : ContDiffOn ℝ 1 (fun y : Space => ν * age R y) (youngOpen ν R) :=
        contDiffOn_const.mul hage
      have hχ1 : ContDiff ℝ 1 χy := hχy.smooth.of_le (xd_le_top 1)
      have hdχ1 : ContDiff ℝ 1 (deriv χy) :=
        ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
          (xd_le_top 1)
      have hχA : ContDiffOn ℝ 1 (fun y : Space => χy (ν * age R y)) (youngOpen ν R) :=
        hχ1.comp_contDiffOn hνage
      have hdA : ContDiffOn ℝ 1 (fun y : Space => deriv χy (ν * age R y)) (youngOpen ν R) :=
        hdχ1.comp_contDiffOn hνage
      have hK : ContDiffOn ℝ 1 (fun y : Space => -2 * ν * R ^ 2 / ϱ y ^ 3) (youngOpen ν R) :=
        ContDiffOn.div contDiffOn_const (hϱ1.pow 3) (fun y hy => pow_ne_zero 3 (hne y hy))
      have hcf : ContDiffOn ℝ 1 (fun y : Space =>
          deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y) (youngOpen ν R) :=
        (hdA.mul hK).div hϱ1 hne
      have hZd : DifferentiableOn ℝ (Zd τ) (youngOpen ν R) :=
        xd_Zd_diffOn hν hμ hr0 hP hT hM τ
      have hΨd := xd_Psid_diffOn hν hμ hR hP hT hM haxi τ
      have hform : DifferentiableOn ℝ (fun y : Space =>
          χy (ν * age R y) • Zd τ y +
            (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
              outPrim Zd τ (ϱ y) (y 2)) • coordinateVector 2) (youngOpen ν R) :=
        ((hχA.differentiableOn (by simp)).smul hZd).add
          ((((hcf.differentiableOn (by simp)).mul hΨd).smul_const _))
      refine hform.congr fun y hy => ?_
      have hyr : rO < ϱ y := hy
      have hZt := tcr_hasDerivAt_tau hν hμ hr0 hP hT hM τ hyr
      have hΨt := tcr_outPrim_tau hν hμ hr0 hP hT hM τ hyr
      have hW : HasDerivAt (fun t => W t y)
          (χy (ν * age R y) • Zd τ y +
            (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
              outPrim Zd τ (ϱ y) (y 2)) • coordinateVector 2) τ := by
        show HasDerivAt (fun t => wardStreamCut ν R χy Z t y) _ τ
        unfold wardStreamCut
        exact (hZt.const_smul (χy (ν * age R y))).add ((hΨt.const_mul _).smul_const _)
      exact hW.deriv
    · refine ⟨_, hVo, hyV, ?_⟩
      refine (differentiableOn_const (0 : Space)).congr fun x hx => ?_
      have : (fun t => W t x) = fun _ => (0 : Space) := funext fun t => hV0 t x hx.2
      rw [this]
      simp

end Main

end UnforcedLeray.Short.PartIIIb.Concrete
