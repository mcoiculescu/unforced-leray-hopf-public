import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Comm

/-!
# Transition-annulus derivative bound for `commMain` (`PartIII-b:C/rep/8/1/1/2/5/2/1/1`)

Source `the November 2 reference manuscript`
lines 3700-3712, 4195-4215, 5427-5432. Bounds `‖fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y -
fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y‖` by `C₀ * commMainMaj ν ε r Z₁ Z₂ τ y` on the transition
annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBWidth

open YBComm

/-- Pointwise Fréchet derivative bound for `commMain ν R χy W τ` at an off-axis point `y`. -/
theorem fderiv_commMain_bound {ν R : ℝ} {χy : ℝ → ℝ} (_hχ : IsStreamCutoff χy)
    (W : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (hW : ContDiffAt ℝ 2 (W τ) y)
    {a1 a2 : ℝ} (hA1 : HasDerivAt (tcA1 ν R χy) a1 (ϱ y))
    (hA2 : HasDerivAt (tcA2 ν R χy) a2 (ϱ y)) :
    DifferentiableAt ℝ (commMain ν R χy W τ) y ∧
    ‖fderiv ℝ (commMain ν R χy W τ) y‖ ≤
      |a1| * ‖W τ y‖ +
        (|tcA1 ν R χy (ϱ y)| + |tcA2 ν R χy (ϱ y)| * (2 * (ϱ y)⁻¹) + |a2|) *
          ‖fderiv ℝ (W τ) y‖ +
        |tcA2 ν R χy (ϱ y)| * ‖iteratedFDeriv ℝ 2 (W τ) y‖ := by
  have hna : y ∉ axis := Sub8_1_1_2_3.not_axis_of_pos hy
  have hϱ := hasFDerivAt_ϱ hna
  have hϱn : ‖ϱD y‖ ≤ 1 := wgx_norm_ϱD_le hy
  have hWd : HasFDerivAt (W τ) (fderiv ℝ (W τ) y) y :=
    (hW.differentiableAt (by norm_num)).hasFDerivAt
  have hDW : HasFDerivAt (fderiv ℝ (W τ)) (fderiv ℝ (fderiv ℝ (W τ)) y) y :=
    ((hW.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨rd, hrd, hrdn⟩ := wgy_radialUnit_hasFDerivAt hy
  have hcA1 := hA1.comp_hasFDerivAt y hϱ
  have hcA2 := hA2.comp_hasFDerivAt y hϱ
  have hT1 := hcA1.smul hWd
  have hT2 := hcA2.smul (hDW.clm_apply hrd)
  have hD : HasFDerivAt (commMain ν R χy W τ) _ y := hT1.add hT2
  refine ⟨hD.differentiableAt, ?_⟩
  rw [hD.fderiv]
  set Zd := fderiv ℝ (W τ) y
  set Zdd := fderiv ℝ (fderiv ℝ (W τ)) y
  set Zy := W τ y
  have n1 := wgy_n1 ((tcA1 ν R χy ∘ ϱ) y) a1 Zd Zy (ϱD y) hϱn
  have hru := wgy_radialUnit_norm_le y hy
  have n2 : ‖(tcA2 ν R χy ∘ ϱ) y • (Zd.comp rd + Zdd.flip (radialUnit y)) +
      (a2 • ϱD y).smulRight (Zd (radialUnit y))‖ ≤
      |(tcA2 ν R χy ∘ ϱ) y| * (‖Zd‖ * (2 * (ϱ y)⁻¹) + ‖Zdd‖) + |a2| * ‖Zd‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      gcongr
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left hrdn (norm_nonneg _))
      · calc ‖Zdd.flip (radialUnit y)‖ ≤ ‖Zdd.flip‖ * ‖radialUnit y‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖Zdd‖ * 1 := by rw [ContinuousLinearMap.opNorm_flip]; gcongr
          _ = ‖Zdd‖ := mul_one _
    · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      have h1 : ‖Zd (radialUnit y)‖ ≤ ‖Zd‖ := by
        calc ‖Zd (radialUnit y)‖ ≤ ‖Zd‖ * ‖radialUnit y‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖Zd‖ * 1 := by gcongr
          _ = ‖Zd‖ := mul_one _
      calc |a2| * ‖ϱD y‖ * ‖Zd (radialUnit y)‖ ≤ |a2| * 1 * ‖Zd‖ := by gcongr
        _ = |a2| * ‖Zd‖ := by ring
  have hiter : ‖iteratedFDeriv ℝ 2 (W τ) y‖ = ‖Zdd‖ := by
    rw [← norm_iteratedFDeriv_one, ← norm_iteratedFDeriv_fderiv]
  rw [hiter]
  refine ((norm_add_le _ _).trans (add_le_add n1 n2)).trans ?_
  simp only [Function.comp_apply]
  linarith

/-- Refined transition-annulus bounds on `tcA1`, `tcA2` and their radial derivatives, keeping the
factor `ν` in `tcA2`. -/
theorem coeff_annulus_bounds {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν R : ℝ, 0 < ν → ν ≤ 1 → 1 ≤ R → ∀ s : ℝ,
      R * Real.sqrt ν ≤ s → s ≤ R * Real.sqrt (5 * ν / 4) →
      ∃ a1 a2 : ℝ, HasDerivAt (tcA1 ν R χy) a1 s ∧ HasDerivAt (tcA2 ν R χy) a2 s ∧
        |tcA1 ν R χy s| ≤ C ∧
        |a1| ≤ C * (R * Real.sqrt ν)⁻¹ ∧
        |tcA2 ν R χy s| ≤ C * ν * (R * Real.sqrt ν)⁻¹ ∧
        |tcA2 ν R χy s| * (2 * s⁻¹) ≤ C ∧
        |a2| ≤ C := by
  obtain ⟨C0, hC0, htc⟩ := tcCoeff χy hχ
  obtain ⟨C1, hC1, hder⟩ := wgy_coeff_deriv hχ
  obtain ⟨M, hM0, hprof⟩ := wgyc_profile χy hχ
  refine ⟨C0 + C1 + 4 * M, by positivity, ?_⟩
  intro ν R hν hν1 hR1 r hr1 hr2'
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := by rw [hLdef]; positivity
  have hLsq : ν * R ^ 2 = L ^ 2 := by
    rw [hLdef, mul_pow, Real.sq_sqrt hν.le]; ring
  set u : ℝ := L⁻¹
  have hu0 : 0 < u := inv_pos.2 hL
  have huL : u * L = 1 := inv_mul_cancel₀ hL.ne'
  have hr : 0 < r := lt_of_lt_of_le hL hr1
  have hQ2L : R * Real.sqrt (5 * ν / 4) ≤ 2 * L := by
    rw [hLdef]
    have : Real.sqrt (5 * ν / 4) ≤ 2 * Real.sqrt ν := by
      rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc R * Real.sqrt (5 * ν / 4) ≤ R * (2 * Real.sqrt ν) := by gcongr
      _ = 2 * (R * Real.sqrt ν) := by ring
  have hr2 : r ≤ 2 * L := hr2'.trans hQ2L
  have hur1 : 1 ≤ u * r := by
    calc 1 = u * L := huL.symm
      _ ≤ u * r := by gcongr
  have hur2 : u * r ≤ 2 := by
    calc u * r ≤ u * (2 * L) := by gcongr
      _ = 2 := by rw [mul_left_comm, huL]; ring
  have hνu : ν * u ^ 2 ≤ 1 := by
    have h1 : ν * R ^ 2 * u ^ 2 = 1 := by
      rw [hLsq]
      have : L ^ 2 * u ^ 2 = (u * L) ^ 2 := by ring
      rw [this, huL]; norm_num
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have : ν * u ^ 2 ≤ ν * R ^ 2 * u ^ 2 := by
      have := mul_le_mul_of_nonneg_left hR2 hν.le
      nlinarith [sq_nonneg u]
    linarith
  have hru : r⁻¹ ≤ u := inv_anti₀ hL hr1
  obtain ⟨bA1, -, -, -⟩ := htc ν R hν hν1 hR1 r hr1 hr2'
  obtain ⟨a1, a2, -, -, hA1, hA2, -, -, ba1, -, -, -⟩ := hder ν R hν hν1 hR1 r hr1 hr2
  have hc : tcC0 ν R χy = fun x => 1 * tcC0 1 1 χy (u * x) := by
    funext x; rw [one_mul]; exact congrFun (wgyc_c_scale ν R χy hL hLsq) x
  have hc1 : deriv (tcC0 ν R χy) = fun x => 1 * (u * deriv (tcC0 1 1 χy) (u * x)) := by
    rw [hc]; exact wgyc_e1 _ _ _
  have hc2 : deriv (deriv (tcC0 ν R χy)) =
      fun x => 1 * (u * (u * deriv (deriv (tcC0 1 1 χy)) (u * x))) := by
    rw [hc1]; exact wgyc_e2 _ _ _
  obtain ⟨m1, m2, -⟩ := hprof (u * r) ⟨hur1, hur2⟩
  have bc1 : |deriv (tcC0 ν R χy) r| ≤ M * u := by
    rw [hc1]; simp only [one_mul]; rw [abs_mul, abs_of_pos hu0]
    calc u * |deriv (tcC0 1 1 χy) (u * r)| ≤ u * M := by gcongr
      _ = M * u := by ring
  have bc2 : |deriv (deriv (tcC0 ν R χy)) r| ≤ M * u ^ 2 := by
    rw [hc2]; simp only [one_mul]; rw [abs_mul, abs_mul, abs_of_pos hu0]
    calc u * (u * |deriv (deriv (tcC0 1 1 χy)) (u * r)|) ≤ u * (u * M) := by gcongr
      _ = M * u ^ 2 := by ring
  have bA2 : |tcA2 ν R χy r| ≤ 2 * M * ν * u := by
    unfold tcA2
    rw [abs_mul, abs_mul, abs_of_pos hν]
    have : |(-2 : ℝ)| = 2 := by norm_num
    rw [this]
    calc 2 * ν * |deriv (tcC0 ν R χy) r| ≤ 2 * ν * (M * u) := by gcongr
      _ = 2 * M * ν * u := by ring
  have hmem : Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds hr
  have cd0 := Sub8_1_1_2_3.tcC0_cdOn (ν := ν) (R := R) hχ
  have cd1 := Sub8_1_1_2_3.cdOn_deriv cd0
  have hC1_diff : DifferentiableAt ℝ (deriv (tcC0 ν R χy)) r :=
    (cd1.contDiffAt hmem).differentiableAt (by simp)
  have hA2' : HasDerivAt (tcA2 ν R χy) (-2 * ν * deriv (deriv (tcC0 ν R χy)) r) r :=
    hC1_diff.hasDerivAt.const_mul (-2 * ν)
  have ha2_eq : a2 = -2 * ν * deriv (deriv (tcC0 ν R χy)) r := hA2.unique hA2'
  have ba2' : |a2| ≤ 2 * M := by
    rw [ha2_eq, abs_mul, abs_mul, abs_of_pos hν]
    have : |(-2 : ℝ)| = 2 := by norm_num
    rw [this]
    calc 2 * ν * |deriv (deriv (tcC0 ν R χy)) r| ≤ 2 * ν * (M * u ^ 2) := by gcongr
      _ = 2 * M * (ν * u ^ 2) := by ring
      _ ≤ 2 * M * 1 := by gcongr
      _ = 2 * M := by ring
  have bA2_inv : |tcA2 ν R χy r| * (2 * r⁻¹) ≤ 4 * M := by
    have hr0 : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
    calc |tcA2 ν R χy r| * (2 * r⁻¹) ≤ (2 * M * ν * u) * (2 * u) := by gcongr
      _ = 4 * M * (ν * u ^ 2) := by ring
      _ ≤ 4 * M * 1 := by gcongr
      _ = 4 * M := by ring
  refine ⟨a1, a2, hA1, hA2, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · calc |a1| ≤ C1 * u := ba1
      _ ≤ (C0 + C1 + 4 * M) * u := by nlinarith
  · calc |tcA2 ν R χy r| ≤ 2 * M * ν * u := bA2
      _ ≤ (C0 + C1 + 4 * M) * ν * u := by nlinarith [mul_nonneg hν.le hu0.le]
  · linarith
  · linarith

/-- Difference of `commMain` derivatives on the transition annulus is bounded by `commMainMaj`. -/
theorem fderiv_commMain_sub_le {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ ν ε : ℝ, 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
        ∀ (Z₁ Z₂ : ℝ → Space → Space) (τ : ℝ) (xo : Space),
          ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ContDiffAt ℝ 2 (Z₁ τ) (ε⁻¹ • xo) →
          ContDiffAt ℝ 2 (Z₂ τ) (ε⁻¹ • xo) →
          let y := ε⁻¹ • xo
          let r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
          ‖fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y‖ ≤
            C₀ * commMainMaj ν ε r Z₁ Z₂ τ y := by
  obtain ⟨C, hC0, hC⟩ := coeff_annulus_bounds hχ
  refine ⟨3 * C, by positivity, ?_⟩
  intro ν ε hν hν1 hε hε1 Z₁ Z₂ τ xo hxo1 hxo2 hZ₁ hZ₂ y r
  have hr_sq : r ^ 2 = xo 0 ^ 2 + xo 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hr_pos : 0 < r := Real.sqrt_pos.2 (lt_of_lt_of_le hν hxo1)
  have hr1 : Real.sqrt ν ≤ r := Real.sqrt_le_sqrt hxo1
  have hr2 : r ≤ Real.sqrt (5 * ν / 4) := Real.sqrt_le_sqrt hxo2
  have hR1 : 1 ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε, hε1⟩
  have hR_pos : 0 < ε⁻¹ := inv_pos.2 hε
  have hy_rho : ϱ y = ε⁻¹ * r := by
    change ϱ (ε⁻¹ • xo) = ε⁻¹ * r
    rw [ϱ_smul, abs_of_pos hR_pos]
    rfl
  have hs1 : ε⁻¹ * Real.sqrt ν ≤ ϱ y := by rw [hy_rho]; gcongr
  have hs2 : ϱ y ≤ ε⁻¹ * Real.sqrt (5 * ν / 4) := by rw [hy_rho]; gcongr
  have hy_pos : 0 < ϱ y := by rw [hy_rho]; positivity
  obtain ⟨a1, a2, hA1, hA2, bA1, ba1, bA2, bA2_inv, ba2⟩ :=
    hC ν ε⁻¹ hν hν1 hR1 (ϱ y) hs1 hs2
  set W : ℝ → Space → Space := fun t y' => Z₁ t y' - Z₂ t y' with hWdef
  have hW_cd : ContDiffAt ℝ 2 (W τ) y := hZ₁.sub hZ₂
  obtain ⟨hW_diff, hW_bnd⟩ := fderiv_commMain_bound hχ W τ hy_pos hW_cd hA1 hA2
  obtain ⟨hZ1_diff, -⟩ := fderiv_commMain_bound hχ Z₁ τ hy_pos hZ₁ hA1 hA2
  obtain ⟨hZ2_diff, -⟩ := fderiv_commMain_bound hχ Z₂ τ hy_pos hZ₂ hA1 hA2
  have hev1 : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (Z₁ τ) y' := hZ₁.eventually (by simp)
  have hev2 : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (Z₂ τ) y' := hZ₂.eventually (by simp)
  have heq : (fun y' => commMain ν ε⁻¹ χy Z₁ τ y' - commMain ν ε⁻¹ χy Z₂ τ y') =ᶠ[𝓝 y]
      commMain ν ε⁻¹ χy W τ := by
    filter_upwards [hev1, hev2] with y' h1 h2
    have d1 : DifferentiableAt ℝ (Z₁ τ) y' := h1.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (Z₂ τ) y' := h2.differentiableAt (by norm_num)
    unfold commMain
    have hfd : fderiv ℝ (W τ) y' = fderiv ℝ (Z₁ τ) y' - fderiv ℝ (Z₂ τ) y' :=
      fderiv_sub d1 d2
    rw [hfd, sub_apply, smul_sub, smul_sub]
    abel
  have hfd_sub : fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y =
      fderiv ℝ (commMain ν ε⁻¹ χy W τ) y := by
    rw [← fderiv_sub hZ1_diff hZ2_diff]
    exact heq.fderiv_eq
  rw [hfd_sub]
  have hW0 : W τ y = Z₁ τ y - Z₂ τ y := rfl
  have hW1 : fderiv ℝ (W τ) y = fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y :=
    fderiv_sub (hZ₁.differentiableAt (by norm_num)) (hZ₂.differentiableAt (by norm_num))
  have hW2 : iteratedFDeriv ℝ 2 (W τ) y =
      iteratedFDeriv ℝ 2 (Z₁ τ) y - iteratedFDeriv ℝ 2 (Z₂ τ) y :=
    iteratedFDeriv_sub_apply hZ₁ hZ₂
  rw [hW0, hW1, hW2] at hW_bnd
  have hr2ν : r ≤ 2 * Real.sqrt ν := by
    refine hr2.trans ?_
    rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv_le : (ε⁻¹ * Real.sqrt ν)⁻¹ ≤ 2 * (ε * r⁻¹) := by
    rw [mul_inv, inv_inv]
    have h1 : (Real.sqrt ν)⁻¹ ≤ 2 * r⁻¹ := by
      rw [inv_le_iff_one_le_mul₀' (Real.sqrt_pos.2 hν)]
      have : r * r⁻¹ = 1 := mul_inv_cancel₀ hr_pos.ne'
      calc (1 : ℝ) = r * r⁻¹ := this.symm
        _ ≤ (2 * Real.sqrt ν) * r⁻¹ := by gcongr
        _ = Real.sqrt ν * (2 * r⁻¹) := by ring
    calc ε * (Real.sqrt ν)⁻¹ ≤ ε * (2 * r⁻¹) := by gcongr
      _ = 2 * (ε * r⁻¹) := by ring
  have ba1' : |a1| ≤ 2 * C * (ε * r⁻¹) := by
    calc |a1| ≤ C * (ε⁻¹ * Real.sqrt ν)⁻¹ := ba1
      _ ≤ C * (2 * (ε * r⁻¹)) := by gcongr
      _ = 2 * C * (ε * r⁻¹) := by ring
  have bA2' : |tcA2 ν ε⁻¹ χy (ϱ y)| ≤ 2 * C * (ν * ε * r⁻¹) := by
    calc |tcA2 ν ε⁻¹ χy (ϱ y)| ≤ C * ν * (ε⁻¹ * Real.sqrt ν)⁻¹ := bA2
      _ ≤ C * ν * (2 * (ε * r⁻¹)) := by gcongr
      _ = 2 * C * (ν * ε * r⁻¹) := by ring
  have bmid : |tcA1 ν ε⁻¹ χy (ϱ y)| + |tcA2 ν ε⁻¹ χy (ϱ y)| * (2 * (ϱ y)⁻¹) + |a2| ≤ 3 * C := by
    linarith
  set N0 := ‖Z₁ τ y - Z₂ τ y‖
  set N1 := ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖
  set N2 := ‖iteratedFDeriv ℝ 2 (Z₁ τ) y - iteratedFDeriv ℝ 2 (Z₂ τ) y‖
  have hN0 : 0 ≤ N0 := norm_nonneg _
  have hN1 : 0 ≤ N1 := norm_nonneg _
  have hN2 : 0 ≤ N2 := norm_nonneg _
  have t0 : |a1| * N0 ≤ 2 * C * (ε * r⁻¹) * N0 := by gcongr
  have t1 : (|tcA1 ν ε⁻¹ χy (ϱ y)| + |tcA2 ν ε⁻¹ χy (ϱ y)| * (2 * (ϱ y)⁻¹) + |a2|) * N1 ≤
      3 * C * N1 := by gcongr
  have t2 : |tcA2 ν ε⁻¹ χy (ϱ y)| * N2 ≤ 2 * C * (ν * ε * r⁻¹) * N2 := by gcongr
  have hpos0 : 0 ≤ C * (ε * r⁻¹ * N0) := by positivity
  have hpos2 : 0 ≤ C * (ν * ε * r⁻¹ * N2) := by positivity
  unfold commMainMaj
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete.YBWidth
