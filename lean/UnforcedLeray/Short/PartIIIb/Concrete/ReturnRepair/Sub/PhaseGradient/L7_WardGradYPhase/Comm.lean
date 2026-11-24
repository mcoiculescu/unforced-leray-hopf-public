import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Coeff

/-!
# `PartIII-b:C/rep/2/7`, the derivative of the explicit commutator `tcComm`

Source `the November 2 reference manuscript` 3700-3712, 4203-4214.
On the transition annulus `L ≤ ϱ ≤ 2L`,
`‖D tcComm‖ ≤ C (L⁻¹‖Z‖ + ‖DZ‖ + L⁻¹‖D²Z‖ + L⁻²‖DZ‖ + L⁻³|Ψ_Z|)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `v ↦ (v₀, v₁, 0)` as a linear map. -/
def wgyW : Space →ₗ[ℝ] Space where
  toFun v := (!₂[v 0, v 1, 0] : Space)
  map_add' v w := by
    ext i; fin_cases i <;> simp
  map_smul' c v := by
    ext i; fin_cases i <;> simp

def wgyWL : Space →L[ℝ] Space := LinearMap.toContinuousLinearMap wgyW

theorem wgyWL_apply (v : Space) : wgyWL v = (!₂[v 0, v 1, 0] : Space) := rfl

theorem wgy_norm_sq (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

theorem wgyWL_norm_le (v : Space) : ‖wgyWL v‖ ≤ ‖v‖ := by
  have h1 : ‖wgyWL v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [wgyWL_apply, wgy_norm_sq]; simp
  have h2 := wgy_norm_sq v
  have : ‖wgyWL v‖ ^ 2 ≤ ‖v‖ ^ 2 := by rw [h1, h2]; nlinarith [sq_nonneg (v 2)]
  exact abs_le_of_sq_le_sq' this (norm_nonneg _) |>.2 |> fun h => by
    simpa [abs_of_nonneg (norm_nonneg _)] using h

theorem wgyW_norm_eq (y : Space) : ‖wgyWL y‖ = ϱ y := by
  have h1 : ‖wgyWL y‖ ^ 2 = ϱ y ^ 2 := by
    rw [wgyWL_apply, wgy_norm_sq, ϱ_sq]; simp
  have := (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 h1
  exact this

theorem wgy_radialUnit_eq (y : Space) : radialUnit y = (ϱ y)⁻¹ • wgyWL y := rfl

theorem wgy_radialUnit_hasFDerivAt {y : Space} (hy : 0 < ϱ y) :
    ∃ rd : Space →L[ℝ] Space, HasFDerivAt radialUnit rd y ∧ ‖rd‖ ≤ 2 * (ϱ y)⁻¹ := by
  have hna : y ∉ axis := fun h => by
    have := (mem_axis_iff y).1 h
    linarith
  have hϱ := hasFDerivAt_ϱ hna
  have hinv : HasFDerivAt (fun y' => (ϱ y')⁻¹) (-((ϱ y ^ 2)⁻¹ • ϱD y)) y := by
    have := (hasDerivAt_inv hy.ne').comp_hasFDerivAt y hϱ
    simpa [Function.comp_def] using this
  have hw : HasFDerivAt (fun y' => wgyWL y') wgyWL y := wgyWL.hasFDerivAt
  have h := hinv.smul hw
  refine ⟨_, h, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  have hv := wgx_ϱD_le hy v
  have e1 : ‖(ϱ y)⁻¹ • wgyWL v‖ ≤ (ϱ y)⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy)]
    exact mul_le_mul_of_nonneg_left (wgyWL_norm_le v) (by positivity)
  have e2 : ‖(-((ϱ y ^ 2)⁻¹ * ϱD y v)) • wgyWL y‖ ≤ (ϱ y)⁻¹ * ‖v‖ := by
    rw [norm_smul, wgyW_norm_eq, Real.norm_eq_abs, abs_neg, abs_mul,
      abs_of_pos (inv_pos.2 (pow_pos hy 2))]
    calc (ϱ y ^ 2)⁻¹ * |ϱD y v| * ϱ y ≤ (ϱ y ^ 2)⁻¹ * ‖v‖ * ϱ y := by gcongr
      _ = (ϱ y)⁻¹ * ‖v‖ := by field_simp
  refine (norm_add_le _ _).trans ?_
  linarith [e1, e2]

theorem wgy_radialUnit_norm_le (y : Space) (hy : 0 < ϱ y) : ‖radialUnit y‖ ≤ 1 := by
  rw [wgy_radialUnit_eq, norm_smul, wgyW_norm_eq, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy),
    inv_mul_cancel₀ hy.ne']

lemma wgy_n1 (A a : ℝ) (Zd : Space →L[ℝ] Space) (z : Space) (ϱd : Space →L[ℝ] ℝ)
    (hϱd : ‖ϱd‖ ≤ 1) :
    ‖A • Zd + (a • ϱd).smulRight z‖ ≤ |A| * ‖Zd‖ + |a| * ‖z‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
  · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    calc |a| * ‖ϱd‖ * ‖z‖ ≤ |a| * 1 * ‖z‖ := by gcongr
      _ = |a| * ‖z‖ := by ring

lemma wgy_n3 (B1 b1 B2 b2 Ψ z2 : ℝ) (Ψd : Space →L[ℝ] ℝ) (zd2 : Space →L[ℝ] ℝ)
    (ϱd : Space →L[ℝ] ℝ) (hϱd : ‖ϱd‖ ≤ 1) :
    ‖((B1 • Ψd + Ψ • (b1 • ϱd)) + (B2 • zd2 + z2 • (b2 • ϱd)) : Space →L[ℝ] ℝ)‖ ≤
      |B1| * ‖Ψd‖ + |Ψ| * |b1| + (|B2| * ‖zd2‖ + |z2| * |b2|) := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← mul_assoc]
      calc |Ψ| * |b1| * ‖ϱd‖ ≤ |Ψ| * |b1| * 1 := by gcongr
        _ = |Ψ| * |b1| := mul_one _
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← mul_assoc]
      calc |z2| * |b2| * ‖ϱd‖ ≤ |z2| * |b2| * 1 := by gcongr
        _ = |z2| * |b2| := mul_one _

set_option maxHeartbeats 1600000 in
theorem wgy_comm_fderiv_bound {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → ∀ (Z : ℝ → Space → Space) (τ : ℝ)
      (y : Space) (Ψd : Space →L[ℝ] ℝ), y ∈ streamAnn ν R → ContDiffAt ℝ 2 (Z τ) y →
      HasFDerivAt (fun y' => outPrim Z τ (ϱ y') (y' 2)) Ψd y →
      ‖Ψd‖ ≤ 4 * (R * Real.sqrt ν) * ‖Z τ y‖ →
      DifferentiableAt ℝ (tcComm ν R χ Z τ) y ∧
      ‖fderiv ℝ (tcComm ν R χ Z τ) y‖ ≤
        C * ((R * Real.sqrt ν)⁻¹ * ‖Z τ y‖ + ‖fderiv ℝ (Z τ) y‖ +
          (R * Real.sqrt ν)⁻¹ * ‖fderiv ℝ (fderiv ℝ (Z τ)) y‖ +
          ((R * Real.sqrt ν)⁻¹) ^ 2 * ‖fderiv ℝ (Z τ) y‖ +
          ((R * Real.sqrt ν)⁻¹) ^ 3 * |outPrim Z τ (ϱ y) (y 2)|) := by
  obtain ⟨C0, hC0, hcoef⟩ := tcCoeff χ hχ
  obtain ⟨C1, hC1, hder⟩ := wgy_coeff_deriv hχ
  refine ⟨6 * (C0 + C1), by positivity, ?_⟩
  intro ν R hν hν1 hR1 Z τ y Ψd hyann hZ hΨ hΨn
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hL : 0 < L := by rw [hLdef]; positivity
  obtain ⟨hr1, hr2'⟩ := hyann
  have hQ2L : R * Real.sqrt (5 * ν / 4) ≤ 2 * L := by
    rw [hLdef]
    have : Real.sqrt (5 * ν / 4) ≤ 2 * Real.sqrt ν := by
      rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc R * Real.sqrt (5 * ν / 4) ≤ R * (2 * Real.sqrt ν) := by gcongr
      _ = 2 * (R * Real.sqrt ν) := by ring
  have hr2 : ϱ y ≤ 2 * L := hr2'.trans hQ2L
  have hy : 0 < ϱ y := lt_of_lt_of_le hL hr1
  have hna : y ∉ axis := fun h => by
    have := (mem_axis_iff y).1 h
    linarith
  set s : ℝ := L⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 hL
  have hsL : s * L = 1 := inv_mul_cancel₀ hL.ne'
  have hys : (ϱ y)⁻¹ ≤ s := inv_anti₀ hL hr1
  obtain ⟨cA1, cA2, cB1, cB2⟩ := hcoef ν R hν hν1 hR1 (ϱ y) hr1 hr2'
  obtain ⟨a1, a2, b1, b2, hA1, hA2, hB1, hB2, ba1, ba2, bb1, bb2⟩ :=
    hder ν R hν hν1 hR1 (ϱ y) hr1 hr2
  have hϱ := hasFDerivAt_ϱ hna
  have hϱn : ‖ϱD y‖ ≤ 1 := wgx_norm_ϱD_le hy
  have hZd : HasFDerivAt (Z τ) (fderiv ℝ (Z τ) y) y :=
    (hZ.differentiableAt (by norm_num)).hasFDerivAt
  have hDZ : HasFDerivAt (fderiv ℝ (Z τ)) (fderiv ℝ (fderiv ℝ (Z τ)) y) y :=
    ((hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨rd, hrd, hrdn⟩ := wgy_radialUnit_hasFDerivAt hy
  have hz2 : HasFDerivAt (fun y' => Z τ y' 2)
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp (fderiv ℝ (Z τ) y)) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZd
  have hcA1 := hA1.comp_hasFDerivAt y hϱ
  have hcA2 := hA2.comp_hasFDerivAt y hϱ
  have hcB1 := hB1.comp_hasFDerivAt y hϱ
  have hcB2 := hB2.comp_hasFDerivAt y hϱ
  have hT1 := hcA1.smul hZd
  have hT2 := hcA2.smul (hDZ.clm_apply hrd)
  have hT3 := (((hcB1.mul hΨ).add (hcB2.mul hz2))).smul_const (coordinateVector 2)
  have hD := (hT1.add hT2).add hT3
  have hD' : HasFDerivAt (tcComm ν R χ Z τ) _ y := hD
  refine ⟨hD'.differentiableAt, ?_⟩
  rw [hD'.fderiv]
  have hec : ‖(coordinateVector 2 : Space)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  set Zd := fderiv ℝ (Z τ) y with hZddef
  set Zdd := fderiv ℝ (fderiv ℝ (Z τ)) y with hZdddef
  set Zy := Z τ y with hZydef
  set Ψy := outPrim Z τ (ϱ y) (y 2) with hΨy
  have n1 := wgy_n1 ((tcA1 ν R χ ∘ ϱ) y) a1 Zd Zy (ϱD y) hϱn
  have n3 := wgy_n3 ((tcB1 ν R χ ∘ ϱ) y) b1 ((tcB2 ν R χ ∘ ϱ) y) b2 Ψy (Zy 2) Ψd
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp Zd) (ϱD y) hϱn
  have hru := wgy_radialUnit_norm_le y hy
  have n2 : ‖(tcA2 ν R χ ∘ ϱ) y • (Zd.comp rd + Zdd.flip (radialUnit y)) +
      (a2 • ϱD y).smulRight (Zd (radialUnit y))‖ ≤
      |(tcA2 ν R χ ∘ ϱ) y| * (‖Zd‖ * ‖rd‖ + ‖Zdd‖) + |a2| * ‖Zd‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      gcongr
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact ContinuousLinearMap.opNorm_comp_le _ _
      · calc ‖Zdd.flip (radialUnit y)‖ ≤ ‖Zdd.flip‖ * ‖radialUnit y‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖Zdd‖ * 1 := by
              rw [ContinuousLinearMap.opNorm_flip]; gcongr
          _ = ‖Zdd‖ := mul_one _
    · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      have h1 : ‖Zd (radialUnit y)‖ ≤ ‖Zd‖ := by
        calc ‖Zd (radialUnit y)‖ ≤ ‖Zd‖ * ‖radialUnit y‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖Zd‖ * 1 := by gcongr
          _ = ‖Zd‖ := mul_one _
      calc |a2| * ‖ϱD y‖ * ‖Zd (radialUnit y)‖ ≤ |a2| * 1 * ‖Zd‖ := by gcongr
        _ = |a2| * ‖Zd‖ := by ring
  have n3' : ‖((tcB1 ν R χ ∘ ϱ) y • Ψd + Ψy • b1 • ϱD y +
      ((tcB2 ν R χ ∘ ϱ) y • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp Zd +
        Zy 2 • b2 • ϱD y)).smulRight (coordinateVector 2)‖ ≤
      |(tcB1 ν R χ ∘ ϱ) y| * ‖Ψd‖ + |Ψy| * |b1| +
        (|(tcB2 ν R χ ∘ ϱ) y| * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp Zd‖ +
          |Zy 2| * |b2|) := by
    rw [ContinuousLinearMap.norm_smulRight_apply, hec, mul_one]
    exact n3
  have key := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add n1 n2)) n3')
  refine key.trans ?_
  have hprojn : ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp Zd‖ ≤ ‖Zd‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, Real.norm_eq_abs]
    exact (wgx_abs_apply_le _ 2).trans (Zd.le_opNorm v)
  have hz2n : |Zy 2| ≤ ‖Zy‖ := wgx_abs_apply_le _ 2
  have hrd2 : ‖rd‖ ≤ 2 * s := by
    refine hrdn.trans ?_
    linarith
  have hΨn' : ‖Ψd‖ ≤ 4 * L * ‖Zy‖ := hΨn
  have z0 : 0 ≤ ‖Zd‖ := norm_nonneg _
  have z1 : 0 ≤ ‖Zy‖ := norm_nonneg _
  have z2 : 0 ≤ ‖Zdd‖ := ContinuousLinearMap.opNorm_nonneg _
  have z3 : 0 ≤ |Ψy| := abs_nonneg _
  have hcA1' : |(tcA1 ν R χ ∘ ϱ) y| ≤ C0 := cA1
  have hcA2' : |(tcA2 ν R χ ∘ ϱ) y| ≤ C0 * s := cA2
  have hcB1' : |(tcB1 ν R χ ∘ ϱ) y| ≤ C0 * s ^ 2 := cB1
  have hcB2' : |(tcB2 ν R χ ∘ ϱ) y| ≤ C0 := cB2
  have t1 : |(tcA1 ν R χ ∘ ϱ) y| * ‖Zd‖ ≤ C0 * ‖Zd‖ := by gcongr
  have t2 : |a1| * ‖Zy‖ ≤ C1 * s * ‖Zy‖ := by gcongr
  have t3 : |(tcA2 ν R χ ∘ ϱ) y| * (‖Zd‖ * ‖rd‖ + ‖Zdd‖) ≤
      C0 * s * (‖Zd‖ * (2 * s) + ‖Zdd‖) := by gcongr
  have t4 : |a2| * ‖Zd‖ ≤ C1 * s ^ 2 * ‖Zd‖ := by gcongr
  have t5 : |(tcB1 ν R χ ∘ ϱ) y| * ‖Ψd‖ ≤ C0 * s ^ 2 * (4 * L * ‖Zy‖) := by gcongr
  have t5' : C0 * s ^ 2 * (4 * L * ‖Zy‖) = 4 * C0 * s * ‖Zy‖ := by
    calc C0 * s ^ 2 * (4 * L * ‖Zy‖) = 4 * C0 * s * ‖Zy‖ * (s * L) := by ring
      _ = 4 * C0 * s * ‖Zy‖ := by rw [hsL, mul_one]
  have t6 : |Ψy| * |b1| ≤ |Ψy| * (C1 * s ^ 3) := by gcongr
  have t7 : |(tcB2 ν R χ ∘ ϱ) y| * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp Zd‖ ≤
      C0 * ‖Zd‖ := by gcongr
  have t8 : |Zy 2| * |b2| ≤ ‖Zy‖ * (C1 * s) := by gcongr
  have p1 : 0 ≤ C0 * ‖Zd‖ := by positivity
  have p2 : 0 ≤ C1 * ‖Zd‖ := by positivity
  have p3 : 0 ≤ C0 * s ^ 2 * ‖Zd‖ := by positivity
  have p4 : 0 ≤ C1 * s ^ 2 * ‖Zd‖ := by positivity
  have p5 : 0 ≤ C0 * s * ‖Zy‖ := by positivity
  have p6 : 0 ≤ C1 * s * ‖Zy‖ := by positivity
  have p7 : 0 ≤ C0 * s * ‖Zdd‖ := by positivity
  have p8 : 0 ≤ C1 * s * ‖Zdd‖ := by positivity
  have p9 : 0 ≤ C0 * s ^ 3 * |Ψy| := by positivity
  have p10 : 0 ≤ C1 * s ^ 3 * |Ψy| := by positivity
  linarith [t1, t2, t3, t4, t5, t5', t6, t7, t8, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]

end UnforcedLeray.Short.PartIIIb.Concrete

end
