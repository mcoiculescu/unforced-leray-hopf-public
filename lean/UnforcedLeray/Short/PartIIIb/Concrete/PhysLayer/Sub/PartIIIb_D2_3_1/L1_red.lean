import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3_1

/-!
# `WardX0FarBound` from the smoothness and far-field leaves (`PartIII-b:IIIb-D2/3/1/3/1/1/L1`)

Source of record: `the November 2 reference manuscript` 4156-4186, 3604-3621.
The old source is replaced by its separated representative `T'` (`OldSourceReg`).  For
`ρ ≥ 2 r_o` the far-field decay `SepFarDecay` bounds `W_μ` and `∇W_μ` by `C ϱ^{-3}`; on the
compact range `r < ρ ≤ 2 r_o` the continuity of `wardX0` and `fderiv wardX0` (from
`wardX0Smooth_of`) gives the bound.  Both regimes are `ρ · (·) ≤ C ρ^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma wardFar_re_sub_le (a b : ℂ) : ‖(a - b).re‖ ≤ ‖a‖ + ‖b‖ := by
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (norm_sub_le _ _)

lemma wardFar_proj_fderiv (F : Space → Space) (y v : Space) (i : Fin 3)
    (hF : DifferentiableAt ℝ F y) :
    fderiv ℝ (fun x => F x i) y v = fderiv ℝ F y v i := by
  have h : HasFDerivAt (fun x => F x i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ F y)) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hF.hasFDerivAt
  rw [h.fderiv]
  rfl

lemma wardFar_re_fderiv_le (g h : Space → ℂ) (y v : Space)
    (hg : DifferentiableAt ℝ g y) (hh : DifferentiableAt ℝ h y) :
    ‖fderiv ℝ (fun x => (g x - h x).re) y v‖ ≤
      (‖fderiv ℝ g y‖ + ‖fderiv ℝ h y‖) * ‖v‖ := by
  have hd : HasFDerivAt (fun x => (g x - h x).re)
      (Complex.reCLM.comp (fderiv ℝ g y - fderiv ℝ h y)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hg.hasFDerivAt.sub hh.hasFDerivAt)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, Complex.reCLM_apply]
  rw [Real.norm_eq_abs]
  calc |(fderiv ℝ g y v - fderiv ℝ h y v).re|
      ≤ ‖fderiv ℝ g y v - fderiv ℝ h y v‖ := Complex.abs_re_le_norm _
    _ ≤ ‖fderiv ℝ g y v‖ + ‖fderiv ℝ h y v‖ := norm_sub_le _ _
    _ ≤ ‖fderiv ℝ g y‖ * ‖v‖ + ‖fderiv ℝ h y‖ * ‖v‖ :=
        add_le_add ((fderiv ℝ g y).le_opNorm v) ((fderiv ℝ h y).le_opNorm v)
    _ = (‖fderiv ℝ g y‖ + ‖fderiv ℝ h y‖) * ‖v‖ := by ring

lemma wardFar_varrho (a b : ℝ) (ha : 0 ≤ a) : ϱ (!₂[a, 0, b] : Space) = a := by
  unfold ϱ
  simp [Real.sqrt_sq ha]

lemma wardFar_arith (ρ K C X : ℝ) (hρ : 0 < ρ) (hK : K ≤ C) (hX : |X| ≤ K * ρ ^ (-3:ℝ)) :
    ‖ρ * X‖ ≤ C * ρ ^ (-(2:ℝ)) := by
  have hpow : ρ ^ (-(2:ℝ)) = ρ ^ (-(3:ℝ)) * ρ := by
    rw [← Real.rpow_add_one hρ.ne']
    norm_num
  have hnn : 0 ≤ ρ ^ (-(3:ℝ)) * ρ := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ, hpow]
  calc ρ * |X| ≤ ρ * (K * ρ ^ (-(3:ℝ))) := mul_le_mul_of_nonneg_left hX hρ.le
    _ = K * (ρ ^ (-(3:ℝ)) * ρ) := by ring
    _ ≤ C * (ρ ^ (-(3:ℝ)) * ρ) := mul_le_mul_of_nonneg_right hK hnn

lemma wardFar_small_bound (ρ R M X : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R) (hM : 0 ≤ M)
    (hX : |X| ≤ M) : |X| ≤ (R ^ 3 * M) * ρ ^ (-(3:ℝ)) := by
  have hneg : ρ ^ (-(3:ℝ)) = (ρ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hρ.le]
    congr 1
    exact_mod_cast Real.rpow_natCast ρ 3
  have h3 : ρ ^ 3 ≤ R ^ 3 := by gcongr
  have hp : 0 < ρ ^ 3 := by positivity
  rw [hneg]
  calc |X| ≤ M := hX
    _ = (M * ρ ^ 3) * (ρ ^ 3)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hp.ne', mul_one]
    _ ≤ (M * R ^ 3) * (ρ ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hM) (inv_nonneg.mpr hp.le)
    _ = (R ^ 3 * M) * (ρ ^ 3)⁻¹ := by ring

theorem wardX0FarBound_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hreg : OldSourceReg c mZ ρb γ ν ε hχo) (hfar : SepFarDecay) (hW : SepWSmoothOn) :
    WardX0FarBound c mZ ρb γ ν ε μ hχo := by
  intro hc hρb hmZ hν hε hμ T g₁ g₂ e₁ e₂ τ r z hr
  obtain ⟨P, T', hP, hS, hM, hEq, -⟩ := hreg hc hρb hmZ hν hε T g₁ g₂ e₁ e₂
  have hr0pos : 0 < ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
  set r0 : ℝ := ε⁻¹ * Real.sqrt (5 * ν / 6) with hr0def
  have hμ' : -(1 / 4 : ℝ) < ((μ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    exact hμ
  have hμ1 : -(1 / 4 : ℝ) < (((μ : ℝ) : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hSm : ContDiffOn ℝ 2 (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) (youngOpen ν ε⁻¹) :=
    wardX0Smooth_of c mZ ρb γ ν ε μ hχo hreg hW hc hρb hmZ hν hε hμ T g₁ g₂ e₁ e₂ τ
  have hOpen : IsOpen (youngOpen ν ε⁻¹) := by
    unfold youngOpen
    exact isOpen_lt continuous_const Axi.continuous_ϱ
  have hG : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T' y τ i)
      (youngOpen ν ε⁻¹) :=
    fun i => hW ν (μ : ℂ) r0 P T' hν hμ' hr0pos.le hP hS hM τ i
  have hH : ∀ i : Fin 3, ContDiffOn ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i)
      (youngOpen ν ε⁻¹) :=
    fun i => hW ν ((μ : ℂ) + 1) r0 P T' hν hμ1 hr0pos.le hP hS hM τ i
  have K1 : ∀ (y : Space) (i : Fin 3),
      wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y i =
        (IIIa.sepW ν (μ : ℂ) T' y τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i).re := by
    intro y i
    simp only [wardX0, hEq, PiLp.toLp_apply]
  have hFd : ∀ y : Space, y ∈ youngOpen ν ε⁻¹ →
      DifferentiableAt ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y := fun y hy =>
    (hSm.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hGd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν ε⁻¹ →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν (μ : ℂ) T' x τ i) y := fun i y hy =>
    ((hG i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hHd : ∀ (i : Fin 3) (y : Space), y ∈ youngOpen ν ε⁻¹ →
      DifferentiableAt ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i) y := fun i y hy =>
    ((hH i).contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have Dcomp : ∀ (y v : Space) (i : Fin 3), y ∈ youngOpen ν ε⁻¹ →
      fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y v i =
        fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T' x τ i
          - IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i).re) y v := by
    intro y v i hy
    have hfun : (fun x => wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ x i) =
        (fun x => (IIIa.sepW ν (μ : ℂ) T' x τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' x τ i).re) :=
      funext fun x => K1 x i
    rw [← wardFar_proj_fderiv _ y v i (hFd y hy), hfun]
  have Vbound : ∀ (y : Space) (i : Fin 3),
      ‖wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y i‖ ≤
        ‖IIIa.sepW ν (μ : ℂ) T' y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i‖ := by
    intro y i
    rw [K1 y i]
    exact wardFar_re_sub_le _ _
  obtain ⟨C1, hC1⟩ := hfar ν (μ : ℂ) r0 P T' hν hμ' hr0pos.le hP hS hM τ
  obtain ⟨C2, hC2⟩ := hfar ν ((μ : ℂ) + 1) r0 P T' hν hμ1 hr0pos.le hP hS hM τ
  have hcv : ‖coordinateVector (2 : Fin 3)‖ = 1 := by
    first
    | exact UnforcedLeray.RieszLp.norm_coordinateVector 2
    | simp [coordinateVector]
  have hLval : ∀ (y : Space) (i : Fin 3), y ∈ youngOpen ν ε⁻¹ → 2 * r0 ≤ ϱ y →
      |wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y i| ≤ (C1 + C2) * ϱ y ^ (-3:ℝ) := by
    intro y i _ h2
    calc |wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y i|
        = ‖wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖IIIa.sepW ν (μ : ℂ) T' y τ i‖ + ‖IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i‖ := Vbound y i
      _ ≤ C1 * ϱ y ^ (-3:ℝ) + C2 * ϱ y ^ (-3:ℝ) :=
          add_le_add (hC1 i y h2).1 (hC2 i y h2).1
      _ = (C1 + C2) * ϱ y ^ (-3:ℝ) := by ring
  have hLder : ∀ (y : Space), y ∈ youngOpen ν ε⁻¹ → 2 * r0 ≤ ϱ y →
      |fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y (coordinateVector 2) 2|
        ≤ (C1 + C2) * ϱ y ^ (-3:ℝ) := by
    intro y hyU h2
    calc |fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y (coordinateVector 2) 2|
        = ‖fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y (coordinateVector 2) 2‖ :=
          (Real.norm_eq_abs _).symm
      _ = ‖fderiv ℝ (fun x => (IIIa.sepW ν (μ : ℂ) T' x τ 2
            - IIIa.sepW ν ((μ : ℂ) + 1) T' x τ 2).re) y (coordinateVector 2)‖ := by
          rw [Dcomp y (coordinateVector 2) 2 hyU]
      _ ≤ (‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) T' x τ 2) y‖
            + ‖fderiv ℝ (fun x => IIIa.sepW ν ((μ : ℂ) + 1) T' x τ 2) y‖)
            * ‖coordinateVector 2‖ :=
          wardFar_re_fderiv_le _ _ y _ (hGd 2 y hyU) (hHd 2 y hyU)
      _ ≤ (C1 * ϱ y ^ (-3:ℝ) + C2 * ϱ y ^ (-3:ℝ)) * 1 := by
          rw [hcv]
          simp only [mul_one]
          exact add_le_add (hC1 2 y h2).2 (hC2 2 y h2).2
      _ = (C1 + C2) * ϱ y ^ (-3:ℝ) := by ring
  -- the compact range and its continuity
  have hφ : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by
    fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) (youngOpen ν ε⁻¹) := by
    rintro ⟨a, b⟩ hp
    have ha : r ≤ a := hp.1.1
    have hpos : 0 ≤ a := by linarith
    show r0 < ϱ (!₂[a, 0, b] : Space)
    rw [wardFar_varrho a b hpos]
    linarith
  have hFc : ContinuousOn (fun p : ℝ × ℝ => wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    hSm.continuousOn.comp hφ.continuousOn hmaps
  have hDc : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) (!₂[p.1, 0, p.2] : Space))
      (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    (hSm.continuousOn_fderiv_of_isOpen hOpen (by norm_num)).comp hφ.continuousOn hmaps
  have hSc : IsCompact (Icc r (2 * r0) ×ˢ Metric.closedBall z 1) :=
    isCompact_Icc.prod (ProperSpace.isCompact_closedBall z 1)
  obtain ⟨M1, hM1⟩ := hSc.exists_bound_of_continuousOn hFc
  obtain ⟨M2, hM2⟩ := hSc.exists_bound_of_continuousOn hDc.norm
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = (|C1| + |C2|) + (2 * r0) ^ 3 * (|M1| + |M2|) :=
    ⟨_, rfl⟩
  refine ⟨2, Cc, by norm_num, ?_⟩
  intro ρ hρ z' hz'
  have hρr : r < ρ := hρ
  have hρpos : 0 < ρ := lt_trans (lt_trans hr0pos hr) hρr
  set y0 : Space := (!₂[ρ, 0, z'] : Space) with hy0
  have hyρ : ϱ y0 = ρ := by
    rw [hy0]
    exact wardFar_varrho ρ z' hρpos.le
  have hy0U : y0 ∈ youngOpen ν ε⁻¹ := by
    show r0 < ϱ y0
    rw [hyρ]
    linarith
  have hnn : 0 ≤ (2 * r0) ^ 3 * (|M1| + |M2|) := by positivity
  rcases le_total (2 * r0) ρ with h2 | h2
  · -- far regime `2 r_o ≤ ρ`
    have h2' : 2 * r0 ≤ ϱ y0 := by
      rw [hyρ]
      exact h2
    have hKL : C1 + C2 ≤ Cc := by
      rw [hCc]
      linarith [le_abs_self C1, le_abs_self C2]
    have hA := hLval y0 2 hy0U h2'
    have hB := hLder y0 hy0U h2'
    have hD := hLval y0 0 hy0U h2'
    rw [hyρ] at hA hB hD
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKL hA, wardFar_arith ρ _ _ _ hρpos hKL hB,
      wardFar_arith ρ _ _ _ hρpos hKL hD⟩
  · -- near regime `r < ρ ≤ 2 r_o`: compact bound
    have hmem : (ρ, z') ∈ Icc r (2 * r0) ×ˢ Metric.closedBall z 1 :=
      ⟨⟨hρr.le, h2⟩, Metric.ball_subset_closedBall hz'⟩
    have hVn : ‖wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y0‖ ≤ M1 := hM1 (ρ, z') hmem
    have hDn : ‖fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y0‖ ≤ M2 := by
      simpa only [norm_norm] using hM2 (ρ, z') hmem
    have hMM : |M1| + |M2| ≥ 0 := by positivity
    have hVal : ∀ i : Fin 3, |wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y0 i| ≤ |M1| + |M2| := by
      intro i
      rw [← Real.norm_eq_abs]
      refine (PiLp.norm_apply_le _ i).trans (hVn.trans ?_)
      linarith [le_abs_self M1, abs_nonneg M2]
    have hDer : |fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y0 (coordinateVector 2) 2|
        ≤ |M1| + |M2| := by
      rw [← Real.norm_eq_abs]
      refine (PiLp.norm_apply_le _ 2).trans ?_
      refine ((fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y0).le_opNorm _).trans ?_
      rw [hcv, mul_one]
      linarith [le_abs_self M2, abs_nonneg M1]
    have hKS : (2 * r0) ^ 3 * (|M1| + |M2|) ≤ Cc := by
      rw [hCc]
      linarith [abs_nonneg C1, abs_nonneg C2]
    exact ⟨wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 2)),
      wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM hDer),
      wardFar_arith ρ _ _ _ hρpos hKS
        (wardFar_small_bound ρ (2 * r0) (|M1| + |M2|) _ hρpos h2 hMM (hVal 0))⟩

end UnforcedLeray.Short.PartIIIb.Concrete
