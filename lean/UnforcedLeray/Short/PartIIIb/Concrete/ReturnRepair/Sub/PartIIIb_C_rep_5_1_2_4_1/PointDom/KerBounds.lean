import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.KerBounds.Grad

/-!
# `pdKerBounds` (`PartIII-b:C/rep/5/1/2/4/1/2/5`; source 3604-3610 with `j ≤ 2`, 3708-3709)

`PDKerBounds` for the phase-lag kernel `xKer`: `xKer = c(h) • gradKCon (ν(1-λ²)) · M` with
`c(h) = -(λ^{2μ+3} - λ^{2μ+5})`, `λ = e^{-h/2}`.  The derivatives in `x` come from
`sep:kernel` (`IIIa.sepKernelBounds`, orders `1,2,3` of `K_t`), the `h`-derivative from the heat
equation `∂_t ∇K_t = Δ ∇K_t` (`gradKHeat_of_partial kernelPartialHeat`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem kb_rpow0 (x : Space) : ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) = (‖x‖ ^ 4)⁻¹ := by
  rw [show (-4 - ((0 : ℕ) : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]

theorem kb_rpow1 (x : Space) : ‖x‖ ^ (-4 - ((1 : ℕ) : ℝ)) = (‖x‖ ^ 5)⁻¹ := by
  rw [show (-4 - ((1 : ℕ) : ℝ)) = -((5 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]

theorem kb_rpow2 (x : Space) : ‖x‖ ^ (-4 - ((2 : ℕ) : ℝ)) = (‖x‖ ^ 6)⁻¹ := by
  rw [show (-4 - ((2 : ℕ) : ℝ)) = -((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]

theorem kb_pdLam_pow (h r : ℝ) : pdLam h ^ r = Real.exp (-(h / 2) * r) := by
  unfold pdLam
  rw [← Real.exp_mul]

/-- Order-`n` bound for `∇K_t : M` in the inverse-power form. -/
theorem kb_grad0 {t : ℝ} (ht : 0 < t) (M : Matrix (Fin 3) (Fin 3) ℝ) {C : ℝ}
    (hC : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (0 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤ C * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)))
    {x : Space} (hx : x ≠ 0) :
    ‖gradKCon t x M‖ ≤ 27 * (max C 0 * (‖x‖ ^ 4)⁻¹) * IIIa.tensorNorm M := by
  have h := KB.kb_gradKCon_iter ht M 0 (by norm_num) x (max C 0 * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)))
    (fun i j => (hC x hx i j t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _)))
  rw [norm_iteratedFDeriv_zero, kb_rpow0] at h
  exact h

theorem kb_grad1 {t : ℝ} (ht : 0 < t) (M : Matrix (Fin 3) (Fin 3) ℝ) {C : ℝ}
    (hC : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (1 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤ C * ‖x‖ ^ (-4 - ((1 : ℕ) : ℝ)))
    {x : Space} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 1 (fun y => gradKCon t y M) x‖ ≤
      27 * (max C 0 * (‖x‖ ^ 5)⁻¹) * IIIa.tensorNorm M := by
  have h := KB.kb_gradKCon_iter ht M 1 (by norm_num) x (max C 0 * ‖x‖ ^ (-4 - ((1 : ℕ) : ℝ)))
    (fun i j => (hC x hx i j t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _)))
  rw [kb_rpow1] at h
  exact h

theorem kb_grad2 {t : ℝ} (ht : 0 < t) (M : Matrix (Fin 3) (Fin 3) ℝ) {C : ℝ}
    (hC : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (2 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤ C * ‖x‖ ^ (-4 - ((2 : ℕ) : ℝ)))
    {x : Space} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 2 (fun y => gradKCon t y M) x‖ ≤
      27 * (max C 0 * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M := by
  have h := KB.kb_gradKCon_iter ht M 2 (by norm_num) x (max C 0 * ‖x‖ ^ (-4 - ((2 : ℕ) : ℝ)))
    (fun i j => (hC x hx i j t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _)))
  rw [kb_rpow2] at h
  exact h

/-- The coefficient `c(h) = -(λ^{2μ+3} - λ^{2μ+5})` is bounded by `λ^{2μ+3}`. -/
theorem kb_coef_bounds (μ h : ℝ) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (hh : 0 < h) :
    0 ≤ pdLam h ^ (2 * μ + 3) ∧ 0 ≤ pdLam h ^ (2 * μ + 5) ∧
      pdLam h ^ (2 * μ + 5) ≤ pdLam h ^ (2 * μ + 3) ∧ pdLam h ^ (2 * μ + 3) ≤ 1 := by
  have hpos : 0 < pdLam h := Real.exp_pos _
  have hle : pdLam h ≤ 1 := by
    unfold pdLam
    exact Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨Real.rpow_nonneg hpos.le _, Real.rpow_nonneg hpos.le _, ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_ge hpos hle (by linarith)
  · exact Real.rpow_le_one hpos.le hle (by linarith)

/-- The `h`-derivative of the coefficient, a multiple of `λ^{2μ+3}`. -/
theorem kb_coef_deriv_bound (μ h : ℝ) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (hh : 0 < h) :
    |-(-(2 * μ + 3) / 2 * pdLam h ^ (2 * μ + 3) - -(2 * μ + 5) / 2 * pdLam h ^ (2 * μ + 5))|
      ≤ 6 * pdLam h ^ (2 * μ + 3) := by
  obtain ⟨hA, hB, hBA, -⟩ := kb_coef_bounds μ h hμ0 hμ1 hh
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 * μ + 3 by linarith) hA,
    mul_nonneg (show (0:ℝ) ≤ 2 * μ + 5 by linarith) hB,
    mul_le_mul_of_nonneg_right (show 2 * μ + 3 ≤ (5:ℝ) by linarith) hA,
    mul_le_mul_of_nonneg_right (show 2 * μ + 5 ≤ (7:ℝ) by linarith) hB,
    mul_le_mul_of_nonneg_left hBA (show (0:ℝ) ≤ 2 * μ + 5 by linarith)]

/-- `λ^{2μ+3}`-form of the bound on `xKer` (order `n`). -/
theorem kb_xKer_iter (ν μ h : ℝ) (hν : 0 < ν) (hh : 0 < h) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {x : Space} (hx : x ≠ 0) (n : ℕ) (hn : n ≤ 2) (C : ℝ)
    (hC : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤
        C * ‖x‖ ^ (-4 - (n : ℝ))) :
    ‖iteratedFDeriv ℝ n (fun x' => xKer ν μ h x' M) x‖ ≤
      pdLam h ^ (2 * μ + 3) * (27 * (max C 0 * ‖x‖ ^ (-4 - (n : ℝ))) * IIIa.tensorNorm M) := by
  obtain ⟨hA, hB, hBA, -⟩ := kb_coef_bounds μ h hμ0 hμ1 hh
  have hT : 0 < ν * (1 - pdLam h ^ 2) := by
    have hlam2 : pdLam h ^ 2 = Real.exp (-h) := by
      unfold pdLam; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hlam2]
    have : Real.exp (-h) < 1 := by
      have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
      simpa using this
    exact mul_pos hν (by linarith)
  have hfun : (fun x' => xKer ν μ h x' M) = fun x' =>
      (-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))) •
        gradKCon (ν * (1 - pdLam h ^ 2)) x' M := rfl
  have hGcd : ContDiffAt ℝ n (fun y => gradKCon (ν * (1 - pdLam h ^ 2)) y M) x :=
    ((KB.kb_contDiff_gradKCon hT M).contDiffAt).of_le (by exact_mod_cast hn)
  rw [hfun, iteratedFDeriv_const_smul_apply' hGcd, norm_smul, Real.norm_eq_abs]
  have hG := KB.kb_gradKCon_iter hT M n hn x (max C 0 * ‖x‖ ^ (-4 - (n : ℝ)))
    (fun i j => (hC x hx i j _ hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _)))
  have hc : |-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))| ≤ pdLam h ^ (2 * μ + 3) := by
    rw [abs_neg, abs_of_nonneg (by linarith)]
    linarith
  exact mul_le_mul hc hG (norm_nonneg _) hA

theorem kb_hT (ν h : ℝ) (hν : 0 < ν) (hh : 0 < h) : 0 < ν * (1 - pdLam h ^ 2) := by
  have hlam2 : pdLam h ^ 2 = Real.exp (-h) := by
    unfold pdLam; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hlam2]
  have : Real.exp (-h) < 1 := by
    have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
    simpa using this
  exact mul_pos hν (by linarith)

/-- The `h`-derivative of `xKer` (chain rule through `t = ν(1-λ²)`, heat equation for `∂_t`). -/
theorem kb_xKer_hasDeriv (ν μ h : ℝ) (hν : 0 < ν) (hh : 0 < h) (x : Space)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    HasDerivAt (fun h' => xKer ν μ h' x M)
      ((-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))) •
          ((ν * Real.exp (-h)) • physLap (fun y => gradKCon (ν * (1 - pdLam h ^ 2)) y M) x) +
        (-(-(2 * μ + 3) / 2 * pdLam h ^ (2 * μ + 3) - -(2 * μ + 5) / 2 * pdLam h ^ (2 * μ + 5))) •
          gradKCon (ν * (1 - pdLam h ^ 2)) x M) h := by
  have hTpos := kb_hT ν h hν hh
  have dA : HasDerivAt (fun h' => pdLam h' ^ (2 * μ + 3)) (-(2 * μ + 3) / 2 * pdLam h ^ (2 * μ + 3)) h := by
    have : (fun h' => pdLam h' ^ (2 * μ + 3)) = fun h' => Real.exp (-(h' / 2) * (2 * μ + 3)) := by
      funext h'; exact kb_pdLam_pow _ _
    rw [this]
    have hd : HasDerivAt (fun h' : ℝ => -(h' / 2) * (2 * μ + 3)) (-(1 / 2) * (2 * μ + 3)) h := by
      have := ((hasDerivAt_id h).div_const 2).neg.mul_const (2 * μ + 3)
      simpa using this
    have := hd.exp
    convert this using 1
    rw [kb_pdLam_pow]; ring
  have dB : HasDerivAt (fun h' => pdLam h' ^ (2 * μ + 5)) (-(2 * μ + 5) / 2 * pdLam h ^ (2 * μ + 5)) h := by
    have : (fun h' => pdLam h' ^ (2 * μ + 5)) = fun h' => Real.exp (-(h' / 2) * (2 * μ + 5)) := by
      funext h'; exact kb_pdLam_pow _ _
    rw [this]
    have hd : HasDerivAt (fun h' : ℝ => -(h' / 2) * (2 * μ + 5)) (-(1 / 2) * (2 * μ + 5)) h := by
      have := ((hasDerivAt_id h).div_const 2).neg.mul_const (2 * μ + 5)
      simpa using this
    have := hd.exp
    convert this using 1
    rw [kb_pdLam_pow]; ring
  have dT : HasDerivAt (fun h' => ν * (1 - pdLam h' ^ 2)) (ν * Real.exp (-h)) h := by
    have : (fun h' => ν * (1 - pdLam h' ^ 2)) = fun h' => ν * (1 - Real.exp (-h')) := by
      funext h'
      unfold pdLam; rw [← Real.exp_nat_mul]; congr 3; push_cast; ring
    rw [this]
    have := (((hasDerivAt_id h).neg.exp).const_sub 1).const_mul ν
    exact this.congr_deriv (by simp)
  have da : HasDerivAt (fun h' => -(pdLam h' ^ (2 * μ + 3) - pdLam h' ^ (2 * μ + 5)))
      (-(-(2 * μ + 3) / 2 * pdLam h ^ (2 * μ + 3) - -(2 * μ + 5) / 2 * pdLam h ^ (2 * μ + 5))) h :=
    (dA.sub dB).neg
  have hGT := (gradKHeat_of_partial kernelPartialHeat) (ν * (1 - pdLam h ^ 2)) hTpos x M
  have dG := hGT.scomp h dT
  exact da.smul dG

theorem kb_tensor_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ IIIa.tensorNorm M := by
  unfold IIIa.tensorNorm
  exact Real.sqrt_nonneg _

theorem kb_pack (A X P T M C : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hMC : 27 * M ≤ C) (hX : X ≤ A * (27 * (M * P) * T)) : X ≤ C * A * P * T := by
  have h1 : 27 * (M * P) * T ≤ C * P * T := by
    have e : 27 * (M * P) = (27 * M) * P := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hP) hT
  calc X ≤ A * (27 * (M * P) * T) := hX
    _ ≤ A * (C * P * T) := mul_le_mul_of_nonneg_left h1 hA
    _ = C * A * P * T := by ring

theorem kb_abstract (A c c' E ν T p4 p6 M0 M2 C : ℝ) (Gv Lv : Space) (hA : 0 ≤ A)
    (hc : |c| ≤ A) (hc' : |c'| ≤ 6 * A) (hE0 : 0 ≤ E) (hEν : E ≤ ν) (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hp4 : 0 ≤ p4) (hp6 : 0 ≤ p6) (hM0 : 0 ≤ M0) (hM2 : 0 ≤ M2) (hC0 : 162 * M0 ≤ C)
    (hC2 : 81 * M2 ≤ C) (hG : ‖Gv‖ ≤ 27 * (M0 * p4) * T) (hL : ‖Lv‖ ≤ 3 * (27 * (M2 * p6) * T)) :
    ‖c • (E • Lv) + c' • Gv‖ ≤ C * A * (p4 + ν * p6) * T := by
  have h1 : ‖c • (E • Lv)‖ ≤ A * (ν * (3 * (27 * (M2 * p6) * T))) := by
    rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hE0]
    exact mul_le_mul hc (mul_le_mul hEν hL (norm_nonneg _) hν) (mul_nonneg hE0 (norm_nonneg _)) hA
  have h2 : ‖c' • Gv‖ ≤ 6 * A * (27 * (M0 * p4) * T) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc' hG (norm_nonneg _) (by linarith)
  have key : 162 * M0 * p4 + 81 * ν * M2 * p6 ≤ C * (p4 + ν * p6) := by
    have e1 : 162 * M0 * p4 ≤ C * p4 := mul_le_mul_of_nonneg_right (by linarith) hp4
    have e2 : 81 * M2 * (ν * p6) ≤ C * (ν * p6) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hν hp6)
    have e3 : 81 * ν * M2 * p6 = 81 * M2 * (ν * p6) := by ring
    have e4 : C * (p4 + ν * p6) = C * p4 + C * (ν * p6) := by ring
    rw [e3, e4]
    linarith
  have f : A * T * (162 * M0 * p4 + 81 * ν * M2 * p6) ≤ A * T * (C * (p4 + ν * p6)) :=
    mul_le_mul_of_nonneg_left key (mul_nonneg hA hT)
  calc ‖c • (E • Lv) + c' • Gv‖ ≤ ‖c • (E • Lv)‖ + ‖c' • Gv‖ := norm_add_le _ _
    _ ≤ A * (ν * (3 * (27 * (M2 * p6) * T))) + 6 * A * (27 * (M0 * p4) * T) :=
        add_le_add h1 h2
    _ = A * T * (162 * M0 * p4 + 81 * ν * M2 * p6) := by ring
    _ ≤ A * T * (C * (p4 + ν * p6)) := f
    _ = C * A * (p4 + ν * p6) * T := by ring

theorem kb_deriv_bound (ν μ h : ℝ) (hν : 0 < ν) (hh : 0 < h) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1)
    (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) (C M0 M2 : ℝ) (hM0 : 0 ≤ M0) (hM2 : 0 ≤ M2)
    (hC0 : 162 * M0 ≤ C) (hC2 : 81 * M2 ≤ C)
    (hG0 : ‖gradKCon (ν * (1 - pdLam h ^ 2)) x M‖ ≤ 27 * (M0 * (‖x‖ ^ 4)⁻¹) * IIIa.tensorNorm M)
    (hG2 : ‖physLap (fun y => gradKCon (ν * (1 - pdLam h ^ 2)) y M) x‖ ≤
      3 * (27 * (M2 * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M)) :
    ‖deriv (fun h' => xKer ν μ h' x M) h‖ ≤
      C * pdLam h ^ (2 * μ + 3) * ((‖x‖ ^ 4)⁻¹ + ν * (‖x‖ ^ 6)⁻¹) * IIIa.tensorNorm M := by
  rw [(kb_xKer_hasDeriv ν μ h hν hh x M).deriv]
  obtain ⟨hA, hB, hBA, -⟩ := kb_coef_bounds μ h hμ0 hμ1 hh
  have hcb : |-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))| ≤ pdLam h ^ (2 * μ + 3) := by
    rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hBA)]
    linarith
  have hE0 : 0 ≤ ν * Real.exp (-h) := mul_nonneg hν.le (Real.exp_pos _).le
  have hEν : ν * Real.exp (-h) ≤ ν :=
    mul_le_of_le_one_right hν.le (Real.exp_le_one_iff.mpr (by linarith))
  exact kb_abstract _ _ _ _ _ _ _ _ _ _ _ _ _ hA hcb (kb_coef_deriv_bound μ h hμ0 hμ1 hh)
    hE0 hEν hν.le (kb_tensor_nonneg M) (by positivity) (by positivity) hM0 hM2 hC0 hC2 hG0 hG2

theorem pdKerBounds : PDKerBounds := by
  obtain ⟨C0, hC0⟩ := IIIa.sepKernelBounds 0
  obtain ⟨C1, hC1⟩ := IIIa.sepKernelBounds 1
  obtain ⟨C2, hC2⟩ := IIIa.sepKernelBounds 2
  have hK0 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (0 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤
        C0 * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) :=
    fun x hx i k s hs => (hC0 x hx i k).1 s hs
  have hK1 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (1 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤
        C1 * ‖x‖ ^ (-4 - ((1 : ℕ) : ℝ)) :=
    fun x hx i k s hs => (hC1 x hx i k).1 s hs
  have hK2 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (2 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤
        C2 * ‖x‖ ^ (-4 - ((2 : ℕ) : ℝ)) :=
    fun x hx i k s hs => (hC2 x hx i k).1 s hs
  have hM0 : 0 ≤ max C0 0 := le_max_right _ _
  have hM1 : 0 ≤ max C1 0 := le_max_right _ _
  have hM2 : 0 ≤ max C2 0 := le_max_right _ _
  refine ⟨200 * (max C0 0 + max C1 0 + max C2 0), mul_nonneg (by norm_num) (by linarith), ?_⟩
  intro ν μ h hν hμ0 hμ1 hh M
  have hT := kb_hT ν h hν hh
  have hCa : 27 * max C0 0 ≤ 200 * (max C0 0 + max C1 0 + max C2 0) := by linarith
  have hCb : 27 * max C1 0 ≤ 200 * (max C0 0 + max C1 0 + max C2 0) := by linarith
  have hCc : 27 * max C2 0 ≤ 200 * (max C0 0 + max C1 0 + max C2 0) := by linarith
  have h162 : 162 * max C0 0 ≤ 200 * (max C0 0 + max C1 0 + max C2 0) := by linarith
  have h81 : 81 * max C2 0 ≤ 200 * (max C0 0 + max C1 0 + max C2 0) := by linarith
  have hA := (kb_coef_bounds μ h hμ0 hμ1 hh).1
  refine ⟨(KB.kb_contDiff_gradKCon hT M).const_smul
      (-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))),
    fun x => (kb_xKer_hasDeriv ν μ h hν hh x M).differentiableAt, fun x hx => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · have h0 := kb_xKer_iter ν μ h hν hh hμ0 hμ1 M hx 0 (by norm_num) C0 hK0
    rw [norm_iteratedFDeriv_zero, kb_rpow0] at h0
    exact kb_pack _ _ _ _ _ _ hA (by positivity) (kb_tensor_nonneg M) hM0 hCa h0
  · rw [← norm_iteratedFDeriv_one]
    have h1 := kb_xKer_iter ν μ h hν hh hμ0 hμ1 M hx 1 (by norm_num) C1 hK1
    rw [kb_rpow1] at h1
    exact kb_pack _ _ _ _ _ _ hA (by positivity) (kb_tensor_nonneg M) hM1 hCb h1
  · have h2 := kb_xKer_iter ν μ h hν hh hμ0 hμ1 M hx 2 (by norm_num) C2 hK2
    rw [kb_rpow2] at h2
    exact kb_pack _ _ _ _ _ _ hA (by positivity) (kb_tensor_nonneg M) hM2 hCc h2
  · have hG0 := kb_grad0 hT M hK0 hx
    have hG2 := (KB.kb_physLap_norm_le (KB.kb_contDiff_gradKCon hT M) x).trans
      (mul_le_mul_of_nonneg_left (kb_grad2 hT M hK2 hx) (by norm_num))
    exact kb_deriv_bound ν μ h hν hh hμ0 hμ1 x M _ (max C0 0) (max C2 0) hM0 hM2 h162 h81 hG0 hG2
  · have hG0 := kb_grad0 hT M hK0 hx
    unfold wKer
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hA]
    exact kb_pack _ _ _ _ _ _ hA (by positivity) (kb_tensor_nonneg M) hM0 hCa
      (mul_le_mul_of_nonneg_left hG0 hA)

end UnforcedLeray.Short.PartIIIb.Concrete

end
