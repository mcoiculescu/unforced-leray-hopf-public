import UnforcedLeray.Short.PartIIIa.Sub.T23_5_Leaves
import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org.Bridge
import UnforcedLeray.Short.PartIIIa.Sub.T23_3_org

/-!
# Part III-a, `PartIII-a:T23/5/2`: the inlet chart coefficient from the stream

Source of record: `the November 2 reference manuscript`, lines 2360-2366
(normalized lift `e_eps = e_0 + eps e_1`, `e_0 = chi(-psi_eta, psi_q)`,
`e_1 = (0, (chi - 2 s chi') psi - chi eta psi_eta)`) and line 2711 (`v = s^{-1/2} V`).

Proves `inletChartFromStream : InletChartFromStream` (`Sub/T23_5_Leaves.lean`) with
`K = 2 + 4C`, `C` the uniform bound on `|deriv smoothTransition|` (`T23Inlet.deriv_smoothTransition_bound`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb UnforcedLeray.Blueprint

namespace InletChartCut

/-- The cut ring-stream profile is bounded by the stream and its gradient, with the `ε`-weighted
second component: `|e| ≤ (2+4C)(1 + ε(1+|η|))(|ψ| + |Dψ|)`, `ε = R⁻¹`. -/
theorem cut_norm_le {R H C : ℝ} (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) (hC0 : 0 ≤ C)
    (hR : 0 < R) (hH : 0 < H) {ψ : ℝ × ℝ → ℝ} {m : ℝ × (ℝ × ℝ)}
    (hψ : DifferentiableAt ℝ ψ m.2) :
    ‖ringStreamProfile R (fun n => ageCutoff H n.1 * ψ n.2) m‖ ≤
      (2 + 4 * C) * (1 + R⁻¹ * (1 + |m.2.2|)) * (|ψ m.2| + ‖fderiv ℝ ψ m.2‖) := by
  have hχd : DifferentiableAt ℝ (ageCutoff H) m.1 :=
    (contDiff_ageCutoff H (n := 1)).differentiable one_ne_zero _
  rw [ringStreamProfile_cutoff R hχd hψ]
  have hχ : |ageCutoff H m.1| ≤ 1 := T23Inlet.abs_ageCutoff_le_one H m.1
  have hsχ : |m.1 * deriv (ageCutoff H) m.1| ≤ 2 * C :=
    T23Inlet.abs_mul_deriv_ageCutoff_le hH hC m.1
  have hη : |fderiv ℝ ψ m.2 (0, 1)| ≤ ‖fderiv ℝ ψ m.2‖ :=
    T23Inlet.abs_fderiv_apply_le m.2 0 1 (by simp [Prod.norm_def])
  have hq : |fderiv ℝ ψ m.2 (1, 0)| ≤ ‖fderiv ℝ ψ m.2‖ :=
    T23Inlet.abs_fderiv_apply_le m.2 1 0 (by simp [Prod.norm_def])
  have hε0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  set χ := ageCutoff H m.1 with hχdef
  set χ' := deriv (ageCutoff H) m.1 with hχ'def
  set D := ‖fderiv ℝ ψ m.2‖ with hDdef
  set a := fderiv ℝ ψ m.2 (0, 1) with hadef
  set b := fderiv ℝ ψ m.2 (1, 0) with hbdef
  set y := ψ m.2 with hydef
  set η := m.2.2 with hηdef
  set ε := R⁻¹ with hεdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hη0 : 0 ≤ |η| := abs_nonneg _
  have hy0 : 0 ≤ |y| := abs_nonneg _
  have hC0' : 0 ≤ C := hC0
  have e1 : |-(χ * a)| ≤ D := by
    rw [abs_neg, abs_mul]
    calc |χ| * |a| ≤ 1 * |a| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
      _ ≤ D := by linarith
  have e2 : |χ * b| ≤ D := by
    rw [abs_mul]
    calc |χ| * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
      _ ≤ D := by linarith
  have e3 : |(χ - 2 * m.1 * χ') * y| ≤ (1 + 4 * C) * |y| := by
    rw [abs_mul]
    have : |χ - 2 * m.1 * χ'| ≤ 1 + 4 * C := by
      have h2 : 2 * m.1 * χ' = 2 * (m.1 * χ') := by ring
      rw [h2]
      calc |χ - 2 * (m.1 * χ')| ≤ |χ| + |2 * (m.1 * χ')| := abs_sub _ _
        _ = |χ| + 2 * |m.1 * χ'| := by rw [abs_mul, abs_two]
        _ ≤ 1 + 4 * C := by linarith
    exact mul_le_mul_of_nonneg_right this hy0
  have e4 : |χ * η * a| ≤ |η| * D := by
    rw [abs_mul, abs_mul]
    calc |χ| * |η| * |a| ≤ 1 * |η| * D :=
          mul_le_mul (mul_le_mul_of_nonneg_right hχ hη0) hη (abs_nonneg _) (by positivity)
      _ = |η| * D := by ring
  -- the `ε`-weighted second component
  have e5 : |ε * ((χ - 2 * m.1 * χ') * y - χ * η * a)| ≤
      ε * ((1 + 4 * C) * |y| + |η| * D) := by
    rw [abs_mul, abs_of_nonneg hε0]
    apply mul_le_mul_of_nonneg_left _ hε0
    exact (abs_sub _ _).trans (add_le_add e3 e4)
  refine (T23Inlet.norm_smul_m0_add_smul_m1_le _ _).trans ?_
  have e6 : |χ * b + ε * ((χ - 2 * m.1 * χ') * y - χ * η * a)| ≤
      D + ε * ((1 + 4 * C) * |y| + |η| * D) := (abs_add_le _ _).trans (add_le_add e2 e5)
  have hstep : |-(χ * a)| + |χ * b + ε * ((χ - 2 * m.1 * χ') * y - χ * η * a)| ≤
      2 * D + ε * ((1 + 4 * C) * |y| + |η| * D) := by linarith
  -- absorb into the target shape
  have hk1 : 1 + 4 * C ≤ (2 + 4 * C) * (1 + |η|) := by nlinarith
  have hk2 : |η| ≤ (2 + 4 * C) * (1 + |η|) := by nlinarith
  have hA : (1 + 4 * C) * |y| + |η| * D ≤ (2 + 4 * C) * (1 + |η|) * (|y| + D) := by
    have h1 : (1 + 4 * C) * |y| ≤ (2 + 4 * C) * (1 + |η|) * |y| :=
      mul_le_mul_of_nonneg_right hk1 hy0
    have h2 : |η| * D ≤ (2 + 4 * C) * (1 + |η|) * D :=
      mul_le_mul_of_nonneg_right hk2 hD0
    have h3 : (2 + 4 * C) * (1 + |η|) * (|y| + D) =
        (2 + 4 * C) * (1 + |η|) * |y| + (2 + 4 * C) * (1 + |η|) * D := by ring
    linarith
  have hB : ε * ((1 + 4 * C) * |y| + |η| * D) ≤
      (2 + 4 * C) * (ε * (1 + |η|)) * (|y| + D) := by
    have hε1 : ε * ((1 + 4 * C) * |y| + |η| * D) ≤ ε * ((2 + 4 * C) * (1 + |η|) * (|y| + D)) :=
      mul_le_mul_of_nonneg_left hA hε0
    have h3 : ε * ((2 + 4 * C) * (1 + |η|) * (|y| + D)) =
        (2 + 4 * C) * (ε * (1 + |η|)) * (|y| + D) := by ring
    linarith
  have hD2 : 2 * D ≤ (2 + 4 * C) * (|y| + D) := by
    nlinarith
  have hfinal : (2 + 4 * C) * (1 + ε * (1 + |η|)) * (|y| + D) =
      (2 + 4 * C) * (|y| + D) + (2 + 4 * C) * (ε * (1 + |η|)) * (|y| + D) := by ring
  nlinarith [hstep, hB, hD2, hfinal]

end InletChartCut

open InletChartCut in
/-- **The inlet chart coefficient is controlled by the inlet stream** (SP 2360-2366; SP 2711). -/
theorem inletChartFromStream : UnforcedLeray.Short.IIIa.InletChartFromStream := by
  obtain ⟨C, hC0, hC⟩ := T23Inlet.deriv_smoothTransition_bound
  refine ⟨2 + 4 * C, by linarith, fun p i pt hs hψ => ?_⟩
  have hinv : p.R⁻¹ = p.ε := by
    show (p.ε⁻¹)⁻¹ = p.ε
    exact inv_inv _
  have hcoef : chartCoeff p.R (p.inlet i) pt =
      ringStreamProfile p.R (fun n => ageCutoff p.H n.1 * p.frozenStream i n.2) pt := by
    have h := chartCoeff_Nv p.R_pos (p.inletProfile i) hs
    rw [show p.inlet i = Nv p.R (p.inletProfile i) from rfl, h]
    rfl
  rw [hcoef]
  have hb := cut_norm_le hC hC0 p.R_pos p.H_pos hψ
  rw [hinv] at hb
  exact hb

end UnforcedLeray.Short.IIIa
