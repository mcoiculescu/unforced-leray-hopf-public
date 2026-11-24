import UnforcedLeray.Short.PartI.Sub.PartI_T04_10
import NonUniqueEuler.P.Infra.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral Gronwall (leaf `IntegralGronwall` of `PartI:T04/10`)

Source: pure real analysis (no source line).

Proof. Put `P x = ∫_0^x C(1+Z)` and `Y = a + P`, which is continuous on `[0,T]`. Since
`Z ≤ Y` and `C ≥ 0`, `Y x ≤ a + ∫_0^x C(1+Y)`. The function
`V x = (a+1) e^{Cx} - 1` satisfies `V x = a + ∫_0^x C(1+V)` with equality. Hence
`D = Y - V` is continuous with `D x ≤ ∫_0^x C D`, and the variable-coefficient integral
Gronwall theorem `NonUniqueEuler.LinODE.int_gronwall` (with `c = 0`) gives `D ≤ 0`.
So `Z ≤ Y ≤ V ≤ (a+1) e^{Cs}`. No sign of `a+1` is needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartI

theorem integralGronwall : IntegralGronwall := by
  intro Z T a C hC hZi _hZb hZle s hs
  have hT : 0 ≤ T := hs.1.trans hs.2
  -- integrability of the integrand on `[0,T]`
  have hgi : IntegrableOn (fun r => C * (1 + Z r)) (Icc (0 : ℝ) T) := by
    have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) T) :=
      (continuousOn_const (c := (1 : ℝ))).integrableOn_Icc
    exact Integrable.const_mul (Integrable.add h1 hZi) C
  have hgu : IntegrableOn (fun r => C * (1 + Z r)) (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT]; exact hgi
  -- the primitive `P` is continuous on `[0,T]`
  have hPc : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, C * (1 + Z r)) (Icc (0 : ℝ) T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hgu
    rwa [uIcc_of_le hT] at this
  -- `Y = a + P` is continuous on `[0,T]`
  have hYc : ContinuousOn (fun x => a + ∫ r in (0 : ℝ)..x, C * (1 + Z r)) (Icc (0 : ℝ) T) :=
    continuousOn_const.add hPc
  have hYc' : ContinuousOn (fun r => C * (1 + (a + ∫ t in (0 : ℝ)..r, C * (1 + Z t))))
      (Icc (0 : ℝ) T) :=
    (continuousOn_const.add hYc).const_mul C
  -- every `[0,x]` with `x ∈ [0,T]` carries interval-integrable continuous functions
  have hcontII : ∀ x ∈ Icc (0 : ℝ) T, ∀ f : ℝ → ℝ, ContinuousOn f (Icc (0 : ℝ) T) →
      IntervalIntegrable f volume 0 x := by
    intro x hx f hf
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact hf.mono (Icc_subset_Icc_right hx.2)
  have hgII : ∀ x ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun r => C * (1 + Z r)) volume 0 x := by
    intro x hx
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx.1]
    exact hgi.mono_set (Icc_subset_Icc le_rfl hx.2)
  -- the comparison function `V x = (a+1) e^{Cx} - 1`
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ → ℝ, V = fun x => (a + 1) * Real.exp (C * x) - 1 := ⟨_, rfl⟩
  have hVx : ∀ x, V x = (a + 1) * Real.exp (C * x) - 1 := fun x => by rw [hVdef]
  have hVc : Continuous V := by
    rw [hVdef]; fun_prop
  have hVint : ∀ x : ℝ, a + ∫ r in (0 : ℝ)..x, C * (1 + V r) = V x := by
    intro x
    have hfun : (fun r => C * (1 + V r)) = fun r => C * (a + 1) * Real.exp (C * r) := by
      funext r; rw [hVx r]; ring
    have hd : ∀ r ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun r => (a + 1) * Real.exp (C * r)) (C * (a + 1) * Real.exp (C * r)) r := by
      intro r _
      have h : HasDerivAt (fun r => (a + 1) * Real.exp (C * r))
          ((a + 1) * (Real.exp (C * r) * (C * 1))) r :=
        (((hasDerivAt_id r).const_mul C).exp).const_mul (a + 1)
      exact h.congr_deriv (by ring)
    have hint : IntervalIntegrable (fun r => C * (a + 1) * Real.exp (C * r)) volume 0 x :=
      Continuous.intervalIntegrable (by fun_prop) 0 x
    rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp only [mul_zero, Real.exp_zero, mul_one, hVx]
    ring
  have hVII : ∀ x : ℝ, IntervalIntegrable (fun r => C * (1 + V r)) volume 0 x := fun x =>
    (continuous_const.mul (continuous_const.add hVc)).intervalIntegrable 0 x
  -- `P x ≤ ∫_0^x C(1+Y)`, from `Z ≤ Y` and `C ≥ 0`
  have hPle : ∀ x ∈ Icc (0 : ℝ) T,
      (∫ r in (0 : ℝ)..x, C * (1 + Z r)) ≤
        ∫ r in (0 : ℝ)..x, C * (1 + (a + ∫ t in (0 : ℝ)..r, C * (1 + Z t))) := by
    intro x hx
    apply intervalIntegral.integral_mono_on hx.1 (hgII x hx)
      (hcontII x hx _ (hYc'))
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hx.2⟩
    have hZr := hZle r hrT
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  -- `D = Y - V` satisfies `D x ≤ ∫_0^x C D`
  have hDc : ContinuousOn (fun x => (a + ∫ r in (0 : ℝ)..x, C * (1 + Z r)) - V x)
      (Icc (0 : ℝ) T) :=
    hYc.sub hVc.continuousOn
  have hDle : ∀ x ∈ Icc (0 : ℝ) T,
      (a + ∫ r in (0 : ℝ)..x, C * (1 + Z r)) - V x ≤
        ∫ t in (0 : ℝ)..x, C * (0 + ((a + ∫ r in (0 : ℝ)..t, C * (1 + Z r)) - V t)) := by
    intro x hx
    have hsplit : (∫ r in (0 : ℝ)..x, C * (1 + (a + ∫ t in (0 : ℝ)..r, C * (1 + Z t)))) -
        (∫ r in (0 : ℝ)..x, C * (1 + V r)) =
        ∫ t in (0 : ℝ)..x, C * (0 + ((a + ∫ r in (0 : ℝ)..t, C * (1 + Z r)) - V t)) := by
      rw [← intervalIntegral.integral_sub (hcontII x hx _ hYc') (hVII x)]
      apply intervalIntegral.integral_congr
      intro r _
      simp only
      ring
    have hP := hPle x hx
    have hV := hVint x
    linarith
  -- Gronwall with `c = 0` gives `D ≤ 0`
  have hG := NonUniqueEuler.LinODE.int_gronwall
    (u := fun x => (a + ∫ r in (0 : ℝ)..x, C * (1 + Z r)) - V x)
    (b := fun _ => C) (c := 0) (α := 0) (β := T) hDc continuousOn_const
    (fun _ _ => hC) le_rfl hDle s hs
  have hD0 : (a + ∫ r in (0 : ℝ)..s, C * (1 + Z r)) - V s ≤ 0 := by
    simpa using hG
  have hZs := hZle s hs
  have hVs := hVx s
  have hexp : (0 : ℝ) ≤ Real.exp (C * s) := (Real.exp_pos _).le
  nlinarith [hZs, hD0, hVs, hexp]

end UnforcedLeray.Short.PartI
