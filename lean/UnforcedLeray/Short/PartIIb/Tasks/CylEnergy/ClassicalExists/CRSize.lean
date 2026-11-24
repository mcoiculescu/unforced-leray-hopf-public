import UnforcedLeray.Short.PartIIb.Sub.T22_1_10
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds
import UnforcedLeray.Lib.BudgetsGronwall.SingularVolterra

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.
Given the derivative formulas `CRFormulas`, each of the seven terms of `W2(G(τ))` is an integral
`∫_s^τ` of a heat-kernel term against `F(r)` (`HeatWBounds`, with `a = ν(τ - r)`). Each term is
bounded by its integrand majorant (`term_bound`), the majorants are integrable by
`intervalIntegrable_kernel_mul`, and the constants add up to `crK`:
the zero-order term gives `2 e^{νL} b(r)`, the six derivative terms give
`2 e^{νL} (b(r) + ν^{-1/2} (τ-r)^{-1/2} b(r))`, with `L = ν(T - s)`; the sum is at most
`2 e^{νL} (7 + 6ν^{-1/2}) (1 + (τ-r)^{-1/2}) b(r)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CRSize

lemma ae_ne_pt (τ : ℝ) : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ τ := by
  have h := (Set.countable_singleton τ).ae_notMem (volume : Measure ℝ)
  filter_upwards [h] with r hr
  exact hr

/-- One integral term: `|∫ f| c ≤ ∫ g` from a.e. pointwise bounds on the integrand. -/
lemma term_bound {s τ : ℝ} (hsτ : s ≤ τ) (f g : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc s τ → |f r| * c ≤ g r)
    (hg : IntervalIntegrable g volume s τ) :
    |∫ r in s..τ, f r| * c ≤ ∫ r in s..τ, g r := by
  have e : |∫ r in s..τ, f r| * c = ‖∫ r in s..τ, f r * c‖ := by
    rw [intervalIntegral.integral_mul_const, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hc]
  rw [e]
  refine intervalIntegral.norm_integral_le_of_norm_le hsτ ?_ hg
  filter_upwards [h] with r hr hm
  have h1 := hr hm
  show ‖f r * c‖ ≤ g r
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
  exact h1

/-- The zero-order majorant: `2 e^{ν(τ-r)} B ≤ 2 e^{ν(T-s)} B`. -/
lemma major_zero {ν τ r s T B X : ℝ} (hν : 0 < ν) (hsr : s ≤ r) (hrτ : r ≤ τ) (hτT : τ ≤ T)
    (hB : 0 ≤ B) (hX : X ≤ 2 * Real.exp (ν * (τ - r)) * B) :
    X ≤ 2 * Real.exp (ν * (T - s)) * B := by
  have ha : ν * (τ - r) ≤ ν * (T - s) := mul_le_mul_of_nonneg_left (by linarith) hν.le
  have hE : Real.exp (ν * (τ - r)) ≤ Real.exp (ν * (T - s)) := Real.exp_le_exp.2 ha
  have hfin : 2 * Real.exp (ν * (τ - r)) * B ≤ 2 * Real.exp (ν * (T - s)) * B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hB
  linarith

/-- The derivative majorant: `2 e^{ν(τ-r)} (1 + a^{-1/2}) B ≤ 2 e^{ν(T-s)} (B + ν^{-1/2}((τ-r)^{-1/2} B))`,
`a = ν(τ-r)`. -/
lemma major_point {ν τ r s T B X : ℝ} (hν : 0 < ν) (hsr : s ≤ r) (hrτ : r ≤ τ) (hτT : τ ≤ T)
    (hB : 0 ≤ B)
    (hX : X ≤ 2 * Real.exp (ν * (τ - r)) * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B) :
    X ≤ 2 * Real.exp (ν * (T - s)) *
      (B + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * B)) := by
  have ha : ν * (τ - r) ≤ ν * (T - s) := mul_le_mul_of_nonneg_left (by linarith) hν.le
  have hE : Real.exp (ν * (τ - r)) ≤ Real.exp (ν * (T - s)) := Real.exp_le_exp.2 ha
  have hp : (ν * (τ - r)) ^ (-(1 / 2 : ℝ)) = ν ^ (-(1 / 2 : ℝ)) * (τ - r) ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow hν.le (by linarith)
  have hc : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have hq : 0 ≤ (τ - r) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  rw [hp] at hX
  have hX2 : 2 * Real.exp (ν * (τ - r)) * (1 + ν ^ (-(1 / 2 : ℝ)) * (τ - r) ^ (-(1 / 2 : ℝ))) * B
      = 2 * Real.exp (ν * (τ - r)) *
          (B + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * B)) := by ring
  have hY : 0 ≤ B + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * B) :=
    add_nonneg hB (mul_nonneg hc (mul_nonneg hq hB))
  have hfin : 2 * Real.exp (ν * (τ - r)) *
        (B + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * B))
      ≤ 2 * Real.exp (ν * (T - s)) *
        (B + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * B)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hY
  linarith

/-- Pointwise a.e. majorant for a first or second derivative term `∂ᵢ` of the heat semigroup
applied to `Gr r` with `|Gr r| cosh ≤ b r` (`HeatWBounds`, second part). -/
lemma pt_deriv {ν s τ T : ℝ} {b : ℝ → ℝ} {Gr : ℝ → Pl → ℝ} (i : Fin 2) (x : Pl) (hν : 0 < ν)
    (hsτ : s ≤ τ) (hτT : τ ≤ T) (hb0 : ∀ r ∈ Icc s T, 0 ≤ b r)
    (hW : ∀ r ∈ Icc s T, WB (b r) (Gr r)) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc s τ →
      |heatSGd i (ν * (τ - r)) (Gr r) x| * Real.cosh x.2 ≤
        2 * Real.exp (ν * (T - s)) * (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) := by
  filter_upwards [ae_ne_pt τ] with r hrne hr
  have hrτ : r < τ := lt_of_le_of_ne hr.2 hrne
  have hrI : r ∈ Icc s T := ⟨hr.1.le, le_trans hr.2 hτT⟩
  have ha : 0 < ν * (τ - r) := mul_pos hν (sub_pos.2 hrτ)
  have hw := (heatWBounds (b r) (Gr r) (hW r hrI)).2 (ν * (τ - r)) ha i x
  exact major_point hν hr.1.le hr.2 hτT (hb0 r hrI) hw


end CRSize

open CRSize

/-- **`T22/1/10/2`** The weighted bound `W2(G(τ)) cosh η ≤ K ∫_s^τ (1 + (τ-r)^{-1/2}) b(r) dr`
(`CRSize`). -/
theorem crSize : UnforcedLeray.Short.IIb.CylPDE.CRSize := by
  intro ν s T hν hsT F b hH τ hτ hform x
  unfold CRHyp at hH
  obtain ⟨_, hcb, hb0', hWF⟩ := hH
  have hb0 : ∀ r ∈ Icc s T, 0 ≤ b r := hb0'
  unfold CRFormulas at hform
  obtain ⟨hf1, hf2⟩ := hform
  have hsτ : s ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hbc : ContinuousOn b (uIcc s τ) := by
    rw [Set.uIcc_of_le hsτ]
    exact hcb.mono (Icc_subset_Icc le_rfl hτT)
  have hbI : IntervalIntegrable b volume s τ := hbc.intervalIntegrable
  have hpI : IntervalIntegrable (fun r : ℝ => (τ - r) ^ (-(1 / 2 : ℝ)) * b r) volume s τ :=
    UnforcedLeray.Gronwall.intervalIntegrable_kernel_mul hbc τ
  have hc : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have hE : 0 ≤ Real.exp (ν * (T - s)) := (Real.exp_pos _).le
  have hcosh : 0 ≤ Real.cosh x.2 := (Real.cosh_pos _).le
  -- zero-order term
  have h0 : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc s τ →
      |heatSG (ν * (τ - r)) (F r) x| * Real.cosh x.2 ≤ 2 * Real.exp (ν * (T - s)) * b r := by
    refine ae_of_all _ (fun r hr => ?_)
    have hrI : r ∈ Icc s T := ⟨hr.1.le, le_trans hr.2 hτT⟩
    have hw := (heatWBounds (b r) (F r) (hWF r hrI).1).1 (ν * (τ - r))
      (mul_nonneg hν.le (sub_nonneg.2 hr.2)) x
    exact major_zero hν hr.1.le hr.2 hτT (hb0 r hrI) hw
  have hG0I : IntervalIntegrable (fun r : ℝ => 2 * Real.exp (ν * (T - s)) * b r) volume s τ :=
    hbI.const_mul _
  have hG1I : IntervalIntegrable
      (fun r : ℝ => 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r))) volume s τ :=
    (hbI.add (hpI.const_mul _)).const_mul _
  have A0 : |∫ r in s..τ, heatSG (ν * (τ - r)) (F r) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) * b r :=
    term_bound hsτ _ _ hcosh h0 hG0I
  have A1 : |∫ r in s..τ, heatSGd 0 (ν * (τ - r)) (F r) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) :=
    term_bound hsτ _ _ hcosh
      (pt_deriv (Gr := F) 0 x hν hsτ hτT hb0 (fun r hr => (hWF r hr).1)) hG1I
  have A2 : |∫ r in s..τ, heatSGd 1 (ν * (τ - r)) (F r) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) :=
    term_bound hsτ _ _ hcosh
      (pt_deriv (Gr := F) 1 x hν hsτ hτT hb0 (fun r hr => (hWF r hr).1)) hG1I
  have A3 : |∫ r in s..τ, heatSGd 0 (ν * (τ - r)) (B0579.pd 0 (F r)) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) :=
    term_bound hsτ _ _ hcosh
      (pt_deriv (Gr := fun r => B0579.pd 0 (F r)) 0 x hν hsτ hτT hb0
        (fun r hr => (hWF r hr).2 0)) hG1I
  have A4 : |∫ r in s..τ, heatSGd 1 (ν * (τ - r)) (B0579.pd 0 (F r)) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) :=
    term_bound hsτ _ _ hcosh
      (pt_deriv (Gr := fun r => B0579.pd 0 (F r)) 1 x hν hsτ hτT hb0
        (fun r hr => (hWF r hr).2 0)) hG1I
  have A5 : |∫ r in s..τ, heatSGd 0 (ν * (τ - r)) (B0579.pd 1 (F r)) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) :=
    term_bound hsτ _ _ hcosh
      (pt_deriv (Gr := fun r => B0579.pd 1 (F r)) 0 x hν hsτ hτT hb0
        (fun r hr => (hWF r hr).2 1)) hG1I
  have A6 : |∫ r in s..τ, heatSGd 1 (ν * (τ - r)) (B0579.pd 1 (F r)) x| * Real.cosh x.2 ≤
      ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
        (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) :=
    term_bound hsτ _ _ hcosh
      (pt_deriv (Gr := fun r => B0579.pd 1 (F r)) 1 x hν hsτ hτT hb0
        (fun r hr => (hWF r hr).2 1)) hG1I
  have I0nn : 0 ≤ ∫ r in s..τ, b r :=
    intervalIntegral.integral_nonneg hsτ (fun r hr => hb0 r ⟨hr.1, le_trans hr.2 hτT⟩)
  have I1nn : 0 ≤ ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * b r :=
    intervalIntegral.integral_nonneg hsτ (fun r hr =>
      mul_nonneg (Real.rpow_nonneg (sub_nonneg.2 hr.2) _) (hb0 r ⟨hr.1, le_trans hr.2 hτT⟩))
  have V0 : ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) * b r =
      2 * Real.exp (ν * (T - s)) * ∫ r in s..τ, b r :=
    intervalIntegral.integral_const_mul _ _
  have V1 : ∫ r in s..τ, 2 * Real.exp (ν * (T - s)) *
      (b r + ν ^ (-(1 / 2 : ℝ)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * b r)) =
      2 * Real.exp (ν * (T - s)) *
        ((∫ r in s..τ, b r) + ν ^ (-(1 / 2 : ℝ)) * ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * b r) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hbI (hpI.const_mul _),
      intervalIntegral.integral_const_mul]
  have hJ : ∫ r in s..τ, (1 + (τ - r) ^ (-(1 / 2 : ℝ))) * b r =
      (∫ r in s..τ, b r) + ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * b r := by
    have e : ∀ r : ℝ, (1 + (τ - r) ^ (-(1 / 2 : ℝ))) * b r =
        b r + (τ - r) ^ (-(1 / 2 : ℝ)) * b r := fun r => by ring
    simp only [e]
    exact intervalIntegral.integral_add hbI hpI
  have e0 : duhamelConv ν s F τ x = ∫ r in s..τ, heatSG (ν * (τ - r)) (F r) x := rfl
  have hW2 : W2 (duhamelConv ν s F τ) x =
      |∫ r in s..τ, heatSG (ν * (τ - r)) (F r) x| +
      |∫ r in s..τ, heatSGd 0 (ν * (τ - r)) (F r) x| +
      |∫ r in s..τ, heatSGd 1 (ν * (τ - r)) (F r) x| +
      |∫ r in s..τ, heatSGd 0 (ν * (τ - r)) (B0579.pd 0 (F r)) x| +
      |∫ r in s..τ, heatSGd 0 (ν * (τ - r)) (B0579.pd 1 (F r)) x| +
      |∫ r in s..τ, heatSGd 1 (ν * (τ - r)) (B0579.pd 0 (F r)) x| +
      |∫ r in s..τ, heatSGd 1 (ν * (τ - r)) (B0579.pd 1 (F r)) x| := by
    unfold W2
    rw [e0, hf1 0 x, hf1 1 x, hf2 0 0 x, hf2 0 1 x, hf2 1 0 x, hf2 1 1 x]
  have hdiff : 0 ≤ 2 * Real.exp (ν * (T - s)) *
      (7 * (∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * b r) +
        6 * ν ^ (-(1 / 2 : ℝ)) * ∫ r in s..τ, b r) :=
    mul_nonneg (by positivity) (by linarith [mul_nonneg hc I0nn, I1nn])
  unfold crK
  rw [hJ, hW2]
  linarith [A0, A1, A2, A3, A4, A5, A6, V0, V1, hdiff]

end UnforcedLeray.Short.IIb.CylPDE
