import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed

/-!
# `ν_n → 0` and `ε_n → 0`, eventually `ν_n ≤ 1` and `ε_n ≤ 1` (source 5928-5945)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5928-5945:
`ν_n → 0` and `ε_n → 0`, with `ε_n³ = e^{-γ/ν_n} ν_n^{Re κ-5-2σ₀} /(2|𝒞(σ₀)|)`, `γ = Re λ > 0`.

Write `x_n = ν_n⁻¹ → ∞`.  Then `e^{-γ/ν_n} ν_n^r = x_n^{-r} e^{-γ x_n}` with `r = Re κ - 5 - 2σ₀`,
which tends to `0` by `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`.  Dividing by `2‖𝒞(σ₀)‖ > 0`
and taking the cube root (`rpow_const_nhds_zero`) gives `ε_n → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The rewriting `e^{-(γ/ν)} ν^r = (ν⁻¹)^{-r} e^{-γ ν⁻¹}` for `ν > 0`. -/
theorem retAux_exp_mul_rpow (ν γ r : ℝ) (hν : 0 < ν) :
    Real.exp (-(γ / ν)) * ν ^ r = (ν⁻¹) ^ (-r) * Real.exp (-γ * ν⁻¹) := by
  rw [Real.inv_rpow hν.le, Real.rpow_neg hν.le, inv_inv, div_eq_mul_inv, neg_mul]
  ring

theorem retNu_retEps_eventually_le_one {Pl : PlanarData} {σ₀ : ℝ} (hω : Pl.eigenvalue.im ≠ 0) (hγ : 0 < Pl.eigenvalue.re) (hC : Pl.signedCoeff σ₀ ≠ 0) : ∀ᶠ n : ℕ in atTop, retNu Pl σ₀ n ≤ 1 ∧ retEps Pl σ₀ n ≤ 1 := by
  have hdpos : 0 < 2 * ‖Pl.signedCoeff σ₀‖ := mul_pos two_pos (norm_pos_iff.2 hC)
  have hνpos : ∀ n : ℕ, 0 < retNu Pl σ₀ n := fun n => retNu_pos Pl σ₀ n
  have hνT : Tendsto (retNu Pl σ₀) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨retNu_tendsto σ₀ hω, Eventually.of_forall hνpos⟩
  have hxT : Tendsto (fun n : ℕ => (retNu Pl σ₀ n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hνT
  have hG : Tendsto (fun x : ℝ => x ^ (-(Pl.kappa.re - 5 - 2 * σ₀)) * Real.exp (-Pl.eigenvalue.re * x))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hγ
  have h2 : Tendsto (fun n : ℕ => ((retNu Pl σ₀ n)⁻¹) ^ (-(Pl.kappa.re - 5 - 2 * σ₀)) *
      Real.exp (-Pl.eigenvalue.re * (retNu Pl σ₀ n)⁻¹) / (2 * ‖Pl.signedCoeff σ₀‖)) atTop (𝓝 0) := by
    have h := (hG.comp hxT).div_const (2 * ‖Pl.signedCoeff σ₀‖)
    rw [zero_div] at h
    exact h
  have hbase : Tendsto (fun n : ℕ => Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
      retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖)) atTop (𝓝 0) := by
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) h2
    dsimp only
    rw [retAux_exp_mul_rpow _ _ _ (hνpos n)]
  have hEps : Tendsto (fun n : ℕ => retEps Pl σ₀ n) atTop (𝓝 0) :=
    hbase.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1 / 3)
  have hEv : ∀ᶠ n : ℕ in atTop, retEps Pl σ₀ n ≤ 1 :=
    Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hEps
  have hνev : ∀ᶠ n : ℕ in atTop, retNu Pl σ₀ n ≤ 1 :=
    Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) (retNu_tendsto σ₀ hω)
  filter_upwards [hνev, hEv] with n h1 h2'
  exact ⟨h1, h2'⟩

end UnforcedLeray.Short.PartIIIb.Concrete

end
