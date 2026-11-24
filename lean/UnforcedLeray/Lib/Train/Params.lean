import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Train parameters at `c = ν⁻²` (INF16 T0)


target T0; decision D8 and bypass B3 of `scoping/README.md` (the train is built at `ρ = 2`,
`c = ν^{-2}`, the instance used by the final construction, tex line 13718).

Blueprint unit **B0139** (`sec:st18-3305`, `paper/main.tex` lines 2042–2058, 2096–2129):
`c = ν^{-ρ}`, `e_c = 1/(ν c²)`, heat width `a(s) = 1 + ν s`, slow time `σ = ν s`, overlap age
`s_c = (c² - 1)/ν` (tex lines 2052–2056, 2196–2199) and overlap variable `T = ν(s - s_c)/c²`.
Here `ρ = 2` (labelled specialization, scoping README Q1).

Main declarations: `per` (`c = ν⁻²`), `ec` (`e_c = ν³`), `width` (`a(s)`), `slowTime`,
`sOv` (`s_c`), `ovT` (the overlap variable), with `ec_eq` (`e_c = (ν c²)⁻¹`), `ec_pos`,
`ec_le_one`, `sOv_eq`, `width_sOv` (`a(s_c) = c²`), `per_eq_rpow`, `one_le_per`,
`two_le_per`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Train

/-- The period `c = ν^{-2}` (tex line 2044 with `ρ = 2`; bypass B3). -/
def per (ν : ℝ) : ℝ := ν⁻¹ ^ 2

/-- The overlap coefficient at `c = ν⁻²`: `e_c = (ν c²)⁻¹ = ν³` (tex lines 2056–2057, 2100). -/
def ec (ν : ℝ) : ℝ := ν ^ 3

/-- The heat width `a(s) = 1 + ν s` (tex lines 2052, 2197). -/
def width (ν s : ℝ) : ℝ := 1 + ν * s

/-- Slow time `σ = ν s` (tex line 2197). -/
def slowTime (ν s : ℝ) : ℝ := ν * s

/-- The overlap age `s_c = (c² - 1)/ν` at `c = ν⁻²` (tex lines 2053, 2198). -/
def sOv (ν : ℝ) : ℝ := (per ν ^ 2 - 1) / ν

/-- The overlap variable `T = ν (s - s_c)/c²` (tex lines 2054–2055). -/
def ovT (ν s : ℝ) : ℝ := ν * (s - sOv ν) / per ν ^ 2

theorem width_eq_one_add_slowTime (ν s : ℝ) : width ν s = 1 + slowTime ν s := rfl

theorem per_pos {ν : ℝ} (hν : 0 < ν) : 0 < per ν := by unfold per; positivity

/-- `c = ν^{-ρ}` with `ρ = 2` (tex line 2044), as a real power. -/
theorem per_eq_rpow {ν : ℝ} (hν : 0 < ν) : per ν = ν ^ (-(2 : ℝ)) := by
  rw [per, Real.rpow_neg hν.le, inv_pow]
  norm_cast

/-- `c ≥ 1` for `0 < ν ≤ 1`. -/
theorem one_le_per {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : 1 ≤ per ν := by
  unfold per
  have : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  nlinarith

/-- The manuscript's standing `c ≥ 2` (tex line 2183) holds for `0 < ν ≤ 1/2`. -/
theorem two_le_per {ν : ℝ} (hν : 0 < ν) (hν2 : ν ≤ 1 / 2) : 2 ≤ per ν := by
  unfold per
  have : 2 ≤ ν⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hν]; linarith
  nlinarith

/-- `e_c = (ν c²)⁻¹` (tex line 2100) at `c = ν⁻²`. -/
theorem ec_eq {ν : ℝ} (hν : ν ≠ 0) : ec ν = (ν * per ν ^ 2)⁻¹ := by
  unfold ec per
  field_simp

theorem ec_pos {ν : ℝ} (hν : 0 < ν) : 0 < ec ν := by unfold ec; positivity

/-- `0 < e_c ≤ 1` for `0 < ν ≤ 1`. -/
theorem ec_le_one {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : ec ν ≤ 1 := by
  unfold ec
  exact pow_le_one₀ hν.le hν1

/-- `s_c = (ν⁻⁴ - 1)/ν`. -/
theorem sOv_eq (ν : ℝ) : sOv ν = (ν⁻¹ ^ 4 - 1) / ν := by
  unfold sOv per; ring

/-- `a(s_c) = c²`: the overlap age is where the heat width reaches the period squared. -/
theorem width_sOv {ν : ℝ} (hν : ν ≠ 0) : width ν (sOv ν) = per ν ^ 2 := by
  unfold width sOv
  field_simp
  ring

theorem sOv_nonneg {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : 0 ≤ sOv ν := by
  unfold sOv
  have h1 := one_le_per hν hν1
  apply div_nonneg _ hν.le
  nlinarith

theorem one_le_width {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) : 1 ≤ width ν s := by
  unfold width; nlinarith [mul_nonneg hν hs]

theorem width_pos {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) : 0 < width ν s :=
  lt_of_lt_of_le one_pos (one_le_width hν hs)

/-- `1 ≤ a(s) ≤ c²` exactly on the pre-overlap range `0 ≤ s ≤ s_c`. -/
theorem width_le_per_sq {ν s : ℝ} (hν : 0 < ν) (hs : s ≤ sOv ν) : width ν s ≤ per ν ^ 2 := by
  rw [← width_sOv hν.ne']
  unfold width
  nlinarith

/-- The overlap variable vanishes at the overlap age. -/
theorem ovT_sOv (ν : ℝ) : ovT ν (sOv ν) = 0 := by simp [ovT]

end UnforcedLeray.Train
