import UnforcedLeray.Units.B0418

/-!
# B0419 — `L^q` decay of the free similarity semigroup (`eq:free-stress-8`)

Blueprint unit B0419, `paper/main.tex` lines 7420--7425, in the proof
"Semigroup construction and initial inverse bound" (§`sec:st18-8976`):

> The heat semigroup is contractive on spatial `L^q`, and the dilation Jacobian yields
> `‖S_ν(r)‖_{L^q → L^q} ≤ e^{-γ_q r}`.  (eq:free-stress-8)

with `γ_q = ½(3/q - 1)` (tex line 7368) and `S_ν(r)` the explicit free similarity semigroup
`S_ν(r)h(y) = e^{r/2} [e^{ν(e^r-1)Δ} h](e^{r/2} y)` of `eq:free-stress-7` (unit B0418).

## Conventions and reuse

* `S_ν(r)` on fields is the library operator `AncientLocalization.freeEvolution ν r`
  (`lean/UnforcedLeray/Analysis/AncientLocalization/FreeEvolution.lean`); on `L^q` classes it
  is the B0418 operator `B0418.freeSemigroupLp hq ν r`

* `γ_q` is the B0418 definition `B0418.gammaExp q = (3 / q.toReal - 1) / 2`

  is assumed throughout, `q.toReal` is the actual exponent (no `toReal ∞ = 0` junk value);
  `gammaExp_ofReal` records `γ_q = (3/q - 1)/2` for a real exponent `q`.
* The heat factor `e^{tΔ}h` is the library `Heat.flow`, a literal Gaussian Bochner integral
  which converges absolutely at every point for `h ∈ L^q`, `1 ≤ q < ∞`
  (`B0418.heat_integrand_integrable`), so no integral junk value enters.
* Fields are real three-vector fields `SpatialField = Space → Space` on `Space = ℝ³`
  (the manuscript treats complex fields componentwise), as in B0418.
* Exponent range: `1 ≤ q < ∞` (blueprint statement). The enclosing theorem (tex line 7365)
  only uses `1 < q < 3`, and the section's standing assumption is `ν > 0`; neither the
  restriction `q < 3` nor `ν > 0` is needed, so no hypothesis is stronger than the
  manuscript's. The bound holds for every real `r`; the unit asserts it for `r ≥ 0`.
  For `ν ≤ 0` (outside the manuscript) the heat time `ν(e^r-1)` is `≤ 0` when `r ≥ 0`, and
  the library's `Heat.flow` at a nonpositive time is the identity (`Heat.flow_nonpos`), so
  `S_ν(r)` is then the pure dilation; the bound is still true there but says nothing about a
  backward heat flow. The manuscript's case is `ν > 0`, which the statements cover.

## Proof (as in the manuscript)

`S_ν(r) = D ∘ e^{ν(e^r-1)Δ}` with `D h(y) = e^{r/2} h(e^{r/2} y)`. The dilation is an exact
`L^q` scaling, `‖D g‖_q = e^{r/2} e^{-3r/(2q)} ‖g‖_q = e^{-γ_q r} ‖g‖_q`
(`eLpNorm_freeEvolution_eq`, the "dilation Jacobian"), and the heat flow is an `L^q`
contraction by Young's inequality with the unit-mass Gaussian (`heat_contraction`,
which is `B0418.eLpNorm_flow_le`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0419

open UnforcedLeray.AncientLocalization UnforcedLeray.B0418

variable {q : ℝ≥0∞}

/-! ### The decay exponent `γ_q` -/

/-- `γ_q = ½(3/q - 1)` for a real exponent `q ≥ 0` (tex line 7368), stated through the
B0418 definition `gammaExp`. -/
theorem gammaExp_ofReal {q : ℝ} (hq : 0 ≤ q) :
    gammaExp (ENNReal.ofReal q) = (3 / q - 1) / 2 := by
  rw [gammaExp, ENNReal.toReal_ofReal hq]

/-- At `q = 2`, `γ_2 = 1/4`: the bound `eq:free-stress-8` is then the library's
`freeEvolution_l2Norm_le` decay `e^{-r/4}`. -/
theorem gammaExp_two : gammaExp 2 = 1 / 4 := by
  rw [gammaExp, ENNReal.toReal_ofNat]
  norm_num

/-! ### The two ingredients named in the proof (tex lines 7420--7422) -/

/-- "The heat semigroup is contractive on spatial `L^q`" (tex lines 7420--7421):
`‖e^{tΔ}h‖_q ≤ ‖h‖_q` for `1 ≤ q < ∞` and `h ∈ L^q` (Young's inequality with the unit-mass
Gaussian; B0418 `eLpNorm_flow_le`). -/
theorem heat_contraction (hq1 : 1 ≤ q) (hq : q ≠ ∞) {h : SpatialField}
    (hh : MemLp h q volume) (t : ℝ) :
    eLpNorm (Heat.flow h t) q volume ≤ eLpNorm h q volume :=
  eLpNorm_flow_le hq1 hq hh t

/-- "The dilation Jacobian" (tex lines 7421--7422): the exact identity
`‖S_ν(r)h‖_q = e^{-γ_q r} ‖e^{ν(e^r-1)Δ}h‖_q`, i.e. `e^{r/2} e^{-3r/(2q)} = e^{-γ_q r}`.
No integrability of `h` is needed for this identity of extended norms. -/
theorem eLpNorm_freeEvolution_eq (hq : q ≠ ∞) (h : SpatialField) (ν r : ℝ) :
    eLpNorm (freeEvolution ν r h) q volume =
      ENNReal.ofReal (Real.exp (-gammaExp q * r)) *
        eLpNorm (Heat.flow h (ν * (Real.exp r - 1))) q volume := by
  unfold freeEvolution similarityDilation
  rw [eLpNorm_spatialScale_Lp hq _ (Real.exp_pos _).ne', ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, abs_of_pos (by positivity),
    ← Real.exp_nat_mul, ← Real.exp_neg,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [gammaExp, ENNReal.toReal_div, ENNReal.toReal_one]
  push_cast
  ring

/-! ### The bound `eq:free-stress-8` -/

/-- `eq:free-stress-8` on fields: for `1 ≤ q < ∞`, `h ∈ L^q` and `r ≥ 0`,
`‖S_ν(r)h‖_q ≤ e^{-γ_q r} ‖h‖_q`. Proved from the two ingredients above. -/
theorem eLpNorm_freeEvolution_le_of_nonneg (hq1 : 1 ≤ q) (hq : q ≠ ∞) (ν : ℝ)
    {h : SpatialField} (hh : MemLp h q volume) {r : ℝ} (_hr : 0 ≤ r) :
    eLpNorm (freeEvolution ν r h) q volume ≤
      ENNReal.ofReal (Real.exp (-gammaExp q * r)) * eLpNorm h q volume := by
  rw [eLpNorm_freeEvolution_eq hq h ν r]
  gcongr
  exact heat_contraction hq1 hq hh _

/-- `S_ν(r)` maps `L^q` into `L^q`, `1 ≤ q < ∞` (so the operator norm is meaningful). -/
theorem freeEvolution_memLp' (hq1 : 1 ≤ q) (hq : q ≠ ∞) (ν r : ℝ) {h : SpatialField}
    (hh : MemLp h q volume) : MemLp (freeEvolution ν r h) q volume :=
  freeEvolution_memLp hq1 hq hh ν r

/-- **Unit B0419**, `eq:free-stress-8` (tex lines 7420--7425). For `1 ≤ q < ∞`, every `ν`
and every `r ≥ 0`, the free similarity semigroup `S_ν(r)` of `eq:free-stress-7` (B0418),
as a bounded operator on `L^q(ℝ³; ℝ³)`, satisfies
`‖S_ν(r)‖_{L^q → L^q} ≤ e^{-γ_q r}`, `γ_q = ½(3/q - 1)`;
equivalently `‖S_ν(r)h‖_q ≤ e^{-γ_q r}‖h‖_q` for every field `h ∈ L^q`, where `S_ν(r)h` is the
literal formula `e^{r/2}[e^{ν(e^r-1)Δ}h](e^{r/2}y)`. -/
theorem free_semigroup_Lq_decay [Fact (1 ≤ q)] (hq : q ≠ ∞) (ν : ℝ) :
    (∀ r : ℝ, 0 ≤ r → ‖freeSemigroupLp hq ν r‖ ≤ Real.exp (-gammaExp q * r)) ∧
    (∀ r : ℝ, 0 ≤ r → ∀ h : SpatialField, MemLp h q volume →
      eLpNorm (fun y => Real.exp (r / 2) •
          Heat.flow h (ν * (Real.exp r - 1)) (Real.exp (r / 2) • y)) q volume ≤
        ENNReal.ofReal (Real.exp (-gammaExp q * r)) * eLpNorm h q volume) := by
  refine ⟨fun r _ => norm_freeSemigroupLp_le hq ν r, fun r hr h hh => ?_⟩
  have he : (fun y => Real.exp (r / 2) •
      Heat.flow h (ν * (Real.exp r - 1)) (Real.exp (r / 2) • y)) = freeEvolution ν r h := by
    funext y
    exact (freeEvolution_apply ν r h y).symm
  rw [he]
  exact eLpNorm_freeEvolution_le_of_nonneg Fact.out hq ν hh hr

/-- `eq:free-stress-8` with a real exponent `1 ≤ q < ∞` and the literal
`γ_q = ½(3/q - 1)` (tex line 7368): `‖S_ν(r)h‖_q ≤ e^{-(3/q-1) r / 2} ‖h‖_q` for `r ≥ 0`. -/
theorem eLpNorm_freeEvolution_le_real {q : ℝ} (hq : 1 ≤ q) (ν : ℝ) {h : SpatialField}
    (hh : MemLp h (ENNReal.ofReal q) volume) {r : ℝ} (hr : 0 ≤ r) :
    eLpNorm (freeEvolution ν r h) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Real.exp (-((3 / q - 1) / 2) * r)) *
        eLpNorm h (ENNReal.ofReal q) volume := by
  rw [← gammaExp_ofReal (by linarith)]
  exact eLpNorm_freeEvolution_le_of_nonneg (by simpa using ENNReal.ofReal_le_ofReal hq)
    ENNReal.ofReal_ne_top ν hh hr

/-- At `q = 2` the operator bound reads `‖S_ν(r)‖_{L² → L²} ≤ e^{-r/4}`, consistent with the
library's `AncientLocalization.freeEvolution_l2Norm_le`. -/
theorem norm_freeSemigroupLp_two_le (ν r : ℝ) :
    ‖freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top ν r‖ ≤ Real.exp (-r / 4) := by
  have h := norm_freeSemigroupLp_le (p := 2) ENNReal.ofNat_ne_top ν r
  rw [gammaExp_two] at h
  convert h using 2
  ring

end UnforcedLeray.B0419
