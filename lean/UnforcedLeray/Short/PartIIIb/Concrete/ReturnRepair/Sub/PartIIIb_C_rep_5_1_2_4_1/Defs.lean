import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin

/-!
# `Y` on one output bin: the physical majorant and the two-step reduction

Source `the November 2 reference manuscript` 5585-5593 (+4161-4186, 3604-3621).

`WardYBinMassAt` (the bin kernel bound) is the composition of

1. `WardYPointDom` : the pointwise domination, off the axis, of `Y = D_{μ+1}𝒞_y(W_μ - W_{μ+1})` at
   `(τ, y)` by the gap-kernel majorant `wardYKerMaj` (sources of horizontal radius
   `ϱ(z) < θ ϱ(y)`, `θ = e^{-δ/2}`; kernel `|y - λz|^{-4}`, 3604-3610, 5588-5589) plus the stream
   majorant `wardYStreamMaj` (outward primitive of that kernel, 4178-4186, 5592);
2. `WardYMajBin` : the chart bin `L²` bound of the gap-kernel majorant (order-four kernel `L²` norm
   `C D^{-5/2}`, Minkowski over the source, chart normalization `s^{-1/2}`, `𝒩_T g = s g`;
   5588-5593);
3. `WardYStreamMajBin` : the same bound for the stream majorant (5592).

`wardYBinMass_of` proves the composition (monotonicity of the lintegral, `‖(w_r,w_z)‖ ≤ ‖w‖`,
`(a+b)² ≤ 2a² + 2b²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The gap-kernel majorant at `(τ, y)`: `∫₀¹ ∫_{ϱ(z) < θ ϱ(y)} |y - λz|^{-4} |𝒩_T g(z, τ + 2 log λ)| dz dλ`
(source 3611-3621 for the form, 3604-3610 for the kernel, 5588-5589 for the radial gap). -/
def wardYKerMaj (R c θ : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < θ * ϱ y},
    ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
      UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) (τ + 2 * Real.log l) z

/-- The stream majorant at `(τ, y)`:
`∫₀¹ ∫_{ϱ(z) < θ ϱ(y)} ϱ(y)^{-2} (ϱ(y)² + (y₃ - λz₃)²)^{-1} |𝒩_T g(z, τ + 2 log λ)| dz dλ`
(source 4178-4186 and 5592 "the outward stream primitive obeys the same bound").  The stream terms
`(χ_y'/r) Ψ_Z e_z` of `𝒞_y` (and their `D_{μ+1}`-derivatives) carry the outward primitive
`Ψ_Z(r, y₃) = -∫_r^∞ ρ Z_z(ρ, y₃) dρ` of the order-four kernel; across the radial gap
`∫_r^∞ ρ ((ρ - θr)² + h²)^{-2} dρ ≤ C (r² + h²)^{-1}` (`h = |y₃ - λz₃|`) and `χ_y'/r = O(r^{-2})`.
This kernel is not dominated by `|y - λz|^{-4}` uniformly in `h` (that would need the vanishing
total flux of the axisymmetric field), but it has the same bin `L²` scaling `D^{-5/2}`. -/
def wardYStreamMaj (R c θ : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < θ * ϱ y},
    ENNReal.ofReal ((ϱ y ^ 2 * (ϱ y ^ 2 + (y 2 - l * z 2) ^ 2))⁻¹) *
      UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) (τ + 2 * Real.log l) z

/-- The chart majorant `p ↦ s^{-1/2} · wardYKerMaj` at `(τ, y) = (chartTau R p, chartY R p)`. -/
def wardYChartMaj (R c θ : ℝ) (g : Chart → Ten3) (p : Chart) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt p.1)⁻¹ *
    wardYKerMaj R c θ g (NearInst.chartTau R p) (NearInst.chartY R p)

/-- The chart stream majorant `p ↦ s^{-1/2} · wardYStreamMaj` at `(chartTau R p, chartY R p)`. -/
def wardYStreamChartMaj (R c θ : ℝ) (g : Chart → Ten3) (p : Chart) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt p.1)⁻¹ *
    wardYStreamMaj R c θ g (NearInst.chartTau R p) (NearInst.chartY R p)

/-- **(i)+(ii)+(iv): pointwise domination of `Y`** (source 5585-5589, 4161-4186).  For `0 < ν`,
`0 < R`, `δ < log(12/11)`, a young cutoff `χy`, and a source `g` vanishing at ages `< 6/(5ν)`:
`|Y(τ,y)| ≤ C ν^{-k} · (wardYKerMaj + wardYStreamMaj)` for every `(τ, y)` off the axis (`0 < ϱ y`; the source's
age `s = R²/r²` is defined only for `r > 0`, line 4163, and the axis is null for the chart measure;
in Lean `age R y = R²/0 = 0` there, so `χ_y = 1` and `Y` need not vanish while the majorant does).  (For `ν·age(y) > 1` the left side is zero,
the stream cutoff and its derivative vanishing near `y`; for `ν·age(y) ≤ 1` all sources have age
`≥ 6/(5ν) > e^δ/ν`, so `ϱ(z) ≤ √(5/6) ϱ(y) < e^{-δ/2}ϱ(y)`: the radial gap `|y - λz| ≥
(1-θ)ϱ(y)` is automatic, and `D_{μ+1}`, the cutoff and the outward primitive are bounded by the
order-four kernel `|x|^{-4}`, uniformly for `λ^{2μ+2}`, `μ` in the window.) -/
def WardYPointDom (ν μ R c δ : ℝ) (χy : ℝ → ℝ) (C : ℝ) (k : ℕ) : Prop :=
  0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsYoungCutoff χy → δ < Real.log (12 / 11) → 0 < δ →
    ∀ g : Chart → Ten3, Measurable g → (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) →
      ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
        ‖wardY ν μ R c χy g τ y‖ₑ ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k) * (wardYKerMaj R c (Real.exp (-(δ / 2))) g τ y +
            wardYStreamMaj R c (Real.exp (-(δ / 2))) g τ y)

/-- **(iii): the chart bin bound of the majorant** (source 5588-5593): the `L²(bin, ageμ c (-3/2))`
norm of `wardYChartMaj` is `≤ C ν^{-k} ε^{3/2} s^{5/4} · N₀(e^{δ-h}s)`, `R = ε⁻¹`, `s` the bin
upper age. -/
def WardYMajBin (ν ε c δ h S : ℝ) (C : ℝ) (k : ℕ) : Prop :=
  0 < ν → 0 < ε → 0 < c → 0 < δ → δ < Real.log (12 / 11) → h = δ / 4 →
    ∀ (j : ℕ) (g : Chart → Ten3), Measurable g → (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) →
      (∫⁻ p in binSet S h j, wardYChartMaj ε⁻¹ c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ)
          ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ (3 / 2 : ℝ) * binUpper S h j ^ (5 / 4 : ℝ)) *
          ageMass c (Real.exp (δ - h) * binUpper S h j) g

/-- **The chart bin bound of the stream majorant** (source 5592 "The outward stream primitive obeys
the same bound", 5588-5593): measurability of the chart stream majorant and the same bin `L²`
bound as `WardYMajBin`.  The kernel `ϱ(y)^{-2}(ϱ(y)² + h²)^{-1}` has, over an output bin of
radius `r ≍ R/√s`, the same `L²` scaling `r^{-5/2}` as the order-four kernel off the gap. -/
def WardYStreamMajBin (ν ε c δ h S : ℝ) (C : ℝ) (k : ℕ) : Prop :=
  0 < ν → 0 < ε → 0 < c → 0 < δ → δ < Real.log (12 / 11) → h = δ / 4 →
    ∀ (j : ℕ) (g : Chart → Ten3), Measurable g → (∀ p : Chart, p.1 < 6 / (5 * ν) → g p = 0) →
      AEMeasurable (wardYStreamChartMaj ε⁻¹ c (Real.exp (-(δ / 2))) g)
          ((ageμ c (-3 / 2)).restrict (binSet S h j)) ∧
      (∫⁻ p in binSet S h j, wardYStreamChartMaj ε⁻¹ c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ)
          ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ (3 / 2 : ℝ) * binUpper S h j ^ (5 / 4 : ℝ)) *
          ageMass c (Real.exp (δ - h) * binUpper S h j) g

/-- Sequence-level `WardYPointDom` (uniform for large `n`, `z ∈ [-1,1]`). -/
def SeqData.WardYPointDomSeq (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    WardYPointDom (D.level n).ν (D.mu n z) (D.level n).ε⁻¹ (cOf (D.level n).ν) D.K.δ D.K.χy C k

/-- Sequence-level `WardYMajBin`. -/
def SeqData.WardYMajBinSeq (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    WardYMajBin (D.level n).ν (D.level n).ε (cOf (D.level n).ν) D.K.δ D.K.hbin
      ((D.level n).Scut D.K) C k

/-- Sequence-level `WardYStreamMajBin`. -/
def SeqData.WardYStreamMajBinSeq (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    WardYStreamMajBin (D.level n).ν (D.level n).ε (cOf (D.level n).ν) D.K.δ D.K.hbin
      ((D.level n).Scut D.K) C k

/-- The meridional pair has norm at most the Euclidean norm of the vector. -/
theorem merid_norm_le (v : Space) : ‖(!₂[v 0, v 2] : Merid)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_three, Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 1)]

end UnforcedLeray.Short.PartIIIb.Concrete

end
