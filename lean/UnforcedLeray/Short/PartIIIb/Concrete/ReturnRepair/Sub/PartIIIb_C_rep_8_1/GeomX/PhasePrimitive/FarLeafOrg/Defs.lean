import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T17

/-!
# Statements for the far-field oscillation leaf `SepOscFar` (organizer sm0)

Source `the November 2 reference manuscript`
lines 5400-5427 (degree `-5` of `D∇K`, ratio old/young radius `< 1`, one phase primitive in the
dilation variable with its dilation-one boundary term kept) and 3768-3790 (`sep:mean-comparison`,
oscillatory part).

Plan.  For a zero-mean `c`-periodic source the response `∇_yW_μ` at `y = ε⁻¹ x_obs` is a sum of
the `l`-integrals `∫_0^1 ω(l) f(q₀ + ε⁻¹ log l) dl`, `ω(l) = l^{2μ+2} D_w∇_kK_{ν(1-l²)}(y - l z)`,
and `f(q(l)) = ε l ∂_l[Jf(q(l))]` (`J f = ∫_0^q f`, bounded by `∫_0^c |f|`).  One integration by
parts in `l` gives a bound **independent of `τ`**:
`ε (∫_0^c|f|) (b|ω(b)| + ∫_0^b |ω + l ω'|)` and the boundary at `l = 0` vanishes since
`2 Re μ + 3 > 0`.  The kernel bounds `FarKerDt` (`∂_t K_t = ΔK_t`) give
`|ω| , |ω + lω'| ≲ l^{2Re μ+2} ε^5 (r - ρ_o)^{-5} (1 + ...)`, `r = |x_obs'| ≥ ρ_i`, with
`r/(r-ρ_o) ≤ ρ_i/(ρ_i-ρ_o)`; integrating over the source (`dz = ε⁻² dx' dY`) gives `ε⁴ r⁻⁵`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray.Short.IIIa

/-- **(a) Far kernel derivative bounds with the age derivative** (SP 3604-3610 with `∂_tK_t = ΔK_t`,
`UnforcedLeray.Short.PartIIIb.Concrete.heatLerayK_heat`, joint `C³`:
`heatLerayK_jointC3`): `∂_t∇_kK_t = ∇_kΔK_t`, so `D^n∂_t∇_kK_t` is a derivative of `K_t` of order
`n + 3` and `SepKernelBounds` (theorem `sepKernelBounds`, `j = n + 2 ≤ 3`) gives the bound
`C |x|^{-6-n}`, uniformly in `t > 0`. -/
def FarKerDt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j k : Fin 3) (t : ℝ), 0 < t → ∀ x : Space, x ≠ 0 → ∀ n : ℕ, n ≤ 1 →
    ‖iteratedFDeriv ℝ n (fun y => deriv (fun s => fderiv ℝ (fun x' => heatLerayK s i j x') y
      (UnforcedLeray.coordinateVector k)) t) x‖ ≤ C * ‖x‖ ^ (-6 - (n : ℝ))

/-- **(b) One phase primitive in the dilation variable** (SP 5400-5427, 3768-3790): for a measurable
`c`-periodic zero-mean `f` and a coefficient `ω` that is `C¹` on `(0,1)` with
`‖ω(l)‖, ‖ω(l) + lω'(l)‖ ≤ M l^{δ-1}` on `(0,b]` (`δ > 0`), integration by parts in `l` against
`f(q₀ + ε⁻¹ log l) = ε l ∂_l[Jf(q₀ + ε⁻¹ log l)]` (`Jf(s) = ∫_0^s f`, `|Jf| ≤ ∫_0^c |f|` by
periodicity and zero mean; boundary at `l = 0` is `ε l ω(l) Jf → 0`; boundary at `l = b` kept) gives
`‖∫_0^b ω(l) f(q₀+ε⁻¹log l) dl‖ ≤ ε (∫_0^c|f|) (b‖ω(b)‖ + ∫_0^b ‖ω + lω'‖ dl)`.
Suggested proof: substitute `l = exp(ε(s-q₀))` and use Fubini for `Jf(s) = ∫_0^s f` (a function
that is merely absolutely continuous, so no pointwise product rule is available). -/
def PhaseIBP : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∀ f : ℝ → ℝ, Measurable f → (∀ q, f (q + c) = f q) →
    IntervalIntegrable f volume 0 c → (∫ q in (0 : ℝ)..c, f q) = 0 →
    ∀ (q₀ : ℝ) (ω : ℝ → ℂ) (b δ M : ℝ), 0 < b → b < 1 → 0 < δ → 0 ≤ M →
      ContDiffOn ℝ 1 ω (Ioo (0 : ℝ) 1) →
      (∀ l ∈ Ioc (0 : ℝ) b, ‖ω l‖ ≤ M * l ^ (δ - 1)) →
      (∀ l ∈ Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖ ≤ M * l ^ (δ - 1)) →
        ‖∫ l in Ioc (0 : ℝ) b, ω l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ ≤
          ε * (∫ q in (0 : ℝ)..c, |f q|) *
            (b * ‖ω b‖ + ∫ l in Ioc (0 : ℝ) b, ‖ω l + (l : ℂ) * deriv ω l‖)

/-- **(c) The oscillatory estimate for one source point** (SP 5400-5427, 3768-3790): `z` is a
source point with `ε|z'| ≤ ρ_o` (so `x' = εz'`, `Y = z₃`), `q₀ = ε⁻¹ log(ε|z'|) + τ/(2ε)` the phase
of the point, `f` the phase profile `q ↦ F_{jk}(x',Y,q)`.  The `l`-integral of the
`w`-directional `y`-derivative of the kernel factor of `sepW` is bounded, *independently of `q₀`
(hence of `τ`)*, by `ε⁶ (1+|z₃|) r^{-5}` times polynomial factors, times `∫_0^c ‖f‖` (this is
`ENNReal`-valued so that a non-integrable profile gives `⊤`; `C` may be taken positive).
Proof: `PhaseIBP` with `ω(l) = l^{2μ+2} D_w∂_kK_{ν(1-l²),ij}(y - lz)`, `δ = 2 Re μ + 3 ≥ 5/2`,
`ω + lω' = (2μ+3) ω - 2νl³ l^{2μ+2}(D_w∂_t∂_kK)(·) - l^{2μ+3} D_z D_w∂_kK(·)`
(`FarKerDt`, `sepKernelBounds` for `j ≤ 2`, gap `|y - lz| ≥ (r - ρ_o)/ε`, `|z| ≤ ρ_o/ε + |z₃|`,
`r/(r-ρ_o) ≤ ρ_i/(ρ_i-ρ_o)`, `ν ≤ 1`, `ε ≤ 1`); take `b → 1` (the bound is uniform in `b<1`,
`Ioo 0 1` integral is the limit of `Ioc 0 b`). -/
def OscPoint : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ f : ℝ → ℝ, Measurable f → (∀ q, f (q + c) = f q) → (∫ q in Ioc 0 c, f q) = 0 →
      ∀ (z xo : Space) (q₀ : ℝ), ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo →
        ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (i j k : Fin 3) (w : Space), ‖w‖ ≤ 1 →
          ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
              ((fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
                (y' - l • z) (UnforcedLeray.coordinateVector k)) (ε⁻¹ • xo) w : ℝ) : ℂ) *
              ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ₑ ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ m * ε ^ 6 *
                (1 + |z 2|) * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) *
              ∫⁻ q in Ioc 0 c, ‖f q‖ₑ

/-- **(d) Pointwise-in-`τ` far oscillation estimate** (SP 5400-5427): the same as `SepOscFar`
for a zero-mean source, with the majorant the constant right-hand side, valid at **every** `τ`.
Proof: (i) at every `τ` the order-`0` majorant `∫_0^1 l^{2Re μ+2} ∫ |y-lz|^{-4}|T(z,τ+2log l)| dz dl`
is finite (gap, `l ≤ 1`, Tonelli, sum over periods of `l ↦ l^{2Re μ+3}`, `thinMoment ≠ ⊤`), so
`∇_y W_μ` is the integral of the `y`-derivative of the integrand (differentiation under the
integral; reuse the machinery of `PartIII-a_T16_1_1`: `sepDiffF`, `sepDiffRho`, `HeatLerayKSmoothAll`,
`SepDiffFMeas`, `SepDiffFDerivBound`); (ii) apply `OscPoint` at each `z` (the point has
`ε|z'| ≤ ρ_o` on the support, `q₀(z)` as above, `f = F_{jk}(εz', z₃, ·)`, the nine `(j,k)` and the
direction `w` cost an absolute constant); (iii) integrate in `z`: `dz = ε⁻² dx' dY`
(polar coordinates in `z'`), so the total is `ε⁴`; (iv) `∫_0^c‖F_{jk}‖ ≤ c (c⁻¹∫_0^c ‖F‖²)^{1/2}`
(Cauchy-Schwarz) and `(1 + |Y|)` is the weight in `thinMoment`. -/
def OscFarPt : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        (∀ x' Y i j, ∫ q in Ioc 0 c, F x' Y q i j = 0) →
        thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ τ : ℝ,
          ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo)‖ₑ ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * thinMoment c F

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
