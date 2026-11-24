import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3
import UnforcedLeray.Lib.AxisymmetricB.Average
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3`: design of the proof of `WardYMajBinCore`

Source `the November 2 reference manuscript` 5585-5593 (bins, radial gap,
order-four kernel `L²` norm `C D^{-5/2}`, Minkowski and the mass `N₀`), 5571-5575 (`N₀(a)`),
3604-3621 (`|∇K_t(x)| ≤ C|x|^{-4}`, the resolvent `W_μ`), 2672-2684 (chart
`s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`, `𝒩_T T = sT`, physical Jacobian
`πR² s^{-5/2} ds dη`, normalized phase `dq/c`), 4171 (`X₀ = W_μ - W_{μ+1}`).

## Architecture (physical phase space, one Minkowski over source atoms)

Write `P = 2c/R` (the phase period), `G = ‖g‖ₑ`, `θ = e^{-δ/2}`, and for the output bin
`(s₁, s₀]`, `s₀ = s_j`, `s₁ = s_{j+1} = e^{-h}s₀`.

1. `ChartMajSq`: `srcNorm(𝒩_T g) ≤ t'·G(chart)` (`cartLiftFrobBound`), so the chart majorant is
   bounded by `s^{-1/2} psiMaj(τ_p, y_p)`, where `psiMaj` has the azimuth-free source weight
   `srcW σ z = age(z)·G(chartOf z σ)`.
2. `ChartToPhys`: `psiMaj` is invariant under rotations about the vertical axis and `P`-periodic
   in `τ`, so the chart `L²` norm on the bin (measure `s^{-1}·s^{-3/2}dς = s^{-5/2}dς`) equals the
   physical `L²` norm over one period: `(2πcR)⁻¹ ∫_{(0,P] × ybin} psiMaj²` (`chartPhaseLIntegral`).
3. `PsiMajRep`: the substitution `λ = e^{(σ-τ)/2}` writes `psiMaj(τ, y) = ∫ phKer(τ, y; σ, z)
   srcW(σ, z) dσ dz` over the source atoms `(σ, z) ∈ ℝ × ℝ³` (no fold needed here).
4. `PsiAtomsMinkowski`: Minkowski's integral inequality over the atoms
   (`NonUniqueEuler.Conv.lintegral_lintegral_rpow_le_of_measurable`).
5. `AtomBound`: for an atom `(σ, z)`, `‖phKer(·; σ, z)‖_{L²((0,P] × ybin)} ≤ √gapA · √omega2(σ)`:
   the radial gap `ϱ(z) < θϱ(y)` gives `|y - λz| ≥ (1-θ)R/√s₀ = D` and `∫_{|x|≥D}|x|^{-8} =
   4π/(5D⁵)` (`gapKernel_sq_lintegral_le`); the phase factor `∫_{(0,P]} 1_{σ<τ} e^{σ-τ}/4 dτ ≤
   (P/4) min(1, e^σ) 1_{σ<P}`.  The kernel vanishes unless `age(z) > s₁/θ² = e^{δ-h}s₀`.
6. `SourceMass`: folding `σ` over periods (`Σ_n √omega2(σ + nP) ≤ √P + 1/√P`, the geometric sum
   `Σ_m e^{-mP/2} ≤ 1 + 2/P` is the factor `1 + c/R`) and `chartPhaseLIntegral` turn
   `∫ 1_{age>a} srcW √omega2` into `(√P + 1/√P) · PπR² · N₀(a)`.
7. `ConstAlgebra`: `(2πcR)^{-1/2} √gapA (√P + 1/√P) PπR² ≤ C₀(θ)(1 + c/R) R^{-3/2} s₀^{5/4}`.

`Main.lean` proves `WardYMajBinCore` from the leaves `ChartMajSq`, `PsiMajMeasurable`,
`PsiMajRotInv`, `PsiMajPeriodic`, `ChartToPhys`, `PsiAtomsMinkowski`, `AtomBound`, `SourceMass`,
`ConstAlgebra`, `BinNull`; the remaining Props are sub-leaves of these.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-! ## Objects -/

/-- The azimuth-free source weight `W(σ, z) = t'·G(chartOf R c z σ)`, `t' = age R z = R²/ϱ(z)²`
(source 2683: `𝒩_T g = s g`; `G = ‖g‖ₑ`). -/
def srcW (R c : ℝ) (G : Chart → ℝ≥0∞) (σ : ℝ) (z : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (age R z) * G (NearInst.chartOf R c z σ)

/-- The azimuth-free majorant `Ψ(τ, y) = ∫₀¹ ∫_{ϱ(z) < θϱ(y)} |y - λz|^{-4} W(τ + 2 log λ, z) dz dλ`
(source 3611-3621 for the form, 3604-3610 for the kernel, 5588-5589 for the radial gap). -/
def psiMaj (R c θ : ℝ) (G : Chart → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in {z : Space | ϱ z < θ * ϱ y},
    ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) * srcW R c G (τ + 2 * Real.log l) z

/-- The phase kernel between the output `(τ, y)` and the source atom `(σ, z)`: with
`λ = e^{(σ-τ)/2}`, `1_{σ<τ} 1_{ϱ(z)<θϱ(y)} (λ/2) |y - λz|^{-4}` (source 3611-3621 after
`σ = τ + 2 log λ`). -/
def phKer (θ τ : ℝ) (y : Space) (σ : ℝ) (z : Space) : ℝ≥0∞ :=
  if σ < τ ∧ ϱ z < θ * ϱ y then
    ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) *
      ENNReal.ofReal ((‖y - Real.exp ((σ - τ) / 2) • z‖ ^ 4)⁻¹)
  else 0

/-- The physical points of the output bin: ages `age R y ∈ (s₁, s₀]` (source 5585-5586). -/
def ybin (R s1 s0 : ℝ) : Set Space := {y | age R y ∈ Ioc s1 s0}

/-- The spatial `L²` constant of the order-four kernel off the radial gap,
`4π/5 · D^{-5}`, `D = (1-θ)R/√s₀` (source 5588-5591). -/
def gapA (θ R s0 : ℝ) : ℝ := 4 * Real.pi / 5 * (((1 - θ) * R / Real.sqrt s0)⁻¹) ^ 5

/-- The phase weight of an atom at phase `σ` over one output period `(0, P]`:
`(P/4) min(1, e^σ)` for `σ < P`, zero otherwise. -/
def omega2 (P σ : ℝ) : ℝ := if σ < P then P / 4 * min 1 (Real.exp σ) else 0

/-- The constant `C₀(θ) = 2 √(4π/5) √π (1-θ)^{-5/2}`. -/
def wyC0 (θ : ℝ) : ℝ :=
  2 * Real.sqrt (4 * Real.pi / 5) * Real.sqrt Real.pi * ((1 - θ)⁻¹) ^ (5 / 2 : ℝ)

/-! ## Leaves (each a Prop proved in its own file) -/

/-- **Chart majorant** (source 2683, 3611-3621, 5588): `srcNorm(𝒩_T g)(σ, z) ≤ age(z)·‖g(chartOf z σ)‖`
(`cartLiftFrobBound`), hence `wardYKerMaj ≤ psiMaj` and, with the chart normalization `s^{-1/2}`,
`wardYChartMaj² ≤ s⁻¹ psiMaj(τ_p, y_p)²`. -/
def ChartMajSq : Prop :=
  ∀ (R c θ : ℝ) (g : Chart → Ten3) (p : Chart),
    wardYChartMaj R c θ g p ^ (2 : ℝ) ≤
      ENNReal.ofReal (p.1⁻¹) *
        psiMaj R c θ (fun q => ‖g q‖ₑ) (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)

/-- Joint measurability of the majorant in `(τ, y)`. -/
def PsiMajMeasurable : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), Measurable G →
    Measurable (fun x : ℝ × Space => psiMaj R c θ G x.1 x.2)

/-- Joint measurability of `phKer · srcW` in output and atom. -/
def KerSrcMeasurable : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), Measurable G →
    Measurable (fun q : (ℝ × Space) × (ℝ × Space) =>
      phKer θ q.1.1 q.1.2 q.2.1 q.2.2 * srcW R c G q.2.1 q.2.2)

/-- Rotation invariance about the vertical axis (the source weight depends on `z` only through
`ϱ(z), z₃`, source 2672-2684). -/
def PsiMajRotInv : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞) (α τ : ℝ) (y : Space),
    psiMaj R c θ G τ (Axi.rotZ α y) = psiMaj R c θ G τ y

/-- `P`-periodicity in the phase (`chartOf` is `2c/R`-periodic, source 2672-2674). -/
def PsiMajPeriodic : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), 0 < R → 0 < c → ∀ y : Space,
    Function.Periodic (fun τ => psiMaj R c θ G τ y) (2 * c / R)

/-- The chart point of `(z, τ)` read back: `chartY` is `z` rotated into the half plane `φ = 0`, and
`chartTau` is `τ` up to a whole number of periods (source 2672-2674). -/
def ChartOfHalfPlane : Prop :=
  ∀ (R c : ℝ) (z : Space) (τ : ℝ), 0 < R → 0 < c → 0 < ϱ z →
    NearInst.chartY R (NearInst.chartOf R c z τ) = !₂[ϱ z, 0, z 2] ∧
      ∃ k : ℤ, NearInst.chartTau R (NearInst.chartOf R c z τ) = τ - k * (2 * c / R)

/-- Every point is rotated into the half plane `φ = 0` by some `rotZ α`. -/
def RotZHalfPlane : Prop := ∀ y : Space, ∃ α : ℝ, Axi.rotZ α y = !₂[ϱ y, 0, y 2]

/-- Age weights: `s⁻¹ · s^{-3/2} dς = s^{-5/2} dς` (source 2679-2684). -/
def AgeμInvShift : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Chart → ℝ≥0∞, Measurable f →
    ∫⁻ p, ENNReal.ofReal (p.1⁻¹) * f p ∂(ageμ c (-3 / 2)) = ∫⁻ p, f p ∂(ageμ c (-5 / 2))

/-- **Chart output to physical output** (source 2679-2684: physical Jacobian `πR² s^{-5/2} ds dη`,
normalized phase `dq/c`).  For a rotation-invariant, `P`-periodic, measurable `Φ` and a set of
positive ages `E`, the chart integral of `s⁻¹ Φ(τ_p, y_p)` against `s^{-3/2}dς` over `{s ∈ E}` is
at most `(2πcR)⁻¹` times the physical integral over one period. -/
def ChartToPhys : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ Φ : ℝ → Space → ℝ≥0∞,
    Measurable (fun x : ℝ × Space => Φ x.1 x.2) →
    (∀ (α τ : ℝ) (y : Space), Φ τ (Axi.rotZ α y) = Φ τ y) →
    (∀ y : Space, Function.Periodic (fun τ => Φ τ y) (2 * c / R)) →
    ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioi 0 →
      ∫⁻ p in {p : Chart | p.1 ∈ E}, ENNReal.ofReal (p.1⁻¹) *
          Φ (NearInst.chartTau R p) (NearInst.chartY R p) ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) *
          ∫⁻ x in Ioc 0 (2 * c / R) ×ˢ {y : Space | age R y ∈ E}, Φ x.1 x.2

/-- The substitution `λ = e^{(σ-τ)/2}`, `dλ = (λ/2) dσ`, of `(0,1)` by `(-∞, τ)`. -/
def LogSubst : Prop :=
  ∀ (τ : ℝ) (f : ℝ → ℝ≥0∞), Measurable f →
    ∫⁻ l in Ioo (0 : ℝ) 1, f l =
      ∫⁻ σ in Iio τ, ENNReal.ofReal (Real.exp ((σ - τ) / 2) / 2) * f (Real.exp ((σ - τ) / 2))

/-- **Atom representation** (source 3611-3621 with `σ = τ + 2 log λ`):
`psiMaj(τ, y) ≤ ∫ phKer(τ, y; σ, z) srcW(σ, z) d(σ, z)`. -/
def PsiMajRep : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), Measurable G → ∀ (τ : ℝ) (y : Space),
    psiMaj R c θ G τ y ≤ ∫⁻ a : ℝ × Space, phKer θ τ y a.1 a.2 * srcW R c G a.1 a.2

/-- **Minkowski over the source atoms** (source 5590 "Minkowski"): for every output set `X`,
`‖psiMaj‖_{L²(X)} ≤ ∫ srcW(a) ‖phKer(·; a)‖_{L²(X)} da`. -/
def PsiAtomsMinkowski : Prop :=
  ∀ (R c θ : ℝ) (G : Chart → ℝ≥0∞), Measurable G → ∀ X : Set (ℝ × Space),
    (∫⁻ x in X, psiMaj R c θ G x.1 x.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ∫⁻ a : ℝ × Space, srcW R c G a.1 a.2 *
        (∫⁻ x in X, phKer θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- **Source ages** (source 5586-5587: "all source ages exceed `e^{δ-h}s_j`"): an off-axis atom
seen across the radial gap from an output point of age `> s₁` has age `> s₁/θ²`. -/
def AtomSupport : Prop :=
  ∀ (R θ s1 s0 : ℝ), 0 < R → 0 < θ → 0 < s1 → ∀ (τ : ℝ) (y : Space) (σ : ℝ) (z : Space),
    y ∈ ybin R s1 s0 → 0 < ϱ z → ¬ (s1 / θ ^ 2 < age R z) → phKer θ τ y σ z = 0

/-- **Spatial `L²` norm across the gap** (source 5588-5591): for `0 < λ < 1`, on outputs of age
`≤ s₀` across the radial gap, `|y - λz| ≥ (1-θ)ϱ(y) ≥ D = (1-θ)R/√s₀`, and
`∫_{|x| ≥ D} |x|^{-8} dx = 4π/(5D⁵)` (`gapKernel_sq_lintegral_le`). -/
def GapSpatialL2 : Prop :=
  ∀ (R θ s0 l : ℝ) (z : Space), 0 < R → 0 < θ → θ < 1 → 0 < s0 → 0 < l → l < 1 →
    ∫⁻ y in {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y},
        ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) ^ (2 : ℝ) ≤ ENNReal.ofReal (gapA θ R s0)

/-- **Phase factor of one atom**: `∫_{(0,P]} 1_{σ<τ} e^{σ-τ}/4 dτ ≤ omega2 P σ`. -/
def PhaseWeight : Prop :=
  ∀ (P σ : ℝ), 0 < P →
    ∫⁻ τ in Ioc 0 P, (if σ < τ then ENNReal.ofReal (Real.exp (σ - τ) / 4) else 0) ≤
      ENNReal.ofReal (omega2 P σ)

/-- **Atom bound** (source 5588-5591): the `L²((0,P] × ybin)` norm of the kernel of one atom is
`≤ √gapA √omega2(σ)`, and the weighted atom vanishes unless its age exceeds `s₁/θ²`. -/
def AtomBound : Prop :=
  ∀ (R c θ s1 s0 P : ℝ) (G : Chart → ℝ≥0∞), 0 < R → 0 < θ → θ < 1 → 0 < s1 → s1 ≤ s0 →
    0 < P → ∀ a : ℝ × Space,
      srcW R c G a.1 a.2 * (∫⁻ x in Ioc 0 P ×ˢ ybin R s1 s0,
          phKer θ x.1 x.2 a.1 a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        Set.indicator {a : ℝ × Space | s1 / θ ^ 2 < age R a.2}
            (fun a => srcW R c G a.1 a.2) a *
          ENNReal.ofReal (Real.sqrt (gapA θ R s0) * Real.sqrt (omega2 P a.1))

/-- **The fold sum** (task spec: `l = e^{-mc/R}λ`, `Σ_m e^{-mc/R} ≤ 1 + R/c`): for `σ ∈ (0, P]`,
`Σ_n √omega2(σ + nP) ≤ √P + 1/√P`. -/
def OmegaSum : Prop :=
  ∀ P : ℝ, 0 < P → ∀ σ ∈ Ioc (0 : ℝ) P,
    ∑' n : ℤ, ENNReal.ofReal (Real.sqrt (omega2 P (σ + n * P))) ≤
      ENNReal.ofReal (Real.sqrt P + 1 / Real.sqrt P)

/-- **Folding the atom phase** over the periods `(nP, (n+1)P]`. -/
def PhaseFold : Prop :=
  ∀ P : ℝ, 0 < P → ∀ H : ℝ → ℝ≥0∞, Measurable H → Function.Periodic H P →
    ∫⁻ σ, ENNReal.ofReal (Real.sqrt (omega2 P σ)) * H σ ≤
      ENNReal.ofReal (Real.sqrt P + 1 / Real.sqrt P) * ∫⁻ σ in Ioc 0 P, H σ

/-- **Source mass** (source 5571-5575 for `N₀`, 2679-2684 for the change of variables): the atom
weights of age `> a₀`, folded over periods, carry `(√P + 1/√P) · PπR² · N₀(a₀)`. -/
def SourceMass : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ g : Chart → Ten3, Measurable g → ∀ a0 : ℝ,
    ∫⁻ a : ℝ × Space, Set.indicator {a : ℝ × Space | a0 < age R a.2}
        (fun a => srcW R c (fun p => ‖g p‖ₑ) a.1 a.2) a *
        ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) a.1)) ≤
      ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
        ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) * ageMass c a0 g

/-- **The constants** (source 5590-5591: `ε^{3/2} s_j^{5/4}`, here `R = ε⁻¹`):
`(2πcR)^{-1/2} √gapA (√P + 1/√P) PπR² ≤ C₀(θ) (1 + c/R) R^{-3/2} s₀^{5/4}`, `P = 2c/R`. -/
def ConstAlgebra : Prop :=
  ∀ (θ R c s0 : ℝ), 0 < θ → θ < 1 → 0 < R → 0 < c → 0 < s0 →
    ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (Real.sqrt (gapA θ R s0)) *
        ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
        ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) ≤
      ENNReal.ofReal (wyC0 θ * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) * s0 ^ (5 / 4 : ℝ))

/-- For `S ≤ 0` the bin lies in `{s ≤ 0}`, which `ageμ` does not see. -/
def BinNull : Prop :=
  ∀ (c a S h : ℝ) (j : ℕ) (f : Chart → ℝ≥0∞), S ≤ 0 →
    ∫⁻ p in binSet S h j, f p ∂(ageμ c a) = 0

/-- The source weight is jointly measurable. -/
theorem measurable_srcW (R c : ℝ) {G : Chart → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun a : ℝ × Space => srcW R c G a.1 a.2) := by
  unfold srcW age
  have h1 : Measurable fun a : ℝ × Space => R ^ 2 / ϱ a.2 ^ 2 :=
    measurable_const.div ((measurable_ϱ.comp measurable_snd).pow_const 2)
  exact (ENNReal.measurable_ofReal.comp h1).mul (hG.comp (T8_1.measurable_chartOf R c))

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
