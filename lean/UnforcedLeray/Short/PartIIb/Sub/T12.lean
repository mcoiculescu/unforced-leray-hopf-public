import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b, task `PartII-b:T12`: existence and `H_r` bound of the flat response (conditional)

Source of record: `the November 2 reference manuscript`, lines 1920-1930:
"The causal formula `T_0F(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} P_0 F(t) dt/t` and weighted dilation give
`‖T_0‖_{H_r → H_r} ≤ C_r/a_r`", `a_r = Re μ + (3/r - 1)/2` (the shift gap `γ_r` of
`ProfileGraphFlat`, SP 1927).

## Target of the task (statement-first)

`FlatCausalExists`: for `1 < r < 3` there is `C = C_r` such that for every `μ` with `a_r > 0`, every
`ν, c > 0` and every `F ∈ H_r` there is a flat response `b ∈ H_r` (`IsFlatResponse ν μ F b`) with
`‖b‖_{H_r} ≤ (C/a_r) ‖F‖_{H_r}`. This is the "existence + `H_r` bound" input of `PartII-b:T14`
(`ProfileGraphFlat`); the graph bounds are `T13`, uniqueness is `T11`.

## Why a density extension is not needed


Duhamel operator to be linear on a dense class and `IsFlatResponse` to be closed under `H_r`-limits.
Both are avoided by working directly in `H_r`: split `T_0 = D ∘ P_0` where

* `P_0` is the planar Leray (Helmholtz) projection acting in `(q, η)` at each age, bounded on `H_r`
  with a constant `C_r` depending only on `r` (it is a Calderón-Zygmund operator; this is the
  repository's INF01 / Grafakos Cor. 5.2.8 input, here for `ℂ²`-valued fields on the cylinder);
* `D G(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} G(t) dt/t` (`flatDuhamel`) is the causal heat Duhamel operator
  on weakly solenoidal `G ∈ H_r`: heat contraction in `L^r(dq/c dη)`, Minkowski, and the dilation
  identity `‖φ(u ·)‖_{L^r(s^{r/2-5/2}ds)} = u^{γ_r}‖φ‖` give `‖D G‖_{H_r} ≤ (1/a_r)‖G‖_{H_r}`.

## Proved here

`flatCausalExists_of` : the conditional assembly `FlatCausalExists` from the seven leaves

* `CylinderHelmholtzLr` (`PartII-b:T12/1`): the cylinder Helmholtz decomposition in `L^r`;
* `FlatLerayLiftOfSlice` (`PartII-b:T12/2`): lift from slices to `H_r` (`FlatLerayHr`);
* `DuhamelMeasurable` (`PartII-b:T12/3`), `DuhamelBound` (`PartII-b:T12/4`),
  `DuhamelPeriodic` (`PartII-b:T12/5`), `DuhamelSolenoidal` (`PartII-b:T12/6`),
  `DuhamelEquation` (`PartII-b:T12/7`): properties of `flatDuhamel`.

The helper leaf `FlatHeatContraction` (`PartII-b:T12/8`) feeds `T12/4`.

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## The causal Duhamel operator -/

/-- The planar heat kernel `(4πθ)⁻¹ exp(-|w|²/(4θ))` of `e^{θΔ_{q,η}}`, `θ > 0`. -/
def flatHeatKernel (θ : ℝ) (w : ℝ × ℝ) : ℝ :=
  (4 * Real.pi * θ)⁻¹ * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * θ))

/-- `e^{θΔ_{q,η}} f` for a `ℂ²`-valued field `f` on the plane `(q, η)` (convolution with
`flatHeatKernel θ`; the junk value `0` where the integral does not converge). -/
def flatHeat (θ : ℝ) (f : ℝ × ℝ → CMerid) (z : ℝ × ℝ) : CMerid :=
  ∫ w : ℝ × ℝ, flatHeatKernel θ w • f (z - w)

/-- The causal Duhamel operator of SP 1924, applied to an already solenoidal `G` (so that `P_0 G = G`):
`D G(s, z) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} G(t, ·)(z) dt/t`. For `s ≤ 0` the integral is over the empty
set and the value is `0`. -/
def flatDuhamel (ν : ℝ) (μ : ℂ) (G : CProf) : CProf := fun x =>
  ∫ t in Ioo 0 x.1, (((t / x.1 : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) •
    flatHeat (ν * (x.1 - t)) (fun z => G (t, z)) x.2

/-! ## Weak solenoidality and orthogonality to planar solenoidal tests -/

/-- `b` is weakly solenoidal in `(q, η)`: `∫ (b_0 ∂_qφ + b_1 ∂_ηφ) = 0` for tests `φ` of `s > 0`
(this is the clause `IsFlatResponse.solenoidal`). -/
def WeakSolenoidal (b : CProf) : Prop :=
  ∀ φ, IsCoordTest φ →
    Integrable (fun x => b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) = 0

/-- `D` is orthogonal to every planar solenoidal test (`D` is a gradient in `(q, η)`), with
integrable pairing. -/
def PerpPlanarSol (D : CProf) : Prop :=
  ∀ Ψ, IsPlanarSolTest Ψ → Integrable (cdot D Ψ) ∧ ∫ x, cdot D Ψ x = 0

/-! ## The target and the Leray leaves -/

/-- **Target of `PartII-b:T12`** (SP 1920-1930): existence of the flat response `T_0F ∈ H_r` with
the bound `‖T_0F‖_{H_r} ≤ (C_r/a_r)‖F‖_{H_r}`, `a_r = Re μ + (3/r-1)/2`. -/
def FlatCausalExists : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∃ C : ℝ, 0 < C ∧ ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 →
    ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F : CProf, InHr c r F →
      ∃ b : CProf, InHr c r b ∧ IsFlatResponse ν μ F b ∧
        hNorm c r b ≤ ENNReal.ofReal (C / (μ.re + (3 / r - 1) / 2)) * hNorm c r F

/-- A scalar test on the cylinder `ℝ/cℤ × ℝ`, lifted to the plane `(q, η)`: smooth, `c`-periodic in
`q`, vanishing for `|η|` large. -/
structure CylTest (c : ℝ) (φ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ z : ℝ × ℝ, φ (z.1 + c, z.2) = φ z
  bounded : ∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → φ z = 0

/-- A divergence-free vector test field on the cylinder (`∂_qΨ_0 + ∂_ηΨ_1 = 0`). -/
structure CylSolTest (c : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ) : Prop where
  comp : ∀ i : Fin 2, CylTest c (fun z => Ψ z i)
  div_free : ∀ z : ℝ × ℝ,
    fderiv ℝ (fun y => Ψ y 0) z (1, 0) + fderiv ℝ (fun y => Ψ y 1) z (0, 1) = 0

/-- `F` is a `c`-periodic field on the plane `(q, η)` lying in `L^r(dq/c dη)` of one cell. -/
def CylLp (c r : ℝ) (F : ℝ × ℝ → CMerid) : Prop :=
  (∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z) ∧
    MemLp F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- `G = P_0 F` is a Helmholtz decomposition of `F` on the cylinder: `G` is `c`-periodic, in
`L^r(dq/c dη)` of a cell, weakly divergence free (`∫ G·∇φ = 0` for cylinder tests `φ`), and `F - G`
annihilates every divergence-free cylinder test field (it is a gradient). -/
def IsCylHelmholtz (c r : ℝ) (F G : ℝ × ℝ → CMerid) : Prop :=
  CylLp c r G ∧
    (∀ φ : ℝ × ℝ → ℝ, CylTest c φ →
      Integrable (fun z => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
          (UnforcedLeray.Cyl.avgμ c) ∧
        ∫ z, (G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
          ∂(UnforcedLeray.Cyl.avgμ c) = 0) ∧
    (∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) (UnforcedLeray.Cyl.avgμ c) ∧
        ∫ z, ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) = 0)

/-- **Leaf `PartII-b:T12/1`** (SP 1923-1926, `P_0`; INF01, Grafakos *Classical Fourier Analysis*
Cor. 5.2.8): the planar Leray (Helmholtz) projection `P_0` on the cylinder `T_c × ℝ` is a
linear operator on `c`-periodic `ℂ²`-valued fields in `L^r(dq/c dη)`, `1 < r < ∞`: `P_0 F` is a
Helmholtz decomposition of `F` (`IsCylHelmholtz`), `‖P_0 F‖_{L^r} ≤ C_r ‖F‖_{L^r}` with `C_r`
independent of `c` (scaling `x ↦ x/c`; "no period loss", SP 1930), and `P_0` is `ℂ`-linear
(almost everywhere; the decomposition is unique, so this only picks a linear representative). -/
def CylinderHelmholtzLr : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
    ∃ P : (ℝ × ℝ → CMerid) → (ℝ × ℝ → CMerid),
      (∀ F : ℝ × ℝ → CMerid, CylLp c r F →
        IsCylHelmholtz c r F (P F) ∧
          eLpNorm (P F) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
            ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) ∧
      (∀ (F₁ F₂ : ℝ × ℝ → CMerid) (a : ℂ), CylLp c r F₁ → CylLp c r F₂ →
        P (F₁ + a • F₂) =ᵐ[UnforcedLeray.Cyl.avgμ c] P F₁ + a • P F₂)

/-- The Leray decomposition at the level of `H_r` (the ages are carried along as a parameter):
for `F ∈ H_r` there is `G = P_0 F ∈ H_r`, weakly solenoidal in `(q, η)`, with `F - G` orthogonal to
every planar solenoidal test of `s > 0`, and `‖G‖_{H_r} ≤ C_r ‖F‖_{H_r}`, `C_r` independent of `c`. -/
def FlatLerayHr : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ F : CProf, InHr c r F →
    ∃ G : CProf, InHr c r G ∧ hNorm c r G ≤ ENNReal.ofReal C * hNorm c r F ∧
      WeakSolenoidal G ∧ PerpPlanarSol (F - G)

/-- **Leaf `PartII-b:T12/2`** (SP 1923-1926): the slice-wise Helmholtz decomposition
(`CylinderHelmholtzLr`) lifts to `H_r = L^r(s^{r/2-5/2}ds; L^r(dq/c dη))`. The difficulty is a
jointly measurable choice of `G(s, ·)` (the decomposition is unique, so the slice operator `P_0` is a
bounded linear operator on `L^r(dq/c dη)`; amplify it to the product measure), and unfolding the
non-periodic compactly supported planar tests into periodic cylinder tests. -/
def FlatLerayLiftOfSlice : Prop := CylinderHelmholtzLr → FlatLerayHr

/-! ## The Duhamel leaves -/

/-- **Leaf `PartII-b:T12/3`** (SP 1924): for `G ∈ H_r` the Duhamel integral is (a.e.) strongly
measurable in `(s, q, η)`. -/
def DuhamelMeasurable : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → AEStronglyMeasurable (flatDuhamel ν μ G) (hMeas c r)

/-- **Helper leaf `PartII-b:T12/8`** (SP 1923-1927, "heat estimate"; used by `T12/4`): the cylinder
heat semigroup is a contraction on `L^r(dq/c dη)`, `r ≥ 1`, for `c`-periodic (a.e.) `g`: the kernel
`flatHeatKernel θ` has mass one and the cell norm is invariant under translations
(Minkowski's integral inequality). Not a hypothesis of `flatCausalExists_of`. -/
def FlatHeatContraction : Prop :=
  ∀ (r c θ : ℝ) (g : ℝ × ℝ → CMerid), 1 ≤ r → 0 < c → 0 < θ →
    (∀ᵐ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) → AEStronglyMeasurable g volume →
    eLpNorm (flatHeat θ g) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
      eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `PartII-b:T12/4`** (SP 1923-1927, "weighted dilation give `‖T_0‖ ≤ C_r/a_r`"): the
Duhamel operator is bounded on `H_r` with norm `≤ 1/a_r`: heat contraction on `L^r(dq/c dη)`,
Minkowski in `t`, and the dilation `‖φ(u ·)‖_{L^r(s^{r/2-5/2}ds)} = u^{(3/r-1)/2}‖φ‖`. -/
def DuhamelBound : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G →
      hNorm c r (flatDuhamel ν μ G) ≤
        ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * hNorm c r G

/-- **Leaf `PartII-b:T12/5`**: the Duhamel integral of a `c`-periodic profile is `c`-periodic in `q`
(the heat kernel is translation invariant). -/
def DuhamelPeriodic : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (c : ℝ) (G : CProf), 0 < c → QPeriodic c G → QPeriodic c (flatDuhamel ν μ G)

/-- **Leaf `PartII-b:T12/6`**: the heat flow preserves weak solenoidality (`e^{θΔ}` commutes with
the divergence), so `D G` is weakly solenoidal when `G ∈ H_r` is. -/
def DuhamelSolenoidal : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → WeakSolenoidal G → InHr c r (flatDuhamel ν μ G) →
      WeakSolenoidal (flatDuhamel ν μ G)

/-- **Leaf `PartII-b:T12/7`** (SP 1924): the Duhamel integral solves `(μ + S - νsΔ_{q,η}) b = G`
weakly: for every planar solenoidal test `Ψ` the pairings converge and
`∫ b·((μ-1)Ψ - SΨ - νsΔΨ) = ∫ G·Ψ` (`flatTranspose`; `S^T = -1 - s∂_s`). -/
def DuhamelEquation : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → InHr c r (flatDuhamel ν μ G) → ∀ Ψ, IsPlanarSolTest Ψ →
      Integrable (fun x => ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i) ∧
        Integrable (cdot G Ψ) ∧
        ∫ x, ∑ i : Fin 2, flatDuhamel ν μ G x i * flatTranspose ν μ Ψ x i = ∫ x, cdot G Ψ x

/-! ## Conditional assembly -/

/-- `cdot` is additive in the profile slot. -/
theorem cdot_eq_add_sub (F G : CProf) (Ψ : Coord → Fin 2 → ℝ) :
    cdot F Ψ = fun x => cdot G Ψ x + cdot (F - G) Ψ x := by
  funext x
  simp only [cdot, Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- **Conditional existence and bound of the flat response** (target of `PartII-b:T12`). -/
theorem flatCausalExists_of (hL : CylinderHelmholtzLr) (hLift : FlatLerayLiftOfSlice)
    (hM : DuhamelMeasurable) (hB : DuhamelBound) (hP : DuhamelPeriodic)
    (hS : DuhamelSolenoidal) (hE : DuhamelEquation) : FlatCausalExists := by
  intro r hr1 hr3
  obtain ⟨C, hC, hCL⟩ := hLift hL r hr1 hr3
  refine ⟨C, hC, fun μ ha ν c hν hc F hF => ?_⟩
  obtain ⟨G, hG, hGn, hGs, hGp⟩ := hCL c hc F hF
  have hbm := hM r hr1 hr3 μ ha ν c hν hc G hG
  have hbn := hB r hr1 hr3 μ ha ν c hν hc G hG
  have hbper := hP ν μ c G hc hG.periodic
  have hbH : InHr c r (flatDuhamel ν μ G) :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.finite)⟩
  have hbs := hS r hr1 hr3 μ ha ν c hν hc G hG hGs hbH
  refine ⟨flatDuhamel ν μ G, hbH, ⟨hbs, ?_⟩, ?_⟩
  · intro Ψ hΨ
    obtain ⟨hi1, hi2, he⟩ := hE r hr1 hr3 μ ha ν c hν hc G hG hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]
      exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]
      exact he
  · have ha' : 0 ≤ 1 / (μ.re + (3 / r - 1) / 2) := (one_div_pos.mpr ha).le
    calc hNorm c r (flatDuhamel ν μ G)
        ≤ ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * hNorm c r G := hbn
      _ ≤ ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * (ENNReal.ofReal C * hNorm c r F) := by
          gcongr
      _ = ENNReal.ofReal (C / (μ.re + (3 / r - 1) / 2)) * hNorm c r F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul ha']
          congr 2
          ring

end UnforcedLeray.Short.IIb
