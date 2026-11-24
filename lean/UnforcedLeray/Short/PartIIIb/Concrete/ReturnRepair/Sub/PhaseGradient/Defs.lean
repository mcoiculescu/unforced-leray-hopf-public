import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16

/-!
# Design of `repair:phase-gradient` (`PartIII-b:C/rep/2`, source 5203-5223)

Source of record: `the November 2 reference manuscript` (73 pages):
5203-5223 (`repair:phase-gradient`), 3603-3647 (`sep:kernel`, `sep:resolvent`, `sep:young`),
3800-3845 (the free equations `B X₀ = νΔX₀ - (μ+½)X₀ + W_μ`, `sep:phase-sup`), 4161-4200 (the
Ward fields `X₀ = W_μ - W_{μ+1}`, `X = 𝒞_y X₀`, `Y = D_{μ+1}X`, the outward primitive and
`ward:shifted-resolvent` `D_{μ+1}X₀ = W_μ`), 5148-5176 (the old repair source and `F_r`).

The target `PhaseGradientAt` (`Estimates.lean` §4) bounds
`‖DX‖_{L^∞_τL^{22/3}} + ‖DY‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{46/11} F_r` for the Ward fields
`X = repX`, `Y = repY` of the old repair source `repSrcTen` (a chart representative of `χ_oT₂`).

## Route

* **Separated representative** (`RepairSepBridge`, S5).  The old repair source has a separated
  space-time representative `T` (measurable, `P`-periodic with `P = 2εc`, supported in the old
  disk `|z'| ≤ R√(5ν/6)`, finite `Y₂` moment, axisymmetric) with the same separated responses
  `sepW` and `‖T‖_{L²_τL^{22/19}} ≤ F_r` (source 4155-4171, 5148-5176; the construction of
  `oldSourceReg_of`).  Hence `wardX0 = sepX0 T`, `repX = sepWX T`, `repY = sepWY T`
  (definitional after rewriting `sepW`).
* **Separated resolvent, phase by phase** (`SepDomPhaseSup` S1a, `SepWPhaseSup` S1).  At every
  phase, `‖1_young D^jW_μ(τ)‖_{L^{22/3}} ≤ C D^{-4-j+9/11}‖T‖_{L²_τL^{22/19}}` (kernel exponent
  `b = 11/3`: `1 + 3/22 = 19/22 + 3/11`), uniformly for `P ≤ 1` ("the normalized phase estimate
  over `P ≤ 1`", 5219-5221).  `sepWPhaseSup_of` (proved here) reduces S1 to the pointwise
  domination `IIIa.SepWDominated` and the scalar estimate S1a.
* **Transfer to `X₀`** (`SepX0PhaseBound`, S2), **the outward primitive** (`OutPrimPhaseBound`,
  S3a), **the stream cutoff** (`WardGradXPhase`, S3: `‖DX(τ)‖_{L^{22/3}} ≤ P_ν(R√ν)^{-46/11}F`),
  **the free equation** (`SepX0FreeEq`, S4a: `D_{μ+1}X₀ = Re W_μ`) and **`Y`**
  (`WardGradYPhase`, S4: the same bound for `DY`).
* **Assembly** (`Assembly.lean`, S6): the physical rescaling `(R√ν)^{-46/11} ≤ ν^{-3}ε^{46/11}`
  (`R = ε⁻¹`, `ν ≤ 1`), `essSup` of the phase-wise bounds, and the eventual regime facts
  (`ν, ε ≤ 1`, `P ≤ 1`, the Floquet window) from `SeqData.RepairStanding`.

All lengths are multiples of `L = R√ν`: the old disk `R√(5ν/6)`, the receiver `R√ν`, the
transition annulus `R√ν ≤ r ≤ R√(5ν/4)` of `χ_y` (`s = R²/r²`, `χ_y = 1` for `s ≤ 0.8/ν`,
`χ_y = 0` for `s ≥ 1/ν`, 4164-4167) and the gap `D = (1 - √(5/6))L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Slice norms -/

/-- `‖f‖_{L^q_y} = (∫ f^q dy)^{1/q}` of a nonnegative density on one phase slice. -/
def lqNorm (q : ℝ) (f : Space → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ y : Space, f y ^ q) ^ (1 / q)

/-- The slice norm of a real density: the inner norm of `phaseSupLr` (`Estimates.lean` §2). -/
def sliceLq (q : ℝ) (f : Space → ℝ) : ℝ≥0∞ :=
  lqNorm q (fun y => ENNReal.ofReal |f y|)

theorem phaseSupLr_eq_essSup (P r : ℝ) (f : ℝ × Space → ℝ) :
    phaseSupLr P r f =
      essSup (fun t => sliceLq r (fun y => f (t, y))) (volume.restrict (Ioc (0 : ℝ) P)) :=
  rfl

theorem lqNorm_mono {q : ℝ} (hq : 0 < q) {f g : Space → ℝ≥0∞} (h : ∀ y, f y ≤ g y) :
    lqNorm q f ≤ lqNorm q g := by
  unfold lqNorm
  have hq' : 0 ≤ 1 / q := by positivity
  gcongr with y
  exact h y

theorem lqNorm_const_mul {q : ℝ} (hq : 0 < q) (c : ℝ≥0∞) (hc : c ≠ ∞) (f : Space → ℝ≥0∞) :
    lqNorm q (fun y => c * f y) = c * lqNorm q f := by
  unfold lqNorm
  have h1 : ∫⁻ y, (c * f y) ^ q = c ^ q * ∫⁻ y, f y ^ q := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le hc)
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  congr 1
  rw [mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- A phase-wise a.e. bound gives the `L^∞_τ` bound. -/
theorem phaseSupLr_le_of_ae {P r : ℝ} {f : ℝ × Space → ℝ} {B : ℝ≥0∞}
    (h : ∀ᵐ τ : ℝ, sliceLq r (fun y => f (τ, y)) ≤ B) : phaseSupLr P r f ≤ B :=
  essSup_le_of_ae_le B (ae_restrict_of_ae h)

/-! ## 2. The fields of a separated space-time source

For a tensor source `T(τ, z)` (in the applications the separated representative of the old
repair source), the source objects of 4171-4186 with `T` in place of `oldPhys R c g`. -/

/-- `Re W_μ` (`sep:resolvent`, 3622-3626; `W_μ = -S_μT`), real Cartesian components. -/
def sepWre (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun i => (IIIa.sepW ν (μ : ℂ) T y τ i).re

/-- `X₀ = W_μ - W_{μ+1}` (`ward:displacement`, 4171-4174): `wardX0` with the source `T`. -/
def sepX0 (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun i =>
    (IIIa.sepW ν (μ : ℂ) T y τ i - IIIa.sepW ν ((μ : ℂ) + 1) T y τ i).re

/-- `X = 𝒞_y X₀` (4171, 4181-4186) with the source `T`. -/
def sepWX (ν μ R : ℝ) (χy : ℝ → ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ → Space → Space :=
  wardStreamCut ν R χy (sepX0 ν μ T)

/-- `Y = D_{μ+1}X` (4171) with the source `T`. -/
def sepWY (ν μ R : ℝ) (χy : ℝ → ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ → Space → Space :=
  physDmu ν (μ + 1) (sepWX ν μ R χy T)

theorem wardX0_eq_sepX0 (ν μ R c : ℝ) (g : Chart → Ten3) :
    wardX0 ν μ R c g = sepX0 ν μ (oldPhys R c g) := rfl

theorem wardX_eq_sepWX (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) :
    wardX ν μ R c χy g = sepWX ν μ R χy (oldPhys R c g) := rfl

theorem wardY_eq_sepWY (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) :
    wardY ν μ R c χy g = sepWY ν μ R χy (oldPhys R c g) := rfl

/-- `X₀` only sees the responses `sepW` of its source. -/
theorem sepX0_congr {ν μ : ℝ} {T T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ (μ' : ℂ) (y : Space) (τ : ℝ), IIIa.sepW ν μ' T y τ = IIIa.sepW ν μ' T' y τ) :
    sepX0 ν μ T = sepX0 ν μ T' := by
  funext τ y
  simp only [sepX0, h]

theorem sepX0_eq_sub (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    sepX0 ν μ T τ y = sepWre ν μ T τ y - sepWre ν (μ + 1) T τ y := by
  have h : ((μ + 1 : ℝ) : ℂ) = (μ : ℂ) + 1 := by push_cast; ring
  simp only [sepX0, sepWre, h]
  rfl

/-- An axisymmetric swirl-free tensor source (source 2666-2683, 4171-4178): equivariant under the
rotations about the vertical axis and the reflection `φ ↦ -φ` (`actM`, `rotM`, `reflM` of
`Sub/IIIb-D2_3_1_2_3.lean`; the lift `oldPhys` has both, `oldPhysRotEquiv`, `oldPhysReflEquiv`). -/
def IsAxiSource (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ co si : ℝ, co ^ 2 + si ^ 2 = 1 → ∀ (τ : ℝ) (z : Space),
      T τ (actM (rotM co si) z) = rotM co si * T τ z * (rotM co si).transpose) ∧
    ∀ (τ : ℝ) (z : Space), T τ (actM reflM z) = reflM * T τ z * reflM.transpose

/-- The transition annulus `R√ν ≤ r ≤ R√(5ν/4)` of the stream cutoff, `r = |y'|`
(`χ_y(ν R²/r²)`: `χ̂_y = 1` on `[0, 4/5]`, `= 0` on `[1, ∞)`, 4164-4167). -/
def streamAnn (ν R : ℝ) : Set Space :=
  {y | R * Real.sqrt ν ≤ ϱ y ∧ ϱ y ≤ R * Real.sqrt (5 * ν / 4)}

/-! ## 3. The steps

`F = ‖T‖_{L²_τL^{22/19}}` is `IIIa.ltauLq P (22/19) (IIIa.srcNorm T)`; `q = 22/3`. -/

/-- **(S1a) The scalar dilation integral, phase by phase** (source 3624-3647 with 5219-5221):
for `1 ≤ p, b, q`, `1 + 1/q = 1/p + 1/b`, `δ ≤ a - 2 + 3/p`, `a ≥ 0`, `0 < P ≤ 1` and a
`P`-periodic jointly measurable `g`, at **every** phase `τ`,
`‖sepDom a j D g (τ,·)‖_{L^q_y} ≤ C D^{-4-j+3/b} ‖g‖_{L²_τL^p_y}`, `C = C(j,p,q,b,δ)`.
Proof: Young in `y` with `‖1_{|x|≥D}|x|^{-4-j}‖_{L^b} = C D^{-4-j+3/b}` and the dilation
`λ^{-3+3/p}`, Minkowski in `λ`: the bound `C D^{..} ∫_0^1 λ^{a-3+3/p}‖g(τ+2log λ)‖_p dλ`; with
`λ = e^{-h/2}` this is `(C D^{..}/2)∫_0^∞ e^{-κh}‖g(τ-h)‖_p dh`, `κ = (a-2+3/p)/2 ≥ δ/2`; split
`h` into periods, use periodicity and Cauchy-Schwarz on each:
`≤ (C D^{..}/2) (1 - e^{-κP})⁻¹ P ‖g‖_{L²_τL^p}` and `P/(1-e^{-κP}) ≤ 1/κ + P ≤ 2/δ + 1` for
`P ≤ 1`. -/
def SepDomPhaseSup : Prop :=
  ∀ (j : ℕ) (p q b δ : ℝ), 1 ≤ p → 1 ≤ b → 1 ≤ q → 1 + 1 / q = 1 / p + 1 / b → 0 < δ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → δ ≤ a - 2 + 3 / p → ∀ D P : ℝ, 0 < D → 0 < P → P ≤ 1 →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
        ∀ τ : ℝ, lqNorm q (IIIa.sepDom a j D g τ) ≤
          ENNReal.ofReal (C * D ^ (-4 - (j : ℝ) + 3 / b)) * IIIa.ltauLq P p g

/-- **(S1) The separated resolvent in phase supremum** (source 3622-3647, 5212-5221): `K` compact in
`Re μ > -1/4`, `0 ≤ r_o < r_i`, `D = r_i - r_o`, `0 < P ≤ 1`, `T` a separated source; at every
phase, `‖1_{|y'|≥r_i} D^jW_μ(τ)‖_{L^{22/3}_y} ≤ C D^{-4-j+9/11}‖T‖_{L²_τL^{22/19}}` (kernel
exponent `b = 11/3`; `j = 1` is the `D^{-46/11}` of 5212-5217). -/
def SepWPhaseSup : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) →
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K, ∀ rOut rIn P : ℝ, 0 ≤ rOut →
      rOut < rIn → 0 < P → P ≤ 1 → ∀ T, IIIa.IsSepSource P rOut T → ∀ τ : ℝ,
        lqNorm (22 / 3) (IIIa.youngDerivNorm ν μ T j rIn τ) ≤
          ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)

/-- **(S2) Transfer to `X₀ = W_μ - W_{μ+1}`** (source 4171-4174, 4192-4194): real `μ` in a window
`[σ₁, σ₂]`, `σ₁ > -1/4`, `j ≤ 2`, `0 < P ≤ 1`, a separated source with finite `Y₂` moment; at
every phase, `‖1_{|y'|≥r_i} D^jX₀(τ)‖_{L^{22/3}} ≤ C D^{-4-j+9/11}‖T‖_{L²_τL^{22/19}}`.
(`W_μ`, `W_{μ+1}` are `C²` on `|y'| > r_o`, `SepWSmoothOn` / `sepWSmoothOn_of`; `D^j Re = Re D^j`;
Minkowski; S1 with `K = {μ, μ+1 : μ ∈ [σ₁, σ₂]}`.) -/
def SepX0PhaseBound : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ j : ℕ, j ≤ 2 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ rOut rIn P : ℝ), 0 < ν → μ ∈ Icc σ₁ σ₂ → 0 ≤ rOut → rOut < rIn → 0 < P → P ≤ 1 →
      ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T → ∀ τ : ℝ,
        lqNorm (22 / 3)
            (fun y => if rIn ≤ ϱ y then ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ else 0) ≤
          ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)

/-- **(S3a) The outward primitive on the transition annulus** (source 4181-4192: "the
separated-kernel estimates prove convergence of this primitive and its differentiated versions
for the ... repair `L²_τL^{22/19}` sources"): for `Z = Re W_μ` and `Z = X₀`, at every phase,
`‖Ψ_Z(τ, |y'|, y₃)‖_{L^{22/3}(R√ν ≤ |y'| ≤ R√(5ν/4))} ≤ C (R√ν)^{-13/11} F`
(`Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,0,z) dρ`, `outPrim`).  Proof sketch: `|Z| ≤ C sepDom` (j = 0) at the
half-plane points `(ρ,0,z)`, `ρ ≥ r ≥ R√ν`; `ρ ≤ κ(ρ - r_o)` with `κ = 1/(1-√(5/6))` gives
`∫_r^∞ ρ|(ρ,0,z) - λz'|^{-4} dρ ≤ κ/(2(D² + (z - λz'_3)²))`; Hölder over the old disk, Young in the
vertical variable with `‖(D²+t²)^{-1}‖_{L^{11/3}(ℝ)} = C D^{-2+3/11}`, Minkowski in `λ` and the
phase summation of S1a; all lengths are multiples of `R√ν`. -/
def OutPrimPhaseBound : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → 0 < R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → ∀ τ : ℝ,
        lqNorm (22 / 3) (fun y => (streamAnn ν R).indicator
            (fun y => ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)|) y) ≤
          ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ))) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) ∧
        lqNorm (22 / 3) (fun y => (streamAnn ν R).indicator
            (fun y => ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|) y) ≤
          ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ))) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)

/-- **(S3) The stream cutoff preserves the gradient bound** (source 4181-4192, 5212-5217):
`‖D(𝒞_y X₀)(τ)‖_{L^{22/3}} ≤ P_ν (R√ν)^{-46/11} F` for a.e. phase.  Off the axis, `X = 0` for
`|y'| < R√ν`; for `|y'| ≥ R√ν`,
`DX = χ_y DX₀ + X₀ ⊗ ∇χ_y + D((χ_y'/r)Ψ e_z)` with `|∇χ_y| ≤ C/(R√ν)`, `|χ_y'/r| ≤ C(R√ν)^{-2}`,
`|∂_r(χ_y'/r)| ≤ C(R√ν)^{-3}` on the annulus, `∂_rΨ = rX₀_z`, `∂_zΨ = -rX₀_r` (`outPrimDerivR`,
`outPrimDerivZ`; `X₀` is `C²`, solenoidal, axisymmetric: `SepWSmoothOn`, `SepWDivFree`,
`SepWEquivariance`); the terms are bounded by S2 (`j = 0, 1`, `r_i = R√ν`,
`D = (1-√(5/6))R√ν`) and S3a. -/
def WardGradXPhase : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ᵐ τ : ℝ, sliceLq (22 / 3) (fun y => ‖fderiv ℝ (sepWX ν μ R χy T τ) y‖) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * (R * Real.sqrt ν) ^ (-(46 / 11 : ℝ))) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)

/-- **(S4a) The free equation of `X₀`** (`ward:shifted-resolvent`, source 4199-4200; 3800-3807
`BX₀ = νΔX₀ - (μ+½)X₀ + W_μ`): `D_{μ+1}X₀ = W_μ` at every phase and every point off the old disk.
With `λ = e^{-h/2}`, `X₀ = -∫_0^∞ (G_μ - G_{μ+1})(h) * T(τ-h) dh`,
`G_μ(h) = e^{-(μ+3/2)h}∇K_{ν(1-e^{-h})}(y - e^{-h/2}z)`; `(G_μ - G_{μ+1})(0) = 0`, so no
instantaneous term and no phase derivative of `T` occurs (5223); the heat equation
`∂_tK = ΔK` and the homogeneity `x·∇∇K_t + 2t∂_t∇K_t = -4∇K_t` (`sep:kernel`, 3603-3610) give
`(∂_h - ½y·∇ - νΔ + μ - ½)G_μ = 0`. -/
def SepX0FreeEq : Prop :=
  ∀ (ν μ rOut P : ℝ), 0 < ν → -(1 / 4) < μ → 0 ≤ rOut → 0 < P →
    ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
        physDmu ν (μ + 1) (sepX0 ν μ T) τ y = sepWre ν μ T τ y

/-- **(S4) `Y = D_{μ+1}X` has the same bound** (source 4171, 4192-4200, 5212-5223):
`‖DY(τ)‖_{L^{22/3}} ≤ P_ν (R√ν)^{-46/11} F` for a.e. phase.  By S4a,
`Y = 𝒞_y W_μ + [D_{μ+1}, 𝒞_y]X₀` (`𝒞_y` is phase independent; `[y·∇, χ_y] = y·∇χ_y`,
`ν[Δ, χ_y] = ν(2∇χ_y·∇ + Δχ_y)`, `(y·∇)Ψ_Z = Ψ_{y·∇Z} + 2Ψ_Z`, `ΔΨ_Z = Ψ_{ΔZ} + 2Z_z`); every term
is bounded by S1 (`W_μ`, `j ≤ 1`), S2 (`j ≤ 2`) and S3a, with `ν/(R√ν)² = R⁻² ≤ 1`. -/
def WardGradYPhase : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ᵐ τ : ℝ, sliceLq (22 / 3) (fun y => ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * (R * Real.sqrt ν) ^ (-(46 / 11 : ℝ))) *
            IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)

/-- **(S5) The separated representative of the old repair source** (source 4155-4171, 5148-5176,
2684-2703): for `c, ρ_b > 0`, `m_Z ≥ 0`, `ν, ε > 0` and every stress `M`, the chart representative
`g` of the repair component of `χ_oM` has a separated source `T` with period `P = 2εc`, old disk
`|z'| ≤ ε⁻¹√(5ν/6)`, finite `Y₂` moment, axisymmetric, with the same separated responses as
`oldPhys ε⁻¹ c g` and `‖T‖_{L²_τL^{22/19}} ≤ F_r = ‖strPhys ε⁻¹ c g‖_{L²_τL^{22/19}}`.
(The construction of `oldSourceReg_of`, `Sub/IIIb-D2_3_1_1_1.lean`: `T = oldCutSrc` of the
representative `cutFun χ_o ν • M.snd`, a.e. equal to `oldPhys ε⁻¹ c g` in `(τ, z)`, so the
`L²_τL^{22/19}` norms agree; `oldPhysRotEquiv`, `oldPhysReflEquiv` and the radial cut give
`IsAxiSource`.) -/
def RepairSepBridge : Prop :=
  ∀ (c mZ ρb γ ν ε : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo), 0 < c → 0 < ρb → 0 ≤ mZ →
    0 < ν → 0 < ε → ∀ M : StrG c mZ ρb γ ν,
      ∃ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
        IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6)) T ∧
        SepMoment (2 * ε * c) T ∧ IsAxiSource T ∧
        (∀ (μ : ℂ) (y : Space) (τ : ℝ),
          IIIa.sepW ν μ (oldPhys ε⁻¹ c ((chiOStr c mZ ρb γ ν hχo M).snd : Chart → Ten3)) y τ =
            IIIa.sepW ν μ T y τ) ∧
        IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T) ≤
          phaseL2Lr (2 * ε * c) (22 / 19)
            (strPhys ε⁻¹ c ((chiOStr c mZ ρb γ ν hχo M).snd : Chart → Ten3))

/-! ## 4. S1 from the pointwise domination and S1a -/

/-- `SepWPhaseSup` from `IIIa.SepWDominated` (`PartIII-a:T16/1`), `IIIa.SepKernelBounds` and S1a
(`p = 22/19`, `q = 22/3`, `b = 11/3`, `δ = 2 ≤ 2Re μ + 57/22`). -/
theorem sepWPhaseSup_of (hA : IIIa.SepWDominated) (hK : IIIa.SepKernelBounds)
    (hB : SepDomPhaseSup) : SepWPhaseSup := by
  intro K _ hKre j
  obtain ⟨C0, hC0, hA'⟩ := IIIa.sepWDominated_slice_ae hA hK j
  obtain ⟨Cb, hCb, hB'⟩ := hB j (22 / 19) (22 / 3) (11 / 3) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cz, hCz, hBz⟩ := hB 0 (22 / 19) (22 / 3) (11 / 3) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C0 * Cb + 1, by positivity, ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP hP1 T hT τ
  have hμre := hKre μ hμ
  have hD : 0 < rIn - rOut := by linarith
  have ha : 0 ≤ 2 * μ.re + 2 := by linarith
  have hδ' : (2 : ℝ) ≤ (2 * μ.re + 2) - 2 + 3 / (22 / 19) := by norm_num; linarith
  have hgm := IIIa.sepAE_measurable_srcNorm hT
  have hper : ∀ τ z, IIIa.srcNorm T (τ + P) z = IIIa.srcNorm T τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hT.periodic]
  have hq0 : (0 : ℝ) < 22 / 3 := by norm_num
  have hb : (3 : ℝ) / (11 / 3) = 9 / 11 := by norm_num
  have hpos : 0 < (C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hD _)
  by_cases htop : IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  have h0 : lqNorm (22 / 3) (IIIa.sepDom (2 * μ.re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ) < ⊤ :=
    (hBz _ ha hδ' _ P hD hP hP1 _ hgm hper τ).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 htop))
  have hI : (∫⁻ y, IIIa.sepDom (2 * μ.re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y ^
      (22 / 3 : ℝ)) ≠ ⊤ := by
    unfold lqNorm at h0
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h0).ne
  have hae := hA' ν hν μ hμre rOut rIn P hrO hrr hP T hT τ (22 / 3) hq0 hI
  calc lqNorm (22 / 3) (IIIa.youngDerivNorm ν μ T j rIn τ)
      ≤ lqNorm (22 / 3) (fun y => ENNReal.ofReal C0 *
          IIIa.sepDom (2 * μ.re + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y) := by
        unfold lqNorm
        refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by positivity)
        filter_upwards [hae] with y hy
        exact ENNReal.rpow_le_rpow hy hq0.le
    _ = ENNReal.ofReal C0 *
          lqNorm (22 / 3) (IIIa.sepDom (2 * μ.re + 2) j (rIn - rOut) (IIIa.srcNorm T) τ) :=
        lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / (11 / 3))) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) := by
        gcongr
        exact hB' _ ha hδ' _ P hD hP hP1 _ hgm hper τ
    _ = ENNReal.ofReal (C0 * Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
        rw [hb, ← mul_assoc, ← ENNReal.ofReal_mul hC0, mul_assoc]
    _ ≤ ENNReal.ofReal ((C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
        gcongr
        linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
