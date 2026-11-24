import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg

/-!
# `PartIII-b:C/rep/5/2/2/11` : decomposition of `TransCommPoint`

Source `the November 2 reference manuscript`
4176-4214 (outward primitive `Ψ_Z`, `Ψ_{AZ} = AΨ_Z + Ψ_Z`, `Ψ_{ΔZ} = (∂_r² - r⁻¹∂_r + ∂_z²)Ψ_Z`,
`∂_rΨ_Z = rZ_z`; `ward:cutoff-source`), 3700-3712 (`𝒬 = [B, 𝒞_χ] - ν[Δ, 𝒞_χ]`: derivatives of
`χ` cost `D⁻¹`, `Bχ` bounded, each extra Laplacian costs `νD⁻²`).

With `Z = X₀ = sepX0`, `ψ_Z(τ,y) = Ψ_Z(τ,|y'|,y₃)`, `𝒞_yZ = c(ϱ)Z + F(ϱ)ψ_Z e_z`
(`c = χ̂_y(νR²/r²)`, `F = χ̂_y'(νR²/r²)·(-2νR²/r³)/r`), `D = D_{μ+1}`:
`D𝒞_yZ - 𝒞_yDZ = -½[y·∇, 𝒞_y]Z - ν[Δ, 𝒞_y]Z`, since `∂_τ` commutes with `𝒞_y` (`TCTime`),
`[y·∇, 𝒞_y]Z = (y·∇c)Z + ((y·∇F)ψ + 2Fψ)e_z` (`TCGrad`),
`[Δ, 𝒞_y]Z = (Δc)Z + 2(∇c·∇)Z + ((ΔF)ψ + 2F'ϱ Z_z + 2F Z_z)e_z` (`TCLap`, `TCRad`).

Leaves (true source facts, as `Prop`s):
* `TCReg`, `TCInt`, `TCTime`, `TCGrad`, `TCLap`, `TCRad`: regularity and the four identities of the
  outward primitive for `Z = sepX0` (analysis of `X₀`; 4176-4214, 3603-3647);
* `TCLeibniz`: the algebraic expansion, for an abstract field `Z` satisfying them (pure calculus);
* `TCCoeff`: the one-variable bounds on the cutoff coefficients (3684-3712).

`transCommPoint_of` proves `TransCommPoint` from the leaves.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The primitive as a vertical field `ψ_Z(τ,y) e_z`, `ψ_Z(τ,y) = Ψ_Z(τ,|y'|,y₃)`. -/
def psiFld (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  outPrim Z τ (ϱ y) (y 2) • coordinateVector 2

/-- The horizontal radial unit vector `(y₁,y₂,0)/ϱ`. -/
def radialUnit (y : Space) : Space := (ϱ y)⁻¹ • (!₂[y 0, y 1, 0] : Space)

/-- Cutoff profile `c(r) = χ̂_y(νR²/r²)`. -/
def tcC0 (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ := χy (ν * (R ^ 2 / r ^ 2))

/-- Stream coefficient `F(r) = χ̂_y'(νR²/r²)(-2νR²/r³)/r`. -/
def tcF0 (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv χy (ν * (R ^ 2 / r ^ 2)) * (-2 * ν * R ^ 2 / r ^ 3) / r

/-- Coefficient of `Z`: `-½ r c' - ν(c'' + c'/r)`. -/
def tcA1 (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(1 / 2) * r * deriv (tcC0 ν R χy) r -
    ν * (deriv (deriv (tcC0 ν R χy)) r + deriv (tcC0 ν R χy) r / r)

/-- Coefficient of `∂_ϱ Z`: `-2ν c'`. -/
def tcA2 (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ := -2 * ν * deriv (tcC0 ν R χy) r

/-- Coefficient of `ψ e_z`: `-½(rF' + 2F) - ν(F'' + F'/r)`. -/
def tcB1 (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(1 / 2) * (r * deriv (tcF0 ν R χy) r + 2 * tcF0 ν R χy r) -
    ν * (deriv (deriv (tcF0 ν R χy)) r + deriv (tcF0 ν R χy) r / r)

/-- Coefficient of `Z_z e_z`: `-2ν(rF' + F)`. -/
def tcB2 (ν R : ℝ) (χy : ℝ → ℝ) (r : ℝ) : ℝ :=
  -2 * ν * (r * deriv (tcF0 ν R χy) r + tcF0 ν R χy r)

/-- The explicit commutator `[D_{μ+1}, 𝒞_y]Z` at `(τ,y)`. -/
def tcComm (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcA1 ν R χy (ϱ y) • Z τ y + tcA2 ν R χy (ϱ y) • fderiv ℝ (Z τ) y (radialUnit y) +
    (tcB1 ν R χy (ϱ y) * outPrim Z τ (ϱ y) (y 2) + tcB2 ν R χy (ϱ y) * Z τ y 2) •
      coordinateVector 2

/-- The standing context of `TransCommPoint`, at a point `y` of the transition annulus. -/
def TCCtx (σ₁ σ₂ ν μ R P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) : Prop :=
  -(1 / 4) < σ₁ ∧ 0 < ν ∧ ν ≤ 1 ∧ 1 ≤ R ∧ 0 < P ∧ μ ∈ Icc σ₁ σ₂ ∧
    IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T ∧ SepMoment P T ∧ IsAxiSource T ∧
    y ∈ streamAnn ν R

/-- **Regularity of `X₀` and of its primitive** (source 4176-4214, 3603-3647: `X₀ = W_μ - W_{μ+1}`
is `C²` in `y` off the old disk and `C¹` in `τ` (no instantaneous term, `(G_μ - G_{μ+1})(0) = 0`);
`Ψ_{X₀}` is `C²` in `y` and `C¹` in `τ` by `∂_rΨ = rZ_z`, `∂_zΨ = -rZ_r` and the decay of
the separated kernels). -/
def TCReg : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      ContDiffAt ℝ 2 (sepX0 ν μ T τ) y ∧ DifferentiableAt ℝ (fun t => sepX0 ν μ T t y) τ ∧
        ContDiffAt ℝ 2 (psiFld (sepX0 ν μ T) τ) y ∧
        DifferentiableAt ℝ (fun t => psiFld (sepX0 ν μ T) t y) τ

/-- **Integrability along the half line** (source 4181-4192: "the separated-kernel estimates prove
convergence of this primitive and its differentiated versions"): `ρ·(P)_z(ρ,0,z)` is integrable on
`(ϱ y, ∞)` for `P = X₀, ∂_τX₀, y·∇X₀, ΔX₀`. -/
def TCInt : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      IntegrableOn (fun ρ : ℝ => ρ * sepX0 ν μ T τ !₂[ρ, 0, y 2] 2) (Ioi (ϱ y)) ∧
      IntegrableOn (fun ρ : ℝ => ρ * (deriv (fun s => sepX0 ν μ T s !₂[ρ, 0, y 2]) τ) 2)
        (Ioi (ϱ y)) ∧
      IntegrableOn (fun ρ : ℝ => ρ *
        (fderiv ℝ (sepX0 ν μ T τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y)) ∧
      IntegrableOn (fun ρ : ℝ => ρ * (physLap (sepX0 ν μ T τ) !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y))

/-- **`∂_τ` commutes with the primitive** (source 4176-4214: `𝒞_y` is phase independent; differentiate
the outward primitive under the integral). -/
def TCTime : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      deriv (fun t => psiFld (sepX0 ν μ T) t y) τ =
        psiFld (fun t y' => deriv (fun s => sepX0 ν μ T s y') t) τ y

/-- **`Ψ_{y·∇Z} = (y·∇)Ψ_Z - 2Ψ_Z`** (source 4176-4214: `Ψ_{AZ} = AΨ_Z + Ψ_Z`, `A = -y·∇/2`;
boundary terms vanish by decay). -/
def TCGrad : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      psiFld (fun t y' => fderiv ℝ (sepX0 ν μ T t) y' y') τ y =
        fderiv ℝ (psiFld (sepX0 ν μ T) τ) y y - (2 : ℝ) • psiFld (sepX0 ν μ T) τ y

/-- **`Ψ_{ΔZ} = ΔΨ_Z - 2Z_z e_z`** (source 4176-4214: `Ψ_{ΔZ} = (∂_r² - r⁻¹∂_r + ∂_z²)Ψ_Z`,
`ΔΨ_Z = ∂_r²Ψ + r⁻¹∂_rΨ + ∂_z²Ψ`, `r⁻¹∂_rΨ = Z_z`). -/
def TCLap : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      psiFld (fun t y' => physLap (sepX0 ν μ T t) y') τ y =
        physLap (psiFld (sepX0 ν μ T) τ) y - (2 * sepX0 ν μ T τ y 2) • coordinateVector 2

/-- **Radial derivative of the primitive** (source 4178: `∂_rΨ_Z = rZ_z`, with `Z_z(ρ,0,z) =
Z_z(y)` by axisymmetry of `X₀`). -/
def TCRad : Prop :=
  ∀ σ₁ σ₂ ν μ R P (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space),
    TCCtx σ₁ σ₂ ν μ R P T y →
      fderiv ℝ (psiFld (sepX0 ν μ T) τ) y (radialUnit y) =
        (ϱ y * sepX0 ν μ T τ y 2) • coordinateVector 2

/-- **The algebraic expansion** (source 3700-3712, 4203-4214; pure calculus): for an abstract field `Z`
that is `C²` in `y`, `C¹` in `τ`, with `C²`/`C¹` primitive, such that `ρ Z'_z` is integrable on
`(ϱ y, ∞)` for `Z' ∈ {Z, ∂_τZ, y·∇Z, ΔZ}` and the identities `TCTime`, `TCGrad`, `TCLap`, `TCRad` hold
at `(τ,y)`, off the axis: `D_{μ+1}(𝒞_yZ) - 𝒞_y(D_{μ+1}Z) = tcComm Z`.  (`outPrim` is linear on
integrable data; Leibniz for `c(ϱ)Z + F(ϱ)ψ e_z`; `∇ϱ = radialUnit`, `y·∇ϱ = ϱ`, `Δ(g∘ϱ) = g'' + g'/ϱ`
off the axis.) -/
def TCLeibniz : Prop :=
  ∀ (ν μ R : ℝ) (χy : ℝ → ℝ), IsStreamCutoff χy → 0 < ν → 0 < R →
    ∀ (Z : ℝ → Space → Space) (τ : ℝ) (y : Space), 0 < ϱ y →
      ContDiffAt ℝ 2 (Z τ) y → DifferentiableAt ℝ (fun t => Z t y) τ →
      ContDiffAt ℝ 2 (psiFld Z τ) y → DifferentiableAt ℝ (fun t => psiFld Z t y) τ →
      IntegrableOn (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, y 2] 2) (Ioi (ϱ y)) →
      IntegrableOn (fun ρ : ℝ => ρ * (deriv (fun s => Z s !₂[ρ, 0, y 2]) τ) 2) (Ioi (ϱ y)) →
      IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, y 2] !₂[ρ, 0, y 2]) 2)
        (Ioi (ϱ y)) →
      IntegrableOn (fun ρ : ℝ => ρ * (physLap (Z τ) !₂[ρ, 0, y 2]) 2) (Ioi (ϱ y)) →
      deriv (fun t => psiFld Z t y) τ = psiFld (fun t y' => deriv (fun s => Z s y') t) τ y →
      psiFld (fun t y' => fderiv ℝ (Z t) y' y') τ y =
        fderiv ℝ (psiFld Z τ) y y - (2 : ℝ) • psiFld Z τ y →
      psiFld (fun t y' => physLap (Z t) y') τ y =
        physLap (psiFld Z τ) y - (2 * Z τ y 2) • coordinateVector 2 →
      fderiv ℝ (psiFld Z τ) y (radialUnit y) = (ϱ y * Z τ y 2) • coordinateVector 2 →
      ∀ μ' : ℝ, physDmu ν μ' (wardStreamCut ν R χy Z) τ y -
          wardStreamCut ν R χy (physDmu ν μ' Z) τ y = tcComm ν R χy Z τ y

/-- **The cutoff coefficient bounds** (source 3684-3712; `νL⁻² = R⁻² ≤ 1`, `L = R√ν`, only
`χ̂_y⁽ᵏ⁾` for `k ≤ 3` on `[4/5,1]` enter, `t = νR²/r² ∈ [4/5,1]` on the annulus): for `L ≤ r ≤ L√(5/4)`,
`|A₁| ≤ C`, `|A₂| ≤ C L⁻¹`, `|B₁| ≤ C L⁻²`, `|B₂| ≤ C`. -/
def TCCoeff : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R →
    ∀ r : ℝ, R * Real.sqrt ν ≤ r → r ≤ R * Real.sqrt (5 * ν / 4) →
      |tcA1 ν R χy r| ≤ C ∧ |tcA2 ν R χy r| ≤ C * (R * Real.sqrt ν)⁻¹ ∧
        |tcB1 ν R χy r| ≤ C * ((R * Real.sqrt ν)⁻¹) ^ 2 ∧ |tcB2 ν R χy r| ≤ C

theorem tc_expr_bound {C L a1 a2 b1 b2 ψ : ℝ} (hC : 0 ≤ C) (h1 : |a1| ≤ C)
    (h2 : |a2| ≤ C * L⁻¹) (h3 : |b1| ≤ C * (L⁻¹) ^ 2) (h4 : |b2| ≤ C) (Z0 G : Space)
    (Gd : ℝ≥0∞) (hG : ‖G‖ₑ ≤ Gd) :
    ‖a1 • Z0 + a2 • G + (b1 * ψ + b2 * Z0 2) • coordinateVector 2‖ₑ ≤
      ENNReal.ofReal (2 * C) * (‖Z0‖ₑ + ENNReal.ofReal L⁻¹ * Gd +
        ENNReal.ofReal ((L⁻¹) ^ 2) * ENNReal.ofReal |ψ|) := by
  have he3 : ‖(coordinateVector 2 : Space)‖ₑ = 1 := by
    simp [coordinateVector, enorm_eq_nnnorm]
  have hz : ‖Z0 2‖ₑ ≤ ‖Z0‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le Z0 2)
  have hcl : ∀ a : ℝ, ‖a‖ₑ = ENNReal.ofReal |a| := fun a => Real.enorm_eq_ofReal_abs a
  set X := ‖Z0‖ₑ with hX
  set A := ENNReal.ofReal L⁻¹ * Gd with hA
  set B := ENNReal.ofReal ((L⁻¹) ^ 2) * ENNReal.ofReal |ψ| with hB
  have s1 : ‖a1 • Z0‖ₑ ≤ ENNReal.ofReal C * X := by
    rw [enorm_smul, hcl]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl
  have s2 : ‖a2 • G‖ₑ ≤ ENNReal.ofReal C * A := by
    rw [enorm_smul, hcl, hA, ← mul_assoc, ← ENNReal.ofReal_mul hC]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) hG
  have s3a : ‖b1 * ψ‖ₑ ≤ ENNReal.ofReal C * B := by
    rw [enorm_mul, hcl, hcl, hB, ← mul_assoc, ← ENNReal.ofReal_mul hC]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h3) le_rfl
  have s3b : ‖b2 * Z0 2‖ₑ ≤ ENNReal.ofReal C * X := by
    rw [enorm_mul, hcl]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h4) hz
  have s3 : ‖(b1 * ψ + b2 * Z0 2) • (coordinateVector 2 : Space)‖ₑ ≤
      ENNReal.ofReal C * B + ENNReal.ofReal C * X := by
    rw [enorm_smul, he3, mul_one]
    exact (enorm_add_le _ _).trans (add_le_add s3a s3b)
  have hcc : ENNReal.ofReal (2 * C) = ENNReal.ofReal C + ENNReal.ofReal C := by
    rw [two_mul, ENNReal.ofReal_add hC hC]
  have key : (ENNReal.ofReal C + ENNReal.ofReal C) * (X + A + B) =
      (ENNReal.ofReal C * X + ENNReal.ofReal C * A + (ENNReal.ofReal C * B + ENNReal.ofReal C * X))
        + (ENNReal.ofReal C * A + ENNReal.ofReal C * B) := by ring
  rw [hcc, key]
  refine le_trans ?_ le_self_add
  exact (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add s1 s2)) s3)

theorem tc_radialUnit_norm {y : Space} (h : 0 < ϱ y) : ‖radialUnit y‖ ≤ 1 := by
  unfold radialUnit
  have hw : ‖(!₂[y 0, y 1, 0] : Space)‖ = ϱ y := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three, ϱ, sq_abs]
  rw [norm_smul, hw, norm_inv, Real.norm_eq_abs, abs_of_pos h, inv_mul_cancel₀ h.ne']

/-- **`TransCommPoint` from the leaves.** -/
theorem transCommPoint_of (hReg : TCReg) (hInt : TCInt) (hT1 : TCTime) (hG : TCGrad)
    (hL : TCLap) (hRad : TCRad) (hLeib : TCLeibniz) (hCo : TCCoeff) : TransCommPoint := by
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨C, hC0, hB⟩ := hCo χy hχ
  refine ⟨2 * C, 0, by positivity, ?_⟩
  intro ν μ R P hν hν1 hR1 hP hμ T hT hM hA τ y hy
  have hctx : TCCtx σ₁ σ₂ ν μ R P T y := ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩
  have hR : 0 < R := by linarith
  have hL0 : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hϱ0 : 0 < ϱ y := lt_of_lt_of_le hL0 hy.1
  obtain ⟨r1, r2, r3, r4⟩ := hReg σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨i1, i2, i3, i4⟩ := hInt σ₁ σ₂ ν μ R P T τ y hctx
  have key := hLeib ν μ R χy hχ hν hR (sepX0 ν μ T) τ y hϱ0 r1 r2 r3 r4 i1 i2 i3 i4
    (hT1 σ₁ σ₂ ν μ R P T τ y hctx) (hG σ₁ σ₂ ν μ R P T τ y hctx)
    (hL σ₁ σ₂ ν μ R P T τ y hctx) (hRad σ₁ σ₂ ν μ R P T τ y hctx) (μ + 1)
  have e : sepComm ν μ R χy T τ y = tcComm ν R χy (sepX0 ν μ T) τ y := key
  rw [e]
  unfold tcComm
  obtain ⟨b1, b2, b3, b4⟩ := hB ν R hν hν1 hR1 (ϱ y) hy.1 hy.2
  have hG' : ‖fderiv ℝ (sepX0 ν μ T τ) y (radialUnit y)‖ₑ ≤ ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖fderiv ℝ (sepX0 ν μ T τ) y (radialUnit y)‖
        ≤ ‖fderiv ℝ (sepX0 ν μ T τ) y‖ * ‖radialUnit y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (sepX0 ν μ T τ) y‖ * 1 :=
          mul_le_mul_of_nonneg_left (tc_radialUnit_norm hϱ0) (norm_nonneg _)
      _ = _ := mul_one _
  have := tc_expr_bound (L := R * Real.sqrt ν) hC0 b1 b2 b3 b4 (sepX0 ν μ T τ y)
    (fderiv ℝ (sepX0 ν μ T τ) y (radialUnit y)) ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ hG'
    (ψ := outPrim (sepX0 ν μ T) τ (ϱ y) (y 2))
  simpa [transLen] using this

end UnforcedLeray.Short.PartIIIb.Concrete
