import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Decomposition of `XmtSolenoidal` (task `PartIII-b:C/srcL/7`)

Source of record: `the November 2 reference manuscript`, lines 4170-4190 (the
outward primitive `Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,z) dρ`; "Their decay makes the boundary term `rZ_r`
at infinity vanish. Hence `∂_r Ψ_Z = r Z_z` and `∂_z Ψ_Z = -r Z_r`. The cutoff is solenoidal")
and 4764-4800 (`Σ_M` is the Cartesian rotation of `ρ⁻¹E(u)`, `u = ρ⁻²`; `V_{μ,M}`, `W^mt`,
`X^mt = 𝒞_{χ_y}(W^mt_μ - W^mt_{μ+1})`; "It is trace free ... The uncut field is a harmonic
gradient").

Write `Z = W^mt_μ - W^mt_{μ+1}`, `r = |y'|`, `b = 5ν/(6ε²)` (so `outReg ν ε = {b < r²}`).

1. Region split (proved here).  Where `(εr)² < ν` the cutoff `χ_y` vanishes on an open
   neighbourhood, so `X^mt = 0` near `y` (this covers the axis); otherwise `y ∈ outReg ν ε`.
2. Axisymmetry (source 4771-4782).  `Σ_M(R_θ x') = R_θ Σ_M(x') R_θᵀ` (`SigmaMRot`: `Q(R_θx') =
   R_θ Q(x')` and `E` depends on `u = |x'|⁻²` only), `D³N(R_θ w) = R_θ^{⊗3} D³N(w)`
   (`NewtonD3Rot`: `N ∘ R_θ = N`), the contraction is covariant (`KerContractRot`) and `dx'` is
   rotation invariant (`RotPlMP`), so the inner integral (`NewtonInnerRot`) and then
   `V(R_θ x) = R_θ V(x)` off the old disc (`NewtonVEquivariant`); hence `Z` is axisymmetric on
   `outReg ν ε` (`axiEquivariant_youngW_of`).
3. Harmonic gradient (source 4797-4800).  `ΔN = 0` off `0` (`NewtonLap`), so
   `Σ_i ∂_i ∂_i∂_j∂_k N = 0` (`NewtonD3Div`), and differentiating under both integrals,
   `div V = 0` off the old disc (`NewtonInnerDiv`, `NewtonVDivFree`); hence `div Z = 0` on
   `outReg ν ε` (`div_youngW_diff_of`).
4. Outward primitive (source 4180-4186).  For an axisymmetric solenoidal `Z` with the decay of
   `XSZDecay`: the rotation generator gives `DZ(p)[Jp] = J Z(p)`, `J = ∂_θ R_θ|₀` (`AxiGenerator`),
   so along the ray `∂_ρ(ρ Z_r) = ρ(∂₁Z₁ + ∂₂Z₂) = -ρ ∂_z Z_z` (`RayFluxDeriv`); with
   `∂_z Ψ_Z = -∫_r^∞ ρ ∂_z Z_z dρ` (`StreamPsiDzInt`) and `ρ Z_r → 0` (`RayFluxTendsto`),
   `∂_z Ψ_Z = -r Z_r = -(y₁Z₁ + y₂Z₂)` (`streamPsiDz_of`).
5. Cutoff divergence.  `div 𝒞_y Z = χ_y' Z_r + χ_y div Z + (χ_y'/r) ∂_z Ψ_Z` (`StreamCutDiv`),
   which vanishes by 3 and 4 (`xmtSolenoidal_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Rotations about the axis -/

/-- The rotation `R_θ` by the angle `θ` about the `z`-axis (`e_z` is fixed). -/
def rotAx (θ : ℝ) (y : Vec3) : Vec3 :=
  ![Real.cos θ * y 0 - Real.sin θ * y 1, Real.sin θ * y 0 + Real.cos θ * y 1, y 2]

/-- The matrix of `R_θ` (`rotAx_apply`). -/
def rotMat (θ : ℝ) : Mat3 :=
  ![![Real.cos θ, -Real.sin θ, 0], ![Real.sin θ, Real.cos θ, 0], ![0, 0, 1]]

/-- The rotation by `θ` of the source plane `x' ∈ ℝ²`; `rotAx θ (x', 0) = (rotPl θ x', 0)`
(`rotAx_embPlane`). -/
def rotPl (θ : ℝ) (x' : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * x'.1 - Real.sin θ * x'.2, Real.sin θ * x'.1 + Real.cos θ * x'.2)

/-- Axisymmetry of a vector field on a set `U` (source 4771-4782, 4797-4799): `Z` commutes with
every rotation `R_θ` about the `z`-axis at the points of `U`, `Z(R_θ y) = R_θ Z(y)`.  For `U`
rotation invariant this says that the cylindrical components `Z_r, Z_φ, Z_z` depend on `(r, z)`
only.  The source fields are given by absolutely convergent integrals only off the old source
disc, so the property is stated on the outward region. -/
def AxiEquivariant (Z : Vec3 → Vec3) (U : Set Vec3) : Prop :=
  ∀ (θ : ℝ) (y : Vec3), y ∈ U → Z (rotAx θ y) = rotAx θ (Z y)

theorem rotAx_apply (θ : ℝ) (y : Vec3) (i : Fin 3) :
    rotAx θ y i = ∑ j, rotMat θ i j * y j := by
  fin_cases i <;> simp [rotAx, rotMat, Fin.sum_univ_three] <;> ring

theorem rotAx_add (θ : ℝ) (a b : Vec3) : rotAx θ (a + b) = rotAx θ a + rotAx θ b := by
  funext i; fin_cases i <;> simp [rotAx] <;> ring

theorem rotAx_smul (θ s : ℝ) (y : Vec3) : rotAx θ (s • y) = s • rotAx θ y := by
  funext i; fin_cases i <;> simp [rotAx] <;> ring

theorem rotAx_sub (θ : ℝ) (a b : Vec3) : rotAx θ (a - b) = rotAx θ a - rotAx θ b := by
  funext i; fin_cases i <;> simp [rotAx] <;> ring

theorem rotAx_neg_rotAx (θ : ℝ) (y : Vec3) : rotAx (-θ) (rotAx θ y) = y := by
  funext i
  fin_cases i
  · simp only [rotAx, Real.cos_neg, Real.sin_neg]
    simp
    linear_combination (y 0) * Real.sin_sq_add_cos_sq θ
  · simp only [rotAx, Real.cos_neg, Real.sin_neg]
    simp
    linear_combination (y 1) * Real.sin_sq_add_cos_sq θ
  · simp [rotAx]

/-- `R_θ` as a continuous linear equivalence of `ℝ³`, with inverse `R_{-θ}`. -/
def rotAxL (θ : ℝ) : Vec3 ≃L[ℝ] Vec3 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := rotAx θ
      map_add' := rotAx_add θ
      map_smul' := fun s y => rotAx_smul θ s y
      invFun := rotAx (-θ)
      left_inv := rotAx_neg_rotAx θ
      right_inv := fun y => by simpa using rotAx_neg_rotAx (-θ) y }

theorem rotAxL_apply (θ : ℝ) (y : Vec3) : rotAxL θ y = rotAx θ y := rfl

theorem sum_sq_rotAx (θ : ℝ) (w : Vec3) : ∑ i, rotAx θ w i ^ 2 = ∑ i, w i ^ 2 := by
  simp [rotAx, Fin.sum_univ_three]
  linear_combination (w 0 ^ 2 + w 1 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- `N ∘ R_θ = N`. -/
theorem newtonN_rotAx (θ : ℝ) (w : Vec3) : newtonN (rotAx θ w) = newtonN w := by
  unfold newtonN
  rw [sum_sq_rotAx]

theorem cylR_rotAx (θ : ℝ) (y : Vec3) : cylR (rotAx θ y) = cylR y := by
  unfold cylR
  congr 1
  simp [rotAx]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem rotAx_embPlane (θ : ℝ) (x' : ℝ × ℝ) : rotAx θ (embPlane x') = embPlane (rotPl θ x') := by
  funext i; fin_cases i <;> simp [rotAx, embPlane, rotPl]

theorem rotPl_sq (θ : ℝ) (x' : ℝ × ℝ) :
    (rotPl θ x').1 ^ 2 + (rotPl θ x').2 ^ 2 = x'.1 ^ 2 + x'.2 ^ 2 := by
  simp only [rotPl]
  linear_combination (x'.1 ^ 2 + x'.2 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- The columns of `rotMat θ` are orthonormal. -/
theorem rotMat_orth (θ : ℝ) (b p : Fin 3) :
    ∑ j, rotMat θ j b * rotMat θ j p = if b = p then 1 else 0 := by
  fin_cases b <;> fin_cases p <;> simp [rotMat, Fin.sum_univ_three] <;>
    first
    | ring1
    | linear_combination Real.sin_sq_add_cos_sq θ

/-- `R_θ` preserves `x₁² + x₂²` (so it preserves the region `{5ν/6 < x₁² + x₂²}`). -/
theorem sq_rotAx_horiz (θ : ℝ) (x : Vec3) :
    rotAx θ x 0 ^ 2 + rotAx θ x 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [rotAx]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.sin_sq_add_cos_sq θ

/-! ## 2. The cylindrical radius along the outward ray -/

theorem cylR_sq_sum (y : Vec3) : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem isOpen_cylSq (b : ℝ) : IsOpen {y : Vec3 | b < cylR y ^ 2} :=
  isOpen_lt continuous_const (continuous_cylR.pow 2)

theorem cylR_pos_of_lt {b : ℝ} (hb : 0 < b) {y : Vec3} (hy : b < cylR y ^ 2) : 0 < cylR y := by
  have h0 : 0 ≤ cylR y := Real.sqrt_nonneg _
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hy
    norm_num at hy
    linarith

theorem cylR_rayPt (y : Vec3) (ρ : ℝ) (hy : 0 < cylR y) : cylR (rayPt y ρ) = |ρ| := by
  have h2 : y 0 ^ 2 + y 1 ^ 2 = cylR y ^ 2 := (cylR_sq_sum y).symm
  have hne : cylR y ≠ 0 := hy.ne'
  have key : (rayPt y ρ) 0 ^ 2 + (rayPt y ρ) 1 ^ 2 = ρ ^ 2 := by
    simp only [rayPt, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_pow, mul_pow, div_pow, div_pow, ← mul_add, ← add_div, h2,
      div_self (pow_ne_zero 2 hne), mul_one]
  show Real.sqrt ((rayPt y ρ) 0 ^ 2 + (rayPt y ρ) 1 ^ 2) = |ρ|
  rw [key, Real.sqrt_sq_eq_abs]

theorem rayPt_self (y : Vec3) (hy : 0 < cylR y) : rayPt y (cylR y) = y := by
  have hne : cylR y ≠ 0 := hy.ne'
  funext i
  fin_cases i <;> simp [rayPt] <;> field_simp

/-- The radial flux `ρ Z_r` along the outward ray through `y` (`Z_r = e_r · Z`,
`e_r = (y₁/r, y₂/r, 0)` the fixed radial direction of the ray). -/
def rayFlux (Z : Vec3 → Vec3) (y : Vec3) (ρ : ℝ) : ℝ :=
  ρ * (y 0 / cylR y * Z (rayPt y ρ) 0 + y 1 / cylR y * Z (rayPt y ρ) 1)

theorem rayFlux_self (Z : Vec3 → Vec3) (y : Vec3) (hy : 0 < cylR y) :
    rayFlux Z y (cylR y) = y 0 * Z y 0 + y 1 * Z y 1 := by
  have hne : cylR y ≠ 0 := hy.ne'
  unfold rayFlux
  rw [rayPt_self y hy]
  field_simp

/-- The decay of `XSZDecay` (source 4776-4791, 4917-4937), the hypothesis of `XSStreamPsi`:
`|D^k Z(w)| ≤ C_k (1+|w|)^{-(4+k)}` on each `{a ≤ r²}`, `a > b`. -/
def DecayOff (b : ℝ) (Z : Vec3 → Vec3) : Prop :=
  ∀ a : ℝ, b < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
    ‖iteratedFDeriv ℝ k Z w‖ ≤ C * (1 + ‖w‖) ^ (-(4 + (k : ℝ)))

/-! ## 3. The leaves -/

/-- **(a0)** Rotations of the source plane preserve `dx'` (source 4776-4782: the `x'`-integral of
`V_{μ,M}` is over `ℝ²` with Lebesgue measure; conjugate by `Complex.measurableEquivRealProd` to
the rotation `rotation (Circle.exp θ)` of `ℂ`). -/
def RotPlMP : Prop :=
  ∀ θ : ℝ, MeasurePreserving (rotPl θ) (volume : Measure (ℝ × ℝ)) volume

/-- **(a1)** Rotation covariance of the third Newton derivatives off `0` (source 4776-4782,
`N(x) = 1/(4π|x|)` is rotation invariant): `∂_i∂_j∂_k N(R_θ w) = Σ R_{ia} R_{jb} R_{kd}
∂_a∂_b∂_d N(w)`. -/
def NewtonD3Rot : Prop :=
  ∀ (θ : ℝ) (w : Vec3), w ≠ 0 → ∀ i j k : Fin 3,
    newtonD3 (rotAx θ w) i j k =
      ∑ a, ∑ b, ∑ d, rotMat θ i a * rotMat θ j b * rotMat θ k d * newtonD3 w a b d

/-- **(a2)** Rotation covariance of the Cartesian source (source 4771-4775: `Σ_M(x')` is the
Cartesian rotation `Q(φ)(ρ⁻¹E(u))Q(φ)ᵀ` of a tensor of `u = ρ⁻²` alone, and
`Q(R_θ x') = R_θ Q(x')`): `Σ_M(R_θ x') = R_θ Σ_M(x') R_θᵀ`.  No hypothesis on `M`. -/
def SigmaMRot : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (θ : ℝ) (x' : ℝ × ℝ) (a b : Fin 3),
    sigmaM c ν χo M (rotPl θ x') a b =
      ∑ i, ∑ j, rotMat θ a i * sigmaM c ν χo M x' i j * rotMat θ b j

/-- **(a3)** The contraction `D³N : Σ` in the last two indices is covariant (source 4780-4782, the
velocity contraction of `∇K₀`): if `D` is rotated by `R_θ^{⊗3}` and `S` by `R_θ S R_θᵀ`, then
`Σ_{jk} D_{ijk} S_{jk}` is rotated by `R_θ` (orthonormality `rotMat_orth`). -/
def KerContractRot : Prop :=
  ∀ (θ : ℝ) (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (S : Fin 3 → Fin 3 → ℝ) (i : Fin 3),
    ∑ j, ∑ k, (∑ a, ∑ b, ∑ d, rotMat θ i a * rotMat θ j b * rotMat θ k d * D a b d) *
        (∑ p, ∑ q, rotMat θ j p * S p q * rotMat θ k q) =
      ∑ a, rotMat θ i a * ∑ j, ∑ k, D a j k * S j k

/-- **(a4)** The inner integral of `V_{μ,M}` is covariant off the old source disc (source
4776-4782, 4917-4937): for `t ∈ (0,1]` and `5ν/6 < x₁² + x₂²`,
`∫ Σ_{jk} ∂_i∂_j∂_k N(R_θx - t(x',0)) Σ_M(x')_{jk} dx' = Σ_a R_{ia} ∫ Σ_{jk} ∂_a∂_j∂_k N(x - t(x',0))
Σ_M(x')_{jk} dx'` (substitute `x' = R_θ a` by (a0); `R_θx - t(R_θa, 0) = R_θ(x - t(a,0))`; (a1),
(a2), (a3) pointwise; the integrands are integrable since the kernel is bounded on the support
`|a|² < 5ν/6` of `Σ_M` and `Σ_M ∈ L¹`). -/
def NewtonInnerRot : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → IsOutwardCutoff χo →
    OldThinFinite c ν M → ∀ (θ : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : Vec3,
      5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 → ∀ i : Fin 3,
        ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane x') i j k *
            sigmaM c ν χo M x' j k =
          ∑ a, rotMat θ i a * ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (x - t • embPlane x') a j k *
            sigmaM c ν χo M x' j k

/-- **(a5)** The zero-width Newton field is axisymmetric off the old source disc (source
4776-4782, 4917-4937): for `x` with `5ν/6 < x₁² + x₂²` (where both integrals converge
absolutely), `V_{μ,M}(R_θ x) = R_θ V_{μ,M}(x)`.  From (a4) for each `t ∈ (0,1]` and the
integrability on `(0,1]` of the outer integrands `t ↦ newtonFam a t x`. -/
def NewtonVEquivariant : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
      ∀ (θ : ℝ) (x : Vec3), 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 →
        newtonV c ν μ χo M (rotAx θ x) = rotAx θ (newtonV c ν μ χo M x)

/-- **(b1)** The Newton kernel is harmonic off `0` (source 4797-4800, `ΔN = 0` for
`N = 1/(4π|x|)`), in the nested-derivative form of `newtonD3`. -/
def NewtonLap : Prop :=
  ∀ w : Vec3, w ≠ 0 →
    ∑ i, fderiv ℝ (fun z : Vec3 => fderiv ℝ newtonN z (Pi.single i 1)) w (Pi.single i 1) = 0

/-- **(b2)** The divergence of the third-derivative kernel in its first index vanishes off `0`
(source 4797-4800): `Σ_i ∂_i(∂_i∂_j∂_k N) = ∂_j∂_k ΔN = 0` (derivatives of the smooth `N` commute
on `ℝ³ \ {0}`). -/
def NewtonD3Div : Prop :=
  ∀ w : Vec3, w ≠ 0 → ∀ j k : Fin 3,
    ∑ i, fderiv ℝ (fun x : Vec3 => newtonD3 x i j k) w (Pi.single i 1) = 0

/-- **(b3)** The inner integral of `V_{μ,M}` is solenoidal off the old disc (source 4776-4800):
for `t ∈ (0,1]` and `5ν/6 < x₁² + x₂²`, the vector field
`z ↦ (∫ Σ_{jk} ∂_i∂_j∂_k N(z - t(a,0)) Σ_M(a)_{jk} da)_i` has zero divergence at `x`
(differentiate under the `a`-integral, then (b2)). -/
def NewtonInnerDiv : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → IsOutwardCutoff χo →
    OldThinFinite c ν M → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : Vec3, 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 →
      ∑ i, fderiv ℝ (fun z : Vec3 => ∫ a : ℝ × ℝ,
        ∑ j, ∑ k, newtonD3 (z - t • embPlane a) i j k * sigmaM c ν χo M a j k) x
          (Pi.single i 1) = 0

/-- **(b4)** The zero-width Newton field is solenoidal off the old disc (source 4797-4800: "The
uncut field is a harmonic gradient"): `div V_{μ,M}(x) = 0` for `5ν/6 < x₁² + x₂²` (differentiate
under the `t`-integral, then (b3)). -/
def NewtonVDivFree : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M → ∀ x : Vec3, 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2 →
      ∑ i, fderiv ℝ (newtonV c ν μ χo M) x (Pi.single i 1) i = 0

/-- **(c1)** The infinitesimal rotation (source 4180-4186, axisymmetry used in the cylindrical
divergence): if `Z(R_θ p) = R_θ Z(p)` for all `θ` and `Z` is differentiable at `p`, then
`DZ(p)[Jp] = J Z(p)` with `J v = ∂_θ R_θ v|_{θ=0} = (-v₂, v₁, 0)`. -/
def AxiGenerator : Prop :=
  ∀ (Z : Vec3 → Vec3) (p : Vec3), (∀ θ : ℝ, Z (rotAx θ p) = rotAx θ (Z p)) →
    DifferentiableAt ℝ Z p → fderiv ℝ Z p ![-p 1, p 0, 0] = ![-Z p 1, Z p 0, 0]

/-- **(c2)** The cylindrical divergence along the outward ray (source 4180-4186): at
`p = rayPt y ρ`, with `e_r = (y₁/r, y₂/r, 0)`, `e_φ = (-y₂/r, y₁/r, 0)`, the generator identity
gives `ρ e_φ·DZ(p)e_φ = Z_r(p)`, hence `∂_ρ(ρ Z_r) = Z_r + ρ e_r·DZ e_r = ρ(∂₁Z₁ + ∂₂Z₂)`, and
`div Z(p) = 0` turns this into `-ρ ∂_z Z_z(p)`. -/
def RayFluxDeriv : Prop :=
  ∀ (Z : Vec3 → Vec3) (y : Vec3) (ρ : ℝ), 0 < cylR y → DifferentiableAt ℝ Z (rayPt y ρ) →
    fderiv ℝ Z (rayPt y ρ) ![-rayPt y ρ 1, rayPt y ρ 0, 0] =
      ![-Z (rayPt y ρ) 1, Z (rayPt y ρ) 0, 0] →
    ∑ i, fderiv ℝ Z (rayPt y ρ) (Pi.single i 1) i = 0 →
      HasDerivAt (rayFlux Z y) (-(ρ * fderiv ℝ Z (rayPt y ρ) (Pi.single 2 1) 2)) ρ

/-- **(c3)** Differentiation of the outward primitive in `z` (source 4180-4186, 4917-4937: "The
separated-kernel estimates prove convergence of this primitive and its differentiated
versions"): for `Z` smooth on `{b < r²}` with the decay `DecayOff b Z`, the integrand
`ρ ∂_z Z_z(ρ, z)` is integrable on `(r, ∞)` and `∂_z Ψ_Z(y) = -∫_r^∞ ρ ∂_z Z_z dρ`
(`cylR (y + t e_z) = cylR y`, `rayPt (y + t e_z) ρ = rayPt y ρ + t e_z`; dominated
differentiation in `t` with the bound `ρ C (1 + ρ/2)^{-5}` from `k = 1`). -/
def StreamPsiDzInt : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), 0 < b →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2} → DecayOff b Z →
      ∀ y : Vec3, b < cylR y ^ 2 →
        IntegrableOn (fun ρ => ρ * fderiv ℝ Z (rayPt y ρ) (Pi.single 2 1) 2) (Ioi (cylR y)) ∧
          fderiv ℝ (streamPsi Z) y (Pi.single 2 1) =
            -∫ ρ in Ioi (cylR y), ρ * fderiv ℝ Z (rayPt y ρ) (Pi.single 2 1) 2

/-- **(c4)** The boundary term at infinity vanishes (source 4184-4185: "Their decay makes the
boundary term `rZ_r` at infinity vanish"): `ρ Z_r(rayPt y ρ) → 0` as `ρ → ∞` (from `k = 0`). -/
def RayFluxTendsto : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), 0 < b → DecayOff b Z → ∀ y : Vec3, b < cylR y ^ 2 →
    Tendsto (rayFlux Z y) atTop (𝓝 0)

/-- **(c)** `∂_z Ψ_Z = -r Z_r` (source 4180-4186) for an axisymmetric, solenoidal field with the
decay of `XSZDecay`; here `r Z_r = y₁Z₁ + y₂Z₂`.  Proved from (c1)-(c4) in `streamPsiDz_of`. -/
def StreamPsiDz : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), 0 < b →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2} →
    AxiEquivariant Z {y | b < cylR y ^ 2} →
    (∀ y : Vec3, b < cylR y ^ 2 → ∑ i, fderiv ℝ Z y (Pi.single i 1) i = 0) →
    DecayOff b Z →
      ∀ y : Vec3, b < cylR y ^ 2 →
        fderiv ℝ (streamPsi Z) y (Pi.single 2 1) = -(y 0 * Z y 0 + y 1 * Z y 1)

/-- **(d)** The divergence of the outward stream cutoff off the axis (source 4182-4186:
`𝒞_y Z = χ_y Z + (χ_y'/r) Ψ_Z e_z`): `div 𝒞_y Z = χ_y' Z_r + χ_y div Z + (χ_y'/r) ∂_z Ψ_Z`,
with `χ_y = chiYr ν ε χy ∘ cylR`, `Z_r = (y₁Z₁ + y₂Z₂)/r`; the coefficient `χ_y'(r)/r` depends on
`y` through `r` only, so its `z`-derivative vanishes. -/
def StreamCutDiv : Prop :=
  ∀ (ν ε : ℝ) (χy : ℝ → ℝ), IsStreamCutoff χy → 0 < ε →
    ∀ (Z : Vec3 → Vec3) (y : Vec3), 0 < cylR y → DifferentiableAt ℝ Z y →
      DifferentiableAt ℝ (streamPsi Z) y →
        ∑ i, fderiv ℝ (streamCut ν ε χy Z) y (Pi.single i 1) i =
          deriv (chiYr ν ε χy) (cylR y) * ((y 0 * Z y 0 + y 1 * Z y 1) / cylR y) +
            chiYr ν ε χy (cylR y) * ∑ i, fderiv ℝ Z y (Pi.single i 1) i +
            deriv (chiYr ν ε χy) (cylR y) / cylR y * fderiv ℝ (streamPsi Z) y (Pi.single 2 1)

/-! ## 4. Compositions -/

theorem smul_mem_newtonRegion {ν ε : ℝ} (hε : 0 < ε) {y : Vec3} (hy : y ∈ outReg ν ε) :
    5 * ν / 6 < (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 := by
  have hy' : 5 * ν / (6 * ε ^ 2) < y 0 ^ 2 + y 1 ^ 2 := by
    have h : 5 * ν / (6 * ε ^ 2) < cylR y ^ 2 := hy
    rwa [cylR_sq_sum] at h
  have h2 : 0 < 6 * ε ^ 2 := by positivity
  have := (div_lt_iff₀ h2).1 hy'
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

/-- `W^mt_μ(R_θ y) = R_θ W^mt_μ(y)` on the outward region, from (a3). -/
theorem youngW_rotAx_of (hA : NewtonVEquivariant) {c ν ε μ : ℝ} {χo : ℝ → ℝ}
    {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (hμ : 0 < μ)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (θ : ℝ) {y : Vec3}
    (hy : y ∈ outReg ν ε) :
    youngW c ν ε μ χo M (rotAx θ y) = rotAx θ (youngW c ν ε μ χo M y) := by
  have hx := smul_mem_newtonRegion hε hy
  unfold youngW
  rw [← rotAx_smul, hA c ν μ χo M hc hν hμ hχ hM θ (ε • y) hx, rotAx_smul]

/-- `Z = W^mt_μ - W^mt_{μ+1}` is axisymmetric on the outward region. -/
theorem axiEquivariant_youngW_of (hA : NewtonVEquivariant) {c ν ε μ : ℝ} {χo : ℝ → ℝ}
    {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (hμ : 0 < μ)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) :
    AxiEquivariant (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (outReg ν ε) := by
  intro θ y hy
  simp only [Pi.sub_apply]
  rw [youngW_rotAx_of hA hc hν hε hμ hχ hM θ hy,
    youngW_rotAx_of (μ := μ + 1) hA hc hν hε (by linarith) hχ hM θ hy, rotAx_sub]

/-- `W^mt_μ` is differentiable and solenoidal on the outward region, from (b4):
`div W^mt_μ(y) = ε³ (div V_{μ,M})(εy)`. -/
theorem youngW_div_of (hV : NewtonVSmooth) (hB : NewtonVDivFree) {c ν ε μ : ℝ} {χo : ℝ → ℝ}
    {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (hμ : 0 < μ)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) {y : Vec3} (hy : y ∈ outReg ν ε) :
    DifferentiableAt ℝ (youngW c ν ε μ χo M) y ∧
      ∑ i, fderiv ℝ (youngW c ν ε μ χo M) y (Pi.single i 1) i = 0 := by
  have hx := smul_mem_newtonRegion hε hy
  have hU : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have hVd : DifferentiableAt ℝ (newtonV c ν μ χo M) (ε • y) :=
    ((hV c ν μ χo M hc hν hμ hχ hM).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hlin : HasFDerivAt (fun y : Vec3 => ε • y) (ε • ContinuousLinearMap.id ℝ Vec3) y :=
    (hasFDerivAt_id y).const_smul ε
  have hY : HasFDerivAt (youngW c ν ε μ χo M)
      ((ε ^ 2) • (fderiv ℝ (newtonV c ν μ χo M) (ε • y)).comp
        (ε • ContinuousLinearMap.id ℝ Vec3)) y :=
    (hVd.hasFDerivAt.comp y hlin).const_smul (ε ^ 2)
  refine ⟨hY.differentiableAt, ?_⟩
  rw [hY.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hB c ν μ χo M hc hν hμ hχ hM (ε • y) hx]
  ring

/-- `div Z = 0` on the outward region, `Z = W^mt_μ - W^mt_{μ+1}`. -/
theorem div_youngW_diff_of (hV : NewtonVSmooth) (hB : NewtonVDivFree) {c ν ε μ : ℝ}
    {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (hμ : 0 < μ)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) :
    ∀ y ∈ outReg ν ε,
      ∑ i, fderiv ℝ (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) y (Pi.single i 1) i
        = 0 := by
  intro y hy
  obtain ⟨hd1, hs1⟩ := youngW_div_of hV hB hc hν hε hμ hχ hM hy
  obtain ⟨hd2, hs2⟩ := youngW_div_of (μ := μ + 1) hV hB hc hν hε (by linarith) hχ hM hy
  rw [fderiv_sub hd1 hd2]
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, Finset.sum_sub_distrib, hs1, hs2,
    sub_zero]

/-- **(c)** from (c1)-(c4): the fundamental theorem of calculus on `(r, ∞)` for `ρ ↦ ρ Z_r`. -/
theorem streamPsiDz_of (h1 : AxiGenerator) (h2 : RayFluxDeriv) (h3 : StreamPsiDzInt)
    (h4 : RayFluxTendsto) : StreamPsiDz := by
  intro b Z hb hZ heq hdiv hdec y hy
  have hr : 0 < cylR y := cylR_pos_of_lt hb hy
  have hU : IsOpen {y : Vec3 | b < cylR y ^ 2} := isOpen_cylSq b
  have hmem : ∀ ρ, cylR y ≤ ρ → b < cylR (rayPt y ρ) ^ 2 := by
    intro ρ hρ
    rw [cylR_rayPt y ρ hr, sq_abs]
    nlinarith
  have hderiv : ∀ ρ, cylR y ≤ ρ →
      HasDerivAt (rayFlux Z y) (-(ρ * fderiv ℝ Z (rayPt y ρ) (Pi.single 2 1) 2)) ρ := by
    intro ρ hρ
    have hp := hmem ρ hρ
    have hd : DifferentiableAt ℝ Z (rayPt y ρ) :=
      (hZ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    exact h2 Z y ρ hr hd (h1 Z (rayPt y ρ) (fun θ => heq θ (rayPt y ρ) hp) hd) (hdiv _ hp)
  obtain ⟨hint, hfor⟩ := h3 b Z hb hZ hdec y hy
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := rayFlux Z y) (f' := fun ρ => -(ρ * fderiv ℝ Z (rayPt y ρ) (Pi.single 2 1) 2))
    (hderiv (cylR y) le_rfl).continuousAt.continuousWithinAt
    (fun ρ hρ => hderiv ρ (le_of_lt hρ)) hint.neg (h4 b Z hb hdec y hy)
  rw [hfor, ← integral_neg, hftc, rayFlux_self Z y hr]
  ring

/-- **`XmtSolenoidal`** (source 4170-4190, 4797-4800) from the leaves: region split, then
(d) with (b) and (c). -/
theorem xmtSolenoidal_of (hA : NewtonVEquivariant) (hB : NewtonVDivFree) (hC : StreamPsiDz)
    (hD : StreamCutDiv) (hV : NewtonVSmooth) (h2 : XSZDecay) (h3 : XSStreamPsi) :
    XmtSolenoidal := by
  intro c ν ε μ χo χy hL M hM y
  by_cases hy : (ε * cylR y) ^ 2 < ν
  · -- near `y` the cutoff vanishes, so `X^mt = 0` there (this covers the axis)
    have hopen : IsOpen {y' : Vec3 | (ε * cylR y') ^ 2 < ν} :=
      isOpen_lt ((continuous_const.mul continuous_cylR).pow 2) continuous_const
    have hev : Xmt c ν ε μ χo χy M =ᶠ[𝓝 y] fun _ => (0 : Vec3) := by
      filter_upwards [hopen.mem_nhds hy] with y' hy'
      have hz : chiYr ν ε χy (cylR y') = 0 := chiYr_zero_of_lt hL.chiY hL.eps_pos hy'
      have hd : deriv (chiYr ν ε χy) (cylR y') = 0 := by
        have hop : IsOpen {r : ℝ | (ε * r) ^ 2 < ν} :=
          isOpen_lt ((continuous_const.mul continuous_id).pow 2) continuous_const
        have : chiYr ν ε χy =ᶠ[𝓝 (cylR y')] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hy'] with r hr
          exact chiYr_zero_of_lt hL.chiY hL.eps_pos hr
        rw [this.deriv_eq]; simp
      simp [Xmt, streamCut, hz, hd]
    rw [hev.fderiv_eq]
    simp
  · have hν := hL.nu_pos
    have hε := hL.eps_pos
    have hyU : y ∈ outReg ν ε := by
      show 5 * ν / (6 * ε ^ 2) < cylR y ^ 2
      rw [div_lt_iff₀ (by positivity)]
      have hy' : ν ≤ (ε * cylR y) ^ 2 := not_lt.1 hy
      nlinarith
    set Z : Vec3 → Vec3 := youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M with hZ
    have hb : 0 < 5 * ν / (6 * ε ^ 2) := by positivity
    have hZs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z (outReg ν ε) :=
      xsZSmooth_of hV c ν ε μ χo M hL.c_pos hν hε hL.mu_pos hL.chiO hM
    have hdec : DecayOff (5 * ν / (6 * ε ^ 2)) Z :=
      h2 c ν ε μ χo M hL.c_pos hν hε hL.mu_pos hL.chiO hM
    have hΨ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (streamPsi Z) (outReg ν ε) :=
      h3 _ Z hb hZs hdec
    have hpos : 0 < cylR y := cylR_pos_of_lt hb hyU
    have hO := (isOpen_outReg ν ε).mem_nhds hyU
    have hZd : DifferentiableAt ℝ Z y := (hZs.contDiffAt hO).differentiableAt (by simp)
    have hΨd : DifferentiableAt ℝ (streamPsi Z) y :=
      (hΨ.contDiffAt hO).differentiableAt (by simp)
    have hdiv : ∀ y' ∈ outReg ν ε, ∑ i, fderiv ℝ Z y' (Pi.single i 1) i = 0 :=
      div_youngW_diff_of hV hB hL.c_pos hν hε hL.mu_pos hL.chiO hM
    have hax : AxiEquivariant Z (outReg ν ε) :=
      axiEquivariant_youngW_of hA hL.c_pos hν hε hL.mu_pos hL.chiO hM
    have hdz : fderiv ℝ (streamPsi Z) y (Pi.single 2 1) = -(y 0 * Z y 0 + y 1 * Z y 1) :=
      hC _ Z hb hZs hax hdiv hdec y hyU
    have hcut := hD ν ε χy hL.chiY hε Z y hpos hZd hΨd
    show ∑ i, fderiv ℝ (streamCut ν ε χy Z) y (Pi.single i 1) i = 0
    rw [hcut, hdiv y hyU, hdz]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
