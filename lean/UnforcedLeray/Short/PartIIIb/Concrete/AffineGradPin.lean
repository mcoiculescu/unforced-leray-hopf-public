import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope

/-!
# The physical gradient `∇ĥ_A` of the affine lift and its pin (source 4976-4985, 5009-5016, 5036-5039)

Source of record: `the November 2 reference manuscript` (73 pages).

Step (1) of `ORG:stmt/PartIII-b/GeneralAffineBounds/grad-pin`.  `GeneralAffineBounds`
(StatementsA.lean) contains `R⁻¹‖∇ĥ_A‖_{Y_2}` (source 5011-5013) through the `ReturnSeq` field
`gradhA n z : Aff n →ₗ Grd n`; at the concrete instance `Grd n = GrdG c_n`
(`Concrete/AffineBoundSpaces.lean`), the tensor space `L²(π s^{-1/2} dς; ℝ^{3×3})` of
coefficients `T = s⁻¹∇ĥ` in the tensor lift `𝒩_T T = sT` (source 2681-2689), so that
`R⁻¹‖∇ĥ‖_{Y_2} = √π‖s⁻¹∇ĥ‖_{H_T}`.  This file defines the physical spatial gradient of `ĥ_A`
on the chart and pins `gradhA` to it.

## Chart conventions (checked against source 2666-2701, 1638-1650, 1918-1921, 5036-5039)

Cylinder chart `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`, with `ρ = r = |y'|` the
cylindrical radius (source 2672-2674, 4162: `r = |y'|`, `s = R²/r²`), `R = ε⁻¹`, component order
`(r, φ, z)`.  At fixed phase `τ` and height `z`: `∂_r s = -2s/r`, `∂_r q = R/r`,
`∂_r η = -η/r`, and `R/r = √s`, so the exact ring-chart rules (source 5036-5039) are
`∂_r = √s(∂_q − ε𝒦)`, `∂_z = √s ∂_η`, `𝒦 = η∂_η + 2s∂_s` (`Kop`), and `1/r = ε√s`
(`r = R/√s`, source 4996-4997).  Consistency check: `𝒦√s = √s` gives
`∂_r(√s b) = s(∂_q − ε(𝒦+1))b = sQ_ε b` (source 1920) and `∂_z(√s b) = s∂_ηb` (source 1921).

The gradient convention is `(∇u)_{ij} = ∂_j u_i` (the matrix `Du` of source 4232-4241,
`(Du X)_i = Σ_j ∂_j u_i X_j`); the Frobenius norm, hence `‖∇ĥ_A‖_{Y_2}`, does not depend on this
choice.  For an axisymmetric field `u = u_r e_r + u_φ e_φ + u_z e_z` (∂_φ = 0) in the
orthonormal frame `(e_r, e_φ, e_z)`:
`∇u = [[∂_r u_r, −u_φ/r, ∂_z u_r], [∂_r u_φ, u_r/r, ∂_z u_φ], [∂_r u_z, 0, ∂_z u_z]]`.
`ĥ_A = √s[(h^p_A)_r e_r + ((h^p_A)_z + ε(1−𝒦)ψ^p_A) e_z]` has no swirl (`hhatA_phi`), so
`∇ĥ_A` has no component with exactly one azimuthal index (`physGradA_mixed`, source 1645-1646);
its hoop entry is `(ĥ_A)_r/r = ε√s (ĥ_A)_r`.

## Contents

* `chartComp`, `dQ`, `dEta`, `physDr`, `physDz`, `cylGrad` : the chart gradient;
  `physGradA ν ε χ A s x = cylGrad ε (hhatA ν ε χ A) s x` (`= ∇ĥ_A` at the chart point).
* `gradAcoef` : the tensor coefficient `s⁻¹∇ĥ_A`; `IsAffineGradPinned G ι χf ν ε` : the pin of a
  gradient map `G : Aff →L GrdG c` (mirrors `IsAffinePinned`, `Concrete/ReturnOps.lean`).
* Leaves (tasks): `CylGradLinear` (`PartIII-b:C/grad/1`), `HhatADiff` (`PartIII-b:C/grad/2`,
  source 4978), `GradCoefBound` (`PartIII-b:C/grad/3`, the `∇ĥ_A` part of source 5011-5013, proof
  5073-5079).
* Proved: `hhatA_phi`, `hhatA_of_nonpos`, `physGradA_mixed`, `physGradA_of_nonpos`,
  `gradCoefLinear_of` (`A ↦ ∇ĥ_A` linear on `𝒜`, source 4985), `AffineGradData` with `gradAL`,
  `isAffineGradPinned_of`, `affineGradData_of` (the pinned gradient map at one regime from the
  leaves and the envelope `M(ιA) ≤ C_env‖A‖`, `Concrete/AffineEnvelope.lean`), and
  `affineGradNorm_le` (the `‖∇ĥ_A‖` part of `GeneralAffineBounds`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The chart gradient -/

/-- Component `i` (order `(r, φ, z)`) of a chart vector field `u(s, (q, η))`. -/
def chartComp (u : ℝ → ℝ × ℝ → Vec3) (i : Fin 3) : ℝ → ℝ × ℝ → ℝ := fun s y => u s y i

/-- `∂_q ψ` at the chart point `(s, x)`, `x = (q, η)`. -/
def dQ (ψ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ (ψ s) x (ei 0)

/-- `∂_η ψ` at the chart point `(s, x)`. -/
def dEta (ψ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ (ψ s) x (ei 1)

/-- The physical radial derivative in the ring chart, `∂_r = √s(∂_q − ε𝒦)`,
`𝒦 = η∂_η + 2s∂_s` (source 5036-5039; `Kop`, source 4979). -/
def physDr (ε : ℝ) (ψ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.sqrt s * (dQ ψ s x - ε * Kop ψ s x)

/-- The physical axial derivative in the ring chart, `∂_z = √s∂_η` (source 5036-5039). -/
def physDz (ψ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ := Real.sqrt s * dEta ψ s x

/-- The physical spatial gradient `(∇u)_{ij} = ∂_j u_i` of the axisymmetric field
`u = u_r e_r + u_φ e_φ + u_z e_z` recorded on the ring chart, in the frame `(e_r, e_φ, e_z)`,
with `∂_r, ∂_z` the ring-chart rules (source 5036-5039) and `1/r = ε√s` (`r = R/√s`, source
4996-4997):
`[[∂_r u_r, −u_φ/r, ∂_z u_r], [∂_r u_φ, u_r/r, ∂_z u_φ], [∂_r u_z, 0, ∂_z u_z]]`. -/
def cylGrad (ε : ℝ) (u : ℝ → ℝ × ℝ → Vec3) (s : ℝ) (x : ℝ × ℝ) : Mat3 :=
  ![![physDr ε (chartComp u 0) s x, -(ε * Real.sqrt s * u s x 1), physDz (chartComp u 0) s x],
    ![physDr ε (chartComp u 1) s x, ε * Real.sqrt s * u s x 0, physDz (chartComp u 1) s x],
    ![physDr ε (chartComp u 2) s x, 0, physDz (chartComp u 2) s x]]

/-- `∇ĥ_A` at the chart point `(s, x)`: the physical spatial gradient of the affine lift
`ĥ_A = √s[(h^p_A)_r e_r + ((h^p_A)_z + ε(1−𝒦)ψ^p_A) e_z]` (source 4979-4980, `hhatA`),
`ε = R⁻¹`. -/
def physGradA (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : Mat3 :=
  cylGrad ε (hhatA ν ε χ A) s x

/-- The tensor coefficient `T = s⁻¹∇ĥ_A` of `∇ĥ_A` in the tensor lift `𝒩_T T = sT`
(source 2681-2689), so that `R⁻¹‖∇ĥ_A‖_{Y_2} = ‖T‖_{L²(π s^{-1/2} dς)}`. -/
def gradAcoef (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) : Ten3 :=
  (p.1)⁻¹ • matTen (physGradA ν ε χf A p.1 p.2)

/-- The gradient map `G : A ↦ ∇ĥ_A` of the instance is the physical gradient of the affine lift
of `Concrete/ReturnAff.lean` (source 4979-4980, 5011-5013), read in the tensor coefficient
convention `T = s⁻¹ ·` (physical tensor) of `GrdG` (source 2681-2689).  `ι` is the inclusion of
`𝒜` into matrix functions, `χf` the source cutoff profile, `ε = R⁻¹`.  Mirrors
`IsAffinePinned` (`Concrete/ReturnOps.lean`). -/
def IsAffineGradPinned {c : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    (G : Aff →L[ℝ] GrdG c) (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) (χf : ℝ → ℝ) (ν ε : ℝ) : Prop :=
  ∀ A : Aff, (G A : Chart → Ten3) =ᵐ[gradMeasure c]
    fun p => (p.1)⁻¹ • matTen (physGradA ν ε χf (ι A) p.1 p.2)

/-! ## 2. Sanity facts -/

/-- `ĥ_A` has no swirl (source 4980). -/
@[simp] theorem hhatA_phi (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hhatA ν ε χ A s x 1 = 0 := by
  simp [hhatA, emb]

/-- `ĥ_A = √s(…)` vanishes off the age range `s > 0`. -/
theorem hhatA_of_nonpos {s : ℝ} (hs : s ≤ 0) (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3)
    (x : ℝ × ℝ) : hhatA ν ε χ A s x = 0 := by
  simp [hhatA, Real.sqrt_eq_zero_of_nonpos hs]

theorem chartComp_hhatA_phi (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) :
    chartComp (hhatA ν ε χ A) 1 = fun _ _ => 0 := by
  funext s y
  exact hhatA_phi ν ε χ A s y

/-- `∇ĥ_A` has no component with exactly one azimuthal index (source 1645-1646). -/
theorem physGradA_mixed (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    physGradA ν ε χ A s x 0 1 = 0 ∧ physGradA ν ε χ A s x 1 0 = 0 ∧
      physGradA ν ε χ A s x 1 2 = 0 ∧ physGradA ν ε χ A s x 2 1 = 0 := by
  simp [physGradA, cylGrad, chartComp_hhatA_phi, physDr, physDz, dQ, dEta, Kop]

/-- `∇ĥ_A` vanishes off the age range `s > 0` (all entries carry the factor `√s`). -/
theorem physGradA_of_nonpos {s : ℝ} (hs : s ≤ 0) (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3)
    (x : ℝ × ℝ) : physGradA ν ε χ A s x = 0 := by
  have h0 : Real.sqrt s = 0 := Real.sqrt_eq_zero_of_nonpos hs
  funext i j
  fin_cases i <;> fin_cases j <;> simp [physGradA, cylGrad, physDr, physDz, h0]

/-! ## 3. Leaves -/

/-- `C/grad/1`: the chart gradient is linear in the field at a point where the components are
differentiable in `x = (q, η)` and in `s` (the chart derivatives `∂_q, ∂_η, ∂_s` are linear). -/
def CylGradLinear : Prop :=
  ∀ (ε : ℝ) (u v : ℝ → ℝ × ℝ → Vec3) (r s : ℝ) (x : ℝ × ℝ),
    (∀ i, DifferentiableAt ℝ (chartComp u i s) x) →
    (∀ i, DifferentiableAt ℝ (chartComp v i s) x) →
    (∀ i, DifferentiableAt ℝ (fun s' => chartComp u i s' x) s) →
    (∀ i, DifferentiableAt ℝ (fun s' => chartComp v i s' x) s) →
    cylGrad ε (u + v) s x = cylGrad ε u s x + cylGrad ε v s x ∧
    cylGrad ε (r • u) s x = r • cylGrad ε u s x

/-- `C/grad/2`: `ĥ_A` is differentiable in `x = (q, η)` and in `s` at every chart point with
`s > 0`, for `A ∈ 𝒜` (`C^6` in `s`, source 4741-4745) and `ν > 0` (source 4978: "The sums and
their required derivatives converge by Gaussian decay"; the `z` component contains
`𝒦ψ^p_A`, so this uses second derivatives of `ψ^p_A`, within the budget of source 5081-5084). -/
def HhatADiff (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s →
    ∀ (x : ℝ × ℝ) (i : Fin 3),
      DifferentiableAt ℝ (chartComp (hhatA ν ε χf A) i s) x ∧
      DifferentiableAt ℝ (fun s' => chartComp (hhatA ν ε χf A) i s' x) s

/-- `C/grad/3`: the `∇ĥ_A` term of the first line of `ret:general-affine-bounds` (source
5009-5016; proof 5073-5079: "The same calculation with the physical spatial Jacobian `s^{-5/2}`
bounds the lift and its gradient"): for `0 < ε, ν ≤ 1`,
`R⁻¹‖∇ĥ_A‖_{Y_2} = ‖s⁻¹∇ĥ_A‖_{L²(π s^{-1/2} dς)} ≤ P_ν M(A)`, `P_ν = Cν^{-k}`, `c = ν⁻²`. -/
def GradCoefBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν ε : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
    ∀ A : ℝ → Mat3, IsAffElem as A →
      MemLp (gradAcoef ν ε χf A) 2 (gradMeasure (cOf ν)) ∧
      eLpNorm (gradAcoef ν ε χf A) 2 (gradMeasure (cOf ν)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * affM ν χf A)

/-- `A ↦ ∇ĥ_A` is linear on `𝒜` (source 4985), at every chart point with `s > 0`. -/
def GradCoefLinear (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν ε : ℝ), 0 < ν → ∀ (A A' : ℝ → Mat3) (r : ℝ), IsAffElem as A → IsAffElem as A' →
    ∀ p : Chart, 0 < p.1 →
      gradAcoef ν ε χf (A + A') p = gradAcoef ν ε χf A p + gradAcoef ν ε χf A' p ∧
      gradAcoef ν ε χf (r • A) p = r • gradAcoef ν ε χf A p

/-! ## 4. Linearity of `A ↦ ∇ĥ_A` -/

/-- A no-swirl vector is determined by its `(r, z)` components after a nonzero rescaling. -/
theorem vec3_eq_of_merOf {u v : Vec3} {t : ℝ} (ht : t ≠ 0) (hu : u 1 = 0) (hv : v 1 = 0)
    (h : merOf (t • u) = merOf (t • v)) : u = v := by
  have h0 := congrArg (fun w : Merid => w 0) h
  have h2 := congrArg (fun w : Merid => w 1) h
  simp only [merOf] at h0 h2
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h2
  funext i
  fin_cases i
  · simpa [ht] using h0
  · simp [hu, hv]
  · simpa [ht] using h2

/-- `ĥ_{A+A'} = ĥ_A + ĥ_{A'}` and `ĥ_{rA} = rĥ_A` as chart fields, from the coefficient
linearity `HhatCoefLinear` (`s > 0`) and `ĥ = 0` for `s ≤ 0`. -/
theorem hhatA_linear_of {as : ℝ} {χf : ℝ → ℝ} (lh : HhatCoefLinear as χf) {ν ε : ℝ}
    (hν : 0 < ν) {A A' : ℝ → Mat3} (r : ℝ) (hA : IsAffElem as A) (hA' : IsAffElem as A') :
    hhatA ν ε χf (A + A') = hhatA ν ε χf A + hhatA ν ε χf A' ∧
    hhatA ν ε χf (r • A) = r • hhatA ν ε χf A := by
  constructor
  · funext s x
    by_cases hs : 0 < s
    · have ht : (Real.sqrt s)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.2 hs)
      refine vec3_eq_of_merOf ht (hhatA_phi _ _ _ _ _ _) (by simp) ?_
      have h := (lh ν ε hν A A' r hA hA' (s, x) hs).1
      simp only [hAcoef] at h
      rw [Pi.add_apply, Pi.add_apply, smul_add, affMerOf_add]
      exact h
    · have hs' : s ≤ 0 := not_lt.1 hs
      simp [hhatA_of_nonpos hs']
  · funext s x
    by_cases hs : 0 < s
    · have ht : (Real.sqrt s)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.2 hs)
      refine vec3_eq_of_merOf ht (hhatA_phi _ _ _ _ _ _) (by simp) ?_
      have h := (lh ν ε hν A A r hA hA (s, x) hs).2
      simp only [hAcoef] at h
      rw [h, Pi.smul_apply, Pi.smul_apply, smul_comm (Real.sqrt s)⁻¹ r, affMerOf_smul r]
    · have hs' : s ≤ 0 := not_lt.1 hs
      simp [hhatA_of_nonpos hs']

/-- `A ↦ ∇ĥ_A` is linear on `𝒜` (source 4985), from the leaves. -/
theorem gradCoefLinear_of {as : ℝ} {χf : ℝ → ℝ} (hc : CylGradLinear)
    (lh : HhatCoefLinear as χf) (dh : HhatADiff as χf) : GradCoefLinear as χf := by
  intro ν ε hν A A' r hA hA' p hp
  obtain ⟨hadd, hsm⟩ := hhatA_linear_of lh (ε := ε) hν r hA hA'
  have hl := hc ε (hhatA ν ε χf A) (hhatA ν ε χf A') r p.1 p.2
    (fun i => (dh ν ε hν A hA p.1 hp p.2 i).1) (fun i => (dh ν ε hν A' hA' p.1 hp p.2 i).1)
    (fun i => (dh ν ε hν A hA p.1 hp p.2 i).2) (fun i => (dh ν ε hν A' hA' p.1 hp p.2 i).2)
  constructor
  · simp only [gradAcoef, physGradA]
    rw [hadd, hl.1, matTen_add, smul_add]
  · simp only [gradAcoef, physGradA]
    rw [hsm, hl.2, matTen_smul, smul_comm]

/-! ## 5. The pinned gradient map at one regime -/

/-- The gradient measure lives on `s > 0`. -/
theorem ae_gradMeasure_fst_pos (c : ℝ) : ∀ᵐ p ∂(gradMeasure c), 0 < p.1 :=
  Measure.ae_smul_measure (ae_ageμ_fst_pos c _) _

section Regime

variable {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]

/-- At one regime `(ν, ε)` (`c = ν⁻²`), the gradient coefficients `s⁻¹∇ĥ_{ιA}` form an `L²`
family on `Aff` in the measure `π s^{-1/2} dς` of `GrdG`. -/
structure AffineGradData (as ν ε : ℝ) (χf : ℝ → ℝ) (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) : Prop where
  grad : IsL2Family (gradMeasure (cOf ν)) fun A : Aff => gradAcoef ν ε χf (ι A)

namespace AffineGradData

variable {as ν ε : ℝ} {χf : ℝ → ℝ} {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}

/-- `A ↦ ∇ĥ_A` as a continuous linear map into `GrdG` (source 5011-5013). -/
def gradAL (h : AffineGradData as ν ε χf ι) : Aff →L[ℝ] GrdG (cOf ν) := h.grad.toCLM

/-- The constructed gradient map is pinned. -/
theorem isAffineGradPinned_of (h : AffineGradData as ν ε χf ι) :
    IsAffineGradPinned h.gradAL ι χf ν ε := fun A => h.grad.toCLM_ae A

end AffineGradData

/-- From the leaves, the gradient data at one regime `0 < ν, ε ≤ 1`, given the generic envelope
`M(ιA) ≤ C_env‖A‖` (source 5089-5091; `affM_le_norm_of`, `Concrete/AffineEnvelope.lean`). -/
theorem affineGradData_of {as ν ε : ℝ} {χf : ℝ → ℝ} {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}
    (hι : ∀ A, IsAffElem as (ι A)) (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Cenv : ℝ) (henv : ∀ A, affM ν χf (ι A) ≤ Cenv * ‖A‖)
    (lg : GradCoefLinear as χf) (bg : GradCoefBound as χf) :
    AffineGradData as ν ε χf ι := by
  obtain ⟨Cg, kg, hCg, bg⟩ := bg
  have hpos : ∀ᵐ p ∂(gradMeasure (cOf ν)), 0 < p.1 := ae_gradMeasure_fst_pos _
  have hCk : 0 ≤ Cg * ν⁻¹ ^ kg := mul_nonneg hCg (pow_nonneg (inv_nonneg.2 hν.le) _)
  refine ⟨
    { memLp := fun A => (bg ν ε hν hν1 hε hε1 _ (hι A)).1
      add := fun A A' => by
        filter_upwards [hpos] with p hp
        simp only [map_add, Pi.add_apply]
        exact (lg ν ε hν _ _ 1 (hι A) (hι A') p hp).1
      smul := fun r A => by
        filter_upwards [hpos] with p hp
        simp only [map_smul, Pi.smul_apply]
        exact (lg ν ε hν _ _ r (hι A) (hι A) p hp).2
      bound := ⟨Cg * ν⁻¹ ^ kg * Cenv, fun A => (bg ν ε hν hν1 hε hε1 _ (hι A)).2.trans ?_⟩ }⟩
  refine ENNReal.ofReal_le_ofReal ?_
  calc Cg * ν⁻¹ ^ kg * affM ν χf (ι A) ≤ Cg * ν⁻¹ ^ kg * (Cenv * ‖A‖) :=
        mul_le_mul_of_nonneg_left (henv A) hCk
    _ = Cg * ν⁻¹ ^ kg * Cenv * ‖A‖ := by ring

end Regime

/-- The `∇ĥ_A` part of the first line of `ret:general-affine-bounds` (source 5009-5016) for the
constructed gradient maps, uniformly for `0 < ν, ε ≤ 1`: `‖∇ĥ_A‖_{GrdG} ≤ Cν^{-k} M(A)`. -/
theorem affineGradNorm_le {as : ℝ} {χf : ℝ → ℝ} (bg : GradCoefBound as χf) :
    ∃ (C : ℝ) (k : ℕ), ∀ (ν ε : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
      ∀ {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] (ι : Aff →ₗ[ℝ] (ℝ → Mat3)),
      (∀ A, IsAffElem as (ι A)) → ∀ (h : AffineGradData as ν ε χf ι) (A : Aff),
        ‖h.gradAL A‖ ≤ C * ν⁻¹ ^ k * affM ν χf (ι A) := by
  obtain ⟨Cg, kg, hCg, bg⟩ := bg
  refine ⟨Cg, kg, ?_⟩
  intro ν ε hν hν1 hε hε1 Aff _ _ ι hι h A
  rw [AffineGradData.gradAL, IsL2Family.norm_toCLM]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg hCg (pow_nonneg (inv_nonneg.2 hν.le) _)) (affM_nonneg _ _ _))
    (bg ν ε hν hν1 hε hε1 _ (hι A)).2

end UnforcedLeray.Short.PartIIIb.Concrete
