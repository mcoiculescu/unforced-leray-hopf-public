import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Concrete physical affine data (source lines 4733-4760, 4951-5110)

* The weighted space `𝒜` of `C^6` trace-free matrix functions (4741-4752): carrier predicate
  `IsAffElem` and norm functional `affNorm` (the Banach-space instance is task `C/ret/1`).
* The physical affine lifting data of `return/physical-affine` (4951-5010): cutoff `χ_f`,
  `A^y = χ_f A`, `B = (A^y)' + μ A^y/s`, the Gaussians `V_j, p_j, ψ_j`, and the fields
  `f_A, e_A, h^p_A, ψ^p_A, ĥ_A, F_A, E_A`.

Conventions. Matrices are `Fin 3 → Fin 3 → ℝ` in the component order `(r, φ, z)` = `(0,1,2)`;
`|A|` is the Frobenius norm.  Meridional vectors are `ℝ × ℝ` with coordinates `(q, η)`, and the
meridional block of a matrix is the `(r,z)` block.  A meridional vector `(v₁, v₂)` is embedded
in `(r, φ, z)`-space as `(v₁, 0, v₂)`.  Lattice sums over `j ∈ ℤ` are `tsum`s (they converge by
Gaussian decay, line 4991; summability is a separate task).
-/

set_option autoImplicit false

noncomputable section

open Set Real
open scoped BigOperators

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `3×3` matrices in the order `(r, φ, z)`. -/
abbrev Mat3 := Fin 3 → Fin 3 → ℝ

/-- Vectors in the order `(r, φ, z)`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Frobenius norm `|A|`. -/
def frob (A : Mat3) : ℝ := Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- Matrix-vector product. -/
def mv (A : Mat3) (v : Vec3) : Vec3 := fun i => ∑ j, A i j * v j

/-- Transpose. -/
def tr3 (A : Mat3) : Mat3 := fun i j => A j i

/-! ## The weighted space `𝒜` (lines 4741-4752) -/

/-- `s ∂_s` on matrix functions. -/
def sDeriv (A : ℝ → Mat3) : ℝ → Mat3 := fun s => s • deriv A s

/-- `(s ∂_s)^j`. -/
def sDerivIter : ℕ → (ℝ → Mat3) → ℝ → Mat3
  | 0, A => A
  | j + 1, A => sDeriv (sDerivIter j A)

/-- `Σ_{j=0}^k |(s∂_s)^j A(s)|`. -/
def affSum (k : ℕ) (A : ℝ → Mat3) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), frob (sDerivIter j A s)

/-- The weighted integrand `e^{-a_s s} s^{-5/2} Σ_{j≤k}|(s∂_s)^j A(s)|`. -/
def affTerm (as : ℝ) (k : ℕ) (A : ℝ → Mat3) (s : ℝ) : ℝ :=
  Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * affSum k A s

/-- The norm `‖A‖_𝒜 = sup_{s>0} e^{-a_s s} s^{-5/2} Σ_{j≤6} |(s∂_s)^j A(s)|` (line 4750). -/
def affNorm (as : ℝ) (A : ℝ → Mat3) : ℝ := sSup (affTerm as 6 A '' Ioi 0)

/-- Membership in `𝒜` (lines 4741-4745): `C^6` on `(0,∞)`, trace free, no entry with exactly one
azimuthal index (`φ = 1`), finite norm; extended by zero to `s ≤ 0`. -/
structure IsAffElem (as : ℝ) (A : ℝ → Mat3) : Prop where
  smooth : ContDiffOn ℝ 6 A (Ioi 0)
  traceFree : ∀ s, 0 < s → A s 0 0 + A s 1 1 + A s 2 2 = 0
  noMixedAzimuth : ∀ s, 0 < s →
    A s 0 1 = 0 ∧ A s 1 0 = 0 ∧ A s 1 2 = 0 ∧ A s 2 1 = 0
  zeroOff : ∀ s, s ≤ 0 → A s = 0
  bdd : BddAbove (affTerm as 6 A '' Ioi 0)

/-! ## Cutoff and the matrices `A^y`, `B` (lines 4953-4960, 4750-4760) -/

/-- The source cutoff profile `χ̂_f`: smooth, `1` on `t ≤ 1`, `0` on `t ≥ 1.1`, values in `[0,1]`
(so `χ_f(s) = χ̂_f(νs)`, lines 4750-4752 and 4953-4955).  The smoothness index is `C^∞`,
`((⊤ : ℕ∞) : WithTop ℕ∞)`, not the analytic `ω = ⊤ : WithTop ℕ∞` (an analytic cutoff equal to
one on `t ≤ 1` would be identically one).  Satisfiable: `isSourceCutoff_std`. -/
structure IsSourceCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  one : ∀ t, t ≤ 1 → χ t = 1
  zero : ∀ t, 11 / 10 ≤ t → χ t = 0
  range : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1

/-- A standard source cutoff profile, `t ↦ smoothTransition (11 - 10 t)`. -/
def sourceCutoffStd (t : ℝ) : ℝ := Real.smoothTransition (11 - 10 * t)

/-- `IsSourceCutoff` is satisfiable. -/
theorem isSourceCutoff_std : IsSourceCutoff sourceCutoffStd where
  smooth := Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id))
  one t ht := Real.smoothTransition.one_of_one_le (by linarith)
  zero t ht := Real.smoothTransition.zero_of_nonpos (by linarith)
  range t := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- `A^y = χ_f A`. -/
def Ay (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → Mat3 := fun s => χ (ν * s) • A s

/-- `B = (A^y)' + μ A^y / s` (lines 4957-4958; the cutoff derivative is included). -/
def Bmat (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → Mat3 :=
  fun s => deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s

/-! ## Meridional algebra -/

/-- Meridional index `0 ↦ r`, `1 ↦ z`. -/
def mi : Fin 2 → Fin 3 := ![0, 2]

/-- Meridional basis `e_0 = (1,0)`, `e_1 = (0,1)` in `(q, η)`. -/
def ei : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- Embedding `(v₁, v₂) ↦ (v₁, 0, v₂)`. -/
def emb (v : ℝ × ℝ) : Vec3 := ![v.1, 0, v.2]

/-- Meridional block applied to a meridional vector: `A_mer x`. -/
def merApply (A : Mat3) (x : ℝ × ℝ) : ℝ × ℝ :=
  (A 0 0 * x.1 + A 0 2 * x.2, A 2 0 * x.1 + A 2 2 * x.2)

/-- `tr A_mer = A_rr + A_zz`. -/
def merTrace (A : Mat3) : ℝ := A 0 0 + A 2 2

/-- `J(q, η) = (-η, q)`. -/
def Jrot (x : ℝ × ℝ) : ℝ × ℝ := (-x.2, x.1)

/-! ## The Gaussians `V_j, p_j, ψ_j` (lines 4963-4968) -/

/-- `c = ν⁻²`. -/
def cOf (ν : ℝ) : ℝ := (ν ^ 2)⁻¹

/-- `a = 1 + νs`. -/
def ageA (ν s : ℝ) : ℝ := 1 + ν * s

/-- `x_j = (q - jc, η)`. -/
def xj (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 - j * cOf ν, x.2)

/-- `|x|²`. -/
def sq2 (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- `V_j = a⁻² e^{-|x_j|²/(4a)} J x_j`. -/
def Vj (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) • Jrot (xj ν j x)

/-- `p_j = -a⁻³ e^{-|x_j|²/(2a)}`. -/
def pj (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ :=
  -((ageA ν s ^ 3)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)))

/-- `ψ_j = -2 a⁻¹ e^{-|x_j|²/(4a)}`. -/
def psij (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ :=
  -2 * (ageA ν s)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))

/-! ## The fields (lines 4969-4985) -/

/-- Meridional gradient of a scalar: `(∂_q f, ∂_η f)`. -/
def mgrad (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ f x (ei 0), fderiv ℝ f x (ei 1))

/-- `f_A = -Σ_j [(B_mer x_j)·∇V_j + B V_j]`, evaluated at `(s, x)` (the matrix `B` at `s`). -/
def fA (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : Vec3 :=
  -(∑' j : ℤ,
    (emb (fderiv ℝ (Vj ν s j) x (merApply (Bmat ν μ χ A s) (xj ν j x)))
      + mv (Bmat ν μ χ A s) (emb (Vj ν s j x))))

/-- The contraction `(A : D²V)_i = Σ_{a,b meridional} A_{ab} ∂_a ∂_b V_i`, embedded. -/
def hessContr (A : Mat3) (V : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : Vec3 :=
  emb (∑ a : Fin 2, ∑ b : Fin 2,
    A (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a))

/-- `e_A = Σ_j [2 B V_j + 2ν A^y : D²V_j - (A^y + (A^y)ᵀ) ∇p_j]`. -/
def eA (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : Vec3 :=
  ∑' j : ℤ,
    ((2 : ℝ) • mv (Bmat ν μ χ A s) (emb (Vj ν s j x))
      + (2 * ν) • hessContr (Ay ν χ A s) (Vj ν s j) x
      - mv (fun a b => Ay ν χ A s a b + Ay ν χ A s b a) (emb (mgrad (pj ν s j) x)))

/-- `h^p_A = Σ_j [V_j, A^y_mer x_j]` with `[V, W] = DW·V - DV·W` and `W = A_mer x_j`
(so `DW = A_mer`). -/
def hpA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑' j : ℤ,
    (merApply (Ay ν χ A s) (Vj ν s j x)
      - fderiv ℝ (Vj ν s j) x (merApply (Ay ν χ A s) (xj ν j x)))

/-- `ψ^p_A = Σ_j [(tr A^y_mer) ψ_j - (A^y_mer x_j)·∇ψ_j]`. -/
def psipA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' j : ℤ,
    (merTrace (Ay ν χ A s) * psij ν s j x
      - fderiv ℝ (psij ν s j) x (merApply (Ay ν χ A s) (xj ν j x)))

/-- `𝒦 ψ = η ∂_η ψ + 2 s ∂_s ψ` for a function `ψ(s, q, η)`. -/
def Kop (ψ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  x.2 * fderiv ℝ (ψ s) x (ei 1) + 2 * s * deriv (fun s' => ψ s' x) s

/-- `ĥ_A = √s [(h^p_A)_r e_r + ((h^p_A)_z + ε(1 - 𝒦)ψ^p_A) e_z]` (line 4980). -/
def hhatA (ν ε : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : Vec3 :=
  Real.sqrt s • emb ((hpA ν χ A s x).1,
    (hpA ν χ A s x).2 + ε * (psipA ν χ A s x - Kop (fun s' y => psipA ν χ A s' y) s x))

/-- `F_A = s^{3/2} f_A`. -/
def FA (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : Vec3 :=
  s ^ (3 / 2 : ℝ) • fA ν μ χ A s x

/-- `E_A = s^{3/2} e_A`. -/
def EA (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : Vec3 :=
  s ^ (3 / 2 : ℝ) • eA ν μ χ A s x

/-! ## Statements about these fields (source 4994-5010) -/

/-- `A^y_mer J = J[(tr A^y_mer) I - (A^y_mer)ᵀ]` (line 4993), for the meridional block of any
`A`; hence `h^p_A = J ∇ψ^p_A` pointwise termwise. -/
def MerJIdentity (A : Mat3) : Prop :=
  ∀ x : ℝ × ℝ, merApply A (Jrot x) =
    Jrot (merTrace A * x.1 - (A 0 0 * x.1 + A 2 0 * x.2),
          merTrace A * x.2 - (A 0 2 * x.1 + A 2 2 * x.2))

/-- Lattice sums converge: the Gaussian family `j ↦ V_j(x)` etc. is summable
(line 4991, "Gaussian decay"), for every derivative used. -/
def PhysAffineSummable (ν : ℝ) (s : ℝ) : Prop :=
  ∀ x : ℝ × ℝ, Summable (fun j : ℤ => ‖Vj ν s j x‖) ∧ Summable (fun j : ℤ => ‖pj ν s j x‖) ∧
    Summable (fun j : ℤ => ‖psij ν s j x‖)

/-- `h^p_A = J ∇ψ^p_A` (line 4994), for `A` with the symmetry/trace data of `𝒜`; the source has
`ν > 0` (`c = ν⁻²`, `a = 1 + νs`, lines 4963-4994), so the statement carries `0 < ν`. -/
def HpIsJGrad (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : Prop :=
  0 < ν ∧ ∀ s, 0 < s → ∀ x : ℝ × ℝ, hpA ν χ A s x = Jrot (mgrad (psipA ν χ A s) x)

example : MerJIdentity (fun _ _ => 0) := by
  intro x; simp [merApply, merTrace, Jrot]

end UnforcedLeray.Short.PartIIIb.Concrete
