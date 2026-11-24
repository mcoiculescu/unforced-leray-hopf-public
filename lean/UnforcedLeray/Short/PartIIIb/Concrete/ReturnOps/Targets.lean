import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps

/-!
# Targets of the tasks `PartIII-b:C/ret/6..11` (helpers of `Concrete/ReturnOps.lean`)

* linearity in `A` of the physical affine data (source 4985: "All these maps depend linearly on
  `A`"), at the level of `B = (A^y)' + μA^y/s` and of the lattice sums `f_A, e_A, h^p_A, ψ^p_A`
  (source 4969-4977), given summability of the lattice terms (Gaussian decay, source 4978);
* the normalization of `VelG` (source 2685-2689, 5143) and the pointwise form of `chiOStr`
  (source 4163-4166).

The lattice terms are named so that the summability hypotheses can be stated; `fA_eq` etc.
record that the fields of `Concrete/ReturnAff.lean` are the (negated) `tsum`s of these terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th lattice term of `-f_A` (source 4970). -/
def fATerm (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) : Vec3 :=
  emb (fderiv ℝ (Vj ν s j) x (merApply (Bmat ν μ χ A s) (xj ν j x)))
    + mv (Bmat ν μ χ A s) (emb (Vj ν s j x))

/-- The `j`-th lattice term of `e_A` (source 4971-4972). -/
def eATerm (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) : Vec3 :=
  (2 : ℝ) • mv (Bmat ν μ χ A s) (emb (Vj ν s j x))
    + (2 * ν) • hessContr (Ay ν χ A s) (Vj ν s j) x
    - mv (fun a b => Ay ν χ A s a b + Ay ν χ A s b a) (emb (mgrad (pj ν s j) x))

/-- The `j`-th lattice term of `h^p_A` (source 4973). -/
def hpATerm (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) : ℝ × ℝ :=
  merApply (Ay ν χ A s) (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply (Ay ν χ A s) (xj ν j x))

/-- The `j`-th lattice term of `ψ^p_A` (source 4974-4975). -/
def psipATerm (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) : ℝ :=
  merTrace (Ay ν χ A s) * psij ν s j x
    - fderiv ℝ (psij ν s j) x (merApply (Ay ν χ A s) (xj ν j x))

theorem fA_eq (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    fA ν μ χ A s x = -(∑' j : ℤ, fATerm ν μ χ A s x j) := rfl

theorem eA_eq (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    eA ν μ χ A s x = ∑' j : ℤ, eATerm ν μ χ A s x j := rfl

theorem hpA_eq (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hpA ν χ A s x = ∑' j : ℤ, hpATerm ν χ A s x j := rfl

theorem psipA_eq (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    psipA ν χ A s x = ∑' j : ℤ, psipATerm ν χ A s x j := rfl

/-- `C/ret/6`: `B = (A^y)' + μA^y/s` is linear in `A` where `A^y` is differentiable
(source 4957-4958, 4985). -/
def BmatLinear : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (r s : ℝ),
    DifferentiableAt ℝ (Ay ν χ A) s → DifferentiableAt ℝ (Ay ν χ A') s →
    Bmat ν μ χ (A + A') s = Bmat ν μ χ A s + Bmat ν μ χ A' s ∧
    Bmat ν μ χ (r • A) s = r • Bmat ν μ χ A s

/-- `C/ret/7`: `f_A` is linear in `A` (source 4970, 4985), given linearity of `B` at `s` and
summability of the lattice terms. -/
def FALinear : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (r s : ℝ) (x : ℝ × ℝ),
    Bmat ν μ χ (A + A') s = Bmat ν μ χ A s + Bmat ν μ χ A' s →
    Bmat ν μ χ (r • A) s = r • Bmat ν μ χ A s →
    Summable (fATerm ν μ χ A s x) → Summable (fATerm ν μ χ A' s x) →
    fA ν μ χ (A + A') s x = fA ν μ χ A s x + fA ν μ χ A' s x ∧
    fA ν μ χ (r • A) s x = r • fA ν μ χ A s x

/-- `C/ret/8`: `e_A` is linear in `A` (source 4971-4972, 4985). -/
def EALinear : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (r s : ℝ) (x : ℝ × ℝ),
    Bmat ν μ χ (A + A') s = Bmat ν μ χ A s + Bmat ν μ χ A' s →
    Bmat ν μ χ (r • A) s = r • Bmat ν μ χ A s →
    Summable (eATerm ν μ χ A s x) → Summable (eATerm ν μ χ A' s x) →
    eA ν μ χ (A + A') s x = eA ν μ χ A s x + eA ν μ χ A' s x ∧
    eA ν μ χ (r • A) s x = r • eA ν μ χ A s x

/-- `C/ret/9`: `h^p_A` and `ψ^p_A` are linear in `A` (source 4973-4975, 4985). -/
def HpPsiLinear : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (r s : ℝ) (x : ℝ × ℝ),
    Summable (hpATerm ν χ A s x) → Summable (hpATerm ν χ A' s x) →
    Summable (psipATerm ν χ A s x) → Summable (psipATerm ν χ A' s x) →
    (hpA ν χ (A + A') s x = hpA ν χ A s x + hpA ν χ A' s x ∧
      hpA ν χ (r • A) s x = r • hpA ν χ A s x) ∧
    (psipA ν χ (A + A') s x = psipA ν χ A s x + psipA ν χ A' s x ∧
      psipA ν χ (r • A) s x = r • psipA ν χ A s x)

/-- `C/ret/10`: the norm of `VelG` is the normalized gain body norm
`‖b‖² = π ∫ g⁻² |b|² s^{-3/2} dς` (source 2685-2689, 5143). -/
def VelGNormSq : Prop :=
  ∀ (c γ ν : ℝ) (b : VelG c γ ν),
    ‖b‖ ^ 2 = Real.pi * ∫ p, ginv γ ν p ^ 2 * ‖(b : Chart → Merid) p‖ ^ 2 ∂(ageμ c (-3 / 2))

/-- `C/ret/11`: `χ_o` acts on both stress components by pointwise multiplication with
`χ̂_o(νs)` (source 4163-4166). -/
def ChiOStrApply : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (χ : ℝ → ℝ) (hχ : IsOutwardCutoff χ) (T : StrG c mZ ρb γ ν),
    (((chiOStr c mZ ρb γ ν hχ T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      fun p => cutFun χ ν p • (T.fst : Chart → Ten3) p) ∧
    (((chiOStr c mZ ρb γ ν hχ T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      fun p => cutFun χ ν p • (T.snd : Chart → Ten3) p)

end UnforcedLeray.Short.PartIIIb.Concrete
