import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PerGen
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.GaussBound

/-!
# `PartIII-b:C/asrc/ra/5/5` : `h^p_A` is `C²` on `s > 0` (source 4973, 4978, 5076-5079)

Decomposition.  `hpA ν χ A s x = ∑' j, G(s, x_j)` with a summand
`G = exp(-|y|²/(4a)) • P`, `P` a polynomial in `y` with coefficients `C²` in `s`
(`a⁻²`, `a⁻¹`, entries of `A^y(s)`).  The Gaussian lattice-sum smoothness
`contDiffOn_tsum_shift` (task /1) needs `ContDiffOn` and the `hbd` bound for `G`;
`GaussMulHbd` (generic: Leibniz + `gauss_iterated_bound`) turns polynomial growth of
`P` into both, and `PolyGrowth` of `P` is a Leibniz computation on explicit entries.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `P` is `C^n` on `s > 0` with all derivatives of order `≤ n` of polynomial growth in `x`,
uniformly for `s` in compact subsets of `(0,∞)`. -/
def PolyGrowth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (P : ℝ × (ℝ × ℝ) → E) : Prop :=
  ContDiffOn ℝ (n : WithTop ℕ∞) P (Ioi (0 : ℝ) ×ˢ univ) ∧
    ∀ s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ m : ℕ, m ≤ n →
      ∀ s ∈ Icc s0 s1, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ m P (s, x)‖ ≤ C * (1 + sq2 x) ^ N

/-- **Generic Gaussian times polynomial growth** (Leibniz for
`norm_iteratedFDerivWithin_smul_le` on the open set `Ioi 0 ×ˢ univ`, `gauss_iterated_bound`,
and absorption `(1+q²+η²)^N e^{-(q²+η²)/b} ≤ C e^{-q²/(2b)}` for `|η| ≤ R`). -/
def GaussMulHbd (n : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ), 0 < κ → 0 < ν →
    ∀ P : ℝ × (ℝ × ℝ) → E, PolyGrowth n P →
      ContDiffOn ℝ (n : WithTop ℕ∞)
        (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)) • P p)
        (Ioi (0 : ℝ) ×ˢ univ) ∧
      ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K → ∀ L : Set ℝ, IsCompact L →
        ∃ C a : ℝ, 0 < a ∧ ∀ m : ℕ, m ≤ n → ∀ s ∈ K, ∀ q : ℝ, ∀ η ∈ L,
          ‖iteratedFDeriv ℝ m
              (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)) • P p)
              (s, (q, η))‖ ≤ C * Real.exp (-a * q ^ 2)

/-- The `j = 0` summand of `hpA`, at `y = x_j`:
`G(s,y) = A^y_mer V_0(s,y) - DV_0(s,y)[A^y_mer y]`. -/
def GhpA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  merApply (Ay ν χ A p.1) (Vj ν p.1 0 p.2) -
    fderiv ℝ (Vj ν p.1 0) p.2 (merApply (Ay ν χ A p.1) p.2)

/-- Polynomial prefactor of `GhpA`, with `a = ageA ν s`, `M = A^y(s)`, `v = M_mer y`:
`a⁻² (M_mer (J y) - (-(⟨y,v⟩/(2a)) • J y + J v))`. -/
def PhpA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  ((ageA ν p.1 ^ 2)⁻¹) •
    (merApply (Ay ν χ A p.1) (Jrot p.2) -
      ((-((p.2.1 * (merApply (Ay ν χ A p.1) p.2).1 + p.2.2 * (merApply (Ay ν χ A p.1) p.2).2)
          / (2 * ageA ν p.1))) • Jrot p.2 + Jrot (merApply (Ay ν χ A p.1) p.2)))

/-- (N3) the lattice-sum form of `hpA` (translation: `V_j(s,x) = V_0(s,x_j)`,
`DV_j(s)(x) = DV_0(s)(x_j)`). -/
def HpASum : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3),
    (fun p : ℝ × (ℝ × ℝ) => hpA ν χ A p.1 p.2) =
      fun p => ∑' j : ℤ, GhpA ν χ A (p.1, (p.2.1 - j * cOf ν, p.2.2))

/-- (N-fd) the explicit form of the summand: `V_0 = a⁻² e^{-|y|²/(4a)} J y`, so
`GhpA = e^{-|y|²/(4a)} • PhpA` (derivative of the Gaussian in `y`). -/
def GhpA_eq : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (p : ℝ × (ℝ × ℝ)),
    GhpA ν χ A p = Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) • PhpA ν χ A p

/-- (N1) polynomial growth of `PhpA` (entries of `A^y = χ(νs) A(s)` are `C⁶` on `s > 0`,
source 4741-4745, 4978; `a⁻¹, a⁻²` smooth; the rest is polynomial in `y`). -/
def PhpA_growth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    PolyGrowth 2 (PhpA ν χf A)

theorem hpAC2_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpASum) (h2 : GhpA_eq) (h3 : PhpA_growth as χf)
    (h4 : GaussMulHbd 2) : HpAC2 as χf := by
  intro hχ ν hν A hA
  have hG : GhpA ν χf A = fun p : ℝ × (ℝ × ℝ) =>
      Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) • PhpA ν χf A p := funext (h2 ν χf A)
  obtain ⟨hcd, hbd⟩ := h4 (ℝ × ℝ) 4 ν (by norm_num) hν _ (h3 hχ ν hν A hA)
  rw [← hG] at hcd hbd
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have := contDiffOn_tsum_shift 2 (cOf ν) hc (Ioi (0 : ℝ)) isOpen_Ioi (GhpA ν χf A) hcd hbd
  rw [h1 ν χf A]
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete
