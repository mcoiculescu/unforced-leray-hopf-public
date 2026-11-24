import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5

/-!
# `PartIII-b:C/asrc/ra/5/3` : `s Ψ_A` is `C¹` on `s > 0` (source 5024, 5040-5043, 4978)

Same scheme as `PartIII-b_C_asrc_ra_5_5`: `PsiA ν χ A s x = ∑' j, GpsiA(s, x_j)` with
`GpsiA = e^{-|y|²/(2a)} • PpsiA` (`p_0 = -a⁻³ e^{-|y|²/(2a)}`, `∇p_0 = a⁻⁴ e^{-|y|²/(2a)} y`),
`PpsiA = a⁻⁴ ⟨A^y_mer y, y⟩`, and `GaussMulHbd 1` (from `PartIII-b_C_asrc_ra_5_5`, κ = 2).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j = 0` summand of `PsiA` at `y = x_j`. -/
def GpsiA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  (merApply (Ay ν χ A p.1) p.2).1 * (mgrad (pj ν p.1 0) p.2).1 +
    (merApply (Ay ν χ A p.1) p.2).2 * (mgrad (pj ν p.1 0) p.2).2

/-- `a⁻⁴ ⟨A^y_mer y, y⟩`. -/
def PpsiA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  (ageA ν p.1 ^ 4)⁻¹ *
    (p.2.1 * (merApply (Ay ν χ A p.1) p.2).1 + p.2.2 * (merApply (Ay ν χ A p.1) p.2).2)

/-- (N3) lattice-sum form of `PsiA` (`p_j(s,x) = p_0(s,x_j)`, `∇p_j(x) = ∇p_0(x_j)`). -/
def PsiASum : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3),
    (fun p : ℝ × (ℝ × ℝ) => PsiA ν χ A p.1 p.2) =
      fun p => ∑' j : ℤ, GpsiA ν χ A (p.1, (p.2.1 - j * cOf ν, p.2.2))

/-- (N-fd) `GpsiA = e^{-|y|²/(2a)} • PpsiA`. -/
def GpsiA_eq : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (p : ℝ × (ℝ × ℝ)),
    GpsiA ν χ A p = Real.exp (-(sq2 p.2) / (2 * ageA ν p.1)) • PpsiA ν χ A p

/-- (N1) polynomial growth of `PpsiA` (entries of `A^y` are `C⁶` on `s > 0`). -/
def PpsiA_growth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    PolyGrowth 1 (PpsiA ν χf A)

theorem affPsiC1_of (as : ℝ) (χf : ℝ → ℝ) (h1 : PsiASum) (h2 : GpsiA_eq)
    (h3 : PpsiA_growth as χf) (h4 : GaussMulHbd 1) : AffPsiC1 as χf := by
  intro hχ ν hν A hA
  have hG : GpsiA ν χf A = fun p : ℝ × (ℝ × ℝ) =>
      Real.exp (-(sq2 p.2) / (2 * ageA ν p.1)) • PpsiA ν χf A p := funext (h2 ν χf A)
  obtain ⟨hcd, hbd⟩ := h4 ℝ 2 ν (by norm_num) hν _ (h3 hχ ν hν A hA)
  rw [← hG] at hcd hbd
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hsum := contDiffOn_tsum_shift 1 (cOf ν) hc (Ioi (0 : ℝ)) isOpen_Ioi (GpsiA ν χf A) hcd hbd
  rw [← h1 ν χf A] at hsum
  exact (contDiffOn_fst (n := 1)).mul hsum

end UnforcedLeray.Short.PartIIIb.Concrete
