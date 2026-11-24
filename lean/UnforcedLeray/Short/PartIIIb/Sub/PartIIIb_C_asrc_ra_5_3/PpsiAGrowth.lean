import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGSmul
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGOfS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGSnd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PGClm
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `PartIII-b:C/asrc/ra/5/3` : polynomial growth of `PpsiA` (source 4741-4745, 4978, 5076-5079)

`PpsiA = a⁻⁴ (y₁ (M_mer y)₁ + y₂ (M_mer y)₂)` with `M = A^y(s) = χ(νs) A(s)`, so
`PpsiA = Σ_{i,j ∈ {0,2}} c_{ij}(s) · y_{i'} y_{j'}`, where `c_{ij}(s) = a⁻⁴ χ(νs) A(s)_{ij}`
(the entries `A(s)_{ij}` are `C⁶` on `(0,∞)` by `IsAffElem.smooth`).  Each term is a
`PolyGrowth 1` function by the toolkit of `PartIII-b_C_asrc_ra_5_5`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The scalar coefficient `c_{ij}(s) = a⁻⁴ χ(νs) A(s)_{ij}` of `PpsiA`. -/
def ppsiAcoef (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (i j : Fin 3) (s : ℝ) : ℝ :=
  (ageA ν s ^ 4)⁻¹ * (χ (ν * s) * A s i j)

theorem ppsiAcoef_cd (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (hχ : IsSourceCutoffC χ) (hν : 0 < ν)
    (hA : ContDiffOn ℝ 6 A (Ioi 0)) (i j : Fin 3) :
    ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (ppsiAcoef ν χ A i j) (Ioi 0) := by
  have hA1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) A (Ioi 0) :=
    hA.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 6))
  have hAij : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (fun s => A s i j) (Ioi 0) :=
    contDiffOn_pi.1 (contDiffOn_pi.1 hA1 i) j
  have hle : ((1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hχs : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (fun s => χ (ν * s)) (Ioi 0) :=
    ((ContDiff.of_le (hχ.smooth.comp ((contDiff_const (c := ν)).mul contDiff_id)) hle).contDiffOn).mono
      (subset_univ _)
  have hage : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (fun s => (ageA ν s ^ 4)⁻¹) (Ioi 0) := by
    refine ContDiffOn.inv ?_ ?_
    · exact (((contDiff_const (c := (1 : ℝ))).add ((contDiff_const (c := ν)).mul contDiff_id)).pow
        4).contDiffOn
    · intro s hs
      have hpos : 0 < ageA ν s := by
        unfold ageA
        have hs' : (0 : ℝ) < s := hs
        linarith [mul_pos hν hs']
      exact pow_ne_zero _ hpos.ne'
  exact hage.mul (hχs.mul hAij)

/-- `p ↦ p.2.1` has polynomial growth of order `1`. -/
theorem ppsiA_fst_growth : PolyGrowth 1 (fun p : ℝ × (ℝ × ℝ) => p.2.1) :=
  polyGrowth_clm 1 (ContinuousLinearMap.fst ℝ ℝ ℝ) (fun p : ℝ × (ℝ × ℝ) => p.2) (polyGrowth_snd 1)

/-- `p ↦ p.2.2` has polynomial growth of order `1`. -/
theorem ppsiA_snd_growth : PolyGrowth 1 (fun p : ℝ × (ℝ × ℝ) => p.2.2) :=
  polyGrowth_clm 1 (ContinuousLinearMap.snd ℝ ℝ ℝ) (fun p : ℝ × (ℝ × ℝ) => p.2) (polyGrowth_snd 1)

/-- A product of two polynomial-growth scalar functions of `y` (`p.2.a * p.2.b` type). -/
theorem ppsiA_mul_growth (Q R : ℝ × (ℝ × ℝ) → ℝ) (hQ : PolyGrowth 1 Q) (hR : PolyGrowth 1 R) :
    PolyGrowth 1 (fun p => Q p * R p) :=
  polyGrowth_smul 1 Q R hQ hR

/-- A coefficient of class `C¹` on `(0,∞)` in `s` times a polynomial-growth function. -/
theorem ppsiA_term_growth (g : ℝ → ℝ) (Q : ℝ × (ℝ × ℝ) → ℝ)
    (hg : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) g (Ioi 0)) (hQ : PolyGrowth 1 Q) :
    PolyGrowth 1 (fun p => g p.1 * Q p) :=
  polyGrowth_smul 1 (fun p => g p.1) Q (polyGrowth_of_s 1 g hg) hQ

theorem ppsiA_growth_proof (as : ℝ) (χf : ℝ → ℝ) : PpsiA_growth as χf := by
  intro hχ ν hν A hA
  have hA6 : ContDiffOn ℝ 6 A (Ioi 0) := hA.smooth
  have key : PpsiA ν χf A = fun p : ℝ × (ℝ × ℝ) =>
      ppsiAcoef ν χf A 0 0 p.1 * (p.2.1 * p.2.1) + ppsiAcoef ν χf A 0 2 p.1 * (p.2.1 * p.2.2)
        + ppsiAcoef ν χf A 2 0 p.1 * (p.2.2 * p.2.1) + ppsiAcoef ν χf A 2 2 p.1 * (p.2.2 * p.2.2) := by
    funext p
    simp only [PpsiA, merApply, ppsiAcoef, Ay, Pi.smul_apply, smul_eq_mul]
    ring
  have hyy11 : PolyGrowth 1 (fun p : ℝ × (ℝ × ℝ) => p.2.1 * p.2.1) :=
    ppsiA_mul_growth _ _ ppsiA_fst_growth ppsiA_fst_growth
  have hyy12 : PolyGrowth 1 (fun p : ℝ × (ℝ × ℝ) => p.2.1 * p.2.2) :=
    ppsiA_mul_growth _ _ ppsiA_fst_growth ppsiA_snd_growth
  have hyy21 : PolyGrowth 1 (fun p : ℝ × (ℝ × ℝ) => p.2.2 * p.2.1) :=
    ppsiA_mul_growth _ _ ppsiA_snd_growth ppsiA_fst_growth
  have hyy22 : PolyGrowth 1 (fun p : ℝ × (ℝ × ℝ) => p.2.2 * p.2.2) :=
    ppsiA_mul_growth _ _ ppsiA_snd_growth ppsiA_snd_growth
  have t00 := ppsiA_term_growth _ _ (ppsiAcoef_cd ν χf A hχ hν hA6 0 0) hyy11
  have t02 := ppsiA_term_growth _ _ (ppsiAcoef_cd ν χf A hχ hν hA6 0 2) hyy12
  have t20 := ppsiA_term_growth _ _ (ppsiAcoef_cd ν χf A hχ hν hA6 2 0) hyy21
  have t22 := ppsiA_term_growth _ _ (ppsiAcoef_cd ν χf A hχ hν hA6 2 2) hyy22
  rw [key]
  exact (polyGrowth_add 1 _ _ (polyGrowth_add 1 _ _ (polyGrowth_add 1 _ _ t00 t02).1 t20).1 t22).1

end UnforcedLeray.Short.PartIIIb.Concrete
