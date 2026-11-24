import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatAPeriodic

/-!
# `c`-periodicity of the `F_A + E_A` coefficient in `q` (source 4963-4975)

The lattice terms of `f_A` and `e_A` depend on `q` only through `x_j = (q - jc, η)`, so the shift
`q ↦ q + nc` reindexes the `ℤ`-sums (`hper_tsum_shift`), and the derivatives commute with the
translation (`hper_fderiv_shift`). The prefactors `s^{3/2}`, `(√s)⁻¹` do not depend on `q`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fe_fderiv_Vj (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) (y.1 + (n : ℝ) * cOf ν, y.2) = fderiv ℝ (Vj ν s (j - n)) y :=
  hper_fderiv_shift (Vj ν s j) (Vj ν s (j - n)) ((n : ℝ) * cOf ν) (hper_Vj_shift ν s n j) y

theorem fe_pj_shift (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    pj ν s j (y.1 + (n : ℝ) * cOf ν, y.2) = pj ν s (j - n) y := by
  unfold pj
  rw [hper_xj_shift]

theorem fe_fderiv_pj (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    fderiv ℝ (pj ν s j) (y.1 + (n : ℝ) * cOf ν, y.2) = fderiv ℝ (pj ν s (j - n)) y :=
  hper_fderiv_shift (pj ν s j) (pj ν s (j - n)) ((n : ℝ) * cOf ν) (fe_pj_shift ν s n j) y

theorem fe_mgrad (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    mgrad (pj ν s j) (y.1 + (n : ℝ) * cOf ν, y.2) = mgrad (pj ν s (j - n)) y := by
  unfold mgrad
  rw [fe_fderiv_pj]

theorem fe_hess (ν s : ℝ) (A : Mat3) (n j : ℤ) (x : ℝ × ℝ) :
    hessContr A (Vj ν s j) (x.1 + (n : ℝ) * cOf ν, x.2) = hessContr A (Vj ν s (j - n)) x := by
  unfold hessContr
  congr 1
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have h : ∀ y : ℝ × ℝ,
      (fun y => fderiv ℝ (Vj ν s j) y (ei b)) (y.1 + (n : ℝ) * cOf ν, y.2)
        = (fun y => fderiv ℝ (Vj ν s (j - n)) y (ei b)) y := by
    intro y
    dsimp only
    rw [fe_fderiv_Vj]
  rw [hper_fderiv_shift (fun y => fderiv ℝ (Vj ν s j) y (ei b))
    (fun y => fderiv ℝ (Vj ν s (j - n)) y (ei b)) ((n : ℝ) * cOf ν) h x]

theorem fe_fA (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    fA ν μ χ A s (x.1 + (n : ℝ) * cOf ν, x.2) = fA ν μ χ A s x := by
  unfold fA
  congr 1
  refine hper_tsum_shift ((n : ℝ) * cOf ν) n
    (fun j y => emb (fderiv ℝ (Vj ν s j) y (merApply (Bmat ν μ χ A s) (xj ν j y)))
      + mv (Bmat ν μ χ A s) (emb (Vj ν s j y))) ?_ x
  intro j y
  rw [hper_xj_shift, fe_fderiv_Vj, hper_Vj_shift]

theorem fe_eA (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    eA ν μ χ A s (x.1 + (n : ℝ) * cOf ν, x.2) = eA ν μ χ A s x := by
  unfold eA
  refine hper_tsum_shift ((n : ℝ) * cOf ν) n
    (fun j y => (2 : ℝ) • mv (Bmat ν μ χ A s) (emb (Vj ν s j y))
      + (2 * ν) • hessContr (Ay ν χ A s) (Vj ν s j) y
      - mv (fun a b => Ay ν χ A s a b + Ay ν χ A s b a) (emb (mgrad (pj ν s j) y))) ?_ x
  intro j y
  rw [hper_Vj_shift, fe_hess, fe_mgrad]

theorem fe_FAcoef (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    FAcoef ν μ χ A (s, (x.1 + (n : ℝ) * cOf ν, x.2)) = FAcoef ν μ χ A (s, x) := by
  simp only [FAcoef, FA]
  rw [fe_fA]

theorem fe_EAcoef (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ) (x : ℝ × ℝ) :
    EAcoef ν μ χ A (s, (x.1 + (n : ℝ) * cOf ν, x.2)) = EAcoef ν μ χ A (s, x) := by
  simp only [EAcoef, EA]
  rw [fe_eA]

theorem affFEPer (as : ℝ) (χf : ℝ → ℝ) : AffFEPer as χf := by
  intro _ ν μ _ A _ s η _ ξ
  have h1 := fe_FAcoef ν μ χf A s 1 (ξ, η)
  have h2 := fe_EAcoef ν μ χf A s 1 (ξ, η)
  simp only [Int.cast_one, one_mul] at h1 h2
  show (FAcoef ν μ χf A + EAcoef ν μ χf A) (s, (ξ + cOf ν, η))
      = (FAcoef ν μ χf A + EAcoef ν μ χf A) (s, (ξ, η))
  rw [Pi.add_apply, Pi.add_apply, h1, h2]

end UnforcedLeray.Short.PartIIIb.Concrete
