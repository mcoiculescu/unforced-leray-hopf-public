import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadDtReg

lemma isOpen_strip (t s : ℝ) : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioo.prod isOpen_univ

variable {t s : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}

lemma contDiffOn_strip
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ioo t s ×ˢ univ) :=
  hj.mono (prod_mono Ioo_subset_Ico_self (subset_refl _))

lemma ladDt_eq_fderiv
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) :
    ladDt ψ ρ x = fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) := by
  rw [ladDt_eq_fderivWithin hj hρ x,
    fderivWithin_of_mem_nhds (prod_mem_nhds (Ico_mem_nhds hρ.1 hρ.2) univ_mem)]

/-- The strip derivative is smooth: `ψ` is smooth on the open strip, so is its slice gradient. -/
lemma contDiff_ladDt_of
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t s) : ContDiff ℝ ∞ (ladDt ψ ρ) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (Ioo t s ×ˢ univ) :=
    (contDiffOn_strip hj).fderiv_of_isOpen (isOpen_strip t s) (by simp)
  have hcomp : ContDiff ℝ ∞ (fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have h1 : ContDiffAt ℝ ∞ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (ρ, x) :=
      hD.contDiffAt ((isOpen_strip t s).mem_nhds ⟨hρ, mem_univ x⟩)
    exact h1.comp x (contDiff_const.prodMk contDiff_id).contDiffAt
  have e : ladDt ψ ρ = fun x : ℝ × ℝ =>
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun x => ladDt_eq_fderiv hj hρ x
  rw [e]
  exact hcomp.clm_apply contDiff_const

end LadDtReg

open LadDtReg in
theorem ladDtRegular : UnforcedLeray.Short.IIIa.LadDtRegular := by
  intro c t s ψ hj hper ρ hρ
  refine ⟨contDiff_ladDt_of hj hρ, fun x => ?_⟩
  show derivWithin (fun r => ψ r (x.1 + c, x.2)) (Set.Ici ρ) ρ = derivWithin (fun r => ψ r x) (Set.Ici ρ) ρ
  apply Filter.EventuallyEq.derivWithin_eq
  · filter_upwards [nhdsWithin_le_nhds (Ico_mem_nhds hρ.1 hρ.2)] with r hr
    exact hper r hr x
  · exact hper ρ ⟨hρ.1.le, hρ.2⟩ x

end UnforcedLeray.Short.IIIa
