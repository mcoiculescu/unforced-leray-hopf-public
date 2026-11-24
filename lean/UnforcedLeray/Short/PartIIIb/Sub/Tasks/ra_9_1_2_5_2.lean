import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem vjPsijContDiff (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContDiffOn ℝ 5 (fun p : Chart => Vj ν p.1 j p.2) (Ioi 0 ×ˢ univ) ∧
    ContDiffOn ℝ 5 (fun p : Chart => psij ν p.1 j p.2) (Ioi 0 ×ˢ univ) := by
  have hS : ∀ p ∈ (Ioi (0:ℝ) ×ˢ univ : Set Chart), 0 < p.1 := fun p hp => hp.1
  have hA : ContDiffOn ℝ 5 (fun p : Chart => ageA ν p.1) (Ioi 0 ×ˢ univ) := by
    unfold ageA
    exact (contDiff_const.add (contDiff_const.mul contDiff_fst)).contDiffOn
  have hApos : ∀ p ∈ (Ioi (0:ℝ) ×ˢ univ : Set Chart), 0 < ageA ν p.1 := by
    intro p hp
    have := mul_pos hν (hS p hp)
    unfold ageA
    linarith
  have hSq : ContDiff ℝ 5 (fun p : Chart => sq2 (xj ν j p.2)) := by
    unfold sq2 xj
    fun_prop
  have hE : ContDiffOn ℝ 5 (fun p : Chart => -(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))
      (Ioi 0 ×ˢ univ) :=
    ContDiffOn.div hSq.neg.contDiffOn (contDiffOn_const.mul hA)
      (fun p hp => mul_ne_zero (by norm_num) (hApos p hp).ne')
  have hexp : ContDiffOn ℝ 5 (fun p : Chart => Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)))
      (Ioi 0 ×ˢ univ) :=
    Real.contDiff_exp.comp_contDiffOn hE
  have hinv : ContDiffOn ℝ 5 (fun p : Chart => (ageA ν p.1)⁻¹) (Ioi 0 ×ˢ univ) :=
    hA.inv (fun p hp => (hApos p hp).ne')
  have hpow : ContDiffOn ℝ 5 (fun p : Chart => (ageA ν p.1 ^ 2)⁻¹) (Ioi 0 ×ˢ univ) :=
    (hA.pow 2).inv (fun p hp => pow_ne_zero 2 (hApos p hp).ne')
  have hJ : ContDiffOn ℝ 5 (fun p : Chart => Jrot (xj ν j p.2)) (Ioi 0 ×ˢ univ) := by
    have h : ContDiff ℝ 5 (fun p : Chart => Jrot (xj ν j p.2)) := by
      unfold Jrot xj
      fun_prop
    exact h.contDiffOn
  constructor
  · exact (hpow.mul hexp).smul hJ
  · exact ((contDiffOn_const.mul hinv).mul hexp)

end UnforcedLeray.Short.PartIIIb.Concrete
