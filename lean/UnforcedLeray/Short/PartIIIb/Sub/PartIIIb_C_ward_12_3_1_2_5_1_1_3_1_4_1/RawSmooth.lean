import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.RawCalc

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1`: `RawProfSmoothGen`

Source `the November 2 reference manuscript` 1206-1222 (`b_raw = (v₁, v₂ + εH)`,
`H = (1-K)ψ`, `K = η∂_η + 2s∂_s`).  Generic calculus: the one-variable derivatives of `ψ` are
partial `fderiv`s of the jointly smooth `ψ` (helpers in `RawCalc.lean`), so `rawProfile` is
`v + (ε R) • e₁` with `R` built from `ψ`, `η`, `s` and `fderiv`s of `ψ`, which is `C^∞` on `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rawProfSmoothGen : RawProfSmoothGen := by
  intro ε v ψ hv hψ
  have hU := isOpen_ageSet
  have hψU : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hψ.mono (fun m hm => ⟨show (0 : ℝ) < m.1 from hm, mem_univ _⟩)
  have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hv.mono (fun m hm => ⟨le_of_lt (show (0 : ℝ) < m.1 from hm), mem_univ _⟩)
  have hG : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    fderiv_dir_contDiffOn hU hψU _
  have hS : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0)))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    fderiv_dir_contDiffOn hU hψU _
  have hη : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.2.2) := by fun_prop
  have ht : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.1) := by fun_prop
  have hR : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x -
        (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hψU.sub ((hη.contDiffOn.mul hG).add ((contDiffOn_const.mul ht.contDiffOn).mul hS))
  have hfin : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2 + (ε *
        ((fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x -
          (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
            2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hvU.add ((contDiffOn_const.mul hR).smul contDiffOn_const)
  exact hfin.congr (fun m hm => rawProfile_eq_fderiv ε v ψ hψU hm)

end UnforcedLeray.Short.PartIIIb.Concrete
