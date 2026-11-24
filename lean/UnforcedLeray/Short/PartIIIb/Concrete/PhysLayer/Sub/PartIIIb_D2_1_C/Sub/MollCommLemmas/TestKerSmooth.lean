import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `TestKerSmooth`: the test kernel is smooth with compact support

Source `the November 2 reference manuscript` (the adjoint graph at `r = 2` and the
mollified commutator); the definitions are those of `MollCommDefs`. With `κ = ρ.normed volume`
(smooth, compactly supported by Mathlib), `testKer ν μ ρ x` is a combination of `κ`, `∂_τ κ`,
`v·∇κ` at the vector `(0, x.2 - z.2)` (smooth in `z`), and `Δκ`. Each term vanishes outside
`tsupport κ`, so the support is compact.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem testKerSmooth : TestKerSmooth := by
  intro ν μ ρ x
  have hsm : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hcs : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  unfold testKer
  simp only [kerDτ, kerDv, kerLap]
  generalize ρ.normed volume = κ at hsm hcs ⊢
  have hF : ContDiff ℝ ∞ (fderiv ℝ κ) := (contDiff_infty_iff_fderiv.mp hsm).2
  have hg : ∀ v : Space, ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ κ z ((0 : ℝ), v)) :=
    fun v => hF.clm_apply contDiff_const
  have hgd : ∀ v : Space, ContDiff ℝ ∞ (fun z : ℝ × Space =>
      fderiv ℝ (fun z' : ℝ × Space => fderiv ℝ κ z' ((0 : ℝ), v)) z ((0 : ℝ), v)) :=
    fun v => ((contDiff_infty_iff_fderiv.mp (hg v)).2).clm_apply contDiff_const
  constructor
  · have h2 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ κ z ((1 : ℝ), (0 : Space))) :=
      hF.clm_apply contDiff_const
    have h3 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ κ z ((0 : ℝ), x.2 - z.2)) :=
      hF.clm_apply (contDiff_const.prodMk (contDiff_const.sub contDiff_snd))
    have h4 : ContDiff ℝ ∞ (fun z : ℝ × Space => ∑ j : Fin 3,
        fderiv ℝ (fun z' : ℝ × Space => fderiv ℝ κ z' ((0 : ℝ), coordinateVector j)) z
          ((0 : ℝ), coordinateVector j)) :=
      ContDiff.sum (fun j _ => hgd (coordinateVector j))
    exact (((contDiff_const.mul hsm).sub h2).add (contDiff_const.mul h3)).sub
      (contDiff_const.mul h4)
  · refine HasCompactSupport.intro hcs.isCompact ?_
    intro z hz
    have hκz : κ z = 0 := by
      have := notMem_tsupport_iff_eventuallyEq.mp hz
      simpa using this.self_of_nhds
    have hf : fderiv ℝ κ z = 0 := fderiv_of_notMem_tsupport ℝ hz
    have hL : ∀ v : Space, fderiv ℝ (fun z' : ℝ × Space => fderiv ℝ κ z' ((0 : ℝ), v)) z
        ((0 : ℝ), v) = 0 := by
      intro v
      have hz1 : z ∉ tsupport (fun z' : ℝ × Space => fderiv ℝ κ z' ((0 : ℝ), v)) :=
        fun h => hz (tsupport_fderiv_apply_subset ℝ ((0 : ℝ), v) h)
      rw [fderiv_of_notMem_tsupport ℝ hz1]
      simp
    simp [hκz, hf, hL]

end UnforcedLeray.Short.PartIIIb.Concrete
