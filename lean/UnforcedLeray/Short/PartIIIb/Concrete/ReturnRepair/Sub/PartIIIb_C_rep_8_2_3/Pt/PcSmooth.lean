import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/15`: joint smoothness of the Gaussian pressure `PcSmooth`

Source of record: `the November 2 reference manuscript` 4963-4968.
On `U = Ioi 0 ×ˢ univ`, the theta factorization `PcTheta` writes the pressure as the envelope
`-(1+νs)⁻³ e^{-η²/(2(1+νs))}` times `IIb.tt c 0 ((2(1+νs))⁻¹, q)`, both jointly smooth there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

theorem pcSmooth_of (h : PcTheta) : PcSmooth := by
  intro ν c hν hc
  have hpos : ∀ x : ℝ × Plane, x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) → 0 < 1 + ν * x.1 := by
    intro x hx
    have := mul_pos hν hx.1
    linarith
  have hc1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => 1 + ν * x.1) (Ioi 0 ×ˢ univ) := by
    fun_prop
  have hc3 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((1 + ν * x.1) ^ 3)⁻¹) (Ioi 0 ×ˢ univ) :=
    (hc1.pow 3).inv fun x hx => pow_ne_zero _ (hpos x hx).ne'
  have hexp : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) (Ioi 0 ×ˢ univ) := by
    refine ContDiffOn.exp ?_
    refine ContDiffOn.div ?_ ?_ fun x hx => ?_
    · fun_prop
    · exact contDiffOn_const.mul hc1
    · exact (mul_pos two_pos (hpos x hx)).ne'
  have henv : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1))))
      (Ioi 0 ×ˢ univ) :=
    hc3.neg.mul hexp
  have hm : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) (Ioi 0 ×ˢ univ) := by
    refine ContDiffOn.prodMk ?_ (by fun_prop)
    exact (contDiffOn_const.mul hc1).inv fun x hx => (mul_pos two_pos (hpos x hx)).ne'
  have hmaps : MapsTo (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      (Ioi 0 ×ˢ univ) {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx
    show 0 < (2 * (1 + ν * x.1))⁻¹
    exact inv_pos.2 (mul_pos two_pos (hpos x hx))
  have htt : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      (Ioi 0 ×ˢ univ) :=
    (UnforcedLeray.Short.IIb.contDiffOn_tt_infty hc.ne' 0).comp hm hmaps
  exact (henv.mul htt).congr fun x hx => h ν c x.1 hν hc hx.1.le x.2
end UnforcedLeray.Short.PartIIIb.Concrete
