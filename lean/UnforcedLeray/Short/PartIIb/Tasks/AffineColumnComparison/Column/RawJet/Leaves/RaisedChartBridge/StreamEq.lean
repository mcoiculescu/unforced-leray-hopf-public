import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_1

/-!


For `s > 0` the slice derivatives of the jointly smooth chart function are chart partials,
so `raisedStream ψ = raisedH ψ` (source SP 1206-1216, 2419).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

private lemma psiChart_contDiffAt_of {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (psiChart ψ) y := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) :=
    isOpen_Ioi.prod isOpen_univ
  exact hψ.contDiffAt (hopen.mem_nhds (Set.mk_mem_prod hy (mem_univ _)))

private lemma psiChart_differentiableAt_of {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : DifferentiableAt ℝ (psiChart ψ) y :=
  (psiChart_contDiffAt_of hψ hy).differentiableAt (by simp)

theorem raisedStreamEq_proof : UnforcedLeray.Short.IIb.RaisedStreamEq := by
  intro ψ hψ y hy
  obtain ⟨s, ξ, η⟩ := y
  have hy' : (0 : ℝ) < s := hy
  have hd : DifferentiableAt ℝ (psiChart ψ) ((s, (ξ, η)) : Coord) :=
    psiChart_differentiableAt_of hψ hy'
  -- `η`-slice
  have hE : Axi.dEta (psiChart ψ) (s, (ξ, η)) = deriv (fun t => ψ s (ξ, t)) η := by
    have hg : HasDerivAt (fun t : ℝ => ((s, (ξ, t)) : Coord)) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
      (hasDerivAt_const η s).prodMk ((hasDerivAt_const η ξ).prodMk (hasDerivAt_id η))
    have hc : HasFDerivAt (psiChart ψ) (fderiv ℝ (psiChart ψ) (s, (ξ, η))) ((s, (ξ, η)) : Coord) :=
      hd.hasFDerivAt
    have hcomp := hc.comp_hasDerivAt η hg
    have heq : (psiChart ψ ∘ fun t : ℝ => ((s, (ξ, t)) : Coord)) = fun t => ψ s (ξ, t) := rfl
    rw [heq] at hcomp
    exact (hcomp.deriv).symm
  -- `s`-slice
  have hS : Axi.dS (psiChart ψ) (s, (ξ, η)) = deriv (fun t => ψ t (ξ, η)) s := by
    have hg : HasDerivAt (fun t : ℝ => ((t, (ξ, η)) : Coord)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
      (hasDerivAt_id s).prodMk ((hasDerivAt_const s ξ).prodMk (hasDerivAt_const s η))
    have hc : HasFDerivAt (psiChart ψ) (fderiv ℝ (psiChart ψ) (s, (ξ, η))) ((s, (ξ, η)) : Coord) :=
      hd.hasFDerivAt
    have hcomp := hc.comp_hasDerivAt s hg
    have heq : (psiChart ψ ∘ fun t : ℝ => ((t, (ξ, η)) : Coord)) = fun t => ψ t (ξ, η) := rfl
    rw [heq] at hcomp
    exact (hcomp.deriv).symm
  unfold UnforcedLeray.Cons.C03.raisedStream raisedH
  rw [hE, hS]
  simp only [psiChart]
  ring

end UnforcedLeray.Short.IIb
