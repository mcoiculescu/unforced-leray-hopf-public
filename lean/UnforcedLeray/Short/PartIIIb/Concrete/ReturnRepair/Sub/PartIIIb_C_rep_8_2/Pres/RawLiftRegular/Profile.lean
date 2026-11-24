import UnforcedLeray.Cons.C03Background.RawLift
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Lib.Axisymmetric.RingChart
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smoothness of the raw profile for positive age (task `PartIII-b:C/rep/8/2/pres/6/2/3`)

Source lines 1205-1225 (`H = (1-K)ψ` is smooth for `s > 0`) and 4139-4141.
`rawProfile ε v ψ p = v p.1 p.2 + (ε * raisedStream ψ p.1 p.2.1 p.2.2) • e₁₁`, and
`raisedStream ψ s ξ η = ψ s (ξ,η) - (η ∂_η ψ + 2 s ∂_s ψ)`, where the two partial derivatives are
the one-variable `deriv`s of `ψ`.  They are identified with the Fréchet derivative of the uncurried
stream along the constant directions `(0,(0,1))` and `(1,(0,0))` (`Axi.dEta`, `Axi.dS`), which is
`C^∞` on the open set `Ioi 0 ×ˢ univ` by `ContDiffOn.fderiv_of_isOpen`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb

/-- **Smoothness of the raw profile for positive age.** -/
theorem rawProfile_contDiffOn_of (hS : UnforcedLeray.Short.PartI.TrainStreamSmooth) {ν c : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) (ε : ℝ) :
    ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile ε tr.v tr.ψ) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hS ν c hν hc tr hb
  -- first Fréchet derivative of the uncurried stream, and its smoothness
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    hF.fderiv_of_isOpen hopen (by simp)
  have hdEta_c : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Axi.dEta (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) p)
      (Ioi 0 ×ˢ univ) := by
    unfold UnforcedLeray.Axi.dEta
    exact hD1.clm_apply contDiffOn_const
  have hdS_c : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Axi.dS (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) p)
      (Ioi 0 ×ˢ univ) := by
    unfold UnforcedLeray.Axi.dS
    exact hD1.clm_apply contDiffOn_const
  -- one-variable partial derivatives are the Fréchet derivatives along constant directions
  have hdEta : ∀ s ξ η : ℝ, 0 < s →
      deriv (fun t => tr.ψ s (ξ, t)) η =
        UnforcedLeray.Axi.dEta (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (s, (ξ, η)) := by
    intro s ξ η hs
    have hp : ((s, (ξ, η)) : ℝ × (ℝ × ℝ)) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      Set.mk_mem_prod hs (mem_univ _)
    have hdiff : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (s, (ξ, η)) :=
      (hF.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
    have hline : HasDerivAt (fun t : ℝ => ((s, (ξ, t)) : ℝ × (ℝ × ℝ)))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
      (hasDerivAt_const η s).prodMk ((hasDerivAt_const η ξ).prodMk (hasDerivAt_id' η))
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt η hline
    unfold UnforcedLeray.Axi.dEta
    exact hcomp.deriv
  have hdS : ∀ s ξ η : ℝ, 0 < s →
      deriv (fun t => tr.ψ t (ξ, η)) s =
        UnforcedLeray.Axi.dS (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (s, (ξ, η)) := by
    intro s ξ η hs
    have hp : ((s, (ξ, η)) : ℝ × (ℝ × ℝ)) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      Set.mk_mem_prod hs (mem_univ _)
    have hdiff : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (s, (ξ, η)) :=
      (hF.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
    have hline : HasDerivAt (fun t : ℝ => ((t, (ξ, η)) : ℝ × (ℝ × ℝ)))
        ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
      (hasDerivAt_id' s).prodMk ((hasDerivAt_const s ξ).prodMk (hasDerivAt_const s η))
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s hline
    unfold UnforcedLeray.Axi.dS
    exact hcomp.deriv
  -- the raised stream is C^∞ on the positive-age region
  have hη : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.2) (Ioi 0 ×ˢ univ) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.2)).contDiffOn
  have hsτ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.1) (Ioi 0 ×ˢ univ) :=
    contDiff_fst.contDiffOn
  have hG : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) =>
        tr.ψ p.1 p.2 - (p.2.2 * UnforcedLeray.Axi.dEta (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) p +
          2 * p.1 * UnforcedLeray.Axi.dS (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) p))
      (Ioi 0 ×ˢ univ) :=
    hF.sub ((hη.mul hdEta_c).add (((contDiffOn_const.mul hsτ).mul hdS_c)))
  have hraised : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Cons.C03.raisedStream tr.ψ p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ univ) := by
    refine hG.congr ?_
    rintro ⟨s, ξ, η⟩ hp
    have hs : 0 < s := hp.1
    show UnforcedLeray.Cons.C03.raisedStream tr.ψ s ξ η = _
    rw [UnforcedLeray.Cons.C03.raisedStream, hdEta s ξ η hs, hdS s ξ η hs]
  -- the velocity part
  have hv : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hsum : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 +
        (ε * UnforcedLeray.Cons.C03.raisedStream tr.ψ p.1 p.2.1 p.2.2) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
      (Ioi 0 ×ˢ univ) :=
    hv.add ((contDiffOn_const.mul hraised).smul contDiffOn_const)
  exact hsum

end UnforcedLeray.Short.PartIIIb
