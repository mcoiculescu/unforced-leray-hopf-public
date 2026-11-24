import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartIIa.Sub.R01_1

/-!
# Part III-a, `PartIII-a:T23/1/5`: the stream completion splits into mean and fluctuation

Source of record: `the November 2 reference manuscript`, lines 2721-2723
(`ψ = \bar ψ + \tilde ψ` in the stream completion). Calculus only.

Target: `raisedStreamSplit_of`, which proves `RaisedStreamSplit` (`Sub/T23_1_org.lean`) from the
Part I smoothness of the stream `TrainStreamSmooth` and the Part II-a smoothness of the mean stream
`MeanStreamSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem raisedStreamSplit_of (hS : UnforcedLeray.Short.PartI.TrainStreamSmooth)
    (hSm : UnforcedLeray.Short.PartIIa.MeanStreamSmooth) :
    UnforcedLeray.Short.IIIa.RaisedStreamSplit := by
  unfold UnforcedLeray.Short.IIIa.RaisedStreamSplit
  intro ν c hν hc tr hbuc s hs q η
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hopenM : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  -- joint smoothness of the stream at the point (s, (q, η))
  have hJψ : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (s, (q, η)) :=
    ((hS ν c hν hc tr hbuc).contDiffAt
      (hopen.mem_nhds (mk_mem_prod (mem_Ioi.2 hs) (mem_univ _)))).differentiableAt (by simp)
  -- η-direction and s-direction of the stream
  have hf_η : DifferentiableAt ℝ (fun t : ℝ => ((s, (q, t)) : ℝ × (ℝ × ℝ))) η :=
    (differentiableAt_const s).prodMk ((differentiableAt_const q).prodMk differentiableAt_id)
  have hf_s : DifferentiableAt ℝ (fun t : ℝ => ((t, (q, η)) : ℝ × (ℝ × ℝ))) s :=
    differentiableAt_id.prodMk (differentiableAt_const (q, η))
  have hψ_η : DifferentiableAt ℝ (fun t : ℝ => tr.ψ s (q, t)) η :=
    DifferentiableAt.comp (g := fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2)
      (f := fun t : ℝ => ((s, (q, t)) : ℝ × (ℝ × ℝ))) η hJψ hf_η
  have hψ_s : DifferentiableAt ℝ (fun t : ℝ => tr.ψ t (q, η)) s :=
    DifferentiableAt.comp (g := fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2)
      (f := fun t : ℝ => ((t, (q, η)) : ℝ × (ℝ × ℝ))) s hJψ hf_s
  -- joint smoothness of the mean stream at (s, η)
  have hJS : DifferentiableAt ℝ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (s, η) :=
    ((hSm ν c hν hc tr hbuc).contDiffAt
      (hopenM.mem_nhds (mk_mem_prod (mem_Ioi.2 hs) (mem_univ η)))).differentiableAt (by simp)
  have hg_η : DifferentiableAt ℝ (fun t : ℝ => ((s, t) : ℝ × ℝ)) η :=
    (differentiableAt_const s).prodMk differentiableAt_id
  have hg_s : DifferentiableAt ℝ (fun t : ℝ => ((t, η) : ℝ × ℝ)) s :=
    differentiableAt_id.prodMk (differentiableAt_const η)
  have hS_η : DifferentiableAt ℝ (fun e : ℝ => UnforcedLeray.Short.PartI.meanStream tr s e) η :=
    DifferentiableAt.comp (g := fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) η hJS hg_η
  have hS_s : DifferentiableAt ℝ (fun r : ℝ => UnforcedLeray.Short.PartI.meanStream tr r η) s :=
    DifferentiableAt.comp (g := fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (f := fun t : ℝ => ((t, η) : ℝ × ℝ)) s hJS hg_s
  -- the fluctuation is the difference of the stream and its mean, pointwise
  have e1 : deriv (fun t : ℝ => UnforcedLeray.Short.IIIa.fluctStream tr s (q, t)) η =
      deriv (fun t : ℝ => tr.ψ s (q, t)) η -
        deriv (fun e : ℝ => UnforcedLeray.Short.PartI.meanStream tr s e) η := by
    rw [show (fun t : ℝ => UnforcedLeray.Short.IIIa.fluctStream tr s (q, t)) =
        fun t : ℝ => tr.ψ s (q, t) - UnforcedLeray.Short.PartI.meanStream tr s t from rfl]
    exact deriv_sub hψ_η hS_η
  have e2 : deriv (fun t : ℝ => UnforcedLeray.Short.IIIa.fluctStream tr t (q, η)) s =
      deriv (fun t : ℝ => tr.ψ t (q, η)) s -
        deriv (fun r : ℝ => UnforcedLeray.Short.PartI.meanStream tr r η) s := by
    rw [show (fun t : ℝ => UnforcedLeray.Short.IIIa.fluctStream tr t (q, η)) =
        fun t : ℝ => tr.ψ t (q, η) - UnforcedLeray.Short.PartI.meanStream tr t η from rfl]
    exact deriv_sub hψ_s hS_s
  have e3 : UnforcedLeray.Short.IIIa.fluctStream tr s (q, η) =
      tr.ψ s (q, η) - UnforcedLeray.Short.PartI.meanStream tr s η := rfl
  unfold UnforcedLeray.Cons.C03.raisedStream UnforcedLeray.Short.IIIa.meanCompletion
  rw [e1, e2, e3]
  ring

end UnforcedLeray.Short.IIIa
