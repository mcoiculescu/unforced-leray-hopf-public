import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_5_1
import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# `PartIII-b:C/near/delta/5/1/3`: linearity of the raised stream on `ψ = ψ̄ + ψ̃`

Source of record: `the November 2 reference manuscript`, lines 2721-2723 (the
stream completion `H = (1 - η∂_η - 2s∂_s)ψ` is linear, so it splits along `ψ = ψ̄ + ψ̃`).

Status: the conditional form `raisedStreamSplit_of` is proved from the two Part I smoothness
statements `PartI.TrainStreamSmooth` and `PartI.BUCMeanStreamSmooth`. The unconditional target
`raisedStreamSplit : RaisedStreamSplit` is NOT proved here: those two smoothness statements are
unproved `Prop`s, and `B0140.IsTrain` gives only `Differentiable ℝ (ψ s)` (joint in `(q,η)`),
not differentiability in the age `s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03

/-- Conditional form: `RaisedStreamSplit` from the smoothness of the train stream and of the
mean stream (`PartI.TrainStreamSmooth`, `PartI.BUCMeanStreamSmooth`). -/
theorem raisedStreamSplit_of (hS : UnforcedLeray.Short.PartI.TrainStreamSmooth)
    (hSm : UnforcedLeray.Short.PartI.BUCMeanStreamSmooth) : RaisedStreamSplit := by
  intro ν c tr hν hc hbuc s hs q η
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hopenM : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  -- joint smoothness of the stream at (s, (q, η))
  have hJψ : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (s, (q, η)) :=
    ((hS ν c hν hc tr hbuc).contDiffAt
      (hopen.mem_nhds (mk_mem_prod (mem_Ioi.2 hs) (mem_univ _)))).differentiableAt (by simp)
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
  have e1 : deriv (fun t : ℝ => tr.ψ s (q, t) - UnforcedLeray.Short.PartI.meanStream tr s t) η =
      deriv (fun t : ℝ => tr.ψ s (q, t)) η -
        deriv (fun t : ℝ => UnforcedLeray.Short.PartI.meanStream tr s t) η :=
    deriv_sub hψ_η hS_η
  have e2 : deriv (fun t : ℝ => tr.ψ t (q, η) - UnforcedLeray.Short.PartI.meanStream tr t η) s =
      deriv (fun t : ℝ => tr.ψ t (q, η)) s -
        deriv (fun t : ℝ => UnforcedLeray.Short.PartI.meanStream tr t η) s :=
    deriv_sub hψ_s hS_s
  show tr.ψ s (q, η) - (η * deriv (fun t : ℝ => tr.ψ s (q, t)) η +
        2 * s * deriv (fun t : ℝ => tr.ψ t (q, η)) s) =
      (UnforcedLeray.Short.PartI.meanStream tr s η -
        (η * deriv (fun t : ℝ => UnforcedLeray.Short.PartI.meanStream tr s t) η +
          2 * s * deriv (fun t : ℝ => UnforcedLeray.Short.PartI.meanStream tr t η) s)) +
      ((tr.ψ s (q, η) - UnforcedLeray.Short.PartI.meanStream tr s η) -
        (η * deriv (fun t : ℝ => tr.ψ s (q, t) - UnforcedLeray.Short.PartI.meanStream tr s t) η +
          2 * s * deriv (fun t : ℝ => tr.ψ t (q, η) -
            UnforcedLeray.Short.PartI.meanStream tr t η) s))
  rw [e1, e2]
  ring

/-- The target: `RaisedStreamSplit`, from the proved smoothness of the train and mean streams. -/
theorem raisedStreamSplit : RaisedStreamSplit :=
  raisedStreamSplit_of UnforcedLeray.Short.PartI.trainStreamSmooth
    UnforcedLeray.Short.PartI.bucMeanStreamSmooth

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
