import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1

/-!
# `TrainStreamSmooth` (`PartIII-b:C/rep/8/2/1/1/org`)

Source `the November 2 reference manuscript`
lines 270-288 (the train is the global Gallay-Slijepčević solution, smooth for positive time),
397 and 1202 (`v = ∇^⊥ψ`, `ψ` its decaying stream), 2042 (`v_c` is the train of
`sct:train`), 2073-2077 (`H = (1-K)ψ`, `K = η∂_η + 2s∂_s`, which differentiates `ψ` in `s`).

Design.  Joint smoothness of `ψ` in `(s,q,η)` is not a consequence of the fields of
`B0140.IsTrain` (it fixes `ψ(s,·)` only up to its limit at `|η| → ∞`, slice by slice; see
`Short/PartI/Sub/T01.lean`), and adding it to `IsTrain` would break the Part I existence chain
(`PartI/Sub/T04/Compose.lean` builds the train from slice-by-slice streams).  Following the Part I
decision (`ORG:train-class`) the actual train of a return level is the BUC train, and
`ReturnLevel` records `train_buc` and `train_stream_smooth` (`Concrete/ReturnInst.lean`, task
`PartIII-b:C/rep/8/2/1/2/1/org`; for BUC trains the same statement is
`PartI.trainStreamSmooth`).  Here `trainFpsi L (σ, z) = ψ(e^σ, z)` is the composite of `ψ`,
smooth on `(0,∞) × ℝ²`, with the smooth map `(σ, z) ↦ (e^σ, z)` into `(0,∞) × ℝ²`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The decaying stream of the actual train is jointly `C^∞` in `(σ, q, η)`, `σ = log s`**
(source 270-288, 397, 2040-2049, 2073-2077). -/
theorem trainStreamSmooth : TrainStreamSmooth := by
  intro L
  have hg : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => ((Real.exp z.1, z.2) : ℝ × UnforcedLeray.Cyl.Plane)) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk contDiff_snd
  exact L.train_stream_smooth.comp_contDiff hg (fun z => ⟨Real.exp_pos z.1, mem_univ _⟩)

end UnforcedLeray.Short.PartIIIb.Concrete

end
