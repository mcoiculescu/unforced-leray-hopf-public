import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2085-2093.
The slices of the train drift are smooth (`tr.isTrain.smooth_v`, restricted to `r ≥ 0`), and the
bounds of `DriftC2Bdd` on `[0, Σ/ν]` restrict to `[s, t] ⊆ [0, Σ/ν]`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

theorem trainDriftSmoothBdd : UnforcedLeray.Short.IIb.TrainDriftSmoothBdd := by
  intro Sg ν c V tr hDC s t hs ht
  have hsub : ∀ r ∈ Icc s t, r ∈ Icc (0 : ℝ) (Sg / ν) :=
    fun r hr => ⟨le_trans hs hr.1, le_trans hr.2 ht⟩
  refine ⟨fun r hr i => ?_, fun r hr x i => hDC r (hsub r hr) x i⟩
  have hr0 : 0 ≤ r := le_trans hs hr.1
  have hsm := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun z _ => ⟨mem_Ici.2 hr0, mem_univ z⟩)
  have hvd : ContDiff ℝ ∞ (tr.v r) := contDiffOn_univ.1 hsm
  exact (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hvd

end UnforcedLeray.Short.IIb
