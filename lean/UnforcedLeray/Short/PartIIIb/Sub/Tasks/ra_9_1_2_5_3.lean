import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_3.Helpers

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.Concrete.T53

/-- Matrix entries of a `C^4` matrix-valued function. -/
theorem entry_cdo {f : Chart → Mat3} {s : Set Chart} (hf : ContDiffOn ℝ 4 f s) (i j : Fin 3) :
    ContDiffOn ℝ 4 (fun p => f p i j) s :=
  (contDiffOn_apply ℝ ℝ j univ).comp
    ((contDiffOn_apply ℝ (Fin 3 → ℝ) i univ).comp hf (mapsTo_univ _ _)) (mapsTo_univ _ _)

theorem merApply_cdo {f : Chart → Mat3} {g : Chart → ℝ × ℝ} {s : Set Chart}
    (hf : ContDiffOn ℝ 4 f s) (hg : ContDiffOn ℝ 4 g s) :
    ContDiffOn ℝ 4 (fun p => merApply (f p) (g p)) s := by
  refine ContDiffOn.prodMk ?_ ?_
  · exact ((entry_cdo hf 0 0).mul (contDiff_fst.comp_contDiffOn hg)).add
      ((entry_cdo hf 0 2).mul (contDiff_snd.comp_contDiffOn hg))
  · exact ((entry_cdo hf 2 0).mul (contDiff_fst.comp_contDiffOn hg)).add
      ((entry_cdo hf 2 2).mul (contDiff_snd.comp_contDiffOn hg))

theorem merTrace_cdo {f : Chart → Mat3} {s : Set Chart} (hf : ContDiffOn ℝ 4 f s) :
    ContDiffOn ℝ 4 (fun p => merTrace (f p)) s := by
  unfold merTrace
  exact (entry_cdo hf 0 0).add (entry_cdo hf 2 2)

theorem latTermSmooth (as : ℝ) (χf : ℝ → ℝ) : LatTermSmooth as χf := by
  intro hχ ν hν A hA j
  have hχ6 : ContDiff ℝ 6 χf := hχ.smooth.of_le (by simp)
  have hAy : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := by
    unfold Ay
    have hc : ContDiffOn ℝ 6 (fun s : ℝ => χf (ν * s)) (Ioi 0) :=
      (hχ6.comp (contDiff_const.mul contDiff_id)).contDiffOn.mono (subset_univ _)
    exact hc.smul hA.smooth
  have hAyU : ContDiffOn ℝ 4 (fun p : Chart => Ay ν χf A p.1) (Ioi 0 ×ˢ univ) :=
    ((hAy.of_le (by norm_num)).comp (contDiffOn_fst (𝕜 := ℝ) (n := 4) (s := Ioi 0 ×ˢ univ))
      (fun p hp => hp.1))
  have hxj : ContDiff ℝ 4 (fun p : Chart => xj ν j p.2) := by
    unfold xj; fun_prop
  have hW : ContDiffOn ℝ 4 (fun p : Chart => merApply (Ay ν χf A p.1) (xj ν j p.2))
      (Ioi 0 ×ˢ univ) :=
    merApply_cdo (f := fun p : Chart => Ay ν χf A p.1) (g := fun p : Chart => xj ν j p.2)
      hAyU hxj.contDiffOn
  have hV : ContDiffOn ℝ 4 (fun p : Chart => Vj ν p.1 j p.2) (Ioi 0 ×ˢ univ) :=
    (Vj_contDiffOn ν hν j).of_le (by norm_num)
  have hX : ContDiffOn ℝ 4
      (fun p : Chart => merApply (Ay ν χf A p.1) (Vj ν p.1 j p.2)) (Ioi 0 ×ˢ univ) :=
    merApply_cdo (f := fun p : Chart => Ay ν χf A p.1) (g := fun p : Chart => Vj ν p.1 j p.2)
      hAyU hV
  have hVd : ContDiffOn ℝ 4
      (fun p : Chart => fderiv ℝ (fun x => Vj ν p.1 j x) p.2) (Ioi 0 ×ˢ univ) :=
    partial_contDiffOn (fun q : Chart => Vj ν q.1 j q.2) (Vj_contDiffOn ν hν j)
  have hPs : ContDiffOn ℝ 4 (fun p : Chart => psij ν p.1 j p.2) (Ioi 0 ×ˢ univ) :=
    (psij_contDiffOn ν hν j).of_le (by norm_num)
  have hPsd : ContDiffOn ℝ 4
      (fun p : Chart => fderiv ℝ (fun x => psij ν p.1 j x) p.2) (Ioi 0 ×ˢ univ) :=
    partial_contDiffOn (fun q : Chart => psij ν q.1 j q.2) (psij_contDiffOn ν hν j)
  have hTr : ContDiffOn ℝ 4 (fun p : Chart => merTrace (Ay ν χf A p.1)) (Ioi 0 ×ˢ univ) :=
    merTrace_cdo hAyU
  let E' : (ℝ × ℝ) ≃L[ℝ] Merid := LinearEquiv.toContinuousLinearEquiv toMerLE
  constructor
  · have h := E'.contDiff.comp_contDiffOn (hX.sub (hVd.clm_apply hW))
    exact h
  · exact (hTr.mul hPs).sub (hPsd.clm_apply hW)

end UnforcedLeray.Short.PartIIIb.Concrete
