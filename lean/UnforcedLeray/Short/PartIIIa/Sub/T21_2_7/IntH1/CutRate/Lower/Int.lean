import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutLowerIntAux

lemma ladCut_contDiff' (R : ℝ) : ContDiff ℝ ∞ (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma pdCx_contDiff' (k : Fin 2) {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (by simp)).clm_apply contDiff_const

lemma ladLapCx_continuous' {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (ladLapCx Φ) := by
  unfold ladLapCx
  exact (pdCx_contDiff' 0 (pdCx_contDiff' 0 hΦ)).continuous.add
    (pdCx_contDiff' 1 (pdCx_contDiff' 1 hΦ)).continuous

lemma sq_ge_of_not_box {c R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hK : x ∉ B0579.box c (3 * R)) : 8 * R ^ 2 ≤ x.2 ^ 2 := by
  by_contra h
  push Not at h
  apply hK
  apply B0579.mem_box_of_mem_cell hx
  nlinarith [sq_abs x.2, abs_nonneg x.2]

lemma ladCut_zero_of_not_box' {c R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (hK : x ∉ B0579.box c (3 * R)) : ladCut R x = 0 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.2.1 x (by nlinarith [sq_ge_of_not_box hR hx hK, sq_nonneg R])

lemma integrableOn_cell_box' {c R : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ x ∈ B0579.cell c, x ∉ B0579.box c (3 * R) → g x = 0) :
    IntegrableOn g (B0579.cell c) :=
  B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (3 * R)) h0

end CutLowerIntAux

open CutLowerIntAux in
/-- **(i) Integrability** (SP 3060-3067): the three integrands are continuous in `x` (joint smoothness
of `φ` on the strip, `continuous_ladChi`, `continuous_ladDt`) and vanish off the compact box
`box c (3R)` (`ladCutProps`), so they are integrable on the cell. -/
theorem cutLowerInt (m : ℝ) : CutLowerInt m := by
  intro ν tr t s G φ M hL R hR ρ hρ
  obtain ⟨hctx, _, _⟩ := hL
  obtain ⟨hν, hν1, hb, ht, hts, hG, hφ, hj⟩ := id hctx
  have hR8 : 2 * R ^ 2 ≤ 8 * R ^ 2 := by nlinarith [sq_nonneg R]
  have hslice : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hLc : Continuous (ladCut R) := (ladCut_contDiff' R).continuous
  have hJ : Continuous (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) := B0579.continuous_jb_rpow (-m)
  have hPhi : Continuous (φ ρ) := hslice.continuous
  have hChi : Continuous (ladChi tr φ ρ) := continuous_ladChi tr ht hj hρ
  have hLL : Continuous (ladLapCx (φ ρ)) := ladLapCx_continuous' hslice
  have hDt : Continuous (ladDt φ ρ) := continuous_ladDt hj hρ
  have hC2 : Continuous (fun x : ℝ × ℝ => (ν : ℂ) * ladLapCx (φ ρ) x) :=
    continuous_const.mul hLL
  have hTr : Continuous (fun x : ℝ × ℝ => ladTransport tr ρ (φ ρ) x) := by
    have h0 : Continuous (fun x : ℝ × ℝ =>
        ladChi tr φ ρ x - ladDt φ ρ x - (ν : ℂ) * ladLapCx (φ ρ) x) :=
      (hChi.sub hDt).sub hC2
    refine h0.congr (fun x => ?_)
    unfold ladChi
    ring
  have hF1 : Continuous (lowF1 tr m R φ ρ) := by
    unfold lowF1
    exact (hLc.pow 2).mul (hJ.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hPhi).mul hChi)))
  have hF2 : Continuous (lowF2 m R φ ρ) := by
    unfold lowF2
    exact (hLc.pow 2).mul (hJ.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hPhi).mul hLL)))
  have hF3 : Continuous (lowF3 tr m R φ ρ) := by
    unfold lowF3
    exact (hLc.pow 2).mul (hJ.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hPhi).mul hTr)))
  refine ⟨?_, ?_, ?_⟩
  · refine integrableOn_cell_box' (c := ν ^ (-2 : ℝ)) (R := R) hF1 ?_
    intro x hx hK
    simp [lowF1, ladCut_zero_of_not_box' hR hx hK]
  · refine integrableOn_cell_box' (c := ν ^ (-2 : ℝ)) (R := R) hF2 ?_
    intro x hx hK
    simp [lowF2, ladCut_zero_of_not_box' hR hx hK]
  · refine integrableOn_cell_box' (c := ν ^ (-2 : ℝ)) (R := R) hF3 ?_
    intro x hx hK
    simp [lowF3, ladCut_zero_of_not_box' hR hx hK]

end UnforcedLeray.Short.IIIa
