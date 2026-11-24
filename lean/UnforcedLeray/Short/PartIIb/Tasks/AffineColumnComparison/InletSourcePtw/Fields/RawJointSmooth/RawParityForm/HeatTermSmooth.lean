import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- **The heat terms are smooth for positive age** (`HeatTermSmooth`; SP 1310-1313).
On `s > 0`, `heatTerm ν j (s, (q, η)) = ∂_η^{2j} G_{νs}(η) = (√s)^{-(2j+1)} g_{2j}(η/√s)`
(`B0191.heatDeriv_selfSimilar`), which is smooth in `(s, η)` since `√s` is smooth and nonzero
for `s > 0` and `g_{2j}` is smooth (`contDiff_profileDeriv`). -/
theorem heatTermSmooth : UnforcedLeray.Short.IIb.HeatTermSmooth := by
  intro ν _hν j
  have hsq : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => Real.sqrt y.1) (Ioi 0 ×ˢ univ) :=
    ContDiffOn.sqrt (contDiff_fst.contDiffOn) (fun y hy => hy.1.ne')
  have hinv : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => (Real.sqrt y.1)⁻¹) (Ioi 0 ×ˢ univ) :=
    hsq.inv (fun y hy => (Real.sqrt_pos.mpr hy.1).ne')
  have hpow : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => ((Real.sqrt y.1)⁻¹) ^ (2 * j + 1)) (Ioi 0 ×ˢ univ) :=
    hinv.pow _
  have hsnd : ContDiff ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => y.2.2) := contDiff_snd.comp contDiff_snd
  have harg : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => (Real.sqrt y.1)⁻¹ * y.2.2) (Ioi 0 ×ˢ univ) :=
    hinv.mul hsnd.contDiffOn
  have hprof : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) =>
        UnforcedLeray.B0191.profileDeriv ν (2 * j) ((Real.sqrt y.1)⁻¹ * y.2.2)) (Ioi 0 ×ˢ univ) :=
    (contDiff_profileDeriv ν (2 * j)).comp_contDiffOn harg
  have hg : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) =>
        ((Real.sqrt y.1)⁻¹) ^ (2 * j + 1) *
          UnforcedLeray.B0191.profileDeriv ν (2 * j) ((Real.sqrt y.1)⁻¹ * y.2.2))
      (Ioi 0 ×ˢ univ) :=
    hpow.mul hprof
  refine ContDiffOn.congr hg ?_
  intro y hy
  have hs : 0 < y.1 := hy.1
  have hfun : UnforcedLeray.Short.PartI.heatKernel1 (ν * y.1) =
      UnforcedLeray.B0191.heatKernel ν y.1 := by
    funext η
    simp only [UnforcedLeray.Short.PartI.heatKernel1, UnforcedLeray.B0191.heatKernel, mul_assoc]
  have key : IIb.heatTerm ν j y =
      ((Real.sqrt y.1)⁻¹) ^ (2 * j + 1) *
        UnforcedLeray.B0191.profileDeriv ν (2 * j) ((Real.sqrt y.1)⁻¹ * y.2.2) := by
    unfold IIb.heatTerm
    rw [hfun]
    exact UnforcedLeray.B0191.heatDeriv_selfSimilar ν (2 * j) y.2.2 hs
  exact key

end UnforcedLeray.Short.IIb
