import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/2` (`DualPsiInfSmooth`): smoothness of `ψ_∞`.

Source: `the November 2 reference manuscript` lines 1923-1927.
`ψ_∞ = σ^{μ-1} χ(σ) H(s-σ,·)`: off `tsupport χ` it vanishes near the point; on `tsupport χ ⊂ (0,s)`
each factor is smooth (`σ^{μ-1}` for `σ > 0`, `χ` smooth, `H` smooth on `{τ > 0}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dualSm_cpow (μ : ℂ) {σ0 : ℝ} (h0 : 0 < σ0) :
    ContDiffAt ℝ ∞ (fun σ : ℝ => ((σ : ℂ)) ^ (μ - 1)) σ0 := by
  have hs : (σ0 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (by rw [Complex.ofReal_re]; exact h0))
  have h1 : ContDiffAt ℂ ∞ (fun w : ℂ => w ^ (μ - 1)) (σ0 : ℂ) :=
    AnalyticAt.contDiffAt (analyticAt_id.cpow analyticAt_const hs)
  exact (h1.restrict_scalars (𝕜 := ℝ)).comp σ0 Complex.ofRealCLM.contDiff.contDiffAt

theorem dualPsiInfSmooth : UnforcedLeray.Short.IIb.DualPsiInfSmooth := by
  intro c ν μ H s r' χ hc hν hs hH hχ
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x.1 ∈ tsupport χ
  · have hxI : x.1 ∈ Ioo (0 : ℝ) s := hχ.2.2 hx
    have hx0 : 0 < x.1 := hxI.1
    have hP : ContDiffAt ℝ ∞ (fun y : Coord => ((y.1 : ℂ)) ^ (μ - 1)) x :=
      (dualSm_cpow μ hx0).comp x contDiff_fst.contDiffAt
    have hQ : ContDiffAt ℝ ∞ (fun y : Coord => ((χ y.1 : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (((hχ.1).comp contDiff_fst).contDiffAt)
    have hm : ContDiff ℝ ∞ (fun y : Coord => (s - y.1, y.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    have hp : (s - x.1, x.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
      ⟨show (0 : ℝ) < s - x.1 by linarith [hxI.2], mem_univ _⟩
    have hHc : ContDiffAt ℝ ∞ H (s - x.1, x.2) :=
      hH.smooth.contDiffAt (IsOpen.mem_nhds (IsOpen.prod isOpen_Ioi isOpen_univ) hp)
    have hR : ContDiffAt ℝ ∞ (fun y : Coord => ((H (s - y.1, y.2) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (hHc.comp x hm.contDiffAt)
    unfold dualPsiInf
    exact (hP.mul hQ).mul hR
  · have hxU : x ∈ {y : Coord | y.1 ∉ tsupport χ} := hx
    have hU : IsOpen {y : Coord | y.1 ∉ tsupport χ} :=
      (isClosed_tsupport χ).isOpen_compl.preimage continuous_fst
    have hev : dualPsiInf μ χ H s =ᶠ[𝓝 x] (fun _ : Coord => (0 : ℂ)) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      unfold dualPsiInf
      rw [image_eq_zero_of_notMem_tsupport hy]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev

end UnforcedLeray.Short.IIb
