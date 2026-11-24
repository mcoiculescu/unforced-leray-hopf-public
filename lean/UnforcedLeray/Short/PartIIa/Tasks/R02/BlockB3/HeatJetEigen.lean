import UnforcedLeray.Short.PartIIa.Calc.BlockB3
import UnforcedLeray.Short.PartIIa.Tasks.R02.HeatProfile
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth

/-!
# Part II-a, block `B₃`: the leaf `HeatJetEigen` (task `PartII-a:R02/11/5`)

Target: `heatJetEigen : HeatJetEigen`, i.e. `K^ℓ ∂_η^j G_{νs} = (-(j+1))^ℓ ∂_η^j G_{νs}` on `{s > 0}`.

Source of record: `the November 2 reference manuscript` line 1255
(heat identity `K∂_η^jG_{νs} = -(j+1)∂_η^jG_{νs}`), iterated.

Route: induction on `ℓ`, generalizing `j` and the point. The step uses that `K^{ℓ+1} = K ∘ K^ℓ`,
the induction hypothesis on the open set `{s > 0}` (hence eventually near `x`), and the heat
identity `LateHeatProfile` (i) from `lateHeatProfile`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-! ### Smoothness helpers (copied from `Calc/BlockB1.lean`; the B3 organizer does not export them) -/

theorem contDiffOn_ageOperator {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (ageOperator F) {y : ProfilePoint | 0 < y.2.2} := by
  have h1 := contDiffOn_fderiv_apply hF eηDir
  have h2 := contDiffOn_fderiv_apply hF esDir
  have he : ContDiff ℝ ∞ (fun y : ProfilePoint => y.2.1) := by fun_prop
  have hs : ContDiff ℝ ∞ (fun y : ProfilePoint => y.2.2) := by fun_prop
  exact (he.contDiffOn.mul h1).add ((contDiffOn_const.mul hs.contDiffOn).mul h2)

theorem differentiableAt_of_late {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    DifferentiableAt ℝ F x :=
  (hF.contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)

theorem eventuallyEq_of_late {F G : ProfilePoint → ℝ}
    (h : EqOn F G {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    F =ᶠ[𝓝 x] G :=
  Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun z hz => h hz)
open UnforcedLeray.Short.PartI (heatKernel1)

/-- **Leaf `HeatJetEigen`** (source line 1255): iterated heat identity on `{s > 0}`. -/
theorem heatJetEigen : HeatJetEigen := by
  unfold HeatJetEigen
  intro ν hν ℓ
  have hG : ContDiffOn ℝ ∞ (heatProfile ν) {y : ProfilePoint | 0 < y.2.2} := by
    have h := heatKernelIterSmooth ν hν 0
    simp only [iteratedDeriv_zero] at h
    exact contDiffOn_trainProfile_of_eta (G := fun s e => heatKernel1 (ν * s) e) h
  induction ℓ with
  | zero =>
    intro j x hx
    unfold jet
    simp
  | succ n ih =>
    intro j x hx
    have hD : DifferentiableAt ℝ (partialEta^[j] (heatProfile ν)) x :=
      differentiableAt_of_late (contDiffOn_partialEta_iter hG j) hx
    have hsucc : jet (n + 1) j 0 (heatProfile ν) = ageOperator (jet n j 0 (heatProfile ν)) := by
      unfold jet
      exact Function.iterate_succ_apply' ageOperator n _
    have hev : jet n j 0 (heatProfile ν) =ᶠ[𝓝 x]
        fun y => (-((j : ℝ) + 1)) ^ n * (partialEta^[j] (heatProfile ν)) y :=
      eventuallyEq_of_late (fun y hy => ih j y hy) hx
    rw [hsucc, kx_ageOp_congr hev, kx_ageOp_const_mul _ hD,
      lateHeatProfile.1 ν hν j x hx]
    ring

end UnforcedLeray.Short.PartIIa.BlockB3
