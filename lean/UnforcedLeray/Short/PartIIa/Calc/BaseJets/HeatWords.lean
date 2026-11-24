import UnforcedLeray.Short.PartIIa.Calc.BaseJets
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth

/-!
# Part II-a, task `PartII-a:R02/8/18`: heat words

Source of record: `the November 2 reference manuscript`, lines 1267-1268
(`K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}`), with the profile calculus of `Calc/BaseJets.lean`.
The target `HeatWords` is the `K`-eigenvalue statement iterated `ℓ` times.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- The heat profile is `C^∞` on `{s > 0}` for `ν > 0`. -/
theorem heatProfile_contDiffOn_jet {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (heatProfile ν) {x : ProfilePoint | 0 < x.2.2} := by
  have hg : ContDiff ℝ ∞ (fun y : ProfilePoint => (y.2.2, y.2.1)) :=
    (contDiff_snd.comp contDiff_snd).prodMk (contDiff_fst.comp contDiff_snd)
  exact (heatKernel1_contDiffOn_scaled hν).comp hg.contDiffOn
    (fun y hy => ⟨hy, mem_univ _⟩)

theorem heatWords_of (h : LateHeatProfile) (hL : IterCalcLin) : HeatWords := by
  intro ν hν
  refine ⟨heatProfile_contDiffOn_jet hν, fun ℓ b => ?_⟩
  have hG : ContDiffOn ℝ ∞ (partialEta^[b] (heatProfile ν)) {x : ProfilePoint | 0 < x.2.2} :=
    contDiffOn_partialEta_iter (heatProfile_contDiffOn_jet hν) b
  induction ℓ with
  | zero =>
    intro x _
    simp
  | succ ℓ ih =>
    intro x hx
    have e2 : EqOn (ageOperator (ageOperator^[ℓ] (partialEta^[b] (heatProfile ν))))
        (ageOperator (fun y => (-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) y))
        {x : ProfilePoint | 0 < x.2.2} :=
      hL.1 _ _ ih 1 0 0
    have e3 : EqOn (ageOperator (fun y => (-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) y))
        (fun y => (-((b : ℝ) + 1)) ^ ℓ * ageOperator (partialEta^[b] (heatProfile ν)) y)
        {x : ProfilePoint | 0 < x.2.2} :=
      hL.2.2 (partialEta^[b] (heatProfile ν)) hG ((-((b : ℝ) + 1)) ^ ℓ) 1 0 0
    have e2x : ageOperator (ageOperator^[ℓ] (partialEta^[b] (heatProfile ν))) x =
        ageOperator (fun y => (-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) y) x :=
      e2 hx
    have e3x : ageOperator (fun y => (-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) y) x =
        (-((b : ℝ) + 1)) ^ ℓ * ageOperator (partialEta^[b] (heatProfile ν)) x :=
      e3 hx
    rw [Function.iterate_succ_apply', e2x, e3x, h.1 ν hν b x hx, pow_succ]
    ring

end UnforcedLeray.Short.PartIIa.Jet
