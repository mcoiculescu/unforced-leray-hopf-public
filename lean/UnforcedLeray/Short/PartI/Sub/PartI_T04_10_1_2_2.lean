import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalUniquenessBounded

/-!
# Part I, `PartI:T04/10/1/2/2`: `APCutoffLimit` from three analytic leaves

Source of record: `the November 2 reference manuscript`, lines 285-288
(approximation and transverse cutoffs; `R → ∞` by dominated convergence).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Curl jet bound** (lines 285-288, "`‖D^k curl v‖ ≤ C ‖D^{k+1} v‖`"): `Cyl.curl u` is a fixed
continuous linear image of `fderiv ℝ u`, so for smooth `u`, `‖D^k (curl u)(z)‖ ≤ C ‖D^{k+1} u(z)‖`
with `C` depending only on `k`. -/
def CurlJetBound : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Plane → Vec, ContDiff ℝ ∞ u → ∀ z : Plane,
    ‖iteratedFDeriv ℝ k (Cyl.curl u) z‖ ≤ C * ‖iteratedFDeriv ℝ (k + 1) u z‖

/-- **Vorticity jets are square integrable on the cell** (lines 285-288, from `jet_l2` and
`CurlJetBound`): for a class solution, `s ∈ [0,T]`, `k`, the function
`z ↦ ‖D^k curl v(s) (z)‖²` is integrable on the cell (it is continuous, dominated by
`C² ‖D^{k+1} v(s)‖²`, integrable by `jet_l2`). -/
def CellVortJetIntegrable : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ s ∈ Icc (0 : ℝ) T, ∀ k : ℕ,
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ^ 2) (Cyl.cell c)

/-- **Measurability in time of the cutoff vorticity jet energy** (lines 285-288): for a class
solution and fixed `k`, `R`, the map `r ↦ cutoffVortJet c k v R r` is a.e.-strongly measurable on
`[0,T]`.  (Route: on the open `Ioo 0 T`, `(r,z) ↦ ‖D^k curl v(r)(z)‖²` is continuous, being built
from the jointly smooth `v` — `ContDiffOn` on `Ioo 0 T ×ˢ univ` is on an open set, so the partial
iterated derivative is the composition of `iteratedFDeriv` of the joint map with `inr`;
`Cyl.cell`-integral of a jointly continuous function times `etaCutoff R` is continuous/measurable
in `r` by `StronglyMeasurable.integral_prod_right` or dominated continuity; endpoints are null.) -/
def CutoffVortJetMeasurable : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ (k : ℕ) (R : ℝ),
      AEStronglyMeasurable (fun r => cutoffVortJet c k v R r) (volume.restrict (Icc (0 : ℝ) T))

/-- Pointwise `R → ∞` limit for the cutoff jet energy. -/
theorem cutoffVortJet_tendsto (hI : CellVortJetIntegrable) (ν c T : ℝ) (v : ℝ → Plane → Vec)
    (p : ℝ → Plane → ℝ) (hν : 0 < ν) (hc : 1 ≤ c) (hcls : IsAPrioriClass ν c T v p)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (k : ℕ) :
    Tendsto (fun R => cutoffVortJet c k v R s) atTop (𝓝 (vortJet c k v s)) := by
  have hint := hI ν c T v p hν hc hcls s hs k
  unfold cutoffVortJet vortJet
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ^ 2)
  · exact Eventually.of_forall fun R =>
      ((cuEtaCutoffContinuous R).aestronglyMeasurable).mul hint.aestronglyMeasurable
  · refine Eventually.of_forall fun R => Eventually.of_forall fun z => ?_
    obtain ⟨h0, h1⟩ := cuEtaCutoffUnit R z.2
    have hb : 0 ≤ ‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg h0 hb)]
    nlinarith
  · exact hint
  · refine Eventually.of_forall fun z => ?_
    simpa using (cuEtaCutoffTendsto z.2).mul_const (‖iteratedFDeriv ℝ k (Cyl.curl (v s)) z‖ ^ 2)

/-- **`APCutoffLimit` from the three leaves.** -/
theorem apCutoffLimit_of (hI : CellVortJetIntegrable) (hM : CutoffVortJetMeasurable) :
    APCutoffLimit := by
  intro ν c T v p hν hc hcls h3 s hs
  refine ⟨cutoffVortJet_tendsto hI ν c T v p hν hc hcls s hs 2,
    cutoffVortJet_tendsto hI ν c T v p hν hc hcls 0 ⟨le_rfl, hcls.pos.le⟩ 2, ?_⟩
  have hsub : Ι (0 : ℝ) s ⊆ Icc (0 : ℝ) T := by
    rw [Set.uIoc_of_le hs.1]
    exact fun r hr => ⟨hr.1.le, hr.2.trans hs.2⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun r => vortJet c 3 v r)
  · exact Eventually.of_forall fun R => (hM ν c T v p hν hc hcls 3 R).mono_set hsub
  · refine Eventually.of_forall fun R => Eventually.of_forall fun r hr => ?_
    have hr' := hsub hr
    have hint := hI ν c T v p hν hc hcls r hr' 3
    have hnn : 0 ≤ cutoffVortJet c 3 v R r :=
      integral_nonneg fun z => mul_nonneg (cuEtaCutoffUnit R z.2).1 (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    unfold cutoffVortJet vortJet
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (cuEtaCutoffUnit R z.2).1 (sq_nonneg _)) hint
      (Eventually.of_forall fun z => by
        obtain ⟨h0, h1⟩ := cuEtaCutoffUnit R z.2
        have hb : 0 ≤ ‖iteratedFDeriv ℝ 3 (Cyl.curl (v r)) z‖ ^ 2 := sq_nonneg _
        show etaCutoff R z.2 * _ ≤ _
        nlinarith)
  · exact intervalIntegrable_iff.2 (h3.mono_set hsub)
  · exact Eventually.of_forall fun r hr =>
      cutoffVortJet_tendsto hI ν c T v p hν hc hcls r (hsub hr) 3

end UnforcedLeray.Short.PartI
