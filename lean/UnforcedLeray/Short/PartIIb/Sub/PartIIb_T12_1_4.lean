import UnforcedLeray.Short.PartIIb.Sub.T12_1

/-!
# Part II-b, task `PartII-b:T12/1/4` (`PlanePeriodicLimit`): split into the averaging sequence and the
weak-limit extraction

Source: `the November 2 reference manuscript` lines 1933-1935 ("applying the
Euclidean estimate to a cutoff of `N` repeated cells, dividing its `r`-th power by `N`, and letting
`N → ∞`; there is no period loss").

* `PPLSequence` (leaf `/1`): from `PlaneHelmholtzLr`, cut `F` to `N` cells, project, average the
  `2N+1` translates; the averages `H_N` are uniformly bounded on every window, almost periodic, and
  satisfy the planar identities asymptotically.
* `PPLExtract` (leaf `/2`): any such sequence has a weak limit which is an everywhere periodic `G`
  with `IsPlaneHelmholtz F G` and the stated bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The window `W_M = {-M c ≤ q < M c}` of `2M` periods. -/
def ppWindow (c : ℝ) (M : ℕ) : Set (ℝ × ℝ) := {z | -(M : ℝ) * c ≤ z.1 ∧ z.1 < (M : ℝ) * c}

/-- Properties of an averaged sequence `H_N` for a `c`-periodic `F` (constant `C` for the `L^r`
bound; the `L²` bound has constant `3`). -/
structure PPLProps (r C c : ℝ) (F : ℝ × ℝ → CMerid) (H : ℕ → ℝ × ℝ → CMerid) : Prop where
  memLp : ∀ N M : ℕ, MemLp (H N) 2 (volume.restrict (ppWindow c M)) ∧
    MemLp (H N) (ENNReal.ofReal r) (volume.restrict (ppWindow c M))
  boundR : ∀ N M : ℕ, eLpNorm (H N) (ENNReal.ofReal r) (volume.restrict (ppWindow c M)) ≤
    ENNReal.ofReal C * ENNReal.ofReal (2 * M * c) ^ (1 / r) *
      eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)
  bound2 : ∀ N M : ℕ, eLpNorm (H N) 2 (volume.restrict (ppWindow c M)) ≤
    3 * ENNReal.ofReal (2 * M * c) ^ (1 / (2 : ℝ)) * eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c)
  almostPeriodic : ∀ M : ℕ, Tendsto
    (fun N => eLpNorm (fun z : ℝ × ℝ => H N (z.1 + c, z.2) - H N z) 2
      (volume.restrict (ppWindow c M))) atTop (𝓝 0)
  divFree : ∀ φ : ℝ × ℝ → ℝ, PlaneTest φ → Tendsto
    (fun N => ∫ z, (H N z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + H N z 1 * (fderiv ℝ φ z (0, 1) : ℂ)))
    atTop (𝓝 0)
  orth : ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, PlaneSolTest Ψ → Tendsto
    (fun N => ∫ z, ∑ i : Fin 2, (F z i - H N z i) * (Ψ z i : ℂ)) atTop (𝓝 0)

/-- **Leaf `PartII-b:T12/1/4/1`** (SP 1933-1935, steps (1)-(3) of the task spec; uses
`PlaneHelmholtzLr`): the averaged cut-off projections. -/
def PPLSequence : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → CMerid,
    CylLp c r F → CylLp c 2 F → ∃ H : ℕ → ℝ × ℝ → CMerid, PPLProps r C c F H

/-- **Leaf `PartII-b:T12/1/4/2`** (steps (4)-(6)): weak-limit extraction on the weighted window space
(`Infra/WeaklyNullCompact/Extraction.lean`), periodicity from almost periodicity, norming
(`Lib/CZCore/Norming.lean`), periodic folding. -/
def PPLExtract : Prop :=
  ∀ r : ℝ, 1 < r → ∀ C : ℝ, 0 < C → ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → CMerid,
    CylLp c r F → CylLp c 2 F → ∀ H : ℕ → ℝ × ℝ → CMerid, PPLProps r C c F H →
      ∃ G : ℝ × ℝ → CMerid, CylLp c r G ∧ IsPlaneHelmholtz F G ∧
        eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

theorem planePeriodicLimit_of (h1 : PPLSequence) (h2 : PPLExtract) : PlanePeriodicLimit := by
  intro r hr
  obtain ⟨C, hC, hH⟩ := h1 r hr
  refine ⟨C, hC, fun c hc F hF hF2 => ?_⟩
  obtain ⟨H, hP⟩ := hH c hc F hF hF2
  exact h2 r hr C hC c hc F hF hF2 H hP

end UnforcedLeray.Short.IIb
