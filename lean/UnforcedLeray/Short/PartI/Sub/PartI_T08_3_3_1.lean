import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

/-!
# Part I, task `PartI:T08/3/3/1` (`PressureGradJetL2OfDivForm`): decomposition

Source: `the November 2 reference manuscript` lines 326-336 (`π = p - p_c^p`,
`Δπ = -div F`, `F = A + div Q_c`) and 261-288 (transverse cutoffs).

Order `0` uses only `|π| ≤ M` (no bound on `∇π`): cutoff `φ_R`, `χ_R = φ_R²`
(`etaCutoff`), `∫ χ_R |∇π|² ≤ C ∫ |F|² + O(M² c)` uniformly in `R`, then monotone
convergence (`CutoffL2OfBound`).  Order `j + 1` applies the `L²` version of the cutoff integration
by parts to `h = ∂_w ∂_k π` (`h, Δh ∈ L²` only; the existing `GradL2OfLapL2` needs bounded
`h, ∇h`, which word derivatives of `π` do not have): `∫ φ² |∇h|² ≤ 2∫ φ² |h||Δh| +
4∫ h² |∇φ|²`.  The word induction is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **Leaf A (order 0).** `π` smooth, `c`-periodic, bounded, `F` smooth periodic with `L²` word
jets and `Δπ + div F = 0`: then `∂_q π, ∂_η π ∈ L²(cell)`.  Route: cutoff IBP
`∫ φ²|∇π|² = -∫ φ² π Δπ - 2∫ φ π ∇φ·∇π`, `-∫ φ² π Δπ = -∫ φ² ∇π·F - 2∫ φ π ∇φ·F`,
Cauchy-Schwarz, strip area `2Rc`, `|∇φ| ≤ C/R`; bound uniform in `R`; `CutoffL2OfBound`. -/
def PressureGradOrder0 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (π : Plane → ℝ) (F : Plane → Vec),
    ContDiff ℝ ∞ π → Cyl.IsPeriodic c π → (∃ M : ℝ, ∀ z, |π z| ≤ M) →
    SmoothJetL2 c F → Cyl.IsPeriodic c F →
    (∀ z, Train.lapS π z + (Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z)
      = 0) →
    MemLp (Cyl.partialQ π) 2 (Cyl.cellμ c) ∧ MemLp (Cyl.partialEta π) 2 (Cyl.cellμ c)

/-- **Leaf B (gradient in `L²` from `h, Δh ∈ L²`, no boundedness).**  A smooth `c`-periodic `h`
with `h, Δh ∈ L²(cell)` has `∂_q h, ∂_η h ∈ L²(cell)`.  Route: `φ = √etaCutoff R`
(`φ = smoothTransition (2 - |η|/R)`), `∫ φ²|∇h|² = -∫ φ² h Δh - 2∫ φ h ∇φ·∇h ≤ ‖h‖‖Δh‖ +
½∫ φ²|∇h|² + 2∫ h²|∇φ|²` with `|∇φ| ≤ C/R`; uniform in `R`; `CutoffL2OfBound`. -/
def GradL2OfLapL2NoBound : Prop :=
  ∀ (c : ℝ) (h : Plane → ℝ), 0 < c → ContDiff ℝ ∞ h → Cyl.IsPeriodic c h →
    MemLp h 2 (Cyl.cellμ c) → MemLp (Train.lapS h) 2 (Cyl.cellμ c) →
    MemLp (Cyl.partialQ h) 2 (Cyl.cellμ c) ∧ MemLp (Cyl.partialEta h) 2 (Cyl.cellμ c)

/-- **Leaf C (Laplacian of the pressure-gradient word jets).** Under the hypotheses of the
target, every `Δ ∂_w (∇π)_k = -∂_w ∂_k div F` is in `L²(cell)` (word derivatives commute with
`Δ`, `∂_k`, `div`: `JetViscIBP.derivWord_lap`, `ForcingIBP.derivWord_comm`; then `SmoothJetL2 F`
for the word `w` followed by `k` on the components). -/
def PressureGradWordLapL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (π : Plane → ℝ) (F : Plane → Vec),
    ContDiff ℝ ∞ π → SmoothJetL2 c F →
    (∀ z, Train.lapS π z + (Cyl.partialQ (fun w => F w 0) z + Cyl.partialEta (fun w => F w 1) z)
      = 0) →
    ∀ (w : List Bool) (k : Fin 2),
      MemLp (Train.lapS (wordComp w (Train.gradS π) k)) 2 (Cyl.cellμ c)

theorem gradS_comp_zero (π : Plane → ℝ) : (fun z => Train.gradS π z 0) = Cyl.partialQ π := rfl

theorem gradS_comp_one (π : Plane → ℝ) : (fun z => Train.gradS π z 1) = Cyl.partialEta π := rfl

theorem pressureGradJetL2OfDivForm_of (hA : PressureGradOrder0) (hB : GradL2OfLapL2NoBound)
    (hC : PressureGradWordLapL2) : PressureGradJetL2OfDivForm := by
  intro c hc π F hπ hper hbd hF hFper hlap w k
  have hsm : ∀ (w : List Bool) (k : Fin 2), ContDiff ℝ ∞ (wordComp w (Train.gradS π) k) := by
    intro w k
    refine B0151.contDiff_derivWord ?_ w
    fin_cases k
    · exact ForcingIBP.cd_partialQ hπ
    · exact ForcingIBP.cd_partialEta hπ
  have hpp : ∀ (w : List Bool) (k : Fin 2), Cyl.IsPeriodic c (wordComp w (Train.gradS π) k) := by
    intro w k
    have h0 : B0151.IsPeriodicQ c π := fun q η => hper (q, η)
    have key : B0151.IsPeriodicQ c (fun x => Train.gradS π x k) := by
      fin_cases k
      · exact h0.partialX
      · exact h0.partialY
    intro z
    exact B0151.periodic_derivWord key w z.1 z.2
  induction w generalizing k with
  | nil =>
    obtain ⟨h0, h1⟩ := hA c hc π F hπ hper hbd hF hFper hlap
    fin_cases k
    · exact h0
    · exact h1
  | cons b w ih =>
    have hL := hB c _ hc (hsm w k) (hpp w k) (ih k) (hC c hc π F hπ hF hlap w k)
    cases b with
    | true => exact hL.1
    | false => exact hL.2

end UnforcedLeray.Short.PartI
