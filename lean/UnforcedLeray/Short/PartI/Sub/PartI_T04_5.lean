import UnforcedLeray.Short.PartI.Sub.T04.APriori
import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, `PartI:T04/5` and `PartI:T04/6`: the energy and enstrophy inequalities, reduced to the
cutoff inequalities

Source of record: `the November 2 reference manuscript`, lines 278-287 ("Approximation
and transverse cutoffs then give the velocity and vorticity energy identities").

`APEnergyCutoffIneq` / `APEnstrophyCutoffIneq` are the cutoff inequalities
`F_R(s) ≤ F_R(0) + C R^{-1/2}` (the derivative of the cutoff energy is `≤` cutoff errors, the
dissipation term having a sign, lines 278-287).  Here the limit `R → ∞` is carried out
(dominated convergence): `apEnergy_of`, `apEnstrophy_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Cutoff velocity energy `F_R(s) = ∫_cell χ_R(η) |v(s)|²` (lines 285-286). -/
def apCutoffEnergy (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖v s z‖ ^ 2

/-- Cutoff enstrophy `G_R(s) = ∫_cell χ_R(η) ω(s)²`, `ω = curl v` (line 286). -/
def apCutoffEnstrophy (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.curl (v s) z) ^ 2

/-- **Cutoff velocity energy inequality** (lines 278-286): momentum equation tested with `χ_R v`,
dissipation dropped by its sign, transport, viscous cross and pressure terms `O(R^{-1/2})`
(pressure bounded by `ClassicalPressureBound`). -/
def APEnergyCutoffIneq : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      apCutoffEnergy c v R s ≤ apCutoffEnergy c v R 0 + C / Real.sqrt R

/-- **Cutoff enstrophy inequality** (lines 285-287): scalar vorticity equation tested with
`χ_R ω`, plus square integrability of `ω(s)` on the cell. -/
def APEnstrophyCutoffIneq : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      (∀ s ∈ Icc (0 : ℝ) T, IntegrableOn (fun z => (Cyl.curl (v s) z) ^ 2) (Cyl.cell c)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
        apCutoffEnstrophy c v R s ≤ apCutoffEnstrophy c v R 0 + C / Real.sqrt R

/-- Dominated convergence for the cutoff: `∫_cell χ_R g → ∫_cell g` for integrable `g`. -/
theorem tendsto_cutoff_integral (hη : EtaCutoffFacts) (c : ℝ) (g : Plane → ℝ)
    (hg : IntegrableOn g (Cyl.cell c)) :
    Tendsto (fun R : ℝ => ∫ z in Cyl.cell c, etaCutoff R z.2 * g z) atTop
      (nhds (∫ z in Cyl.cell c, g z)) := by
  obtain ⟨C₀, -, hC⟩ := hη
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖g z‖) ?_ ?_ hg.norm ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    obtain ⟨hs, -, -, -, -⟩ := hC R hR
    have hc : Continuous fun z : Plane => etaCutoff R z.2 :=
      (hs.continuous).comp continuous_snd
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨-, h01, -, -, -⟩ := hC R hR
    rw [norm_mul, Real.norm_of_nonneg (h01 z.2).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (h01 z.2).2
  · refine Filter.Eventually.of_forall fun z => ?_
    have : ∀ᶠ R : ℝ in atTop, etaCutoff R z.2 * g z = g z := by
      filter_upwards [eventually_ge_atTop (max 1 |z.2|)] with R hR
      obtain ⟨-, -, h1, -, -⟩ := hC R (le_trans (le_max_left _ _) hR)
      rw [h1 z.2 (le_trans (le_max_right _ _) hR), one_mul]
    exact tendsto_const_nhds.congr' (this.mono fun R h => h.symm)

/-- Passing to the limit `R → ∞` in a cutoff inequality `F_R(s) ≤ F_R(0) + C R^{-1/2}`. -/
theorem le_of_cutoff_ineq (hη : EtaCutoffFacts) (c : ℝ) (g₀ g₁ : Plane → ℝ) (C : ℝ)
    (h₀ : IntegrableOn g₀ (Cyl.cell c)) (h₁ : IntegrableOn g₁ (Cyl.cell c))
    (h : ∀ R : ℝ, 1 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * g₁ z ≤
      (∫ z in Cyl.cell c, etaCutoff R z.2 * g₀ z) + C / Real.sqrt R) :
    ∫ z in Cyl.cell c, g₁ z ≤ ∫ z in Cyl.cell c, g₀ z := by
  have hs : Tendsto (fun R : ℝ => C / Real.sqrt R) atTop (nhds 0) :=
    (tendsto_const_nhds (x := C)).div_atTop (Real.tendsto_sqrt_atTop)
  have h0 := (tendsto_cutoff_integral hη c g₀ h₀).add hs
  rw [add_zero] at h0
  refine le_of_tendsto_of_tendsto (tendsto_cutoff_integral hη c g₁ h₁) h0 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR using h R hR

/-- `PartI:T04/5`, conditional on the cutoff inequality. -/
theorem apEnergy_of (h : APEnergyCutoffIneq) : APEnergy := by
  intro ν c T v p hν hc hcls s hs
  obtain ⟨C, -, hC⟩ := h ν c T v p hν hc hcls
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hcls.pos.le⟩
  have hint : ∀ r ∈ Icc (0 : ℝ) T, IntegrableOn (fun z => ‖v r z‖ ^ 2) (Cyl.cell c) :=
    fun r hr => hcls.classical.finite_energy r hr
  have := le_of_cutoff_ineq etaCutoffFacts c (fun z => ‖v 0 z‖ ^ 2) (fun z => ‖v s z‖ ^ 2) C
    (hint 0 h0) (hint s hs) (fun R hR => by simpa only [apCutoffEnergy, apCutoffEnstrophy] using hC R hR s hs)
  simpa only [velJet, norm_iteratedFDeriv_zero] using this

/-- `PartI:T04/6`, conditional on the cutoff enstrophy inequality. -/
theorem apEnstrophy_of (h : APEnstrophyCutoffIneq) : APEnstrophy := by
  intro ν c T v p hν hc hcls s hs
  obtain ⟨hint, C, -, hC⟩ := h ν c T v p hν hc hcls
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hcls.pos.le⟩
  have := le_of_cutoff_ineq etaCutoffFacts c (fun z => (Cyl.curl (v 0) z) ^ 2)
    (fun z => (Cyl.curl (v s) z) ^ 2) C (hint 0 h0) (hint s hs) (fun R hR => by simpa only [apCutoffEnergy, apCutoffEnstrophy] using hC R hR s hs)
  simpa only [vortJet, norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs] using this

end UnforcedLeray.Short.PartI
