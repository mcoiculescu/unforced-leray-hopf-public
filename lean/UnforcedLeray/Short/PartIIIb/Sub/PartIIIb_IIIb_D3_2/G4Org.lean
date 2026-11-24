import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.FlatUniform

/-!
# `PartIII-b:IIIb-D3/2/G4/org`: group G4 (tested source norm, `I_T` integrability)

Source of record: `the November 2 reference manuscript`: tested norm 4475, 4480-4487;
class `B_a`, `I_T` 4584-4592; `‖g_B‖_𝓘 ≤ C‖B‖_a`, `α = 1.1` 4665-4667; split of `I_T` 4668-4690.

`GroupTested D` has two conjuncts (`TestedConj`, `IntConj`).
* `TestedConj`: `‖g_B(t)‖ ≤ C‖H‖ |B(t)|`-type pointwise bound from the bounded sources
  (`FlatSrcBdd`, via `FI.src`), `|B(t)| ≤ ‖B‖_a e^{at}t^{3/2}` a.e. (`bclassAeBound`),
  `|F_+(t,0)⁻¹| ≤ C e^{-γt/3}` on `[0,1.1/ν]` (`fpmInvBound`), and the window-uniform integral
  `∫ t^{μ+3/2} e^{-(γ/3-a)t} ≤ C` for `μ` in a compact subset of `[0,∞)`
  (`a = a_s < γ/16`, window `mu_eventually_mem`); `∫ ≥ 0` integrand, so no integrability of the
  tested integrand is needed (`integral_mono_of_nonneg`, right side integrable).
* `IntConj`: integrability of the two pieces of the `I_T` integrand (needs the actual readout
  `Mcell = symOuter(trainMer, kcMer ξ)`; organize item).

Assembly: `flatGroupTested_of`; the task `PartIII-b:IIIb-D3/2/G4` states
`flatGroupTested D := flatGroupTested_of flatTestedConj flatITInt D`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF

/-- First conjunct of `GroupTested` (source 4665-4667). -/
def TestedConj (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
    testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
      ((S n).gB B) ≤ C * bNorm D.K.as B

/-- Second conjunct of `GroupTested` (source 4672-4690). -/
def IntConj (D : SeqData) : Prop :=
  ForActual D fun S => ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
    Integrable (fun s => (S n).ITdens (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
        (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s)
      (volume.restrict (Ioi (0 : ℝ))) ∧
    Integrable (fun s => (S n).ITdens (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
        (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s)
      (volume.restrict (Ioi (0 : ℝ)))

/-- **Group G4 from its two conjuncts.** -/
theorem flatGroupTested_of (h1 : ∀ D : SeqData, TestedConj D) (h2 : ∀ D : SeqData, IntConj D)
    (D : SeqData) : GroupTested D := by
  intro dm dp hst κ hκ m _ hm S hS
  exact ⟨h1 D dm dp hst κ hκ m hm S hS, h2 D dm dp hst κ hκ m hm S hS⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
