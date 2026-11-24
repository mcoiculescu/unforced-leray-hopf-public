import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.Org
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.DeltaC

/-!
# `ORG:D3/2/G1/1`: `YoungSourceFacts` from two concrete source Props (source 4376-4406)

* `FrozenPairBoundedActual`: the frozen pair and dual are bounded on `0 ≤ s ≤ 2/ν` (4376-4380).
* `RetainedBlocksActual`: the retained block estimates (4382-4384, 4396-4406) with residual
  `δ_c = C_Σ(c⁻² + P_ν e^{C_Σ/ν - b_Σ c²})` at `c = ν⁻²` (4390-4395); `δ_c ≤ Cν²` is
  `deltaCSmall_holds` (YoungBlocks.lean:51), proved here.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF

namespace G1

/-- **Frozen pair bounded on the finite band** (source 4376-4380: the heat-scaled endpoint maps have
uniform norms on `a ≤ 1 + Σ`, `Σ = 2`; from `FullClockLongForward`/`FullClockWeakForward` and
`PerFrameFactsAll`). -/
def FrozenPairBoundedActual (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (N0 : ℕ) (C : ℝ), ∀ n ≥ N0, ∀ s ∈ Icc (0 : ℝ) (2 / nu D n), ∀ j : Bool,
    ‖(S n).pk.q j s‖ ≤ C ∧ ‖(S n).pk.ell j s‖ ≤ C

/-- **Retained block estimates with the source residual** (source 4382-4384, 4390-4395, 4396-4406;
`prop:short-full-clock` via `ConcreteYF.TrainBlockInput` and `IsTrainPkg` of the actual package):
for some `C_Σ, b_Σ > 0, P_ν = K ν^{-p}`, with `c = ν⁻²`. -/
def RetainedBlocksActual (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (CS bS K : ℝ) (p : ℕ), 0 < bS ∧ 0 ≤ CS ∧ 0 ≤ K ∧
    RetainedBlocks (fun n => (S n).pk) (nu D) D.Pl.eigenvalue D.Pl.kappa 2 1.1
      (fun n => deltaC (K * (nu D n)⁻¹ ^ p) CS bS (nu D n) (nu D n ^ (-2 : ℝ)))

theorem youngSourceFacts_of (D : SeqData) (h1 : FrozenPairBoundedActual D)
    (h2 : RetainedBlocksActual D) : YoungSourceFacts D := by
  intro dm dp hD κ hκ m hfact hm S hS
  obtain ⟨N1, C1, hb⟩ := h1 dm dp hD κ hκ m hm S hS
  obtain ⟨CS, bS, K, p, hbS, hCS, hK, hR⟩ := h2 dm dp hD κ hκ m hm S hS
  obtain ⟨C, ν₀, hν₀, hC⟩ := deltaCSmall_holds CS bS K p hbS
  have hlim : Tendsto (nu D) atTop (𝓝 0) := retNu_tendsto D.σ₀ hD.omega_ne
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Iic_mem_nhds hν₀))
  refine ⟨max N1 N2, fun n => deltaC (K * (nu D n)⁻¹ ^ p) CS bS (nu D n) (nu D n ^ (-2 : ℝ)),
    ⟨C1, fun n hn s hs j => hb n (le_trans (le_max_left _ _) hn) s hs j⟩, ⟨C, fun n hn => ?_⟩, hR⟩
  have hpos : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  refine ⟨?_, hC _ hpos (hN2 n (le_trans (le_max_right _ _) hn))⟩
  show 0 ≤ ConcreteYF.deltaC _ _ _ _ _
  unfold ConcreteYF.deltaC ConcreteYF.deltaBase
  have : 0 ≤ K * (nu D n)⁻¹ ^ p := mul_nonneg hK (pow_nonneg (inv_nonneg.2 hpos.le) _)
  positivity

end G1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
