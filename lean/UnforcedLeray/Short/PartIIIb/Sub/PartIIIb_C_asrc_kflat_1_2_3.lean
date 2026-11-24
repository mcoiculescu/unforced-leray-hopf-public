import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.TrainGrowth
import UnforcedLeray.Short.PartIIIa.FullClock

/-!
# Decomposition of `TrainFlowKinetic` (source 2836-2860, 3020-3022, 3228-3251, 4440-4446)

Source: `the November 2 reference manuscript`.

The constant `C` of `TrainFlowKinetic` may depend on `ν`, the train and `FI` (it is quantified after
them), so polynomial losses in `ν` are allowed.  The age range `u ≥ 1.1/ν` is split at the end of the
core `H = IIIa.coreEnd ν b` (2836-2860):

* `TFKShort m b ν₀`: for `1.1/ν ≤ u ≤ H` the bound `‖K_c 𝒰(u,1.1/ν)w‖ ≤ C‖w‖` is the weak/long
  forward estimate (`eq:short-causal-long-forward` 3020-3022, `eq:short-causal-weak-forward`
  3081-3094) followed by the embedding `‖K_d f‖ ≤ C_m‖f‖_{X_{m,d}}` (`eq:ct-embeddings` 3228-3240);
* `TFKLong m b ν₀`: for `u ≥ H` the state at `H` is carried to the clock `b` (4440-4446) and the
  kinetic impulse estimate `eq:ct-kinetic-impulse` (3242-3251) bounds the physical kinetic norm
  `νθ‖K_{d(θ)}Zh‖₂ ≤ C_b νr‖K_{d(r)}h‖₂`, uniformly in the age.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Short range of `TrainFlowKinetic` (source 2836-2860, 3020-3022, 3081-3094, 3228-3240). -/
def TFKShort (m : ℝ) [Fact (1 < m)] (b ν₀ : ℝ) : Prop :=
  ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν : ℝ) (hν : 0 < ν), ν ≤ ν₀ →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatInstData κ ν (cOf ν) m tr),
      haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
      ∃ C : ℝ, ∀ u : ℝ, 11 / 10 / ν ≤ u → u ≤ UnforcedLeray.Short.IIIa.coreEnd ν b →
        ∀ w : Xmc (cOf ν) m, ‖kcLp (FI.ev.U u (11 / 10 / ν) w)‖ ≤ C * ‖w‖

/-- Long range of `TrainFlowKinetic` (source 3242-3251, 4440-4446). -/
def TFKLong (m : ℝ) [Fact (1 < m)] (b ν₀ : ℝ) : Prop :=
  ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν : ℝ) (hν : 0 < ν), ν ≤ ν₀ →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatInstData κ ν (cOf ν) m tr),
      haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
      ∃ C : ℝ, ∀ u : ℝ, 11 / 10 / ν ≤ u → UnforcedLeray.Short.IIIa.coreEnd ν b ≤ u →
        ∀ w : Xmc (cOf ν) m, ‖kcLp (FI.ev.U u (11 / 10 / ν) w)‖ ≤ C * ‖w‖

/-- The short range holds for all large clocks `b` (and small `ν`). -/
def TFKShortAll (m : ℝ) [Fact (1 < m)] : Prop :=
  8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ TFKShort m b ν₀

/-- The long range holds for all large clocks `b` (and small `ν`). -/
def TFKLongAll (m : ℝ) [Fact (1 < m)] : Prop :=
  8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ TFKLong m b ν₀

theorem trainFlowKinetic_of (m : ℝ) [Fact (1 < m)]
    (h1 : TFKShortAll m) (h2 : TFKLongAll m) : TrainFlowKinetic m := by
  intro h8
  obtain ⟨b₁, hS⟩ := h1 h8
  obtain ⟨b₂, hL⟩ := h2 h8
  obtain ⟨ν₁, hν₁, hS'⟩ := hS (max b₁ b₂) (le_max_left _ _)
  obtain ⟨ν₂, hν₂, hL'⟩ := hL (max b₁ b₂) (le_max_right _ _)
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro κ ν hν hle tr hbuc FI
  obtain ⟨C₁, hC₁⟩ := hS' κ ν hν (hle.trans (min_le_left _ _)) tr hbuc FI
  obtain ⟨C₂, hC₂⟩ := hL' κ ν hν (hle.trans (min_le_right _ _)) tr hbuc FI
  refine ⟨max C₁ C₂, fun u hu w => ?_⟩
  by_cases hH : u ≤ UnforcedLeray.Short.IIIa.coreEnd ν (max b₁ b₂)
  · exact (hC₁ u hu hH w).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (hC₂ u hu (not_le.mp hH).le w).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end UnforcedLeray.Short.PartIIIb.Concrete
