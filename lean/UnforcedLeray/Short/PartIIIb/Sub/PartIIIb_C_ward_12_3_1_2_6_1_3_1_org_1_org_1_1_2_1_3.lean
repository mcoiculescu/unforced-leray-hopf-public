import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_2_1

/-!
# `heatDuhamelWeightedRemainder` from four generic heat-kernel leaves

Source `the November 2 reference manuscript`
455-458 and proof 527-551.  Leaves: weighted heat-kernel jet bound (used inside 535-551);
datum part (Taylor expansion of `G_{nu s}(eta - xi)` with even moments, 527-540);
source part (split at `t = s/2`, 541-551); additivity of the nested jets of the two parts.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub

open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartIIIb.Concrete

/-- The nested jet `partial_eta^b partial_s^l F` evaluated at `(s, eta)`. -/
def jet (F : ℝ → ℝ → ℝ) (b ℓ : ℕ) (s η : ℝ) : ℝ :=
  iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => F r e) s) η

/-- Hypotheses on the source `g` (SP 399, 543-545): smooth for `t > 0`, even, weighted mixed jets
decay like `e^{-kappa t}`. -/
def SourceHyp (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ) ∧
  (∀ t : ℝ, 0 < t → ∀ η : ℝ, g t (-η) = g t η) ∧
  (∀ k b ℓ : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 < t → ∀ η : ℝ,
        (1 + |η|) ^ k * ‖iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => g r e) t) η‖ ≤
          C * Real.exp (-(κ * t)))

/-- Hypotheses on the datum `S0` (SP 543-545): even, all even moments integrable. -/
def DatumHyp (S0 : ℝ → ℝ) : Prop :=
  (∀ η : ℝ, S0 (-η) = S0 η) ∧
  (∀ j : ℕ, Integrable (fun η : ℝ => η ^ (2 * j) * S0 η) volume)

/-- **Leaf 1: weighted heat-kernel jet bound** (SP 535-537: scaling of `G_{nu s}`;
`(1+|eta|)^m |partial_eta^b partial_s^l G_{nu s}(eta)| <= C s^{(m-b-1)/2-l}` for `s >= 1`). -/
def HeatKernelWeightedBound : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ m b ℓ : ℕ, ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
    (1 + |η|) ^ m * ‖jet (fun r e => heatKernel1 (ν * r) e) b ℓ s η‖ ≤
      C * s ^ ((((m : ℝ) - (b : ℝ)) - 1) / 2 - ℓ)

/-- **Leaf 2: datum part of the remainder** (SP 527-540: Taylor expansion of
`G_{nu s}(eta - xi)` through order `2N+1`, odd moments vanish by evenness, remainder by the
moment of order `2N+2`). -/
def DatumRemainderBound : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ S0 : ℝ → ℝ, DatumHyp S0 → ∀ N m b ℓ : ℕ, ∃ C : ℝ,
    ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      (1 + |η|) ^ m * ‖jet (genRemainder ν S0 (fun _ _ => 0) N) b ℓ s η‖ ≤
        C * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ)

/-- **Leaf 3: source part of the remainder** (SP 541-551: split of the Duhamel integral at
`t = s/2`; joint Taylor expansion in `(xi, t)` for `t <= s/2` using `d_t G = nu d_eta^2 G`; for
`t >= s/2` derivatives are moved onto the exponentially decaying source). -/
def SourceRemainderBound : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ g : ℝ → ℝ → ℝ, SourceHyp g → ∀ N m b ℓ : ℕ, ∃ C : ℝ,
    ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
      (1 + |η|) ^ m * ‖jet (genRemainder ν (fun _ => 0) g N) b ℓ s η‖ ≤
        C * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ)

/-- **Leaf 4: additivity of the remainder jets** (`genDuhamel` and `genCoeff` are additive in
`(S0, g)` because the Gaussian-weighted integrands are integrable under the moment/decay
hypotheses; `genDuhamel` is smooth in `(s, eta)` for `s > 0`, differentiation under the integral,
the boundary term at `t = s` being the smooth source). -/
def RemainderJetSplit : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (S0 : ℝ → ℝ) (g : ℝ → ℝ → ℝ), DatumHyp S0 → SourceHyp g →
    ∀ N b ℓ : ℕ, ∀ s : ℝ, 0 < s → ∀ η : ℝ,
      jet (genRemainder ν S0 g N) b ℓ s η =
        jet (genRemainder ν S0 (fun _ _ => 0) N) b ℓ s η +
          jet (genRemainder ν (fun _ => 0) g N) b ℓ s η

theorem heatDuhamelWeightedRemainder_of (h2 : DatumRemainderBound) (h3 : SourceRemainderBound)
    (h4 : RemainderJetSplit) : HeatDuhamelWeightedRemainder := by
  intro ν hν S0 g hev hmom hsm hge hdec N m b ℓ
  have hD : DatumHyp S0 := ⟨hev, hmom⟩
  have hS : SourceHyp g := ⟨hsm, hge, hdec⟩
  obtain ⟨C2, hC2⟩ := h2 ν hν S0 hD N m b ℓ
  obtain ⟨C3, hC3⟩ := h3 ν hν g hS N m b ℓ
  refine ⟨C2 + C3, fun s hs η => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hsp : 0 ≤ s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ) := Real.rpow_nonneg hs0.le _
  have e : iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => genRemainder ν S0 g N r e) s) η =
      jet (genRemainder ν S0 (fun _ _ => 0) N) b ℓ s η +
        jet (genRemainder ν (fun _ => 0) g N) b ℓ s η := h4 ν hν S0 g hD hS N b ℓ s hs0 η
  rw [e]
  have hw : 0 ≤ (1 + |η|) ^ m := by positivity
  calc (1 + |η|) ^ m * ‖jet (genRemainder ν S0 (fun _ _ => 0) N) b ℓ s η +
          jet (genRemainder ν (fun _ => 0) g N) b ℓ s η‖
      ≤ (1 + |η|) ^ m * (‖jet (genRemainder ν S0 (fun _ _ => 0) N) b ℓ s η‖ +
          ‖jet (genRemainder ν (fun _ => 0) g N) b ℓ s η‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ = (1 + |η|) ^ m * ‖jet (genRemainder ν S0 (fun _ _ => 0) N) b ℓ s η‖ +
          (1 + |η|) ^ m * ‖jet (genRemainder ν (fun _ => 0) g N) b ℓ s η‖ := by ring
    _ ≤ C2 * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ) +
          C3 * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ) :=
        add_le_add (hC2 s hs η) (hC3 s hs η)
    _ = (C2 + C3) * s ^ ((((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub
