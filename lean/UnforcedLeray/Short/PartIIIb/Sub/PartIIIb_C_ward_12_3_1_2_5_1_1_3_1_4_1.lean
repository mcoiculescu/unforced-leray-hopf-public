import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1`: `RawProfFarJet`, decomposed

Source `the November 2 reference manuscript`
1206-1222 (`b_raw = (v₁, v₂ + εH)`, `H = (1-K)ψ`), 397 and 2049 (the train and its decaying stream
are smooth), 427-446 (all mixed age/space jets bounded at fixed parameters; stream fluctuation
jets).

`rawProfFarJet_of` proves `RawProfFarJet` (`FarOrg.lean`) from four statements, each a short
fact:

* `VelJointJetsFixed` : joint `(s, q, η)` jets of `v` of order `≤ 2` are bounded on `s > 0`
  (from `PartI.TrainJetsBoundedFixed` and `PartI.JointFromAgeJets`);
* `StreamJointJetsPoly` : joint jets of `ψ` of order `≤ 3` are `≤ C (1+|η|)^M` on `0 < s ≤ s₀`
  (`ψ = ψ̃ + ψ̄`: `PartI.TrainFluctAgeJetFixed`, `PartI.JointFromAgeJets`, `MeanStreamJetPoly`);
* `RawProfSmoothGen`, `RawProfJetGen` : generic calculus for `rawProfile`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Joint jets of the velocity** (SP 427-435 at fixed parameters, `ρ = 2`: `c = ν⁻²`): for a BUC
train with `ν ≤ ν₀` and each order `l ≤ 2` the full derivative of `(s, z) ↦ v s z` in
`(s, q, η)` is bounded on `s > 0`.  (From `PartI.TrainJetsBoundedFixed` for the mixed jets and
`PartI.JointFromAgeJets` componentwise.) -/
def VelJointJetsFixed : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∃ C : ℝ, ∀ l : ℕ, l ≤ 2 → ∀ y : ℝ × Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.v x.1 x.2) y‖ ≤ C

/-- **The mean stream `ψ̄ = S`: smooth for `s > 0` with polynomially bounded joint jets for small
age** (SP 397-404, 427-446: `S` is the horizontal average of the decaying stream; at fixed
parameters `S` is smooth up to `s = 0`, with `S(s, ·)` and its derivatives of polynomial growth in
`η`).  Joint derivatives in `(s, q, η)` of `(s, q, η) ↦ S(s, η)`. -/
def MeanStreamJetPoly : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
          (Ioi 0 ×ˢ univ) ∧
      ∃ (C s0 : ℝ) (M : ℕ), 0 < s0 ∧ ∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ s0 →
        ‖iteratedFDeriv ℝ l
            (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤
          C * (1 + |y.2.2|) ^ M

/-- **Joint jets of the stream** `ψ = ψ̃ + ψ̄` (SP 427-446): order `≤ 3` joint derivatives in
`(s, q, η)` are `≤ C (1+|η|)^M` for `0 < s ≤ s₀`. -/
def StreamJointJetsPoly : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∃ (C s0 : ℝ) (M : ℕ), 0 < s0 ∧ ∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ s0 →
        ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.ψ x.1 x.2) y‖ ≤ C * (1 + |y.2.2|) ^ M

/-- **Smoothness of the raw profile** (generic calculus; SP 1206-1222): if `v` is `C^∞` on
`s ≥ 0` and `ψ` is jointly `C^∞` on `s > 0`, then `b_raw = (v₁, v₂ + εH)`,
`H = ψ - η∂_ηψ - 2s∂_sψ` (one-variable derivatives, which are partial `fderiv`s of the joint `ψ`),
is `C^∞` on `s > 0`. -/
def RawProfSmoothGen : Prop :=
  ∀ (ε : ℝ) (v : ℝ → Plane → UnforcedLeray.Train.Vec) (ψ : ℝ → Plane → ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ici 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ψ x.1 x.2) (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile ε v ψ) {m : ℝ × (ℝ × ℝ) | 0 < m.1}

/-- **Jets of the raw profile from the jets of `v` and `ψ`** (generic calculus; SP 1206-1222):
`D^l rawProfile = D^l v + ε D^l H • e₂` with `H = ψ - η∂_ηψ - 2s∂_sψ`; the factor `η` costs
`(1+|η|)` and the factor `2s` costs `2 s₀`, so jets of `v` of order `≤ 2` bounded and jets of `ψ`
of order `≤ 3` by `C(1+|η|)^M` on `0 < s ≤ s₀` give the same for `rawProfile` (order `≤ 2`). -/
def RawProfJetGen : Prop :=
  ∀ (ε : ℝ) (v : ℝ → Plane → UnforcedLeray.Train.Vec) (ψ : ℝ → Plane → ℝ) (s0 : ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ici 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ψ x.1 x.2) (Ioi 0 ×ˢ univ) →
    (∃ Cv : ℝ, ∀ l : ℕ, l ≤ 2 → ∀ y : ℝ × Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => v x.1 x.2) y‖ ≤ Cv) →
    (∃ (Cψ : ℝ) (M : ℕ), ∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ s0 →
        ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => ψ x.1 x.2) y‖ ≤ Cψ * (1 + |y.2.2|) ^ M) →
    ∃ (C : ℝ) (M : ℕ), ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ s0 → ∀ l : ℕ, l ≤ 2 →
      ‖iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile ε v ψ) m‖ ≤ C * (1 + |m.2.2|) ^ M

theorem rawProfFarJet_of (h1 : VelJointJetsFixed) (h2 : StreamJointJetsPoly)
    (hS : RawProfSmoothGen) (hJ : RawProfJetGen) : RawProfFarJet := by
  intro dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := h1
  obtain ⟨ν2, hν2, H2⟩ := h2
  refine ⟨min ν1 ν2, lt_min hν1 hν2, ?_⟩
  intro p d hreg hν
  have hνp : 0 < p.ν := p.ν_pos
  have hc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hv := p.train.isTrain.smooth_v
  have hψ := hreg.train_stream_smooth
  refine ⟨hS p.ε p.train.v p.train.ψ hv hψ, ?_⟩
  obtain ⟨Cv, hCv⟩ := H1 p.ν p.c hνp (hν.trans (min_le_left _ _)) hc p.train hreg.train_buc
  obtain ⟨Cψ, s0, M, hs0, hCψ⟩ :=
    H2 p.ν p.c hνp (hν.trans (min_le_right _ _)) hc p.train hreg.train_buc
  obtain ⟨C, M', hC⟩ := hJ p.ε p.train.v p.train.ψ s0 hv hψ ⟨Cv, hCv⟩ ⟨Cψ, M, hCψ⟩
  exact ⟨C, s0, M', hs0, hC⟩

end UnforcedLeray.Short.PartIIIb.Concrete
