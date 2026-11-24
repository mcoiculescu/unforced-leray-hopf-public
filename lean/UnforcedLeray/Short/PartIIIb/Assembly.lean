import UnforcedLeray.Short.PartIIIb.StatementsA
import UnforcedLeray.Short.PartIIIb.Compose
import UnforcedLeray.Short.PartIIIb.WardProofs

/-!
# Spectral assembly (lines 5776-5985): the closing argument for the phase-locked sequence

`spectral_assembly` is the source's argument of lines 5888-5985 at the level of its steps:
the sequence of regimes `S` (phase-locked viscosities, `μ = μ_n(z)`) satisfies the identities of
the Ward and affine modules (`ReturnOps` predicates), the operators are norm continuous in `z`
(line 5905-5909), and the two asymptotic inputs of `closure:mixed-return` hold:

* `HSmall` : `r_n + h_n → 0` (second error of line 5902-5904), with
  `R_n = L𝒫 - a_μ Λ_{μ,ν}` (line 5893);
* `GainConv` : `Λ_{μ_n(z),ν_n}(a_{μ_n(z)}) → e^{-z}` uniformly on `[-1,1]` (lines 5960-5972).

Conclusion (lines 5975-5985): for every large `n` there is `z_n ∈ (-1,1)`, `z_n → 0`, and a nonzero
`T'` with `D T' = 0`, `b = -S T'`, `T' = M b`, `b ≠ 0`.  The hypotheses `HSmall`, `GainConv`
are derived from the module results in tasks `T_hsmall`, `T_gain` (see `Statements.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- `R = L𝒫 - a_μ Λ_{μ,ν}` (line 5893), so that `K = L𝒫 = a ℓ + R`. -/
def Rdef {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) : Aff →L[ℝ] Aff :=
  o.Lg ∘L o.P - o.Lam.smulRight o.aMu

/-- Operator-norm continuity in the real parameter `z` for fixed geometry (lines 5905-5909). -/
def ReturnNormContinuity (S : ReturnSeq) : Prop :=
  ∀ n, ContinuousOn (fun z => (S.ops n z).P) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).Lg) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).Q) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).aMu) (Icc (-1) 1) ∧
    ContinuousOn (fun z => (S.ops n z).Lam) (Icc (-1) 1)

/-- `r_n + h_n → 0` (lines 5744-5746, 5900-5904). -/
def HSmall (S : ReturnSeq) : Prop :=
  Tendsto (fun n => (⨆ z : Icc (-1 : ℝ) 1, ‖Rdef (S.ops n z)‖) +
      (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Lg‖ * ‖(S.ops n z).Q ∘L (S.ops n z).P‖) /
        (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖)) atTop (𝓝 0)

/-- `Λ a → e^{-z}` uniformly on `[-1,1]` (lines 5960-5972). -/
def GainConv (S : ReturnSeq) : Prop :=
  TendstoUniformlyOn (fun n z => (S.ops n z).Lam (S.ops n z).aMu) (fun z => Real.exp (-z))
    atTop (Icc (-1 : ℝ) 1)

/-- The conclusion of the spectral assembly (lines 5975-5985). -/
def EnergyModes (S : ReturnSeq) : Prop :=
  ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 0) ∧ ∀ᶠ n in atTop, z n ∈ Ioo (-1 : ℝ) 1 ∧
    ∃ (T' : S.Str n) (b : S.Vel n), T' ≠ 0 ∧ (S.ops n (z n)).D T' = 0 ∧
      b = -((S.ops n (z n)).S T') ∧ T' = (S.ops n (z n)).M b ∧ b ≠ 0

/-- The closing argument (lines 5888-5985) from `closure:mixed-return`. -/
theorem spectral_assembly (hMR : MixedReturnLemma) (S : ReturnSeq)
    (hN : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (S.ops n z).IsNearInverse)
    (hG : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (S.ops n z).IsGraphLift)
    (hW : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (S.ops n z).WardStressNormal)
    (hA : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (S.ops n z).PhysAffineIdentity)
    (hH : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (S.ops n z).HNilpotent)
    (hcont : ReturnNormContinuity S) (N : ℕ) (M : ℝ)
    (hM : ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ‖(S.ops n z).aMu‖ * ‖(S.ops n z).Lam‖ ≤ M)
    (hC : ∀ n ≥ N, (⨆ z : Icc (-1 : ℝ) 1, ‖(S.ops n z).Q‖) < 1)
    (hsmall : HSmall S) (hgain : GainConv S) : EnergyModes S := by
  -- shift the sequence by `N`
  have hRcont : ∀ n, ContinuousOn (fun z => Rdef (S.ops n z)) (Icc (-1) 1) := by
    intro n
    obtain ⟨cP, cLg, -, ca, cl⟩ := hcont n
    have h1 : ContinuousOn (fun z => (S.ops n z).Lg ∘L (S.ops n z).P) (Icc (-1) 1) :=
      cLg.clm_comp cP
    have h2 : ContinuousOn (fun z => (S.ops n z).Lam.smulRight (S.ops n z).aMu) (Icc (-1) 1) :=
      ((ContinuousLinearMap.smulRightL ℝ (S.Aff n) (S.Aff n)).continuous₂.comp_continuousOn
        (cl.prodMk ca))
    exact h1.sub h2
  obtain ⟨z, hz0, hz⟩ := energy_modes_of_blocks hMR
    (Vel := fun n => S.Vel (n + N)) (Str := fun n => S.Str (n + N))
    (Src := fun n => S.Src (n + N)) (Aff := fun n => S.Aff (n + N)) (Gam := fun n => S.Gam (n + N))
    (fun n z => S.ops (n + N) z)
    (fun n z hz => hN _ z hz) (fun n z hz => hG _ z hz) (fun n z hz => hW _ z hz)
    (fun n z hz => hA _ z hz) (fun n z hz => hH _ z hz)
    (fun n z => Rdef (S.ops (n + N) z)) M
    (fun n z _ => by simp [Rdef])
    (fun n => (hcont (n + N)).1) (fun n => (hcont (n + N)).2.1) (fun n => (hcont (n + N)).2.2.1)
    (fun n => (hcont (n + N)).2.2.2.1) (fun n => (hcont (n + N)).2.2.2.2)
    (fun n => hRcont (n + N))
    (fun n z hz => hM (n + N) (Nat.le_add_left _ _) z hz)
    (fun n => hC (n + N) (Nat.le_add_left _ _))
    ((tendsto_add_atTop_iff_nat N).mpr hsmall)
    (by
      unfold GainConv at hgain
      rw [Metric.tendstoUniformlyOn_iff] at hgain ⊢
      intro ε hε
      exact (tendsto_add_atTop_nat N).eventually (hgain ε hε))
  refine ⟨fun n => if h : N ≤ n then z (n - N) else 0, ?_, ?_⟩
  · have h1 : Tendsto (fun n => z (n - N)) atTop (𝓝 0) :=
      hz0.comp (tendsto_sub_atTop_nat N)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [hn]
  · rw [eventually_atTop] at hz ⊢
    obtain ⟨K, hK⟩ := hz
    refine ⟨K + N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
    have hmK : K ≤ m := by omega
    have := hK m hmK
    have hN' : N ≤ m + N := Nat.le_add_left _ _
    simpa [hN'] using this

end UnforcedLeray.Short.PartIIIb
