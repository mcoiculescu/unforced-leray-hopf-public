import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.Step.Helpers
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.XGjIntegral
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.LogKernel

/-!
# Spine: `MildLevelStep`, the one-derivative gain (leaf 6 of task `Spine:SP-CAN/4/1`)

Target: `UnforcedLeray.Short.Spine.MildLevelStep` (`Short/Spine/Sub/SP_CAN4_1.lean`): under
`GreenAll`, a mild solution `V` with `MildLevel V j` has `MildLevel V (j+1)`.

Source of record: `the November 2 reference manuscript`, lines 1086 and 1134-1145.

Proof. Fix `θ > 0`, `θ' = e θ` (`e = exp 1`). The Duhamel form of the mild identity
(`MildLevelStepHelp.mild_decomp`) gives
`V θ = e^{D} V θ' + ∫_θ^{θ'} e^{(log v - log θ) D} L₀ (V v) dv`.
* The first term is in `X_{G,j+1}` with `xgjNorm (j+1) ≤ xgjNorm j (V θ') ≤ K`
  (`B0123.expD_smoothing`, `a = 1`).
* For `v ∈ (θ, θ']`, `a = log v - log θ ∈ (0, 1]`, `L₀ (V v) ∈ X_{G,j}` with
  `xgjNorm j ≤ C_L K`, hence the integrand is in `X_{G,j+1}` with norm `≤ a^{-1/2} C_L K`.
  Its integral is in `X_{G,j+1}` (`xgjIntervalIntegralMem_proof`) with norm
  `≤ 5 θ C_L K` (`logKernelIntegral_proof`).
* The triangle inequality (`MildLevelStepHelp.xgjNorm_add_le`) gives
  `xgjNorm (j+1) (V θ) ≤ K + 5 θ C_L K`, where `K` bounds `xgjNorm j` on `[θ, eθ]`.

For a compact `[α, β] ⊂ (0, ∞)` the bound `K` is taken on `[α, eβ]`, which contains `[θ, eθ]` for
every `θ ∈ [α, β]`; this gives the local bound `K + 5 β C_L K`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- `θ ≤ e θ` for `θ > 0`. -/
theorem le_exp_mul_self {θ : ℝ} (hθ : 0 < θ) : θ ≤ Real.exp 1 * θ := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  nlinarith

/-- The pointwise step: the bound at `θ` in `X_{G,j+1}` from a bound `K` of the `X_{G,j}` graph
norm on `[θ, eθ]`. -/
theorem pointwise_step {V : ℝ → XG} (hV : IsMildOnPos V) (j : ℕ) {CL : ℝ} (hCL0 : 0 ≤ CL)
    (hCL : ∀ f : XG, ∀ hf : f ∈ B0123.XGj j, ∃ hL : B0012.L0 f ∈ B0123.XGj j,
      B0123.xgjNorm j ⟨B0012.L0 f, hL⟩ ≤ CL * B0123.xgjNorm j ⟨f, hf⟩)
    (hVj : ∀ s : ℝ, 0 < s → V s ∈ B0123.XGj j) {θ K : ℝ} (hθ : 0 < θ)
    (hbd : ∀ s ∈ Icc θ (Real.exp 1 * θ), ∀ h : V s ∈ B0123.XGj j,
      B0123.xgjNorm j ⟨V s, h⟩ ≤ K) :
    ∃ h : V θ ∈ B0123.XGj (j + 1), B0123.xgjNorm (j + 1) ⟨V θ, h⟩ ≤ K + 5 * θ * (CL * K) := by
  have hθθ' : θ ≤ Real.exp 1 * θ := le_exp_mul_self hθ
  have hθ' : 0 < Real.exp 1 * θ := lt_of_lt_of_le hθ hθθ'
  have hlog : Real.log (Real.exp 1 * θ) - Real.log θ = 1 := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hθ.ne', Real.log_exp]
    ring
  have hVθ0 : V θ ∈ B0123.XGj j := hVj θ hθ
  have hV' : V (Real.exp 1 * θ) ∈ B0123.XGj j := hVj _ hθ'
  have hK0 : 0 ≤ K :=
    (B0123.xgjNorm_nonneg j ⟨V θ, hVθ0⟩).trans (hbd θ ⟨le_rfl, hθθ'⟩ hVθ0)
  have hKθ' : B0123.xgjNorm j ⟨V (Real.exp 1 * θ), hV'⟩ ≤ K :=
    hbd _ ⟨hθθ', le_rfl⟩ hV'
  -- the first term: one derivative gain at `a = 1`
  obtain ⟨h1, hn1⟩ := B0123.expD_smoothing j (a := 1) one_pos le_rfl ⟨V (Real.exp 1 * θ), hV'⟩
  have h1' : B0123.expD 1 (V (Real.exp 1 * θ)) ∈ B0123.XGj (j + 1) := h1
  have hn1' : B0123.xgjNorm (j + 1) ⟨B0123.expD 1 (V (Real.exp 1 * θ)), h1'⟩ ≤
      B0123.xgjNorm j ⟨V (Real.exp 1 * θ), hV'⟩ := by
    have e : (1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := Real.one_rpow _
    rw [e, one_mul] at hn1
    exact hn1
  -- the Duhamel decomposition on `[θ, eθ]`
  have hdec := MildLevelStepHelp.mild_decomp hV hθ hθθ'
  rw [hlog] at hdec
  -- continuity of the integrand on `[θ, eθ]`
  have hcontV : ContinuousOn V (Icc θ (Real.exp 1 * θ)) := by
    have hc := continuousOn_S_left (ε := θ) (θ₁ := Real.exp 1 * θ) hθ (V (Real.exp 1 * θ))
    exact hc.congr (fun v hv => hV v (Real.exp 1 * θ) (lt_of_lt_of_le hθ hv.1) hv.2)
  have hcontF : ContinuousOn (fun v => B0012.L0 (V v)) (Icc θ (Real.exp 1 * θ)) :=
    B0012.L0.continuous.comp_continuousOn hcontV
  have hIF : IntervalIntegrable
      (fun v => B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v))) volume θ
        (Real.exp 1 * θ) :=
    CanonicalMild.intervalIntegrable_expD_log hθ hθθ' hcontF
  -- the Duhamel kernel is integrable with integral at most `5θ`
  have hLK : LogKernelIntegral := logKernelIntegral_proof
  obtain ⟨hKerInt, hKerBd⟩ := hLK θ hθ
  have hGInt : IntervalIntegrable
      (fun v => (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ)) * (CL * K)) volume θ
        (Real.exp 1 * θ) :=
    hKerInt.mul_const (CL * K)
  -- the pointwise majorant of the integrand
  have hmaj : ∀ᵐ u ∂volume, u ∈ Ioc θ (Real.exp 1 * θ) →
      ∃ h : B0123.expD (Real.log u - Real.log θ) (B0012.L0 (V u)) ∈ B0123.XGj (j + 1),
        B0123.xgjNorm (j + 1) ⟨B0123.expD (Real.log u - Real.log θ) (B0012.L0 (V u)), h⟩ ≤
          (Real.log u - Real.log θ) ^ (-(1 / 2 : ℝ)) * (CL * K) := by
    refine ae_of_all _ (fun u hu => ?_)
    obtain ⟨hu1, hu2⟩ := hu
    have hu0 : 0 < u := lt_trans hθ hu1
    have hVu : V u ∈ B0123.XGj j := hVj u hu0
    have hKu : B0123.xgjNorm j ⟨V u, hVu⟩ ≤ K := hbd u ⟨hu1.le, hu2⟩ hVu
    obtain ⟨hLV, hLVb⟩ := hCL (V u) hVu
    have hLVK : B0123.xgjNorm j ⟨B0012.L0 (V u), hLV⟩ ≤ CL * K :=
      hLVb.trans (mul_le_mul_of_nonneg_left hKu hCL0)
    have ha : 0 < Real.log u - Real.log θ := sub_pos.mpr (Real.log_lt_log hθ hu1)
    have ha1 : Real.log u - Real.log θ ≤ 1 := by
      have := Real.log_le_log hu0 hu2
      linarith
    obtain ⟨h2, hn2⟩ := B0123.expD_smoothing j ha ha1 ⟨B0012.L0 (V u), hLV⟩
    refine ⟨h2, hn2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left hLVK (Real.rpow_nonneg ha.le _)
  -- the integral stays in `X_{G,j+1}`
  obtain ⟨hI, hIb⟩ := xgjIntervalIntegralMem_proof (j + 1) _ _ θ (Real.exp 1 * θ) hθθ' hIF
    hGInt hmaj
  have hI' : (∫ v in θ..(Real.exp 1 * θ),
      B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v))) ∈ B0123.XGj (j + 1) := hI
  have hIb' : B0123.xgjNorm (j + 1)
      ⟨∫ v in θ..(Real.exp 1 * θ), B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v)), hI'⟩ ≤
        5 * θ * (CL * K) := by
    have hG : (∫ v in θ..(Real.exp 1 * θ),
        (Real.log v - Real.log θ) ^ (-(1 / 2 : ℝ)) * (CL * K)) ≤ 5 * θ * (CL * K) := by
      rw [intervalIntegral.integral_mul_const]
      exact mul_le_mul_of_nonneg_right hKerBd (mul_nonneg hCL0 hK0)
    exact hIb.trans hG
  -- membership of `V θ` and the triangle inequality
  have hVθ : V θ ∈ B0123.XGj (j + 1) := by
    rw [hdec]
    exact Submodule.add_mem _ h1' hI'
  refine ⟨hVθ, ?_⟩
  have htri := MildLevelStepHelp.xgjNorm_add_le (j + 1)
    (B0123.expD 1 (V (Real.exp 1 * θ)))
    (∫ v in θ..(Real.exp 1 * θ), B0123.expD (Real.log v - Real.log θ) (B0012.L0 (V v)))
    (V θ) h1' hI' hVθ hdec
  linarith [htri, hn1', hKθ', hIb']

/-- **Leaf 6, the one-derivative gain** (`Sub/SP_CAN4_1.lean`, `MildLevelStep`): under `GreenAll`,
a mild solution with `MildLevel V j` has `MildLevel V (j+1)`. -/
theorem mildLevelStep_proof : UnforcedLeray.Short.Spine.MildLevelStep := by
  intro hE V hV j hj
  obtain ⟨CL, hCL0, hCL⟩ := MildLevelStepHelp.L0_xgj j (hE j)
  unfold MildLevel at hj ⊢
  obtain ⟨hj1, hj2⟩ := hj
  have hVj : ∀ s : ℝ, 0 < s → V s ∈ B0123.XGj j := hj1
  refine ⟨fun s hs => ?_, fun α β hα hαβ => ?_⟩
  · obtain ⟨K, hK⟩ := hj2 s (Real.exp 1 * s) hs (le_exp_mul_self hs)
    obtain ⟨h, -⟩ := pointwise_step hV j hCL0 hCL hVj hs hK
    exact h
  · have hαeβ : α ≤ Real.exp 1 * β := hαβ.trans (le_exp_mul_self (lt_of_lt_of_le hα hαβ))
    obtain ⟨K, hK⟩ := hj2 α (Real.exp 1 * β) hα hαeβ
    have hK0 : 0 ≤ K :=
      (B0123.xgjNorm_nonneg j ⟨V α, hVj α hα⟩).trans (hK α ⟨le_rfl, hαeβ⟩ (hVj α hα))
    refine ⟨K + 5 * β * (CL * K), fun s hs h => ?_⟩
    have hs0 : 0 < s := lt_of_lt_of_le hα hs.1
    obtain ⟨h', hb⟩ := pointwise_step hV j hCL0 hCL hVj hs0 (fun u hu h0 =>
      hK u ⟨hs.1.trans hu.1, hu.2.trans (mul_le_mul_of_nonneg_left hs.2 (Real.exp_pos 1).le)⟩ h0)
    have hb' : B0123.xgjNorm (j + 1) ⟨V s, h⟩ ≤ K + 5 * s * (CL * K) := hb
    have hsβ : s * (CL * K) ≤ β * (CL * K) :=
      mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hCL0 hK0)
    linarith [hb', hsβ]

end UnforcedLeray.Short.Spine
