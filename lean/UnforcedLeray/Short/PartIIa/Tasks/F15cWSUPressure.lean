import UnforcedLeray.Short.PartIIa.Sub.F15
import UnforcedLeray.Short.PartIIa.Tasks.F15cWSUPressure.Helmholtz
import UnforcedLeray.Units.B0005.Bridge.Commute
import UnforcedLeray.Units.B0411

/-!
# Part II-a, task `PartII-a:F15/3`: pressure extension (reduction)

Source of record: `the November 2 reference manuscript`, lines 1498-1500, 1548.

`wsuPressure_of` proves `WSUPressure` from one named analytic input `WSUPressureApprox`:
every phase test `Φ` is a limit, in the graph topology of `L0T ν` on `Y_2`, of tests of the form
`Ψ_n + ∇ψ_n` with `Ψ_n` a divergence-free phase test and `ψ_n` a scalar phase test (Helmholtz
splitting `Φ = curl A + ∇N`, cut off as `curl(χ_n A) + ∇(χ_n N)`).

Proved here: gradients are mapped to gradients by `μ + L0T ν` (`B0005.driftT_gradT`,
`B0005.lapT_gradT`), so a phase-solenoidal `v` kills `(μ+L0T)∇ψ`; hence `v` kills the whole
approximating sequence, and continuity of the phase pairing passes to the limit.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Input `WSUPressureApprox` (test-level Helmholtz plus cutoff, lines 1498-1500): every phase
test `Φ` is approximated, together with `L0T ν Φ`, in `Y_{2'} = Y_2`, by
`Ψ_n + ∇ψ_n` with `Ψ_n` divergence-free and `ψ_n` scalar phase tests. -/
def WSUPressureApprox : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    ∃ (Ψ : ℕ → ℝ × Space → CVec3) (ψ : ℕ → ℝ × Space → ℂ),
      (∀ n, IsPhaseTest P (Ψ n) ∧ (∀ p, ∑ j, dy j (Ψ n) p j = 0) ∧ IsPhaseTest P (ψ n)) ∧
      Tendsto (fun n => testElem P (conjExp 2) (Ψ n + gradT (ψ n))) atTop
        (𝓝 (testElem P (conjExp 2) Φ)) ∧
      Tendsto (fun n => testElem P (conjExp 2) (L0T ν (Ψ n + gradT (ψ n)))) atTop
        (𝓝 (testElem P (conjExp 2) (L0T ν Φ)))

theorem dτ_add_wp {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) : dτ (A + B) = dτ A + dτ B := by
  funext p
  simp [dτ, fderiv_add (hA p) (hB p)]

theorem radialT_add_wp {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) : radialT (A + B) = radialT A + radialT B := by
  funext p
  simp only [radialT, Pi.add_apply, dy_add hA hB, smul_add, Finset.sum_add_distrib]

theorem lapT_add_wp {P : ℝ} {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) : lapT (A + B) = lapT A + lapT B := by
  have dA : Differentiable ℝ A := hA.smooth.differentiable (by simp)
  have dB : Differentiable ℝ B := hB.smooth.differentiable (by simp)
  have h2 : ∀ j : Fin 3, dy j (dy j (A + B)) = dy j (dy j A) + dy j (dy j B) := fun j => by
    rw [dy_add dA dB j]
    exact dy_add ((hA.dy j).smooth.differentiable (by simp))
      ((hB.dy j).smooth.differentiable (by simp)) j
  funext p
  simp only [lapT, Pi.add_apply, h2, Finset.sum_add_distrib]

theorem L0T_add_wp {P : ℝ} (ν : ℝ) {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) : L0T ν (A + B) = L0T ν A + L0T ν B := by
  have dA : Differentiable ℝ A := hA.smooth.differentiable (by simp)
  have dB : Differentiable ℝ B := hB.smooth.differentiable (by simp)
  have hd : driftT (A + B) = driftT A + driftT B := by
    funext p
    simp only [driftT, Pi.add_apply, dτ_add_wp dA dB, radialT_add_wp dA dB]
    module
  simp only [L0T, nuLapT]
  rw [lapT_add_wp hA hB, hd]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

/-- `(μ + L0T ν)` maps a gradient to a gradient, so a phase-solenoidal field kills it. -/
theorem pressure_kills_gradient {P : ℝ} [Fact (0 < P)] (ν : ℝ) (μ : ℂ) {v : Yq P 2}
    (hv : IsPhaseSolenoidal v) {ψ : ℝ × Space → ℂ} (hψ : IsPhaseTest P ψ) :
    phasePair P 2 (μ • gradT ψ + L0T ν (gradT ψ)) v = 0 := by
  have e : L0T ν (gradT ψ) = gradT (driftT ψ - (1 / 2 : ℝ) • ψ) - (ν : ℝ) • gradT (lapT ψ)
      - (1 / 2 : ℝ) • gradT ψ := by
    simp only [L0T, nuLapT, B0005.driftT_gradT hψ.smooth, B0005.lapT_gradT hψ.smooth]
  have h1 : IsPhaseTest P (gradT (driftT ψ - (1 / 2 : ℝ) • ψ)) :=
    (hψ.driftT.sub (hψ.const_smul _)).gradT
  have h2 : IsPhaseTest P (gradT (lapT ψ)) := hψ.lapT.gradT
  have h3 : IsPhaseTest P (gradT ψ) := hψ.gradT
  rw [e, phasePair_add (h3.const_smul μ) (((h1.sub (h2.const_smul _)).sub (h3.const_smul _))),
    phasePair_sub (h1.sub (h2.const_smul _)) (h3.const_smul _),
    phasePair_sub h1 (h2.const_smul _), phasePair_const_smul h3,
    phasePair_real_smul h2, phasePair_real_smul h3,
    hv _ hψ, hv _ hψ.lapT, hv _ (hψ.driftT.sub (hψ.const_smul _))]
  ring

/-- **(F15/3) Pressure extension from `WSUPressureApprox`.** -/
theorem wsuPressure_of (hA : WSUPressureApprox) : WSUPressure := by
  intro P _ ν hν μ v hv H Φ hΦ
  obtain ⟨Ψ, ψ, hprop, h1, h2⟩ := hA P ν Φ hΦ
  have c1 : Tendsto (fun n => phasePair P 2 (Ψ n + gradT (ψ n)) v) atTop
      (𝓝 (phasePair P 2 Φ v)) :=
    (((phasePairing P 2).flip v).continuous.tendsto _).comp h1
  have c2 : Tendsto (fun n => phasePair P 2 (L0T ν (Ψ n + gradT (ψ n))) v) atTop
      (𝓝 (phasePair P 2 (L0T ν Φ) v)) :=
    (((phasePairing P 2).flip v).continuous.tendsto _).comp h2
  have hzero : ∀ n, μ * phasePair P 2 (Ψ n + gradT (ψ n)) v +
      phasePair P 2 (L0T ν (Ψ n + gradT (ψ n))) v = 0 := by
    intro n
    obtain ⟨hΨ, hdiv, hψn⟩ := hprop n
    have hg : IsPhaseTest P (gradT (ψ n)) := hψn.gradT
    have a1 := H (Ψ n) hΨ hdiv
    have a2 := pressure_kills_gradient ν μ hv hψn
    rw [phasePair_add (hΨ.const_smul μ) (isPhaseTest_L0T hΨ ν),
      phasePair_const_smul hΨ] at a1
    rw [phasePair_add (hg.const_smul μ) (isPhaseTest_L0T hg ν),
      phasePair_const_smul hg] at a2
    rw [L0T_add_wp ν hΨ hg, phasePair_add (isPhaseTest_L0T hΨ ν) (isPhaseTest_L0T hg ν),
      phasePair_add hΨ hg]
    linear_combination a1 + a2
  have lim : Tendsto (fun n => μ * phasePair P 2 (Ψ n + gradT (ψ n)) v +
      phasePair P 2 (L0T ν (Ψ n + gradT (ψ n))) v) atTop
      (𝓝 (μ * phasePair P 2 Φ v + phasePair P 2 (L0T ν Φ) v)) :=
    (c1.const_mul μ).add c2
  have hz : μ * phasePair P 2 Φ v + phasePair P 2 (L0T ν Φ) v = 0 := by
    have : Tendsto (fun n => μ * phasePair P 2 (Ψ n + gradT (ψ n)) v +
        phasePair P 2 (L0T ν (Ψ n + gradT (ψ n))) v) atTop (𝓝 0) := by
      simp only [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique lim this
  show phasePair P 2 (μ • Φ + L0T ν Φ) v = phasePair P 2 Φ 0
  rw [phasePair_add (hΦ.const_smul μ) (isPhaseTest_L0T hΦ ν), phasePair_const_smul hΦ, map_zero]
  exact hz

/-- **(F15/3) Test-level Helmholtz plus cutoff approximation in the `L0T` graph norm.** -/
theorem wsuPressureApprox : WSUPressureApprox := by
  intro P _ ν Φ hΦ
  have hΦm : ∀ m : Fin 3, IsPhaseTest P (fun p => Φ p m) := fun m =>
    hΦ.clm_comp (B0005.projC m)
  let B : Fin 3 → ℝ × Space → ℂ := fun m => F15c.newtonJointC (fun p => Φ p m)
  let A_c : Fin 3 → ℝ × Space → ℂ := fun i => dy (i + 1) (B (i + 2)) - dy (i + 2) (B (i + 1))
  let N : ℝ × Space → ℂ := -∑ k : Fin 3, dy k (B k)
  have hB_smooth : ∀ m, ContDiff ℝ ∞ (B m) := fun m => F15c.contDiff_newtonJointC (hΦm m)
  have hB_dy : ∀ m k, F15c.IsGoodScalar P (dy k (B m)) := fun m k =>
    F15c.isGoodScalar_dy_newtonJointC (hΦm m) k
  have hA : ∀ i, F15c.IsGoodScalar P (A_c i) := fun i =>
    (hB_dy (i + 2) (i + 1)).sub (hB_dy (i + 1) (i + 2))
  have hN : F15c.IsGoodScalar P N :=
    (F15c.IsGoodScalar.sum _ fun k _ => hB_dy k k).neg
  have hsplit : F15c.curlScalar A_c + gradT N = Φ := by
    have h1 := F15c.curlScalar_curl_add_gradT_neg_div hB_smooth
    have h2 : (fun p => WithLp.toLp 2 fun i => -lapT (B i) p) = Φ := by
      funext p
      ext i
      rw [WithLp.ofLp_toLp, congrFun (F15c.lapT_newtonJointC (hΦm i)) p, Pi.neg_apply, neg_neg]
    exact h1.trans h2
  refine ⟨fun n => F15c.curlScalar (fun m => F15c.cutS n (A_c m)),
    fun n => F15c.cutS n N, ?_, ?_⟩
  · intro n
    have ha_cut : ∀ m, IsPhaseTest P (F15c.cutS n (A_c m)) := fun m =>
      F15c.isPhaseTest_cutS (hA m) n
    refine ⟨F15c.isPhaseTest_curlScalar ha_cut,
      F15c.div_curlScalar_eq_zero (fun m => (ha_cut m).smooth),
      F15c.isPhaseTest_cutS hN n⟩
  · rw [← hsplit]
    exact F15c.tendsto_curlScalar_add_gradT_cutS ν hA hN

/-- **(F15/3) Unconditional pressure extension for weak steady Leray solutions.** -/
theorem wsuPressure : WSUPressure :=
  wsuPressure_of wsuPressureApprox

end UnforcedLeray.Short.PartIIa
