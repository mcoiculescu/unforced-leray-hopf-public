import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Closed.RealPairPh
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3

/-!
# `PartIII-b:C/near/pins/5/4`: `SWClosed` (source 3888-3890)

The weak equation passes to `Z`-limits: `Seps` is continuous, the velocity pairing against a phase
test is a bounded functional on `H` (`realPairFunctionalPh`, the copy of `realPairFunctional` for
arbitrary phase tests, the divergence-free clause being unused), and the stress pairing
`F ↦ ⟨𝒩_T zsum F, ∇Φ⟩` is continuous on `Z` (`strPairCont_proved` at `γ = 0`, `ν = 1`, where the
gain weight is `1` and `StrG` is `Z`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sw_stress_cont (c mZ ρb ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest (2 * ε * c) Φ) :
    Continuous fun F : Zsp c mZ ρb => stressPair (2 * ε * c) (strPhys ε⁻¹ c (zsum F)) Φ := by
  have h := strPairCont_proved c mZ ρb 0 1 ε hc one_pos hε Φ hΦ
  have hg : (fun p : Chart => ENNReal.ofReal (ginv 0 1 p ^ 2)) = fun _ => 1 := by
    funext p
    simp [ginv, UnforcedLeray.Short.IIIa.gainG]
  have hZ : gainZ1Measure c mZ 0 1 = z1Measure c mZ := by
    unfold gainZ1Measure
    rw [hg]
    exact withDensity_one
  have hH : gainHTMeasure c ρb 0 1 = htRhoMeasure c ρb := by
    unfold gainHTMeasure
    rw [hg]
    exact withDensity_one
  have key : ∀ m1 m2 : Measure Chart, m1 = gainZ1Measure c mZ 0 1 →
      m2 = gainHTMeasure c ρb 0 1 →
      Continuous fun T : WithLp 1 (Lp (α := Chart) Ten3 2 m1 × Lp (α := Chart) Ten3 2 m2) =>
        stressPair (2 * ε * c) (strPhys ε⁻¹ c
          (fun p => (T.fst : Chart → Ten3) p + (T.snd : Chart → Ten3) p)) Φ := by
    intro m1 m2 h1 h2
    subst h1 h2
    exact h
  exact key _ _ hZ.symm hH.symm

theorem swClosed : SWClosed := by
  intro hyp p μ mZ ρb hmZ hρ Seps Fs F vs v hFs hvs hv hwn
  have hP : 0 < 2 * p.ε * p.c := by
    have := p.ε_pos; have := p.c_pos; positivity
  have hS : Tendsto (fun n => Seps (Fs n)) atTop (𝓝 (Seps F)) :=
    (Seps.continuous.tendsto F).comp hFs
  have hlim : ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest (2 * p.ε * p.c) Ψ →
      Tendsto (fun n => pairF (2 * p.ε * p.c) Ψ (velPhys p.ε⁻¹ p.c (vs n))) atTop
        (𝓝 (pairF (2 * p.ε * p.c) Ψ (velPhys p.ε⁻¹ p.c v))) := by
    intro Ψ hΨ
    obtain ⟨L, hL⟩ := realPairFunctionalPh p.c p.ε p.c_pos p.ε_pos Ψ hΨ
    have e1 : ∀ n, pairF (2 * p.ε * p.c) Ψ (velPhys p.ε⁻¹ p.c (vs n)) = L (Seps (Fs n)) :=
      fun n => (hL _ (vs n) (hvs n)).symm
    have e2 : pairF (2 * p.ε * p.c) Ψ (velPhys p.ε⁻¹ p.c v) = L (Seps F) :=
      (hL _ v hv).symm
    simp only [e1, e2]
    exact (L.continuous.tendsto _).comp hS
  refine ⟨?_, ?_⟩
  · intro φ hφ
    have h1 := hlim _ hφ.gradT
    have h3 : Tendsto (fun n => pairF (2 * p.ε * p.c) (gradT φ)
        (velPhys p.ε⁻¹ p.c (vs n))) atTop (𝓝 0) := by
      have h0 : ∀ n, pairF (2 * p.ε * p.c) (gradT φ) (velPhys p.ε⁻¹ p.c (vs n)) = 0 :=
        fun n => (hwn n).solenoidal φ hφ
      simp only [h0]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h3
  · intro Φ hΦ
    have hL : IsPhaseTest (2 * p.ε * p.c) (L0T p.ν Φ) :=
      (hΦ.1.driftT.sub (hΦ.1.lapT.const_smul (p.ν))).sub (hΦ.1.const_smul (1 / 2 : ℝ))
    have hΨ : IsPhaseTest (2 * p.ε * p.c) (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x) :=
      hL.add (hΦ.1.const_smul (μ : ℂ))
    have h1 := hlim _ hΨ
    have h2 : Tendsto (fun n => -stressPair (2 * p.ε * p.c)
        (strPhys p.ε⁻¹ p.c (zsum (Fs n))) Φ) atTop
        (𝓝 (-stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum F)) Φ)) :=
      (((sw_stress_cont p.c mZ ρb p.ε p.c_pos p.ε_pos Φ hΦ.1).tendsto F).comp hFs).neg
    have h3 : ∀ n, pairF (2 * p.ε * p.c) (fun x => L0T p.ν Φ x + (μ : ℂ) • Φ x)
        (velPhys p.ε⁻¹ p.c (vs n)) =
        -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum (Fs n))) Φ :=
      fun n => (hwn n).equation Φ hΦ
    exact tendsto_nhds_unique h1 (h2.congr (fun n => (h3 n).symm))

end UnforcedLeray.Short.PartIIIb.NearInst
