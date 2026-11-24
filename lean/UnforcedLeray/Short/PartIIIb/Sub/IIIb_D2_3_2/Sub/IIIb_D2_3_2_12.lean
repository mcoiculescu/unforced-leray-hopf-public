import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# Closedness of the weak Ward equation from three pairing continuities (source 4284-4286)

`WardEqClosed` is an intersection over solenoidal tests `Φ` of zero sets of a function of `T`
built from `B.hf, B.Ef, B.Yf, B.M` (continuous linear) and the three pairings of the lifts with
phase tests.  The three lift-pairing continuities are the separated-kernel / gain-norm bounds of
source 4284-4286 (`shorter-proof-2026-11-02.tex`): a phase test has bounded spatial support, and
the lifts `velPhys`, `strPhys` are `L²` on the phase cell with norm controlled by the gain norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Continuity of `v ↦ ⟨H, 𝒩_v v⟩` on `VelG` for a phase test `H` (source 4284-4286: `VelG` lifts
to `L²` of the phase cell, `fwuB_memLp_velPhys`, with `‖velPhys v‖_{L²} ≲ ‖v‖` since the body
density `π g⁻²` is bounded below; `H` is continuous with bounded support). -/
def VelPairCont (c γ ν ε : ℝ) : Prop :=
  0 < c → 0 < ν → 0 < ε → ∀ H : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) H →
    Continuous fun v : VelG c γ ν => pairF (2 * ε * c) H (velPhys ε⁻¹ c v)

/-- Continuity of `f ↦ ⟨H, 𝒩_v f⟩` on `SrcG` (same, with the ungained measure `π s^{-3/2}dς`,
source 2683-2689, 4284-4286). -/
def SrcPairCont (c ε : ℝ) : Prop :=
  0 < c → 0 < ε → ∀ H : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) H →
    Continuous fun f : SrcG c => pairF (2 * ε * c) H (velPhys ε⁻¹ c f)

/-- Continuity of `T ↦ ⟨strPhys (T₁+T₂), ∇Φ⟩` on `StrG` for a phase test `Φ` (source 4284-4286,
2698-2700: the chart-to-physical stress lift `𝒩_T g = s g` is `L²` on the phase cell over the
support of `∇Φ`, controlled by `‖g⁻¹T₁‖_{Z_1} + ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}`). -/
def StrPairCont (c mZ ρb γ ν ε : ℝ) : Prop :=
  0 < c → 0 < ν → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
    Continuous fun T : StrG c mZ ρb γ ν =>
      stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum T)) Φ

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

theorem wardEqClosed_of (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ)
    (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hV : VelPairCont c γ ν ε) (hS : SrcPairCont c ε) (hT : StrPairCont c mZ ρb γ ν ε) :
    WardEqClosed B ε μ := by
  have hset : {T : StrG c mZ ρb γ ν | WardHEquationAt B ε μ T} =
      ⋂ Φ : ℝ × Space → CVec3, {T | IsSolTest (2 * ε * c) Φ → 
        pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) =
          pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
            stressPair (2 * ε * c)
              (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ} := by
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  unfold WardEqClosed
  rw [hset]
  refine isClosed_iInter fun Φ => ?_
  by_cases hΦ : IsSolTest (2 * ε * c) Φ
  · have hL : IsPhaseTest (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) :=
      (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul (μ : ℂ))
    have c1 : Continuous fun T : StrG c mZ ρb γ ν =>
        pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) :=
      (hV hc hν hε _ hL).comp B.hf.continuous
    have c2 : Continuous fun T : StrG c mZ ρb γ ν =>
        pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) :=
      (hS hc hε _ hΦ.1).comp B.Ef.continuous
    have c3 : Continuous fun T : StrG c mZ ρb γ ν =>
        stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ :=
      (hT hc hν hε Φ hΦ.1).comp (B.M.continuous.comp (B.Yf.continuous.add B.hf.continuous))
    have : {T : StrG c mZ ρb γ ν | IsSolTest (2 * ε * c) Φ →
        pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) =
          pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
            stressPair (2 * ε * c)
              (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ} =
        {T | pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) =
          pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
            stressPair (2 * ε * c)
              (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ} := by
      ext T
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h hΦ, fun h _ => h⟩
    rw [this]
    exact isClosed_eq c1 (c2.add c3)
  · have : {T : StrG c mZ ρb γ ν | IsSolTest (2 * ε * c) Φ →
        pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) =
          pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
            stressPair (2 * ε * c)
              (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ} = Set.univ := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fun h => absurd h hΦ
    rw [this]
    exact isClosed_univ

end UnforcedLeray.Short.PartIIIb.Concrete
