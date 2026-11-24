import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **Sub-lemma 1** (source 4229-4258, 4178-4186): the Ward field `h = [U, X]` is weakly
solenoidal, because `X` is (`∂_rΨ_Z = rZ_z`, `∂_zΨ_Z = -rZ_r`, the outward stream function of
`wardStreamCut`/`outPrim`) and `h = [U, X]` is the Lie bracket of the solenoidal pair `U, X`
with `div U = 0` (`IsExactProfile`). -/
def WardHSolenoidal (B : ReturnBase c mZ ρb γ ν Aff) (ε : ℝ) : Prop :=
  ∀ T : StrG c mZ ρb γ ν, IsWeakSolenoidal (2 * ε * c) (velPhys ε⁻¹ c (B.hf T))

/-- **Sub-lemma 2** (source 4260-4282, `ward:physical-identity` 4268-4270): the weak form of
`D_μh + ℙ div M_Uh = -ℙ div M_UY + ℙẼ_μ`: for every solenoidal phase test `Φ`,
`⟨D_μᵗΦ, h⟩ = ⟨Φ, Ẽ_μ⟩ + ⟨M_U(Y+h), ∇Φ⟩` (`⟨div T, Φ⟩ = -stressPair T Φ`). -/
def WardHEquation (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) : Prop :=
  ∀ (T : StrG c mZ ρb γ ν) (Φ : ℝ × Space → CVec3), IsSolTest (2 * ε * c) Φ →
    pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) =
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
        stressPair (2 * ε * c)
          (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ

theorem wardEnergyEquation_of_parts {ε μ : ℝ} (B : ReturnBase c mZ ρb γ ν Aff)
    (hAdd : WeakDmuAdd c γ ν ε μ) (hS : IsStressInverse B ε μ)
    (h1 : WardHSolenoidal B ε) (h2 : WardHEquation B ε μ) :
    WardEnergyEquation B ε μ := by
  intro T
  have hh : IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c (B.hf T))
      (fun Φ => pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
        stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ) :=
    ⟨h1 T, fun Φ hΦ => h2 T Φ hΦ⟩
  have hs := hS (B.M (B.Yf T + B.hf T))
  have := hAdd _ _ _ _ hh hs
  have hr : ((fun Φ => pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
        stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ) +
      fun Φ => -stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ) =
      fun Φ => pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) := by
    funext Φ
    simp only [Pi.add_apply]
    ring
  rw [hr] at this
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete
