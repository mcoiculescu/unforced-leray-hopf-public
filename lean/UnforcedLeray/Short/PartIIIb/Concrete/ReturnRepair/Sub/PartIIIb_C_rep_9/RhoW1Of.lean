import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Levels

/-!
# `PartIII-b:C/rep/9/2`: `δ_U ≤ P_ν ρ` for large `n`, from the background bounds

Source `the November 2 reference manuscript` 5094 ("`δ_U ≤ P_νρ` from the
background bounds"), with `δ_U = ‖U - U_raw‖_{W^{1,∞}}` (5007-5008) and `short-bg:strong`
(2538-2541: `‖w‖_{W^{1,∞}} + ‖E_εα‖_{W^{1,∞}} ≤ 𝒫_ν e^{m/ν}ε^{3/11}`).

At an actual level the split is the contraction-ball background (`IsActualLevel.ball`, source
2505-2524, 2706-2711), and `U - U_raw = E_εα + w`.  `BgW1Levels` (`ReturnInst/Background/Levels.lean`,
`bgW1Levels_of'` from `IIb.StrongRegularity`) bounds it in `W^{1,∞}` by
`IIb.rhoB p m₀ C k = Cν^{-k}e^{m₀/ν}ε^{3/11} = Cν^{-k}ρ` (`rhoRep`, `ρ = ε^{3/11}e^{m₀/ν}`, 5138)
with `m = m₀`, the contraction condition `2m₀ < 3d₋/11` (`RepairStanding.m0_ball`, 2510-2512) and
the ball constants `C₀, k₀` of `D`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `IIb.rhoB` of a level of the sequence with exponent `m₀` is `Cν^{-k}ρ` (source 2706-2713,
5138). -/
theorem rhoB_level_eq (D : SeqData) (n : ℕ) (C : ℝ) (k : ℕ) :
    UnforcedLeray.Short.IIb.rhoB ((D.level n).params D.Pl) D.K.m0 C k =
      C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k * rhoRep D.K (D.level n) := by
  show C * (retNu D.Pl D.σ₀ n ^ k)⁻¹ * Real.exp (D.K.m0 / retNu D.Pl D.σ₀ n) *
      retEps D.Pl D.σ₀ n ^ (3 / 11 : ℝ) =
    C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k *
      (retEps D.Pl D.σ₀ n ^ (3 / 11 : ℝ) * Real.exp (D.K.m0 / retNu D.Pl D.σ₀ n))
  rw [inv_pow]
  ring

/-- **`δ_U ≤ P_ν ρ` for large `n`** (source 5094, 5007-5008, 2538-2541): under the repair standing,
the `W^{1,∞}` bound of `U - U_raw` of the background levels (`BgW1Levels`, from
`short-bg:strong`) gives `RhoW1`. -/
theorem rhoW1_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (hW : BgW1Levels) :
    D.RhoW1 := by
  obtain ⟨C, k, ν₀, -, hν₀, h⟩ := hW D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos
    hst.planar.eigenpair D.K.m0 hst.m0_pos dm dp hst.dm_pos hst.m0_ball D.K.C0 D.K.k0
    hst.C0_pos
  refine ⟨C, k, ?_⟩
  filter_upwards [hst.actual, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀)]
    with n hn hν τ y
  have hb := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.V n) (D.rb n) hn.ball τ y
  rw [rhoB_level_eq] at hb
  exact hb

end UnforcedLeray.Short.PartIIIb.Concrete
