import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0412

/-!
# The correction graph identifies `A₀w` with the phase transpose `L₀ᵗw`

The state-space graph supplies the two distributional graph identities for `w`. Their
combination is exactly the `A₀` term in the ordinary operator relation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412

/-- The two distributional graph identities on `w ∈ X` combine to the transpose of `A₀`. -/
theorem A0_phasePair_eq_L0T_of_X {P ν : ℝ} [Fact (0 < P)]
    {w : X P ν q0E} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    phasePair P q0E (L0T ν Φ) (w : Yq P q0E) =
      phasePair P q0E Φ
        (T0X w - nuLapX w - (1 / 2 : ℂ) • (w : Yq P q0E)) := by
  have hL0 := hasPhaseOp_L0T (hasPhaseOp_nuLapX w) (hasPhaseOp_T0X w)
  exact hL0 Φ hΦ

/-- For every phase test, the pairing with the concrete `A₀w` equals the pairing of `L₀ᵗ` with
the correction. This is the graph identity used when the three operator relations are combined. -/
theorem A0_phasePair_eq_L0T (p : Params) {z : p.Z}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    phasePair p.period q0E Φ (p.A0 z) =
      phasePair p.period q0E (L0T p.ν Φ) (p.wOf z) := by
  have hx := (mem_graphSpace (P := p.period) (ν := p.ν)).1 z.2
  have hX := (mem_XGraph_iff (P := p.period) (ν := p.ν) (q := q0E)).1 hx.1
  rcases hX with ⟨hw, ha, hb⟩
  let wX : X p.period p.ν q0E := ⟨p.wOf z, hw⟩
  have hA0 : p.A0 z =
      T0X ⟨cw p.period (z : Amb p.period), hw⟩ -
        nuLapX ⟨cw p.period (z : Amb p.period), hw⟩ -
        (1 / 2 : ℂ) • (p.wOf z : Yq p.period q0E) := by
    change cT p.period (z : Amb p.period) - cΔ p.period (z : Amb p.period) -
      (1 / 2 : ℝ) • cw p.period (z : Amb p.period) = _
    rw [← hb, ← ha]
    simp only [Params.wOf]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num
  rw [hA0]
  exact (A0_phasePair_eq_L0T_of_X (P := p.period) (ν := p.ν) (w := wX) hΦ).symm

#print axioms A0_phasePair_eq_L0T

end UnforcedLeray.Cons.C03.Concrete
