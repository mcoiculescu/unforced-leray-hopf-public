import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphA0
import UnforcedLeray.Units.B0411
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctionalDual.SolDiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlHelpers

/-!
# `GEWeak`: weak differentiation of the projected equation (source 2533-2537)

Task `PartIII-b:C/ward/12/3/1/2/1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

/-- Divergence commutes with `∂_i` on solenoidal tests: `∂_iΦ` is solenoidal. -/
theorem gEW_isSolTest_dy {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest P Φ) (j : Fin 3) :
    IsSolTest P (dy j Φ) := by
  have hC : ContDiff ℝ ∞ Φ := hΦ.1.smooth
  refine ⟨hΦ.1.dy j, fun x => ?_⟩
  have hdiv : divT Φ = fun _ => (0 : ℂ) := by
    funext y
    exact hΦ.2 y
  have h1 := dy_divT Φ hC j
  rw [hdiv, UnforcedLeray.Short.PartIIIb.NearInst.PairDualAux.dy_zero_fun] at h1
  have h2 := congrFun h1 x
  have h3 : ∑ k : Fin 3, dy k (dy j Φ) x k = ∑ k : Fin 3, (dy j (dy k Φ) x) k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dy_dy_comm hC j k]
  rw [h3]
  exact h2.symm

/-- `∂_j(L₀ᵗΦ) = L₀ᵗ(∂_jΦ) + ½∂_jΦ` (`[∂_j, y·∇] = ∂_j`). -/
theorem gEW_dy_L0T {ν : ℝ} {Φ : ℝ × Space → CVec3} (hC : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    dy j (UnforcedLeray.B0411.L0T ν Φ) =
      UnforcedLeray.B0411.L0T ν (dy j Φ) + (1 / 2 : ℂ) • dy j Φ := by
  have h := UnforcedLeray.Short.PartIIIb.NearInst.PairDualAux.dy_L0T_add (ν := ν) (μ := 0) hC j
  have e0 : (fun x => UnforcedLeray.B0411.L0T ν Φ x + ((0 : ℝ) : ℂ) • Φ x) =
      UnforcedLeray.B0411.L0T ν Φ := by
    funext x
    simp
  rw [e0] at h
  rw [h]
  funext x
  simp only [UnforcedLeray.B0411.L0T, UnforcedLeray.PhaseSpace.nuLapT, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Complex.ofReal_zero, zero_smul, add_zero]
  module

theorem gEWeak : GEWeak := by
  unfold GEWeak
  apply geRegime_const
  intro p z g hd
  obtain ⟨_, hg⟩ := hd
  intro gF gL gQ hF hL hQ hsum j Φ hΦ
  have hΦp : IsPhaseTest p.period Φ := hΦ.1
  have hC : ContDiff ℝ ∞ Φ := hΦ.1.smooth
  have hΨ : IsSolTest p.period (dy j Φ) := gEW_isSolTest_dy hΦ j
  have hΨp : IsPhaseTest p.period (dy j Φ) := hΨ.1
  -- (1) the HasPhaseOp relation tested at Φ
  have H1 := hg j Φ hΦp
  simp only at H1
  rw [phasePair_neg hΨp] at H1
  -- (2) the HasPhaseOp relation tested at L₀ᵗΦ
  have hL0 : IsPhaseTest p.period (UnforcedLeray.B0411.L0T p.ν Φ) :=
    UnforcedLeray.B0411.isPhaseTest_L0T hΦp p.ν
  have HA := hg j _ hL0
  simp only at HA
  rw [gEW_dy_L0T hC j] at HA
  have hL0Ψ : IsPhaseTest p.period (UnforcedLeray.B0411.L0T p.ν (dy j Φ)) :=
    UnforcedLeray.B0411.isPhaseTest_L0T hΨp p.ν
  have hhalf : IsPhaseTest p.period ((1 / 2 : ℂ) • dy j Φ) := hΨp.const_smul _
  rw [phasePair_neg (hL0Ψ.add hhalf), phasePair_add hL0Ψ hhalf,
    phasePair_const_smul hΨp] at HA
  -- (3) the transpose identity for the correction `w`
  have HB := UnforcedLeray.Cons.C03.Concrete.A0_phasePair_eq_L0T p (z := z) hΨp
  -- (4) the ordinary relation tested at ∂_jΦ
  have HC := hL (dy j Φ) hΨ
  -- (5) the sum of the three pieces, tested at ∂_jΦ
  have HS := congrArg (phasePair p.period UnforcedLeray.B0412.q0E (dy j Φ)) hsum
  rw [map_add, map_add, map_zero] at HS
  linear_combination (-1 : ℂ) * HA + HB + (1 : ℂ) * HC + (-1 : ℂ) * HS + (1 / 2 : ℂ) * H1

end UnforcedLeray.Short.PartIIIb.Concrete
