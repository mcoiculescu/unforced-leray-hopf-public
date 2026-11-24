import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSymmetry
import UnforcedLeray.Units.B0005.Bridge.Solenoidal

/-!
# Every-phase divergence pairings of the graph phase trace

For each fixed spatial test, compactly supported time-space product tests turn phase-divergence
into a scalar time-distribution identity. Continuity of the actual `L^q` phase trace upgrades
that identity to every phase.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.B0005 UnforcedLeray.B0412
open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.RieszLp

local instance fact_q0_ge_one_sol : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  ⟨by norm_num [B0281.q0]⟩

private theorem q0_holder_sol : B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
  rw [B0281.q0_eq]
  exact B0276.holderConjugate

/-- The continuous phase trace of an actual graph element has zero divergence pairing with
every spatial test at every phase. -/
theorem Params.phaseRepC_divergence_pairing (p : Params) (z : p.Z) (τ : ℝ)
    (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    ∫ y, dotL (B0005.gvec φ y)
      ((phaseRepC (q := q0E) q0E_ne_top (hasPhaseOp_T0X (p.graphX z))
        (τ : AddCircle p.period) : Space → CVec3) y) = 0 := by
  let hTime := hasPhaseOp_T0X (p.graphX z)
  let w := p.wOf z
  let V : C(AddCircle p.period, Lp CVec3 q0E (volume : Measure Space)) :=
    phaseRepC (q := q0E) q0E_ne_top hTime
  have hwX : w ∈ X p.period p.ν q0E := (p.graphX z).property
  have hsol : IsPhaseSolenoidal w := by
    rcases mem_X.mp hwX with ⟨hdiv, _, _, _⟩
    simpa [w, Params.graphX] using hdiv
  have hline : ∀ᵐ t : ℝ ∂volume,
      w (t : AddCircle p.period) = V (t : AddCircle p.period) := by
    filter_upwards [PhaseTrace.phaseRep_ae_line q0E_ne_top hTime] with t ht
    change w (t : AddCircle p.period) =
      PhaseTrace.phaseRep q0E_ne_top hTime t
    simpa [w, Params.graphX] using ht.symm
  have hgrad : MemLp (B0005.gvec φ) (conjExp q0E) volume :=
    B0005.memLp_gvec hφ (conjExp q0E)
  let L : Lp CVec3 q0E volume →L[ℂ] ℂ :=
    innerPair q0E (hgrad.toLp (B0005.gvec φ))
  have hL (f : Lp CVec3 q0E volume) :
      L f = ∫ y, dotL (B0005.gvec φ y) ((f : Space → CVec3) y) := by
    change innerPair q0E (hgrad.toLp (B0005.gvec φ)) f = _
    rw [innerPair_apply]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hgrad] with y hy
    rw [hy]
  let g : ℝ → ℂ := fun t => L (V (t : AddCircle p.period))
  have hgcont : Continuous g := by
    dsimp [g]
    exact L.continuous.comp (V.continuous.comp (AddCircle.continuous_mk' p.period))
  have hgloc : LocallyIntegrable g volume := hgcont.locallyIntegrable
  have htests : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∫ t, θ t • g t = 0 := by
    intro θ hθ hθc
    obtain ⟨A, B, hAB, hθAB⟩ := B0005.exists_Icc_of_hasCompactSupport hθc
    have hG0 := B0005.isPhaseTest_scalarTest hθ hφ
    have hGT : TimeSupp A B (B0005.scalarTest θ φ) := by
      intro t y ht
      simp [B0005.scalarTest, hθAB t ht]
    have hGgrad0 : IsPhaseTest 0 (gradT (B0005.scalarTest θ φ)) := hG0.gradT
    have hGgradT : TimeSupp A B (gradT (B0005.scalarTest θ φ)) := by
      intro t y ht
      simp [gradT, B0005.timeSupp_dy hGT _ t y ht]
    have hperiodic := isPhaseTest_perT p.period_pos hGT hG0
    have hkey := hsol _ hperiodic
    rw [B0005.gradT_perT p.period_pos hGT hG0.smooth,
      PhaseTrace.phasePair_perT hGgrad0 hAB hGgradT] at hkey
    have hpair : ∫ t, PhaseTrace.pairH hGgrad0 w t = 0 := by
      rcases smul_eq_zero.mp hkey with hzero | hzero
      · have hc : (p.period⁻¹ : ℝ) ≠ 0 := inv_ne_zero p.period_pos.ne'
        exact False.elim (hc hzero)
      · exact hzero
    have hpw (t : ℝ) : PhaseTrace.pairH hGgrad0 w t =
        (θ t : ℂ) * L (w (t : AddCircle p.period)) := by
      rw [PhaseTrace.pairH_eq]
      calc
        _ = ∫ y, (θ t : ℂ) *
            dotL (B0005.gvec φ y) ((w (t : AddCircle p.period) : Space → CVec3) y) := by
              refine integral_congr_ae (Eventually.of_forall fun y => ?_)
              exact B0005.dotL_gradT_scalarTest hθ hφ.smooth (t, y)
                ((w (t : AddCircle p.period) : Space → CVec3) y)
        _ = (θ t : ℂ) * L (w (t : AddCircle p.period)) := by
              rw [integral_const_mul, ← hL]
    have hpair' : ∫ t, θ t • L (w (t : AddCircle p.period)) = 0 := by
      have heq : (fun t => PhaseTrace.pairH hGgrad0 w t) =ᵐ[volume]
          fun t => θ t • L (w (t : AddCircle p.period)) := by
        filter_upwards [ae_of_all volume hpw] with t ht
        simpa [Complex.real_smul] using ht
      rw [← integral_congr_ae heq]
      exact hpair
    have hreplace : (fun t => θ t • L (w (t : AddCircle p.period))) =ᵐ[volume]
        fun t => θ t • g t := by
      filter_upwards [hline] with t ht
      simp only [g]
      rw [ht]
    rw [← integral_congr_ae hreplace]
    exact hpair'
  have hzero : ∀ᵐ t : ℝ ∂volume, g t = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hgloc htests
  have hgall : ∀ t : ℝ, g t = 0 := by
    have heq : g =ᵐ[volume] fun _ : ℝ => (0 : ℂ) := hzero
    have hfun := (Continuous.ae_eq_iff_eq volume hgcont continuous_const).mp heq
    intro s
    exact congrFun hfun s
  rw [← hL]
  exact hgall τ

end UnforcedLeray.Cons.C03.Concrete
