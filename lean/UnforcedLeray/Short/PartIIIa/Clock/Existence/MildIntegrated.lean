import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5.L2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakOf

/-!
# Part III-a, `PartIII-a:T21/3/6`: the mild solution is weak (horizon form)

Source of record: `the November 2 reference manuscript`, the mild/weak transfer
(SP 2819-2836). `MildIntegratedOn` (Sub/T21_3_Horizon.lean) is proved for all parameters from
`ScaledHeatWeak` (conjuncts (a), (b)), the mild equation `horizonData_mild`, and the continuity of
the horizon evolution and of the clamped flux.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist.MildAux

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

variable {c m : ℝ} [Fact (0 < c)]

/-- Every cylinder test pairs with `X_m` through a fixed element of `X_m`. -/
theorem exists_pair {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    ∃ G : UnforcedLeray.B0579.X c m, ∀ f : UnforcedLeray.B0579.X c m,
      ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f := by
  obtain ⟨R, hR⟩ := hψ.band
  have hGm := L2Aux.memLp_band_cellMeasure (c := c) hψ.continuous hR (-m)
  refine ⟨UnforcedLeray.B0579.mulW c (-m) m (hGm.toLp ψ), fun f => ?_⟩
  rw [UnforcedLeray.B0579.inner_mulW_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(UnforcedLeray.B0579.ac_cellMeasure c (-m)).ae_le hGm.coeFn_toLp] with x hx
  rw [hx]

/-- Pairing with a fixed element of `X_m`, on the state space. -/
theorem ell_eq (hm : 1 ≤ m) {ψ : ℝ × ℝ → ℝ} {G : UnforcedLeray.B0579.X c m}
    (hG : ∀ f : UnforcedLeray.B0579.X c m,
      ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f)
    (u : ActualVorticity (c := c) (m := m) hm) :
    ∫ x in UnforcedLeray.B0579.cell c, vortFn hm u x * ψ x = inner ℝ G (u.1 : UnforcedLeray.B0579.X c m) :=
  hG u.1

theorem ell_add (hm : 1 ≤ m) {ψ : ℝ × ℝ → ℝ} {G : UnforcedLeray.B0579.X c m}
    (hG : ∀ f : UnforcedLeray.B0579.X c m,
      ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f)
    (u v : ActualVorticity (c := c) (m := m) hm) :
    ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (u + v) x * ψ x =
      (∫ x in UnforcedLeray.B0579.cell c, vortFn hm u x * ψ x) +
        ∫ x in UnforcedLeray.B0579.cell c, vortFn hm v x * ψ x := by
  rw [ell_eq hm hG, ell_eq hm hG, ell_eq hm hG, Submodule.coe_add, inner_add_right]

theorem ell_continuous (hm : 1 ≤ m) {ψ : ℝ × ℝ → ℝ} {G : UnforcedLeray.B0579.X c m}
    (hG : ∀ f : UnforcedLeray.B0579.X c m,
      ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f) :
    Continuous (fun u : ActualVorticity (c := c) (m := m) hm =>
      ∫ x in UnforcedLeray.B0579.cell c, vortFn hm u x * ψ x) := by
  have : (fun u : ActualVorticity (c := c) (m := m) hm =>
      ∫ x in UnforcedLeray.B0579.cell c, vortFn hm u x * ψ x) =
      fun u => inner ℝ G (u.1 : UnforcedLeray.B0579.X c m) := by
    funext u
    exact ell_eq hm hG u
  rw [this]
  exact continuous_const.inner continuous_subtype_val

/-- The clamped flux applied along a continuous state path is continuous in the age. -/
theorem contOn_flux (hm : 1 ≤ m) {ν T : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {hT : 0 ≤ T}
    (P : ActualTrainFluxPathOn (c := c) (m := m) (ν := ν) hm tr hT) {a b : ℝ}
    (ω : ℝ → ActualVorticity (c := c) (m := m) hm) (hω : ContinuousOn ω (Icc a b)) :
    ContinuousOn (fun r => actualTrainFluxBOn hm P r (ω r)) (Icc a b) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ t, ‖actualTrainFluxBOn hm P t‖ ≤ K :=
    ⟨_, fun t => norm_actualTrainFluxBOn_le hm P t⟩
  intro r0 hr0
  show Tendsto (fun r => actualTrainFluxBOn hm P r (ω r)) (𝓝[Icc a b] r0)
    (𝓝 (actualTrainFluxBOn hm P r0 (ω r0)))
  have T1 : Tendsto (fun r => K * ‖ω r - ω r0‖) (𝓝[Icc a b] r0) (𝓝 0) := by
    have h := tendsto_iff_norm_sub_tendsto_zero.1 (hω r0 hr0)
    simpa using h.const_mul K
  have T2 : Tendsto (fun r => ‖actualTrainFluxBOn hm P r (ω r0) -
      actualTrainFluxBOn hm P r0 (ω r0)‖) (𝓝[Icc a b] r0) (𝓝 0) := by
    have h := (continuous_actualTrainFluxBOn_apply hm P (ω r0)).tendsto r0
    exact tendsto_iff_norm_sub_tendsto_zero.1 (h.mono_left nhdsWithin_le_nhds)
  have hsum := T1.add T2
  rw [add_zero] at hsum
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hsum
  refine Eventually.of_forall fun r => ?_
  have e : actualTrainFluxBOn hm P r (ω r) - actualTrainFluxBOn hm P r0 (ω r0) =
      actualTrainFluxBOn hm P r (ω r - ω r0) +
        (actualTrainFluxBOn hm P r (ω r0) - actualTrainFluxBOn hm P r0 (ω r0)) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  gcongr
  calc ‖actualTrainFluxBOn hm P r (ω r - ω r0)‖
      ≤ ‖actualTrainFluxBOn hm P r‖ * ‖ω r - ω r0‖ :=
        (actualTrainFluxBOn hm P r).le_opNorm _
    _ ≤ K * ‖ω r - ω r0‖ := by
        gcongr
        exact hK r

end UnforcedLeray.Short.IIIa.Exist.MildAux

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open MildAux

/-- **`T21/3/6` (horizon form) for all parameters.** -/
theorem mildIntegratedOnAll : UnforcedLeray.Short.IIIa.Exist.MildIntegratedOnAll := by
  intro ν c m _ hm tr T hT P H _
  unfold MildIntegratedOn
  intro hH a ha w φ hφ s hs
  unfold ScaledHeatWeak at hH
  obtain ⟨hA, hB⟩ := hH
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ActualFlux (c := c) (m := m), ∀ r,
      F r = actualTrainFluxBOn hm P r ((horizonData hm P H).evolution r a w) :=
    ⟨_, fun r => rfl⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ → ActualVorticity (c := c) (m := m) hm, ∀ r,
      ω r = (horizonData hm P H).evolution r a w :=
    ⟨_, fun r => rfl⟩
  have hle : a ≤ s := hs.1
  have hsub : Icc a s ⊆ Icc a (a + 1) := Icc_subset_Icc le_rfl hs.2
  have hωc : ContinuousOn ω (Icc a (a + 1)) := by
    have h := UnforcedLeray.Infra.VolterraEvolution.VolterraData.continuousOn_evolution
      (horizonData_compatible hm P H) a w
    exact (h.mono Icc_subset_Ici_self).congr (fun r _ => hωdef r)
  have hFc : ContinuousOn F (Icc a (a + 1)) := by
    refine (contOn_flux hm P ω hωc).congr (fun r _ => ?_)
    show F r = actualTrainFluxBOn hm P r (ω r)
    rw [hFdef r, hωdef r]
  have hmild : ∀ r ∈ Icc a (a + 1),
      ω r = H.S₀ (r - a) w + ∫ r' in a..r, H.S (r - r') (F r') := by
    intro r hr
    have h := horizonData_mild hm P H (s := a) (t := r) hr.1 hr.2 w
    rw [← hωdef r] at h
    have e : ∀ r', actualTrainFluxBOn hm P r' ((horizonData hm P H).evolution r' a w) = F r' :=
      fun r' => (hFdef r').symm
    simp only [e] at h
    exact h
  -- pairings
  obtain ⟨Gφ, hGφ⟩ := exists_pair (c := c) (m := m) (ψ := φ) hφ
  obtain ⟨GΔ, hGΔ⟩ := exists_pair (c := c) (m := m) (ψ := lapP φ)
    (UnforcedLeray.Short.IIIa.isCylTest_lapP hφ)
  obtain ⟨G0, hG0⟩ := exists_pair (c := c) (m := m) (ψ := UnforcedLeray.B0579.pd 0 φ) (hφ.pd 0)
  obtain ⟨G1, hG1⟩ := exists_pair (c := c) (m := m) (ψ := UnforcedLeray.B0579.pd 1 φ) (hφ.pd 1)
  have split : ∀ (ψ : ℝ × ℝ → ℝ) (G : UnforcedLeray.B0579.X c m),
      (∀ f : UnforcedLeray.B0579.X c m,
        ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f) →
      ∀ r ∈ Icc a (a + 1),
        ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (ω r) x * ψ x =
          (∫ x in UnforcedLeray.B0579.cell c, vortFn hm (H.S₀ (r - a) w) x * ψ x) +
            ∫ x in UnforcedLeray.B0579.cell c,
              vortFn hm (∫ r' in a..r, H.S (r - r') (F r')) x * ψ x := by
    intro ψ G hG r hr
    rw [hmild r hr]
    exact ell_add hm hG _ _
  have hcontω : ∀ (ψ : ℝ × ℝ → ℝ) (G : UnforcedLeray.B0579.X c m),
      (∀ f : UnforcedLeray.B0579.X c m,
        ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f) →
      ContinuousOn (fun r => ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (ω r) x * ψ x)
        (Icc a (a + 1)) := fun ψ G hG =>
    (ell_continuous hm hG).comp_continuousOn hωc
  have hS : ContinuousOn (fun r : ℝ => H.S₀ (r - a) w) (Icc a (a + 1)) :=
    (H.continuousOn_S₀ w).comp (continuous_sub_right a).continuousOn
      (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hcontS : ∀ (ψ : ℝ × ℝ → ℝ) (G : UnforcedLeray.B0579.X c m),
      (∀ f : UnforcedLeray.B0579.X c m,
        ∫ x in UnforcedLeray.B0579.cell c, f x * ψ x = inner ℝ G f) →
      ContinuousOn (fun r => ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (H.S₀ (r - a) w) x * ψ x)
        (Icc a (a + 1)) := fun ψ G hG =>
    (ell_continuous hm hG).comp_continuousOn hS
  have hII : ∀ f : ℝ → ℝ, ContinuousOn f (Icc a (a + 1)) → IntervalIntegrable f volume a s :=
    fun f hf => ContinuousOn.intervalIntegrable_of_Icc hle (hf.mono hsub)
  have hωint := hII _ (hcontω (lapP φ) GΔ hGΔ)
  have hSint := hII _ (hcontS (lapP φ) GΔ hGΔ)
  -- flux pairing
  obtain ⟨R0, hR0⟩ := (hφ.pd 0).band
  obtain ⟨R1, hR1⟩ := (hφ.pd 1).band
  have hflux_eq : ∀ r, (∫ x in UnforcedLeray.B0579.cell c,
      (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
        fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x)) =
      inner ℝ G0 (F r 0) + inner ℝ G1 (F r 1) := by
    intro r
    have i0 : IntegrableOn (fun x => fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x)
        (UnforcedLeray.B0579.cell c) :=
      L2Aux.integrableOn_band_mul (F r 0) (hφ.pd 0).continuous hR0
    have i1 : IntegrableOn (fun x => fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x)
        (UnforcedLeray.B0579.cell c) :=
      L2Aux.integrableOn_band_mul (F r 1) (hφ.pd 1).continuous hR1
    rw [MeasureTheory.integral_add i0 i1]
    exact congrArg₂ (· + ·) (hG0 (F r 0)) (hG1 (F r 1))
  have hfluxC : ContinuousOn (fun r => ∫ x in UnforcedLeray.B0579.cell c,
      (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
        fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x)) (Icc a (a + 1)) := by
    have h : ContinuousOn (fun r => inner ℝ G0 (F r 0) + inner ℝ G1 (F r 1)) (Icc a (a + 1)) := by
      refine ContinuousOn.add ?_ ?_
      · exact (continuous_const.inner continuous_id).comp_continuousOn
          ((continuous_apply 0).comp_continuousOn hFc)
      · exact (continuous_const.inner continuous_id).comp_continuousOn
          ((continuous_apply 1).comp_continuousOn hFc)
    exact h.congr (fun r _ => hflux_eq r)
  have hfluxII := hII _ hfluxC
  -- the five ingredients
  have hA' := hA w φ hφ (s - a) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hshift : ∫ r in a..s, ∫ x in UnforcedLeray.B0579.cell c,
      vortFn hm (H.S₀ (r - a) w) x * lapP φ x =
      ∫ r in (0 : ℝ)..(s - a), ∫ x in UnforcedLeray.B0579.cell c,
        vortFn hm (H.S₀ r w) x * lapP φ x := by
    have := intervalIntegral.integral_comp_sub_right
      (fun r : ℝ => ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (H.S₀ r w) x * lapP φ x)
      (a := a) (b := s) a
    rw [sub_self] at this
    exact this
  have hYr : ∫ r in a..s, ∫ x in UnforcedLeray.B0579.cell c,
        vortFn hm (∫ r' in a..r, H.S (r - r') (F r')) x * lapP φ x =
      (∫ r in a..s, ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (ω r) x * lapP φ x) -
        ∫ r in a..s, ∫ x in UnforcedLeray.B0579.cell c,
          vortFn hm (H.S₀ (r - a) w) x * lapP φ x := by
    rw [← intervalIntegral.integral_sub hωint hSint]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hle] at hr
    have := split (lapP φ) GΔ hGΔ r ⟨hr.1, le_trans hr.2 hs.2⟩
    show _ = _ - _
    linarith
  have hDu := hB F a (a + 1) (by linarith) le_rfl hFc φ hφ s hs
  have hsφ := split φ Gφ hGφ s hs
  have hE6 : (∫ r in a..s, (ν * (∫ x in UnforcedLeray.B0579.cell c,
        vortFn hm (ω r) x * lapP φ x) +
      ∫ x in UnforcedLeray.B0579.cell c,
        (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
          fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x))) =
      ν * (∫ r in a..s, ∫ x in UnforcedLeray.B0579.cell c, vortFn hm (ω r) x * lapP φ x) +
        ∫ r in a..s, ∫ x in UnforcedLeray.B0579.cell c,
          (fluxFn (F r) 0 x * UnforcedLeray.B0579.pd 0 φ x +
            fluxFn (F r) 1 x * UnforcedLeray.B0579.pd 1 φ x) := by
    rw [intervalIntegral.integral_add (hωint.const_mul ν) hfluxII,
      intervalIntegral.integral_const_mul]
  simp only [← hFdef]
  simp only [← hωdef]
  rw [hE6]
  linear_combination hsφ + hA' + hDu + ν * hYr - ν * hshift

end UnforcedLeray.Short.IIIa.Exist
