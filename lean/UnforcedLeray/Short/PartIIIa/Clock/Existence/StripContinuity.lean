import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5.L2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxIdentity

/-!
# Part III-a, `PartIII-a:T21/3/7`: continuity fields on all parameters (horizon form)

Source of record: `the November 2 reference manuscript`, the continuity of the
strip path in `X_{m,c}` and the interval integrability of the tested right-hand side.
The norm identity `stc_xNorm_cplx_sub` and the continuity of the pairings `stcPairL` are proved
here from the accepted lemmas `inner_mulW_neg`, `integrableOn_band_mul` and the flux identity
`fluxIdentityOnAll`; the continuity of the Volterra evolution is `UnforcedLeray.Infra.VolterraEvolution.VolterraData.continuousOn_evolution`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

section Pairing

variable {c m : ℝ}

/-- The continuous functional `f ↦ ∫_cell f g` on `X_{m,c}`, for a continuous band-supported `g`. -/
def stcPairL (g : ℝ × ℝ → ℝ) (hg : Continuous g)
    (hb : ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    UnforcedLeray.B0579.X c m →L[ℝ] ℝ :=
  innerSL ℝ (UnforcedLeray.B0579.mulW c (-m) m
    ((L2Aux.memLp_band_cellMeasure (c := c) hg hb.choose_spec (-m)).toLp g))

theorem stc_pairL_apply (g : ℝ × ℝ → ℝ) (hg : Continuous g)
    (hb : ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) (f : UnforcedLeray.B0579.X c m) :
    stcPairL g hg hb f = ∫ x in UnforcedLeray.B0579.cell c, f x * g x := by
  unfold stcPairL
  rw [innerSL_apply_apply, UnforcedLeray.B0579.inner_mulW_neg]
  have hGm := L2Aux.memLp_band_cellMeasure (c := c) hg hb.choose_spec (-m)
  have hae : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), (hGm.toLp g) x = g x :=
    (UnforcedLeray.B0579.ac_cellMeasure c (-m)).ae_le hGm.coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp only [hx]

end Pairing

/-- Joint continuity of `t ↦ B t (u t)` for a uniformly bounded, strongly continuous family
of operators `B t` and a continuous path `u`. -/
theorem stc_continuousOn_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : ℝ → E →L[ℝ] F) (β : ℝ)
    (hβ : ∀ t, ‖B t‖ ≤ β) (hB : ∀ u : E, Continuous fun t => B t u)
    {u : ℝ → E} {S : Set ℝ} (hu : ContinuousOn u S) :
    ContinuousOn (fun t => B t (u t)) S := by
  intro t0 ht0
  have hu0 : Tendsto u (𝓝[S] t0) (𝓝 (u t0)) := hu t0 ht0
  have h1 : Tendsto (fun t => β * ‖u t - u t0‖ + ‖B t (u t0) - B t0 (u t0)‖) (𝓝[S] t0) (𝓝 0) := by
    have ha : Tendsto (fun t => β * ‖u t - u t0‖) (𝓝[S] t0) (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hu0).const_mul β
    have hb : Tendsto (fun t => ‖B t (u t0) - B t0 (u t0)‖) (𝓝[S] t0) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (((hB (u t0)).tendsto t0).mono_left nhdsWithin_le_nhds)
    simpa using ha.add hb
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h1
  have hsplit : B t (u t) - B t0 (u t0) = B t (u t - u t0) + (B t (u t0) - B t0 (u t0)) := by
    rw [map_sub]; abel
  rw [hsplit]
  have hb1 : ‖B t (u t - u t0)‖ ≤ β * ‖u t - u t0‖ :=
    ((B t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hβ t) (norm_nonneg _))
  linarith [norm_add_le (B t (u t - u t0)) (B t (u t0) - B t0 (u t0))]

section Norm

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- The complex strip difference has `X_{m,c}`-norm equal to the norm of the state difference. -/
theorem stc_xNorm_cplx_sub (v1 v2 : ActualVorticity (c := c) (m := m) hm) :
    xNorm c m (cplx (vortFn hm v1) - cplx (vortFn hm v2)) = ENNReal.ofReal ‖v1 - v2‖ := by
  have hsub : ‖v1 - v2‖ = ‖v1.1 - v2.1‖ := rfl
  have hfin : eLpNorm (⇑(v1.1 - v2.1 : UnforcedLeray.B0579.X c m)) 2
      (UnforcedLeray.B0579.cellMeasure c m) ≠ ⊤ :=
    (MeasureTheory.Lp.memLp _).eLpNorm_lt_top.ne
  have h2 : (⇑(v1.1 - v2.1 : UnforcedLeray.B0579.X c m)) =ᵐ[UnforcedLeray.B0579.cellMeasure c m]
      fun x => vortFn hm v1 x - vortFn hm v2 x :=
    (MeasureTheory.Lp.coeFn_sub _ _).trans (Eventually.of_forall fun x => rfl)
  have h3 : eLpNorm (cplx (vortFn hm v1) - cplx (vortFn hm v2)) 2
      (UnforcedLeray.B0579.cellMeasure c m)
      = eLpNorm (fun x => vortFn hm v1 x - vortFn hm v2 x) 2
        (UnforcedLeray.B0579.cellMeasure c m) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, cplx]
      rw [← Complex.ofReal_sub, Complex.norm_real])
  have h4 : eLpNorm (⇑(v1.1 - v2.1 : UnforcedLeray.B0579.X c m)) 2
      (UnforcedLeray.B0579.cellMeasure c m)
      = eLpNorm (fun x => vortFn hm v1 x - vortFn hm v2 x) 2
        (UnforcedLeray.B0579.cellMeasure c m) := eLpNorm_congr_ae h2
  unfold xNorm
  rw [h3, ← h4, hsub, Lp.norm_def, ENNReal.ofReal_toReal hfin]

/-- The planar Laplacian of a cylinder test function is continuous and band-supported. -/
theorem stc_lapP_cyl {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.B0579.IsCylTest c φ) :
    Continuous (UnforcedLeray.Short.IIIa.lapP φ) ∧
      ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → UnforcedLeray.Short.IIIa.lapP φ x = 0 := by
  refine ⟨?_, ?_⟩
  · exact ((hφ.pd 0).pd 0).continuous.add ((hφ.pd 1).pd 1).continuous
  · obtain ⟨R0, h0⟩ := ((hφ.pd 0).pd 0).band
    obtain ⟨R1, h1⟩ := ((hφ.pd 1).pd 1).band
    refine ⟨max R0 R1, fun x hx => ?_⟩
    unfold UnforcedLeray.Short.IIIa.lapP
    rw [h0 x (lt_of_le_of_lt (le_max_left _ _) hx), h1 x (lt_of_le_of_lt (le_max_right _ _) hx)]
    simp

/-- **Continuity fields, horizon data** (`T21/3/7`): for every parameter, the continuity
fields on unit strips hold. -/
theorem stripContinuityOnAll : UnforcedLeray.Short.IIIa.Exist.StripContinuityOnAll := by
  unfold StripContinuityOnAll StripContinuityOn
  intro ν c m _ hm tr T hT P H hReg a ha haT w
  refine ⟨?_, ?_⟩
  · have hcontE : ContinuousOn (fun s' => (horizonData hm P H).evolution s' a w) (Icc a (a + 1)) :=
      (UnforcedLeray.Infra.VolterraEvolution.VolterraData.continuousOn_evolution (horizonData_compatible hm P H) a w).mono
        (fun r hr => hr.1)
    intro s hs
    simp only [stc_xNorm_cplx_sub hm]
    have h := ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 (hcontE s hs))
    simpa using h
  · intro φ hφ s hs
    have hsa : a ≤ s := hs.1
    have hsT : s ≤ T := le_trans hs.2 haT
    have hu : ContinuousOn (fun r => (horizonData hm P H).evolution r a w) (Icc a s) :=
      ((UnforcedLeray.Infra.VolterraEvolution.VolterraData.continuousOn_evolution (horizonData_compatible hm P H) a w).mono
        (fun r hr => hr.1)).mono (Icc_subset_Icc le_rfl hs.2)
    have hV : ContinuousOn
        (fun r => (actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w)) (Icc a s) :=
      stc_continuousOn_apply (fun t => actualTrainFluxBOn hm P t) _
        (fun t => norm_actualTrainFluxBOn_le hm P t)
        (fun v => continuous_actualTrainFluxBOn_apply hm P v) hu
    obtain ⟨hLc, hLb⟩ := stc_lapP_cyl hφ
    have hpc0 := (hφ.pd 0).continuous
    have hpb0 := (hφ.pd 0).band
    have hpc1 := (hφ.pd 1).continuous
    have hpb1 := (hφ.pd 1).band
    have hA : ContinuousOn
        (fun r => stcPairL (UnforcedLeray.Short.IIIa.lapP φ) hLc hLb
          ((horizonData hm P H).evolution r a w).1) (Icc a s) :=
      (stcPairL _ hLc hLb).continuous.comp_continuousOn
        (continuous_subtype_val.comp_continuousOn hu)
    have hB0 : ContinuousOn
        (fun r => stcPairL (UnforcedLeray.B0579.pd 0 φ) hpc0 hpb0
          ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 0)) (Icc a s) :=
      (stcPairL _ hpc0 hpb0).continuous.comp_continuousOn ((continuous_apply 0).comp_continuousOn hV)
    have hB1 : ContinuousOn
        (fun r => stcPairL (UnforcedLeray.B0579.pd 1 φ) hpc1 hpb1
          ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 1)) (Icc a s) :=
      (stcPairL _ hpc1 hpb1).continuous.comp_continuousOn ((continuous_apply 1).comp_continuousOn hV)
    have hF : ContinuousOn (fun r =>
        ν * stcPairL (UnforcedLeray.Short.IIIa.lapP φ) hLc hLb
            ((horizonData hm P H).evolution r a w).1 +
          (stcPairL (UnforcedLeray.B0579.pd 0 φ) hpc0 hpb0
              ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 0) +
            stcPairL (UnforcedLeray.B0579.pd 1 φ) hpc1 hpb1
              ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 1)))
        (Icc a s) :=
      ContinuousOn.add (ContinuousOn.mul continuousOn_const hA) (ContinuousOn.add hB0 hB1)
    have hEq : ∀ r ∈ Icc a s,
        (∫ x in UnforcedLeray.B0579.cell c,
            flowIntegrand tr (cplx (vortFn hm ((horizonData hm P H).evolution r a w)))
              (stripVel hm ((horizonData hm P H).evolution r a w)) r φ x) =
          ((ν * stcPairL (UnforcedLeray.Short.IIIa.lapP φ) hLc hLb
                ((horizonData hm P H).evolution r a w).1 +
              (stcPairL (UnforcedLeray.B0579.pd 0 φ) hpc0 hpb0
                  ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 0) +
                stcPairL (UnforcedLeray.B0579.pd 1 φ) hpc1 hpb1
                  ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 1)) : ℝ) : ℂ) := by
      intro r hr
      have hr0 : r ∈ Icc (0 : ℝ) T := ⟨le_trans ha hr.1, le_trans hr.2 hsT⟩
      have hI := (fluxIdentityOnAll ν c m hm tr T hT P hReg) r hr0
        ((horizonData hm P H).evolution r a w) φ hφ
      have i0 : IntegrableOn (fun x => fluxFn (actualTrainFluxBOn hm P r
          ((horizonData hm P H).evolution r a w)) 0 x * UnforcedLeray.B0579.pd 0 φ x)
          (UnforcedLeray.B0579.cell c) :=
        (by obtain ⟨R0, hR0⟩ := hpb0; exact L2Aux.integrableOn_band_mul _ hpc0 hR0)
      have i1 : IntegrableOn (fun x => fluxFn (actualTrainFluxBOn hm P r
          ((horizonData hm P H).evolution r a w)) 1 x * UnforcedLeray.B0579.pd 1 φ x)
          (UnforcedLeray.B0579.cell c) :=
        (by obtain ⟨R1, hR1⟩ := hpb1; exact L2Aux.integrableOn_band_mul _ hpc1 hR1)
      have eL : (∫ x in UnforcedLeray.B0579.cell c,
          vortFn hm ((horizonData hm P H).evolution r a w) x * UnforcedLeray.Short.IIIa.lapP φ x) =
          stcPairL (UnforcedLeray.Short.IIIa.lapP φ) hLc hLb
            ((horizonData hm P H).evolution r a w).1 :=
        (stc_pairL_apply _ hLc hLb _).symm
      have e0 : (∫ x in UnforcedLeray.B0579.cell c, fluxFn (actualTrainFluxBOn hm P r
          ((horizonData hm P H).evolution r a w)) 0 x * UnforcedLeray.B0579.pd 0 φ x) =
          stcPairL (UnforcedLeray.B0579.pd 0 φ) hpc0 hpb0
            ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 0) :=
        (stc_pairL_apply _ hpc0 hpb0 _).symm
      have e1 : (∫ x in UnforcedLeray.B0579.cell c, fluxFn (actualTrainFluxBOn hm P r
          ((horizonData hm P H).evolution r a w)) 1 x * UnforcedLeray.B0579.pd 1 φ x) =
          stcPairL (UnforcedLeray.B0579.pd 1 φ) hpc1 hpb1
            ((actualTrainFluxBOn hm P r) ((horizonData hm P H).evolution r a w) 1) :=
        (stc_pairL_apply _ hpc1 hpb1 _).symm
      rw [hI.2]
      congr 1
      rw [eL, integral_add i0 i1, e0, e1]
    have hIntC : ContinuousOn (fun r =>
        ∫ x in UnforcedLeray.B0579.cell c,
          flowIntegrand tr (cplx (vortFn hm ((horizonData hm P H).evolution r a w)))
            (stripVel hm ((horizonData hm P H).evolution r a w)) r φ x) (Icc a s) :=
      ContinuousOn.congr (Complex.continuous_ofReal.comp_continuousOn hF)
        (fun r hr => hEq r hr)
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hsa]
    exact hIntC

end Norm

end UnforcedLeray.Short.IIIa.Exist
