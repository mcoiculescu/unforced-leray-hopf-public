import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.Local

/-!
# Base `T₀`-identification of the correction (`PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523 ("The projected equation is $A_0U+\mathbb P(U\cdot\nabla U)=0$ with zero
residual").

`corrT0BaseRep_proof : CorrComovingSub.CorrT0BaseRep`.

Proof. Write `U = U_raw + E_εα + w` (`bgField`), `N = νΔU + ½U - 𝔓(U·∇U)`.
1. `ProjectedEquation` gives the compact-solenoidal weak equation for `U`
   (`PointwiseDerivSub.bgField_compactSolenoidal_weakEquation`), which in drift form reads
   `⟪T₀ᵗΦ, U⟫ = ⟪Φ, N⟫` on solenoidal phase tests (`BaseRep/Weak.lean`).
2. Testing with periodized chart lifts of `φ(s)Ψ(x)` (`Ψ` spatially solenoidal), the comoving
   tested value `∫ Ψ(x)·U(s, e^{-s/2}x) dx` has derivative `∫ Ψ(x)·N(s, e^{-s/2}x) dx`
   (`BaseRep/Comoving.lean`); spatial solenoidal separation in `L⁴` then gives the ray identity
   `U(s₂, e^{-s₂/2}x) - U(s₁, e^{-s₁/2}x) = ∫_{s₁}^{s₂} N(r, e^{-r/2}x) dr` (`BaseRep/RayU.lean`).
   No integrability of `T₀U_raw` or `T₀E_i` is needed: the drift is absorbed by the chart.
3. Subtracting the fundamental theorem of calculus along rays for the jointly smooth
   `U_raw + E_εα` gives the ray identity for `w` with right side `corrComovingRHS p z`.
4. The ray identity yields `∫∫ T₀ᵗK·w = ∫∫ K·corrComovingRHS` for compactly supported tests
   (`BaseRep/Transpose.lean`); with `T₀w = b` in distributions and localization
   (`BaseRep/Local.lean`), `b = corrComovingRHS p z` almost everywhere.
The joint continuity of `𝔓(U·∇U)` is `LerayContSub.continuous_smoothLeraySlice`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint UnforcedLeray.PhaseTrace UnforcedLeray.RieszLp
  BaseRepSub

local instance fact_q0_ge_one_baseRep : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

theorem continuous_along_ray {V : ℝ → SpatialField}
    (hV : Continuous fun x : ℝ × Space => V x.1 x.2) (x : Space) :
    Continuous fun r => V r (dilScale r • x) :=
  hV.comp (continuous_id.prodMk (continuous_dilScale.smul continuous_const))

theorem reV_eq_reP (v : CVec3) : RieszLp.reV v = reP v := by
  ext i
  simp [reP]

/-- The ray identity for the correction `w = U - U_raw - E_εα`. -/
theorem corr_ray_identity (p : Params) (z : p.Z) (hW : WeakHyp p.period p.ν (bgField p z))
    (hRawCD : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    (hInCD : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (s₁ s₂ : ℝ) (x : Space) :
    p.corr z s₂ (dilScale s₂ • x) - p.corr z s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, CorrComovingSub.corrComovingRHS p z r (dilScale r • x) := by
  have hRc : Continuous fun x : ℝ × Space => comovingPartial p.raw x.1 x.2 :=
    (CorrComovingSub.contDiff_joint_comovingPartial hRawCD).continuous
  have hIc : ∀ i : Fin 2, Continuous fun x : ℝ × Space => comovingPartial (p.inlet i) x.1 x.2 :=
    fun i => (CorrComovingSub.contDiff_joint_comovingPartial (hInCD i)).continuous
  have hcorr_eq : ∀ τ y, p.corr z τ y =
      bgField p z τ y - p.raw τ y - ∑ i : Fin 2, p.coord z i • p.inlet i τ y := by
    intro τ y
    simp only [bgField]
    abel
  have cN : Continuous fun r => comovingEvolRHS p.ν (bgField p z) r (dilScale r • x) :=
    continuous_along_ray (V := comovingEvolRHS p.ν (bgField p z)) hW.contN x
  have cR : Continuous fun r => comovingPartial p.raw r (dilScale r • x) :=
    continuous_along_ray (V := comovingPartial p.raw) hRc x
  have cI : ∀ i : Fin 2, Continuous fun r => comovingPartial (p.inlet i) r (dilScale r • x) :=
    fun i => continuous_along_ray (V := comovingPartial (p.inlet i)) (hIc i) x
  have cS : Continuous fun r => ∑ i : Fin 2,
      p.coord z i • comovingPartial (p.inlet i) r (dilScale r • x) :=
    continuous_finsetSum _ fun i _ => (cI i).const_smul (p.coord z i)
  have hRHS : (fun r => CorrComovingSub.corrComovingRHS p z r (dilScale r • x)) =
      fun r => comovingEvolRHS p.ν (bgField p z) r (dilScale r • x) -
        (comovingPartial p.raw r (dilScale r • x) +
          ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) r (dilScale r • x)) := rfl
  have iN : IntervalIntegrable (fun r => comovingEvolRHS p.ν (bgField p z) r (dilScale r • x))
      volume s₁ s₂ := cN.intervalIntegrable _ _
  have iR : IntervalIntegrable (fun r => comovingPartial p.raw r (dilScale r • x))
      volume s₁ s₂ := cR.intervalIntegrable _ _
  have iS : IntervalIntegrable (fun r => ∑ i : Fin 2,
      p.coord z i • comovingPartial (p.inlet i) r (dilScale r • x)) volume s₁ s₂ :=
    cS.intervalIntegrable _ _
  have iRS : IntervalIntegrable (fun r => comovingPartial p.raw r (dilScale r • x) +
      ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) r (dilScale r • x)) volume s₁ s₂ :=
    iR.add iS
  have iI : ∀ i ∈ (Finset.univ : Finset (Fin 2)), IntervalIntegrable
      (fun r => p.coord z i • comovingPartial (p.inlet i) r (dilScale r • x)) volume s₁ s₂ :=
    fun i _ => ((cI i).const_smul (p.coord z i)).intervalIntegrable _ _
  rw [hRHS, intervalIntegral.integral_sub iN iRS, intervalIntegral.integral_add iR iS,
    intervalIntegral.integral_finset_sum iI]
  simp only [intervalIntegral.integral_smul]
  rw [← ray_identity_U hW s₁ s₂ x, ← ray_FTC hRawCD s₁ s₂ x]
  have hI : ∀ i : Fin 2, ∫ r in s₁..s₂, comovingPartial (p.inlet i) r (dilScale r • x) =
      p.inlet i s₂ (dilScale s₂ • x) - p.inlet i s₁ (dilScale s₁ • x) :=
    fun i => (ray_FTC (hInCD i) s₁ s₂ x).symm
  simp only [hI, hcorr_eq, smul_sub, Finset.sum_sub_distrib]
  abel

theorem rep_wOf_ae (p : Params) (z : p.Z) (hFrep : IsContRep (p.wOf z) (p.corr z))
    (hwreal : p.wOf z ∈ realSub p.period q0E) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ y : Space ∂volume, rep (p.wOf z) t y = realC (p.corr z t y) := by
  have h2 := hFrep.2
  rw [Measure.volume_eq_prod] at h2
  have h1 := rep_real_ae_of_realSub (p.wOf z) hwreal
  have h3 : ∀ᵐ x : ℝ × Space ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      rep (p.wOf z) x.1 x.2 = realC (p.corr z x.1 x.2) := by
    filter_upwards [h1, h2] with x hx1 hx3
    rw [hx1, PointwiseDerivSub.realC_eq_ofReV, hx3, reV_eq_reP]
  exact Measure.ae_ae_of_ae_prod h3

theorem integrable_slice_rep {P : ℝ} [Fact (0 < P)] (b : Yq P q0E) {K : ℝ × Space → CVec3}
    (hK0 : IsPhaseTest 0 K) (t : ℝ) : Integrable fun y => dotL (K (t, y)) (rep b t y) := by
  refine (integrable_dotL hK0 t (b (t : AddCircle P))).congr ?_
  filter_upwards [rep_slice b t] with y hy
  rw [hy]

theorem integrable_iter_rep {P : ℝ} [Fact (0 < P)] (b : Yq P q0E) {K : ℝ × Space → CVec3}
    (hK0 : IsPhaseTest 0 K) {A B : ℝ} (hAB : A ≤ B) (hT : TimeSupp A B K) :
    Integrable fun t => ∫ y, dotL (K (t, y)) (rep b t y) := by
  refine (integrable_pairH hK0 hAB hT b).congr (Eventually.of_forall fun t => ?_)
  rw [pairH_eq]
  refine integral_congr_ae ?_
  filter_upwards [rep_slice b t] with y hy
  rw [hy]

theorem iter_congr_rep {G : ℝ × Space → CVec3} {f g : ℝ → Space → CVec3}
    (hfg : ∀ᵐ t : ℝ ∂volume, ∀ᵐ y : Space ∂volume, f t y = g t y) :
    ∫ t, ∫ y, dotL (G (t, y)) (f t y) = ∫ t, ∫ y, dotL (G (t, y)) (g t y) := by
  refine integral_congr_ae ?_
  filter_upwards [hfg] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  rw [hy]

theorem iter_sub {K : ℝ × Space → CVec3} {f g : ℝ → Space → CVec3}
    (hf : ∀ t, Integrable fun y => dotL (K (t, y)) (f t y))
    (hg : ∀ t, Integrable fun y => dotL (K (t, y)) (g t y))
    (hF : Integrable fun t => ∫ y, dotL (K (t, y)) (f t y))
    (hG : Integrable fun t => ∫ y, dotL (K (t, y)) (g t y)) :
    ∫ t, ∫ y, dotL (K (t, y)) (f t y - g t y) =
      (∫ t, ∫ y, dotL (K (t, y)) (f t y)) - ∫ t, ∫ y, dotL (K (t, y)) (g t y) := by
  have hsplit : ∀ t, ∫ y, dotL (K (t, y)) (f t y - g t y) =
      (∫ y, dotL (K (t, y)) (f t y)) - ∫ y, dotL (K (t, y)) (g t y) := by
    intro t
    simp only [map_sub]
    exact integral_sub (hf t) (hg t)
  simp only [hsplit]
  exact integral_sub hF hG

theorem test_identity (p : Params) (z : p.Z) {b : Yq p.period q0E}
    (hb : HasPhaseOp driftT (p.wOf z) b)
    (hrepw' : ∀ᵐ t : ℝ ∂volume, ∀ᵐ y : Space ∂volume, rep (p.wOf z) t y = realC (p.corr z t y))
    (hRHSc : Continuous fun x : ℝ × Space => CorrComovingSub.corrComovingRHS p z x.1 x.2)
    (htr : ∀ K : ℝ × Space → CVec3, ContDiff ℝ ∞ K → HasCompactSupport K →
      ∫ t, ∫ y, dotL (driftT K (t, y)) (realC (p.corr z t y)) =
        ∫ t, ∫ y, dotL (K (t, y)) (realC (CorrComovingSub.corrComovingRHS p z t y)))
    {K : ℝ × Space → CVec3} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) :
    ∫ t, ∫ y, dotL (K (t, y))
      (rep b t y - realC (CorrComovingSub.corrComovingRHS p z t y)) = 0 := by
  set H : ℝ → Space → CVec3 := fun t y => realC (CorrComovingSub.corrComovingRHS p z t y)
    with hH
  have hHc : Continuous fun x : ℝ × Space => H x.1 x.2 := continuous_realC.comp hRHSc
  have hid := iterated_identity_of_hasPhaseOp hb hK hKc
  have hw := iter_congr_rep (G := driftT K) hrepw'
  have hK0 := isPhaseTest_zero_of_compact hK hKc
  obtain ⟨R, hR0, hT⟩ := exists_timeSupp_of_compact hKc
  obtain ⟨R', hR'⟩ := hK0.bounded_support
  have hsl2 : ∀ t, Integrable fun y => dotL (K (t, y)) (H t y) := fun t =>
    integrable_slice_dotL (u := fun x : ℝ × Space => H x.1 x.2) hK.continuous hR' hHc t
  have hB : Integrable fun t => ∫ y, dotL (K (t, y)) (H t y) :=
    integrable_slice_dotL_time (u := fun x : ℝ × Space => H x.1 x.2) hK0 hT hHc
  rw [iter_sub (integrable_slice_rep b hK0) hsl2 (integrable_iter_rep b hK0 (by linarith) hT) hB,
    ← hid, hw, htr K hK hKc, sub_self]

/-- **Localization step.** -/
theorem ae_eq_of_ray (p : Params) (z : p.Z) {b : Yq p.period q0E}
    (hb : HasPhaseOp driftT (p.wOf z) b) (hFrep : IsContRep (p.wOf z) (p.corr z))
    (hwreal : p.wOf z ∈ realSub p.period q0E)
    (hRHSc : Continuous fun x : ℝ × Space => CorrComovingSub.corrComovingRHS p z x.1 x.2)
    (hray : ∀ s₁ s₂ x, p.corr z s₂ (dilScale s₂ • x) - p.corr z s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, CorrComovingSub.corrComovingRHS p z r (dilScale r • x)) :
    ∀ᵐ x : ℝ × Space ∂volume,
      rep b x.1 x.2 = realC (CorrComovingSub.corrComovingRHS p z x.1 x.2) := by
  have hD : LocallyIntegrable (fun x : ℝ × Space =>
      rep b x.1 x.2 - realC (CorrComovingSub.corrComovingRHS p z x.1 x.2)) volume :=
    (locallyIntegrable_rep b).sub (continuous_realC.comp hRHSc).locallyIntegrable
  have hzero := ae_eq_zero_of_test hD fun K hK hKc =>
    test_identity p z hb (rep_wOf_ae p z hFrep hwreal) hRHSc
      (fun K hK hKc => transpose_of_ray hFrep.1 hRHSc hray hK hKc) hK hKc
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.1 hx

/-- **`PartII-b:S3/1/1/2/1/2/1` (`CorrT0BaseRep`)** (SP 2519-2523). -/
theorem corrT0BaseRep_proof : UnforcedLeray.Short.IIb.CorrComovingSub.CorrT0BaseRep := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hPer⟩ := exists_period_le_one_of_bgRegime (dp := dp) hdm
  refine ⟨ν₂, hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet b hb
  have hP1 : p.period ≤ 1 := hPer p d hReg hν
  have hUS : ∀ τ, ContDiff ℝ ∞ (bgField p z τ) := HigherPhaseSub.sliceFamily_contDiff_infty hBg
  have hJ : LerayContSub.JetCont (bgField p z) :=
    LerayContSub.jetCont_bgField p hP1 z hRawCD hInCD hGraph
  have hUc : Continuous fun x : ℝ × Space => bgField p z x.1 x.2 := hJ []
  have hCc : Continuous fun x : ℝ × Space =>
      spatialConvect (bgField p z x.1) (bgField p z x.1) x.2 :=
    LerayContSub.jetCont_spatialConvect hUS hUS hJ hJ []
  have hLc : Continuous fun x : ℝ × Space =>
      smoothConvectiveLeray (bgField p z) (bgField p z) x.1 x.2 :=
    LerayContSub.continuous_smoothLeraySlice
      (HigherPhaseSub.sliceFamily_spatialConvect hBg hBg) hCc
  have hDc : Continuous fun x : ℝ × Space => spatialDiffReact p.ν (bgField p z x.1) x.2 := by
    have hfun : (fun x : ℝ × Space => spatialDiffReact p.ν (bgField p z x.1) x.2) =
        fun x => p.ν • ∑ j : Fin 3, dirSpatialJet (bgField p z x.1)
            [EuclideanSpace.single j 1, EuclideanSpace.single j 1] x.2 +
          (1 / 2 : ℝ) • bgField p z x.1 x.2 := by
      funext x
      rfl
    rw [hfun]
    exact ((continuous_finsetSum _ fun j _ => hJ _).const_smul p.ν).add
      (hUc.const_smul (1 / 2 : ℝ))
  have hNc : Continuous fun x : ℝ × Space => comovingEvolRHS p.ν (bgField p z) x.1 x.2 :=
    hDc.sub hLc
  have hW : WeakHyp p.period p.ν (bgField p z) :=
    { slice := hBg
      sol := PointwiseDerivSub.bgField_isSolenoidal p hP1 z hRaw hInlet
      cont := hUc
      contN := hNc
      contC := hCc
      per := PointwiseDerivSub.bgField_periodic p z hRaw hInlet
      weak := fun Φ hΦ =>
        PointwiseDerivSub.bgField_compactSolenoidal_weakEquation p hRaw hInlet z hProj hΦ }
  have hRc : Continuous fun x : ℝ × Space => comovingPartial p.raw x.1 x.2 :=
    (CorrComovingSub.contDiff_joint_comovingPartial hRawCD).continuous
  have hIc : ∀ i : Fin 2, Continuous fun x : ℝ × Space => comovingPartial (p.inlet i) x.1 x.2 :=
    fun i => (CorrComovingSub.contDiff_joint_comovingPartial (hInCD i)).continuous
  have hRHSc : Continuous fun x : ℝ × Space => CorrComovingSub.corrComovingRHS p z x.1 x.2 := by
    have hS : Continuous fun x : ℝ × Space =>
        ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 x.2 :=
      continuous_finsetSum _ fun i _ => (hIc i).const_smul (p.coord z i)
    have h : Continuous fun x : ℝ × Space => comovingEvolRHS p.ν (bgField p z) x.1 x.2 -
        (comovingPartial p.raw x.1 x.2 +
          ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 x.2) := hNc.sub (hRc.add hS)
    refine h.congr fun x => ?_
    rfl
  obtain ⟨g, hg⟩ := hGraph 0
  have hg0 : (g Fin.elim0 : Yq p.period q0E) = p.wOf z := hg
  have hFrep : IsContRep (p.wOf z) (p.corr z) := by
    have h := CorrComovingSub.isContRep_contRep_D hP1 p.ν_pos (g Fin.elim0)
    rw [hg0] at h
    exact h
  have hwreal : p.wOf z ∈ realSub p.period q0E := ((mem_graphSpace p.period).1 z.2).2
  exact ae_eq_of_ray p z hb hFrep hwreal hRHSc (corr_ray_identity p z hW hRawCD hInCD)

end UnforcedLeray.Short.IIb

end
