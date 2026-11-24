import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.TerminalMem
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.VolterraWeak
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.TransportCoeff
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont

/-!
# Weak existence and tested age derivative for the free backward adjoint

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(Volterra construction around the BUC train), 2937-2958, and 3060 (backward adjoint).

Constructs a weak reverse-time solution `IsFreeAdjointWeak` of `-∂_r φ = ν Δφ + v·∇φ` on `[t, s]`
for any `0 < ν` and `PartI.IsBUCTrain tr` (no `ν ≤ 1` restriction, since there is no nonlocal
Biot-Savart term), handles the degenerate endpoint case `s = t`, and proves the differentiated
tested identity `FreeTestedDeriv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Infra.VolterraEvolution
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

/-- Weak reverse-time solution on `[t, s]` in `X_{-m,c}` of the free adjoint equation
`-∂_r φ = ν Δφ + v·∇φ` with terminal datum `g` at age `s` (SP 2937-2958, 3060). -/
structure IsFreeAdjointWeak (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop where
  terminal : φ s =ᵐ[volume.restrict (B0579.cell c)] g
  memX : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure c (-m))
  strongCont : ∀ r ∈ Icc t s,
    Tendsto (fun r' => xNorm c (-m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0)
  periodic : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x
  integrable : ∀ ψ, B0579.IsCylTest c ψ → ∀ r ∈ Icc t s,
    IntegrableOn (freeAdjIntegrand tr (φ r) r ψ) (B0579.cell c)
  timeIntegrable : ∀ ψ, B0579.IsCylTest c ψ →
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x) volume t s
  weak : ∀ ψ, B0579.IsCylTest c ψ → ∀ r ∈ Icc t s,
    ∫ x in B0579.cell c, φ r x * (ψ x : ℂ) =
      (∫ x in B0579.cell c, g x * (ψ x : ℂ)) +
        ∫ r' in r..s, ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r') r' ψ x

/-- Almost-everywhere changes preserve `IsFreeAdjointWeak`. -/
theorem IsFreeAdjointWeak.congr_ae {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ φ' : ℝ → ℝ × ℝ → ℂ} (hφ : IsFreeAdjointWeak ν c m tr t s g φ)
    (hts : t ≤ s) (hae : ∀ r ∈ Icc t s, φ' r =ᵐ[volume] φ r)
    (hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x) :
    IsFreeAdjointWeak ν c m tr t s g φ' := by
  have hcell : ∀ r ∈ Icc t s, φ' r =ᵐ[volume.restrict (B0579.cell c)] φ r :=
    fun r hr => ae_restrict_of_ae (hae r hr)
  have hX : ∀ r ∈ Icc t s, φ' r =ᵐ[B0579.cellMeasure c (-m)] φ r :=
    fun r hr => (B0579.cellMeasure_ac c (-m)).ae_le (hcell r hr)
  have hint : ∀ ψ : ℝ × ℝ → ℝ, ∀ r ∈ Icc t s,
      freeAdjIntegrand tr (φ' r) r ψ =ᵐ[volume.restrict (B0579.cell c)]
        freeAdjIntegrand tr (φ r) r ψ :=
    fun ψ r hr => (hcell r hr).mono fun x hx => by simp only [freeAdjIntegrand, hx]
  have hI : ∀ ψ : ℝ × ℝ → ℝ, ∀ r ∈ Icc t s,
      ∫ x in B0579.cell c, freeAdjIntegrand tr (φ' r) r ψ x =
        ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x :=
    fun ψ r hr => integral_congr_ae (hint ψ r hr)
  refine ⟨(hcell s ⟨hts, le_rfl⟩).trans hφ.terminal,
    fun r hr => (hφ.memX r hr).ae_eq (hX r hr).symm, ?_, hper, ?_, ?_, ?_⟩
  · intro r hr
    have heq : ∀ r' ∈ Icc t s, xNorm c (-m) (φ r' - φ r) = xNorm c (-m) (φ' r' - φ' r) := by
      intro r' hr'
      unfold xNorm
      exact eLpNorm_congr_ae ((hX r' hr').symm.sub (hX r hr).symm)
    exact (hφ.strongCont r hr).congr' (eventually_nhdsWithin_of_forall heq)
  · intro ψ hψ r hr
    exact (hφ.integrable ψ hψ r hr).congr (hint ψ r hr).symm
  · intro ψ hψ
    refine (intervalIntegrable_congr ?_).1 (hφ.timeIntegrable ψ hψ)
    intro r hr
    rw [uIoc_of_le hts] at hr
    exact (hI ψ r (Ioc_subset_Icc_self hr)).symm
  · intro ψ hψ r hr
    have h1 : ∫ x in B0579.cell c, φ' r x * (ψ x : ℂ) = ∫ x in B0579.cell c, φ r x * (ψ x : ℂ) :=
      integral_congr_ae ((hcell r hr).mono fun x hx => by simp only [hx])
    rw [h1, hφ.weak ψ hψ r hr]
    congr 1
    refine intervalIntegral.integral_congr fun r' hr' => ?_
    rw [uIcc_of_le hr.2] at hr'
    exact (hI ψ r' ⟨hr.1.trans hr'.1, hr'.2⟩).symm

/-- Base `k = 0` of the spatial Sobolev bootstrap on `[t, s)` for `IsFreeAdjointWeak`. -/
theorem adjHkOn_zero_Ico_of_freeWeak {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsFreeAdjointWeak ν c m tr t s g φ) :
    AdjHkOn c m 0 (Ico t s) φ := by
  refine ⟨fun r _ => φ r, fun r hr => ?_, fun w _ r hr => ?_⟩
  · exact
      { base := rfl
        periodic := fun _ _ x => hφ.periodic r hr x
        memX := fun _ _ => hφ.memX r (Ico_subset_Icc_self hr)
        deriv := fun _ _ hw => by omega }
  · exact (hφ.strongCont r (Ico_subset_Icc_self hr)).mono_left
      (nhdsWithin_mono r Ico_subset_Icc_self)

/-- Uniform sup bound on the velocity components of a `PartI.IsBUCTrain` on `[0, T] × ℝ²`. -/
theorem buc_vel_bound {ν c : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {T : ℝ} (hT0 : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ (x : ℝ × ℝ) (j : Fin 2), |tr.v r x j| ≤ C := by
  obtain ⟨M₀, hM₀⟩ := hbuc.deriv_bound hT0 0
  refine ⟨max M₀ 0, le_max_right _ _, fun r hr x j => ?_⟩
  have h1 : ‖tr.v r x‖ ≤ M₀ := by
    simpa [norm_iteratedFDeriv_zero] using hM₀ r hr x
  have h2 : |tr.v r x j| ≤ ‖tr.v r x‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (tr.v r x) j
  exact (h2.trans h1).trans (le_max_left _ _)

/-- Multiplication by `-v_j(r)` on `AdjX c m` for a `BUC` train (valid for every `0 < c`). -/
theorem freeTransport_of_buc {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) (m T : ℝ) (hT0 : 0 ≤ T) :
    ∃ (C : ℝ) (Mv : ℝ → Fin 2 → AdjX c m →L[ℂ] AdjX c m),
      0 ≤ C ∧
      (∀ r ∈ Icc 0 T, ∀ j, ‖Mv r j‖ ≤ C) ∧
      (∀ j w, ContinuousOn (fun r => Mv r j w) (Icc 0 T)) ∧
      ∀ r ∈ Icc 0 T, ∀ j w, ⇑(Mv r j w) =ᵐ[B0579.cellMeasure c (-m)]
        fun x => -((tr.v r x j : ℝ) : ℂ) * w x := by
  obtain ⟨C, hC0, hCb⟩ := buc_vel_bound hbuc hT0
  have hG_meas : ∀ r j, AEStronglyMeasurable (velCoordG tr T j r) (B0579.cellMeasure c (-m)) :=
    fun r j => (velCoordG_continuous tr hT0 j r).aestronglyMeasurable
  have hG_bd : ∀ r j, ∀ᵐ x ∂B0579.cellMeasure c (-m), ‖velCoordG tr T j r x‖ ≤ C :=
    fun r j => Eventually.of_forall fun x => by
      unfold velCoordG
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact hCb (clampT T r) (clampT_mem hT0 r) x j
  refine ⟨C, fun r j => mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j), hC0,
    fun r _ j => norm_mulBddCLM_le _ _ hC0 _, ?_, ?_⟩
  · intro j w r₀ hr₀
    unfold ContinuousWithinAt
    rw [tendsto_iff_norm_sub_tendsto_zero]
    let H : ℝ → ℝ × ℝ → ℂ := fun r x => velCoordG tr T j r x * w x
    have key : Tendsto (fun r => eLpNorm (fun x => H r x - H r₀ x) 2 (B0579.cellMeasure c (-m)))
        (𝓝[Icc 0 T] r₀) (𝓝 0) := by
      refine adjTT_dct (l := 𝓝[Icc 0 T] r₀) (K := 2 * C) (by linarith) ?_ (Lp.memLp w) ?_ ?_
      · intro r
        exact (((hG_meas r j).mul (Lp.aestronglyMeasurable w)).sub
          ((hG_meas r₀ j).mul (Lp.aestronglyMeasurable w))).aemeasurable
      · intro r
        filter_upwards [hG_bd r j, hG_bd r₀ j] with x h1 h2
        calc ‖velCoordG tr T j r x * w x - velCoordG tr T j r₀ x * w x‖
            ≤ ‖velCoordG tr T j r x * w x‖ + ‖velCoordG tr T j r₀ x * w x‖ := norm_sub_le _ _
          _ ≤ C * ‖w x‖ + C * ‖w x‖ := by
              rw [norm_mul, norm_mul]
              exact add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
                (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
          _ = 2 * C * ‖w x‖ := by ring
      · intro x
        have hc0 : ContinuousWithinAt (fun r => velCoordG tr T j r x) (Icc 0 T) r₀ :=
          velCoordG_contWithin tr hT0 j x hr₀
        have h1 : Tendsto (fun r => velCoordG tr T j r x * w x) (𝓝[Icc 0 T] r₀)
            (𝓝 (velCoordG tr T j r₀ x * w x)) := (hc0.mul_const (w x)).tendsto
        simpa using h1.sub (tendsto_const_nhds (x := velCoordG tr T j r₀ x * w x))
    have hEqn : ∀ r ∈ Icc 0 T, ‖mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w
        - mulBddCLM (velCoordG tr T j r₀) (hG_meas r₀ j) hC0 (hG_bd r₀ j) w‖ =
        ENNReal.toReal (eLpNorm (fun x => H r x - H r₀ x) 2 (B0579.cellMeasure c (-m))) := by
      intro r _
      rw [Lp.norm_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub
          (mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w)
          (mulBddCLM (velCoordG tr T j r₀) (hG_meas r₀ j) hC0 (hG_bd r₀ j) w),
        mulBddCLM_apply_ae _ (hG_meas r j) hC0 (hG_bd r j) w,
        mulBddCLM_apply_ae _ (hG_meas r₀ j) hC0 (hG_bd r₀ j) w] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have key2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp key
    simp only [ENNReal.toReal_zero] at key2
    refine key2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hEqn r hr).symm
  · intro r hr j w
    filter_upwards [mulBddCLM_apply_ae (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w]
      with x hx
    show (mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w) x = _
    rw [hx, velCoordG, clampT_of_mem hr]

/-- Tested split of `freeAdjIntegrand` for the transport operator `A r w = (Mv r · w, 0)`. -/
theorem freeAid_split {ν c m : ℝ} (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    {s : ℝ} {Mv : ℝ → Fin 2 → AdjX c m →L[ℂ] AdjX c m}
    (hMvae : ∀ r ∈ Icc 0 s, ∀ j w, ⇑(Mv r j w) =ᵐ[B0579.cellMeasure c (-m)]
      fun x => -((tr.v r x j : ℝ) : ℂ) * w x)
    {r : ℝ} (hr : r ∈ Icc 0 s) (w : AdjX c m) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (freeAdjIntegrand tr (⇑w) r ψ) (B0579.cell c) ∧
      ∫ x in B0579.cell c, freeAdjIntegrand tr (⇑w) r ψ x =
        (ν : ℂ) * (∫ x in B0579.cell c, w x * (lapP ψ x : ℂ)) +
          ((∫ x in B0579.cell c, Mv r 0 w x * (B0579.pd 0 ψ x : ℂ)) +
            (∫ x in B0579.cell c, Mv r 1 w x * (B0579.pd 1 ψ x : ℂ)) + 0) := by
  have hIΔ := ((adjPairing c m hc (lapP ψ) (isCylTest_lapP hψ)).1 w).const_mul (ν : ℂ)
  have hIm0 := (adjPairing c m hc (B0579.pd 0 ψ) (hψ.pd 0)).1 (Mv r 0 w)
  have hIm1 := (adjPairing c m hc (B0579.pd 1 ψ) (hψ.pd 1)).1 (Mv r 1 w)
  have hae0 : (fun x => Mv r 0 w x * (B0579.pd 0 ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => -((tr.v r x 0 : ℝ) : ℂ) * w x * (B0579.pd 0 ψ x : ℂ) :=
    ((B0579.ac_cellMeasure c (-m)).ae_eq (hMvae r hr 0 w)).mono fun x hx => by simp only [hx]
  have hae1 : (fun x => Mv r 1 w x * (B0579.pd 1 ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => -((tr.v r x 1 : ℝ) : ℂ) * w x * (B0579.pd 1 ψ x : ℂ) :=
    ((B0579.ac_cellMeasure c (-m)).ae_eq (hMvae r hr 1 w)).mono fun x hx => by simp only [hx]
  have hIv0 : IntegrableOn (fun x => -((tr.v r x 0 : ℝ) : ℂ) * w x * (B0579.pd 0 ψ x : ℂ))
      (B0579.cell c) := hIm0.congr hae0
  have hIv1 : IntegrableOn (fun x => -((tr.v r x 1 : ℝ) : ℂ) * w x * (B0579.pd 1 ψ x : ℂ))
      (B0579.cell c) := hIm1.congr hae1
  have hIv : IntegrableOn
      (fun x => -((tr.v r x 0 : ℝ) : ℂ) * w x * (B0579.pd 0 ψ x : ℂ) +
        -((tr.v r x 1 : ℝ) : ℂ) * w x * (B0579.pd 1 ψ x : ℂ))
      (B0579.cell c) := hIv0.add hIv1
  have hpt : ∀ x, freeAdjIntegrand tr (⇑w) r ψ x =
      (ν : ℂ) * (w x * (lapP ψ x : ℂ)) +
        (-((tr.v r x 0 : ℝ) : ℂ) * w x * (B0579.pd 0 ψ x : ℂ) +
          -((tr.v r x 1 : ℝ) : ℂ) * w x * (B0579.pd 1 ψ x : ℂ)) := by
    intro x
    unfold freeAdjIntegrand UnforcedLeray.Short.IIb.lapP lapP
    push_cast
    ring
  refine ⟨(hIΔ.add hIv).congr (Eventually.of_forall fun x => (hpt x).symm), ?_⟩
  simp_rw [hpt]
  rw [integral_add hIΔ hIv, integral_const_mul, integral_add hIv0 hIv1,
    integral_congr_ae hae0.symm, integral_congr_ae hae1.symm, add_zero]

/-- **Weak existence for `t < s`** (SP 2819-2836, 2937-2958, 3060): Volterra construction on
`AdjX c m` (`c = ν⁻²`) for any `0 < ν`, `8 < m`, and `PartI.IsBUCTrain tr`. -/
theorem freeAdjWeak_exists {ν m : ℝ} (hm : 8 < m) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} (hgm : MemLp g 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) :
    ∃ φ : ℝ → ℝ × ℝ → ℂ, IsFreeAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hs : 0 ≤ s := ht.trans hts.le
  obtain ⟨H, hH⟩ := adjHeatExists m hm ν c hν hc
  obtain ⟨C, Mv, hC0, hMvb, hMvc, hMvae⟩ := freeTransport_of_buc tr hbuc m s hs
  let A : ℝ → AdjX c m →L[ℂ] AdjY c m := fun r => (ContinuousLinearMap.pi (Mv r)).prod 0
  have hAb : ∀ r ∈ Icc 0 s, ‖A r‖ ≤ C := by
    intro r hr
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun w => ?_
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg w))).2 fun j => ?_
      exact (ContinuousLinearMap.le_opNorm (Mv r j) w).trans
        (mul_le_mul_of_nonneg_right (hMvb r hr j) (norm_nonneg w))
    · change ‖(0 : AdjX c m)‖ ≤ C * ‖w‖
      rw [norm_zero]
      exact mul_nonneg hC0 (norm_nonneg w)
  have hAc : ∀ w, ContinuousOn (fun r => A r w) (Icc 0 s) := fun w =>
    (continuousOn_pi.2 fun j => hMvc j w).prodMk continuousOn_const
  set gL : AdjX c m := hgm.toLp g
  have hgL : (⇑gL : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] g :=
    (B0579.ac_cellMeasure c (-m)).ae_le hgm.coeFn_toLp
  set D := adjVData hs H A C hAb hAc
  have hDc : D.Compatible := adjVData_compatible hs H A C hAb hAc
  have hD0 : D.S₀ 0 = ContinuousLinearMap.id ℂ (AdjX c m) := H.S₀_zero
  set Φ : ℝ → AdjX c m := fun τ => D.evolution τ 0 gL
  have hΦc : ContinuousOn Φ (Ici 0) := VolterraData.continuousOn_evolution hDc 0 gL
  have hΦ0 : Φ 0 = gL := evolution_zero_zero D hDc hD0 gL
  have hsub : ∀ r ∈ Icc t s, s - r ∈ Icc (0 : ℝ) s := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hΦs : ContinuousOn (fun r => Φ (s - r)) (Icc t s) :=
    hΦc.comp (continuousOn_const.sub continuousOn_id) fun r hr => (hsub r hr).1
  have key : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      (∀ r ∈ Icc t s,
        IntegrableOn (freeAdjIntegrand tr (perRep c ⇑(Φ (s - r))) r ψ) (B0579.cell c)) ∧
      IntervalIntegrable (fun r => ∫ x in B0579.cell c,
        freeAdjIntegrand tr (perRep c ⇑(Φ (s - r))) r ψ x) volume t s ∧
      ∀ r ∈ Icc t s, ∫ x in B0579.cell c, perRep c ⇑(Φ (s - r)) x * (ψ x : ℂ) =
        (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ r' in r..s, ∫ x in B0579.cell c,
          freeAdjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ x := by
    intro ψ hψ
    obtain ⟨-, Lψ, hLψ⟩ := adjPairing c m hc ψ hψ
    obtain ⟨-, LΔ, hLΔ⟩ := adjPairing c m hc (lapP ψ) (isCylTest_lapP hψ)
    obtain ⟨-, L0, hL0⟩ := adjPairing c m hc (B0579.pd 0 ψ) (hψ.pd 0)
    obtain ⟨-, L1, hL1⟩ := adjPairing c m hc (B0579.pd 1 ψ) (hψ.pd 1)
    let ℓ' : AdjX c m →L[ℂ] ℂ := (ν : ℂ) • LΔ
    have hℓ' : ∀ w : AdjX c m, ℓ' w = (ν : ℂ) * ∫ x in B0579.cell c, w x * (lapP ψ x : ℂ) :=
      fun w => by simp [ℓ', hLΔ]
    let ℓB : AdjY c m →L[ℂ] ℂ :=
      L0.comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => AdjX c m) 0).comp
          (ContinuousLinearMap.fst ℂ _ _)) +
        L1.comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => AdjX c m) 1).comp
          (ContinuousLinearMap.fst ℂ _ _)) +
        Lψ.comp (ContinuousLinearMap.snd ℂ _ _)
    have hℓB : ∀ y : AdjY c m,
        ℓB y = (∫ x in B0579.cell c, (y.1 0) x * (B0579.pd 0 ψ x : ℂ)) +
          (∫ x in B0579.cell c, (y.1 1) x * (B0579.pd 1 ψ x : ℂ)) +
          ∫ x in B0579.cell c, y.2 x * (ψ x : ℂ) := fun y => by simp [ℓB, hL0, hL1, hLψ]
    have hW := volterraWeakForm (AdjX c m) (AdjY c m) D hDc hD0 Lψ ℓ' ℓB
      (fun x τ hτ => by simp only [hLψ, hℓ']; exact hH.1 x ψ hψ τ hτ)
      (fun F a b hab hba hF τ hτ => by simp only [hLψ, hℓ', hℓB]; exact hH.2 F a b hab hba hF ψ hψ τ hτ)
    set f : ℝ → ℂ := fun σ => ℓ' (Φ σ) + ℓB (D.B σ (Φ σ)) with hf_def
    have hWΦ : ∀ τ : ℝ, 0 ≤ τ → Lψ (Φ τ) = Lψ gL + ∫ σ in (0 : ℝ)..τ, f σ :=
      fun τ hτ => hW gL τ hτ
    have hcellEq : ∀ (w : AdjX c m) (r : ℝ), EqOn (freeAdjIntegrand tr (⇑w) r ψ)
        (freeAdjIntegrand tr (perRep c ⇑w) r ψ) (B0579.cell c) := by
      intro w r x hx
      simp only [freeAdjIntegrand, perRep_of_mem_cell hc _ hx]
    have hfeq : ∀ σ ∈ Icc (0 : ℝ) s, f σ = ∫ x in B0579.cell c,
        freeAdjIntegrand tr (perRep c ⇑(Φ σ)) (s - σ) ψ x := by
      intro σ hσ
      have hr : s - σ ∈ Icc (0 : ℝ) s := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
      have hB : D.B σ = A (s - σ) := adjVData_B hs H A C hAb hAc hr
      obtain ⟨-, heq⟩ := freeAid_split hc tr hMvae hr (Φ σ) hψ
      rw [← setIntegral_congr_fun (B0579.measurableSet_cell c) (hcellEq (Φ σ) (s - σ)), heq]
      have hz : ∫ x in B0579.cell c, ((0 : AdjX c m) : ℝ × ℝ → ℂ) x * (ψ x : ℂ) = 0 := by
        have := Lψ.map_zero
        simpa [hLψ] using this
      simp only [hf_def, hB, hℓ', hℓB, A, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.pi_apply, zero_apply, hz]
    have hBc : ContinuousOn (fun σ => D.B σ (Φ σ)) (Ici 0) :=
      continuousOn_clm_apply (fun e => (D.continuous_B e).continuousOn)
        (fun _ _ => ⟨D.β, Eventually.of_forall fun σ => D.norm_B_le σ⟩) hΦc
    have hfc : ContinuousOn f (Ici 0) :=
      (ℓ'.continuous.comp_continuousOn hΦc).add (ℓB.continuous.comp_continuousOn hBc)
    refine ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩
    · obtain ⟨hint, -⟩ := freeAid_split hc tr hMvae ⟨ht.trans hr.1, hr.2⟩ (Φ (s - r)) hψ
      exact hint.congr_fun (hcellEq _ r) (B0579.measurableSet_cell c)
    · have hcont : ContinuousOn (fun r => f (s - r)) (Icc t s) :=
        hfc.comp (continuousOn_const.sub continuousOn_id) fun r hr => (hsub r hr).1
      refine (hcont.congr fun r hr => ?_).intervalIntegrable_of_Icc hts.le
      rw [hfeq (s - r) (hsub r hr), sub_sub_cancel]
    · have h1 : ∫ x in B0579.cell c, perRep c ⇑(Φ (s - r)) x * (ψ x : ℂ) = Lψ (Φ (s - r)) := by
        rw [hLψ]
        refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x hx => ?_
        simp only [perRep_of_mem_cell hc _ hx]
      have h2 : Lψ gL = ∫ x in B0579.cell c, g x * (ψ x : ℂ) := by
        rw [hLψ]
        exact integral_congr_ae (hgL.mono fun x hx => by simp only [hx])
      have h3 : ∫ σ in (0 : ℝ)..(s - r), f σ = ∫ r' in r..s, ∫ x in B0579.cell c,
          freeAdjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ x := by
        have hc3 : ∫ σ in (0 : ℝ)..(s - r), f σ = ∫ σ in (0 : ℝ)..(s - r),
            (fun r' => ∫ x in B0579.cell c,
              freeAdjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ x) (s - σ) := by
          refine intervalIntegral.integral_congr fun σ hσ => ?_
          have hrs : 0 ≤ s - r := by linarith [hr.2]
          rw [uIcc_of_le hrs] at hσ
          have hσs : σ ∈ Icc (0 : ℝ) s := ⟨hσ.1, by linarith [hσ.2, hr.1]⟩
          simp only [hfeq σ hσs, sub_sub_cancel]
        rw [hc3, intervalIntegral.integral_comp_sub_left
          (fun r' => ∫ x in B0579.cell c, freeAdjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ x) s]
        simp only [sub_sub_cancel, sub_zero]
      rw [h1, hWΦ (s - r) (by linarith [hr.2]), h2, h3]
  refine ⟨fun r => perRep c ⇑(Φ (s - r)), ?_⟩
  refine
    { terminal := ?_
      memX := fun r _ => (Lp.memLp (Φ (s - r))).ae_eq (perRep_ae_cellMeasure hc (-m) _).symm
      strongCont := fun r hr => ?_
      periodic := fun r _ x => perRep_periodic hc _ x
      integrable := fun ψ hψ => (key ψ hψ).1
      timeIntegrable := fun ψ hψ => (key ψ hψ).2.1
      weak := fun ψ hψ => (key ψ hψ).2.2 }
  · show perRep c ⇑(Φ (s - s)) =ᵐ[volume.restrict (B0579.cell c)] g
    rw [sub_self, hΦ0]
    exact (perRep_ae_cell hc _).trans hgL
  · have hx : ∀ r', xNorm c (-m) (perRep c ⇑(Φ (s - r')) - perRep c ⇑(Φ (s - r))) =
        edist (Φ (s - r')) (Φ (s - r)) := by
      intro r'
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae
        ((perRep_ae_cellMeasure hc (-m) _).sub (perRep_ae_cellMeasure hc (-m) _))
    refine Tendsto.congr (fun r' => (hx r').symm) ?_
    exact tendsto_iff_edist_tendsto_0.1 ((hΦs r hr).tendsto)

/-- Degenerate endpoint case `s = t₁`: the constant periodic representative is a regular flow. -/
theorem freeAdjExists_eq {ν m : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ × ℝ → ℂ} (hgm : MemLp g 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) :
    ∃ φ : ℝ → ℝ × ℝ → ℂ, IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t t g φ := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨C, Mv, -, -, -, hMvae⟩ := freeTransport_of_buc tr hbuc m t ht
  set gL : AdjX c m := hgm.toLp g
  have hgL : (⇑gL : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] g :=
    (B0579.ac_cellMeasure c (-m)).ae_le hgm.coeFn_toLp
  refine ⟨fun _ => perRep c ⇑gL, ?_⟩
  have hempty : Ico t t = (∅ : Set ℝ) := Ico_self t
  refine
    { terminal := (perRep_ae_cell hc _).trans hgL
      memX := fun _ _ => (Lp.memLp gL).ae_eq (perRep_ae_cellMeasure hc (-m) _).symm
      strongCont := fun r _ => by
        have hz : ∀ r' : ℝ, xNorm c (-m) (perRep c ⇑gL - perRep c ⇑gL) = 0 := fun _ => by
          unfold xNorm
          simp
        exact (tendsto_const_nhds (x := (0 : ℝ≥0∞))).congr fun r' => (hz r').symm
      periodic := fun _ hr => False.elim (lt_irrefl t (lt_of_le_of_lt hr.1 hr.2))
      smooth := fun _ hr => False.elim (lt_irrefl t (lt_of_le_of_lt hr.1 hr.2))
      jointSmooth := by
        rw [hempty, empty_prod]
        exact contDiffOn_empty
      memH1 := fun _ hr => False.elim (lt_irrefl t (lt_of_le_of_lt hr.1 hr.2))
      strongContH1 := fun _ hr => False.elim (lt_irrefl t (lt_of_le_of_lt hr.1 hr.2))
      integrable := fun ψ hψ r hr => by
        have hrt : r = t := le_antisymm hr.2 hr.1
        subst hrt
        obtain ⟨hint, -⟩ := freeAid_split hc tr hMvae ⟨ht, le_rfl⟩ gL hψ
        exact hint.congr_fun
          (fun x hx => by simp only [freeAdjIntegrand, perRep_of_mem_cell hc _ hx])
          (B0579.measurableSet_cell c)
      timeIntegrable := fun _ _ => IntervalIntegrable.refl
      weak := fun ψ _ r hr => by
        have hrt : r = t := le_antisymm hr.2 hr.1
        subst hrt
        rw [intervalIntegral.integral_same, add_zero]
        exact integral_congr_ae (((perRep_ae_cell hc _).trans hgL).mono fun x hx => by
          simp only [hx]) }

/-- Differentiated weak equation for `IsFreeAdjointWeak`: continuity and age derivative within
`[t, s]` of every cylinder-test pairing. -/
def FreeTestedDeriv {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
    ContinuousOn (fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x) (Icc t s) ∧
      ∀ r ∈ Icc t s, HasDerivWithinAt (fun r' => ∫ x in B0579.cell c, φ r' x * (ψ x : ℂ))
        (-∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x) (Icc t s) r

/-- `FreeTestedDeriv` from `IsFreeAdjointWeak` and `PartI.IsBUCTrain` (FTC + `weighted_pair_cont`). -/
theorem freeTestedDeriv {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsFreeAdjointWeak ν c m tr t s g φ) :
    FreeTestedDeriv tr t s φ := by
  intro ψ hψ
  have hs : 0 ≤ s := ht.trans hts.le
  obtain ⟨C, hC0, hCb⟩ := buc_vel_bound hbuc hs
  let M : ℝ → ℝ × ℝ → ℝ := fun r x =>
    ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x)
  let B : ℝ × ℝ → ℝ := fun x =>
    |ν| * |lapP ψ x| + C * (|B0579.pd 0 ψ x| + |B0579.pd 1 ψ x|)
  have hBm : MemLp B 2 (B0579.cellMeasure c m) :=
    ((((isCylTest_lapP hψ).memLp m).norm.const_mul |ν|).add
      ((((hψ.pd 0).memLp m).norm.add ((hψ.pd 1).memLp m).norm).const_mul C))
  have hMB : ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell c, |M r x| ≤ B x := by
    intro r hr x _
    have hr0 : r ∈ Icc (0 : ℝ) s := ⟨ht.trans hr.1, hr.2⟩
    have hv0 : |tr.v r x 0 * B0579.pd 0 ψ x| ≤ C * |B0579.pd 0 ψ x| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hCb r hr0 x 0) (abs_nonneg _)
    have hv1 : |tr.v r x 1 * B0579.pd 1 ψ x| ≤ C * |B0579.pd 1 ψ x| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hCb r hr0 x 1) (abs_nonneg _)
    calc |M r x|
        ≤ |ν * lapP ψ x| + |tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x| :=
          abs_sub _ _
      _ ≤ |ν| * |lapP ψ x| + (|tr.v r x 0 * B0579.pd 0 ψ x| + |tr.v r x 1 * B0579.pd 1 ψ x|) := by
          rw [abs_mul]
          exact add_le_add le_rfl (abs_add_le _ _)
      _ ≤ B x := by unfold B; linarith
  have hMm : ∀ r ∈ Icc t s, AEStronglyMeasurable (M r) (volume.restrict (B0579.cell c)) := by
    intro r hr
    have hr0 : 0 ≤ r := ht.trans hr.1
    have hcont : Continuous (M r) :=
      (continuous_const.mul (isCylTest_lapP hψ).continuous).sub
        (((adjTT_coord_cont_x tr hr0 0).mul (hψ.pd 0).continuous).add
          ((adjTT_coord_cont_x tr hr0 1).mul (hψ.pd 1).continuous))
    exact hcont.aestronglyMeasurable
  have hMc : ∀ x ∈ B0579.cell c, ∀ r₀ ∈ Icc t s,
      Tendsto (fun r => M r x) (𝓝[Icc t s] r₀) (𝓝 (M r₀ x)) := by
    intro x _ r₀ hr₀
    have hsubI : Icc t s ⊆ Ici (0 : ℝ) := fun r hr => ht.trans hr.1
    have h0 : ContinuousOn (fun r => tr.v r x 0) (Icc t s) :=
      (adjTT_coord_contOn_s tr x 0).mono hsubI
    have h1 : ContinuousOn (fun r => tr.v r x 1) (Icc t s) :=
      (adjTT_coord_contOn_s tr x 1).mono hsubI
    have hMcont : ContinuousOn (fun r => M r x) (Icc t s) :=
      continuousOn_const.sub
        ((h0.mul continuousOn_const).add (h1.mul continuousOn_const))
    exact (hMcont r₀ hr₀).tendsto
  have hcont : ContinuousOn (fun r => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r) r ψ x)
      (Icc t s) := by
    have hc0 := weighted_pair_cont _root_.weightedCS φ M B hφ.memX hφ.strongCont hBm hMB hMm hMc
    exact hc0
  refine ⟨hcont, fun r hr => ?_⟩
  set I : ℝ → ℂ := fun r' => ∫ x in B0579.cell c, freeAdjIntegrand tr (φ r') r' ψ x
  set G0 : ℂ := ∫ x in B0579.cell c, g x * (ψ x : ℂ)
  have hIt : ∀ u ∈ Icc t s, IntervalIntegrable I volume t u := fun u hu =>
    (hcont.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1
  have hF : ∀ u ∈ Icc t s,
      (fun r' => ∫ x in B0579.cell c, φ r' x * (ψ x : ℂ)) u =
        G0 + ((∫ x in t..s, I x) - ∫ x in t..u, I x) := by
    intro u hu
    have h := hφ.weak ψ hψ u hu
    rw [intervalIntegral.integral_interval_sub_left (hIt s ⟨hts.le, le_rfl⟩) (hIt u hu)]
    exact h
  have h1 : HasDerivWithinAt (fun u => ∫ x in t..u, I x) (I r) (Icc t s) r := by
    have : Fact (r ∈ Icc t s) := ⟨hr⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hIt r hr)
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc r)
      (hcont.continuousWithinAt hr)
  have hderiv : HasDerivWithinAt (fun u => G0 + ((∫ x in t..s, I x) - ∫ x in t..u, I x))
      (-I r) (Icc t s) r :=
    (h1.const_sub (∫ x in t..s, I x)).const_add G0
  exact hderiv.congr (fun u hu => hF u hu) (hF r hr)

end UnforcedLeray.Short.IIIa.ComplFreeRateSub
