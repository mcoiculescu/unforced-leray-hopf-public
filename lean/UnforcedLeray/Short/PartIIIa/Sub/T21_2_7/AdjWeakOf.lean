import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

/-!
# Part III-a, `PartIII-a:T21/2/7/1`: conditional construction of the weak reverse-time adjoint

Source of record: `the November 2 reference manuscript` (SP), line 3060 and lines
2819-2836 (Volterra iteration, heat semigroup and source response, bounded perturbation),
3052-3058 (the adjoint localized interaction). Statements: `AdjWeakDefs.lean`.

Construction (`adjointWeakExistsBdd_of`). Fix `ν > 0`, a train with the bounds `LadTrainBdd` on
`[0, s]`, `0 ≤ t < s` and `G ∈ X_{-m,d_s}`. The terminal datum `g = physAdj a_s G` lies in
`X_{-m,c}` (`AdjTerminalMem`); `H` is the free part (`AdjHeatExists`), `A(r)` the coefficient
(`AdjCoeffExists` on `[0, s]`). The Volterra data `adjVData` has free part `H` and coefficient
`B(σ) = A(s - σ)` (clamped to `[0, s]`, which is only the global domain demanded by
`VolterraData`), so `Φ(τ) = D.evolution τ 0 g` is the reverse-time adjoint at age `s - τ`, and
`φ(r) = perRep c Φ(s - r)`. Strong continuity is `continuousOn_evolution`; the weak identity is
`VolterraWeakForm` applied to the pairings `AdjPairing` with `ψ`, `Δψ`, `∂_kψ`, the split of
`AdjCoeffExists`, and the substitution `σ = s - r'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Infra.VolterraEvolution

/-- The planar Laplacian of a cylinder test is a cylinder test. -/
theorem isCylTest_lapP {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (lapP ψ) := by
  unfold lapP
  have h1 := (hψ.pd 0).pd 0
  have h2 := (hψ.pd 1).pd 1
  refine ⟨h1.smooth.add h2.smooth, fun x => ?_, ?_⟩
  · simp only [h1.periodic x, h2.periodic x]
  · obtain ⟨R, hR⟩ := h1.band
    obtain ⟨R', hR'⟩ := h2.band
    refine ⟨max R R', fun x hx => ?_⟩
    have := hR x (lt_of_le_of_lt (le_max_left _ _) hx)
    have := hR' x (lt_of_le_of_lt (le_max_right _ _) hx)
    simp [*]

/-- The Volterra data of the reverse-time adjoint on `[t, s]`: free part `H`, coefficient
`B(σ) = A(s - σ)` with the age clamped to `[0, s]`. -/
def adjVData {c m s : ℝ} (hs : 0 ≤ s) (H : AdjHeatSupplier c m)
    (A : ℝ → AdjX c m →L[ℂ] AdjY c m) (β : ℝ) (hAb : ∀ r ∈ Icc 0 s, ‖A r‖ ≤ β)
    (hAc : ∀ w, ContinuousOn (fun r => A r w) (Icc 0 s)) :
    VolterraData ℂ (AdjX c m) (AdjY c m) where
  S₀ := H.S₀
  S := H.S
  B := fun σ => A (projIcc 0 s hs (s - σ))
  M₀ := H.M₀
  C₀ := H.C₀
  β := β
  norm_S₀_le := H.norm_S₀_le
  norm_S_le := H.norm_S_le
  norm_B_le := fun σ => hAb _ (projIcc 0 s hs (s - σ)).2
  continuousOn_S₀ := H.continuousOn_S₀
  continuousOn_S := H.continuousOn_S
  continuous_B := fun w => (hAc w).comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc.comp (continuous_const.sub continuous_id)))
    (fun σ => (projIcc 0 s hs (s - σ)).2)

theorem adjVData_compatible {c m s : ℝ} (hs : 0 ≤ s) (H : AdjHeatSupplier c m)
    (A : ℝ → AdjX c m →L[ℂ] AdjY c m) (β : ℝ) (hAb : ∀ r ∈ Icc 0 s, ‖A r‖ ≤ β)
    (hAc : ∀ w, ContinuousOn (fun r => A r w) (Icc 0 s)) :
    (adjVData hs H A β hAb hAc).Compatible :=
  ⟨H.S₀_comp_S₀, H.S₀_comp_S⟩

theorem adjVData_B {c m s : ℝ} (hs : 0 ≤ s) (H : AdjHeatSupplier c m)
    (A : ℝ → AdjX c m →L[ℂ] AdjY c m) (β : ℝ) (hAb : ∀ r ∈ Icc 0 s, ‖A r‖ ≤ β)
    (hAc : ∀ w, ContinuousOn (fun r => A r w) (Icc 0 s)) {σ : ℝ} (hσ : s - σ ∈ Icc 0 s) :
    (adjVData hs H A β hAb hAc).B σ = A (s - σ) := by
  show A (projIcc 0 s hs (s - σ)) = A (s - σ)
  rw [projIcc_of_mem hs hσ]

/-- `E(0, 0) = 1` when `S₀(0) = 1`. -/
theorem evolution_zero_zero {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedSpace ℝ X] [SMulCommClass ℝ ℂ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] (D : VolterraData ℂ X Y) (hD : D.Compatible)
    (h0 : D.S₀ 0 = ContinuousLinearMap.id ℂ X) (x : X) : D.evolution 0 0 x = x := by
  have h := VolterraData.evolution_volterra hD (s := 0) (τ := 0) ⟨le_rfl, by norm_num⟩ x
  rw [h, sub_self, h0, intervalIntegral.integral_same, add_zero, ContinuousLinearMap.id_apply]

/-- **The construction at fixed data** (SP 3060, 2819-2836): the Volterra evolution of the free
part `H` and the coefficient `A` (with its tested split) from the terminal datum `g ∈ X_{-m,c}`,
represented periodically, is a weak reverse-time adjoint on `[t, s]`. -/
theorem adjointWeak_core {ν c m : ℝ} (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t < s) {g : ℝ × ℝ → ℂ}
    (hgm : MemLp g 2 (B0579.cellMeasure c (-m)))
    (H : AdjHeatSupplier c m) (hH : AdjHeatWeak ν c m H)
    (A : ℝ → AdjX c m →L[ℂ] AdjY c m) (β : ℝ) (hAb : ∀ r ∈ Icc 0 s, ‖A r‖ ≤ β)
    (hAc : ∀ w, ContinuousOn (fun r => A r w) (Icc 0 s))
    (hAid : ∀ r ∈ Icc 0 s, ∀ (w : AdjX c m) (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
        B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
          IntegrableOn (adjIntegrand tr (⇑w) r ψ uψ) (B0579.cell c) ∧
          ∫ x in B0579.cell c, adjIntegrand tr (⇑w) r ψ uψ x =
            (ν : ℂ) * (∫ x in B0579.cell c, w x * (lapP ψ x : ℂ)) +
              ((∫ x in B0579.cell c, (A r w).1 0 x * (B0579.pd 0 ψ x : ℂ)) +
                (∫ x in B0579.cell c, (A r w).1 1 x * (B0579.pd 1 ψ x : ℂ)) +
                ∫ x in B0579.cell c, (A r w).2 x * (ψ x : ℂ)))
    (hPair : AdjPairing) (hVW : VolterraWeakForm) :
    ∃ φ : ℝ → ℝ × ℝ → ℂ, IsAdjointWeak ν c m tr t s g φ := by
  have hs : 0 ≤ s := ht.trans hts.le
  set gL : AdjX c m := hgm.toLp g with hgL_def
  have hgL : (⇑gL : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] g :=
    (B0579.ac_cellMeasure c (-m)).ae_le hgm.coeFn_toLp
  set D := adjVData hs H A β hAb hAc with hD_def
  have hDc : D.Compatible := adjVData_compatible hs H A β hAb hAc
  have hD0 : D.S₀ 0 = ContinuousLinearMap.id ℂ (AdjX c m) := H.S₀_zero
  set Φ : ℝ → AdjX c m := fun τ => D.evolution τ 0 gL with hΦ_def
  have hΦc : ContinuousOn Φ (Ici 0) := VolterraData.continuousOn_evolution hDc 0 gL
  have hΦ0 : Φ 0 = gL := evolution_zero_zero D hDc hD0 gL
  have hsub : ∀ r ∈ Icc t s, s - r ∈ Icc (0 : ℝ) s := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hΦs : ContinuousOn (fun r => Φ (s - r)) (Icc t s) :=
    hΦc.comp (continuousOn_const.sub continuousOn_id) fun r hr => (hsub r hr).1
  -- The tested identities, for one test.
  have key : ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ →
      IsKernelBiotSavart c ψ uψ →
      (∀ r ∈ Icc t s,
        IntegrableOn (adjIntegrand tr (perRep c ⇑(Φ (s - r))) r ψ uψ) (B0579.cell c)) ∧
      IntervalIntegrable (fun r => ∫ x in B0579.cell c,
        adjIntegrand tr (perRep c ⇑(Φ (s - r))) r ψ uψ x) volume t s ∧
      ∀ r ∈ Icc t s, ∫ x in B0579.cell c, perRep c ⇑(Φ (s - r)) x * (ψ x : ℂ) =
        (∫ x in B0579.cell c, g x * (ψ x : ℂ)) + ∫ r' in r..s, ∫ x in B0579.cell c,
          adjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ uψ x := by
    intro ψ uψ hψ huψ
    obtain ⟨-, Lψ, hLψ⟩ := hPair c m hc ψ hψ
    obtain ⟨-, LΔ, hLΔ⟩ := hPair c m hc (lapP ψ) (isCylTest_lapP hψ)
    obtain ⟨-, L0, hL0⟩ := hPair c m hc (B0579.pd 0 ψ) (hψ.pd 0)
    obtain ⟨-, L1, hL1⟩ := hPair c m hc (B0579.pd 1 ψ) (hψ.pd 1)
    obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : AdjX c m →L[ℂ] ℂ, ∀ w : AdjX c m,
        ℓ' w = (ν : ℂ) * ∫ x in B0579.cell c, w x * (lapP ψ x : ℂ) :=
      ⟨(ν : ℂ) • LΔ, fun w => by simp [hLΔ]⟩
    obtain ⟨ℓB, hℓB⟩ : ∃ ℓB : AdjY c m →L[ℂ] ℂ, ∀ y : AdjY c m,
        ℓB y = (∫ x in B0579.cell c, (y.1 0) x * (B0579.pd 0 ψ x : ℂ)) +
          (∫ x in B0579.cell c, (y.1 1) x * (B0579.pd 1 ψ x : ℂ)) +
          ∫ x in B0579.cell c, y.2 x * (ψ x : ℂ) :=
      ⟨L0.comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => AdjX c m) 0).comp
          (ContinuousLinearMap.fst ℂ _ _)) +
        L1.comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => AdjX c m) 1).comp
          (ContinuousLinearMap.fst ℂ _ _)) +
        Lψ.comp (ContinuousLinearMap.snd ℂ _ _), fun y => by simp [hL0, hL1, hLψ]⟩
    have hW := hVW (AdjX c m) (AdjY c m) D hDc hD0 Lψ ℓ' ℓB
      (fun x τ hτ => by
        simp only [hLψ, hℓ']
        exact hH.1 x ψ hψ τ hτ)
      (fun F a b hab hba hF τ hτ => by
        simp only [hLψ, hℓ', hℓB]
        exact hH.2 F a b hab hba hF ψ hψ τ hτ)
    -- the integrand of the weak form
    set f : ℝ → ℂ := fun σ => ℓ' (Φ σ) + ℓB (D.B σ (Φ σ)) with hf_def
    have hWΦ : ∀ τ : ℝ, 0 ≤ τ → Lψ (Φ τ) = Lψ gL + ∫ σ in (0 : ℝ)..τ, f σ :=
      fun τ hτ => hW gL τ hτ
    have hcellEq : ∀ (w : AdjX c m) (r : ℝ), EqOn (adjIntegrand tr (⇑w) r ψ uψ)
        (adjIntegrand tr (perRep c ⇑w) r ψ uψ) (B0579.cell c) := by
      intro w r x hx
      simp only [adjIntegrand, perRep_of_mem_cell hc _ hx]
    have hfeq : ∀ σ ∈ Icc (0 : ℝ) s, f σ = ∫ x in B0579.cell c,
        adjIntegrand tr (perRep c ⇑(Φ σ)) (s - σ) ψ uψ x := by
      intro σ hσ
      have hr : s - σ ∈ Icc (0 : ℝ) s := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
      have hB : D.B σ = A (s - σ) := adjVData_B hs H A β hAb hAc hr
      obtain ⟨-, heq⟩ := hAid (s - σ) hr (Φ σ) ψ uψ hψ huψ
      rw [← setIntegral_congr_fun (B0579.measurableSet_cell c) (hcellEq (Φ σ) (s - σ)), heq]
      simp only [hf_def, hB, hℓ', hℓB]
    have hBc : ContinuousOn (fun σ => D.B σ (Φ σ)) (Ici 0) :=
      continuousOn_clm_apply (fun e => (D.continuous_B e).continuousOn)
        (fun _ _ => ⟨D.β, Eventually.of_forall fun σ => D.norm_B_le σ⟩) hΦc
    have hfc : ContinuousOn f (Ici 0) :=
      (ℓ'.continuous.comp_continuousOn hΦc).add (ℓB.continuous.comp_continuousOn hBc)
    refine ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩
    · obtain ⟨hint, -⟩ := hAid r ⟨ht.trans hr.1, hr.2⟩ (Φ (s - r)) ψ uψ hψ huψ
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
          adjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ uψ x := by
        have hc3 : ∫ σ in (0 : ℝ)..(s - r), f σ = ∫ σ in (0 : ℝ)..(s - r),
            (fun r' => ∫ x in B0579.cell c,
              adjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ uψ x) (s - σ) := by
          refine intervalIntegral.integral_congr fun σ hσ => ?_
          have hrs : 0 ≤ s - r := by linarith [hr.2]
          rw [uIcc_of_le hrs] at hσ
          have hσs : σ ∈ Icc (0 : ℝ) s := ⟨hσ.1, by linarith [hσ.2, hr.1]⟩
          simp only [hfeq σ hσs, sub_sub_cancel]
        rw [hc3, intervalIntegral.integral_comp_sub_left
          (fun r' => ∫ x in B0579.cell c, adjIntegrand tr (perRep c ⇑(Φ (s - r'))) r' ψ uψ x) s]
        simp only [sub_sub_cancel, sub_zero]
      have hτ : 0 ≤ s - r := by linarith [hr.2]
      rw [h1, hWΦ (s - r) hτ, h2, h3]
  refine ⟨fun r => perRep c ⇑(Φ (s - r)), ?_⟩
  refine
    { terminal := ?_
      memX := fun r _ => (Lp.memLp (Φ (s - r))).ae_eq (perRep_ae_cellMeasure hc (-m) _).symm
      strongCont := fun r hr => ?_
      periodic := fun r _ x => perRep_periodic hc _ x
      integrable := fun ψ uψ hψ huψ => (key ψ uψ hψ huψ).1
      timeIntegrable := fun ψ uψ hψ huψ => (key ψ uψ hψ huψ).2.1
      weak := fun ψ uψ hψ huψ => (key ψ uψ hψ huψ).2.2 }
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

/-- **Conditional construction of the weak reverse-time adjoint** (SP 3060, 2819-2836,
3052-3058) for `ν ≤ 1` and trains with the time-local bounds `LadTrainBdd`. -/
theorem adjointWeakExistsBdd_of (m : ℝ) (hHeat : AdjHeatExists m) (hCoeff : AdjCoeffExists m)
    (hPair : AdjPairing) (hVW : VolterraWeakForm) (hTerm : AdjTerminalMem m) :
    AdjointWeakExistsBdd m := by
  intro ν hν hν1 tr hbdd t s ht hts G hG
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hs : 0 ≤ s := ht.trans hts.le
  have ha : 1 ≤ clockA ν s := by
    unfold clockA
    have : 0 ≤ ν * s := mul_nonneg hν.le hs
    linarith
  obtain ⟨H, hH⟩ := hHeat ν _ hν hc
  obtain ⟨C, hC⟩ := hbdd s hs
  obtain ⟨A, β, hAb, hAc, hAid⟩ := hCoeff ν hν hν1 tr s C hs hC
  exact adjointWeak_core hc tr ht hts (hTerm _ _ hc ha G hG) H hH A β hAb hAc hAid hPair hVW

/-- **Conditional construction for the BUC train** (`AdjointWeakExistsBUC`): the leaves and the
train bounds `LadTrainBddAll`. -/
theorem adjointWeakExistsBUC_of (m : ℝ) (hB : LadTrainBddAll m) (hHeat : AdjHeatExists m)
    (hCoeff : AdjCoeffExists m) (hPair : AdjPairing) (hVW : VolterraWeakForm)
    (hTerm : AdjTerminalMem m) : AdjointWeakExistsBUC m :=
  adjointWeakExistsBUC_of_bdd m hB (adjointWeakExistsBdd_of m hHeat hCoeff hPair hVW hTerm)

end UnforcedLeray.Short.IIIa
