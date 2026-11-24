import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Inputs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_2.AxiU
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyRealForms
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.InAff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.Envelope
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FrozenPairExists
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.GaussSourcesExist
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.Spine.Proofs.TrainGlobalExistence
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# The wiring of Part III-b into `Spine.PartIIIOutput`: the conditional theorem (`IIIb-D5`)

Source of record: `the November 2 reference manuscript` (73 pages): 5777-5833,
5835-5920, 5922-5985, 2664-2713, 2316-2318, 2505-2524, 5951-5954.

`partIIIOutput_of_inputs` proves `Spine.PartIIIOutput` from the inputs of
`Proofs/Wiring/Inputs.lean`.  The argument, in the source's order:

1. the reference `R`: `γ = Re λ > 0`, `ω ≠ 0`, `σ₀ ∈ (0, 1/4)`, `𝒞(σ₀) ≠ 0`, `𝒥` continuous at
   `σ₀` (`IsReferenceChoice`, 5924-5933); fixed `m_Z = 2` and `[d₋, d₊] = [γ/6, γ/2] ∋ γ/3`;
2. the integers: `k₀` of the error families (IIIb-D4), `Kint` = the maximum of the integers of
   `pairNormAndNearSolver_concrete`, `curvedFlatComparison_concrete`, `plBound_concrete` and the
   standing producer (3927-3946); then `b_win, δ, m₀` (`ConstantsExist`, 5841-5857); `m₀` is the
   threshold of `PartIIIOutput`;
3. given `m ≤ m₀`, `Sig > 0`, `C`, `N` and the backgrounds `B : ℕ → Spine.ShortBackground`:
   `C₀ = max (2 * C) 1`, the exponent `N` of `ρ_b`, then `c'` of the curved-flat comparison and
   `a_s = min{c', γ/100}/10` (`1.1a_s < min{c', γ/100}/4`, `a_s < γ/16`, 5878-5880), the cutoff
   profiles, and the sequence datum `D = seqOf …` with the flat data of the seed kernels;
4. `RepairStanding` (STANDING from BRIDGE and the choices), the flat pin and the flat columns, the
   module inputs, `concrete_energyModes` (5888-5985), and MODE at the levels of `EnergyModes`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

namespace Wiring

/-- The background of level `n` of `seqOf` is the given one (`U = V + r_b`, source 2669-2672). -/
theorem levelU_seqOf (R : Reference) (hc : R.planar.signedCoeff R.σ₀ ≠ 0) (K : ReturnConsts)
    (Sig : ℝ) (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence) (hsm : PartI.TrainStreamSmooth)
    (κ : IIIa.PlanarFrameKernels) (B : ℕ → Spine.ShortBackground) (n : ℕ) :
    ((seqOf R hc K Sig hSig htr hsm κ B).level n).U = (B n).U :=
  rfl

/-- The period `𝒫_n = 2ε_nc_n` of the Spine is that of the sequence (`Train.per = cOf`). -/
theorem shortPeriod_eq (R : Reference) (n : ℕ) :
    Spine.shortPeriod (Spine.nuSeq R n) (Spine.epsSeq R n) =
      2 * retEps R.planar R.σ₀ n * cOf (retNu R.planar R.σ₀ n) := by
  show 2 * Spine.epsSeq R n * Train.per (Spine.nuSeq R n) = _
  rw [per_eq]
  rfl

/-- **The flat pin of `seqOf`** (source 4557-4612): for large `n` flat data of the level's train
exists (`TrainEvolutionExists`, `frozenPairExists` for the seed kernels, `gaussSourcesExist`), so
the flat setting of the level is the actual one. -/
theorem flatPin_seqOf (hTE : FlatSettingInst.TrainEvolutionExists) {R : Reference}
    (hω : R.planar.eigenvalue.im ≠ 0) (hc : R.planar.signedCoeff R.σ₀ ≠ 0) (K : ReturnConsts)
    (Sig : ℝ) (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence) (hsm : PartI.TrainStreamSmooth)
    {κ : IIIa.PlanarFrameKernels} (hκ : IIIa.IsSeedKernels κ) (B : ℕ → Spine.ShortBackground) :
    ∀ᶠ n : ℕ in atTop, (seqOf R hc K Sig hSig htr hsm κ B).IsActualFlat κ 9 n := by
  obtain ⟨ν₁, hν₁, h1⟩ := hTE 9 (by norm_num)
  obtain ⟨ν₂, hν₂, h2⟩ := FlatSettingInst.frozenPairExists κ hκ (IIIa.perFrameFactsAll κ hκ) 9
    (by norm_num)
  filter_upwards [(retNu_tendsto R.σ₀ hω).eventually (ge_mem_nhds (lt_min hν₁ hν₂))] with n hn
  have hpos := retNu_pos R.planar R.σ₀ n
  have hne : Nonempty (FlatSettingInst.FlatInstData κ (retNu R.planar R.σ₀ n)
      (cOf (retNu R.planar R.σ₀ n)) 9 (levelTrain htr R n (B n))) := by
    obtain ⟨ev⟩ := h1 _ ⟨hpos, hn.trans (min_le_left _ _)⟩ _ rfl inferInstance _
      (levelTrain_buc htr R n (B n))
    obtain ⟨pr⟩ := h2 _ ⟨hpos, hn.trans (min_le_right _ _)⟩ _ rfl inferInstance
    obtain ⟨src⟩ := FlatSettingInst.gaussSourcesExist (retNu R.planar R.σ₀ n) 9 hpos
    exact ⟨⟨ev, pr, src⟩⟩
  refine ⟨Classical.choice hne, ?_⟩
  show levelFlatOf κ K.χo (retNu_pos R.planar R.σ₀ n) (retEps R.planar R.σ₀ n)
    (levelTrain htr R n (B n)) = _
  rw [levelFlatOf, dif_pos hne]
  rfl

/-- **The flat Duhamel columns along the sequence** (source 4084-4086, 4557-4612): from the flat
pin, the BUC trains and `isFlatDuhamelColumn_actual` on the window `K_σ₀ ⊆ (0, 1/4)`; the hypothesis
`hflat` of `flatLimit_concrete` and `curvedFlatComparison_concrete`. -/
theorem flatColumns_of_pin (hCol : FlatColumnInput) (hPC : IIIa.PolyCausal) (D : SeqData)
    (hP : IsPlanarReference D.Pl) (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (hpin : FlatPin D) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearInst.Kflat.IsFlatDuhamelColumn (D.flat n)
      (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf := by
  obtain ⟨κ, hfl⟩ := hpin
  obtain ⟨ν₀, hν₀, hcol⟩ :=
    hCol hPC hP (NearInst.isCompact_winK D.σ₀) (NearInst.winK_sub hσ0 hσ1)
  filter_upwards [hfl, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀),
    NearInst.eventually_mu_mem D hω hσ0 hσ1] with n hfln hn hmu z hz
  obtain ⟨FI, hFI⟩ := hfln
  have : Fact (0 < cOf (retNu D.Pl D.σ₀ n)) := ⟨cOf_pos (retNu_pos _ _ n)⟩
  rw [hFI]
  exact hcol _ ⟨retNu_pos _ _ n, hn⟩ 9 κ (D.train n) (D.train_buc n) FI D.K.χo
    (retEps D.Pl D.σ₀ n) (cOf_pos (retNu_pos _ _ n)) (D.mu n z) (hmu z hz) D.K.as D.K.χf

/-- **`Spine.PartIIIOutput` from the inputs** (source 5835-5985): the order of choice,
the sequence datum of the backgrounds, the standing hypotheses, `concrete_energyModes` and MODE. -/
theorem partIIIOutputSeq_of_inputs
    (hEF : ErrorFamilyInput) (hFL : FlatLimitInput) (hPL : PLBoundInput)
    (hCo : ContinuityInput) (hNB : NearBodyInput) (hCol : FlatColumnInput)
    (hSt : StandingInput) (hWA : WardAffineSeq) (hMo : ModeOfReturn)
    (hK : ConstantsExist) (hBr : BackgroundBridge)
    (hNS : NearInst.NearSolverC) (hEx : NearInst.NearOpsExistC) (hFC : NearInst.ForcedColumnC)
    (hPC : IIIa.PolyCausal) (hTE : FlatSettingInst.TrainEvolutionExists)
    (hκex : IIIa.PlanarFrameKernelsExist) :
    Spine.PartIIIOutput := by
  intro R hR
  -- 1. the reference and the fixed choices `m_Z = 2`, `[d₋, d₊] = [γ/6, γ/2]`
  have hP : IsPlanarReference R.planar := hR.1
  have hω : R.planar.eigenvalue.im ≠ 0 := ne_of_lt hR.2.1.2
  have hσ0 : 0 < R.σ₀ := by linarith [hR.2.2.1.1]
  have hσ1 : R.σ₀ < 1 / 4 := by linarith [hR.2.2.1.2]
  have hCσ : R.planar.signedCoeff R.σ₀ ≠ 0 := hR.2.2.2.1
  have hJ : ContinuousAt R.planar.mellinJ R.σ₀ := hR.2.2.2.2
  have hγ : 0 < gRate R.planar := hP.eigenpair.re_pos
  have hdm : 0 < gRate R.planar / 6 := div_pos hγ (by norm_num)
  have hmZ : (3 : ℝ) / 2 < 2 := by norm_num
  -- 2. the integers, then `b_win, δ, m₀`
  obtain ⟨k₀, hk₀⟩ := hEF R.planar R.σ₀ 2 (gRate R.planar / 6) (gRate R.planar / 2)
  obtain ⟨K₁, hK₁⟩ := NearInst.pairNormAndNearSolver_concrete hNS hEx R.planar hP hω R.σ₀ hσ0
    hσ1 2 hmZ (gRate R.planar / 6) (gRate R.planar / 2) hdm
  obtain ⟨K₂, hK₂⟩ := NearInst.curvedFlatComparison_concrete hNS hEx hFC
    NearInst.Body.bodyRealForms sourceLInAff faCoefBound affMEnvelope R.planar hP hω R.σ₀ hσ0
    hσ1 hCσ 2 hmZ (gRate R.planar / 6) (gRate R.planar / 2) hdm
  obtain ⟨K₃, hK₃⟩ := hPL hNS hEx sourceLInAff faCoefBound affMEnvelope R.planar R.σ₀ 2
    (gRate R.planar / 6) (gRate R.planar / 2)
  obtain ⟨K₄, hK₄⟩ := hSt R.planar hP hω R.σ₀ hσ0 hσ1 2 hmZ (gRate R.planar / 6)
    (gRate R.planar / 2) hdm
  obtain ⟨b, δ, m0, hNC, hb0, -, -, hδ1, hm0, hm0b, hm0γ, hkb, hη0, hηγ⟩ :=
    hK (gRate R.planar) (gRate R.planar / 6) (max (max K₁ K₂) (max K₃ K₄)) k₀ hγ hdm
  refine ⟨m0, hm0, fun m hm hmm0 Sig C N hSig B hB => ?_⟩
  -- 3. `C₀ = max (2 * C) 1`, the exponent `N` of `ρ_b`, `c'`, `a_s`, the cutoffs and the sequence datum
  have hC0 : (0 : ℝ) < max (2 * C) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hNC0 := hNC (max (2 * C) 1) hC0
  obtain ⟨c', hc', hCF⟩ := hK₂ b δ m0 (max (2 * C) 1) N Sig
    (Standing.nearChoice_mono (le_trans (le_max_right _ _) (le_max_left _ _)) hNC0) hSig
  have hx : 0 < min c' (gRate R.planar / 100) := lt_min hc' (div_pos hγ (by norm_num))
  obtain ⟨κ, hκ⟩ := hκex
  let K : ReturnConsts :=
    { mZ := 2, m0 := m0, C0 := max (2 * C) 1, k0 := N, as := min c' (gRate R.planar / 100) / 10,
      δ := δ, b := b, χo := outwardCutoffStd, χy := streamCutoffStd, χf := sourceCutoffStd,
      hχo := isOutwardCutoff_std }
  let D : SeqData := seqOf R hCσ K Sig hSig Spine.trainGlobalExistence PartI.trainStreamSmooth κ B
  have has : 0 < D.K.as := div_pos hx (by norm_num)
  have hbr : D.StandingBridge (gRate R.planar / 6) (gRate R.planar / 2) :=
    hBr R hR b m0 (max (2 * C) 1) N m C N (gRate R.planar / 6) (gRate R.planar / 2) Sig hSig
      hb0 hm hmm0 hm0b hC0 (le_max_left _ _) le_rfl hdm (by linarith) (by linarith)
      K rfl rfl rfl rfl hCσ _ _ κ B hB
  have hch : D.StandingChoices (max (max K₁ K₂) (max K₃ K₄)) (gRate R.planar / 6) :=
    { near := hNC0, δ_lt := hδ1, m0_ball := hm0b, m0_small := hm0γ, as_pos := has,
      as_lt := by
        show min c' (gRate R.planar / 100) / 10 < gRate R.planar / 16
        have := min_le_right c' (gRate R.planar / 100)
        linarith
      chiY := isStreamCutoff_std, chiF := isSourceCutoffC_std }
  -- 4. the standing hypotheses, the flat pin and columns, the closing argument
  have hst : D.RepairStanding (gRate R.planar / 6) (gRate R.planar / 2) :=
    hK₄ D rfl rfl rfl (hch.mono (le_trans (le_max_right _ _) (le_max_right _ _))) hbr
  have hpin : FlatPin D := ⟨κ, flatPin_seqOf hTE hω hCσ K Sig hSig _ _ hκ B⟩
  have hflat := flatColumns_of_pin hCol hPC D hP hω hσ0 hσ1 hpin
  let G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)) := fun _ => 0
  have hWA' := hWA D _ _ hst hpin
  have hEM := concrete_energyModes D G (ωb := (k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))
    (ηδ := NearInst.etaDelta (gRate D.Pl) D.K.δ) (cN := c') hγ hω hσ0 has hJ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hb0.le) (div_pos hγ (by norm_num)).le) hm0.le
    hη0 hkb hm0γ hηγ
    (by
      show 1.1 * (min c' (gRate R.planar / 100) / 10) < min c' (gRate R.planar / 100) / 4
      linarith)
    hst.near (hWA'.mono fun n h z hz => (h z hz).1) (hWA'.mono fun n h z hz => (h z hz).2.1)
    (hWA'.mono fun n h z hz => (h z hz).2.2) (hCo D hst G) (hk₀ D rfl rfl rfl hst G)
    (hK₁ D rfl rfl rfl
      (Standing.nearChoice_mono (le_trans (le_max_left _ _) (le_max_left _ _)) hNC0)
      hst.actual hst.inlet G)
    (hK₃ D rfl rfl rfl
      (Standing.nearChoice_mono (le_trans (le_max_left _ _) (le_max_right _ _)) hNC0) hst
      (hNB D hst) G)
    (hCF D rfl rfl rfl rfl rfl rfl rfl rfl rfl has isSourceCutoffC_std isStreamCutoff_std
      hst.actual hst.inlet hflat G)
    (hFL D hst hflat G)
  -- 5. the energy modes at the levels (MODE)
  obtain ⟨z, -, hz⟩ := hEM
  filter_upwards [hz, hst.actual, hst.pins, hst.near, NearInst.eventually_mu_mem D hω hσ0 hσ1,
    pf2b_period_le_one D hst]
    with n hzn hact hpins hnear hmu hP1
  obtain ⟨hzI, T', bv, hT', hDT, hbv, hTM, hb0'⟩ := hzn
  have hzc : z n ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hzI
  have hwin := NearInst.winK_sub hσ0 hσ1 (hmu (z n) hzc)
  obtain ⟨M, -, hM⟩ := hMo D _ _ hst n hact hP1 (z n) hzc (hnear _ hzc) (hpins _ hzc) hwin.1 hwin.2
    T' bv hT' hDT hbv hTM hb0' (B n).a (B n).Q
  refine ⟨M, ?_⟩
  rw [shortPeriod_eq R n, ← levelU_seqOf R hCσ K Sig hSig Spine.trainGlobalExistence
    PartI.trainStreamSmooth κ B n]
  exact hM

end Wiring

/-- **Part III output from the inputs of the wiring** (source 5777-5985 with 2316-2318,
2505-2524, 2664-2713, 5951-5954).  The inputs (`Proofs/Wiring/Inputs.lean`) and their suppliers:
`ErrorFamilyInput` (`errorFamilyBounds_concrete`, IIIb-D4); `FlatLimitInput`
(`flatLimit_concrete`, IIIb-D3); `PLBoundInput` (`plBound_concrete`, C/rep/15);
`ContinuityInput` (`returnNormContinuity_concrete`, C/cont/main); `NearBodyInput` (`nearBody`,
C/rep/11); `FlatColumnInput` (`isFlatDuhamelColumn_actual`, C/flatset/col); `StandingInput`
(`repairStanding_of_inputs` instantiated, C/standing); `WardAffineSeq` (IIIb-D5/3, from
C/rinst/5); `ModeOfReturn` (IIIb-D5/2); `ConstantsExist` (IIIb-D5/4); `BackgroundBridge`
(IIIb-D5/bridge); and the family statements `NearSolverC`, `NearOpsExistC`, `ForcedColumnC`
(near layer, C/near), `IIIa.PolyCausal` (Part III-a), `TrainEvolutionExists`
; `IIIa.PlanarFrameKernelsExist` is the proved
`IIIa.planarFrameKernelsExist` (`PartIII-a/Clock/FrameKernels.lean`), a hypothesis here only
because that file cannot be imported together with `Spine/Proofs/TrainGlobalExistence.lean`
(both close over a declaration `PartI.fderiv_fderiv_apply`: `PartI/Sub/S04.lean` and
`PartI/Sub/PartI_T04_9_1_euc.lean`). -/
theorem partIIIOutput_of_inputs
    (hEF : Wiring.ErrorFamilyInput) (hFL : Wiring.FlatLimitInput) (hPL : Wiring.PLBoundInput)
    (hCo : Wiring.ContinuityInput) (hNB : Wiring.NearBodyInput) (hCol : Wiring.FlatColumnInput)
    (hSt : Wiring.StandingInput) (hWA : Wiring.WardAffineSeq) (hMo : Wiring.ModeOfReturn)
    (hK : Wiring.ConstantsExist) (hBr : Wiring.BackgroundBridge)
    (hNS : NearInst.NearSolverC) (hEx : NearInst.NearOpsExistC) (hFC : NearInst.ForcedColumnC)
    (hPC : IIIa.PolyCausal) (hTE : FlatSettingInst.TrainEvolutionExists)
    (hκex : IIIa.PlanarFrameKernelsExist) :
    Spine.PartIIIOutput :=
  Wiring.partIIIOutputSeq_of_inputs hEF hFL hPL hCo hNB hCol hSt hWA hMo hK hBr hNS hEx
    hFC hPC hTE hκex

end UnforcedLeray.Short.PartIIIb.Concrete
