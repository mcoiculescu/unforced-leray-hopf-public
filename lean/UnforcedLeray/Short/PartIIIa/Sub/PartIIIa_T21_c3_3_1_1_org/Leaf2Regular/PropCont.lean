import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Regular.SourcePath
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc

/-!
# Helper 2 for `ComplSourceRegular` (`PartIII-a:T21/c3/3/1/1/2/2/4`): strong continuity of `U(s, r)`

Source `the November 2 reference manuscript` (SP) lines 2937-2970.

For fixed `s ∈ [t₁, t₂]`, realizes `(r, X) ↦ U s r (X ∘ planeToC)` (for `r ∈ [t₁, s]`, clamped
outside) as a uniformly bounded family of continuous `ℂ`-linear maps
`uOpCLM : ℝ → Planar.L2w m →L[ℂ] Lp ℂ 2 (B0579.cellMeasure (dd ν s) m)`, and proves strong
continuity `ContinuousOn (fun r => uOpCLM ... r X) (Icc t₁ s)` for every `X : Planar.L2w m` via
density of `RelB4locAux.denseClass`, the cylinder-datum pinning of `IsFreeMovingPropagator`, and
joint start-age continuity `RelB4locAux.cyl_joint_tendsto`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  ComplCouplingSub PerturbDuhamelSub ComplMildYAux

namespace ComplFreeRateSub

namespace Leaf2RegularAux

/-! ### Bounded `Lp`-valued realization of the free moving propagator `U s r` -/

/-- Uniform growth bound of `U s r` over `r ∈ [t₁, s]`. -/
def propBoundConst (ν m t₁ s : ℝ) : ℝ :=
  Real.exp (max (normGrowthConst m + 1) 0 * (movingZ ν s - movingZ ν t₁))

theorem propBoundConst_pos (ν m t₁ s : ℝ) : 0 < propBoundConst ν m t₁ s :=
  Real.exp_pos _

private theorem movingZ_mono {ν s σ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (h : s ≤ σ) :
    movingZ ν s ≤ movingZ ν σ := by
  have ha : 0 < clockA ν σ := by have := hs.trans h; unfold clockA; positivity
  have hb : 0 < clockA ν s := by unfold clockA; positivity
  have hsub : movingZ ν σ - movingZ ν s = (σ - s) / (clockA ν σ * clockA ν s) := by
    unfold movingZ
    field_simp
    unfold clockA
    ring
  have hp : 0 ≤ (σ - s) / (clockA ν σ * clockA ν s) :=
    div_nonneg (sub_nonneg.2 h) (mul_pos ha hb).le
  linarith

theorem exp_growth_le_propBoundConst {ν m t₁ s r : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    (hr : r ∈ Icc t₁ s) :
    Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν r)) ≤
      propBoundConst ν m t₁ s := by
  unfold propBoundConst
  apply Real.exp_le_exp.2
  have hz1 : movingZ ν t₁ ≤ movingZ ν r := movingZ_mono hν ht₁ hr.1
  have hzr : movingZ ν r ≤ movingZ ν s := movingZ_mono hν (ht₁.trans hr.1) hr.2
  have hsub0 : 0 ≤ movingZ ν s - movingZ ν r := sub_nonneg.2 hzr
  have hsub_le : movingZ ν s - movingZ ν r ≤ movingZ ν s - movingZ ν t₁ := by linarith
  calc (normGrowthConst m + 1) * (movingZ ν s - movingZ ν r)
      ≤ max (normGrowthConst m + 1) 0 * (movingZ ν s - movingZ ν r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hsub0
    _ ≤ max (normGrowthConst m + 1) 0 * (movingZ ν s - movingZ ν t₁) :=
        mul_le_mul_of_nonneg_left hsub_le (le_max_right _ _)

theorem prop_memLp {ν m t₁ t₂ s r : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U)
    (hs : s ∈ Icc t₁ t₂) (hr : r ∈ Icc t₁ s) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure (dd ν r) m)) :
    MemLp (U s r g) 2 (B0579.cellMeasure (dd ν s) m) :=
  ⟨hU.2.2.2.2 r s hr.1 hr.2 hs.2 g hg,
    lt_of_le_of_lt (hU.1 r s hr.1 hr.2 hs.2 g)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2)⟩

theorem prop_sub_ae {ν m t₁ t₂ s r : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U)
    (hs : s ∈ Icc t₁ t₂) (hr : r ∈ Icc t₁ s) {g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : MemLp g₁ 2 (B0579.cellMeasure (dd ν r) m))
    (h₂ : MemLp g₂ 2 (B0579.cellMeasure (dd ν r) m)) :
    U s r (fun y => g₁ y - g₂ y) =ᵐ[B0579.cellMeasure (dd ν s) m]
      fun y => U s r g₁ y - U s r g₂ y := by
  obtain ⟨hadd, hsmul⟩ := hU.2.2.1 r s hr.1 hr.2 hs.2
  have hfun : (fun y => g₁ y - g₂ y) = fun y => g₁ y + (-1 : ℂ) * g₂ y := by
    funext y; ring
  rw [hfun]
  filter_upwards [hadd g₁ (fun y => (-1 : ℂ) * g₂ y) h₁ (h₂.const_mul (-1 : ℂ)),
    hsmul (-1 : ℂ) g₂ h₂] with y hy1 hy2
  rw [hy1, hy2]
  ring

theorem prop_congr_ae {ν m t₁ t₂ s r : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U)
    (hs : s ∈ Icc t₁ t₂) (hr : r ∈ Icc t₁ s) {g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : MemLp g₁ 2 (B0579.cellMeasure (dd ν r) m))
    (h₂ : MemLp g₂ 2 (B0579.cellMeasure (dd ν r) m))
    (hae : g₁ =ᵐ[B0579.cellMeasure (dd ν r) m] g₂) :
    U s r g₁ =ᵐ[B0579.cellMeasure (dd ν s) m] U s r g₂ := by
  have hdiff0 : (fun y => g₁ y - g₂ y) =ᵐ[B0579.cellMeasure (dd ν r) m] 0 := by
    filter_upwards [hae] with y hy
    simp [hy]
  have hx0 : xNorm (dd ν r) m (fun y => g₁ y - g₂ y) = 0 := by
    unfold xNorm
    exact (eLpNorm_eq_zero_iff (h₁.sub h₂).1 (by norm_num)).2 hdiff0
  have hUb : xNorm (dd ν s) m (U s r (fun y => g₁ y - g₂ y)) = 0 := by
    have hle := hU.1 r s hr.1 hr.2 hs.2 (fun y => g₁ y - g₂ y)
    rw [hx0, mul_zero] at hle
    exact le_antisymm hle bot_le
  have hU0 : U s r (fun y => g₁ y - g₂ y) =ᵐ[B0579.cellMeasure (dd ν s) m] 0 :=
    (eLpNorm_eq_zero_iff (prop_memLp hU hs hr (h₁.sub h₂)).1 (by norm_num)).1 hUb
  filter_upwards [prop_sub_ae hU hs hr h₁ h₂, hU0] with y hsub hz
  have : U s r g₁ y - U s r g₂ y = 0 := hsub.symm.trans hz
  exact sub_eq_zero.1 this

/-- Continuous `ℂ`-linear operator `Planar.L2w m →L[ℂ] Lp ℂ 2 (B0579.cellMeasure (dd ν s) m)`
representing `U s (rho t₁ s r) (· ∘ planeToC)`. -/
def uOpCLM {ν m t₁ t₂ s : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U) (hs : s ∈ Icc t₁ t₂) (r : ℝ) :
    Planar.L2w m →L[ℂ] Lp ℂ 2 (B0579.cellMeasure (dd ν s) m) :=
  LinearMap.mkContinuous
    { toFun := fun X =>
        (prop_memLp hU hs (Leaf4Aux.rho_mem hs.1 r)
            (memLp_planeToC (dd ν (Leaf4Aux.rho t₁ s r)) m X)).toLp
          (U s (Leaf4Aux.rho t₁ s r) (fun y => (X : ℂ → ℂ) (planeToC y)))
      map_add' := fun X Y => by
        set r' := Leaf4Aux.rho t₁ s r
        have hr' : r' ∈ Icc t₁ s := Leaf4Aux.rho_mem hs.1 r
        obtain ⟨hadd, _⟩ := hU.2.2.1 r' s hr'.1 hr'.2 hs.2
        have hRX := memLp_planeToC (dd ν r') m X
        have hRY := memLp_planeToC (dd ν r') m Y
        have hRXY := memLp_planeToC (dd ν r') m (X + Y)
        have hRX_add : MemLp (fun y => (X : ℂ → ℂ) (planeToC y) + (Y : ℂ → ℂ) (planeToC y)) 2
            (B0579.cellMeasure (dd ν r') m) := hRX.add hRY
        have hadd_ae : (fun y : ℝ × ℝ => ((X + Y : Planar.L2w m) : ℂ → ℂ) (planeToC y))
            =ᵐ[B0579.cellMeasure (dd ν r') m]
            fun y => (X : ℂ → ℂ) (planeToC y) + (Y : ℂ → ℂ) (planeToC y) := by
          have h1 := (Planar.volume_ac m).ae_le (Lp.coeFn_add X Y)
          have h2 := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp h1
          filter_upwards [(B0579.cellMeasure_ac (dd ν r') m).ae_le (ae_restrict_of_ae h2)]
            with y hy
          exact hy
        apply Lp.ext
        filter_upwards [(prop_memLp hU hs hr' hRXY).coeFn_toLp,
          Lp.coeFn_add ((prop_memLp hU hs hr' hRX).toLp _)
            ((prop_memLp hU hs hr' hRY).toLp _),
          (prop_memLp hU hs hr' hRX).coeFn_toLp,
          (prop_memLp hU hs hr' hRY).coeFn_toLp,
          prop_congr_ae hU hs hr' hRXY hRX_add hadd_ae,
          hadd _ _ hRX hRY] with y eXY eadd eX eY econg elin
        rw [eXY, econg, elin, eadd, Pi.add_apply, eX, eY]
      map_smul' := fun c X => by
        set r' := Leaf4Aux.rho t₁ s r
        have hr' : r' ∈ Icc t₁ s := Leaf4Aux.rho_mem hs.1 r
        obtain ⟨_, hsmul⟩ := hU.2.2.1 r' s hr'.1 hr'.2 hs.2
        have hRX := memLp_planeToC (dd ν r') m X
        have hRcX := memLp_planeToC (dd ν r') m (c • X)
        have hRX_smul : MemLp (fun y => c * (X : ℂ → ℂ) (planeToC y)) 2
            (B0579.cellMeasure (dd ν r') m) := hRX.const_mul c
        have hsmul_ae : (fun y : ℝ × ℝ => ((c • X : Planar.L2w m) : ℂ → ℂ) (planeToC y))
            =ᵐ[B0579.cellMeasure (dd ν r') m]
            fun y => c * (X : ℂ → ℂ) (planeToC y) := by
          have h1 := (Planar.volume_ac m).ae_le (Lp.coeFn_smul c X)
          have h2 := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp h1
          filter_upwards [(B0579.cellMeasure_ac (dd ν r') m).ae_le (ae_restrict_of_ae h2)]
            with y hy
          simpa [smul_eq_mul] using hy
        dsimp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [(prop_memLp hU hs hr' hRcX).coeFn_toLp,
          Lp.coeFn_smul c ((prop_memLp hU hs hr' hRX).toLp _),
          (prop_memLp hU hs hr' hRX).coeFn_toLp,
          prop_congr_ae hU hs hr' hRcX hRX_smul hsmul_ae,
          hsmul c _ hRX] with y ecX esm eX econg elin
        rw [ecX, econg, elin, esm, Pi.smul_apply, eX, smul_eq_mul] }
    (propBoundConst ν m t₁ s) (fun X => by
      set r' := Leaf4Aux.rho t₁ s r
      have hr' : r' ∈ Icc t₁ s := Leaf4Aux.rho_mem hs.1 r
      have hRX := memLp_planeToC (dd ν r') m X
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (propBoundConst_pos ν m t₁ s).le (norm_nonneg X)) ?_
      calc xNorm (dd ν s) m (U s r' (fun y => (X : ℂ → ℂ) (planeToC y)))
          ≤ ENNReal.ofReal
              (Real.exp ((normGrowthConst m + 1) * (movingZ ν s - movingZ ν r'))) *
              xNorm (dd ν r') m (fun y => (X : ℂ → ℂ) (planeToC y)) :=
            hU.1 r' s hr'.1 hr'.2 hs.2 _
        _ ≤ ENNReal.ofReal (propBoundConst ν m t₁ s) * ENNReal.ofReal ‖X‖ :=
            mul_le_mul
              (ENNReal.ofReal_le_ofReal (exp_growth_le_propBoundConst hν ht₁ hr'))
              (xNorm_planeToC_le_norm (dd ν r') m X) bot_le bot_le
        _ = ENNReal.ofReal (propBoundConst ν m t₁ s * ‖X‖) :=
            (ENNReal.ofReal_mul (propBoundConst_pos ν m t₁ s).le).symm)

theorem norm_uOpCLM_le {ν m t₁ t₂ s : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U) (hs : s ∈ Icc t₁ t₂) (r : ℝ) :
    ‖uOpCLM hν ht₁ hU hs r‖ ≤ propBoundConst ν m t₁ s :=
  LinearMap.mkContinuous_norm_le _ (propBoundConst_pos ν m t₁ s).le _

theorem uOpCLM_coeFn_ae {ν m t₁ t₂ s r : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U) (hs : s ∈ Icc t₁ t₂) (hr : r ∈ Icc t₁ s)
    (X : Planar.L2w m) :
    ⇑(uOpCLM hν ht₁ hU hs r X) =ᵐ[B0579.cellMeasure (dd ν s) m]
      U s r (fun y => (X : ℂ → ℂ) (planeToC y)) := by
  have h1 : ⇑(uOpCLM hν ht₁ hU hs r X) =ᵐ[B0579.cellMeasure (dd ν s) m]
      U s (Leaf4Aux.rho t₁ s r) (fun y => (X : ℂ → ℂ) (planeToC y)) :=
    (prop_memLp hU hs (Leaf4Aux.rho_mem hs.1 r)
      (memLp_planeToC (dd ν (Leaf4Aux.rho t₁ s r)) m X)).coeFn_toLp
  simpa only [Leaf4Aux.rho_eq hr] using h1

theorem uOpCLM_toL2w_ae {ν m t₁ t₂ s r : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U) (hs : s ∈ Icc t₁ t₂) (hr : r ∈ Icc t₁ s)
    {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (B0579.cellMeasure (dd ν r) m)) :
    ⇑(uOpCLM hν ht₁ hU hs r (toL2w m (fun z => cellZeroExt (dd ν r) g (cToPlane z))))
      =ᵐ[B0579.cellMeasure (dd ν s) m] U s r g := by
  set X := toL2w m (fun z => cellZeroExt (dd ν r) g (cToPlane z))
  exact (uOpCLM_coeFn_ae hν ht₁ hU hs hr X).trans
    (prop_congr_ae hU hs hr (memLp_planeToC (dd ν r) m X) hg
      (planeToC_toL2w_cellZeroExt_ae (dd ν r) m hg))

/-! ### Strong continuity of `r ↦ uOpCLM ... r X` on `Icc t₁ s` -/

/-- Pointwise 3-epsilon continuity criterion for a uniformly bounded operator family between
two normed spaces from a dense subset at a fixed basepoint. -/
theorem continuousWithinAt_clm_of_dense_bdd {α E F : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {S : Set α} {r₀ : α} (hr₀ : r₀ ∈ S) (T : α → E →L[ℂ] F) {M : ℝ}
    (hM : ∀ r ∈ S, ‖T r‖ ≤ M) {D : Set E} (hD : Dense D)
    (hc : ∀ x ∈ D, ContinuousWithinAt (fun r => T r x) S r₀) (x : E) :
    ContinuousWithinAt (fun r => T r x) S r₀ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM r₀ hr₀)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hpos : 0 < ε / (3 * (M + 1)) := by positivity
  obtain ⟨y, hy, hyD⟩ := Metric.dense_iff.mp hD x _ hpos
  have hy' : dist x y < ε / (3 * (M + 1)) := by simpa [dist_comm] using hy
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hc y hyD) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun q hq hqd => ?_⟩
  have hb : ∀ r ∈ S, dist (T r x) (T r y) < ε / 3 := by
    intro r hr
    rw [dist_eq_norm, ← map_sub]
    calc ‖T r (x - y)‖ ≤ ‖T r‖ * ‖x - y‖ := (T r).le_opNorm _
      _ ≤ M * ‖x - y‖ := by gcongr; exact hM r hr
      _ < (M + 1) * (ε / (3 * (M + 1))) := by
          rw [← dist_eq_norm]
          calc M * dist x y ≤ (M + 1) * dist x y := by gcongr; linarith
            _ < (M + 1) * (ε / (3 * (M + 1))) := by gcongr
      _ = ε / 3 := by field_simp
  have h1 := hb q hq
  have h2 := hb r₀ hr₀
  have h3 := hδ' hq hqd
  calc dist (T q x) (T r₀ x)
      ≤ dist (T q x) (T q y) + dist (T q y) (T r₀ y) + dist (T r₀ y) (T r₀ x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (T r₀ y) (T r₀ x)]; linarith
    _ = ε := by ring

theorem uOpCLM_real_case {ν m t₁ t₂ s r₀ : ℝ} (hm : 8 < m) (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U)
    (hs : s ∈ Icc t₁ t₂) (hr₀ : r₀ ∈ Icc t₁ s)
    {Φr : ℂ → ℝ} (hΦs : ContDiff ℝ ∞ Φr) (hΦc : HasCompactSupport Φr) {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ z : ℂ, dd ν r₀ / 2 - δ < |z.re| → |z.re| < dd ν r₀ / 2 + δ → Φr z = 0)
    (W : Planar.L2w m) (hW : ⇑W =ᵐ[Planar.wMeasure m] fun z => ((Φr z : ℝ) : ℂ)) :
    ContinuousWithinAt (fun r => uOpCLM hν ht₁ hU hs r W) (Icc t₁ s) r₀ := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hm1 : (1 : ℝ) < m := by linarith
  have hs0 : 0 ≤ s := ht₁.trans hs.1
  have hr₀0 : 0 ≤ r₀ := ht₁.trans hr₀.1
  have hApos : ∀ r : ℝ, 0 ≤ r → 0 < clockA ν r := fun r hr => by unfold clockA; positivity
  have har₀ : 0 < clockA ν r₀ := hApos r₀ hr₀0
  have has : 0 < clockA ν s := hApos s hs0
  have hd₀' : |cellLen c (clockA ν r₀) - dd ν r₀| < δ / 2 := by
    change |dd ν r₀ - dd ν r₀| < δ / 2
    rw [sub_self, abs_zero]; exact half_pos hδ
  have hnear : ∀ᶠ r in 𝓝 r₀, |cellLen c (clockA ν r) - dd ν r₀| < δ / 2 := by
    have hc_cell := RelB4locAux.continuousAt_cellLen_comp (c := c) (ν := ν)
      (u := id) continuousAt_id har₀
    have h := Metric.tendsto_nhds.1 hc_cell (δ / 2) (half_pos hδ)
    filter_upwards [h] with r hr
    simpa only [Real.dist_eq, id_eq] using hr
  have hgood : ∀ᶠ r in 𝓝[Icc t₁ s] r₀, r ∈ Icc t₁ s ∧
      |cellLen c (clockA ν r) - dd ν r₀| < δ / 2 :=
    Filter.Eventually.and self_mem_nhdsWithin (hnear.filter_mono nhdsWithin_le_nhds)
  -- choose cylinder flows from `exists_regular_of_test`
  have hex : ∀ r : ℝ, ∃ R : ℝ → B0579.Plane → ℝ, 0 ≤ r →
      B0579.IsCylTest c (RelB4locAux.fData c Φr (clockA ν r)) →
        IIb.IsFreeCylFlow m tr r (RelB4locAux.fData c Φr (clockA ν r)) R := by
    intro r
    by_cases h : 0 ≤ r ∧ B0579.IsCylTest c (RelB4locAux.fData c Φr (clockA ν r))
    · obtain ⟨R, hR, -⟩ := RelB4locAux.exists_regular_of_test hm hν hc htr h.1 h.2
      exact ⟨R, fun _ _ => hR⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Fl hFl using hex
  have hcyl₀ := RelB4locAux.isCylTest_fData hc har₀ hδ hd₀' hΦs hΦc hv
  have hfl₀ := hFl r₀ hr₀0 hcyl₀
  -- identification of `uOpCLM ... r W` with `JscaleInv (clockA ν s) (Fl r s)`
  have hid : ∀ r : ℝ, r ∈ Icc t₁ s → |cellLen c (clockA ν r) - dd ν r₀| < δ / 2 →
      ⇑(uOpCLM hν ht₁ hU hs r W) =ᵐ[B0579.cellMeasure (dd ν s) m]
        JscaleInv (clockA ν s) (fun x => ((Fl r s x : ℝ) : ℂ)) := by
    intro r hr hd
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have har : 0 < clockA ν r := hApos r hr0
    have hcyl := RelB4locAux.isCylTest_fData hc har hδ hd hΦs hΦc hv
    have hfl := hFl r hr0 hcyl
    have hpin : (fun y : ℝ × ℝ => (W : ℂ → ℂ) (planeToC y))
        =ᵐ[B0579.cellMeasure (dd ν r) m]
        JscaleInv (clockA ν r) (fun x => ((RelB4locAux.fData c Φr (clockA ν r) x : ℝ) : ℂ)) := by
      have h2 := ae_eq_cellMeasure_of_wMeasure (dd ν r) m hW
      filter_upwards [h2, ae_cellMeasure_mem_cell (dd ν r) m] with y hy hymem
      rw [hy]
      exact (RelB4locAux.JscaleInv_fData hc har Φr hymem).symm
    have hRW := memLp_planeToC (dd ν r) m W
    have hJmem : MemLp (JscaleInv (clockA ν r)
        (fun x => ((RelB4locAux.fData c Φr (clockA ν r) x : ℝ) : ℂ))) 2
        (B0579.cellMeasure (dd ν r) m) := hRW.ae_eq hpin
    exact (uOpCLM_coeFn_ae hν ht₁ hU hs hr W).trans
      ((prop_congr_ae hU hs hr hRW hJmem hpin).trans
        (hU.2.1 r s hr.1 hr.2 hs.2 _ hcyl (Fl r) hfl))
  -- joint convergence of cylinder flows at `(r, s) → (r₀, s)`
  have hpair : Tendsto (fun r : ℝ => (r, s)) (𝓝[Icc t₁ s] r₀) (𝓝 (r₀, s)) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ q in Filter.map (fun r : ℝ => (r, s)) (𝓝[Icc t₁ s] r₀),
      0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ s ∧
        B0579.IsCylTest c (RelB4locAux.fData c Φr (clockA ν q.1)) ∧
        IIb.IsFreeCylFlow m tr q.1 (RelB4locAux.fData c Φr (clockA ν q.1)) (Fl q.1) := by
    rw [Filter.eventually_map]
    filter_upwards [hgood] with r hr
    obtain ⟨hrI, hd⟩ := hr
    have hr0 : 0 ≤ r := ht₁.trans hrI.1
    have hcyl := RelB4locAux.isCylTest_fData hc (hApos r hr0) hδ hd hΦs hΦc hv
    exact ⟨hr0, hrI.2, le_rfl, hcyl, hFl r hr0 hcyl⟩
  obtain ⟨η, hη, hηc, hvan⟩ := RelB4locAux.fData_vanish hc har₀ hδ hd₀' hv
  have hfa : Tendsto (fun q : ℝ × ℝ => clockA ν q.1)
      (Filter.map (fun r : ℝ => (r, s)) (𝓝[Icc t₁ s] r₀)) (𝓝 (clockA ν r₀)) := by
    have hcont : Continuous (fun q : ℝ × ℝ => clockA ν q.1) := by unfold clockA; fun_prop
    exact (hcont.tendsto _).mono_left hpair
  have hfc : Tendsto (fun q : ℝ × ℝ => eLpNorm (RelB4locAux.fData c Φr (clockA ν q.1) -
      RelB4locAux.fData c Φr (clockA ν r₀)) 2 (B0579.cellMeasure c m))
      (Filter.map (fun r : ℝ => (r, s)) (𝓝[Icc t₁ s] r₀)) (𝓝 0) :=
    RelB4locAux.fData_tendsto hm1 hc W hW har₀ hfa
      (hev.mono fun q hq => (hq.2.2.2.1.continuous.sub hcyl₀.continuous).aestronglyMeasurable)
  have hcj := RelB4locAux.cyl_joint_tendsto hm hν hc htr hs0
    (fun r => RelB4locAux.fData c Φr (clockA ν r)) Fl hr₀0 hr₀.2 le_rfl hcyl₀ hfl₀ hη hηc hvan
    (Filter.map (fun r : ℝ => (r, s)) (𝓝[Icc t₁ s] r₀)) hpair hev hfc
  have hlift : Tendsto (fun r : ℝ => RelB4locAux.liftC c m (Fl r s))
      (𝓝[Icc t₁ s] r₀) (𝓝 (RelB4locAux.liftC c m (Fl r₀ s))) := by
    have h := RelB4locAux.tendsto_liftC (g := fun q : ℝ × ℝ => Fl q.1 q.2)
      (hfl₀.memX s hr₀.2) (hev.mono fun q hq => hq.2.2.2.2.memX _ hq.2.1) hcj
    exact tendsto_map'_iff.1 h
  have hdil_lim : Tendsto
      (fun r : ℝ => RelB4locAux.dilW' hm1 (clockA ν s)⁻¹ (RelB4locAux.liftC c m (Fl r s)))
      (𝓝[Icc t₁ s] r₀)
      (𝓝 (RelB4locAux.dilW' hm1 (clockA ν s)⁻¹ (RelB4locAux.liftC c m (Fl r₀ s)))) :=
    ((RelB4locAux.dilW' hm1 (clockA ν s)⁻¹).continuous.tendsto _).comp hlift
  -- transfer norm convergence from `Planar.L2w m` to `Lp ℂ 2 (B0579.cellMeasure (dd ν s) m)`
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hn_lim := tendsto_iff_norm_sub_tendsto_zero.1 hdil_lim
  refine hn_lim.congr' ?_
  filter_upwards [hgood] with r hr
  obtain ⟨hrI, hd⟩ := hr
  have hr0 : 0 ≤ r := ht₁.trans hrI.1
  have hcyl := RelB4locAux.isCylTest_fData hc (hApos r hr0) hδ hd hΦs hΦc hv
  have hfl := hFl r hr0 hcyl
  have hmem_r : MemLp (Fl r s) 2 (B0579.cellMeasure c m) := hfl.memX s hrI.2
  have hmem_r0 : MemLp (Fl r₀ s) 2 (B0579.cellMeasure c m) := hfl₀.memX s hr₀.2
  have hainv : 0 < (clockA ν s)⁻¹ := inv_pos.2 has
  have hid_r := hid r hrI hd
  have hid_r0 := hid r₀ hr₀ hd₀'
  have hae_U : ⇑(uOpCLM hν ht₁ hU hs r W - uOpCLM hν ht₁ hU hs r₀ W)
      =ᵐ[B0579.cellMeasure (dd ν s) m]
      JscaleInv (clockA ν s) (fun x => (((Fl r s - Fl r₀ s) x : ℝ) : ℂ)) := by
    filter_upwards [Lp.coeFn_sub (uOpCLM hν ht₁ hU hs r W) (uOpCLM hν ht₁ hU hs r₀ W),
      hid_r, hid_r0] with y hy e1 e2
    rw [hy, Pi.sub_apply, e1, e2]
    simp only [JscaleInv, Pi.sub_apply, Complex.ofReal_sub, mul_sub]
  have haesm_J : AEStronglyMeasurable
      (JscaleInv (clockA ν s) (fun x => (((Fl r s - Fl r₀ s) x : ℝ) : ℂ)))
      (B0579.cellMeasure (dd ν s) m) :=
    (Lp.aestronglyMeasurable (uOpCLM hν ht₁ hU hs r W - uOpCLM hν ht₁ hU hs r₀ W)).congr hae_U
  have hae_dil : ⇑(RelB4locAux.dilW' hm1 (clockA ν s)⁻¹ (RelB4locAux.liftC c m (Fl r s)) -
        RelB4locAux.dilW' hm1 (clockA ν s)⁻¹ (RelB4locAux.liftC c m (Fl r₀ s)))
      =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt (dd ν s)
        (JscaleInv (clockA ν s) (fun x => (((Fl r s - Fl r₀ s) x : ℝ) : ℂ))) (cToPlane z) := by
    rw [RelB4locAux.dilW'_of_pos hm1 hainv]
    have hdiff_mem : MemLp (Fl r s - Fl r₀ s) 2 (B0579.cellMeasure c m) := hmem_r.sub hmem_r0
    have hl_sub : RelB4locAux.liftC c m (Fl r s) - RelB4locAux.liftC c m (Fl r₀ s) =
        RelB4locAux.liftC c m (Fl r s - Fl r₀ s) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (RelB4locAux.liftC c m (Fl r s))
          (RelB4locAux.liftC c m (Fl r₀ s)),
        RelB4locAux.coeFn_liftC hmem_r, RelB4locAux.coeFn_liftC hmem_r0,
        RelB4locAux.coeFn_liftC hdiff_mem] with z hz e1 e2 e12
      rw [hz, Pi.sub_apply, e1, e2, e12, RelB4locAux.liftFun_sub, Pi.sub_apply]
    rw [← map_sub, hl_sub]
    filter_upwards [Planar.coeFn_dilW hm1 hainv (RelB4locAux.liftC c m (Fl r s - Fl r₀ s)),
      Planar.dilWFun_congr hainv (RelB4locAux.coeFn_liftC hdiff_mem)] with z h1 h2
    exact h1.trans (h2.trans (RelB4locAux.cellZeroExt_JscaleInv_eq hc has (Fl r s - Fl r₀ s) z).symm)
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae_dil,
    eLpNorm_cellZeroExt_cToPlane (dd ν s) m haesm_J, eLpNorm_congr_ae hae_U, xNorm]

theorem continuousOn_uOpCLM_apply {ν m t₁ t₂ s : ℝ} (hm : 8 < m) (hν : 0 < ν) (ht₁ : 0 ≤ t₁)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ)}
    (hU : IsFreeMovingPropagator ν m tr t₁ t₂ U) (hs : s ∈ Icc t₁ t₂) (X : Planar.L2w m) :
    ContinuousOn (fun r => uOpCLM hν ht₁ hU hs r X) (Icc t₁ s) := by
  intro r₀ hr₀
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr₀0 : 0 ≤ r₀ := ht₁.trans hr₀.1
  have har₀ : 0 < clockA ν r₀ := by unfold clockA; positivity
  have hd₀_pos : 0 < dd ν r₀ := div_pos hc (Real.sqrt_pos.2 har₀)
  refine continuousWithinAt_clm_of_dense_bdd hr₀ (uOpCLM hν ht₁ hU hs)
    (fun r _ => norm_uOpCLM_le hν ht₁ hU hs r)
    (RelB4locAux.dense_denseClass m hd₀_pos) (fun W hWD => ?_) X
  obtain ⟨Φ, hΦs, hΦc, ⟨δ, hδ, hv⟩, hW⟩ := hWD
  have hMΦ : MemLp Φ 2 (Planar.wMeasure m) := (Lp.memLp W).ae_eq hW
  have hΦcont : Continuous Φ := hΦs.continuous
  have hMr : MemLp (fun z => (((Φ z).re : ℝ) : ℂ)) 2 (Planar.wMeasure m) :=
    hMΦ.of_le
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hΦcont)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have hMi : MemLp (fun z => (((Φ z).im : ℝ) : ℂ)) 2 (Planar.wMeasure m) :=
    hMΦ.of_le
      (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hΦcont)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : Planar.L2w m,
      ⇑W₁ =ᵐ[Planar.wMeasure m] fun z => (((Φ z).re : ℝ) : ℂ) := ⟨_, hMr.coeFn_toLp⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : Planar.L2w m,
      ⇑W₂ =ᵐ[Planar.wMeasure m] fun z => (((Φ z).im : ℝ) : ℂ) := ⟨_, hMi.coeFn_toLp⟩
  have hsplit : W = W₁ + Complex.I • W₂ := by
    apply Lp.ext
    filter_upwards [hW, Lp.coeFn_add W₁ (Complex.I • W₂), Lp.coeFn_smul Complex.I W₂, hW₁, hW₂]
      with z h0 h1 h2 h3 h4
    rw [h0, h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul, mul_comm]
    exact (Complex.re_add_im (Φ z)).symm
  have hre : ContDiff ℝ ∞ (fun z => (Φ z).re) := Complex.reCLM.contDiff.comp hΦs
  have him : ContDiff ℝ ∞ (fun z => (Φ z).im) := Complex.imCLM.contDiff.comp hΦs
  have hrec : HasCompactSupport (fun z => (Φ z).re) := hΦc.comp_left Complex.zero_re
  have himc : HasCompactSupport (fun z => (Φ z).im) := hΦc.comp_left Complex.zero_im
  have hc1 := uOpCLM_real_case hm hν ht₁ htr hU hs hr₀ hre hrec hδ
    (fun z h1 h2 => by simp [hv z h1 h2]) W₁ hW₁
  have hc2 := uOpCLM_real_case hm hν ht₁ htr hU hs hr₀ him himc hδ
    (fun z h1 h2 => by simp [hv z h1 h2]) W₂ hW₂
  have hfun : (fun r : ℝ => uOpCLM hν ht₁ hU hs r W) =
      fun r => uOpCLM hν ht₁ hU hs r W₁ + Complex.I • uOpCLM hν ht₁ hU hs r W₂ := by
    funext r; rw [hsplit, map_add, map_smul]
  rw [hfun]
  exact hc1.add (hc2.const_smul Complex.I)

end Leaf2RegularAux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
