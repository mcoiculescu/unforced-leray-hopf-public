import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY.Dil
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY.EPart

/-!
# `PartIII-a:T21/c3/2/1/2/3/1`: Leaf C1 `ComplYExists`

Source of record: `the November 2 reference manuscript` (SP), lines 2914-2925
(the normalised moving complement `r = W - E α` of the actual linearised flow, zero-extended from
the moving cell of length `d(s) = c/√a(s)`, `c = ν⁻²`).

Construction. For an age `r` of the block put `a = a(r)` and, on the fixed cell `c`,
`R(r) = I_c w(r) - Σ_i α_i(r) I_c (a⁻² E_i(·/√a))` (`fixedRep`, `I_c` the zero extension).
Then `J_{1/a} R(r) = I_{d(r)} r(r)` pointwise (`dilWFun_rep_eq`), and
`Y(τ) = N(t₁, s(τ))⁻¹ J_{1/a(s(τ))} R(s(τ))`, `s(τ) = ageAt ν t₁ τ`.

* `R` is continuous on `[t₁, t₂]` in `L²_m`: `w` is strongly continuous in `X_{m,c}`
  (`IsLinearisedFlow.strongCont`), the amplitudes are continuous (`continuousOn_ampl_age`), the
  rescaled frame vectors are continuous in `X_{m,c}` (`tendsto_xNorm_eFun`), and the zero
  extension is an isometry `X_{m,c} → L²_m` (`eLpNorm_cellZeroExt_cToPlane`).
* The dilation is strongly continuous and locally bounded (`continuousAt_dilR_apply`,
  `Planar.norm_dilW_inv_le_of_one_le`), and `N`, `s(τ)` are continuous; hence `Y` is continuous on
  `[0, B]`: a.e. strongly measurable and bounded there.
* The measurability of `compl` at `t₁`, `t₂` follows from the representation at `τ = 0, B`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildYAux

open Classical in
/-- The `L²_m` class of a function (`0` if the function is not in `L²_m`). -/
def toL2w (m : ℝ) (g : ℂ → ℂ) : Planar.L2w m :=
  if h : MemLp g 2 (Planar.wMeasure m) then h.toLp g else 0

theorem coeFn_toL2w {m : ℝ} {g : ℂ → ℂ} (h : MemLp g 2 (Planar.wMeasure m)) :
    ⇑(toL2w m g) =ᵐ[Planar.wMeasure m] g := by
  rw [toL2w, dif_pos h]
  exact h.coeFn_toLp

theorem norm_toL2w_sub {m : ℝ} {g g' : ℂ → ℂ} (h : MemLp g 2 (Planar.wMeasure m))
    (h' : MemLp g' 2 (Planar.wMeasure m)) :
    ‖toL2w m g - toL2w m g'‖ = (eLpNorm (g - g') 2 (Planar.wMeasure m)).toReal := by
  simp only [toL2w, dif_pos h, dif_pos h']
  rw [← MemLp.toLp_sub, Lp.norm_toLp]

/-- Zero extension commutes with differences. -/
theorem cellZeroExt_cToPlane_sub (d : ℝ) (V W : ℝ × ℝ → ℂ) :
    ((fun z : ℂ => cellZeroExt d V (cToPlane z)) - fun z : ℂ => cellZeroExt d W (cToPlane z)) =
      fun z : ℂ => cellZeroExt d (V - W) (cToPlane z) := by
  funext z
  simp only [Pi.sub_apply, cellZeroExt]
  by_cases hz : cToPlane z ∈ B0579.cell d
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

/-- Distance of two zero-extended cell fields in `L²_m`. -/
theorem norm_toL2w_cellZeroExt_sub {c m : ℝ} {V W : ℝ × ℝ → ℂ}
    (hV : MemLp V 2 (B0579.cellMeasure c m)) (hW : MemLp W 2 (B0579.cellMeasure c m)) :
    ‖toL2w m (fun z => cellZeroExt c V (cToPlane z)) -
        toL2w m (fun z => cellZeroExt c W (cToPlane z))‖ = (xNorm c m (V - W)).toReal := by
  rw [norm_toL2w_sub (memLp_cellZeroExt_cToPlane c m hV) (memLp_cellZeroExt_cToPlane c m hW),
    cellZeroExt_cToPlane_sub, eLpNorm_cellZeroExt_cToPlane c m (hV.1.sub hW.1)]

/-- Continuity in `L²_m` of zero-extended cell fields from continuity in `X_{m,c}`. -/
theorem continuousWithinAt_toL2w {c m : ℝ} {V : ℝ → ℝ × ℝ → ℂ} {S : Set ℝ} {s : ℝ}
    (hs : s ∈ S) (hV : ∀ r ∈ S, MemLp (V r) 2 (B0579.cellMeasure c m))
    (hlim : Tendsto (fun r => xNorm c m (V r - V s)) (𝓝[S] s) (𝓝 0)) :
    ContinuousWithinAt (fun r => toL2w m (fun z => cellZeroExt c (V r) (cToPlane z))) S s := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have htoR : Tendsto (fun r => (xNorm c m (V r - V s)).toReal) (𝓝[S] s) (𝓝 0) := by
    have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  refine htoR.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (norm_toL2w_cellZeroExt_sub (hV r hr) (hV s hs)).symm

/-- The fixed-cell representative `R(r) = I_c w(r) - Σ_i α_i(r) I_c (a⁻² E_i(·/√a))`. -/
def fixedRep (κ : PlanarFrameKernels) (m : ℝ) {ν b K : ℝ} (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : Planar.L2w m :=
  toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w r) (cToPlane z)) -
    (ampl (periodizedFrame κ ν m b K hν hF) w r 0 •
        toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 r) (cToPlane z)) +
      ampl (periodizedFrame κ ν m b K hν hF) w r 1 •
        toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 r) (cToPlane z)))

/-- The normalised zero-extended moving complement at age `r`: `N(t₁, r)⁻¹ J_{1/a(r)} R(r)`. -/
def complY (κ : PlanarFrameKernels) (P : PlanarData) (m : ℝ) (hm1 : 1 < m) {ν b K : ℝ}
    (hν : 0 < ν) (hF : PerFrameFacts κ ν m b K) (w : ℝ → ℝ × ℝ → ℂ) (t₁ r : ℝ) :
    Planar.L2w m :=
  (((clockN P ν t₁ r : ℝ) : ℂ))⁻¹ • dilR hm1 (clockA ν r)⁻¹ (fixedRep κ m hν hF w r)

/-- Pointwise: `J_{1/a}` of the fixed-cell representative is the zero-extended complement. -/
theorem dilWFun_rep_eq (κ : PlanarFrameKernels) {ν m b K : ℝ} (hν : 0 < ν)
    (hF : PerFrameFacts κ ν m b K) (w : ℝ → ℝ × ℝ → ℂ) {s : ℝ} (hs : 0 ≤ s) (y : ℂ) :
    Planar.dilWFun (clockA ν s)⁻¹ (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w s) (cToPlane z) -
        (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
            cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z) +
          ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
            cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))) y =
      cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
        (compl (periodizedFrame κ ν m b K hν hF) w s) (cToPlane y) := by
  have ha : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hs)
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hsa : 0 < Real.sqrt (clockA ν s) := Real.sqrt_pos.2 ha
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := div_pos hc hsa
  have hsqrt : (Real.sqrt (clockA ν s)⁻¹)⁻¹ = Real.sqrt (clockA ν s) := by
    rw [Real.sqrt_inv, inv_inv]
  have hfac : (((clockA ν s)⁻¹) ^ 2)⁻¹ = (clockA ν s) ^ 2 := by rw [inv_pow, inv_inv]
  have hcT : cToPlane (Real.sqrt (clockA ν s) • y) =
      (Real.sqrt (clockA ν s) * y.re, Real.sqrt (clockA ν s) * y.im) := by
    simp [cToPlane]
  have hratio : ν ^ (-2 : ℝ) / cellLen (ν ^ (-2 : ℝ)) (clockA ν s) = Real.sqrt (clockA ν s) := by
    rw [cellLen, div_div_eq_mul_div, mul_div_cancel_left₀ _ hc.ne']
  have hmem : (Real.sqrt (clockA ν s) * y.re, Real.sqrt (clockA ν s) * y.im) ∈
        B0579.cell (ν ^ (-2 : ℝ)) ↔
      cToPlane y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) := by
    have := scaleMem_cell_iff hc hd (cToPlane y)
    rw [hratio] at this
    exact this
  simp only [Planar.dilWFun]
  rw [hsqrt, hfac, hcT]
  by_cases hy : cToPlane y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
  · have hy' := hmem.2 hy
    simp only [cellZeroExt, Set.indicator_of_mem hy', Set.indicator_of_mem hy]
    simp only [compl, movingW, JscaleInv, eFun, periodizedFrame, Fin.sum_univ_two, cToPlane,
      mul_div_cancel_left₀ _ hsa.ne']
    have ha' : ((clockA ν s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  · have hy' : (Real.sqrt (clockA ν s) * y.re, Real.sqrt (clockA ν s) * y.im) ∉
        B0579.cell (ν ^ (-2 : ℝ)) := fun h => hy (hmem.1 h)
    simp only [cellZeroExt, Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]
    ring

/-- A representation by a zero extension forces strong measurability on the cell. -/
theorem aesm_of_rep {d m N : ℝ} (hN : N ≠ 0) {V : ℝ × ℝ → ℂ} (Y : Planar.L2w m)
    (hY : ⇑Y =ᵐ[volume] fun z : ℂ => ((N : ℝ) : ℂ)⁻¹ * cellZeroExt d V (cToPlane z)) :
    AEStronglyMeasurable V (B0579.cellMeasure d m) := by
  have hY' : ⇑Y =ᵐ[Planar.wMeasure m]
      fun z : ℂ => ((N : ℝ) : ℂ)⁻¹ * cellZeroExt d V (cToPlane z) :=
    (Planar.wMeasure_ac m).ae_le hY
  have h1 : AEStronglyMeasurable
      (fun z : ℂ => ((N : ℝ) : ℂ)⁻¹ * cellZeroExt d V (cToPlane z)) (Planar.wMeasure m) :=
    (Lp.aestronglyMeasurable Y).congr hY'
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have h2 : AEStronglyMeasurable (fun z : ℂ => cellZeroExt d V (cToPlane z))
      (Planar.wMeasure m) := by
    refine (h1.const_mul ((N : ℝ) : ℂ)).congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ hNc, one_mul]
  have h3 : AEStronglyMeasurable (cellZeroExt d V)
      (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) := by
    refine (h2.comp_measurePreserving (measurePreserving_planeToC_wMeasure m)).congr
      (Eventually.of_forall fun y => ?_)
    simp [cToPlane_planeToC]
  unfold cellZeroExt at h3
  rw [aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell d),
    restrict_withDensity (B0579.measurableSet_cell d)] at h3
  exact h3

end ComplMildYAux

open ComplMildYAux in
/-- **Leaf C1 (`ComplYExists`, SP 2914-2925)**: the normalised zero-extended moving complement
`Y(τ) = N(t₁, s(τ))⁻¹ I_{s(τ)} r(s(τ))` exists in `L²_m`, is continuous (hence a.e. strongly
measurable and bounded) on `[0, B]`, and `compl` is strongly measurable at `t₁` and `t₂`. -/
theorem complYExists (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildSplit.ComplYExists κ := by
  intro _hκ P _hP m hm K B b hB hb ν hν hF tr _htr t₁ t₂ ht₁ h12 hbt hBe f w u hw _hcirc
  have hm1 : (1 : ℝ) < m := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hbr : ∀ r ∈ Icc t₁ t₂, b ≤ clockTheta ν r := fun r hr =>
    hbt.trans (theta_anti hν (ht₁.trans hr.1) hr.2)
  have hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    cellLen_one_le_of_theta hν (ht₁.trans hr.1) hb (hbr r hr)
  have hA1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ clockA ν r := fun r hr =>
    one_le_clockA hν.le (ht₁.trans hr.1)
  have hN_pos : ∀ r, 0 ≤ r → 0 < clockN P ν t₁ r := fun r hr => by
    unfold clockN
    exact mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos (div_pos (theta_pos hν ht₁) (theta_pos hν hr)) _)
  -- continuity of the fixed-cell representative
  have hV : ContinuousOn
      (fun r => toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w r) (cToPlane z)))
      (Icc t₁ t₂) := by
    intro r hr
    refine continuousWithinAt_toL2w hr (fun r' hr' => hw.memX r' hr'.1) ?_
    exact (hw.strongCont r hr.1).mono_left
      (nhdsWithin_mono r fun r' (hr' : r' ∈ Icc t₁ t₂) => (hr'.1 : r' ∈ Ici t₁))
  have hE : ∀ i : Fin 2, ContinuousOn
      (fun r => toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν i r) (cToPlane z)))
      (Icc t₁ t₂) := by
    intro i r hr
    exact continuousWithinAt_toL2w hr (fun r' hr' => memLp_eFun κ hm0 hν ht₁ h12 hd1 i r' hr')
      (tendsto_xNorm_eFun κ hm0 hν ht₁ h12 hd1 i r hr)
  have hA : ∀ i : Fin 2, ContinuousOn (fun r => ampl (periodizedFrame κ ν m b K hν hF) w r i)
      (Icc t₁ t₂) := fun i =>
    continuousOn_ampl_age κ hm hν ht₁ h12 hbt hF hd1 hw i
  have hR : ContinuousOn (fun r => fixedRep κ m hν hF w r) (Icc t₁ t₂) :=
    (hV.sub (((hA 0).smul (hE 0)).add ((hA 1).smul (hE 1)))).congr (fun r _ => rfl)
  -- continuity of the normaliser and of the dilation
  have hNinv : ContinuousOn (fun r => (((clockN P ν t₁ r : ℝ) : ℂ))⁻¹) (Icc t₁ t₂) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hcont : ContinuousAt (fun r => ((clockN P ν t₁ r : ℝ) : ℂ)) r :=
      Complex.continuous_ofReal.continuousAt.comp
        (hasDerivAt_clockN_movBeta0 P hν ht₁ hr0).continuousAt
    exact (hcont.inv₀ (by exact_mod_cast (hN_pos r hr0).ne')).continuousWithinAt
  have hcA : Continuous (fun r => clockA ν r) := by
    unfold clockA; fun_prop
  have hD : ContinuousOn (fun r => dilR hm1 (clockA ν r)⁻¹ (fixedRep κ m hν hF w r))
      (Icc t₁ t₂) := by
    intro r hr
    have hpos : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (hA1 r hr)
    have hbound : ∀ r' ∈ Icc t₁ t₂,
        ‖dilR hm1 (clockA ν r')⁻¹‖ ≤ (clockA ν t₂) ^ (3 / 2 : ℝ) := by
      intro r' hr'
      have h1 := hA1 r' hr'
      rw [dilR_of_pos hm1 (inv_pos.2 (lt_of_lt_of_le zero_lt_one h1))]
      exact (Planar.norm_dilW_inv_le_of_one_le hm1 h1).trans
        (Real.rpow_le_rpow (by linarith) (clockA_mono hν.le hr'.2) (by norm_num))
    have hinv : ContinuousAt (fun r' => (clockA ν r')⁻¹) r :=
      hcA.continuousAt.inv₀ hpos.ne'
    have hstrong : ContinuousWithinAt
        (fun r' => dilR hm1 (clockA ν r')⁻¹ (fixedRep κ m hν hF w r)) (Icc t₁ t₂) r :=
      ((continuousAt_dilR_apply hm1 (fixedRep κ m hν hF w r) (inv_pos.2 hpos)).comp
        (f := fun r' => (clockA ν r')⁻¹) hinv).continuousWithinAt
    exact continuousWithinAt_clm_apply (T := fun r' => dilR hm1 (clockA ν r')⁻¹)
      (g := fun r' => fixedRep κ m hν hF w r') hbound hstrong (hR r hr)
  have hΨ : ContinuousOn (fun r => complY κ P m hm1 hν hF w t₁ r) (Icc t₁ t₂) :=
    (hNinv.smul hD).congr (fun r _ => rfl)
  -- the age map
  have hage : ContinuousOn (ageAt ν t₁) (Icc 0 B) := by
    have h : ContinuousOn
        (fun τ => (movingZ ν t₁ + τ) / (1 - ν * (movingZ ν t₁ + τ))) (Icc 0 B) := by
      refine (continuousOn_const.add continuousOn_id).div
        (continuousOn_const.sub (continuousOn_const.mul (continuousOn_const.add continuousOn_id)))
        (fun τ hτ => ?_)
      have := nu_mul_movingZ_add_lt_one hν ht₂ hBe hτ.2
      exact (sub_pos.2 this).ne'
    exact h.congr (fun τ _ => rfl)
  have hmaps : MapsTo (ageAt ν t₁) (Icc 0 B) (Icc t₁ t₂) := fun τ hτ =>
    ageAt_mem_Icc hν ht₁ h12 hBe hτ
  have hY : ContinuousOn (fun τ => complY κ P m hm1 hν hF w t₁ (ageAt ν t₁ τ)) (Icc 0 B) :=
    hΨ.comp hage hmaps
  -- the representation
  have hrep : ComplMildSplit.YRep κ P m b K B ν hν hF t₁ w
      (fun τ => complY κ P m hm1 hν hF w t₁ (ageAt ν t₁ τ)) := by
    intro τ hτ
    have hs := hmaps hτ
    set s := ageAt ν t₁ τ with hs_def
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have hpos : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (hA1 s hs)
    have hainv : 0 < (clockA ν s)⁻¹ := inv_pos.2 hpos
    have hRrep : ⇑(fixedRep κ m hν hF w s) =ᵐ[Planar.wMeasure m]
        fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w s) (cToPlane z) -
          (ampl (periodizedFrame κ ν m b K hν hF) w s 0 *
              cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z) +
            ampl (periodizedFrame κ ν m b K hν hF) w s 1 *
              cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z)) := by
      unfold fixedRep
      filter_upwards [Lp.coeFn_sub (toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (w s)
          (cToPlane z))) (ampl (periodizedFrame κ ν m b K hν hF) w s 0 •
            toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z)) +
          ampl (periodizedFrame κ ν m b K hν hF) w s 1 •
            toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))),
        Lp.coeFn_add (ampl (periodizedFrame κ ν m b K hν hF) w s 0 •
            toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z)))
          (ampl (periodizedFrame κ ν m b K hν hF) w s 1 •
            toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))),
        Lp.coeFn_smul (ampl (periodizedFrame κ ν m b K hν hF) w s 0)
          (toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 0 s) (cToPlane z))),
        Lp.coeFn_smul (ampl (periodizedFrame κ ν m b K hν hF) w s 1)
          (toL2w m (fun z => cellZeroExt (ν ^ (-2 : ℝ)) (eFun κ ν 1 s) (cToPlane z))),
        coeFn_toL2w (memLp_cellZeroExt_cToPlane (ν ^ (-2 : ℝ)) m (hw.memX s hs.1)),
        coeFn_toL2w (memLp_cellZeroExt_cToPlane (ν ^ (-2 : ℝ)) m
          (memLp_eFun κ hm0 hν ht₁ h12 hd1 0 s hs)),
        coeFn_toL2w (memLp_cellZeroExt_cToPlane (ν ^ (-2 : ℝ)) m
          (memLp_eFun κ hm0 hν ht₁ h12 hd1 1 s hs))] with z e1 e2 e3 e4 e5 e6 e7
      rw [e1, Pi.sub_apply, e2, Pi.add_apply, e3, e4, Pi.smul_apply, Pi.smul_apply, e5, e6, e7,
        smul_eq_mul, smul_eq_mul]
    have hdil : ⇑(dilR hm1 (clockA ν s)⁻¹ (fixedRep κ m hν hF w s)) =ᵐ[Planar.wMeasure m]
        Planar.dilWFun (clockA ν s)⁻¹ ⇑(fixedRep κ m hν hF w s) := by
      rw [dilR_of_pos hm1 hainv]
      exact Planar.coeFn_dilW hm1 hainv _
    have hcongr := Planar.dilWFun_congr (M := m) hainv hRrep
    have hfin : ⇑(complY κ P m hm1 hν hF w t₁ s) =ᵐ[Planar.wMeasure m] fun z : ℂ =>
        ((clockN P ν t₁ s : ℝ) : ℂ)⁻¹ *
          cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
            (compl (periodizedFrame κ ν m b K hν hF) w s) (cToPlane z) := by
      unfold complY
      filter_upwards [Lp.coeFn_smul (((clockN P ν t₁ s : ℝ) : ℂ))⁻¹
          (dilR hm1 (clockA ν s)⁻¹ (fixedRep κ m hν hF w s)), hdil, hcongr]
        with z h1 h2 h3
      rw [h1, Pi.smul_apply, h2, h3, dilWFun_rep_eq κ hν hF w hs0 z, smul_eq_mul]
    exact (Planar.volume_ac m).ae_le hfin
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  refine ⟨fun τ => complY κ P m hm1 hν hF w t₁ (ageAt ν t₁ τ), hrep,
    hY.aestronglyMeasurable measurableSet_Icc, ⟨C, hC⟩, ?_, ?_⟩
  · have h0 := hrep 0 ⟨le_rfl, hB.le⟩
    simp only [ageAt_zero hν ht₁] at h0
    exact aesm_of_rep (hN_pos t₁ ht₁).ne' _ h0
  · have hB' := hrep B ⟨hB.le, le_rfl⟩
    simp only [ageAt_eq_of_movingZ_sub hν ht₂ hBe] at hB'
    exact aesm_of_rep (hN_pos t₂ ht₂).ne' _ hB'

end UnforcedLeray.Short.IIIa
