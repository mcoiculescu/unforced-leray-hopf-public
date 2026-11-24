import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.OldNorm
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L8
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S4

/-!
# `PartIII-b:C/cont/WY` (definitions and reduction): `μ`-Lipschitz continuity of the Ward field `Y[T]`

Source of record: `the November 2 reference manuscript`
(73 pages), lines 3604-3648 (`sep:kernel`, `sep:resolvent`, `sep:young`), 3684-3713 (stream cutoff
majorants), 4161-4216 (`ward:shifted-resolvent`, `ward:cutoff-source`), 4306-4311 (young support),
5684-5685, 5701-5704, 5918-5920.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open WardEMeasAux

/-- **`μ`-Lipschitz `L²` bound of `Y`** in the gained body norm on a compact interval
`[a, b] ⊆ (0, 1/4)` (source 4161-4303, 5701-5704; the `μ`-difference analogue of `WardYBound`,
`ReturnInst/Ward/Defs.lean:236`): for `0 < a`, `b < 1/4`, `ν, R, c > 0` and `IsYoungCutoff χy`,
there is `C` such that for all `μ, μ' ∈ [a, b]` and old `L²` data `g`,
`‖coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)‖_{L²(bodyMeasure)} ≤ C |μ - μ'| ‖g‖_{L²(s^{-1/2}dς)}`. -/
def WardYLipschitz : Prop :=
  ∀ (a b ν R c γ : ℝ) (χy : ℝ → ℝ),
    0 < a → b < 1 / 4 → IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, ∀ μ ∈ Icc a b, ∀ μ' ∈ Icc a b, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      eLpNorm (coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)) 2
          (bodyMeasure c γ ν) ≤
        ENNReal.ofReal (C * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2))

/-- The pinned first component `(wardOps Pl K L μ).1` agrees a.e. with `wardYCoef` when the Ward
pin holds at `μ`. -/
theorem wardOps_fst_ae (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) {μ : ℝ}
    (hpin : ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) ×
        (LStr Pl K L →L[ℝ] LSrc L),
      IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres)
    (T : LStr Pl K L) :
    ((wardOps Pl K L μ).1 T : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      wardYCoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy T := by
  have h := Classical.epsilon_spec hpin
  exact (h T _ _ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).1

/-- Operator-norm continuity of `μ ↦ (wardOps Pl K L μ).1` on a subset `W ⊆ [a, b] ⊂ (0, 1/4)`
where the Ward pin holds, from `WardYLipschitz`. -/
theorem wardOps_fst_continuousOn_of (hLip : WardYLipschitz)
    (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hχy : IsYoungCutoff K.χy)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1 / 4) (W : Set ℝ) (hW : W ⊆ Icc a b)
    (hpin : ∀ μ ∈ W, ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) ×
        (LStr Pl K L →L[ℝ] LSrc L),
      IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres) :
    ContinuousOn (fun μ => (wardOps Pl K L μ).1) W := by
  intro μ0 hμ0
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := wo_rhoB_pos Pl K L hC0
  have hcmp : WardOldNormLe := wardOldNormLe_of gainMeasureLower
  have hold : ∀ T : LStr Pl K L,
      IsOldL2 (cOf L.ν) L.ν (strSum (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) :=
    fun T => wo_isOldL2_rep hcmp hρ hmZ hν K.hχo T
  obtain ⟨C, hC⟩ := hLip a b L.ν L.ε⁻¹ (cOf L.ν) (gRate Pl) K.χy ha hb hχy hν hR hc
  obtain ⟨C', hC'⟩ := hcmp (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρ hmZ hν K.χo K.hχo
  set Lc : ℝ := max C 0 * max C' 0 with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  have hbound : ∀ μ ∈ W,
      ‖(wardOps Pl K L μ).1 - (wardOps Pl K L μ0).1‖ ≤ Lc * |μ - μ0| := by
    intro μ hμ
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hLc0 (abs_nonneg _)) fun T => ?_
    have hae1 := wardOps_fst_ae Pl K L (hpin μ hμ) T
    have hae0 := wardOps_fst_ae Pl K L (hpin μ0 hμ0) T
    have hsub := Lp.coeFn_sub ((wardOps Pl K L μ).1 T) ((wardOps Pl K L μ0).1 T)
    have hae : (((wardOps Pl K L μ).1 - (wardOps Pl K L μ0).1) T : Chart → Merid)
        =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
          wardYCoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy T -
            wardYCoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ0 K.hχo K.χy T := by
      filter_upwards [hsub, hae1, hae0] with p hp hp1 hp0
      change (((wardOps Pl K L μ).1 T - (wardOps Pl K L μ0).1 T : LVel Pl L) : Chart → Merid) p = _
      rw [hp, Pi.sub_apply, hp1, hp0, Pi.sub_apply]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    have h1 := hC μ (hW hμ) μ0 (hW hμ0) _ (hold T)
    have h2 := hC' T
    have hle : eLpNorm (wardYCoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy T -
          wardYCoef (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ0 K.hχo K.χy T) 2
          (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) ≤
        ENNReal.ofReal (Lc * |μ - μ0| * ‖T‖) := by
      calc _ ≤ ENNReal.ofReal (C * |μ - μ0|) *
              eLpNorm (strSum (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) 2
                (ageμ (cOf L.ν) (-1 / 2)) := h1
        _ ≤ ENNReal.ofReal (max C 0 * |μ - μ0|) *
              ENNReal.ofReal (max C' 0 * ‖T‖) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
              (h2.trans (ENNReal.ofReal_le_ofReal ?_))
            · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = ENNReal.ofReal (Lc * |μ - μ0| * ‖T‖) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) (abs_nonneg _))]
            congr 1
            rw [hLc]
            ring
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hT : Tendsto (fun μ : ℝ => Lc * |μ - μ0|) (𝓝[W] μ0) (𝓝 0) := by
    have hc : Continuous (fun μ : ℝ => Lc * |μ - μ0|) :=
      continuous_const.mul (continuous_id.sub continuous_const).abs
    have hz : Lc * |μ0 - μ0| = 0 := by simp
    rw [← hz]
    exact (hc.tendsto μ0).mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) hT)

/-- **`WardYCont`** on the concrete sequence from `WardYLipschitz`
(source 4161-4303, 5684-5685, 5701-5704, 5918-5920). -/
theorem wardYCont_of (hLip : WardYLipschitz) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.WardYCont := by
  filter_upwards [hst.pins, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt]
    with n hp hn
  have hχy : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  have ha : 0 < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  have hb : (D.σ₀ + 1 / 4) / 2 < 1 / 4 := by linarith [hst.sigma_lt]
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  refine wardOps_fst_continuousOn_of hLip D.Pl D.K (D.level n) hst.C0_pos hmZ hχy ha hb (D.win n)
    ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hn z hz
  · rintro _ ⟨z, hz, rfl⟩
    exact (hp z hz).ward

/-- **Leaf 1** (`PartIII-b:C/cont/WY/1`, source 3604-3623, 5701-5704): `μ`-Lipschitz domination of
the separated response `sepW` and its spatial derivatives for `μ, μ' ≥ 0` by the separated-kernel
majorant `sepDom` at the fixed weight `2(-1/8) + 2 = 7/4`. -/
def SepWSubDom : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ μ' rOut rIn P : ℝ),
    0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 ≤ rOut → rOut < rIn → 0 < P →
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T →
    ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
      IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ →
      ‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
          iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y‖ₑ ≤
        ENNReal.ofReal (C * |μ - μ'|) *
          IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) j (rIn - rOut) (IIIa.srcNorm T) τ y

/-- **Leaf 2** (`PartIII-b:C/cont/WY/2`, source 3684-3712, 4181-4214, 5701-5704): pointwise
`μ`-Lipschitz domination of `transField ν μ R c χy g - transField ν μ' R c χy g` by the weighted
transition majorant `transMajA (2 * (-1/8) + 2)` of the cut old source `oldCutSrc`, for `μ, μ' ≥ 0`. -/
def WardYTransSubDom : Prop :=
  ∀ (ν R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
        ‖transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y‖ₑ ≤
          ENNReal.ofReal (C * |μ - μ'|) * transMajA (2 * (-1 / 8 : ℝ) + 2) ν R
            (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y

/-- **Leaf 3** (`PartIII-b:C/cont/WY/3`, source 3631-3648, 2683-2689, 5701-5704): young-chart `L²`
`μ`-Lipschitz bound of the scalar-cutoff part `wardYoungW ν μ R c χy g - wardYoungW ν μ' R c χy g`
for `μ, μ' ≥ 0`. -/
def WardYWSubChart : Prop :=
  ∀ (ν R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        eLpNorm (wardYoungRead ν R
            (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y))
          2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal (C * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2))

namespace WardYContSub

theorem read_sq_le_sub {ν R : ℝ} (hR : 0 < R) {F : ℝ → Space → Space} {C : ℝ} (hC0 : 0 ≤ C)
    {M : ℝ → Space → ℝ≥0∞}
    (hF : ∀ (τ : ℝ) (y : Space), 0 < ϱ y → ‖F τ y‖ₑ ≤ ENNReal.ofReal C * M τ y) (q : Chart) :
    ‖wardYoungRead ν R F q‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (C ^ 2) *
      (ENNReal.ofReal q.1⁻¹ * M (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ)) := by
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos _ hs]
      simp
    · rw [wyl_youngRead_of_young _ hq]
      have hy : 0 < ϱ (NearInst.chartY R q) := by
        rw [ϱ_chartY hR hs]; positivity
      have h1 := hF (NearInst.chartTau R q) _ hy
      have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
      rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hsq.le)
        (norm_nonneg _)), ENNReal.ofReal_mul (inv_nonneg.2 hsq.le), ENNReal.mul_rpow_of_nonneg _ _
        (by norm_num), ofReal_norm]
      have hsc : ENNReal.ofReal (Real.sqrt q.1)⁻¹ ^ (2 : ℝ) = ENNReal.ofReal q.1⁻¹ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hsq.le) (by norm_num)]
        congr 1
        rw [Real.rpow_two, inv_pow, Real.sq_sqrt hs.le]
      rw [hsc]
      have h2 : ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ₑ ^ (2 : ℝ) ≤
          (ENNReal.ofReal C * M (NearInst.chartTau R q) (NearInst.chartY R q)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h2
      have hC : ENNReal.ofReal C ^ (2 : ℝ) = ENNReal.ofReal (C ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC0 (by norm_num), Real.rpow_two]
      rw [hC] at h2
      calc ENNReal.ofReal q.1⁻¹ * ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ₑ ^ (2 : ℝ)
          ≤ ENNReal.ofReal q.1⁻¹ * (ENNReal.ofReal (C ^ 2) *
              M (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ)) := by gcongr
        _ = _ := by ring
  · have : wardYoungRead ν R F q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem (show q ∉ wardYoungSet ν from hq)]
    rw [this]
    simp

/-- Young-chart `L²` bound of `transField ν μ - transField ν μ'` from `WardYTransSubDom` and
`wardYTransMajChartG_proved` at `μ₀ = -1/8`. -/
theorem transSub_chart_le (hT : WardYTransSubDom) {ν R c : ℝ} {χy : ℝ → ℝ}
    (hχy : IsYoungCutoff χy) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        eLpNorm (wardYoungRead ν R
            (fun τ y => transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y))
          2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal (C * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
  obtain ⟨C1, hC1, hD⟩ := hT ν R c χy hχy hν hR hc
  obtain ⟨C2, hC2, hM⟩ := wardYTransMajChartG_proved ν (-1 / 8) R c hν hR hc (by norm_num)
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun μ μ' hμ hμ' g hg => ?_⟩
  set K : ℝ := C1 * |μ - μ'|
  have hK0 : 0 ≤ K := mul_nonneg hC1 (abs_nonneg _)
  have hpt := fun q => read_sq_le_sub (ν := ν) hR hK0
    (M := transMajA (2 * (-1 / 8 : ℝ) + 2) ν R
      (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)))
    (hD μ μ' hμ hμ' g hg) q
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ q, ‖wardYoungRead ν R
        (fun τ y => transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y) q‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2))) ^ (1 / (2 : ℝ))
      ≤ (∫⁻ q, ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal q.1⁻¹ *
          transMajA (2 * (-1 / 8 : ℝ) + 2) ν R
            (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))
            (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ)) ∂(ageμ c (-3 / 2))) ^
          (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ = ENNReal.ofReal K * (∫⁻ q, ENNReal.ofReal q.1⁻¹ *
          transMajA (2 * (-1 / 8 : ℝ) + 2) ν R
            (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))
            (NearInst.chartTau R q) (NearInst.chartY R q) ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^
          (1 / (2 : ℝ)) := by
        have hk : ENNReal.ofReal (K ^ 2) ^ (1 / (2 : ℝ)) = ENNReal.ofReal K := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hK0]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hk]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal C2 * eLpNorm g 2 (ageμ c (-1 / 2))) := by
        gcongr
        exact hM g hg
    _ = ENNReal.ofReal (C1 * C2 * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK0]
        congr 2
        ring

/-- Measurability of the young-chart reading of `wardYoungW_μ - wardYoungW_{μ'}`. -/
theorem wardYWSub_aemeas {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) :
    AEStronglyMeasurable
      (wardYoungRead ν R (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y))
      (ageμ c (-3 / 2)) := by
  have mW1 := WardS4.wardW_meas ν μ R c g hg.measurable
  have mW2 := WardS4.wardW_meas ν μ' R c g hg.measurable
  have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
    have h1 : Measurable fun x : ℝ × Space => ν * age R x.2 := by
      unfold age
      have hϱ : Measurable fun x : ℝ × Space => ϱ x.2 :=
        continuous_ϱ.measurable.comp measurable_snd
      exact measurable_const.mul (measurable_const.div (hϱ.pow_const 2))
    exact hχy.smooth.continuous.measurable.comp h1
  have mYW : Measurable fun x : ℝ × Space =>
      wardYoungW ν μ R c χy g x.1 x.2 - wardYoungW ν μ' R c χy g x.1 x.2 :=
    (hχm.smul mW1).sub (hχm.smul mW2)
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hyoung : MeasurableSet (wardYoungSet ν) :=
    measurableSet_le (measurable_fst.const_mul ν) measurable_const
  unfold wardYoungRead
  exact (((measurable_inv.comp hsq).mul
    (mYW.comp ((WardS4.chartTau_meas R).prodMk (WardS4.chartY_meas R))).norm).indicator
    hyoung).aestronglyMeasurable

/-- Measurability of the young-chart reading of `transField_μ - transField_{μ'}`. -/
theorem wardYTransSub_aemeas {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) :
    AEStronglyMeasurable
      (wardYoungRead ν R (fun τ y => transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y))
      (ageμ c (-3 / 2)) := by
  have hres1 := wardYShiftedRes_proved ν μ R c g hν hR hc hμ hg
  have hres2 := wardYShiftedRes_proved ν μ' R c g hν hR hc hμ' hg
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  have mY1 := WardS4.wardY_offaxis_meas hχy hν hR hc hμ hg
  have mY2 := WardS4.wardY_offaxis_meas hχy hν hR hc hμ' hg
  have mW1 := WardS4.wardW_meas ν μ R c g hg.measurable
  have mW2 := WardS4.wardW_meas ν μ' R c g hg.measurable
  have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
    have h1 : Measurable fun x : ℝ × Space => ν * age R x.2 := by
      unfold age
      have hϱ : Measurable fun x : ℝ × Space => ϱ x.2 :=
        continuous_ϱ.measurable.comp measurable_snd
      exact measurable_const.mul (measurable_const.div (hϱ.pow_const 2))
    exact hχy.smooth.continuous.measurable.comp h1
  have mD : Measurable fun x : ℝ × Space =>
      (wemOff (wardY ν μ R c χy g) x.1 x.2 - χy (ν * age R x.2) • wardW ν μ R c g x.1 x.2) -
        (wemOff (wardY ν μ' R c χy g) x.1 x.2 - χy (ν * age R x.2) • wardW ν μ' R c g x.1 x.2) :=
    (mY1.sub (hχm.smul mW1)).sub (mY2.sub (hχm.smul mW2))
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hyoung : MeasurableSet (wardYoungSet ν) :=
    measurableSet_le (measurable_fst.const_mul ν) measurable_const
  have hFm : Measurable fun p : Chart =>
      ‖(wemOff (wardY ν μ R c χy g) (NearInst.chartTau R p) (NearInst.chartY R p) -
          wardYoungW ν μ R c χy g (NearInst.chartTau R p) (NearInst.chartY R p)) -
        (wemOff (wardY ν μ' R c χy g) (NearInst.chartTau R p) (NearInst.chartY R p) -
          wardYoungW ν μ' R c χy g (NearInst.chartTau R p) (NearInst.chartY R p))‖ :=
    (mD.comp ((WardS4.chartTau_meas R).prodMk (WardS4.chartY_meas R))).norm
  have heq : wardYoungRead ν R
      (fun τ y => transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y) = fun q =>
      (wardYoungSet ν).indicator (fun q => (Real.sqrt q.1)⁻¹ *
        ‖(wemOff (wardY ν μ R c χy g) (NearInst.chartTau R q) (NearInst.chartY R q) -
            wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q)) -
          (wemOff (wardY ν μ' R c χy g) (NearInst.chartTau R q) (NearInst.chartY R q) -
            wardYoungW ν μ' R c χy g (NearInst.chartTau R q) (NearInst.chartY R q))‖) q := by
    funext q
    unfold wardYoungRead
    by_cases hp : 0 < q.1
    · have hy : NearInst.chartY R q ∉ axis := by
        intro h
        have h' : NearInst.chartY R q 0 = 0 ∧ NearInst.chartY R q 1 = 0 := h
        have h1 : NearInst.chartY R q 0 = R / Real.sqrt q.1 := by simp [NearInst.chartY]
        exact (div_ne_zero hR.ne' (Real.sqrt_pos.2 hp).ne') (h1 ▸ h'.1)
      have hy0 : 0 < ϱ (NearInst.chartY R q) := by
        rw [ϱ_chartY hR hp]; positivity
      have hsp1 := wardY_split hχ hν.le hres1 (NearInst.chartTau R q) hy0
      have hsp2 := wardY_split hχ hν.le hres2 (NearInst.chartTau R q) hy0
      have hT1 : transField ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) =
          wardY ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) -
            wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) := by
        rw [hsp1]; abel
      have hT2 : transField ν μ' R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) =
          wardY ν μ' R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) -
            wardYoungW ν μ' R c χy g (NearInst.chartTau R q) (NearInst.chartY R q) := by
        rw [hsp2]; abel
      by_cases hm : q ∈ wardYoungSet ν
      · rw [indicator_of_mem hm, indicator_of_mem hm]
        dsimp only
        rw [hT1, hT2, wem_off_of_not_mem hy, wem_off_of_not_mem hy]
      · rw [indicator_of_notMem hm, indicator_of_notMem hm]
    · have hs : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
      by_cases hm : q ∈ wardYoungSet ν
      · rw [indicator_of_mem hm, indicator_of_mem hm, hs, inv_zero, zero_mul, zero_mul]
      · rw [indicator_of_notMem hm, indicator_of_notMem hm]
  rw [heq]
  exact (((measurable_inv.comp hsq).mul hFm).indicator hyoung).aestronglyMeasurable

/-- Pointwise bound of the chart coefficient difference by the sum of the two young-chart readings. -/
theorem coefOf_wardY_sub_le {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (q : Chart) :
    ‖(coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)) q‖ ≤
      wardYoungRead ν R
          (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y) q +
        wardYoungRead ν R
          (fun τ y => transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y) q := by
  have hsub : coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g) =
      coefOf R (fun τ y => wardY ν μ R c χy g τ y - wardY ν μ' R c χy g τ y) := by
    funext p
    unfold coefOf
    ext i
    fin_cases i <;> { simp; ring }
  rw [hsub]
  refine (wyl_coefOf_le (ν := ν) (fun p => add_nonneg (wyl_youngRead_nonneg ν R _ p)
      (wyl_youngRead_nonneg ν R _ p)) (fun p hp => ?_) (fun p hp hpy => ?_) q)
  · rw [(wyl_Y_zero_nhds (μ := μ) (c := c) hν hR hχy g hp _).self_of_nhds,
      (wyl_Y_zero_nhds (μ := μ') (c := c) hν hR hχy g hp _).self_of_nhds, sub_self]
  · have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
    have hres1 := wardYShiftedRes_proved ν μ R c g hν hR hc hμ hg
    have hres2 := wardYShiftedRes_proved ν μ' R c g hν hR hc hμ' hg
    have hϱ : 0 < ϱ (NearInst.chartY R p) := by
      rw [wyl_ϱ_chartY hR hp]
      exact div_pos hR (Real.sqrt_pos.mpr hp)
    rw [wyl_youngRead_of_young _ hpy, wyl_youngRead_of_young _ hpy,
      wardY_split hχ hν.le hres1 _ hϱ, wardY_split hχ hν.le hres2 _ hϱ]
    have heq : (wardYoungW ν μ R c χy g (NearInst.chartTau R p) (NearInst.chartY R p) +
          transField ν μ R c χy g (NearInst.chartTau R p) (NearInst.chartY R p)) -
        (wardYoungW ν μ' R c χy g (NearInst.chartTau R p) (NearInst.chartY R p) +
          transField ν μ' R c χy g (NearInst.chartTau R p) (NearInst.chartY R p)) =
        (wardYoungW ν μ R c χy g (NearInst.chartTau R p) (NearInst.chartY R p) -
          wardYoungW ν μ' R c χy g (NearInst.chartTau R p) (NearInst.chartY R p)) +
        (transField ν μ R c χy g (NearInst.chartTau R p) (NearInst.chartY R p) -
          transField ν μ' R c χy g (NearInst.chartTau R p) (NearInst.chartY R p)) := by abel
    rw [heq, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.2 (Real.sqrt_nonneg _))

end WardYContSub

/-- **`WardYLipschitz`** from the three leaves `SepWSubDom`, `WardYTransSubDom`, `WardYWSubChart`. -/
theorem wardYLipschitz_of (h1 : SepWSubDom) (h2 : SepWSubDom → WardYTransSubDom)
    (h3 : SepWSubDom → WardYWSubChart) : WardYLipschitz := by
  intro a b ν R c γ χy ha hb hχy hν hR hc
  obtain ⟨C1, hC10, hYW⟩ := h3 h1 ν R c χy hχy hν hR hc
  obtain ⟨C2, hC20, hTR⟩ := WardYContSub.transSub_chart_le (h2 h1) hχy hν hR hc
  set KA : ℝ := Real.sqrt (Real.pi * Real.exp (2 * |γ| / ν)) with hKA
  have hKA0 : 0 ≤ KA := Real.sqrt_nonneg _
  refine ⟨KA * (C1 + C2), fun μ hμ μ' hμ' g hg => ?_⟩
  have hμ0 : 0 ≤ μ := le_trans ha.le hμ.1
  have hμ'0 : 0 ≤ μ' := le_trans ha.le hμ'.1
  have hμ4 : -(1 / 4) < μ := by linarith
  have hμ'4 : -(1 / 4) < μ' := by linarith
  have hzero : ∀ q : Chart, 1 < ν * q.1 →
      (coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)) q = 0 := by
    intro q hq
    simp only [Pi.sub_apply,
      (wardYoungPointwise (μ := μ) (c := c) (fun _ _ => 0) hν hR hχy g q hq).1,
      (wardYoungPointwise (μ := μ') (c := c) (fun _ _ => 0) hν hR hχy g q hq).1, sub_self]
  have hm1 := WardYContSub.wardYWSub_aemeas (μ := μ) (μ' := μ') (R := R) hχy hg
  have hm2 := WardYContSub.wardYTransSub_aemeas hχy hν hR hc hμ4 hμ'4 hg
  have hadd := eLpNorm_add_le hm1 hm2 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmon : eLpNorm (coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)) 2
        (ageμ c (-3 / 2)) ≤
      eLpNorm (fun q => wardYoungRead ν R
          (fun τ y => wardYoungW ν μ R c χy g τ y - wardYoungW ν μ' R c χy g τ y) q +
        wardYoungRead ν R
          (fun τ y => transField ν μ R c χy g τ y - transField ν μ' R c χy g τ y) q)
        2 (ageμ c (-3 / 2)) :=
    eLpNorm_mono_real (WardYContSub.coefOf_wardY_sub_le hχy hν hR hc hμ4 hμ'4 hg)
  have hb1 := hYW μ μ' hμ0 hμ'0 g hg
  have hb2 := hTR μ μ' hμ0 hμ'0 g hg
  calc eLpNorm (coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)) 2
        (bodyMeasure c γ ν)
      ≤ ENNReal.ofReal KA *
          eLpNorm (coefOf R (wardY ν μ R c χy g) - coefOf R (wardY ν μ' R c χy g)) 2
            (ageμ c (-3 / 2)) :=
        wyl_eLpNorm_body_le c γ hν hzero
    _ ≤ ENNReal.ofReal KA *
          (ENNReal.ofReal (C1 * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) +
            ENNReal.ofReal (C2 * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2))) :=
        mul_le_mul' le_rfl (hmon.trans (hadd.trans (add_le_add hb1 hb2)))
    _ = ENNReal.ofReal (KA * (C1 + C2) * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hC10 (abs_nonneg _))
          (mul_nonneg hC20 (abs_nonneg _)), ← mul_assoc, ← ENNReal.ofReal_mul hKA0]
        congr 2
        ring

/-- **`SeqData.wardYCont` from the three leaves** (`PartIII-b:C/cont/WY`). -/
theorem wardYCont_of_leaves (h1 : SepWSubDom) (h2 : SepWSubDom → WardYTransSubDom)
    (h3 : SepWSubDom → WardYWSubChart) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.WardYCont :=
  wardYCont_of (wardYLipschitz_of h1 h2 h3) D hst

end UnforcedLeray.Short.PartIIIb.Concrete
