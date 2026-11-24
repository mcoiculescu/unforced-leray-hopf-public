import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanSupport

/-!
# `PartIII-b:C/rep/8/1/3` (`youngSupport`): young support of the comparison data

Source `the November 2 reference manuscript` lines 5395-5398 (the stream cutoff
`χ_y` vanishes for `s > 1/ν`) and 5296-5298 (every residual term contains a derivative of `X` or `Y`).

For `s > 1/ν` the chart receiver `y0 = chartY ε⁻¹ p` has `(ε ϱ y0)² = 1/s < ν` and `ϱ y0 > 0`.  The
open set `ysSet ε ν = {0 < ϱ} ∩ {(ε ϱ)² < ν}` contains `y0`.  On it:
* the stream-cut field `X₁ = wardX` vanishes identically (its stream cut and cut derivative vanish,
  since `ν · age ε⁻¹ y > 1` there), hence so does `Y₁ = physDmu X₁`;
* the mean fields `X^mt, Y^mt` vanish (`young_xmt_zero_open`, `ms_ymt_zero_of_open`).
Hence every first and second spatial derivative of these fields vanishes at `y0`, and so do
`cmpData` and `hessData`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The off-axis part of the young ball: `0 < ϱ` and `(ε ϱ)² < ν`. -/
def ysSet (ε ν : ℝ) : Set Space := {y | 0 < ϱ y} ∩ {y | (ε * ϱ y) ^ 2 < ν}

theorem ysSet_isOpen (ε ν : ℝ) : IsOpen (ysSet ε ν) := by
  unfold ysSet
  refine IsOpen.inter (isOpen_lt continuous_const continuous_ϱ) ?_
  exact isOpen_lt ((continuous_const.mul continuous_ϱ).pow 2) continuous_const

theorem ys_ϱ_eq_cylR (y : Space) : ϱ y = cylR (WithLp.ofLp y) := by
  simp [ϱ, cylR]

/-- On `ysSet`, `ν · age ε⁻¹ y > 1`. -/
theorem ysSet_age {ε ν : ℝ} (hε : 0 < ε) {y : Space} (hy : y ∈ ysSet ε ν) :
    1 < ν * age ε⁻¹ y := by
  simp only [ysSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hy
  obtain ⟨h0, hlt⟩ := hy
  unfold age
  have hne : ϱ y ≠ 0 := h0.ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hq : ν * ((ε⁻¹) ^ 2 / ϱ y ^ 2) = ν / (ε * ϱ y) ^ 2 := by
    rw [mul_pow]
    field_simp
  rw [hq, one_lt_div (pow_pos (mul_pos hε h0) 2)]
  exact hlt

/-- The stream-cut Ward field vanishes where `ν · age R y > 1`. -/
theorem ys_stream_zero {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) (hy : 1 < ν * age R y) :
    wardStreamCut ν R χy Z τ y = 0 := by
  have h0 : χy (ν * age R y) = 0 := hχ.zero _ hy.le
  have hev : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hχ.zero t (Set.mem_Ioi.1 ht).le
  have h1 : deriv χy (ν * age R y) = 0 := by
    rw [hev.deriv_eq]
    exact deriv_const _ 0
  unfold wardStreamCut
  rw [h0, h1]
  simp

/-- `D_μ` of a field vanishing on a neighbourhood of `y` vanishes at `y`. -/
theorem ys_physDmu_zero {ν μ : ℝ} {X : ℝ → Space → Space} {τ : ℝ} {y : Space}
    (hX : ∀ t, X t =ᶠ[𝓝 y] fun _ => (0 : Space)) : physDmu ν μ X τ y = 0 := by
  have hfun : (fun t => X t y) = fun _ => (0 : Space) :=
    funext fun t => (hX t).self_of_nhds
  unfold physDmu physLap
  rw [hfun]
  have hd : fderiv ℝ (X τ) y = 0 := ms_fderiv_eq_zero (hX τ)
  simp [hd, ms_physPd2_zero (hX τ), (hX τ).self_of_nhds]

/-- The mean fields vanish on `ysSet`. -/
theorem ys_mean_zero {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (M : Chart → Mat3) (hε : 0 < ε)
    (hχ : IsStreamCutoff χy) {y : Space} (hy : y ∈ ysSet ε ν) (τ : ℝ) :
    Xmean c ν ε μ χo χy M τ y = 0 ∧ Ymean c ν ε μ χo χy M τ y = 0 := by
  simp only [ysSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hy
  have hc : (ε * cylR (WithLp.ofLp y)) ^ 2 < ν := by
    rw [← ys_ϱ_eq_cylR]
    exact hy.2
  constructor
  · show WithLp.toLp 2 (Xmt c ν ε μ χo χy M (WithLp.ofLp y)) = 0
    rw [young_xmt_zero_open M hε hχ hc]
    simp
  · show WithLp.toLp 2 (YmtFun c ν ε μ χo χy M (WithLp.ofLp y)) = 0
    rw [ms_ymt_zero_of_open M hε hχ _ hc]
    simp

/-- **The young support of the comparison data at one regime** (source 5395-5398, 5296-5298). -/
theorem youngSupportAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) : YoungSupportAt Pl K L μ := by
  intro T p hp
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hs : 0 < p.1 := lt_trans (one_div_pos.2 hν) hp
  set y0 : Space := NearInst.chartY L.ε⁻¹ p with hy0
  have hdef : WithLp.ofLp y0 = ![L.ε⁻¹ / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] := by
    simp [hy0, NearInst.chartY]
  have hnn : 0 ≤ L.ε⁻¹ / Real.sqrt p.1 :=
    div_nonneg (inv_nonneg.2 hε.le) (Real.sqrt_nonneg _)
  have hc : cylR (WithLp.ofLp y0) = L.ε⁻¹ / Real.sqrt p.1 := by
    rw [hdef]
    unfold cylR
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (L.ε⁻¹ / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (L.ε⁻¹ / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq hnn
  have hpos : 0 < ϱ y0 := by
    rw [ys_ϱ_eq_cylR, hc]
    exact div_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hs)
  have hlt : (L.ε * ϱ y0) ^ 2 < L.ν := by
    rw [ys_ϱ_eq_cylR, hc]
    have h1 : L.ε * (L.ε⁻¹ / Real.sqrt p.1) = (Real.sqrt p.1)⁻¹ := by
      field_simp
    rw [h1, inv_pow, Real.sq_sqrt hs.le]
    exact inv_lt_of_inv_lt₀ hν (by simpa [one_div] using hp)
  have hmem : y0 ∈ ysSet L.ε L.ν := ⟨hpos, hlt⟩
  have hU : ysSet L.ε L.ν ∈ 𝓝 y0 := (ysSet_isOpen L.ε L.ν).mem_nhds hmem
  -- the stream-cut Ward field and its time derivatives vanish near `y0`
  have hXn : ∀ t, ∀ z ∈ ysSet L.ε L.ν, actX Pl K L μ T t z = 0 := by
    intro t z hz
    unfold actX wardX
    exact ys_stream_zero hχ _ t z (ysSet_age hε hz)
  have hXe : ∀ t, actX Pl K L μ T t =ᶠ[𝓝 y0] fun _ => (0 : Space) := by
    intro t
    exact Filter.eventually_of_mem hU (fun z hz => hXn t z hz)
  have hXz : ∀ t, ∀ z ∈ ysSet L.ε L.ν, actX Pl K L μ T t =ᶠ[𝓝 z] fun _ => (0 : Space) := by
    intro t z hz
    exact Filter.eventually_of_mem ((ysSet_isOpen L.ε L.ν).mem_nhds hz)
      (fun w hw => hXn t w hw)
  have hYe : ∀ t, actY Pl K L μ T t =ᶠ[𝓝 y0] fun _ => (0 : Space) := by
    intro t
    refine Filter.eventually_of_mem hU (fun z hz => ?_)
    show physDmu L.ν (μ + 1) (actX Pl K L μ T) t z = 0
    exact ys_physDmu_zero (fun s => hXz s z hz)
  have hMX : ∀ t, mnX Pl K L μ T t =ᶠ[𝓝 y0] fun _ => (0 : Space) := by
    intro t
    refine Filter.eventually_of_mem hU (fun z hz => ?_)
    exact (ys_mean_zero (thinRep T) hε hχ hz t).1
  have hMY : ∀ t, mnY Pl K L μ T t =ᶠ[𝓝 y0] fun _ => (0 : Space) := by
    intro t
    refine Filter.eventually_of_mem hU (fun z hz => ?_)
    exact (ys_mean_zero (thinRep T) hε hχ hz t).2
  set τ := NearInst.chartTau L.ε⁻¹ p with hτ
  constructor
  · unfold cmpData
    rw [ms_fderiv_eq_zero (hXe τ), ms_fderiv_eq_zero (hYe τ),
      ms_fderiv_eq_zero (hMX τ), ms_fderiv_eq_zero (hMY τ)]
    simp
  · unfold hessData hessSize
    simp [ms_physPd2_zero (hXe τ), ms_physPd2_zero (hMX τ)]

/-- **Young support of the comparison data** along the sequence (source 5395-5398, 5296-5298). -/
theorem youngSupport (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.YoungSupport := by
  unfold SeqData.YoungSupport
  exact Filter.Eventually.of_forall fun n z _ =>
    youngSupportAt_of D.Pl D.K (D.level n) (D.mu n z) hst.chiY

end UnforcedLeray.Short.PartIIIb.Concrete
