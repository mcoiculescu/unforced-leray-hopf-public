import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# `PartIII-b:C/rep/8/1/1/1/5` (`GeomX.Measurable`): measurability of the `X` comparison along the phase

Source `shorter-proof-2026-11-02.tex` lines 4171-4186 (`X = 𝒞_y X₀`), 5415-5427.

At a chart point `(s,(q,η))` the receiver `chartY R (s,(q,η))` does not depend on `q` and the phase
`chartTau R (s,(q,η)) = 2q/R + log s` is affine in `q`; `mnX` does not depend on the phase.  So
`q ↦ xcmp (τ(q)) y₀` is a measurable function of `τ` composed with an affine map, where
`τ ↦ ‖D_y actX τ (y₀) - A‖`.

* `s > 0`: `y₀` is off the axis; `actX` is jointly measurable (`t84_ward_stream`) and differentiable
  in `y` off the axis (`WardXRegularAt`), so `measurable_fderiv_apply_offaxis` applies.
* `s ≤ 0`: `y₀ = 0` is on the axis.  Near the axis `χ_y(ν R²/ϱ²) = 0` (since `ν R²/ϱ² > 1`) so
  `actX τ` vanishes at every off-axis point near `0`; hence `D_y actX τ (0) = 0` for every `τ`
  (differentiable or not), the integrand is constant in the phase.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace XMeas

/-- A map vanishing at the off-axis points near `0` has zero derivative at `0`. -/
theorem fderiv_zero_of_off_axis_zero {f : Space → Space} {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ y, 0 < ϱ y → ϱ y < δ → f y = 0) : fderiv ℝ f 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ f 0
  swap
  · exact fderiv_zero_of_not_differentiableAt hd
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- the small multiples of an off-axis vector are off-axis and in the ball
  have hev : ∀ u : Space, 0 < ϱ u → ∀ᶠ n : ℕ in atTop, f (((n : ℝ) + 1)⁻¹ • u) = 0 := by
    intro u hu
    obtain ⟨N, hN⟩ := exists_nat_gt (ϱ u / δ)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply hf
    · rw [ϱ_smul, abs_of_pos (by positivity)]
      positivity
    · rw [ϱ_smul, abs_of_pos (by positivity)]
      have hn' : ϱ u / δ < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_lt_iff₀ hδ] at hn'
      rw [inv_mul_lt_iff₀ (by positivity)]
      linarith
  have e0 : (coordinateVector 0 : Space) = EuclideanSpace.single 0 1 := rfl
  have hϱe : 0 < ϱ (coordinateVector 0 : Space) := by
    have h1 : ϱ (coordinateVector 0 : Space) = 1 := by
      simp [ϱ, coordinateVector]
    rw [h1]; norm_num
  have hf0 : f 0 = 0 := by
    have h1 : Tendsto (fun n : ℕ => f (((n : ℝ) + 1)⁻¹ • (coordinateVector 0 : Space))) atTop
        (𝓝 (f 0)) := by
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (coordinateVector 0 : Space)) atTop
          (𝓝 0) := by
        simpa using hseq.smul_const (coordinateVector 0 : Space)
      exact hd.continuousAt.tendsto.comp h2
    have h3 : Tendsto (fun n : ℕ => f (((n : ℝ) + 1)⁻¹ • (coordinateVector 0 : Space))) atTop
        (𝓝 0) :=
      tendsto_const_nhds.congr' ((hev _ hϱe).mono fun n hn => hn.symm)
    exact tendsto_nhds_unique h1 h3
  have hc : Tendsto (fun n : ℕ => ‖(n : ℝ) + 1‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  have hL : ∀ u : Space, 0 < ϱ u → fderiv ℝ f 0 u = 0 := by
    intro u hu
    have h1 := hd.hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) u hc
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) • (f (0 + (((n : ℝ) + 1))⁻¹ • u) - f 0))
        atTop (𝓝 0) :=
      tendsto_const_nhds.congr' ((hev u hu).mono fun n hn => by simp [hn, hf0])
    exact tendsto_nhds_unique h1 h3
  ext1 v
  have hk : (0 : ℝ) < ‖v‖ + 1 := by positivity
  set w : Space := (‖v‖ + 1) • coordinateVector 0 with hw
  have hw0 : w 0 = ‖v‖ + 1 := by simp [hw, coordinateVector]
  have hv0 : |v 0| ≤ ‖v‖ := by
    have := PiLp.norm_apply_le v 0
    simpa using this
  have hpos : ∀ y : Space, 0 < y 0 → 0 < ϱ y := by
    intro y hy
    apply ϱ_pos
    intro h
    exact hy.ne' h.1
  have hwp : 0 < ϱ w := hpos w (by rw [hw0]; exact hk)
  have hvw : 0 < ϱ (v + w) := by
    apply hpos
    have : (v + w) 0 = v 0 + w 0 := rfl
    rw [this, hw0]
    have := neg_abs_le (v 0)
    linarith
  have : v = (v + w) - w := by abel
  rw [this, map_sub, hL _ hvw, hL _ hwp]
  simp

/-- `wardStreamCut` vanishes at off-axis points very near the axis (`ν R²/ϱ² > 1`). -/
theorem wardStreamCut_eq_zero_near_axis (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) {χy : ℝ → ℝ}
    (hχy : IsYoungCutoff χy) (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (hlt : ϱ y < R * Real.sqrt ν) : wardStreamCut ν R χy Z τ y = 0 := by
  have hsq : ϱ y ^ 2 < R ^ 2 * ν := by
    have h1 : ϱ y ^ 2 < (R * Real.sqrt ν) ^ 2 := by
      apply pow_lt_pow_left₀ hlt hy.le (by norm_num)
    rwa [mul_pow, Real.sq_sqrt hν.le] at h1
  have h1 : 1 < ν * age R y := by
    unfold age
    rw [← mul_div_assoc, lt_div_iff₀ (by positivity)]
    nlinarith
  have hz : χy (ν * age R y) = 0 := hχy.zero _ h1.le
  have hd : deriv χy (ν * age R y) = 0 := by
    have : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds h1] with t ht
      exact hχy.zero t ht.le
    rw [this.deriv_eq, deriv_const]
  unfold wardStreamCut
  rw [hz, hd]
  simp

theorem wardStreamCut_fderiv_zero (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) {χy : ℝ → ℝ}
    (hχy : IsYoungCutoff χy) (Z : ℝ → Space → Space) (τ : ℝ) :
    fderiv ℝ (wardStreamCut ν R χy Z τ) 0 = 0 :=
  fderiv_zero_of_off_axis_zero (δ := R * Real.sqrt ν) (by positivity)
    (fun y hy hlt => wardStreamCut_eq_zero_near_axis ν R hν hR hχy Z τ hy hlt)

/-- A family of continuous linear maps of `Space` is measurable when its values on vectors are. -/
theorem measurable_clm_of_apply {α : Type*} [MeasurableSpace α] {Φ : α → Space →L[ℝ] Space}
    (h : ∀ v, Measurable fun a => Φ a v) : Measurable Φ := by
  have e : ∀ L : Space →L[ℝ] Space, L = ∑ j : Fin 3,
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (L (coordinateVector j)) := by
    intro L
    ext1 v
    have hv : v = ∑ j : Fin 3, v j • (coordinateVector j : Space) := by
      have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
      simpa [coordinateVector] using this.symm
    conv_lhs => rw [hv]
    simp [map_sum, ContinuousLinearMap.sum_apply]
  have : Φ = fun a => ∑ j : Fin 3,
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (Φ a (coordinateVector j)) :=
    funext fun a => e (Φ a)
  rw [this]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (ContinuousLinearMap.smulRightL ℝ Space Space
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).continuous.measurable.comp (h _)

/-- Off the axis, the derivative of the Ward field at a fixed point is measurable in the phase. -/
theorem wardX_fderiv_apply_measurable {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {g : Chart → Ten3} (hg : Measurable g) (hreg : WardXRegularAt ν μ R c χy g) {y₀ : Space}
    (hy₀ : y₀ ∉ axis) (v : Space) :
    Measurable fun τ : ℝ => fderiv ℝ (wardX ν μ R c χy g τ) y₀ v := by
  obtain ⟨X, hXC, hXeq, -, -, -⟩ := hreg
  have hF : Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 :=
    T8_4.t84_ward_stream hχy hg
  have hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y := by
    intro τ y hy
    have hev : wardX ν μ R c χy g τ =ᶠ[𝓝 y] X τ := by
      filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
      exact (hXeq τ z hz).symm
    exact ((hXC τ).differentiable (by norm_num) y).congr_of_eventuallyEq hev
  have hm := measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g)
    (V := fun _ _ => v) hF measurable_const hd
  have hcomp := hm.comp (measurable_id.prodMk (measurable_const (a := y₀)))
  convert hcomp using 1
  funext τ
  simp [hy₀]

/-- The Ward regularity of the thin source `thinG` of any `T`, at a regime with the standing
hypotheses (source 4161-4186). -/
theorem thinG_wardXRegularAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχy : IsYoungCutoff K.χy) (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) (hμ : -(1 / 4) < μ)
    (T : LStr Pl K L) :
    WardXRegularAt L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (thinG Pl K L T) := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hρb : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have hν' : 0 < (L.params Pl).ν := L.ν_pos
    have hε' : 0 < (L.params Pl).ε := L.ε_pos
    exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos hν' _))) (Real.exp_pos _))
      (Real.rpow_pos_of_pos hε' _)
  have hreg : WardXRegular (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy :=
    wardXRegular_of (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo K.χy
      (Final.wardX0Smooth_of _ _ _ _ _ _ _ K.hχo) (Final.wardX0Structure_of _ _ _ _ _ _ _ K.hχo)
      (outPrimStream_of _ _ _ _ _ _ _ K.hχo) (wardStreamCutDivFree_of L.ν L.ε⁻¹ K.χy)
  exact hreg hχy (cOf_pos hν) hρb hmZ hν hε hμ (thinPart T) _ _ EventuallyEq.rfl EventuallyEq.rfl

theorem thinG_measurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    Measurable (thinG Pl K L T) := by
  unfold thinG
  exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable

/-- The phase-dependence of the comparison at a fixed receiver is measurable. -/
theorem xcmp_measurable_phase (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχy : IsYoungCutoff K.χy) (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) (hμ : -(1 / 4) < μ)
    (T : LStr Pl K L) {y₀ : Space} (hy₀ : y₀ ∉ axis) :
    Measurable fun τ : ℝ => xcmp Pl K L μ T τ y₀ := by
  have hreg := thinG_wardXRegularAt Pl K L μ hχy hmZ hC0 hμ T
  have hg := thinG_measurable Pl K L T
  have hΨ : Measurable fun τ : ℝ => (fderiv ℝ (actX Pl K L μ T τ) y₀ -
      fderiv ℝ (mnX Pl K L μ T 0) y₀ : Space →L[ℝ] Space) := by
    apply measurable_clm_of_apply
    intro v
    simp only [ContinuousLinearMap.sub_apply]
    exact (wardX_fderiv_apply_measurable hχy hg hreg hy₀ v).sub measurable_const
  exact hΨ.norm

end XMeas

open XMeas in
theorem xcmp_aemeasurable_cell (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ z ∈ Set.Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
      ∀ s η : ℝ, AEMeasurable (fun q : ℝ => xcmp D.Pl D.K (D.level n) (D.mu n z) T
        (NearInst.chartTau (D.level n).ε⁻¹ (s, (q, η)))
        (NearInst.chartY (D.level n).ε⁻¹ (s, (q, η))))
        (MeasureTheory.volume.restrict
          (Set.Ico (-cOf (D.level n).ν / 2) (cOf (D.level n).ν / 2))) := by
  filter_upwards [muWin_gt_quarter D hst] with n hn
  intro z hz T s η
  have hμ := hn z hz
  have hχy : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  have hmZ : 0 ≤ D.K.mZ := by have := hst.mZ_gt; linarith
  have hC0 := hst.C0_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hτ : Measurable fun q : ℝ => NearInst.chartTau (D.level n).ε⁻¹ (s, (q, η)) := by
    unfold NearInst.chartTau
    fun_prop
  by_cases hs : 0 < s
  · have hy₀ : NearInst.chartY (D.level n).ε⁻¹ (s, (0, η)) ∉ axis := by
      intro h
      have h1 := h.1
      have : (D.level n).ε⁻¹ / Real.sqrt s ≠ 0 := by positivity
      exact this (by simpa [NearInst.chartY] using h1)
    have hm := xcmp_measurable_phase D.Pl D.K (D.level n) (D.mu n z) hχy hmZ hC0 hμ T hy₀
    exact (hm.comp hτ).aemeasurable
  · have hs' : s ≤ 0 := not_lt.1 hs
    have hy : ∀ q : ℝ, NearInst.chartY (D.level n).ε⁻¹ (s, (q, η)) = 0 := by
      intro q
      ext i
      fin_cases i <;> simp [NearInst.chartY, Real.sqrt_eq_zero_of_nonpos hs']
    have hmn : ∀ τ, mnX D.Pl D.K (D.level n) (D.mu n z) T τ =
        mnX D.Pl D.K (D.level n) (D.mu n z) T 0 := fun τ => rfl
    have h0 : ∀ τ, fderiv ℝ (actX D.Pl D.K (D.level n) (D.mu n z) T τ) 0 = 0 := fun τ =>
      wardStreamCut_fderiv_zero (D.level n).ν (D.level n).ε⁻¹ hν (inv_pos.2 hε) hχy _ τ
    have hfun : (fun q : ℝ => xcmp D.Pl D.K (D.level n) (D.mu n z) T
        (NearInst.chartTau (D.level n).ε⁻¹ (s, (q, η)))
        (NearInst.chartY (D.level n).ε⁻¹ (s, (q, η)))) = fun _ =>
        ‖(0 : Space →L[ℝ] Space) - fderiv ℝ (mnX D.Pl D.K (D.level n) (D.mu n z) T 0) 0‖ := by
      funext q
      rw [hy q]
      unfold xcmp
      rw [h0, hmn]
    rw [hfun]
    exact measurable_const.aemeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
