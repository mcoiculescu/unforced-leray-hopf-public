import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.ZRegular.Jensen
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs

/-!
# Regularity and decay of `wardX0` from a separated source (helper for `GeomX.ZRegular`)

Source `shorter-proof-2026-11-02.tex` 4171-4186, 3604-3621, 5400-5406.  A chart tensor `G` with
finite `ageμ c (-1/2)`-moment of `|G|²` that vanishes a.e. where `νs ≤ 6/5` gives an old source
`oldPhys ε⁻¹ c G` that is a.e. a separated source supported in `ϱ ≤ ε⁻¹√(5ν/6)`; then
`wardX0` is `C²` on `ϱ > ε⁻¹√(5ν/6)` and `O(ϱ⁻³)` there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace ZRegAux

/-- The separated source of a chart tensor (copy of `oldSourceReg_of` for a general `G`). -/
theorem sepSrc_of_chart (c ν ε : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (G : Chart → Ten3)
    (hGm : Measurable G) (hmom : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤)
    (hz : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → G p = 0) :
    ∃ (P : ℝ) (T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < P ∧
      UnforcedLeray.Short.IIIa.IsSepSource P (ε⁻¹ * Real.sqrt (5 * ν / 6)) T' ∧ SepMoment P T' ∧
      ∀ (μ : ℂ) (y : Space) (τ : ℝ),
        UnforcedLeray.Short.IIIa.sepW ν μ (oldPhys ε⁻¹ c G) y τ =
          UnforcedLeray.Short.IIIa.sepW ν μ T' y τ := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hpull := chartOfNullPullback ε⁻¹ c hR hc _ (ae_iff.1 hz)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c G x.1 x.2 =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [not_not] at hx
    unfold oldCutSrc
    split_ifs with hz'
    · rfl
    · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz'
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (ε⁻¹ ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, osr_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  have hper : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G (τ + 2 * c / ε⁻¹) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic ε⁻¹ c G τ z]
  have hsupp : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  exact ⟨2 * c / ε⁻¹, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G, by positivity,
    ⟨oldCutMeasurable ε⁻¹ c _ G hGm, hper, hsupp⟩,
    oldCutMoment ε⁻¹ c _ G hR hc hGm hmom, (fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ)⟩

theorem outRay_ϱ {y : Space} (hy : 0 < ϱ y) {t : ℝ} (ht : 0 ≤ t) : ϱ (outRay y t) = t := by
  unfold outRay ϱ at *
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h : (t * (y 0 / √(y 0 ^ 2 + y 1 ^ 2))) ^ 2 + (t * (y 1 / √(y 0 ^ 2 + y 1 ^ 2))) ^ 2 =
      t ^ 2 := by
    have h2 : (√(y 0 ^ 2 + y 1 ^ 2)) ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
    field_simp
    rw [h2]
  rw [h]
  exact Real.sqrt_sq ht

theorem wardX0_eq_T' {ν μ R c : ℝ} {g : Chart → Ten3} {T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hEq : ∀ (μ : ℂ) (y : Space) (τ : ℝ),
      UnforcedLeray.Short.IIIa.sepW ν μ (oldPhys R c g) y τ =
        UnforcedLeray.Short.IIIa.sepW ν μ T' y τ) (τ : ℝ) (y : Space) :
    wardX0 ν μ R c g τ y = WithLp.toLp 2 fun i =>
      (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' y τ i -
        UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i).re := by
  unfold wardX0
  simp only [hEq]

theorem wardX0_cd {ν μ R c : ℝ} {g : Chart → Ten3} {P r0 : ℝ}
    {T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ r0)
    (hP : 0 < P) (hS : UnforcedLeray.Short.IIIa.IsSepSource P r0 T') (hM : SepMoment P T')
    (hEq : ∀ (μ : ℂ) (y : Space) (τ : ℝ),
      UnforcedLeray.Short.IIIa.sepW ν μ (oldPhys R c g) y τ =
        UnforcedLeray.Short.IIIa.sepW ν μ T' y τ) (τ : ℝ) :
    ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) {y : Space | r0 < ϱ y} := by
  have hW := sepWSmoothOn_of UnforcedLeray.Short.IIIa.sepKernelBounds
  have hA := hW ν (μ : ℂ) r0 P T' hν (by simpa using hμ) hr0 hP hS hM τ
  have hB := hW ν ((μ : ℂ) + 1) r0 P T' hν (by simp; linarith) hr0 hP hS hM τ
  refine contDiffOn_piLp' 2 fun i => ?_
  have hd : ContDiffOn ℝ 2 (fun y => UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' y τ i -
      UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i) {y : Space | r0 < ϱ y} :=
    (hA i).sub (hB i)
  have := Complex.reCLM.contDiff.comp_contDiffOn hd
  refine this.congr fun y _ => ?_
  rw [wardX0_eq_T' hEq]
  rfl

theorem wardX0_tendsto {ν μ R c : ℝ} {g : Chart → Ten3} {P r0 : ℝ}
    {T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ r0)
    (hP : 0 < P) (hS : UnforcedLeray.Short.IIIa.IsSepSource P r0 T') (hM : SepMoment P T')
    (hEq : ∀ (μ : ℂ) (y : Space) (τ : ℝ),
      UnforcedLeray.Short.IIIa.sepW ν μ (oldPhys R c g) y τ =
        UnforcedLeray.Short.IIIa.sepW ν μ T' y τ) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    Tendsto (fun t : ℝ => wardX0 ν μ R c g τ (outRay y t)) atTop (𝓝 0) := by
  obtain ⟨C1, h1⟩ := sepFarDecay ν (μ : ℂ) r0 P T' hν (by simpa using hμ) hr0 hP hS hM τ
  obtain ⟨C2, h2⟩ := sepFarDecay ν ((μ : ℂ) + 1) r0 P T' hν (by simp; linarith) hr0 hP hS hM τ
  have hz : Tendsto (fun t : ℝ => (C1 + C2) * t ^ (-3 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).const_mul (C1 + C2)
  have hcomp : Tendsto (fun t : ℝ => fun i : Fin 3 =>
      (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' (outRay y t) τ i -
        UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' (outRay y t) τ i).re) atTop
      (𝓝 (fun _ => 0)) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop (max (2 * r0) 1)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
    have hϱ : ϱ (outRay y t) = t := outRay_ϱ hy ht0.le
    have hb1 := (h1 i (outRay y t) (by rw [hϱ]; exact (le_max_left _ _).trans ht)).1
    have hb2 := (h2 i (outRay y t) (by rw [hϱ]; exact (le_max_left _ _).trans ht)).1
    rw [hϱ] at hb1 hb2
    calc ‖(UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' (outRay y t) τ i -
          UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' (outRay y t) τ i).re‖
        ≤ ‖UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' (outRay y t) τ i -
          UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' (outRay y t) τ i‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ _ := norm_sub_le _ _
      _ ≤ C1 * t ^ (-3 : ℝ) + C2 * t ^ (-3 : ℝ) := add_le_add hb1 hb2
      _ = (C1 + C2) * t ^ (-3 : ℝ) := by ring
  have := ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).tendsto (fun _ => 0)).comp hcomp
  have e : ∀ t, wardX0 ν μ R c g τ (outRay y t) = WithLp.toLp 2 fun i =>
      (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T' (outRay y t) τ i -
        UnforcedLeray.Short.IIIa.sepW ν ((μ : ℂ) + 1) T' (outRay y t) τ i).re :=
    fun t => wardX0_eq_T' hEq τ _
  simp only [e]
  have e0 : (0 : Space) = WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℝ)) := rfl
  rw [e0]
  exact this

end ZRegAux

end UnforcedLeray.Short.PartIIIb.Concrete
