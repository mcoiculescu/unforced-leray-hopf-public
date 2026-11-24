import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAConvBound.Alg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAConvBound.DhBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Eq

/-!
# `RAConvBound` helper: chart gradient identification and pointwise bound of `convCoef`
(source 5036-5039, 5045-5050)

Identifies the radial and axial chart derivatives in `rac_Dh_le` for `α = hAcoef ν ε χf A` with the
entries `(0,0), (0,2), (1,1), (2,0), (2,2)` of `gradAcoef ν ε χf A`, and deduces the pointwise
bound `‖convCoef p μ χf U A (s, x)‖ ≤ 24 δU (‖hAcoef (s, x)‖ + √s ‖gradAcoef (s, x)‖)` for `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Slice function `(s', y) ↦ α (s', y) i` of a chart profile. -/
def racComp (α : Chart → Merid) (i : Fin 2) : ℝ → ℝ × ℝ → ℝ :=
  fun s' y => α (s', y) i

theorem rac_chartComp_hhatA_0 (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    chartComp (hhatA ν ε χf A) 0 = fun s' y => Real.sqrt s' * racComp (hAcoef ν ε χf A) 0 s' y := by
  funext s' y
  by_cases hs : 0 < s'
  · have hsq : Real.sqrt s' ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    simp only [chartComp, racComp, hAcoef, merOf, Pi.smul_apply, smul_eq_mul,
      PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [← mul_assoc, mul_inv_cancel₀ hsq, one_mul]
  · have hs' : s' ≤ 0 := not_lt.1 hs
    simp [chartComp, hhatA_of_nonpos hs', Real.sqrt_eq_zero_of_nonpos hs']

theorem rac_chartComp_hhatA_2 (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    chartComp (hhatA ν ε χf A) 2 = fun s' y => Real.sqrt s' * racComp (hAcoef ν ε χf A) 1 s' y := by
  funext s' y
  by_cases hs : 0 < s'
  · have hsq : Real.sqrt s' ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    simp only [chartComp, racComp, hAcoef, merOf, Pi.smul_apply, smul_eq_mul,
      PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← mul_assoc, mul_inv_cancel₀ hsq, one_mul]
  · have hs' : s' ≤ 0 := not_lt.1 hs
    simp [chartComp, hhatA_of_nonpos hs', Real.sqrt_eq_zero_of_nonpos hs']

theorem rac_diff_x {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    DifferentiableAt ℝ (racComp α i s) x :=
  (crg_hasFDeriv_slice hα i).differentiableAt

theorem rac_diff_s {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    DifferentiableAt ℝ (fun s' => racComp α i s' x) s := by
  have h1 : HasDerivAt (fun s' : ℝ => ((s', x) : Chart)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h2 := hα.hasFDerivAt.comp_hasDerivAt s h1
  have h3 := (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s h2
  exact h3.differentiableAt

theorem rac_dQ_eq {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    dQ (racComp α i) s x = Axi.dQ α (s, x) i := by
  unfold dQ racComp
  rw [crg_slice_apply hα i (ei 0)]
  simp [ei]

theorem rac_dEta_eq {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    dEta (racComp α i) s x = Axi.dEta α (s, x) i := by
  unfold dEta racComp
  rw [crg_slice_apply hα i (ei 1)]
  simp [ei]

theorem rac_Kop_eq {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    Kop (racComp α i) s x = (UnforcedLeray.Short.IIb.kAge α (s, x)) i := by
  unfold Kop racComp UnforcedLeray.Short.IIb.kAge
  rw [crg_slice_apply hα i (ei 1), crg_deriv_s hα i]
  simp [ei]
  ring

/-- The five non-zero entries of `gradAcoef` match the radial/axial chart derivatives of `hAcoef`. -/
theorem rac_gradAcoef_entries {ν ε s : ℝ} {χf : ℝ → ℝ} {A : ℝ → Mat3} {x : ℝ × ℝ}
    (hs : 0 < s) (hα : DifferentiableAt ℝ (hAcoef ν ε χf A) (s, x)) :
    (UnforcedLeray.Short.IIb.qEps ε (hAcoef ν ε χf A) (s, x)) 0 =
        (gradAcoef ν ε χf A (s, x)) (0, 0) ∧
      Axi.dEta (hAcoef ν ε χf A) (s, x) 0 = (gradAcoef ν ε χf A (s, x)) (0, 2) ∧
      (UnforcedLeray.Short.IIb.qEps ε (hAcoef ν ε χf A) (s, x)) 1 =
        (gradAcoef ν ε χf A (s, x)) (2, 0) ∧
      Axi.dEta (hAcoef ν ε χf A) (s, x) 1 = (gradAcoef ν ε χf A (s, x)) (2, 2) ∧
      ε * hAcoef ν ε χf A (s, x) 0 = (gradAcoef ν ε χf A (s, x)) (1, 1) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hx0 := rac_diff_x hα 0
  have hs0' := rac_diff_s hα 0
  have hx1 := rac_diff_x hα 1
  have hs1' := rac_diff_s hα 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (UnforcedLeray.Short.IIb.qEps ε (hAcoef ν ε χf A) (s, x)) 0 =
      s⁻¹ * physDr ε (chartComp (hhatA ν ε χf A) 0) s x
    rw [rac_chartComp_hhatA_0, ge_physDr ε _ s x hs hx0 hs0', ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul, rac_dQ_eq hα 0, rac_Kop_eq hα 0]
    rfl
  · show Axi.dEta (hAcoef ν ε χf A) (s, x) 0 =
      s⁻¹ * physDz (chartComp (hhatA ν ε χf A) 0) s x
    rw [rac_chartComp_hhatA_0, ge_physDz _ s x hs hx0, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul, rac_dEta_eq hα 0]
  · show (UnforcedLeray.Short.IIb.qEps ε (hAcoef ν ε χf A) (s, x)) 1 =
      s⁻¹ * physDr ε (chartComp (hhatA ν ε χf A) 2) s x
    rw [rac_chartComp_hhatA_2, ge_physDr ε _ s x hs hx1 hs1', ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul, rac_dQ_eq hα 1, rac_Kop_eq hα 1]
    rfl
  · show Axi.dEta (hAcoef ν ε χf A) (s, x) 1 =
      s⁻¹ * physDz (chartComp (hhatA ν ε χf A) 2) s x
    rw [rac_chartComp_hhatA_2, ge_physDz _ s x hs hx1, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul, rac_dEta_eq hα 1]
  · show ε * hAcoef ν ε χf A (s, x) 0 =
      s⁻¹ * (ε * Real.sqrt s * chartComp (hhatA ν ε χf A) 0 s x)
    rw [rac_chartComp_hhatA_0]
    simp only [racComp]
    have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have : ε * Real.sqrt s * (Real.sqrt s * hAcoef ν ε χf A (s, x) 0) =
        s * (ε * hAcoef ν ε χf A (s, x) 0) := by
      linear_combination (ε * hAcoef ν ε χf A (s, x) 0) * hss
    rw [this, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

/-- Bound on the spatial derivative of the ring lift of `hAcoef` at the chart point `(s, x)`. -/
theorem rac_fderiv_Nv_hAcoef_le {ν ε s : ℝ} {χf : ℝ → ℝ} {A : ℝ → Mat3} {x : ℝ × ℝ}
    (hε : 0 < ε) (hs : 0 < s) (hα : DifferentiableAt ℝ (hAcoef ν ε χf A) (s, x)) :
    ‖fderiv ℝ (Axi.Nv ε⁻¹ (hAcoef ν ε χf A) (NearInst.chartTau ε⁻¹ (s, x)))
        (NearInst.chartY ε⁻¹ (s, x))‖ ≤
      6 * s * ‖gradAcoef ν ε χf A (s, x)‖ := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hy := crg_chartY_not_mem_axis hR (p := (s, x)) hs
  have hrt := fe_chart_roundtrip hR (s, x) hs
  obtain ⟨_, _, hϱ, _⟩ := fe_chartY_facts hR (s, x) hs
  have hα' : DifferentiableAt ℝ (hAcoef ν ε χf A)
      (Axi.chart ε⁻¹ (NearInst.chartTau ε⁻¹ (s, x)) (NearInst.chartY ε⁻¹ (s, x))) := by
    rw [hrt]; exact hα
  have hD := rac_Dh_le hR hy hα'
  rw [hrt, inv_inv, hϱ] at hD
  obtain ⟨e00, e02, e20, e22, e11⟩ := rac_gradAcoef_entries hs hα
  have hhoop : 2 * (ε⁻¹ / √(s, x).1)⁻¹ * √(s, x).1 * |hAcoef ν ε χf A (s, x) 0| =
      2 * s * |(gradAcoef ν ε χf A (s, x)) (1, 1)| := by
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have h1 : (ε⁻¹ / Real.sqrt s)⁻¹ * Real.sqrt s = s * ε := by
      rw [inv_div, div_eq_mul_inv, inv_inv]
      linear_combination ε * hsq
    calc 2 * (ε⁻¹ / √(s, x).1)⁻¹ * √(s, x).1 * |hAcoef ν ε χf A (s, x) 0|
        = 2 * ((ε⁻¹ / Real.sqrt s)⁻¹ * Real.sqrt s) * |hAcoef ν ε χf A (s, x) 0| := by ring
      _ = 2 * s * (ε * |hAcoef ν ε χf A (s, x) 0|) := by rw [h1]; ring
      _ = 2 * s * |ε * hAcoef ν ε χf A (s, x) 0| := by
        rw [abs_mul, abs_of_pos hε]
      _ = 2 * s * |(gradAcoef ν ε χf A (s, x)) (1, 1)| := by rw [e11]
  have b : ∀ p : Fin 3 × Fin 3, |(gradAcoef ν ε χf A (s, x)) p| ≤ ‖gradAcoef ν ε χf A (s, x)‖ := by
    intro p
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (gradAcoef ν ε χf A (s, x)) p
  have b00 := b (0, 0)
  have b02 := b (0, 2)
  have b20 := b (2, 0)
  have b22 := b (2, 2)
  have b11 := b (1, 1)
  rw [hhoop, e00, e02, e20, e22] at hD
  have hs' : (s, x).1 = s := rfl
  rw [hs'] at hD
  calc _ ≤ 2 * s * |(gradAcoef ν ε χf A (s, x)) (1, 1)| +
        s * (|(gradAcoef ν ε χf A (s, x)) (0, 0)| + |(gradAcoef ν ε χf A (s, x)) (0, 2)| +
          |(gradAcoef ν ε χf A (s, x)) (2, 0)| + |(gradAcoef ν ε χf A (s, x)) (2, 2)|) := hD
    _ ≤ 6 * s * ‖gradAcoef ν ε χf A (s, x)‖ := by nlinarith

theorem rac_norm_mer_le (v : Space) : ‖(!₂[v 0, v 2] : Merid)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  linarith [sq_nonneg (v 1)]

/-- Pointwise bound on `convCoef` at `(s, x)` with `s > 0`. -/
theorem rac_convCoef_norm_le {as : ℝ} {χf : ℝ → ℝ} (hχ : IsSourceCutoffC χf)
    {dm dp d : ℝ} (hdm : 0 < dm) {p : Params} (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    {μ δU : ℝ} {U : ℝ → SpatialField} {pr : ℝ → Space → ℝ}
    (hU : IsExactProfile p.ν p.period U pr)
    (hδU : ∀ (τ : ℝ) (y : Space), ‖U τ y - p.raw τ y‖ ≤ δU ∧
      ‖fderiv ℝ (fun y' => U τ y' - p.raw τ y') y‖ ≤ δU)
    {A : ℝ → Mat3} (hA : IsAffElem as A) {s : ℝ} (hs : 0 < s) (x : ℝ × ℝ) :
    ‖convCoef p μ χf U A (s, x)‖ ≤
      24 * δU * (‖hAcoef p.ν p.ε χf A (s, x)‖ + Real.sqrt s * ‖gradAcoef p.ν p.ε χf A (s, x)‖) := by
  have hR : 0 < p.ε⁻¹ := inv_pos.2 p.ε_pos
  have hRne : p.ε⁻¹ ≠ 0 := hR.ne'
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hδ0 : 0 ≤ δU := (norm_nonneg _).trans (hδU 0 0).1
  set τ := NearInst.chartTau p.ε⁻¹ (s, x)
  set y := NearInst.chartY p.ε⁻¹ (s, x)
  have hy : y ∉ Axi.axis := crg_chartY_not_mem_axis hR hs
  have hrt : Axi.chart p.ε⁻¹ τ y = (s, x) := fe_chart_roundtrip hR (s, x) hs
  obtain ⟨hy0, _, _, hage⟩ := fe_chartY_facts hR (s, x) hs
  have hy0_ne : y 0 ≠ 0 := by
    rw [hy0]
    exact div_ne_zero hRne (Real.sqrt_ne_zero'.2 hs)
  -- hLift agrees with Nv of hAcoef near y
  have hc0 : Continuous (fun z : Space => z 0) := by fun_prop
  have hev : ∀ᶠ z in nhds y, z 0 ≠ 0 := hc0.continuousAt.eventually_ne hy0_ne
  have hb : hLift p.ν p.ε p.c χf A τ =ᶠ[nhds y] Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ := by
    filter_upwards [hev] with z hz
    have hzA : z ∉ Axi.axis := fun h => hz h.1
    have hpos : 0 < Axi.age p.ε⁻¹ z := Axi.age_pos hRne hzA
    have hper : Axi.perExt (cOf p.ν) (hAcoef p.ν p.ε χf A) (Axi.chart p.ε⁻¹ τ z) =
        hAcoef p.ν p.ε χf A (Axi.chart p.ε⁻¹ τ z) :=
      convPerExtHat as χf hχ p.ν p.ε p.ν_pos p.ε_pos A hA _ hpos _
    simp only [hLift, Axi.Nv, hc]
    rw [hper]
  -- differentiability of U τ, p.raw τ, and Nv hAcoef τ at y
  have hDH : DifferentiableAt ℝ (hAcoef p.ν p.ε χf A) (s, x) :=
    convDiffHat as χf hχ p.ν p.ε p.ν_pos p.ε_pos A hA s hs x
  have hDH' : DifferentiableAt ℝ (hAcoef p.ν p.ε χf A) (Axi.chart p.ε⁻¹ τ y) := by
    rw [hrt]; exact hDH
  have hh : DifferentiableAt ℝ (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y :=
    (UnforcedLeray.Short.IIb.chartAdv_diffAt p.ε⁻¹ hR (hAcoef p.ν p.ε χf A) τ y hy hDH').2
  have hDR : DifferentiableAt ℝ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
      (Axi.chart p.ε⁻¹ τ y) := by
    rw [hrt]; exact convDiffRaw dm dp hdm p d hreg s hs x
  have hNraw : DifferentiableAt ℝ
      (Axi.Nv p.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) y :=
    (UnforcedLeray.Short.IIb.chartAdv_diffAt p.ε⁻¹ hR _ τ y hy hDR).2
  have hb_raw : DifferentiableAt ℝ (p.raw τ) y :=
    hNraw.congr_of_eventuallyEq (convRawEv p τ y hy)
  have ha : DifferentiableAt ℝ (U τ) y := by
    have hU1 : ContDiff ℝ 1 (fun z : ℝ × Space => U z.1 z.2) := hU.smoothU.of_le (by norm_num)
    exact ((hU1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)) y
  -- cancellation of D_μ, FE, and ∇(sΨ) in convCoef
  have hcancel : convCoef p μ χf U A (s, x) =
      (Real.sqrt s)⁻¹ • !₂[(physDivSym (fun y' => U τ y' - p.raw τ y')
          (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y) 0,
        (physDivSym (fun y' => U τ y' - p.raw τ y')
          (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y) 2] := by
    have hdiv1 : physDivSym (U τ) (hLift p.ν p.ε p.c χf A τ) y =
        physDivSym (U τ) (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y :=
      physDivSym_congr_nhds (EventuallyEq.refl _ _) hb
    have hdiv2 : physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y =
        physDivSym (p.raw τ) (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y :=
      physDivSym_congr_nhds (EventuallyEq.refl _ _) hb
    have hsub := rac_physDivSym_sub (U τ) (p.raw τ)
      (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y ha hb_raw hh
    unfold convCoef rAcoef rAPhys coefOf
    ext i
    fin_cases i <;>
    · simp [show NearInst.chartTau p.ε⁻¹ (s, x) = τ from rfl,
        show NearInst.chartY p.ε⁻¹ (s, x) = y from rfl, hdiv1, hdiv2, ← hsub]
      ring
  have hnorm_h : ‖Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ y‖ =
      Real.sqrt s * ‖hAcoef p.ν p.ε χf A (s, x)‖ := by
    rw [Axi.norm_Nv p.ε⁻¹ _ τ hy, hage, hrt]
  have hfderiv_h := rac_fderiv_Nv_hAcoef_le p.ε_pos hs hDH
  have hdiv_norm := rac_physDivSym_norm (fun y' => U τ y' - p.raw τ y')
    (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y (ha.sub hb_raw) hh (hδU τ y).1 (hδU τ y).2
  have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsq_ne : Real.sqrt s ≠ 0 := hsq_pos.ne'
  have hss : (Real.sqrt s)⁻¹ * s = Real.sqrt s := by
    rw [inv_mul_eq_iff_eq_mul₀ hsq_ne, Real.mul_self_sqrt hs.le]
  rw [hcancel, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq_pos.le)]
  calc (Real.sqrt s)⁻¹ * ‖(!₂[(physDivSym (fun y' => U τ y' - p.raw τ y')
          (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y) 0,
        (physDivSym (fun y' => U τ y' - p.raw τ y')
          (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y) 2] : Merid)‖
      ≤ (Real.sqrt s)⁻¹ * ‖physDivSym (fun y' => U τ y' - p.raw τ y')
          (Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ) y‖ :=
        mul_le_mul_of_nonneg_left (rac_norm_mer_le _) (inv_nonneg.2 hsq_pos.le)
    _ ≤ (Real.sqrt s)⁻¹ * (4 * δU * (6 * s * ‖gradAcoef p.ν p.ε χf A (s, x)‖ +
          Real.sqrt s * ‖hAcoef p.ν p.ε χf A (s, x)‖)) := by
        refine mul_le_mul_of_nonneg_left (hdiv_norm.trans ?_) (inv_nonneg.2 hsq_pos.le)
        rw [hnorm_h]
        exact mul_le_mul_of_nonneg_left (add_le_add_left hfderiv_h _) (by positivity)
    _ = 4 * δU * (6 * (Real.sqrt s * ‖gradAcoef p.ν p.ε χf A (s, x)‖) +
          ‖hAcoef p.ν p.ε χf A (s, x)‖) := by
        have e1 : (Real.sqrt s)⁻¹ * (6 * s * ‖gradAcoef p.ν p.ε χf A (s, x)‖) =
            6 * (Real.sqrt s * ‖gradAcoef p.ν p.ε χf A (s, x)‖) := by
          linear_combination 6 * ‖gradAcoef p.ν p.ε χf A (s, x)‖ * hss
        have e2 : (Real.sqrt s)⁻¹ * (Real.sqrt s * ‖hAcoef p.ν p.ε χf A (s, x)‖) =
            ‖hAcoef p.ν p.ε χf A (s, x)‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hsq_ne, one_mul]
        linear_combination 4 * δU * (e1 + e2)
    _ ≤ 24 * δU * (‖hAcoef p.ν p.ε χf A (s, x)‖ + Real.sqrt s * ‖gradAcoef p.ν p.ε χf A (s, x)‖) := by
        nlinarith [norm_nonneg (hAcoef p.ν p.ε χf A (s, x)),
          mul_nonneg hsq_pos.le (norm_nonneg (gradAcoef p.ν p.ε χf A (s, x)))]

end UnforcedLeray.Short.PartIIIb.Concrete
