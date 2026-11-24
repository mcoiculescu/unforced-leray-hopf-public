import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4

/-!
# `PartIII-b:C/asrc/ra/9/4` : the pointwise chart identity `GeoGradChartEq`

Proof of `geoGradChartEq` (source 5039-5043). On `s = q.1 > 0`, with `R = ε⁻¹`,
`y = chartY R q` and `τ = chartTau R q` one has `chart R τ y = q` (`Axi.chart`), so the chart
rules `Axi.radial_chain`, `Axi.axial_chain` give the meridional components of `∇_y(F∘chart)`
at `y`, and the Cartesian term is the meridional gradient of `PsiA s = s⁻¹ F(s,·)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem geoGradChart_y0 (R : ℝ) (q : Chart) :
    UnforcedLeray.Short.PartIIIb.NearInst.chartY R q 0 = R / √q.1 := by
  simp [UnforcedLeray.Short.PartIIIb.NearInst.chartY]

theorem geoGradChart_y1 (R : ℝ) (q : Chart) :
    UnforcedLeray.Short.PartIIIb.NearInst.chartY R q 1 = 0 := by
  simp [UnforcedLeray.Short.PartIIIb.NearInst.chartY]

theorem geoGradChart_y2 (R : ℝ) (q : Chart) :
    UnforcedLeray.Short.PartIIIb.NearInst.chartY R q 2 = q.2.2 / √q.1 := by
  simp [UnforcedLeray.Short.PartIIIb.NearInst.chartY]

theorem geoGradChart_varrho {R : ℝ} (hR : 0 < R) {q : Chart} (hq : 0 < q.1) :
    UnforcedLeray.Axi.ϱ (UnforcedLeray.Short.PartIIIb.NearInst.chartY R q) = R / √q.1 := by
  have hpos : 0 < R / √q.1 := div_pos hR (Real.sqrt_pos.2 hq)
  unfold UnforcedLeray.Axi.ϱ
  rw [geoGradChart_y0, geoGradChart_y1,
    show (R / √q.1) ^ 2 + (0 : ℝ) ^ 2 = (R / √q.1) ^ 2 by ring, Real.sqrt_sq hpos.le]

theorem geoGradChart_not_axis {R : ℝ} (hR : 0 < R) {q : Chart} (hq : 0 < q.1) :
    UnforcedLeray.Short.PartIIIb.NearInst.chartY R q ∉ UnforcedLeray.Axi.axis := by
  intro h
  obtain ⟨h0, -⟩ : UnforcedLeray.Short.PartIIIb.NearInst.chartY R q 0 = 0 ∧
      UnforcedLeray.Short.PartIIIb.NearInst.chartY R q 1 = 0 := h
  rw [geoGradChart_y0] at h0
  exact (div_pos hR (Real.sqrt_pos.2 hq)).ne' h0

theorem geoGradChart_age {R : ℝ} (hR : 0 < R) {q : Chart} (hq : 0 < q.1) :
    UnforcedLeray.Axi.age R (UnforcedLeray.Short.PartIIIb.NearInst.chartY R q) = q.1 := by
  have hR0 : R ≠ 0 := hR.ne'
  unfold UnforcedLeray.Axi.age
  rw [geoGradChart_varrho hR hq, div_pow, Real.sq_sqrt hq.le]
  field_simp

theorem geoGradChart_trans {R : ℝ} (hR : 0 < R) {q : Chart} (hq : 0 < q.1) :
    UnforcedLeray.Axi.trans R (UnforcedLeray.Short.PartIIIb.NearInst.chartY R q) = q.2.2 := by
  have hR0 : R ≠ 0 := hR.ne'
  have hs0 : √q.1 ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  unfold UnforcedLeray.Axi.trans
  rw [geoGradChart_varrho hR hq, geoGradChart_y2]
  field_simp

theorem geoGradChart_phase {R : ℝ} (hR : 0 < R) {q : Chart} (hq : 0 < q.1) :
    UnforcedLeray.Axi.phase R (UnforcedLeray.Short.PartIIIb.NearInst.chartTau R q)
      (UnforcedLeray.Short.PartIIIb.NearInst.chartY R q) = q.2.1 := by
  have hR0 : R ≠ 0 := hR.ne'
  unfold UnforcedLeray.Axi.phase UnforcedLeray.Short.PartIIIb.NearInst.chartTau
  rw [geoGradChart_age hR hq]
  field_simp
  ring

/-- The chart point of `(s, (q, η))` is recovered: `chart R (chartTau R q) (chartY R q) = q`. -/
theorem geoGradChart_chart {R : ℝ} (hR : 0 < R) {q : Chart} (hq : 0 < q.1) :
    UnforcedLeray.Axi.chart R (UnforcedLeray.Short.PartIIIb.NearInst.chartTau R q)
      (UnforcedLeray.Short.PartIIIb.NearInst.chartY R q) = q :=
  Prod.ext (geoGradChart_age hR hq)
    (Prod.ext (geoGradChart_phase hR hq) (geoGradChart_trans hR hq))

theorem geoGradChart_slice_diff (F : Chart → ℝ) (a : ℝ) (x : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F (a, x)) :
    DifferentiableAt ℝ (fun x' : ℝ × ℝ => F (a, x')) x :=
  hF.comp x ((differentiableAt_const a).prodMk differentiableAt_id)

theorem geoGradChart_fderiv_slice (F : Chart → ℝ) (a : ℝ) (x v : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F (a, x)) :
    fderiv ℝ (fun x' : ℝ × ℝ => F (a, x')) x v = fderiv ℝ F (a, x) (0, v) := by
  have h : HasFDerivAt (fun x' : ℝ × ℝ => F (a, x')) _ x :=
    hF.hasFDerivAt.comp x ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x))
  rw [h.fderiv]
  simp

/-- The first meridional component of `∇_y (F∘chart)` at `y` (chart rule `radial_chain`). -/
theorem geoGradChart_comp0 {R : ℝ} (hR : 0 < R) {F : Chart → ℝ} {q : Chart} (hq : 0 < q.1)
    (hF : DifferentiableAt ℝ F q) {τ : ℝ} {y : Space} (hax : y ∉ UnforcedLeray.Axi.axis)
    (hτy : UnforcedLeray.Axi.chart R τ y = q) (hy0 : y 0 = R / √q.1) (hy1 : y 1 = 0) :
    physGrad (fun y' => F (UnforcedLeray.Axi.chart R τ y')) y 0 =
      √q.1 * (UnforcedLeray.Axi.dQ F q - R⁻¹ *
        (2 * q.1 * UnforcedLeray.Axi.dS F q + q.2.2 * UnforcedLeray.Axi.dEta F q)) := by
  have hF' : DifferentiableAt ℝ F (UnforcedLeray.Axi.chart R τ y) := by
    rw [hτy]; exact hF
  have hrad := UnforcedLeray.Axi.radial_chain hR hax hF'
  have hage : UnforcedLeray.Axi.age R y = q.1 := congrArg Prod.fst hτy
  have htr : UnforcedLeray.Axi.trans R y = q.2.2 := congrArg (fun z => z.2.2) hτy
  rw [hτy, hage, htr] at hrad
  have hϱ : UnforcedLeray.Axi.ϱ y = R / √q.1 := by
    have hpos : 0 < R / √q.1 := div_pos hR (Real.sqrt_pos.2 hq)
    unfold UnforcedLeray.Axi.ϱ
    rw [hy0, hy1, show (R / √q.1) ^ 2 + (0 : ℝ) ^ 2 = (R / √q.1) ^ 2 by ring,
      Real.sqrt_sq hpos.le]
  have hpos : 0 < R / √q.1 := div_pos hR (Real.sqrt_pos.2 hq)
  have hc0 : UnforcedLeray.coordinateVector (0 : Fin 3) = UnforcedLeray.Axi.eR y := by
    ext i
    fin_cases i
    · simp [UnforcedLeray.Axi.eR_apply_zero, hϱ, hy0, div_self hpos.ne', UnforcedLeray.coordinateVector, EuclideanSpace.single_apply]
    · simp [UnforcedLeray.Axi.eR_apply_one, hy1, UnforcedLeray.coordinateVector, EuclideanSpace.single_apply]
    · simp [UnforcedLeray.Axi.eR_apply_two, UnforcedLeray.coordinateVector, EuclideanSpace.single_apply]
  unfold physGrad
  simp only [PiLp.toLp_apply]
  rw [hc0, hrad]
  simp only [smul_eq_mul]

/-- The second meridional component (chart rule `axial_chain`). -/
theorem geoGradChart_comp2 {R : ℝ} (hR : 0 < R) {F : Chart → ℝ} {q : Chart} (hq : 0 < q.1)
    (hF : DifferentiableAt ℝ F q) {τ : ℝ} {y : Space} (hax : y ∉ UnforcedLeray.Axi.axis)
    (hτy : UnforcedLeray.Axi.chart R τ y = q) :
    physGrad (fun y' => F (UnforcedLeray.Axi.chart R τ y')) y 2 =
      √q.1 * UnforcedLeray.Axi.dEta F q := by
  have hF' : DifferentiableAt ℝ F (UnforcedLeray.Axi.chart R τ y) := by
    rw [hτy]; exact hF
  have hax' := UnforcedLeray.Axi.axial_chain hR hax hF'
  have hage : UnforcedLeray.Axi.age R y = q.1 := congrArg Prod.fst hτy
  rw [hτy, hage] at hax'
  unfold physGrad
  simp only [PiLp.toLp_apply]
  have hc2 : UnforcedLeray.coordinateVector (2 : Fin 3) = UnforcedLeray.Axi.e3 := rfl
  rw [hc2, hax']
  simp only [smul_eq_mul]

/-- The chart coefficient of `∇_y (F∘chart)` (source 5039-5043, the `coefOf` side). -/
theorem geoGradChart_coef {R : ℝ} (hR : 0 < R) {F : Chart → ℝ} {q : Chart} (hq : 0 < q.1)
    (hF : DifferentiableAt ℝ F q) :
    UnforcedLeray.Short.PartIIIb.Concrete.coefOf R
        (fun τ y => physGrad (fun y' => F (UnforcedLeray.Axi.chart R τ y')) y) q =
      !₂[UnforcedLeray.Axi.dQ F q - R⁻¹ *
          (2 * q.1 * UnforcedLeray.Axi.dS F q + q.2.2 * UnforcedLeray.Axi.dEta F q),
        UnforcedLeray.Axi.dEta F q] := by
  have hax := geoGradChart_not_axis hR hq
  have h0 := geoGradChart_comp0 hR hq hF hax (geoGradChart_chart hR hq)
    (geoGradChart_y0 R q) (geoGradChart_y1 R q)
  have h2 := geoGradChart_comp2 hR hq hF hax (geoGradChart_chart hR hq)
  have hsq : √q.1 ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  dsimp only [UnforcedLeray.Short.PartIIIb.Concrete.coefOf]
  rw [h0, h2]
  ext i
  fin_cases i <;> simp [hsq]

/-- The Cartesian term `s·∇_{q,η}` of a slice `x ↦ s⁻¹F(s,x)` (source 5039-5043). -/
theorem geoGradChart_cart {F : Chart → ℝ} {q : Chart} (hq : 0 < q.1)
    (hF : DifferentiableAt ℝ F q) (g : ℝ × ℝ → ℝ)
    (hg : ∀ x : ℝ × ℝ, g x = (q.1)⁻¹ * F (q.1, x)) :
    q.1 • UnforcedLeray.Short.PartIIIb.Concrete.toMer
        (UnforcedLeray.Short.PartIIIb.Concrete.mgrad g q.2) =
      !₂[UnforcedLeray.Axi.dQ F q, UnforcedLeray.Axi.dEta F q] := by
  have hg' : g = fun x => (q.1)⁻¹ * F (q.1, x) := funext hg
  have hsl : DifferentiableAt ℝ (fun x : ℝ × ℝ => F (q.1, x)) q.2 :=
    geoGradChart_slice_diff F q.1 q.2 hF
  have e0 : fderiv ℝ g q.2 (UnforcedLeray.Short.PartIIIb.Concrete.ei 0) =
      (q.1)⁻¹ * UnforcedLeray.Axi.dQ F q := by
    rw [hg', fderiv_const_mul hsl, smul_apply,
      geoGradChart_fderiv_slice F q.1 q.2 _ hF]
    rfl
  have e1 : fderiv ℝ g q.2 (UnforcedLeray.Short.PartIIIb.Concrete.ei 1) =
      (q.1)⁻¹ * UnforcedLeray.Axi.dEta F q := by
    rw [hg', fderiv_const_mul hsl, smul_apply,
      geoGradChart_fderiv_slice F q.1 q.2 _ hF]
    rfl
  have hm : UnforcedLeray.Short.PartIIIb.Concrete.mgrad g q.2 =
      ((q.1)⁻¹ * UnforcedLeray.Axi.dQ F q, (q.1)⁻¹ * UnforcedLeray.Axi.dEta F q) := by
    unfold UnforcedLeray.Short.PartIIIb.Concrete.mgrad
    rw [e0, e1]
  rw [hm]
  ext i
  fin_cases i <;> simp [UnforcedLeray.Short.PartIIIb.Concrete.toMer, hq.ne']

/-- **The pointwise chart identity** `geoGradPiece = gradRem` on `s > 0`
(source 5039-5043, target of `PartIII-b:C/asrc/ra/9/4`). -/
theorem geoGradChartEq : GeoGradChartEq := by
  intro p μ χf A q hq hF
  have hR : 0 < p.ε⁻¹ := inv_pos.2 p.ε_pos
  have hc := geoGradChart_coef hR hq hF
  have hg : ∀ x : ℝ × ℝ,
      PsiA p.ν χf A q.1 x = (q.1)⁻¹ * sPsiChart p χf A (q.1, x) := by
    intro x
    show PsiA p.ν χf A q.1 x = (q.1)⁻¹ * (q.1 * PsiA p.ν χf A q.1 x)
    rw [← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
  have hcart := geoGradChart_cart hq hF (PsiA p.ν χf A q.1) hg
  rw [inv_inv] at hc
  show UnforcedLeray.Short.PartIIIb.Concrete.coefOf p.ε⁻¹
      (fun τ y => physGrad (psiLift p.ν p.ε χf A τ) y) q
      - q.1 • toMer (mgrad (PsiA p.ν χf A q.1) q.2) = gradRem p μ χf A q
  rw [hcart]
  have hc' : UnforcedLeray.Short.PartIIIb.Concrete.coefOf p.ε⁻¹
      (fun τ y => physGrad (psiLift p.ν p.ε χf A τ) y) q =
      !₂[UnforcedLeray.Axi.dQ (sPsiChart p χf A) q -
          p.ε * (2 * q.1 * UnforcedLeray.Axi.dS (sPsiChart p χf A) q +
            q.2.2 * UnforcedLeray.Axi.dEta (sPsiChart p χf A) q),
        UnforcedLeray.Axi.dEta (sPsiChart p χf A) q] := hc
  rw [hc']
  ext i
  fin_cases i <;> simp [gradRem] <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
