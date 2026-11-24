import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoFE
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv.Lift
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv.Diff

/-!
# `convChartRuleGen`: the chart rule for the symmetrized convection of two ring lifts
# (`PartIII-b:C/asrc/ra/9/2/2/1`, source 5034-5044)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5034-5044.

For profiles `α, β` differentiable at the chart point, the symmetrized divergence is
`div(a⊗b+b⊗a) = (a·∇)b + (b·∇)a + (div a) b + (div b) a` (`crg_physDivSym_eq`); the advection sum
is the lift of the `Q_ε, ∂_η` expression (`chartAdv_lift`), the divergence of a ring lift is
`s(Q_ε α_r + εα_r + ∂_ηα_z)` (`crg_div_Nv`, from `divergence_liftMer` and `chartAdv_dRho_dz`), and
the planar dictionary (`crg_profile`) identifies the resulting profile with `s·cBil ε α β`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Divergence of the symmetrized product -/

theorem crg_physDivSym_eq (a b : Space → Space) (y : Space) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) :
    physDivSym a b y = Axi.advection a b y + Axi.advection b a y +
      Axi.divergence a y • b y + Axi.divergence b y • a y := by
  ext i
  simp only [physDivSym, PiLp.toLp_apply]
  simp only [pw4_sym_fderiv a b y ha hb i _, Finset.sum_add_distrib]
  rw [Axi.advection, Axi.advection, pw4_fderiv_eq_sum b y (a y), pw4_fderiv_eq_sum a y (b y)]
  simp only [Axi.divergence, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, PiLp.add_apply, Finset.sum_mul]
  ring

/-! ## 2. Slice derivatives of a chart profile -/

theorem crg_hasFDeriv_slice {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    HasFDerivAt (fun y : ℝ × ℝ => α (s, y) i)
      (((EuclideanSpace.proj i : Merid →L[ℝ] ℝ).comp (fderiv ℝ α (s, x))).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : Chart)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x := by
    have := (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
    refine this.congr_fderiv ?_
    ext v <;> simp
  have h2 := (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).hasFDerivAt.comp (s, x) hα.hasFDerivAt
  exact h2.comp x h1

theorem crg_slice_apply {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => α (s, y) i) x v =
      v.1 * Axi.dQ α (s, x) i + v.2 * Axi.dEta α (s, x) i := by
  rw [(crg_hasFDeriv_slice hα i).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    EuclideanSpace.coe_proj]
  rw [Axi.clm_triple (fderiv ℝ α (s, x)) 0 v.1 v.2]
  simp [Axi.dQ, Axi.dEta]

theorem crg_deriv_s {α : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hα : DifferentiableAt ℝ α (s, x)) (i : Fin 2) :
    deriv (fun s' : ℝ => α (s', x) i) s = Axi.dS α (s, x) i := by
  have h1 : HasDerivAt (fun s' : ℝ => ((s', x) : Chart)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s := by
    have := (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    refine this.congr_deriv ?_
    rfl
  have h2 := hα.hasFDerivAt.comp_hasDerivAt s h1
  have h3 := (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s h2
  rw [show (fun s' : ℝ => α (s', x) i) = ((EuclideanSpace.proj i : Merid →L[ℝ] ℝ) ∘
    (α ∘ fun s' : ℝ => ((s', x) : Chart))) from rfl, h3.deriv]
  simp [Axi.dS]

/-! ## 3. Divergence of a ring lift -/

/-- `div(N_v α) = s(Q_ε α_r + ε α_r + ∂_η α_z)`, `ε = R⁻¹`, `s = R²/ϱ²` (source 5034-5039). -/
theorem crg_div_Nv {R : ℝ} (hR : 0 < R) (α : Chart → Merid) (τ : ℝ) (y : Space)
    (hy : y ∉ Axi.axis) (hα : DifferentiableAt ℝ α (Axi.chart R τ y)) :
    Axi.divergence (Axi.Nv R α τ) y =
      Axi.age R y * ((UnforcedLeray.Short.IIb.qEps R⁻¹ α (Axi.chart R τ y)) 0 +
        R⁻¹ * α (Axi.chart R τ y) 0 + (Axi.dEta α (Axi.chart R τ y)) 1) := by
  have hpne : (Axi.mer y).1 ≠ 0 := fun h => hy ((Axi.mem_axis_iff y).2 h)
  have hpos : 0 < (Axi.mer y).1 := lt_of_le_of_ne (Axi.ϱ_nonneg y) (Ne.symm hpne)
  have hαm : DifferentiableAt ℝ α (Axi.merChart R τ (Axi.mer y)) := by
    rw [← Axi.chart_eq_merChart]; exact hα
  have hU := UnforcedLeray.Short.IIb.chartAdv_sqrtProf_diffAt hR.ne' hpne hαm
  obtain ⟨hρ, hz⟩ := UnforcedLeray.Short.IIb.chartAdv_dRho_dz R hR α τ (Axi.mer y) hpos hαm
  rw [Axi.Nv_eq_liftMer R α τ, Axi.divergence_liftMer hy hU]
  have hρ' : Axi.dρ (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • α (Axi.merChart R τ q)) (Axi.mer y) =
      (R ^ 2 / (Axi.mer y).1 ^ 2) • UnforcedLeray.Short.IIb.qEps R⁻¹ α
        (Axi.merChart R τ (Axi.mer y)) := hρ
  rw [hρ', hz]
  have hϱ : 0 < Axi.ϱ y := hpos
  have hs : √(R ^ 2 / (Axi.mer y).1 ^ 2) = R / Axi.ϱ y := by
    rw [← div_pow]; exact Real.sqrt_sq (div_nonneg hR.le hϱ.le)
  have e1 : Axi.age R y = R ^ 2 / (Axi.mer y).1 ^ 2 := rfl
  have e2 : Axi.chart R τ y = Axi.merChart R τ (Axi.mer y) := rfl
  rw [e2, e1]
  simp only [PiLp.smul_apply, smul_eq_mul, hs]
  have : (Axi.mer y).1 = Axi.ϱ y := rfl
  rw [this]
  field_simp

/-! ## 4. The planar dictionary -/

theorem crg_fderiv_plOf {G : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G (s, x)) (v : ℝ × ℝ) :
    fderiv ℝ (plOf G s) x v =
      (v.1 * Axi.dQ G (s, x) 0 + v.2 * Axi.dEta G (s, x) 0,
        v.1 * Axi.dQ G (s, x) 1 + v.2 * Axi.dEta G (s, x) 1) := by
  have h := (crg_hasFDeriv_slice hG 0).prodMk (crg_hasFDeriv_slice hG 1)
  have e0 := crg_slice_apply hG 0 v
  have e1 := crg_slice_apply hG 1 v
  rw [(crg_hasFDeriv_slice hG 0).fderiv] at e0
  rw [(crg_hasFDeriv_slice hG 1).fderiv] at e1
  show fderiv ℝ (fun y : ℝ × ℝ => (G (s, y) 0, G (s, y) 1)) x v = _
  rw [h.fderiv, ContinuousLinearMap.prod_apply, e0, e1]

theorem crg_cAdv {F G : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G (s, x)) :
    cAdv (plOf F) (plOf G) s x =
      (F (s, x) 0 * Axi.dQ G (s, x) 0 + F (s, x) 1 * Axi.dEta G (s, x) 0,
        F (s, x) 0 * Axi.dQ G (s, x) 1 + F (s, x) 1 * Axi.dEta G (s, x) 1) := by
  unfold cAdv
  rw [crg_fderiv_plOf hG]
  rfl

theorem crg_cDiv {F : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    cDiv (plOf F) s x = Axi.dQ F (s, x) 0 + Axi.dEta F (s, x) 1 := by
  unfold cDiv
  rw [crg_fderiv_plOf hF, crg_fderiv_plOf hF]
  simp [ei]

theorem crg_cK {F : Chart → Merid} {s : ℝ} {x : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    cK (plOf F) s x =
      (x.2 * Axi.dEta F (s, x) 0 + 2 * s * Axi.dS F (s, x) 0,
        x.2 * Axi.dEta F (s, x) 1 + 2 * s * Axi.dS F (s, x) 1) := by
  have a0 := crg_slice_apply hF 0 ((0 : ℝ), (1 : ℝ))
  have a1 := crg_slice_apply hF 1 ((0 : ℝ), (1 : ℝ))
  have b0 := crg_deriv_s hF 0
  have b1 := crg_deriv_s hF 1
  simp only [zero_mul, one_mul, zero_add] at a0 a1
  simp only [cK, Kop, plOf, ei]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  rw [a0, a1, b0, b1]

/-- The profile identity: the advection profile of `chartAdv_lift` plus the two `(div)·profile`
terms of `crg_div_Nv` equals `s · cBil ε α β` (source 5034-5044). -/
theorem crg_profile (ε : ℝ) (α β : Chart → Merid) (m : Chart)
    (hα : DifferentiableAt ℝ α m) (hβ : DifferentiableAt ℝ β m) :
    m.1 • (α m 0 • UnforcedLeray.Short.IIb.qEps ε β m + α m 1 • Axi.dEta β m +
        (β m 0 • UnforcedLeray.Short.IIb.qEps ε α m + β m 1 • Axi.dEta α m)) +
      (m.1 * ((UnforcedLeray.Short.IIb.qEps ε α m) 0 + ε * α m 0 + (Axi.dEta α m) 1)) • β m +
      (m.1 * ((UnforcedLeray.Short.IIb.qEps ε β m) 0 + ε * β m 0 + (Axi.dEta β m) 1)) • α m =
    m.1 • toMer (cBil ε (plOf α) (plOf β) m.1 m.2) := by
  obtain ⟨s, x⟩ := m
  have c1 := crg_cAdv (F := α) (G := β) hβ
  have c2 := crg_cAdv (F := β) (G := α) hα
  have d1 := crg_cDiv hα
  have d2 := crg_cDiv hβ
  have k1 := crg_cK hα
  have k2 := crg_cK hβ
  ext i
  fin_cases i
  all_goals
    simp only [cBil, cB0, cB1, c1, c2, d1, d2, k1, k2, UnforcedLeray.Short.IIb.qEps,
      UnforcedLeray.Short.IIb.kAge, toMer, plOf, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply]
    simp
    ring

/-! ## 5. The chart rule -/

theorem crg_chartY_not_mem_axis {R : ℝ} (hR : 0 < R) {p : Chart} (hp : 0 < p.1) :
    NearInst.chartY R p ∉ Axi.axis := by
  intro h
  obtain ⟨_, _, hϱ, _⟩ := fe_chartY_facts hR p hp
  have h0 := (Axi.mem_axis_iff _).1 h
  rw [hϱ] at h0
  exact (div_pos hR (Real.sqrt_pos.2 hp)).ne' h0

/-- The pointwise chart rule off the axis. -/
theorem crg_key {R : ℝ} (hR : 0 < R) (α β : Chart → Merid) (τ : ℝ) (y : Space)
    (hy : y ∉ Axi.axis) (hα : DifferentiableAt ℝ α (Axi.chart R τ y))
    (hβ : DifferentiableAt ℝ β (Axi.chart R τ y)) :
    physDivSym (fun y' => Axi.Nv R α τ y') (fun y' => Axi.Nv R β τ y') y =
      Axi.Nv R (fun m => m.1 • toMer (cBil R⁻¹ (plOf α) (plOf β) m.1 m.2)) τ y := by
  obtain ⟨_, hNa⟩ := UnforcedLeray.Short.IIb.chartAdv_diffAt R hR α τ y hy hα
  obtain ⟨_, hNb⟩ := UnforcedLeray.Short.IIb.chartAdv_diffAt R hR β τ y hy hβ
  have hadv := UnforcedLeray.Short.IIb.chartAdv_lift R hR α β τ y hy hα hβ
  have hprof := crg_profile R⁻¹ α β (Axi.chart R τ y) hα hβ
  show physDivSym (Axi.Nv R α τ) (Axi.Nv R β τ) y = _
  rw [crg_physDivSym_eq _ _ y hNa hNb, hadv, crg_div_Nv hR α τ y hy hα,
    crg_div_Nv hR β τ y hy hβ]
  have e : Axi.age R y = (Axi.chart R τ y).1 := rfl
  rw [e]
  simp only [Axi.Nv]
  rw [← hprof]
  simp only [map_add, map_smul, smul_add]
  module

theorem convChartRuleGen : ConvChartRuleGen := by
  intro R hR α β q hq hα hβ
  have hrt := fe_chart_roundtrip hR q hq
  have hy := crg_chartY_not_mem_axis hR hq
  have hα' : DifferentiableAt ℝ α (Axi.chart R (NearInst.chartTau R q) (NearInst.chartY R q)) := by
    rw [hrt]; exact hα
  have hβ' : DifferentiableAt ℝ β (Axi.chart R (NearInst.chartTau R q) (NearInst.chartY R q)) := by
    rw [hrt]; exact hβ
  have key := crg_key hR α β _ _ hy hα' hβ'
  have h2 : coefOf R (fun τ y => physDivSym (fun y' => Axi.Nv R α τ y') (fun y' => Axi.Nv R β τ y') y) q =
      coefOf R (fun τ y => Axi.Nv R (fun m => m.1 • toMer (cBil R⁻¹ (plOf α) (plOf β) m.1 m.2)) τ y) q := by
    unfold coefOf
    simp only []
    rw [key]
  rw [h2, fe_coefOf_Nv hR _ q hq]

end UnforcedLeray.Short.PartIIIb.Concrete
