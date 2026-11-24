import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Tools

/-!
# `PartIII-b:C/rep/8/1/1/1/asm`: the stream-cut assembly of `GeomX`

Source `the November 2 reference manuscript`
lines 4178-4186 and 5415-5427 (see `Asm/Defs.lean` for the mathematics).

`GeomXAsm.geomX_of_leaves` proves `D.GeomX` from

* the pieces of `Pieces.lean`: `PhasePrimitive`, `TaylorWidth`, `ZRegular`;
* the two deterministic calculus statements `StreamCutAlgStmt` (derivative of the stream cutoff)
  and `RayFTCStmt` (ray bounds of the value, the primitive and its `z`-derivative);
* the source facts `ZPrimRegular` (outward primitive), `DPhaseMeas` (joint measurability of the
  phase part), `StreamCutEq` (`mnX = 𝒞_y zMt` off the axis) and `XcmpCellMeas` (measurability of
  `xcmp` along the cell);
* `IsStreamCutoff D.K.χy` and eventually `ν ≤ 1`.

At a young chart point `(s, η)` with receiver `y = (r, 0, z)`, `r = R/√s`, every phase `q` of the
cell gives `|D(actX - mnX)| ≤ C₀ · rayBound(|DzAct - DzMt|)`; the integrand splits into the phase
part (`dPhase`, `L²_τ`-bounded at every ray chart point after a `c`-periodic shift, then
Minkowski) and the width part (`dWidth`, bounded pointwise), and each of the four terms of
`rayBound` is `≤ A (R/r)^5 = A s^{5/2}` by `rayPow_le`.  Altogether
`cellL2 xcmp ≤ C₀ (4 + 4) A s^{5/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomXAsm

/-! ## 1. The half plane and the clear region -/

theorem ϱ_hpt {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℝ) : ϱ (hpt ρ z) = ρ := by
  unfold ϱ hpt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq hρ]

theorem outRay_hpt {r : ℝ} (hr : 0 < r) (z t : ℝ) : outRay (hpt r z) t = hpt t z := by
  unfold outRay
  rw [ϱ_hpt hr.le]
  unfold hpt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, div_self hr.ne', mul_one, zero_div, mul_zero]

theorem isOpen_clearSet (ε ν : ℝ) : IsOpen (clearSet ε ν) :=
  (isOpen_lt continuous_const continuous_ϱ).inter
    (isOpen_lt continuous_const ((continuous_const.mul continuous_ϱ).pow 2))

theorem hpt_mem_clearSet {ε ν ρ : ℝ} (hρ : 0 < ρ) (h : ν / (11 / 10) < (ε * ρ) ^ 2) (z : ℝ) :
    hpt ρ z ∈ clearSet ε ν := by
  refine ⟨?_, ?_⟩
  · show 0 < ϱ (hpt ρ z)
    rw [ϱ_hpt hρ.le]; exact hρ
  · show ν / (11 / 10) < (ε * ϱ (hpt ρ z)) ^ 2
    rw [ϱ_hpt hρ.le]; exact h

theorem continuous_hpt (z : ℝ) : Continuous fun ρ : ℝ => hpt ρ z := by
  unfold hpt
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_id
  · exact continuous_const
  · exact continuous_const

theorem continuous_chartTau_q (R s η : ℝ) :
    Continuous fun q : ℝ => NearInst.chartTau R (s, (q, η)) := by
  show Continuous fun q : ℝ => 2 * q / R + Real.log s
  exact ((continuous_const.mul continuous_id).div_const R).add continuous_const

/-- The chart point of the ray point `(ρ, 0, z)`: `s' = (R/ρ)²`, `η' = zR/ρ`. -/
theorem chartY_ray {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (q z : ℝ) :
    NearInst.chartY R ((R / ρ) ^ 2, (q, z * (R / ρ))) = hpt ρ z := by
  rw [chartY_eq_hpt, Real.sqrt_sq (div_pos hR hρ).le]
  congr 1
  · field_simp
  · field_simp

theorem sq_rpow_five_half {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (5 / 2 : ℝ) = x ^ 5 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

theorem sqrt_pow_five {s : ℝ} (hs : 0 ≤ s) : Real.sqrt s ^ 5 = s ^ (5 / 2 : ℝ) := by
  rw [← sq_rpow_five_half (Real.sqrt_nonneg s), Real.sq_sqrt hs]

/-! ## 2. Elementary bounds -/

theorem ofReal_combo {C₀ a b d e r : ℝ} (hC₀ : 0 ≤ C₀) {B0 B1 B2 : ℝ≥0∞}
    (hb : ENNReal.ofReal b ≤ B0) (hd : ENNReal.ofReal d ≤ B2) (he : ENNReal.ofReal e ≤ B1)
    (hr : 0 < r) :
    ENNReal.ofReal (C₀ * (a + r⁻¹ * b + r⁻¹ ^ 3 * d + r⁻¹ ^ 2 * e)) ≤
      ENNReal.ofReal C₀ * (ENNReal.ofReal a + ENNReal.ofReal r⁻¹ * B0 +
        ENNReal.ofReal (r⁻¹ ^ 2) * B1 + ENNReal.ofReal (r⁻¹ ^ 3) * B2) := by
  have hri : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
  rw [ENNReal.ofReal_mul hC₀]
  gcongr ENNReal.ofReal C₀ * ?_
  calc ENNReal.ofReal (a + r⁻¹ * b + r⁻¹ ^ 3 * d + r⁻¹ ^ 2 * e)
      ≤ ENNReal.ofReal a + ENNReal.ofReal (r⁻¹ * b) + ENNReal.ofReal (r⁻¹ ^ 3 * d) +
          ENNReal.ofReal (r⁻¹ ^ 2 * e) := by
        refine (ENNReal.ofReal_add_le).trans ?_
        gcongr
        refine (ENNReal.ofReal_add_le).trans ?_
        gcongr
        exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal a + ENNReal.ofReal r⁻¹ * ENNReal.ofReal b +
          ENNReal.ofReal (r⁻¹ ^ 3) * ENNReal.ofReal d +
          ENNReal.ofReal (r⁻¹ ^ 2) * ENNReal.ofReal e := by
        rw [ENNReal.ofReal_mul hri, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal r⁻¹ * B0 + ENNReal.ofReal (r⁻¹ ^ 3) * B2 +
          ENNReal.ofReal (r⁻¹ ^ 2) * B1 := by gcongr
    _ = _ := by ring

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

theorem dDiff_le (T : LStr Pl K L) (τ : ℝ) (x : Space) :
    dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ x ≤
      dPhase Pl K L μ T τ x + dWidth Pl K L μ T τ x := by
  unfold dDiff dPhase dWidth
  calc ‖fderiv ℝ (zAct Pl K L μ T τ) x - fderiv ℝ (zMt Pl K L μ T τ) x‖
      = ‖(fderiv ℝ (zAct Pl K L μ T τ) x - fderiv ℝ (zMid Pl K L μ T τ) x) +
          (fderiv ℝ (zMid Pl K L μ T τ) x - fderiv ℝ (zMt Pl K L μ T τ) x)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _

theorem phasePrimitiveAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : PhasePrimitiveAt Pl K L μ C k) :
    PhasePrimitiveAt Pl K L μ C' k' := by
  intro T s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h T s hs η).1, bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h T s hs η).2⟩

theorem taylorWidthAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : TaylorWidthAt Pl K L μ C k) :
    TaylorWidthAt Pl K L μ C' k' := by
  intro T hTz s hs η q
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h T hTz s hs η q)

end Regime

theorem rayBound_eq' (g : Space → ℝ) (r z : ℝ) :
    rayBound g r z = ENNReal.ofReal (g (hpt r z)) + ENNReal.ofReal (r⁻¹ ^ (0 + 1)) * rayW 0 g r z +
      ENNReal.ofReal (r⁻¹ ^ (1 + 1)) * rayW 1 g r z +
      ENNReal.ofReal (r⁻¹ ^ (2 + 1)) * rayW 2 g r z := by
  rw [zero_add, pow_one]
  rfl

/-! ## 3. One regime -/

section Regime2

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

theorem geomXAt_of_leaves {C₀ C : ℝ} {k : ℕ} (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C)
    (hAlg : StreamCutAlgWith K.χy C₀) (hF : RayFTCStmt) (hS : StreamCutEq)
    (hP : PhasePrimitiveAt Pl K L μ C k) (hT : TaylorWidthAt Pl K L μ C k)
    (hR : ZRegularAt Pl K L μ) (hZ : ZPrimRegularAt Pl K L μ) (hm : DPhaseMeasAt Pl K L μ)
    (hM : ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
        AEMeasurable (fun q : ℝ => xcmp Pl K L μ T
        (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))))
        (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2)))) :
    GeomXAt Pl K L μ (8 * C₀ * C) k := by
  intro T hTz s hs η
  refine ⟨hM T s hs η, ?_⟩
  have hν0 := L.ν_pos
  have hε0 := L.ε_pos
  set R := L.ε⁻¹ with hRdef
  have hR0 : 0 < R := inv_pos.2 hε0
  set c := cOf L.ν with hcdef
  have hc0 : 0 < c := by simp only [hcdef, cOf]; positivity
  have hs0 : 0 < s := hs.1
  have hsν : L.ν * s ≤ 1 := by
    have h2 := hs.2
    rw [le_div_iff₀ hν0] at h2
    linarith
  set r := R / Real.sqrt s with hrdef
  set z := η / Real.sqrt s with hzdef
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hr0 : 0 < r := div_pos hR0 hsq
  have hRr : R / r = Real.sqrt s := by rw [hrdef]; field_simp
  have hRr2 : R ^ 2 / r ^ 2 = s := by rw [← div_pow, hRr, Real.sq_sqrt hs0.le]
  have hS5 : (R / r) ^ 5 = s ^ (5 / 2 : ℝ) := by rw [hRr, sqrt_pow_five hs0.le]
  set N := oldN1 Pl K L T with hNdef
  set A : ℝ≥0∞ := ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4) * N with hAdef
  set S5 : ℝ≥0∞ := ENNReal.ofReal ((R / r) ^ 5) with hS5def
  have hCk : 0 ≤ C * L.ν⁻¹ ^ k * L.ε ^ 4 := by positivity
  have hconv : ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * t)) * N = A * ENNReal.ofReal t := by
    intro t ht
    rw [hAdef, show C * L.ν⁻¹ ^ k * (L.ε ^ 4 * t) = C * L.ν⁻¹ ^ k * L.ε ^ 4 * t by ring,
      ENNReal.ofReal_mul hCk]
    ring
  -- the clear region contains the outward ray
  have hclear0 : ∀ ρ : ℝ, r ≤ ρ → L.ν / (11 / 10) < (L.ε * ρ) ^ 2 := by
    intro ρ hρ
    have h1 : L.ε * r = (Real.sqrt s)⁻¹ := by
      rw [hrdef, hRdef]; field_simp
    have h2 : (L.ε * r) ^ 2 = s⁻¹ := by rw [h1, inv_pow, Real.sq_sqrt hs0.le]
    have h3 : L.ν ≤ s⁻¹ := by
      rw [le_inv_comm₀ hν0 hs0]
      have h6 := hs.2
      rwa [one_div] at h6
    have h4 : (L.ε * r) ^ 2 ≤ (L.ε * ρ) ^ 2 := by
      gcongr
    have h5 : L.ν / (11 / 10) < L.ν := by linarith
    linarith
  have hclear : ∀ ρ : ℝ, r ≤ ρ → hpt ρ z ∈ clearSet L.ε L.ν :=
    fun ρ hρ => hpt_mem_clearSet (hr0.trans_le hρ) (hclear0 ρ hρ) z
  -- the ray chart: per-ray-point bounds
  have hs'ν : ∀ ρ : ℝ, r ≤ ρ → (R / ρ) ^ 2 ∈ Ioc (0 : ℝ) (1 / L.ν) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hr0.trans_le hρ
    refine ⟨by positivity, ?_⟩
    calc (R / ρ) ^ 2 ≤ (R / r) ^ 2 := by gcongr
      _ = s := by rw [div_pow]; exact hRr2
      _ ≤ 1 / L.ν := hs.2
  have hS5ρ : ∀ ρ : ℝ, 0 < ρ → ((R / ρ) ^ 2) ^ (5 / 2 : ℝ) = (R / ρ) ^ 5 :=
    fun ρ hρ => sq_rpow_five_half (div_pos hR0 hρ).le
  have hW5 : ∀ τ : ℝ, ∀ ρ : ℝ, r ≤ ρ →
      ENNReal.ofReal (dWidth Pl K L μ T τ (hpt ρ z)) ≤ A * ENNReal.ofReal ((R / ρ) ^ 5) := by
    intro τ ρ hρ
    have hρ0 : 0 < ρ := hr0.trans_le hρ
    have h := hT T hTz ((R / ρ) ^ 2) (hs'ν ρ hρ) (z * (R / ρ))
      (R / 2 * (τ - Real.log ((R / ρ) ^ 2)))
    have htau : NearInst.chartTau R ((R / ρ) ^ 2, (R / 2 * (τ - Real.log ((R / ρ) ^ 2)),
        z * (R / ρ))) = τ := by
      unfold NearInst.chartTau
      field_simp
      ring
    rw [htau, chartY_ray hR0 hρ0, hconv _ (Real.rpow_nonneg (by positivity) _),
      hS5ρ ρ hρ0] at h
    exact h
  have hP5 : ∀ ρ ∈ Ioi r, cellN c (fun q => ENNReal.ofReal (dPhase Pl K L μ T
      (NearInst.chartTau R (s, (q, η))) (hpt ρ z))) ≤ A * ENNReal.ofReal ((R / ρ) ^ 5) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hr0.trans hρ
    set s' := (R / ρ) ^ 2 with hs'def
    set η' := z * (R / ρ) with hη'def
    set a := R / 2 * (Real.log s - Real.log s') with hadef
    set G : ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (dPhase Pl K L μ T
      (NearInst.chartTau R (s', (q, η'))) (NearInst.chartY R (s', (q, η')))) with hGdef
    have hG : ∀ q, ENNReal.ofReal (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))
        (hpt ρ z)) = G (q + a) := by
      intro q
      have htau : NearInst.chartTau R (s', (q + a, η')) = NearInst.chartTau R (s, (q, η)) := by
        unfold NearInst.chartTau
        rw [hadef]
        field_simp
        ring
      have hy : NearInst.chartY R (s', (q + a, η')) = hpt ρ z := chartY_ray hR0 hρ0 _ _
      show _ = ENNReal.ofReal (dPhase Pl K L μ T (NearInst.chartTau R (s', (q + a, η')))
        (NearInst.chartY R (s', (q + a, η'))))
      rw [htau, hy]
    have hGper : ∀ q, G (q + c) = G q := by
      intro q
      have htau : NearInst.chartTau R (s', (q + c, η')) =
          NearInst.chartTau R (s', (q, η')) + 2 * cOf L.ν / L.ε⁻¹ := by
        unfold NearInst.chartTau
        rw [hcdef, hRdef]
        ring
      have hy : NearInst.chartY R (s', (q + c, η')) = NearInst.chartY R (s', (q, η')) := rfl
      simp only [hGdef, htau, hy, dPhase_add_period]
    calc cellN c (fun q => ENNReal.ofReal (dPhase Pl K L μ T
          (NearInst.chartTau R (s, (q, η))) (hpt ρ z)))
        = cellN c (fun q => G (q + a)) := by simp only [hG]
      _ = cellN c G := cellN_shift hc0 hGper a
      _ = cellL2 R c (dPhase Pl K L μ T) s' η' := (cellL2_eq_cellN R c _ s' η').symm
      _ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s' ^ (5 / 2 : ℝ))) * N :=
          (hP T s' (hs'ν ρ hρ.le) η').2
      _ = A * ENNReal.ofReal ((R / ρ) ^ 5) := by
          rw [hconv _ (Real.rpow_nonneg (by positivity) _), hs'def, hS5ρ ρ hρ0]
  -- the pointwise bound at every phase
  have hmemA : zAct Pl K L μ T ∈ ({zAct Pl K L μ T, zMid Pl K L μ T, zMt Pl K L μ T} :
      Set (ℝ → Space → Space)) := by simp
  have hmemT : zMt Pl K L μ T ∈ ({zAct Pl K L μ T, zMid Pl K L μ T, zMt Pl K L μ T} :
      Set (ℝ → Space → Space)) := by simp
  have hmemA' : zAct Pl K L μ T ∈ ({zAct Pl K L μ T, zMt Pl K L μ T} :
      Set (ℝ → Space → Space)) := by simp
  have hmemT' : zMt Pl K L μ T ∈ ({zAct Pl K L μ T, zMt Pl K L μ T} :
      Set (ℝ → Space → Space)) := by simp
  have hdiff : ∀ τ : ℝ, ∀ Z ∈ ({zAct Pl K L μ T, zMid Pl K L μ T, zMt Pl K L μ T} :
      Set (ℝ → Space → Space)), ∀ ρ : ℝ, r ≤ ρ → DifferentiableAt ℝ (Z τ) (hpt ρ z) := by
    intro τ Z hZm ρ hρ
    exact (((hR T τ).1 Z hZm).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_clearSet _ _).mem_nhds (hclear ρ hρ))
  have hpoint : ∀ τ : ℝ, ENNReal.ofReal (xcmp Pl K L μ T τ (hpt r z)) ≤
      ENNReal.ofReal C₀ * rayBound (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ) r z := by
    intro τ
    have hyc : hpt r z ∈ clearSet L.ε L.ν := hclear r le_rfl
    have hϱ : 0 < ϱ (hpt r z) := hyc.1
    have hxe : xcmp Pl K L μ T τ (hpt r z) =
        ‖fderiv ℝ (wardStreamCut L.ν R K.χy (zAct Pl K L μ T) τ) (hpt r z) -
          fderiv ℝ (wardStreamCut L.ν R K.χy (zMt Pl K L μ T) τ) (hpt r z)‖ := by
      unfold xcmp
      have he : mnX Pl K L μ T τ =ᶠ[𝓝 (hpt r z)]
          wardStreamCut L.ν R K.χy (zMt Pl K L μ T) τ := by
        filter_upwards [(isOpen_lt continuous_const continuous_ϱ).mem_nhds hϱ] with y' hy'
        exact hS Pl K L μ T τ y' hy'
      rw [he.fderiv_eq]
      rfl
    have hPA := hZ T τ (zAct Pl K L μ T) hmemA' r z hr0 (hclear0 r le_rfl)
    have hPT := hZ T τ (zMt Pl K L μ T) hmemT' r z hr0 (hclear0 r le_rfl)
    have hyoung : L.ν * (R ^ 2 / r ^ 2) ≤ 1 := by rw [hRr2]; exact hsν
    have h1 := hAlg L.ν R r z τ (zAct Pl K L μ T) (zMt Pl K L μ T) hν0 hR0 hr0 hyoung
      (hdiff τ _ hmemA r le_rfl) (hdiff τ _ hmemT r le_rfl) hPA hPT
    have hlim : Tendsto (fun t : ℝ => zAct Pl K L μ T τ (hpt t z) - zMt Pl K L μ T τ (hpt t z))
        atTop (𝓝 0) := by
      have l1 := (hR T τ).2 _ hmemA (hpt r z) hyc
      have l2 := (hR T τ).2 _ hmemT (hpt r z) hyc
      simp only [outRay_hpt hr0] at l1 l2
      simpa using l1.sub l2
    obtain ⟨hv, hΨ, hD⟩ := hF r z τ (zAct Pl K L μ T) (zMt Pl K L μ T) hr0
      (fun ρ hρ => ⟨hdiff τ _ hmemA ρ hρ, hdiff τ _ hmemT ρ hρ⟩) hlim hPA hPT
    rw [hxe]
    exact (ENNReal.ofReal_le_ofReal h1).trans (ofReal_combo hC₀ hv hΨ hD hr0)
  -- the width part is bounded pointwise
  have hsplit : ∀ τ : ℝ, rayBound (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ) r z ≤
      rayBound (dPhase Pl K L μ T τ) r z + 4 * (A * S5) := by
    intro τ
    have hterm0 : ENNReal.ofReal (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ (hpt r z)) ≤
        ENNReal.ofReal (dPhase Pl K L μ T τ (hpt r z)) + A * S5 := by
      calc ENNReal.ofReal (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ (hpt r z))
          ≤ ENNReal.ofReal (dPhase Pl K L μ T τ (hpt r z) + dWidth Pl K L μ T τ (hpt r z)) :=
            ENNReal.ofReal_le_ofReal (dDiff_le Pl K L μ T τ _)
        _ ≤ ENNReal.ofReal (dPhase Pl K L μ T τ (hpt r z)) +
            ENNReal.ofReal (dWidth Pl K L μ T τ (hpt r z)) := ENNReal.ofReal_add_le
        _ ≤ _ := by gcongr; exact hW5 τ r le_rfl
    have htermj : ∀ j : ℕ, j ≤ 2 →
        ENNReal.ofReal (r⁻¹ ^ (j + 1)) * rayW j (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ) r z ≤
          ENNReal.ofReal (r⁻¹ ^ (j + 1)) * rayW j (dPhase Pl K L μ T τ) r z + A * S5 := by
      intro j hj
      have hmeas5 : Measurable fun ρ : ℝ => ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) :=
        ((measurable_id.pow_const j).mul
          ((measurable_const.div measurable_id).pow_const 5)).ennreal_ofReal
      have hle : rayW j (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ) r z ≤
          rayW j (dPhase Pl K L μ T τ) r z +
            A * ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) := by
        unfold rayW
        rw [← lintegral_const_mul _ hmeas5, ← lintegral_add_right _ (hmeas5.const_mul A)]
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ0 : 0 < ρ := hr0.trans hρ
        have hpj : 0 ≤ ρ ^ j := pow_nonneg hρ0.le j
        calc ENNReal.ofReal (ρ ^ j * dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ (hpt ρ z))
            ≤ ENNReal.ofReal (ρ ^ j * dPhase Pl K L μ T τ (hpt ρ z) +
                ρ ^ j * dWidth Pl K L μ T τ (hpt ρ z)) := by
              apply ENNReal.ofReal_le_ofReal
              rw [← mul_add]
              exact mul_le_mul_of_nonneg_left (dDiff_le Pl K L μ T τ _) hpj
          _ ≤ ENNReal.ofReal (ρ ^ j * dPhase Pl K L μ T τ (hpt ρ z)) +
                ENNReal.ofReal (ρ ^ j) * ENNReal.ofReal (dWidth Pl K L μ T τ (hpt ρ z)) := by
              refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
              congr 1
              exact ENNReal.ofReal_mul hpj
          _ ≤ ENNReal.ofReal (ρ ^ j * dPhase Pl K L μ T τ (hpt ρ z)) +
                ENNReal.ofReal (ρ ^ j) * (A * ENNReal.ofReal ((R / ρ) ^ 5)) := by
              gcongr
              exact hW5 τ ρ hρ.le
          _ = ENNReal.ofReal (ρ ^ j * dPhase Pl K L μ T τ (hpt ρ z)) +
                A * ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) := by
              congr 1
              rw [ENNReal.ofReal_mul hpj]
              ring
      calc ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
            rayW j (dDiff (zAct Pl K L μ T) (zMt Pl K L μ T) τ) r z
          ≤ ENNReal.ofReal (r⁻¹ ^ (j + 1)) * (rayW j (dPhase Pl K L μ T τ) r z +
              A * ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5)) := by gcongr
        _ = ENNReal.ofReal (r⁻¹ ^ (j + 1)) * rayW j (dPhase Pl K L μ T τ) r z +
              A * (ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
                ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5)) := by ring
        _ ≤ _ := by
            gcongr
            exact rayPow_le hj hr0 hR0.le
    have h0 := htermj 0 (by norm_num)
    have h1 := htermj 1 (by norm_num)
    have h2 := htermj 2 (by norm_num)
    rw [rayBound_eq', rayBound_eq']
    calc _ ≤ (ENNReal.ofReal (dPhase Pl K L μ T τ (hpt r z)) + A * S5) +
          (ENNReal.ofReal (r⁻¹ ^ (0 + 1)) * rayW 0 (dPhase Pl K L μ T τ) r z + A * S5) +
          (ENNReal.ofReal (r⁻¹ ^ (1 + 1)) * rayW 1 (dPhase Pl K L μ T τ) r z + A * S5) +
          (ENNReal.ofReal (r⁻¹ ^ (2 + 1)) * rayW 2 (dPhase Pl K L μ T τ) r z + A * S5) := by
          gcongr
      _ = _ := by ring
  -- the phase part: cell norm of each term
  set F : ℝ → ℝ → ℝ≥0∞ := fun q ρ => ENNReal.ofReal ((clearSet L.ε L.ν).indicator
    (fun y => dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η))) y) (hpt ρ z)) with hFdef
  have hFmeas : Measurable (Function.uncurry F) := by
    have hmap : Measurable fun p : ℝ × ℝ => (NearInst.chartTau R (s, (p.1, η)), hpt p.2 z) :=
      ((continuous_chartTau_q R s η).measurable.comp measurable_fst).prodMk
        ((continuous_hpt z).measurable.comp measurable_snd)
    exact ((hm T).comp hmap).ennreal_ofReal
  have hrayEq : ∀ j : ℕ, ∀ q : ℝ,
      rayW j (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z =
        ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j) * F q ρ := by
    intro j q
    unfold rayW
    refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [hFdef]
    dsimp only
    rw [indicator_of_mem (hclear ρ (le_of_lt hρ)), ENNReal.ofReal_mul (pow_nonneg (hr0.trans hρ).le j)]
  have hmj : ∀ j : ℕ, Measurable fun q => ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
      rayW j (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z := by
    intro j
    have hJ : Measurable (Function.uncurry fun q ρ => ENNReal.ofReal (ρ ^ j) * F q ρ) :=
      ((measurable_snd.pow_const j).ennreal_ofReal).mul hFmeas
    have h2 := hJ.lintegral_prod_right (ν := volume.restrict (Ioi r))
    simp only [hrayEq j]
    exact h2.const_mul _
  have hWj : ∀ j : ℕ, j ≤ 2 → cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
      rayW j (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z) ≤ A * S5 := by
    intro j hj
    rw [cellN_const_mul c ENNReal.ofReal_ne_top]
    simp only [hrayEq j]
    have hmink := cellN_lintegral_le (c := c) (r := r) (F := F)
      (w := fun ρ => ENNReal.ofReal (ρ ^ j)) (b := fun ρ => ENNReal.ofReal ((R / ρ) ^ 5)) (K := A)
      hFmeas (measurable_id.pow_const j).ennreal_ofReal
      ((measurable_const.div measurable_id).pow_const 5).ennreal_ofReal
      (fun _ => ENNReal.ofReal_ne_top)
      (fun ρ hρ => by
        have hρ0 : 0 < ρ := hr0.trans hρ
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (fun _ => ENNReal.ofReal_ne_top)
      (fun ρ hρ => by
        have h := hP5 ρ hρ
        rw [hFdef]
        simpa only [indicator_of_mem (hclear ρ (le_of_lt hρ))] using h)
    have hprod : ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j) * ENNReal.ofReal ((R / ρ) ^ 5) =
        ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) :=
      setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ =>
        (ENNReal.ofReal_mul (pow_nonneg (hr0.trans hρ).le j)).symm
    calc ENNReal.ofReal (r⁻¹ ^ (j + 1)) * cellN c (fun q => ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j) * F q ρ)
        ≤ ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
            (A * ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j) * ENNReal.ofReal ((R / ρ) ^ 5)) := by
          gcongr
      _ = A * (ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
            ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5)) := by rw [hprod]; ring
      _ ≤ A * S5 := by
          gcongr
          exact rayPow_le hj hr0 hR0.le
  have hm0 : AEMeasurable (fun q => ENNReal.ofReal (dPhase Pl K L μ T
      (NearInst.chartTau R (s, (q, η))) (hpt r z))) (cellμ c) :=
    ((hP T s hs η).1.ennreal_ofReal).smul_measure _
  have ht0 : cellN c (fun q => ENNReal.ofReal (dPhase Pl K L μ T
      (NearInst.chartTau R (s, (q, η))) (hpt r z))) ≤ A * S5 := by
    have h := (hP T s hs η).2
    rw [cellL2_eq_cellN, hconv _ (Real.rpow_nonneg hs0.le _), ← hS5] at h
    exact h
  have hPmeas : AEMeasurable (fun q => rayBound (dPhase Pl K L μ T
      (NearInst.chartTau R (s, (q, η)))) r z) (cellμ c) := by
    simp only [rayBound_eq']
    exact ((hm0.add (hmj 0).aemeasurable).add (hmj 1).aemeasurable).add (hmj 2).aemeasurable
  have hPhaseN : cellN c (fun q => rayBound (dPhase Pl K L μ T
      (NearInst.chartTau R (s, (q, η)))) r z) ≤ 4 * (A * S5) := by
    simp only [rayBound_eq']
    calc _ ≤ cellN c (fun q => ENNReal.ofReal (dPhase Pl K L μ T
            (NearInst.chartTau R (s, (q, η))) (hpt r z)) +
            ENNReal.ofReal (r⁻¹ ^ (0 + 1)) *
              rayW 0 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z +
            ENNReal.ofReal (r⁻¹ ^ (1 + 1)) *
              rayW 1 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (2 + 1)) *
              rayW 2 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z) :=
          cellN_add_le ((hm0.add (hmj 0).aemeasurable).add (hmj 1).aemeasurable)
            (hmj 2).aemeasurable
      _ ≤ (cellN c (fun q => ENNReal.ofReal (dPhase Pl K L μ T
            (NearInst.chartTau R (s, (q, η))) (hpt r z)) +
            ENNReal.ofReal (r⁻¹ ^ (0 + 1)) *
              rayW 0 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (1 + 1)) *
              rayW 1 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z)) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (2 + 1)) *
              rayW 2 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z) := by
          gcongr
          exact cellN_add_le (hm0.add (hmj 0).aemeasurable) (hmj 1).aemeasurable
      _ ≤ ((cellN c (fun q => ENNReal.ofReal (dPhase Pl K L μ T
            (NearInst.chartTau R (s, (q, η))) (hpt r z))) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (0 + 1)) *
              rayW 0 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z)) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (1 + 1)) *
              rayW 1 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z)) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (2 + 1)) *
              rayW 2 (dPhase Pl K L μ T (NearInst.chartTau R (s, (q, η)))) r z) := by
          gcongr
          exact cellN_add_le hm0 (hmj 0).aemeasurable
      _ ≤ ((A * S5 + A * S5) + A * S5) + A * S5 := by
          have hW0 := hWj 0 (by norm_num)
          have hW1 := hWj 1 (by norm_num)
          have hW2 := hWj 2 (by norm_num)
          gcongr
      _ = 4 * (A * S5) := by ring
  -- the final estimate
  have hfinal : cellL2 R c (xcmp Pl K L μ T) s η ≤ ENNReal.ofReal C₀ * (8 * (A * S5)) := by
    rw [cellL2_eq_cellN]
    calc cellN c (fun q => ENNReal.ofReal (xcmp Pl K L μ T (NearInst.chartTau R (s, (q, η)))
          (NearInst.chartY R (s, (q, η)))))
        ≤ cellN c (fun q => ENNReal.ofReal C₀ * (rayBound (dPhase Pl K L μ T
            (NearInst.chartTau R (s, (q, η)))) r z + 4 * (A * S5))) := by
          apply cellN_mono
          intro q
          refine (hpoint _).trans ?_
          gcongr
          exact hsplit _
      _ = ENNReal.ofReal C₀ * cellN c (fun q => rayBound (dPhase Pl K L μ T
            (NearInst.chartTau R (s, (q, η)))) r z + 4 * (A * S5)) :=
          cellN_const_mul c ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal C₀ * (cellN c (fun q => rayBound (dPhase Pl K L μ T
            (NearInst.chartTau R (s, (q, η)))) r z) + cellN c (fun _ => 4 * (A * S5))) := by
          gcongr
          exact cellN_add_le hPmeas aemeasurable_const
      _ ≤ ENNReal.ofReal C₀ * (4 * (A * S5) + 4 * (A * S5)) := by
          rw [cellN_const hc0]
          gcongr
      _ = ENNReal.ofReal C₀ * (8 * (A * S5)) := by ring
  refine hfinal.trans (le_of_eq ?_)
  have e : ENNReal.ofReal (8 * C₀ * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) =
      ENNReal.ofReal C₀ * 8 * ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4) *
        ENNReal.ofReal (s ^ (5 / 2 : ℝ)) := by
    rw [show 8 * C₀ * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) =
      C₀ * 8 * (C * L.ν⁻¹ ^ k * L.ε ^ 4) * s ^ (5 / 2 : ℝ) by ring,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ C₀ * 8 * (C * L.ν⁻¹ ^ k * L.ε ^ 4) by positivity),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ C₀ * 8 by positivity), ENNReal.ofReal_mul hC₀,
      ENNReal.ofReal_ofNat]
  rw [e, hS5def, hS5, hAdef]
  ring

end Regime2

/-! ## 4. The sequence -/

/-- **The stream-cut assembly of `GeomX`** from the pieces, the two calculus statements and the
source facts (see the module docstring). -/
theorem geomX_of_leaves (D : SeqData) (hχ : IsStreamCutoff D.K.χy)
    (hν : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1) (hA : StreamCutAlgStmt) (hF : RayFTCStmt)
    (hS : StreamCutEq) (hP : D.PhasePrimitive) (hT : D.TaylorWidth) (hR : D.ZRegular)
    (hZ : D.ZPrimRegular) (hm : D.DPhaseMeas) (hM : D.XcmpCellMeas) : D.GeomX := by
  obtain ⟨C₀, hC₀, hAlg⟩ := hA D.K.χy hχ
  obtain ⟨C₁, k₁, h₁⟩ := hP
  obtain ⟨C₂, k₂, h₂⟩ := hT
  have hC : 0 ≤ max |C₁| |C₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨8 * C₀ * max |C₁| |C₂|, max k₁ k₂, ?_⟩
  filter_upwards [h₁, h₂, hR, hZ, hm, hM, hν] with n hn₁ hn₂ hnR hnZ hnm hnM hν1 z hz
  exact geomXAt_of_leaves D.Pl D.K (D.level n) (D.mu n z) hC₀ hC hAlg hF hS
    (phasePrimitiveAt_mono _ _ _ _ hν1 ((le_abs_self C₁).trans (le_max_left _ _)) hC
      (le_max_left _ _) (hn₁ z hz))
    (taylorWidthAt_mono _ _ _ _ hν1 ((le_abs_self C₂).trans (le_max_right _ _)) hC
      (le_max_right _ _) (hn₂ z hz))
    (hnR z hz) (hnZ z hz) (hnm z hz) (fun T s hs η => hnM z hz T s hs η)

end GeomXAsm

end UnforcedLeray.Short.PartIIIb.Concrete
