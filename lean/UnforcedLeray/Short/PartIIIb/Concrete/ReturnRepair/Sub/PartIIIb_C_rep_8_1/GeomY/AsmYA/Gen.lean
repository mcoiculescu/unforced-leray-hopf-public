import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Tools

/-!
# `PartIII-b:C/rep/8/1/1/2/4/org`: the stream-cut assembly for an abstract field triple

Source `the November 2 reference manuscript`
lines 4178-4186 (outward primitive and stream cutoff `𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z`),
5415-5427 (the geometric comparison in the normalized phase `L²`: one phase primitive, finite
transverse width, heat-to-Newton error), 5427-5432 ("apply the spatial kernel comparison to these
terms separately"), 2666-2668 (the chart).

The stream-cut assembly `GeomXAsm.geomXAt_of_leaves` (`GeomX/Asm/Assembly.lean`) is written for
the fixed triple `zAct, zMid, zMt` of `X₀ = W_μ - W_{μ+1}`.  The same mathematics applies to any
triple of fields `zA` (actual, phase dependent), `zM` (phase-mean chart tensor, finite width) and
`zT` (zero width, Newton): `cellL2_le_of_leaves` below is that assembly with the triple and the
compared quantity `cmp` abstracted (the `GeomX` files are not edited).  It is used for
`Y_A = 𝒞_y W_μ` in `GeomY/AsmYA.lean`.

Hypotheses (all at one level, for every stress `T` of the level):
* `hcmp`: off the axis, `cmp` is `|D𝒞_y zA - D𝒞_y zT|` with `𝒞_y = wardStreamCut ν R χ_y`;
* `hper`: the phase part `|DzA - DzM|` has the phase period `2c/R` (the chart phase period);
* `hP` (phase primitive), `hT` (finite width and heat-to-Newton), `hR` (`C¹` on the clear region,
  decay along outward rays and convergent outward primitives of `zA, zT`), `hm` (joint
  measurability of the phase part on the clear region);
* the calculus statements `StreamCutAlgWith` and `RayFTCStmt` of `GeomX/Asm/Defs.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open GeomXAsm

namespace GeomYAGen

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


theorem dDiff_tri (Z₁ Z₂ Z₃ : ℝ → Space → Space) (τ : ℝ) (x : Space) :
    dDiff Z₁ Z₃ τ x ≤ dDiff Z₁ Z₂ τ x + dDiff Z₂ Z₃ τ x := by
  unfold dDiff
  calc ‖fderiv ℝ (Z₁ τ) x - fderiv ℝ (Z₃ τ) x‖
      = ‖(fderiv ℝ (Z₁ τ) x - fderiv ℝ (Z₂ τ) x) + (fderiv ℝ (Z₂ τ) x - fderiv ℝ (Z₃ τ) x)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _

theorem rayBound_eq' (g : Space → ℝ) (r z : ℝ) :
    rayBound g r z = ENNReal.ofReal (g (hpt r z)) + ENNReal.ofReal (r⁻¹ ^ (0 + 1)) * rayW 0 g r z +
      ENNReal.ofReal (r⁻¹ ^ (1 + 1)) * rayW 1 g r z +
      ENNReal.ofReal (r⁻¹ ^ (2 + 1)) * rayW 2 g r z := by
  rw [zero_add, pow_one]
  rfl


/-! ## 3. One level, abstract triple -/

section Regime

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel}

/-- **The stream-cut assembly for an abstract field triple** (source 4178-4186, 5415-5427): at a
young chart point `(s, η)`, the normalized phase `L²` norm of `cmp T` is at most
`8 C₀ C ν^{-k} ε⁴ s^{5/2} N`.  The proof is that of `GeomXAsm.geomXAt_of_leaves` with
`zAct, zMid, zMt, xcmp` replaced by `zA T, zM T, zT T, cmp T`. -/
theorem cellL2_le_of_leaves {C₀ C : ℝ} {k : ℕ} (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C)
    (zA zM zT : LStr Pl K L → ℝ → Space → Space) (cmp : LStr Pl K L → ℝ → Space → ℝ)
    (hAlg : StreamCutAlgWith K.χy C₀) (hF : RayFTCStmt)
    (hcmp : ∀ (T : LStr Pl K L) (τ : ℝ) (y : Space), 0 < ϱ y →
      cmp T τ y = ‖fderiv ℝ (wardStreamCut L.ν L.ε⁻¹ K.χy (zA T) τ) y -
        fderiv ℝ (wardStreamCut L.ν L.ε⁻¹ K.χy (zT T) τ) y‖)
    (hper : ∀ (T : LStr Pl K L) (τ : ℝ) (y : Space),
      dDiff (zA T) (zM T) (τ + 2 * cOf L.ν / L.ε⁻¹) y = dDiff (zA T) (zM T) τ y)
    (hP : ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
      AEMeasurable (fun q : ℝ => dDiff (zA T) (zM T) (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
          (NearInst.chartY L.ε⁻¹ (s, (q, η))))
        (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
      cellL2 L.ε⁻¹ (cOf L.ν) (dDiff (zA T) (zM T)) s η ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T)
    (hT : ∀ T : LStr Pl K L, ThinAziZero Pl K L T → ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η q : ℝ,
      ENNReal.ofReal (dDiff (zM T) (zT T) (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
          (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T)
    (hR : ∀ (T : LStr Pl K L) (τ : ℝ),
      ∀ Z ∈ ({zA T, zT T} : Set (ℝ → Space → Space)),
        ContDiffOn ℝ 1 (Z τ) (clearSet L.ε L.ν) ∧
        (∀ y ∈ clearSet L.ε L.ν, Tendsto (fun t : ℝ => Z τ (outRay y t)) atTop (𝓝 0)) ∧
        ∀ r z : ℝ, 0 < r → L.ν / (11 / 10) < (L.ε * r) ^ 2 → PrimData Z τ r z)
    (hm : ∀ T : LStr Pl K L, Measurable fun p : ℝ × Space =>
      (clearSet L.ε L.ν).indicator (fun y => dDiff (zA T) (zM T) p.1 y) p.2)
    (T : LStr Pl K L) (hTz : ThinAziZero Pl K L T) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / L.ν))
    (η : ℝ) :
    cellL2 L.ε⁻¹ (cOf L.ν) (cmp T) s η ≤
      ENNReal.ofReal (8 * C₀ * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T := by
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
      ENNReal.ofReal (dDiff (zM T) (zT T) τ (hpt ρ z)) ≤ A * ENNReal.ofReal ((R / ρ) ^ 5) := by
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
  have hP5 : ∀ ρ ∈ Ioi r, cellN c (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
      (NearInst.chartTau R (s, (q, η))) (hpt ρ z))) ≤ A * ENNReal.ofReal ((R / ρ) ^ 5) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hr0.trans hρ
    set s' := (R / ρ) ^ 2 with hs'def
    set η' := z * (R / ρ) with hη'def
    set a := R / 2 * (Real.log s - Real.log s') with hadef
    set G : ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
      (NearInst.chartTau R (s', (q, η'))) (NearInst.chartY R (s', (q, η')))) with hGdef
    have hG : ∀ q, ENNReal.ofReal (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))
        (hpt ρ z)) = G (q + a) := by
      intro q
      have htau : NearInst.chartTau R (s', (q + a, η')) = NearInst.chartTau R (s, (q, η)) := by
        unfold NearInst.chartTau
        rw [hadef]
        field_simp
        ring
      have hy : NearInst.chartY R (s', (q + a, η')) = hpt ρ z := chartY_ray hR0 hρ0 _ _
      show _ = ENNReal.ofReal (dDiff (zA T) (zM T) (NearInst.chartTau R (s', (q + a, η')))
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
      simp only [hGdef, htau, hy]
      exact congrArg ENNReal.ofReal (hper T _ _)
    calc cellN c (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
          (NearInst.chartTau R (s, (q, η))) (hpt ρ z)))
        = cellN c (fun q => G (q + a)) := by simp only [hG]
      _ = cellN c G := cellN_shift hc0 hGper a
      _ = cellL2 R c (dDiff (zA T) (zM T)) s' η' := (cellL2_eq_cellN R c _ s' η').symm
      _ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s' ^ (5 / 2 : ℝ))) * N :=
          (hP T s' (hs'ν ρ hρ.le) η').2
      _ = A * ENNReal.ofReal ((R / ρ) ^ 5) := by
          rw [hconv _ (Real.rpow_nonneg (by positivity) _), hs'def, hS5ρ ρ hρ0]
  -- the pointwise bound at every phase
  have hmemA : zA T ∈ ({zA T, zT T} : Set (ℝ → Space → Space)) := by simp
  have hmemT : zT T ∈ ({zA T, zT T} : Set (ℝ → Space → Space)) := by simp
  have hdiff : ∀ τ : ℝ, ∀ Z ∈ ({zA T, zT T} : Set (ℝ → Space → Space)), ∀ ρ : ℝ, r ≤ ρ →
      DifferentiableAt ℝ (Z τ) (hpt ρ z) := by
    intro τ Z hZm ρ hρ
    exact (((hR T τ Z hZm).1).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_clearSet _ _).mem_nhds (hclear ρ hρ))
  have hpoint : ∀ τ : ℝ, ENNReal.ofReal (cmp T τ (hpt r z)) ≤
      ENNReal.ofReal C₀ * rayBound (dDiff (zA T) (zT T) τ) r z := by
    intro τ
    have hyc : hpt r z ∈ clearSet L.ε L.ν := hclear r le_rfl
    have hϱ : 0 < ϱ (hpt r z) := hyc.1
    have hxe := hcmp T τ (hpt r z) hϱ
    have hPA := (hR T τ (zA T) hmemA).2.2 r z hr0 (hclear0 r le_rfl)
    have hPT := (hR T τ (zT T) hmemT).2.2 r z hr0 (hclear0 r le_rfl)
    have hyoung : L.ν * (R ^ 2 / r ^ 2) ≤ 1 := by rw [hRr2]; exact hsν
    have h1 := hAlg L.ν R r z τ (zA T) (zT T) hν0 hR0 hr0 hyoung
      (hdiff τ _ hmemA r le_rfl) (hdiff τ _ hmemT r le_rfl) hPA hPT
    have hlim : Tendsto (fun t : ℝ => zA T τ (hpt t z) - zT T τ (hpt t z))
        atTop (𝓝 0) := by
      have l1 := (hR T τ (zA T) hmemA).2.1 (hpt r z) hyc
      have l2 := (hR T τ (zT T) hmemT).2.1 (hpt r z) hyc
      simp only [outRay_hpt hr0] at l1 l2
      simpa using l1.sub l2
    obtain ⟨hv, hΨ, hD⟩ := hF r z τ (zA T) (zT T) hr0
      (fun ρ hρ => ⟨hdiff τ _ hmemA ρ hρ, hdiff τ _ hmemT ρ hρ⟩) hlim hPA hPT
    rw [hxe]
    exact (ENNReal.ofReal_le_ofReal h1).trans (ofReal_combo hC₀ hv hΨ hD hr0)
  -- the width part is bounded pointwise
  have hsplit : ∀ τ : ℝ, rayBound (dDiff (zA T) (zT T) τ) r z ≤
      rayBound (dDiff (zA T) (zM T) τ) r z + 4 * (A * S5) := by
    intro τ
    have hterm0 : ENNReal.ofReal (dDiff (zA T) (zT T) τ (hpt r z)) ≤
        ENNReal.ofReal (dDiff (zA T) (zM T) τ (hpt r z)) + A * S5 := by
      calc ENNReal.ofReal (dDiff (zA T) (zT T) τ (hpt r z))
          ≤ ENNReal.ofReal (dDiff (zA T) (zM T) τ (hpt r z) + dDiff (zM T) (zT T) τ (hpt r z)) :=
            ENNReal.ofReal_le_ofReal (dDiff_tri (zA T) (zM T) (zT T) τ _)
        _ ≤ ENNReal.ofReal (dDiff (zA T) (zM T) τ (hpt r z)) +
            ENNReal.ofReal (dDiff (zM T) (zT T) τ (hpt r z)) := ENNReal.ofReal_add_le
        _ ≤ _ := by gcongr; exact hW5 τ r le_rfl
    have htermj : ∀ j : ℕ, j ≤ 2 →
        ENNReal.ofReal (r⁻¹ ^ (j + 1)) * rayW j (dDiff (zA T) (zT T) τ) r z ≤
          ENNReal.ofReal (r⁻¹ ^ (j + 1)) * rayW j (dDiff (zA T) (zM T) τ) r z + A * S5 := by
      intro j hj
      have hmeas5 : Measurable fun ρ : ℝ => ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) :=
        ((measurable_id.pow_const j).mul
          ((measurable_const.div measurable_id).pow_const 5)).ennreal_ofReal
      have hle : rayW j (dDiff (zA T) (zT T) τ) r z ≤
          rayW j (dDiff (zA T) (zM T) τ) r z +
            A * ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) := by
        unfold rayW
        rw [← lintegral_const_mul _ hmeas5, ← lintegral_add_right _ (hmeas5.const_mul A)]
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ0 : 0 < ρ := hr0.trans hρ
        have hpj : 0 ≤ ρ ^ j := pow_nonneg hρ0.le j
        calc ENNReal.ofReal (ρ ^ j * dDiff (zA T) (zT T) τ (hpt ρ z))
            ≤ ENNReal.ofReal (ρ ^ j * dDiff (zA T) (zM T) τ (hpt ρ z) +
                ρ ^ j * dDiff (zM T) (zT T) τ (hpt ρ z)) := by
              apply ENNReal.ofReal_le_ofReal
              rw [← mul_add]
              exact mul_le_mul_of_nonneg_left (dDiff_tri (zA T) (zM T) (zT T) τ _) hpj
          _ ≤ ENNReal.ofReal (ρ ^ j * dDiff (zA T) (zM T) τ (hpt ρ z)) +
                ENNReal.ofReal (ρ ^ j) * ENNReal.ofReal (dDiff (zM T) (zT T) τ (hpt ρ z)) := by
              refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
              congr 1
              exact ENNReal.ofReal_mul hpj
          _ ≤ ENNReal.ofReal (ρ ^ j * dDiff (zA T) (zM T) τ (hpt ρ z)) +
                ENNReal.ofReal (ρ ^ j) * (A * ENNReal.ofReal ((R / ρ) ^ 5)) := by
              gcongr
              exact hW5 τ ρ hρ.le
          _ = ENNReal.ofReal (ρ ^ j * dDiff (zA T) (zM T) τ (hpt ρ z)) +
                A * ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) := by
              congr 1
              rw [ENNReal.ofReal_mul hpj]
              ring
      calc ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
            rayW j (dDiff (zA T) (zT T) τ) r z
          ≤ ENNReal.ofReal (r⁻¹ ^ (j + 1)) * (rayW j (dDiff (zA T) (zM T) τ) r z +
              A * ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5)) := by gcongr
        _ = ENNReal.ofReal (r⁻¹ ^ (j + 1)) * rayW j (dDiff (zA T) (zM T) τ) r z +
              A * (ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
                ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5)) := by ring
        _ ≤ _ := by
            gcongr
            exact rayPow_le hj hr0 hR0.le
    have h0 := htermj 0 (by norm_num)
    have h1 := htermj 1 (by norm_num)
    have h2 := htermj 2 (by norm_num)
    rw [rayBound_eq', rayBound_eq']
    calc _ ≤ (ENNReal.ofReal (dDiff (zA T) (zM T) τ (hpt r z)) + A * S5) +
          (ENNReal.ofReal (r⁻¹ ^ (0 + 1)) * rayW 0 (dDiff (zA T) (zM T) τ) r z + A * S5) +
          (ENNReal.ofReal (r⁻¹ ^ (1 + 1)) * rayW 1 (dDiff (zA T) (zM T) τ) r z + A * S5) +
          (ENNReal.ofReal (r⁻¹ ^ (2 + 1)) * rayW 2 (dDiff (zA T) (zM T) τ) r z + A * S5) := by
          gcongr
      _ = _ := by ring
  -- the phase part: cell norm of each term
  set F : ℝ → ℝ → ℝ≥0∞ := fun q ρ => ENNReal.ofReal ((clearSet L.ε L.ν).indicator
    (fun y => dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η))) y) (hpt ρ z)) with hFdef
  have hFmeas : Measurable (Function.uncurry F) := by
    have hmap : Measurable fun p : ℝ × ℝ => (NearInst.chartTau R (s, (p.1, η)), hpt p.2 z) :=
      ((continuous_chartTau_q R s η).measurable.comp measurable_fst).prodMk
        ((continuous_hpt z).measurable.comp measurable_snd)
    exact ((hm T).comp hmap).ennreal_ofReal
  have hrayEq : ∀ j : ℕ, ∀ q : ℝ,
      rayW j (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z =
        ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j) * F q ρ := by
    intro j q
    unfold rayW
    refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    rw [hFdef]
    dsimp only
    rw [indicator_of_mem (hclear ρ (le_of_lt hρ)), ENNReal.ofReal_mul (pow_nonneg (hr0.trans hρ).le j)]
  have hmj : ∀ j : ℕ, Measurable fun q => ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
      rayW j (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z := by
    intro j
    have hJ : Measurable (Function.uncurry fun q ρ => ENNReal.ofReal (ρ ^ j) * F q ρ) :=
      ((measurable_snd.pow_const j).ennreal_ofReal).mul hFmeas
    have h2 := hJ.lintegral_prod_right (ν := volume.restrict (Ioi r))
    simp only [hrayEq j]
    exact h2.const_mul _
  have hWj : ∀ j : ℕ, j ≤ 2 → cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (j + 1)) *
      rayW j (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z) ≤ A * S5 := by
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
  have hm0 : AEMeasurable (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
      (NearInst.chartTau R (s, (q, η))) (hpt r z))) (cellμ c) :=
    ((hP T s hs η).1.ennreal_ofReal).smul_measure _
  have ht0 : cellN c (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
      (NearInst.chartTau R (s, (q, η))) (hpt r z))) ≤ A * S5 := by
    have h := (hP T s hs η).2
    rw [cellL2_eq_cellN, hconv _ (Real.rpow_nonneg hs0.le _), ← hS5] at h
    exact h
  have hPmeas : AEMeasurable (fun q => rayBound (dDiff (zA T) (zM T)
      (NearInst.chartTau R (s, (q, η)))) r z) (cellμ c) := by
    simp only [rayBound_eq']
    exact ((hm0.add (hmj 0).aemeasurable).add (hmj 1).aemeasurable).add (hmj 2).aemeasurable
  have hPhaseN : cellN c (fun q => rayBound (dDiff (zA T) (zM T)
      (NearInst.chartTau R (s, (q, η)))) r z) ≤ 4 * (A * S5) := by
    simp only [rayBound_eq']
    calc _ ≤ cellN c (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
            (NearInst.chartTau R (s, (q, η))) (hpt r z)) +
            ENNReal.ofReal (r⁻¹ ^ (0 + 1)) *
              rayW 0 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z +
            ENNReal.ofReal (r⁻¹ ^ (1 + 1)) *
              rayW 1 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (2 + 1)) *
              rayW 2 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z) :=
          cellN_add_le ((hm0.add (hmj 0).aemeasurable).add (hmj 1).aemeasurable)
            (hmj 2).aemeasurable
      _ ≤ (cellN c (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
            (NearInst.chartTau R (s, (q, η))) (hpt r z)) +
            ENNReal.ofReal (r⁻¹ ^ (0 + 1)) *
              rayW 0 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (1 + 1)) *
              rayW 1 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z)) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (2 + 1)) *
              rayW 2 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z) := by
          gcongr
          exact cellN_add_le (hm0.add (hmj 0).aemeasurable) (hmj 1).aemeasurable
      _ ≤ ((cellN c (fun q => ENNReal.ofReal (dDiff (zA T) (zM T)
            (NearInst.chartTau R (s, (q, η))) (hpt r z))) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (0 + 1)) *
              rayW 0 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z)) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (1 + 1)) *
              rayW 1 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z)) +
          cellN c (fun q => ENNReal.ofReal (r⁻¹ ^ (2 + 1)) *
              rayW 2 (dDiff (zA T) (zM T) (NearInst.chartTau R (s, (q, η)))) r z) := by
          gcongr
          exact cellN_add_le hm0 (hmj 0).aemeasurable
      _ ≤ ((A * S5 + A * S5) + A * S5) + A * S5 := by
          have hW0 := hWj 0 (by norm_num)
          have hW1 := hWj 1 (by norm_num)
          have hW2 := hWj 2 (by norm_num)
          gcongr
      _ = 4 * (A * S5) := by ring
  -- the final estimate
  have hfinal : cellL2 R c (cmp T) s η ≤ ENNReal.ofReal C₀ * (8 * (A * S5)) := by
    rw [cellL2_eq_cellN]
    calc cellN c (fun q => ENNReal.ofReal (cmp T (NearInst.chartTau R (s, (q, η)))
          (NearInst.chartY R (s, (q, η)))))
        ≤ cellN c (fun q => ENNReal.ofReal C₀ * (rayBound (dDiff (zA T) (zM T)
            (NearInst.chartTau R (s, (q, η)))) r z + 4 * (A * S5))) := by
          apply cellN_mono
          intro q
          refine (hpoint _).trans ?_
          gcongr
          exact hsplit _
      _ = ENNReal.ofReal C₀ * cellN c (fun q => rayBound (dDiff (zA T) (zM T)
            (NearInst.chartTau R (s, (q, η)))) r z + 4 * (A * S5)) :=
          cellN_const_mul c ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal C₀ * (cellN c (fun q => rayBound (dDiff (zA T) (zM T)
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

end Regime

end GeomYAGen

end UnforcedLeray.Short.PartIIIb.Concrete
