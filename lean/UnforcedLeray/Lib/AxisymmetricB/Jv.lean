import UnforcedLeray.Lib.AxisymmetricB.DSS
import Mathlib.MeasureTheory.Function.Floor

/-!
# AX04 (isometry): `J_v = (√π R)⁻¹ N_v` as a linear isometry into the phase-averaged `L²`


§5 Layer 3, target AX04 (`Jv`); Wave 2 block 2J AXI1 of `scoping/README.md`. Blueprint units
served: B0219 (`eq:m3-cylinder-measure`, tex 3256–3268: `‖N_v b‖_{Y_q} = (πR²)^{1/q} ‖b‖_{H_q}`),
B0228 (tex 3684–3718), B0417 (`eq:m4-free-spaces`, tex 7272–7297: `J_v = (√π R)⁻¹ N_v`
unitary onto the axisymmetric no-swirl subspace of the period-averaged `Y₂`), B0482
(tex 7920–7949), B0550 (tex 8724–8732).

* `cellRep c ξ ∈ [−c/2, c/2)`, `perExt c b`: the `c`-periodic extension in `ξ` of a profile
  given on the centred cell (an `L²(ageμ)` class only knows the cell).
* `phaseμ P = P⁻¹ dτ|_{(0,P]} ⊗ dy`: the period-averaged measure. For a `P`-periodic field
  (`Nv_dss`) integration against `phaseμ P` is the normalized Haar average over `ℝ/Pℤ`, the
  time measure of `Y_q` (decision D2).
* `lintegral_phaseμ_Nv`, `eLpNorm_Nv` (tex 3260: `‖N_v b‖_{Y_q} = (πR²)^{1/q} ‖b‖_{H_q}`).
* `Jv hR hc hP : L²(ageμ c (−3/2); ℝ²) →ₗᵢ[ℝ] L²(phaseμ P; ℝ³)`, `J_v b = (√π R)⁻¹ N_v b`
  (tex 7276–7280), with `coeFn_Jv`.

Not built here (recorded as missing): the bridge from the joint `L²(phaseμ P)` to D2's Bochner
space `Y₂ = L²(ℝ/Pℤ; L²(ℝ³; ℂ³))` (it needs the slice map `BochnerTime.toPathLq` and the
complexification), the range characterization `range_Jv` (every 𝒪-invariant element of `Y₂`
is a lift: rotation averaging of vector fields with the reflection argument, risk 4 of the note)
and the resulting unitary `JvEquiv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

/-! ### The periodic extension from the centred cell -/

/-- The representative of `ξ` in the centred cell `[−c/2, c/2)`. -/
def cellRep (c ξ : ℝ) : ℝ := ξ - c * ⌊(ξ + c / 2) / c⌋

theorem cellRep_add {c : ℝ} (hc : c ≠ 0) (ξ : ℝ) : cellRep c (ξ + c) = cellRep c ξ := by
  unfold cellRep
  have h : (ξ + c + c / 2) / c = (ξ + c / 2) / c + 1 := by field_simp; ring
  rw [h, Int.floor_add_one]
  push_cast
  ring

theorem cellRep_of_mem {c ξ : ℝ} (hc : 0 < c) (hξ : ξ ∈ Ico (-c / 2) (c / 2)) :
    cellRep c ξ = ξ := by
  unfold cellRep
  have h : ⌊(ξ + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    refine ⟨div_nonneg (by linarith [hξ.1]) hc.le, ?_⟩
    rw [div_lt_one hc]
    linarith [hξ.2]
  rw [h]
  simp

theorem measurable_cellRep (c : ℝ) : Measurable (cellRep c) := by
  have hfl : Measurable fun ξ : ℝ => ((⌊(ξ + c / 2) / c⌋ : ℤ) : ℝ) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_floor.comp ((measurable_id.add_const _).div_const _))
  exact measurable_id.sub (measurable_const.mul hfl)

/-- The `c`-periodic extension in `ξ` of a profile given on the centred cell. -/
def perExt (c : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (p : ℝ × (ℝ × ℝ)) : Merid :=
  b (p.1, (cellRep c p.2.1, p.2.2))

theorem perExt_periodic {c : ℝ} (hc : c ≠ 0) (b : ℝ × (ℝ × ℝ) → Merid) (s ξ η : ℝ) :
    perExt c b (s, (ξ + c, η)) = perExt c b (s, (ξ, η)) := by
  simp only [perExt, cellRep_add hc]

theorem measurable_perExt (c : ℝ) {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b) :
    Measurable (perExt c b) :=
  hb.comp (measurable_fst.prodMk (((measurable_cellRep c).comp (measurable_fst.comp
    measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))

theorem perExt_eq_of_mem {c : ℝ} (hc : 0 < c) (b : ℝ × (ℝ × ℝ) → Merid) {p : ℝ × (ℝ × ℝ)}
    (hp : p.2 ∈ qCell c) : perExt c b p = b p := by
  simp only [perExt, cellRep_of_mem hc hp.1]

theorem measurableSet_halfCell (c : ℝ) : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell c) :=
  measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)

/-- `ageμ c a` lives on `(0, ∞) × cell`. -/
theorem ae_ageμ_mem {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∀ᵐ p ∂ageμ c a, p ∈ Ioi (0 : ℝ) ×ˢ qCell c := by
  have hS := measurableSet_halfCell c
  rw [ae_iff]
  have h := lintegral_ageμ hc a (f := (Ioi (0 : ℝ) ×ˢ qCell c)ᶜ.indicator 1)
    (measurable_one.indicator hS.compl)
  rw [lintegral_indicator_one hS.compl] at h
  rw [show {p | ¬p ∈ Ioi (0 : ℝ) ×ˢ qCell c} = (Ioi (0 : ℝ) ×ˢ qCell c)ᶜ from rfl, h,
    setLIntegral_congr_fun hS (g := fun _ => 0) (fun p hp => by simp [hp])]
  simp

theorem perExt_ae_eq {c : ℝ} (hc : 0 < c) (a : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) :
    perExt c b =ᵐ[ageμ c a] b := by
  filter_upwards [ae_ageμ_mem hc a] with p hp
  exact perExt_eq_of_mem hc b hp.2

/-! ### The period-averaged measure -/

/-- The period-averaged phase measure `P⁻¹ dτ|_{(0,P]} ⊗ dy` on `ℝ × ℝ³`. -/
def phaseμ (P : ℝ) : Measure (ℝ × Space) :=
  ((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P)).prod volume

theorem lintegral_phaseμ (P : ℝ) {F : ℝ × Space → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂phaseμ P = (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, F (τ, y) := by
  rw [phaseμ, Measure.prod_smul_left, lintegral_smul_measure, lintegral_prod _ hF.aemeasurable,
    smul_eq_mul]

theorem measurable_eR : Measurable eR :=
  measurable_ϱ.inv.smul (contDiff_hor (k := 0)).continuous.measurable

theorem measurable_Nv (R : ℝ) {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b) :
    Measurable fun x : ℝ × Space => Nv R b x.1 x.2 := by
  have hch : Measurable fun x : ℝ × Space => chart R x.1 x.2 :=
    ((measurable_age R).comp measurable_snd).prodMk
      ((measurable_phase R).prodMk ((measurable_trans R).comp measurable_snd))
  have hbm := hb.comp hch
  have h0 : Measurable fun x : ℝ × Space => b (chart R x.1 x.2) 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).continuous.measurable.comp hbm
  have h1 : Measurable fun x : ℝ × Space => b (chart R x.1 x.2) 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).continuous.measurable.comp hbm
  have hs : Measurable fun x : ℝ × Space => √(age R x.2) :=
    Real.continuous_sqrt.measurable.comp ((measurable_age R).comp measurable_snd)
  simp only [Nv, frameL_apply]
  exact hs.smul ((h0.smul (measurable_eR.comp measurable_snd)).add (h1.smul measurable_const))

/-- **AX04, joint form of `lintegral_Nv_rpow`** (B0219, tex 3260). -/
theorem lintegral_phaseμ_Nv {R c P q : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (hq : 0 < q) {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b)
    (hper : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) :
    ∫⁻ x, ‖Nv R b x.1 x.2‖ₑ ^ q ∂phaseμ P =
      ENNReal.ofReal (π * R ^ 2) * ∫⁻ p, ‖b p‖ₑ ^ q ∂ageμ c (q / 2 - 5 / 2) := by
  rw [lintegral_phaseμ P ((measurable_Nv R hb).enorm.pow_const q)]
  exact lintegral_Nv_rpow hR hc hP hq hb hper

/-- **AX04 norm identity** (B0219, tex 3260; B0228, tex 3704: `‖U_b‖_{Y_r} = (πR²)^{1/r}
‖b‖_{H_r}`). For `q > 0` and a measurable profile `c`-periodic in `ξ`,
`‖N_v b‖_{L^q(phaseμ P)} = (πR²)^{1/q} ‖b‖_{L^q(ageμ c (q/2 − 5/2))}`. -/
theorem eLpNorm_Nv {R c P q : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) (hq : 0 < q)
    {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b)
    (hper : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) :
    eLpNorm (fun x : ℝ × Space => Nv R b x.1 x.2) (ENNReal.ofReal q) (phaseμ P) =
      ENNReal.ofReal (π * R ^ 2) ^ (1 / q) *
        eLpNorm b (ENNReal.ofReal q) (ageμ c (q / 2 - 5 / 2)) := by
  have h0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le,
    lintegral_phaseμ_Nv hR hc hP hq hb hper, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

/-! ### The isometry `J_v` -/

/-- The lift `(√π R)⁻¹ N_v (perExt c b)` of a cell profile. -/
def liftFun (R c : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × Space) : Space :=
  (√π * R)⁻¹ • Nv R (perExt c b) x.1 x.2

theorem measurable_liftFun (R c : ℝ) {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b) :
    Measurable (liftFun R c b) := by
  unfold liftFun
  exact (measurable_const (a := (√π * R)⁻¹)).smul (measurable_Nv R (measurable_perExt c hb))

theorem liftFun_add (R c : ℝ) (b b' : ℝ × (ℝ × ℝ) → Merid) :
    liftFun R c (b + b') = liftFun R c b + liftFun R c b' := by
  funext x
  have e : perExt c (b + b') = perExt c b + perExt c b' := rfl
  simp only [liftFun, Pi.add_apply, e, Nv_add, smul_add]

theorem liftFun_sub (R c : ℝ) (b b' : ℝ × (ℝ × ℝ) → Merid) :
    liftFun R c (b - b') = liftFun R c b - liftFun R c b' := by
  funext x
  have e : perExt c (b - b') = perExt c b - perExt c b' := rfl
  simp only [liftFun, Pi.sub_apply, e, Nv_sub, smul_sub]

theorem liftFun_smul (R c k : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) :
    liftFun R c (k • b) = k • liftFun R c b := by
  funext x
  have e : perExt c (k • b) = k • perExt c b := rfl
  simp only [liftFun, Pi.smul_apply, e, Nv_smul, smul_comm (√π * R)⁻¹ k]

/-- `‖J_v b‖_{L²(phaseμ P)} = ‖b‖_{L²(ageμ c (−3/2))}` (tex 7276–7280). -/
theorem eLpNorm_liftFun {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b) :
    eLpNorm (liftFun R c b) 2 (phaseμ P) = eLpNorm b 2 (ageμ c (-3 / 2)) := by
  have h2 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := ENNReal.ofReal_ofNat 2
  have hN := eLpNorm_Nv hR hc hP two_pos (measurable_perExt c hb)
    (perExt_periodic hc.ne' b)
  rw [h2, show (2 : ℝ) / 2 - 5 / 2 = -3 / 2 by norm_num,
    eLpNorm_congr_ae (perExt_ae_eq hc (-3 / 2) b)] at hN
  have hl : liftFun R c b = (√π * R)⁻¹ • fun x : ℝ × Space => Nv R (perExt c b) x.1 x.2 := rfl
  have hpos : 0 < √π * R := mul_pos (Real.sqrt_pos.2 Real.pi_pos) hR
  rw [hl, eLpNorm_const_smul, hN, ← mul_assoc]
  have hconst : ‖(√π * R)⁻¹‖ₑ * ENNReal.ofReal (π * R ^ 2) ^ (1 / (2 : ℝ)) = 1 := by
    rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← ENNReal.ofReal_mul
        (inv_nonneg.2 hpos.le)]
    have e : (π * R ^ 2) ^ (1 / (2 : ℝ)) = √π * R := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
    rw [e, inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
  rw [hconst, one_mul]

theorem memLp_liftFun {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Lp Merid 2 (ageμ c (-3 / 2))) : MemLp (liftFun R c b) 2 (phaseμ P) :=
  ⟨(measurable_liftFun R c (Lp.stronglyMeasurable b).measurable).aestronglyMeasurable, by
    rw [eLpNorm_liftFun hR hc hP (Lp.stronglyMeasurable b).measurable]
    exact Lp.eLpNorm_lt_top b⟩

theorem liftFun_congr_ae {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {b b' : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b) (hb' : Measurable b')
    (h : b =ᵐ[ageμ c (-3 / 2)] b') : liftFun R c b =ᵐ[phaseμ P] liftFun R c b' := by
  have hd : eLpNorm (liftFun R c b - liftFun R c b') 2 (phaseμ P) = 0 := by
    rw [← liftFun_sub, eLpNorm_liftFun hR hc hP (hb.sub hb')]
    have hz : b - b' =ᵐ[ageμ c (-3 / 2)] 0 := by
      filter_upwards [h] with p hp
      simp [hp]
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
  have hm : AEStronglyMeasurable (liftFun R c b - liftFun R c b') (phaseμ P) :=
    ((measurable_liftFun R c hb).sub (measurable_liftFun R c hb')).aestronglyMeasurable
  have hz := (eLpNorm_eq_zero_iff hm two_ne_zero).1 hd
  filter_upwards [hz] with x hx
  exact sub_eq_zero.1 hx

/-- **AX04 `Jv`** (B0417, tex 7276–7280: `J_v = (√π R)⁻¹ N_v`; B0482; B0550). The ring lift is a
linear isometry from `H = L²(ageμ c (−3/2); ℝ²)` into the period-averaged
`L²(phaseμ P; ℝ³)`, `P = 2c/R`. -/
def Jv {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    Lp Merid 2 (ageμ c (-3 / 2)) →ₗᵢ[ℝ] Lp Space 2 (phaseμ P) where
  toFun b := (memLp_liftFun hR hc hP b).toLp (liftFun R c b)
  map_add' b b' := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    rw [← liftFun_add]
    exact liftFun_congr_ae hR hc hP (Lp.stronglyMeasurable _).measurable
      ((Lp.stronglyMeasurable b).measurable.add (Lp.stronglyMeasurable b').measurable)
      (Lp.coeFn_add b b')
  map_smul' k b := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    rw [← liftFun_smul]
    exact liftFun_congr_ae hR hc hP (Lp.stronglyMeasurable _).measurable
      ((Lp.stronglyMeasurable b).measurable.const_smul k) (Lp.coeFn_smul k b)
  norm_map' b := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      eLpNorm_liftFun hR hc hP (Lp.stronglyMeasurable b).measurable, Lp.norm_def]

/-- The representative of `J_v b`: `(√π R)⁻¹ N_v b` on one period. -/
theorem coeFn_Jv {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Lp Merid 2 (ageμ c (-3 / 2))) :
    ⇑(Jv hR hc hP b) =ᵐ[phaseμ P] fun x => (√π * R)⁻¹ • Nv R (perExt c b) x.1 x.2 :=
  MemLp.coeFn_toLp (memLp_liftFun hR hc hP b)

end UnforcedLeray.Axi
