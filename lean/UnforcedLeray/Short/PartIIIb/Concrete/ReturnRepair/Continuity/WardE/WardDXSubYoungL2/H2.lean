import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDXSubYoungL2.H1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3.H2

/-!
# Helpers for `wardDXSubYoungL2_proved` (2): outward primitive and stream-correction `μ`-differences
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Order-`0` `μ`-Lipschitz domination without the finiteness hypothesis (`C0 + 1 > 0`). -/
theorem sepWSubDom_zero (hSub : SepWSubDom) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν μ μ' rOut rIn P : ℝ),
      0 < ν → 0 ≤ μ → 0 ≤ μ' → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T →
      ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
        ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y -
            iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ' : ℂ) T y' τ) y‖ₑ ≤
          ENNReal.ofReal (C0 * |μ - μ'|) *
            IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y := by
  obtain ⟨C0, hC0, hSub0⟩ := hSub 0
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy
  by_cases hmu : μ = μ'
  · subst hmu; simp
  by_cases hfin : IIIa.sepDom (2 * (-1 / 8 : ℝ) + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤
  · refine (hSub0 ν μ μ' rOut rIn P hν hμ hμ' hrO hrr hP T hT τ y hy hfin).trans ?_
    gcongr
    linarith
  · have hpos : 0 < (C0 + 1) * |μ - μ'| := mul_pos (by linarith) (abs_pos.2 (sub_ne_zero.2 hmu))
    rw [not_lt_top_iff.1 hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top

theorem norm_iteratedFDeriv_zero_sub' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} (y : E) :
    ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 g y‖ = ‖f y - g y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply, ← map_sub]
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.norm_map _

theorem w2_enorm_sepWre_sub {ν : ℝ} (m m' : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) :
    ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ₑ ≤
      ENNReal.ofReal ‖w10Re‖ *
        ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
          iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ := by
  have e : ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y -
      iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m' : ℂ) T y' τ) y‖ₑ =
      ENNReal.ofReal ‖IIIa.sepW ν (m : ℂ) T y τ - IIIa.sepW ν (m' : ℂ) T y τ‖ := by
    rw [← ofReal_norm, norm_iteratedFDeriv_zero_sub']
  have h0 : ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ ≤
      ‖w10Re‖ * ‖IIIa.sepW ν (m : ℂ) T y τ - IIIa.sepW ν (m' : ℂ) T y τ‖ := by
    rw [w10_sepWre_eq, w10_sepWre_eq, Function.comp_apply, Function.comp_apply, ← map_sub]
    exact w10Re.le_opNorm _
  rw [e, ← ofReal_norm (sepWre ν m T τ y - sepWre ν m' T τ y), ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h0

/-- Integrability of `ρ ↦ ρ * sepWre ν μ T τ (ρ, 0, z)_z` on `(r, ∞)` for `r > rOut`. -/
theorem sepWre_outPrim_integrable {ν μ rOut P : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ z : ℝ) {r : ℝ} (hrr : rOut < r) :
    IntegrableOn (fun ρ : ℝ => ρ * sepWre ν μ T τ (!₂[ρ, 0, z] : Space) 2) (Ioi r) := by
  obtain ⟨C, hC0, hb⟩ := tcd_X0_bound hν hμ hr0 hP hT hM
  have hD1 : 0 < r - rOut := by linarith
  set κ : ℝ := r / (r - rOut)
  have hrpos : 0 < r := lt_of_le_of_lt hr0 hrr
  have hκ0 : 0 ≤ κ := by positivity
  have hint : IntegrableOn (fun ρ : ℝ => κ * C * (ρ - rOut) ^ (-(3 / 2 : ℝ))) (Ioi r) :=
    (tcd_int_shift rOut r hD1).const_mul _
  have hW := tcd_Wre_cd hν hμ hr0 hP hT hM τ
  have hsub : Ioi r ⊆ Ioi rOut := Ioi_subset_Ioi hrr.le
  have hcont : ContinuousOn (fun ρ : ℝ => ρ * sepWre ν μ T τ (!₂[ρ, 0, z] : Space) 2) (Ioi r) :=
    continuousOn_id.mul ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn
      ((tcd_cont_val hr0 hW z).mono hsub))
  refine Integrable.mono' hint (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
  have hρr : r ≤ ρ := le_of_lt hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le hrpos hρr
  set p : Space := (!₂[ρ, 0, z] : Space)
  have hϱ : ϱ p = ρ := tcd_varrho hρ0.le
  have hy : rOut < ϱ p := by rw [hϱ]; linarith
  set D : ℝ := ρ - rOut
  have hDp : 0 < D := by show 0 < ρ - rOut; linarith
  set w : ℝ := D⁻¹
  have hwp : 0 < w := inv_pos.2 hDp
  have hDw : D * w = 1 := mul_inv_cancel₀ hDp.ne'
  have hρκ : ρ ≤ κ * D := by
    show ρ ≤ r / (r - rOut) * (ρ - rOut)
    rw [div_mul_eq_mul_div, le_div_iff₀ hD1]
    nlinarith
  set u : ℝ := D ^ (-(3 / 2 : ℝ))
  have hu0 : 0 ≤ u := Real.rpow_nonneg hDp.le _
  have hWbd := (hb τ p hy).2
  rw [hϱ] at hWbd
  have sp0 := tcd_rpow_split D hDp 0
  simp only [Nat.cast_zero, sub_zero] at sp0
  have a3 : ‖IIIa.sepW ν (μ : ℂ) T p τ‖ ≤ C * (u * w ^ 1) := by
    simpa [u, w, D, sp0] using hWbd
  have hcomp : |sepWre ν μ T τ p 2| ≤ ‖IIIa.sepW ν (μ : ℂ) T p τ‖ := by
    have h1 : |sepWre ν μ T τ p 2| ≤ ‖IIIa.sepW ν (μ : ℂ) T p τ 2‖ := by
      simpa [sepWre] using Complex.abs_re_le_norm (IIIa.sepW ν (μ : ℂ) T p τ 2)
    exact h1.trans (norm_le_pi_norm (IIIa.sepW ν (μ : ℂ) T p τ) 2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
  calc ρ * |sepWre ν μ T τ p 2| ≤ ρ * (C * (u * w ^ 1)) :=
        mul_le_mul_of_nonneg_left (hcomp.trans a3) hρ0.le
    _ ≤ κ * C * u * w ^ 0 := tcd_alg1 hDw hρκ hC0 hu0 hwp.le 0
    _ = κ * C * u := by ring

theorem outPrim_sub_eq {Z₁ Z₂ : ℝ → Space → Space} {τ r z : ℝ}
    (h1 : IntegrableOn (fun ρ : ℝ => ρ * Z₁ τ (!₂[ρ, 0, z] : Space) 2) (Ioi r))
    (h2 : IntegrableOn (fun ρ : ℝ => ρ * Z₂ τ (!₂[ρ, 0, z] : Space) 2) (Ioi r)) :
    outPrim Z₁ τ r z - outPrim Z₂ τ r z =
      outPrim (fun t y' => Z₁ t y' - Z₂ t y') τ r z := by
  unfold outPrim
  have e : (fun ρ : ℝ => ρ * (Z₁ τ (!₂[ρ, 0, z] : Space) - Z₂ τ (!₂[ρ, 0, z] : Space)) 2) =
      fun ρ => ρ * Z₁ τ (!₂[ρ, 0, z] : Space) 2 - ρ * Z₂ τ (!₂[ρ, 0, z] : Space) 2 := by
    funext ρ
    simp only [PiLp.sub_apply]
    ring
  rw [e, integral_sub h1 h2]
  ring

/-- The truncated modulus of the outward primitive difference of `sepWre ν m T` and
`sepWre ν m' T` on `ϱ y ≤ r2`. -/
def w2NWSub (ν m m' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ :=
  if ϱ y ≤ r2 then
    |outPrim (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2) -
      outPrim (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2)|
  else 0

/-- The corresponding vertical field. -/
def w2PhiWSub (ν m m' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  w2NWSub ν m m' R c r2 g τ y • coordinateVector 2

theorem w2NWSub_nonneg (ν m m' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    0 ≤ w2NWSub ν m m' R c r2 g τ y := by
  unfold w2NWSub; split_ifs <;> positivity

theorem w2NWSub_meridPt (ν m m' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    w2NWSub ν m m' R c r2 g τ (meridPt y) = w2NWSub ν m m' R c r2 g τ y := by
  unfold w2NWSub
  rw [w10_varrho_meridPt, w10_mp2]

theorem w2NWSub_measurable {ν m m' R c : ℝ} (hν : 0 < ν) (r2 : ℝ) {g : Chart → Ten3}
    (hg : Measurable g) :
    Measurable (fun x : ℝ × Space => w2NWSub ν m m' R c r2 g x.1 x.2) := by
  unfold w2NWSub
  have hT : ∀ i j, Measurable
      (fun x : ℝ × Space => oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 i j) :=
    oldCutMeasurable R c (R * Real.sqrt (5 * ν / 6)) g hg
  have hZ1 := sepWre_measurable ν m hν _ hT
  have hZ2 := sepWre_measurable ν m' hν _ hT
  have hO1 := outPrim_measurable hZ1
  have hO2 := outPrim_measurable hZ2
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk ((continuous_ϱ.measurable.comp measurable_snd).prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  refine Measurable.ite ?_ ((hO1.comp hq).sub (hO2.comp hq)).abs measurable_const
  exact measurableSet_le (continuous_ϱ.measurable.comp measurable_snd) measurable_const

theorem w2PhiWSub_norm (ν m m' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    ‖w2PhiWSub ν m m' R c r2 g τ y‖ = w2NWSub ν m m' R c r2 g τ y := by
  unfold w2PhiWSub
  rw [norm_smul, wyl_norm_coordinateVector, mul_one,
    Real.norm_of_nonneg (w2NWSub_nonneg _ _ _ _ _ _ _ _ _)]

/-- Domination of the outward primitive difference of `sepWre ν m T` and `sepWre ν m' T`. -/
theorem w2_psiWSub_dom {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (r2 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space),
      R * Real.sqrt ν ≤ ϱ y → ϱ y ≤ r2 →
        ENNReal.ofReal
            |outPrim (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2) -
              outPrim (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2)| ≤
          ENNReal.ofReal (C * |m - m'|) * w2Dom (w2k (R * Real.sqrt (5 * ν / 6))
            (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (r2 + R * Real.sqrt (5 * ν / 6)))
            (2 * (-1 / 8 : ℝ) + 2)
            (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y := by
  obtain ⟨C0, hC0, hdom⟩ := sepWSubDom_zero sepWSubDom_proved
  refine ⟨‖w10Re‖ * C0, by positivity, ?_⟩
  intro m m' hm hm' g hg τ y hy1 hy2
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  set T := oldCutSrc R c r0 g
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0 with hD
  have hDpos : 0 < D := sub_pos.2 hrr
  set a : ℝ := 2 * (-1 / 8 : ℝ) + 2
  set G := IIIa.srcNorm T
  have hpt : ∀ p : Space, R * Real.sqrt ν ≤ ϱ p →
      ENNReal.ofReal |(sepWre ν m T τ p - sepWre ν m' T τ p) 2| ≤
        ENNReal.ofReal (‖w10Re‖ * C0 * |m - m'|) * w2Dom (IIIa.sepKd 0 D) a G τ p := by
    intro p hp
    have e1 : |(sepWre ν m T τ p - sepWre ν m' T τ p) 2| ≤ ‖sepWre ν m T τ p - sepWre ν m' T τ p‖ :=
      wyl_abs_apply_le _ 2
    have d1 := hdom ν m m' r0 (R * Real.sqrt ν) (2 * c / R) hν hm hm' hr0nn hrr hP T hS τ p hp
    have m1 := w2_enorm_sepWre_sub (ν := ν) m m' T τ p
    calc ENNReal.ofReal |(sepWre ν m T τ p - sepWre ν m' T τ p) 2|
        ≤ ENNReal.ofReal ‖sepWre ν m T τ p - sepWre ν m' T τ p‖ := ENNReal.ofReal_le_ofReal e1
      _ = ‖sepWre ν m T τ p - sepWre ν m' T τ p‖ₑ := ofReal_norm _
      _ ≤ ENNReal.ofReal ‖w10Re‖ *
            (ENNReal.ofReal (C0 * |m - m'|) * w2Dom (IIIa.sepKd 0 D) a G τ p) :=
          m1.trans (mul_le_mul' le_rfl d1)
      _ = ENNReal.ofReal (‖w10Re‖ * C0 * |m - m'|) * w2Dom (IIIa.sepKd 0 D) a G τ p := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), mul_assoc ‖w10Re‖ C0]
  have hrr_y : r0 < ϱ y := lt_of_lt_of_le hrr hy1
  have hint1 := sepWre_outPrim_integrable hν (by linarith : -(1 / 4) < m) hr0nn hP hS hM τ (y 2) hrr_y
  have hint2 := sepWre_outPrim_integrable hν (by linarith : -(1 / 4) < m') hr0nn hP hS hM τ (y 2) hrr_y
  rw [outPrim_sub_eq hint1 hint2]
  have hnorm : ENNReal.ofReal |outPrim (fun t y' => sepWre ν m T t y' - sepWre ν m' T t y') τ (ϱ y) (y 2)| ≤
      ∫⁻ ρ in Ioi (ϱ y), ‖ρ * (sepWre ν m T τ (!₂[ρ, 0, y 2] : Space) -
        sepWre ν m' T τ (!₂[ρ, 0, y 2] : Space)) 2‖ₑ := by
    unfold outPrim
    rw [← Real.enorm_eq_ofReal_abs, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _
  refine hnorm.trans ?_
  calc ∫⁻ ρ in Ioi (ϱ y), ‖ρ * (sepWre ν m T τ (!₂[ρ, 0, y 2] : Space) -
          sepWre ν m' T τ (!₂[ρ, 0, y 2] : Space)) 2‖ₑ
      ≤ ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal (‖w10Re‖ * C0 * |m - m'|) *
          (ENNReal.ofReal ρ * w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ' : ϱ y < ρ := hρ
        have hρ0 : 0 ≤ ρ := (ϱ_nonneg y).trans hρ'.le
        have hϱ : ϱ (!₂[ρ, 0, y 2] : Space) = ρ := wardFar_varrho ρ (y 2) hρ0
        have := hpt (!₂[ρ, 0, y 2] : Space) (by rw [hϱ]; linarith)
        rw [enorm_mul, Real.enorm_of_nonneg hρ0, ← ofReal_norm, Real.norm_eq_abs]
        calc ENNReal.ofReal ρ * ENNReal.ofReal |(sepWre ν m T τ (!₂[ρ, 0, y 2] : Space) -
                sepWre ν m' T τ (!₂[ρ, 0, y 2] : Space)) 2|
            ≤ ENNReal.ofReal ρ * (ENNReal.ofReal (‖w10Re‖ * C0 * |m - m'|) *
                w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space)) := by gcongr
          _ = _ := by ring
    _ = ENNReal.ofReal (‖w10Re‖ * C0 * |m - m'|) *
          ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal ρ *
            w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact w2_tonelli hr0nn hDpos a (w2_srcNorm_measurable hS)
          (fun τ' z hz => w2_srcNorm_zero hS τ' hz) τ hy2 (by rw [hD]; linarith)

/-- `WylBd` for the outward primitive difference of `sepWre ν m T` and `sepWre ν m' T`. -/
theorem w2_psiWSubBd {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (r2 : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m m' : ℝ), 0 ≤ m → 0 ≤ m' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
          (wardYoungRead ν R (w2PhiWSub ν m m' R c r2 g)) (K * |m - m'|) := by
  obtain ⟨C, hC, hDom⟩ := w2_psiWSub_dom hν hR hc r2
  obtain ⟨B, hB, hLt⟩ := w2_ltau (μ := -1 / 8) hν hR hc (by norm_num) r2
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro m m' hm hm' g hg
  obtain ⟨hS, _, _⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  set T := oldCutSrc R c r0 g with hT
  set N : ℝ → Space → ℝ := w2NWSub ν m m' R c r2 g with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := w2NWSub_measurable hν r2 hg.measurable
  have hN0 : ∀ τ y, 0 ≤ N τ y := w2NWSub_nonneg ν m m' R c r2 g
  have hNper : ∀ τ y, N (τ + 2 * c / R) y = N τ y := by
    intro τ y
    simp only [hN, w2NWSub, ← hr0, ← hT, outPrim, sepWre_periodic ν m _ _ hS.periodic,
      sepWre_periodic ν m' _ _ hS.periodic]
  have hFm : Measurable (fun x : ℝ × Space => w2PhiWSub ν m m' R c r2 g x.1 x.2) :=
    hNm.smul_const _
  refine ⟨(w10_read_meas hFm).aestronglyMeasurable, ?_⟩
  set C' : ℝ := C * |m - m'|
  have hC' : 0 ≤ C' := mul_nonneg hC (abs_nonneg _)
  have hDom' : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤ ENNReal.ofReal C' *
        w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * (-1 / 8 : ℝ) + 2)
          (IIIa.srcNorm T) τ y := by
    intro τ y hy
    rw [hN, w2NWSub_meridPt]
    unfold w2NWSub
    split_ifs with h
    · exact hDom m m' hm hm' g hg τ y hy h
    · simp
  have hTr := chartYoungTransport R c ν hR hc hν (w10Fn R ν N) (w10Fn_measurable R ν hNm)
    (w10Fn_axi R ν N) (w10Fn_periodic R ν _ hNper)
  have hI : ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
        (ENNReal.ofReal C' * (ENNReal.ofReal B *
          IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T))) ^ (2 : ℝ) := by
    refine hTr.trans ?_
    gcongr
    have hpt : ∀ τ y, (if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
        ‖w10Fn R ν N τ y‖ₑ else 0) ≤ ENNReal.ofReal C' *
          w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * (-1 / 8 : ℝ) + 2)
            (IIIa.srcNorm T) τ y := by
      intro τ y
      by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
      · rw [if_pos h]
        have h' : R * Real.sqrt ν ≤ ϱ y := h
        rw [w10Fn_enorm hN0 τ h']
        exact hDom' τ y h'
      · rw [if_neg h]
        exact zero_le
    calc IIIa.ltauLq (2 * c / R) 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
            then ‖w10Fn R ν N τ y‖ₑ else 0)
        ≤ IIIa.ltauLq (2 * c / R) 2 (fun τ y => ENNReal.ofReal C' *
            w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * (-1 / 8 : ℝ) + 2)
              (IIIa.srcNorm T) τ y) :=
          IIIa.ltauLq_mono _ _ (by norm_num) hpt
      _ = ENNReal.ofReal C' * IIIa.ltauLq (2 * c / R) 2
            (w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * (-1 / 8 : ℝ) + 2)
              (IIIa.srcNorm T)) :=
          IIIa.ltauLq_const_mul _ _ (by norm_num) _ ENNReal.ofReal_ne_top _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hLt g hg) zero_le
  have hF : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖w2PhiWSub ν m m' R c r2 g τ y‖ ≤ N τ y :=
    fun τ y _ => le_of_eq (w2PhiWSub_norm ν m m' R c r2 g τ y)
  have hfin := w10_final hν hR hc g hg.measurable r0 hN0 hF C' B hC' hB hI
  rwa [show C' * B = C * B * |m - m'| by ring] at hfin

/-- The truncated modulus of the outward primitive difference of `wardX0 ν μ R c g` and
`wardX0 ν μ' R c g` on `ϱ y ≤ r2`. -/
def w2NSub (ν μ μ' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ :=
  if ϱ y ≤ r2 then
    |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) - outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)|
  else 0

/-- The corresponding vertical field. -/
def w2PhiSub (ν μ μ' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  w2NSub ν μ μ' R c r2 g τ y • coordinateVector 2

theorem w2NSub_nonneg (ν μ μ' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    0 ≤ w2NSub ν μ μ' R c r2 g τ y := by
  unfold w2NSub; split_ifs <;> positivity

theorem w2NSub_meridPt (ν μ μ' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    w2NSub ν μ μ' R c r2 g τ (meridPt y) = w2NSub ν μ μ' R c r2 g τ y := by
  unfold w2NSub
  rw [w10_varrho_meridPt, w10_mp2]

theorem w2NSub_measurable {ν μ μ' R c : ℝ} (r2 : ℝ) {g : Chart → Ten3} (hg : Measurable g) :
    Measurable (fun x : ℝ × Space => w2NSub ν μ μ' R c r2 g x.1 x.2) := by
  unfold w2NSub
  have hZ1 := wardX0_measurable_of_measurable ν μ R c g hg
  have hZ2 := wardX0_measurable_of_measurable ν μ' R c g hg
  have hO1 := outPrim_measurable hZ1
  have hO2 := outPrim_measurable hZ2
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk ((continuous_ϱ.measurable.comp measurable_snd).prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  refine Measurable.ite ?_ ((hO1.comp hq).sub (hO2.comp hq)).abs measurable_const
  exact measurableSet_le (continuous_ϱ.measurable.comp measurable_snd) measurable_const

theorem w2PhiSub_norm (ν μ μ' R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    ‖w2PhiSub ν μ μ' R c r2 g τ y‖ = w2NSub ν μ μ' R c r2 g τ y := by
  unfold w2PhiSub
  rw [norm_smul, wyl_norm_coordinateVector, mul_one,
    Real.norm_of_nonneg (w2NSub_nonneg _ _ _ _ _ _ _ _ _)]

/-- `WylBd` for the outward primitive difference of `wardX0 ν μ R c g` and `wardX0 ν μ' R c g`. -/
theorem w2_psiSubBd {ν R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (r2 : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
          (wardYoungRead ν R (w2PhiSub ν μ μ' R c r2 g)) (K * |μ - μ'|) := by
  obtain ⟨KW, hKW, hΨW⟩ := w2_psiWSubBd hν hR hc r2
  refine ⟨2 * KW, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg
  have hμ1 : 0 ≤ μ + 1 := by linarith
  have hμ'1 : 0 ≤ μ' + 1 := by linarith
  have hsub_eq : |(μ + 1) - (μ' + 1)| = |μ - μ'| := by ring_nf
  have b1 := hΨW μ μ' hμ hμ' g hg
  have b2 := hΨW (μ + 1) (μ' + 1) hμ1 hμ'1 g hg
  rw [hsub_eq] at b2
  have hK0 : 0 ≤ KW * |μ - μ'| := mul_nonneg hKW (abs_nonneg _)
  have bSum := b1.add b2 hK0 hK0
  have hFm : Measurable (fun x : ℝ × Space => w2PhiSub ν μ μ' R c r2 g x.1 x.2) :=
    (w2NSub_measurable r2 hg.measurable).smul_const _
  refine ⟨(w10_read_meas hFm).aestronglyMeasurable, ?_⟩
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  set T := oldCutSrc R c r0 g
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hX0_1 := w10_X0_eq (μ := μ) hν hR hc hg
  have hX0_2 := w10_X0_eq (μ := μ') hν hR hc hg
  have hdom : ∀ q : Chart,
      wardYoungRead ν R (w2PhiSub ν μ μ' R c r2 g) q ≤
        wardYoungRead ν R (w2PhiWSub ν μ μ' R c r2 g) q +
          wardYoungRead ν R (w2PhiWSub ν (μ + 1) (μ' + 1) R c r2 g) q := by
    refine w10_read_dom hν hR fun τ y hy => ?_
    rw [w2PhiSub_norm, w2PhiWSub_norm, w2PhiWSub_norm]
    unfold w2NSub w2NWSub
    split_ifs with h2
    · have hrr_y : r0 < ϱ y := lt_of_lt_of_le hrr hy
      have i1 := sepWre_outPrim_integrable hν (by linarith : -(1 / 4) < μ) hr0nn hP hS hM τ (y 2) hrr_y
      have i2 := sepWre_outPrim_integrable hν (by linarith : -(1 / 4) < μ + 1) hr0nn hP hS hM τ (y 2) hrr_y
      have i3 := sepWre_outPrim_integrable hν (by linarith : -(1 / 4) < μ') hr0nn hP hS hM τ (y 2) hrr_y
      have i4 := sepWre_outPrim_integrable hν (by linarith : -(1 / 4) < μ' + 1) hr0nn hP hS hM τ (y 2) hrr_y
      have hX0_sub (m : ℝ) :
          sepX0 ν m T = fun t y' => sepWre ν m T t y' - sepWre ν (m + 1) T t y' := by
        funext t y'; exact sepX0_eq_sub ν m T t y'
      have e1 : outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) =
          outPrim (sepWre ν μ T) τ (ϱ y) (y 2) - outPrim (sepWre ν (μ + 1) T) τ (ϱ y) (y 2) := by
        rw [hX0_1, hX0_sub, ← outPrim_sub_eq i1 i2]
      have e2 : outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2) =
          outPrim (sepWre ν μ' T) τ (ϱ y) (y 2) - outPrim (sepWre ν (μ' + 1) T) τ (ϱ y) (y 2) := by
        rw [hX0_2, hX0_sub, ← outPrim_sub_eq i3 i4]
      rw [e1, e2]
      set A1 := outPrim (sepWre ν μ T) τ (ϱ y) (y 2)
      set B1 := outPrim (sepWre ν (μ + 1) T) τ (ϱ y) (y 2)
      set A2 := outPrim (sepWre ν μ' T) τ (ϱ y) (y 2)
      set B2 := outPrim (sepWre ν (μ' + 1) T) τ (ϱ y) (y 2)
      calc |(A1 - B1) - (A2 - B2)| = |(A1 - A2) + -(B1 - B2)| := by ring_nf
        _ ≤ |A1 - A2| + |-(B1 - B2)| := abs_add_le _ _
        _ = |A1 - A2| + |B1 - B2| := by rw [abs_neg]
    · simp
  refine (eLpNorm_mono_real (fun q => ?_)).trans
    (bSum.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))
  rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
  exact hdom q

theorem w113_norm_merid_sepWre_sub {ν m m' R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hm : -(1 / 4) < m) (hm' : -(1 / 4) < m') {g : Chart → Ten3} (hg : IsOldL2 c ν g)
    (τ : ℝ) (y : Space) (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    ‖sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ (meridPt y) -
        sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ (meridPt y)‖ =
      ‖sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y -
        sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y‖ := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy
  obtain ⟨M, hMo, hTM, hmer, -⟩ := w10_rotdatum hAx hρ
  have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
    rw [w10_varrho_meridPt]; exact hy
  have e1 := w10_equivV hν hm hr hP hS hM hMo hTM τ (meridPt y) hmU
  have e2 := w10_equivV hν hm' hr hP hS hM hMo hTM τ (meridPt y) hmU
  rw [hmer] at e1 e2
  rw [e1, e2, ← w2_actM_sub, norm_actM hMo]

theorem w2_norm_merid_sub {ν μ μ' R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ') {g : Chart → Ten3} (hg : IsOldL2 c ν g)
    (τ : ℝ) (y : Space) (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    ‖wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)‖ =
      ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy
  obtain ⟨M, hMo, hTM, hmer, -⟩ := w10_rotdatum hAx hρ
  have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
    rw [w10_varrho_meridPt]; exact hy
  have e1 := w2_X0_equiv hν hR hc hμ hg hMo hTM τ (meridPt y) hmU
  have e2 := w2_X0_equiv hν hR hc hμ' hg hMo hTM τ (meridPt y) hmU
  rw [hmer] at e1 e2
  rw [e1, e2, ← w2_actM_sub, norm_actM hMo]

theorem w113_streamCorrWSub_pd_bound {ν m m' R c : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hm : -(1 / 4) < m) (hm' : -(1 / 4) < m')
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3)
    {y : Space} (hy : y ∈ youngOpen ν R) :
    ‖physPd (streamCorr ν R χy (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) j y -
        physPd (streamCorr ν R χy (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) j y‖ ≤
      |deriv (w2a ν R χy) (ϱ y)| *
        |outPrim (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2) -
          outPrim (sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2)| +
        |w2a ν R χy (ϱ y)| *
          (2 * ϱ y * ‖sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y -
            sepWre ν m' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y‖) := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hy'
  have hΨ1 : HasFDerivAt (fun x : Space => outPrim (sepWre ν m T) τ (ϱ x) (x 2))
      ((ϱ y * sepWre ν m T τ (meridPt y) 2) • ϱD y +
        (-(ϱ y * sepWre ν m T τ (meridPt y) 0)) •
          (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y :=
    wgx_outPrim_hasFDerivAt hν hR (Sub8_1_1_2_3.wre_contDiffOn hν hm hr0 hP hS hM τ)
      (fun r z hr => Sub8_1_1_2_3.wre_partials hν hR hm hP hS hM hAx τ r z hr) hy
  have hΨ2 : HasFDerivAt (fun x : Space => outPrim (sepWre ν m' T) τ (ϱ x) (x 2))
      ((ϱ y * sepWre ν m' T τ (meridPt y) 2) • ϱD y +
        (-(ϱ y * sepWre ν m' T τ (meridPt y) 0)) •
          (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y :=
    wgx_outPrim_hasFDerivAt hν hR (Sub8_1_1_2_3.wre_contDiffOn hν hm' hr0 hP hS hM τ)
      (fun r z hr => Sub8_1_1_2_3.wre_partials hν hR hm' hP hS hM hAx τ r z hr) hy
  have hwd : HasDerivAt (w2a ν R χy) (deriv (w2a ν R χy) (ϱ y)) (ϱ y) :=
    (((w2a_contDiffOn (ν := ν) (R := R) hχ).contDiffAt (Ioi_mem_nhds hρ)).differentiableAt
      one_ne_zero).hasDerivAt
  have hA1 := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ1
  have hC1 := hA1.smul_const (coordinateVector 2)
  have hA2 := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ2
  have hC2 := hA2.smul_const (coordinateVector 2)
  have hEq1 : physPd (streamCorr ν R χy (sepWre ν m T) τ) j y = _ :=
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hC1.fderiv
  have hEq2 : physPd (streamCorr ν R χy (sepWre ν m' T) τ) j y = _ :=
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hC2.fderiv
  rw [hEq1, hEq2]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ← sub_smul, norm_smul,
    wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs, Function.comp]
  have hn := w113_norm_merid_sepWre_sub hν hR hc hm hm' hg τ y hy
  have hm2 : |(sepWre ν m T τ (meridPt y) - sepWre ν m' T τ (meridPt y)) 2| ≤
      ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 2
  have hm0 : |(sepWre ν m T τ (meridPt y) - sepWre ν m' T τ (meridPt y)) 0| ≤
      ‖sepWre ν m T τ y - sepWre ν m' T τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 0
  have hD := w2_abs_ϱD y hy' j
  have hE := w2_abs_cv2 j
  set Ψ1 := outPrim (sepWre ν m T) τ (ϱ y) (y 2)
  set Ψ2 := outPrim (sepWre ν m' T) τ (ϱ y) (y 2)
  set w := w2a ν R χy (ϱ y)
  set w' := deriv (w2a ν R χy) (ϱ y)
  set d := ϱD y (coordinateVector j)
  set e := coordinateVector j 2
  set Z2 := (sepWre ν m T τ (meridPt y) - sepWre ν m' T τ (meridPt y)) 2
  set Z0 := (sepWre ν m T τ (meridPt y) - sepWre ν m' T τ (meridPt y)) 0
  set N := ‖sepWre ν m T τ y - sepWre ν m' T τ y‖
  have heq : (w * (ϱ y * sepWre ν m T τ (meridPt y) 2 * d +
        -(ϱ y * sepWre ν m T τ (meridPt y) 0) * e) + Ψ1 * (w' * d)) -
      (w * (ϱ y * sepWre ν m' T τ (meridPt y) 2 * d +
        -(ϱ y * sepWre ν m' T τ (meridPt y) 0) * e) + Ψ2 * (w' * d)) =
      w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + (Ψ1 - Ψ2) * (w' * d) := by
    simp only [Z2, Z0, PiLp.sub_apply]
    ring
  refine le_of_eq_of_le (congrArg abs heq) ?_
  have hPb : |ϱ y * Z2 * d| ≤ ϱ y * N := by
    rw [abs_mul, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z2| * |d| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm2 hρ.le) hD (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hQb : |-(ϱ y * Z0) * e| ≤ ϱ y * N := by
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z0| * |e| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm0 hρ.le) hE (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hsum : |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ 2 * ϱ y * N := by
    calc _ ≤ |ϱ y * Z2 * d| + |-(ϱ y * Z0) * e| := abs_add_le _ _
      _ ≤ 2 * ϱ y * N := by linarith
  calc |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + (Ψ1 - Ψ2) * (w' * d)|
      ≤ |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e)| + |(Ψ1 - Ψ2) * (w' * d)| := abs_add_le _ _
    _ ≤ |w'| * |Ψ1 - Ψ2| + |w| * (2 * ϱ y * N) := by
        rw [abs_mul, abs_mul, abs_mul]
        have h1 : |w| * |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ |w| * (2 * ϱ y * N) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        have h2 : |Ψ1 - Ψ2| * (|w'| * |d|) ≤ |w'| * |Ψ1 - Ψ2| := by
          calc |Ψ1 - Ψ2| * (|w'| * |d|) ≤ |Ψ1 - Ψ2| * (|w'| * 1) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hD (abs_nonneg _)) (abs_nonneg _)
            _ = |w'| * |Ψ1 - Ψ2| := by ring
        linarith

theorem w2_corrSub_pd_bound {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3)
    {y : Space} (hy : y ∈ youngOpen ν R) :
    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
        physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ ≤
      |deriv (w2a ν R χy) (ϱ y)| *
        |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
          outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| +
        |w2a ν R χy (ϱ y)| * (2 * ϱ y * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) := by
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hy'
  have hΨ1 := w2_psi_hasFDeriv hν hR hc hμ hg τ hy
  have hΨ2 := w2_psi_hasFDeriv hν hR hc hμ' hg τ hy
  have hwd : HasDerivAt (w2a ν R χy) (deriv (w2a ν R χy) (ϱ y)) (ϱ y) :=
    (((w2a_contDiffOn (ν := ν) (R := R) hχ).contDiffAt (Ioi_mem_nhds hρ)).differentiableAt
      one_ne_zero).hasDerivAt
  have hA1 := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ1
  have hC1 := hA1.smul_const (coordinateVector 2)
  have hA2 := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ2
  have hC2 := hA2.smul_const (coordinateVector 2)
  have hEq1 : physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y = _ :=
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hC1.fderiv
  have hEq2 : physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y = _ :=
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j)) hC2.fderiv
  rw [hEq1, hEq2]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ← sub_smul, norm_smul,
    wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs, Function.comp]
  have hn := w2_norm_merid_sub hν hR hc hμ hμ' hg τ y hy
  have hm2 : |(wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)) 2| ≤
      ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 2
  have hm0 : |(wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)) 0| ≤
      ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 0
  have hD := w2_abs_ϱD y hy' j
  have hE := w2_abs_cv2 j
  set Ψ1 := outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)
  set Ψ2 := outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)
  set w := w2a ν R χy (ϱ y)
  set w' := deriv (w2a ν R χy) (ϱ y)
  set d := ϱD y (coordinateVector j)
  set e := coordinateVector j 2
  set Z2 := (wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)) 2
  set Z0 := (wardX0 ν μ R c g τ (meridPt y) - wardX0 ν μ' R c g τ (meridPt y)) 0
  set N := ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖
  have heq : (w * (ϱ y * wardX0 ν μ R c g τ (meridPt y) 2 * d +
        -(ϱ y * wardX0 ν μ R c g τ (meridPt y) 0) * e) + Ψ1 * (w' * d)) -
      (w * (ϱ y * wardX0 ν μ' R c g τ (meridPt y) 2 * d +
        -(ϱ y * wardX0 ν μ' R c g τ (meridPt y) 0) * e) + Ψ2 * (w' * d)) =
      w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + (Ψ1 - Ψ2) * (w' * d) := by
    simp only [Z2, Z0, PiLp.sub_apply]
    ring
  refine le_of_eq_of_le (congrArg abs heq) ?_
  have hPb : |ϱ y * Z2 * d| ≤ ϱ y * N := by
    rw [abs_mul, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z2| * |d| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm2 hρ.le) hD (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hQb : |-(ϱ y * Z0) * e| ≤ ϱ y * N := by
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z0| * |e| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm0 hρ.le) hE (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hsum : |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ 2 * ϱ y * N := by
    calc _ ≤ |ϱ y * Z2 * d| + |-(ϱ y * Z0) * e| := abs_add_le _ _
      _ ≤ 2 * ϱ y * N := by linarith
  calc |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + (Ψ1 - Ψ2) * (w' * d)|
      ≤ |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e)| + |(Ψ1 - Ψ2) * (w' * d)| := abs_add_le _ _
    _ ≤ |w'| * |Ψ1 - Ψ2| + |w| * (2 * ϱ y * N) := by
        rw [abs_mul, abs_mul, abs_mul]
        have h1 : |w| * |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ |w| * (2 * ϱ y * N) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        have h2 : |Ψ1 - Ψ2| * (|w'| * |d|) ≤ |w'| * |Ψ1 - Ψ2| := by
          calc |Ψ1 - Ψ2| * (|w'| * |d|) ≤ |Ψ1 - Ψ2| * (|w'| * 1) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hD (abs_nonneg _)) (abs_nonneg _)
            _ = |w'| * |Ψ1 - Ψ2| := by ring
        linarith

/-- Young bound from a pointwise domination by `w2NSub` and `‖wardX0 ν μ - wardX0 ν μ'‖`. -/
theorem w2_young_of_pt_sub {ν μ μ' R c : ℝ} {g : Chart → Ten3} (hν : 0 < ν) (hR : 0 < R)
    (r2 : ℝ) {CX : ℝ} (hCX : 0 ≤ CX)
    (hX : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y)) CX)
    {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (wardYoungRead ν R F) (ageμ c (-3 / 2)))
    {K : ℝ} (hK : 0 ≤ K)
    (hΦ : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (w2PhiSub ν μ μ' R c r2 g)) K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpt : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ‖F τ y‖ ≤ a * w2NSub ν μ μ' R c r2 g τ y +
        b * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) :
    YoungL2Le c ν R (a * K + b * CX) F g := by
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => a • w2PhiSub ν μ μ' R c r2 g τ y)) (a * K) := by
    rw [w2_read_smul]
    simpa [abs_of_nonneg ha] using hΦ.const_mul a
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R
        (fun τ y => b • (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y))) (b * CX) := by
    rw [w2_read_smul]
    simpa [abs_of_nonneg hb] using hX.const_mul b
  refine w10_young_of_sum hFm hA hB (mul_nonneg ha hK) (mul_nonneg hb hCX) le_rfl
    fun q => w10_read_dom hν hR (fun τ y hy => ?_) q
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
    abs_of_nonneg hb, w2PhiSub_norm]
  exact hpt τ y hy

/-- **`wardStreamCorr` `μ`-difference in the young `L²` norm (value and first partials)**. -/
theorem wSub_wardStreamCorrYoungL2 (ν R c : ℝ) (χy : ℝ → ℝ) (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g →
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y -
            wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ y) g ∧
        ∀ j : Fin 3,
          YoungL2Le c ν R (C * |μ - μ'|)
            (fun τ y => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
              physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y) g := by
  classical
  obtain ⟨CX, hCX0, hX⟩ := wSub_wardX0YoungL2 ν R c hν hR hc
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4) with hr2
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiSubBd hν hR hc r2
  obtain ⟨Ca, Cb, hCa, hCb, hab⟩ := w2a_bound hχ hν hR
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  refine ⟨(Ca + Cb) * K + (2 * Ca * r2) * CX, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  have hCX_mu : 0 ≤ CX * |μ - μ'| := mul_nonneg hCX0 (abs_nonneg _)
  have hK_mu : 0 ≤ K * |μ - μ'| := mul_nonneg hK (abs_nonneg _)
  have hX1 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y))
      (CX * |μ - μ'|) := by
    have := wyl_bd_of_young (hX μ μ' hμ hμ' g hg).1
    rwa [max_eq_left hCX_mu] at this
  have hval : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ‖wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y -
          wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ y‖ ≤
        Ca * w2NSub ν μ μ' R c r2 g τ y +
          0 * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ := by
    intro τ y hy
    rw [wardStreamCorr_eq, wardStreamCorr_eq, ← sub_smul, ← mul_sub, norm_smul,
      wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs, abs_mul, zero_mul, add_zero]
    by_cases h2 : ϱ y ≤ r2
    · have hN : w2NSub ν μ μ' R c r2 g τ y =
          |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| := by
        unfold w2NSub; rw [if_pos h2]
      rw [hN]
      exact mul_le_mul_of_nonneg_right (hab (ϱ y) hy h2).1 (abs_nonneg _)
    · rw [w2a_zero_of_gt hχ hν hR (not_le.1 h2), abs_zero, zero_mul]
      exact mul_nonneg hCa (w2NSub_nonneg _ _ _ _ _ _ _ _ _)
  have hpd : ∀ (j : Fin 3) τ y, R * Real.sqrt ν ≤ ϱ y →
      ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y‖ ≤
        Cb * w2NSub ν μ μ' R c r2 g τ y +
          (2 * Ca * r2) * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ := by
    intro j τ y hy
    have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
    have hb := w2_corrSub_pd_bound hχ hν hR hc hμ_gt hμ'_gt hg τ j hyU
    refine hb.trans ?_
    by_cases h2 : ϱ y ≤ r2
    · have hN : w2NSub ν μ μ' R c r2 g τ y =
          |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| := by
        unfold w2NSub; rw [if_pos h2]
      rw [hN]
      obtain ⟨h1, h1'⟩ := hab (ϱ y) hy h2
      have hZ := norm_nonneg (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y)
      have hρ : 0 ≤ ϱ y := ϱ_nonneg y
      have e1 : |deriv (w2a ν R χy) (ϱ y)| *
          |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| ≤
          Cb * |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2) -
            outPrim (wardX0 ν μ' R c g) τ (ϱ y) (y 2)| :=
        mul_le_mul_of_nonneg_right h1' (abs_nonneg _)
      have e2 : |w2a ν R χy (ϱ y)| *
          (2 * ϱ y * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) ≤
          (2 * Ca * r2) * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ := by
        calc _ ≤ Ca * (2 * r2 * ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖) :=
              mul_le_mul h1 (by nlinarith) (by positivity) hCa
          _ = _ := by ring
      linarith
    · have h2' := not_le.1 h2
      rw [w2a_zero_of_gt hχ hν hR h2', w2a_deriv_zero_of_gt hχ hν hR h2']
      simp only [abs_zero, zero_mul]
      have := w2NSub_nonneg ν μ μ' R c r2 g τ y
      have hZ := norm_nonneg (wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y)
      have e3 := mul_nonneg hCb this
      have e4 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCa) hr2nn) hZ
      linarith
  constructor
  · have hFm : AEStronglyMeasurable
        (wardYoungRead ν R (fun τ y => wardStreamCorr ν R χy (wardX0 ν μ R c g) τ y -
          wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ y)) (ageμ c (-3 / 2)) :=
      (w10_read_meas ((w2_corr_measurable hg).sub (w2_corr_measurable hg))).aestronglyMeasurable
    refine w2_young_mono (w2_young_of_pt_sub hν hR r2 hCX_mu hX1 hFm hK_mu (hΨ μ μ' hμ hμ' g hg)
      hCa le_rfl hval) ?_
    nlinarith [mul_nonneg hCb hK_mu,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCa) hr2nn) hCX_mu]
  · intro j
    have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
    have hPd1 := w10_meas_pd (w2_corr_measurable (χy := χy) (μ := μ) hg) hUo.measurableSet
      (fun τ y hy => w2_corr_diff hχ hν hR hc hμ_gt hg τ hy) j
    have hPd2 := w10_meas_pd (w2_corr_measurable (χy := χy) (μ := μ') hg) hUo.measurableSet
      (fun τ y hy => w2_corr_diff hχ hν hR hc hμ'_gt hg τ hy) j
    have hread : wardYoungRead ν R
        (fun τ y => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y) =
        wardYoungRead ν R (fun τ y =>
          (if y ∈ youngOpen ν R then
            physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y else 0) -
          (if y ∈ youngOpen ν R then
            physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y else 0)) := by
      refine w10_read_congr hν hR fun τ y hy => ?_
      have : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
      simp [this]
    have hFm : AEStronglyMeasurable (wardYoungRead ν R
        (fun τ y => physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (wardStreamCorr ν R χy (wardX0 ν μ' R c g) τ) j y)) (ageμ c (-3 / 2)) := by
      rw [hread]
      exact (w10_read_meas (hPd1.sub hPd2)).aestronglyMeasurable
    refine w2_young_mono (w2_young_of_pt_sub hν hR r2 hCX_mu hX1 hFm hK_mu (hΨ μ μ' hμ hμ' g hg)
      hCb (by positivity) (fun τ y hy => hpd j τ y hy)) ?_
    nlinarith [mul_nonneg hCa hK_mu]

end UnforcedLeray.Short.PartIIIb.Concrete
end
