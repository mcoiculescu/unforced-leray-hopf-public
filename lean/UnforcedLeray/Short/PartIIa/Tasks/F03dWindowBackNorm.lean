import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Units.B0424.Chart

/-!
# Part II-a, task `PartII-a:F03/4`: the norm of the transported Laplacian (`WindowBackNorm`)

Source of record: `the November 2 reference manuscript`, lines 1435-1436 ("All
Jacobians on the window are bounded"). Target: `WindowBackNorm` in `Short/PartII-a/Sub/F03.lean`.

Proof outline. (1) Pointwise on `ℂ³`: `‖v‖ₑ^q ≤ 3^(q-1) Σ_c ‖v_c‖ₑ^q`. (2) Each component of
`windowLap` is `wdComp`, a copy of `ν D_c` on `|t| < 1`, pulled back by the window chart
`(τ, y) ↦ (e^{τ-τ₀}, e^{(τ-τ₀)/2} y)`. (3) Lower integrals: shift `τ = τ₀ + t`; dilation
`x = e^{t/2} y` (`lintegral_dilChart'`, density `e^{3t/2}`); time change `θ = e^t`
(`lintegral_expChart'`, density `e^t`). The resulting weight `e^{3(q-1)t/2} θ^{-1}` is at most
`e^{3(q-1)/2+1}` on `|t| < 1`. (4) Tonelli for the iterated integral needs measurability of
`D_c`; this enters only through quasi measure preservation of the window chart, which the density
identities give.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic

/-! ### Pointwise bounds on `ℂ³` -/

/-- Real-valued enorm of a nonnegative real. -/
theorem wd_enorm_real (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

/-- `‖v‖ₑ^q ≤ 3^(q-1) Σ_c ‖v_c‖ₑ^q` on `ℂ³` for `q ≥ 1`. -/
theorem wd_enorm_rpow_le (q : ℝ) (hq : 1 ≤ q) (v : CVec3) :
    ‖v‖ₑ ^ q ≤ ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ∑ c, ‖v c‖ₑ ^ q := by
  have hreal : ‖v‖ ≤ ∑ c, ‖v c‖ := by
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ c, ‖v c‖ ^ 2) ≤ Real.sqrt ((∑ c, ‖v c‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun c _ => norm_nonneg _)
      _ = ∑ c, ‖v c‖ := Real.sqrt_sq (Finset.sum_nonneg fun c _ => norm_nonneg _)
  have hE : ‖v‖ₑ ≤ ∑ c, ‖v c‖ₑ := by
    rw [← ofReal_norm v]
    calc ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (∑ c, ‖v c‖) := ENNReal.ofReal_le_ofReal hreal
      _ = ∑ c, ENNReal.ofReal ‖v c‖ := ENNReal.ofReal_sum_of_nonneg fun c _ => norm_nonneg _
      _ = ∑ c, ‖v c‖ₑ := Finset.sum_congr rfl fun c _ => ofReal_norm _
  have hc : ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) =
      ((Finset.univ : Finset (Fin 3)).card : ℝ≥0∞) ^ (q - 1) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) (by linarith),
      Finset.card_univ, Fintype.card_fin]
    norm_num
  calc ‖v‖ₑ ^ q ≤ (∑ c, ‖v c‖ₑ) ^ q := ENNReal.rpow_le_rpow hE (by linarith)
    _ ≤ ((Finset.univ : Finset (Fin 3)).card : ℝ≥0∞) ^ (q - 1) * ∑ c, ‖v c‖ₑ ^ q :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ) (f := fun c => ‖v c‖ₑ) (hp := hq)
    _ = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ∑ c, ‖v c‖ₑ ^ q := by rw [hc]

/-! ### The window chart is quasi measure preserving -/

/-- A measurable map whose pushforward of the density `ρ > 0` measure is `volume` (or is null on
null sets) is quasi measure preserving. -/
theorem wd_qmp_of_density {f : ℝ × Space → ℝ × Space} (hf : Measurable f)
    {ρ : ℝ × Space → ℝ≥0∞} (hρ : Measurable ρ) (hpos : ∀ p, ρ p ≠ 0)
    (hmap : ∀ t : Set (ℝ × Space), MeasurableSet t → volume t = 0 →
      Measure.map f (volume.withDensity ρ) t = 0) :
    Measure.QuasiMeasurePreserving f volume volume := by
  refine ⟨hf, ?_⟩
  intro s hs
  have key : ∀ t : Set (ℝ × Space), MeasurableSet t → volume t = 0 → volume (f ⁻¹' t) = 0 := by
    intro t ht h0
    have h1 := hmap t ht h0
    rw [Measure.map_apply hf ht, withDensity_apply_eq_zero' hρ.aemeasurable] at h1
    have hu : {x | ρ x ≠ 0} = univ := Set.eq_univ_of_forall fun x => hpos x
    rwa [hu, univ_inter] at h1
  have hs' : volume (toMeasurable volume s) = 0 := by rwa [measure_toMeasurable]
  refine le_antisymm ?_ zero_le
  calc Measure.map f volume s ≤ Measure.map f volume (toMeasurable volume s) :=
        measure_mono (subset_toMeasurable _ _)
    _ = 0 := by
        rw [Measure.map_apply hf (measurableSet_toMeasurable _ _)]
        exact key _ (measurableSet_toMeasurable _ _) hs'

theorem wd_qmp_dil :
    Measure.QuasiMeasurePreserving UnforcedLeray.B0424.dilChart volume volume :=
  wd_qmp_of_density UnforcedLeray.B0424.measurable_dilChart
    UnforcedLeray.B0424.measurable_rhoD
    (fun p => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
    (fun t _ h0 => by rw [UnforcedLeray.B0424.map_dilChart]; exact h0)

theorem wd_qmp_exp :
    Measure.QuasiMeasurePreserving UnforcedLeray.B0424.expChart volume volume :=
  wd_qmp_of_density UnforcedLeray.B0424.measurable_expChart
    UnforcedLeray.B0424.measurable_rhoE
    (fun p => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
    (fun t ht h0 => by
      rw [UnforcedLeray.B0424.map_expChart, Measure.restrict_apply ht]
      exact measure_mono_null Set.inter_subset_left h0)

theorem wd_qmp_shift (τ₀ : ℝ) :
    Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (z.1 - τ₀, z.2)) volume volume := by
  have hT : MeasurePreserving (fun z : ℝ × Space => (z.1 - τ₀, z.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_sub_right volume τ₀).prod (MeasurePreserving.id volume)
  exact hT.quasiMeasurePreserving

theorem wd_qmp_window (τ₀ : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × Space => (Real.exp (z.1 - τ₀), Real.exp ((z.1 - τ₀) / 2) • z.2))
      volume volume :=
  wd_qmp_exp.comp (wd_qmp_dil.comp (wd_qmp_shift τ₀))

/-! ### The scalar components -/

/-- Component `c` of `windowLap` in terms of a scalar function `g` on `PS 3`. -/
def wdComp (ν τ₀ : ℝ) (g : PS 3 → ℂ) (z : ℝ × Space) : ℂ :=
  if |z.1 - τ₀| < 1 then
    (ν : ℂ) * ((Real.exp (3 * (z.1 - τ₀) / 2) : ℝ) : ℂ) *
      g (Real.exp (z.1 - τ₀), Real.exp ((z.1 - τ₀) / 2) • z.2)
  else 0

/-- The dilated form: `wdComp ν τ₀ g z = wdMd ν g (dilChart (z.1 - τ₀, z.2))`. -/
def wdMd (ν : ℝ) (g : PS 3 → ℂ) (w : ℝ × Space) : ℂ :=
  if |w.1| < 1 then
    (ν : ℂ) * ((Real.exp (3 * w.1 / 2) : ℝ) : ℂ) * g (Real.exp w.1, w.2)
  else 0

/-- The density-weighted integrand of the dilation step. -/
def wdG1 (q ν : ℝ) (g : PS 3 → ℂ) (w : ℝ × Space) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(3 * w.1 / 2))) * ‖wdMd ν g w‖ₑ ^ q

/-- The integrand of the time-change step: `∫⁻ G1 = ∫⁻_{θ>0} K`. -/
def wdKK (q ν : ℝ) (g : PS 3 → ℂ) (z : ℝ × Space) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-Real.log z.1)) * wdG1 q ν g (Real.log z.1, z.2)

theorem wdComp_eq (ν τ₀ : ℝ) (g : PS 3 → ℂ) (z : ℝ × Space) :
    wdComp ν τ₀ g z = wdMd ν g (UnforcedLeray.B0424.dilChart (z.1 - τ₀, z.2)) := rfl

theorem windowLap_apply_comp (ν τ₀ : ℝ) (D : Fin 3 → PS 3 → ℂ) (z : ℝ × Space) (c : Fin 3) :
    windowLap ν τ₀ D z c = wdComp ν τ₀ (D c) z := by
  unfold windowLap wdComp
  split_ifs <;> simp

/-- Measurability of a component, from the measurability of `g` and the window chart. -/
theorem wd_aemeasurable (ν τ₀ : ℝ) (g : PS 3 → ℂ) (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (wdComp ν τ₀ g) volume := by
  have h1 : AEMeasurable
      (fun z : ℝ × Space => g (Real.exp (z.1 - τ₀), Real.exp ((z.1 - τ₀) / 2) • z.2)) volume :=
    (hg.comp_quasiMeasurePreserving (wd_qmp_window τ₀)).aemeasurable
  have h2 : Measurable
      (fun z : ℝ × Space => (ν : ℂ) * ((Real.exp (3 * (z.1 - τ₀) / 2) : ℝ) : ℂ)) := by
    fun_prop
  have hS : MeasurableSet {z : ℝ × Space | |z.1 - τ₀| < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h3 := (h2.aemeasurable.mul h1).indicator hS
  refine h3.congr (ae_of_all _ fun z => ?_)
  simp only [wdComp, Set.indicator_apply, Set.mem_setOf_eq, Pi.mul_apply]

/-! ### Algebra of the dilation and time-change steps -/

/-- Dilation identity: `ρ_D(p) · G1(dilChart p) = ‖wdMd (dilChart p)‖ₑ^q`. -/
theorem wd_dil_step (q ν : ℝ) (g : PS 3 → ℂ) (p : ℝ × Space) :
    UnforcedLeray.B0424.rhoD p * wdG1 q ν g (UnforcedLeray.B0424.dilChart p) =
      ‖wdMd ν g (UnforcedLeray.B0424.dilChart p)‖ₑ ^ q := by
  have h1 : (UnforcedLeray.B0424.dilChart p).1 = p.1 := rfl
  unfold wdG1 UnforcedLeray.B0424.rhoD
  rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp

/-- Time-change identity: `ρ_E(p) · K(expChart p) = G1 p`. -/
theorem wd_exp_step (q ν : ℝ) (g : PS 3 → ℂ) (p : ℝ × Space) :
    UnforcedLeray.B0424.rhoE p * wdKK q ν g (UnforcedLeray.B0424.expChart p) =
      wdG1 q ν g p := by
  have h1 : (UnforcedLeray.B0424.expChart p).1 = Real.exp p.1 := rfl
  have h2 : (UnforcedLeray.B0424.expChart p).2 = p.2 := rfl
  unfold wdKK UnforcedLeray.B0424.rhoE
  rw [h1, h2, Real.log_exp, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp

/-- The pointwise bound for the time-change integrand on `θ > 0`. -/
theorem wd_KK_le (q ν : ℝ) (hq : 1 < q) (g : PS 3 → ℂ) (z : ℝ × Space) (hz : 0 < z.1) :
    wdKK q ν g z ≤ ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) * ‖(ν : ℂ) * g z‖ₑ ^ q := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hzexp : Real.exp (Real.log z.1) = z.1 := Real.exp_log hz
  by_cases habs : |Real.log z.1| < 1
  · have hg : g (Real.exp (Real.log z.1), z.2) = g z := by rw [hzexp]
    have hMd : ‖wdMd ν g (Real.log z.1, z.2)‖ₑ =
        ENNReal.ofReal (Real.exp (3 * Real.log z.1 / 2)) * ‖(ν : ℂ) * g z‖ₑ := by
      unfold wdMd
      rw [if_pos (show |(Real.log z.1, z.2).1| < 1 from habs)]
      dsimp only
      rw [hg, show (ν : ℂ) * ((Real.exp (3 * Real.log z.1 / 2) : ℝ) : ℂ) * g z =
          ((Real.exp (3 * Real.log z.1 / 2) : ℝ) : ℂ) * ((ν : ℂ) * g z) by ring,
        enorm_mul, wd_enorm_real _ (Real.exp_pos _).le]
    have hα : Real.exp (-Real.log z.1) *
        (Real.exp (-(3 * Real.log z.1 / 2)) * Real.exp (3 * Real.log z.1 / 2) ^ q) ≤
          Real.exp (3 * (q - 1) / 2 + 1) := by
      rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : -1 < Real.log z.1 := (abs_lt.mp habs).1
      have h2 : Real.log z.1 < 1 := (abs_lt.mp habs).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr h2.le)]
    dsimp only [wdKK, wdG1]
    rw [hMd, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos (3 * Real.log z.1 / 2)).le hq0.le]
    calc _ = ENNReal.ofReal (Real.exp (-Real.log z.1) *
            (Real.exp (-(3 * Real.log z.1 / 2)) * Real.exp (3 * Real.log z.1 / 2) ^ q)) *
            ‖(ν : ℂ) * g z‖ₑ ^ q := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) * ‖(ν : ℂ) * g z‖ₑ ^ q :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hα) zero_le
  · simp [wdKK, wdG1, wdMd, habs, ENNReal.zero_rpow_of_pos hq0]

/-! ### The component bound -/

/-- **The component bound.** For `q > 1`, `∫⁻ ‖wdComp ν τ₀ g‖ₑ^q ≤ e^{3(q-1)/2+1} ‖ν g‖_q^q`.
Measurability is not needed: each step is a lower-integral identity of a measurable embedding. -/
theorem wd_lintegral_le (q : ℝ) (hq : 1 < q) (ν τ₀ : ℝ) (g : PS 3 → ℂ) :
    ∫⁻ z : ℝ × Space, ‖wdComp ν τ₀ g z‖ₑ ^ q ≤
      ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) *
        eLpNorm (fun X => (ν : ℂ) * g X) (ENNReal.ofReal q) volume ^ q := by
  have hq0 : (0 : ℝ) < q := by linarith
  -- (1) the shift `τ = τ₀ + t`
  have h1 : ∫⁻ z : ℝ × Space, ‖wdComp ν τ₀ g z‖ₑ ^ q =
      ∫⁻ z : ℝ × Space, ‖wdMd ν g (UnforcedLeray.B0424.dilChart z)‖ₑ ^ q := by
    have hsh := UnforcedLeray.B0424.lintegral_shift (-τ₀)
      (fun w => ‖wdMd ν g (UnforcedLeray.B0424.dilChart w)‖ₑ ^ q)
    simp only [neg_add_eq_sub] at hsh
    simp only [wdComp_eq]
    exact hsh
  -- (2) the dilation `x = e^{t/2} y`
  have h2 : ∫⁻ z : ℝ × Space, ‖wdMd ν g (UnforcedLeray.B0424.dilChart z)‖ₑ ^ q =
      ∫⁻ z : ℝ × Space, wdG1 q ν g z := by
    calc ∫⁻ z : ℝ × Space, ‖wdMd ν g (UnforcedLeray.B0424.dilChart z)‖ₑ ^ q
        = ∫⁻ z : ℝ × Space, UnforcedLeray.B0424.rhoD z *
            wdG1 q ν g (UnforcedLeray.B0424.dilChart z) :=
          lintegral_congr fun z => (wd_dil_step q ν g z).symm
      _ = ∫⁻ z : ℝ × Space, wdG1 q ν g z :=
          (UnforcedLeray.B0424.lintegral_dilChart' (wdG1 q ν g)).symm
  -- (3) the time change `θ = e^t`
  have h3 : ∫⁻ z : ℝ × Space, wdG1 q ν g z =
      ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set Space), wdKK q ν g z := by
    rw [UnforcedLeray.B0424.lintegral_expChart' (wdKK q ν g)]
    exact lintegral_congr fun z => (wd_exp_step q ν g z).symm
  -- (4) the pointwise bound on `θ > 0`
  have h4 : ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set Space), wdKK q ν g z ≤
      ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set Space),
        ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) * ‖(ν : ℂ) * g z‖ₑ ^ q := by
    apply setLIntegral_mono' (measurableSet_Ioi.prod MeasurableSet.univ)
    intro z hz
    exact wd_KK_le q ν hq g z hz.1
  -- (5) drop the restriction
  have h5 : ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set Space),
        ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) * ‖(ν : ℂ) * g z‖ₑ ^ q ≤
      ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) *
        ∫⁻ z : ℝ × Space, ‖(ν : ℂ) * g z‖ₑ ^ q := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
  -- (6) identify the integral with the `L^q` norm
  have h6 : ∫⁻ z : ℝ × Space, ‖(ν : ℂ) * g z‖ₑ ^ q =
      eLpNorm (fun X => (ν : ℂ) * g X) (ENNReal.ofReal q) volume ^ q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, one_div, ENNReal.rpow_inv_rpow hq0.ne']
  calc ∫⁻ z : ℝ × Space, ‖wdComp ν τ₀ g z‖ₑ ^ q
      = ∫⁻ z : ℝ × Space, wdG1 q ν g z := by rw [h1, h2]
    _ = ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set Space), wdKK q ν g z := h3
    _ ≤ ∫⁻ z in Ioi (0 : ℝ) ×ˢ (univ : Set Space),
        ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) * ‖(ν : ℂ) * g z‖ₑ ^ q := h4
    _ ≤ ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) *
        ∫⁻ z : ℝ × Space, ‖(ν : ℂ) * g z‖ₑ ^ q := h5
    _ = ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) *
        eLpNorm (fun X => (ν : ℂ) * g X) (ENNReal.ofReal q) volume ^ q := by rw [h6]

/-! ### The leaf -/

/-- **Leaf `PartII-a:F03/4` (the norm of the transported Laplacian).** For `q > 1` there is `K`
(depending only on `q`) with `∫_{τ₀-1}^{τ₀+1}∫ |windowLap(τ,y)|^q dy dτ ≤ K^q Σ_c ‖ν D_c‖_q^q`, for
every family `D` of a.e.-strongly measurable functions. Here `K^q = 3^(q-1) e^{3(q-1)/2+1}`. -/
theorem windowBackNorm : WindowBackNorm := by
  intro q hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hC1 : (0 : ℝ) ≤ (3 : ℝ) ^ (q - 1) := by positivity
  have hCK : (0 : ℝ) ≤ Real.exp (3 * (q - 1) / 2 + 1) := (Real.exp_pos _).le
  have hK1 : (0 : ℝ) ≤ (3 : ℝ) ^ (q - 1) * Real.exp (3 * (q - 1) / 2 + 1) :=
    mul_nonneg hC1 hCK
  have hK0 : (0 : ℝ) ≤ ((3 : ℝ) ^ (q - 1) * Real.exp (3 * (q - 1) / 2 + 1)) ^ (1 / q) :=
    Real.rpow_nonneg hK1 _
  refine ⟨((3 : ℝ) ^ (q - 1) * Real.exp (3 * (q - 1) / 2 + 1)) ^ (1 / q), hK0, ?_⟩
  intro ν τ₀ D hD
  have hKq : ENNReal.ofReal (((3 : ℝ) ^ (q - 1) * Real.exp (3 * (q - 1) / 2 + 1)) ^ (1 / q)) ^ q
      = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hK0 hq0.le, one_div,
      Real.rpow_inv_rpow hK1 hq0.ne', ENNReal.ofReal_mul hC1]
  rw [hKq]
  have hGm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
      ∑ c, ‖wdComp ν τ₀ (D c) z‖ₑ ^ q) volume := by
    exact (Finset.aemeasurable_sum Finset.univ fun c _ =>
      ((wd_aemeasurable ν τ₀ (D c) (hD c)).enorm).pow_const q).const_mul _
  have hpt : ∀ z : ℝ × Space, ‖windowLap ν τ₀ D z‖ₑ ^ q ≤
      ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ∑ c, ‖wdComp ν τ₀ (D c) z‖ₑ ^ q := by
    intro z
    have := wd_enorm_rpow_le q hq.le (windowLap ν τ₀ D z)
    simpa only [windowLap_apply_comp] using this
  calc ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖windowLap ν τ₀ D (τ, y)‖ₑ ^ q
      ≤ ∫⁻ τ, ∫⁻ y, ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, ‖wdComp ν τ₀ (D c) (τ, y)‖ₑ ^ q :=
        le_trans (lintegral_mono fun τ => lintegral_mono fun y => hpt (τ, y))
          (setLIntegral_le_lintegral _ _)
    _ = ∫⁻ z : ℝ × Space, ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, ‖wdComp ν τ₀ (D c) z‖ₑ ^ q :=
        (lintegral_prod _ hGm).symm
    _ = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, ∫⁻ z : ℝ × Space, ‖wdComp ν τ₀ (D c) z‖ₑ ^ q := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro c _
        exact ((wd_aemeasurable ν τ₀ (D c) (hD c)).enorm).pow_const q
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) *
          ∑ c, (ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) *
            eLpNorm (fun X => (ν : ℂ) * D c X) (ENNReal.ofReal q) volume ^ q) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => wd_lintegral_le q hq ν τ₀ (D c)) zero_le
    _ = ENNReal.ofReal ((3 : ℝ) ^ (q - 1)) * ENNReal.ofReal (Real.exp (3 * (q - 1) / 2 + 1)) *
          ∑ c, eLpNorm (fun X => (ν : ℂ) * D c X) (ENNReal.ofReal q) volume ^ q := by
        rw [← Finset.mul_sum, mul_assoc]

end UnforcedLeray.Short.PartIIa
