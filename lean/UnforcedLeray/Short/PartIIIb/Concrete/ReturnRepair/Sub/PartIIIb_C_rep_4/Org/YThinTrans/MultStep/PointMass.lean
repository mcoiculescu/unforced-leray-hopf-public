import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStepOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransMajFacts
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Minkowski
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Phase
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `PartIII-b:C/rep/4/2/org/3/4/1`: the pointwise kernel step `TransMajPointMass`

Source `the November 2 reference manuscript` 3640-3648 (`sep:young`, pointwise,
`sup_{|x| ≥ D} |x|^{-4-j} = D^{-4-j}`), 3669-3679 (`sep:thin-global`, `p = 1`), 3683-3701 (the
stream cutoff; the primitive `∫_r^∞ ρ(ρ - r_o)^{-4} dρ`), 5338-5347 ("The outward stream primitive
has the same norm powers"; "The separated pointwise velocity is at most `P_ν ε² s² N_0`").

Route.  For `a = 0` the gap kernel is bounded by its sup, so the order-`j` dilation integral is at
most `D^{-4-j}` times the `L¹_z` mass of `g` along the dilation.  The mass is put in `L²_τ` by
Minkowski in `z` and `l`, and the phase shift `τ ↦ τ + 2 log l` is removed by periodicity.  The
primitive `outMaj` is bounded pointwise by `(L/D)(D^{-2}/2)` times the same mass, using that
`g` vanishes off the old disk `|z'| ≤ r_o` (so `|(ρ,0,z) - l z'| ≥ ρ - r_o ≥ D` on `ρ ≥ L`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PmStep

/-- The dilation mass `∫_0^1 ∫_z g(τ + 2 log l, z) dz dl` (the `a = 0` part of `sepDom`). -/
def Kint (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, g (τ + 2 * Real.log l) z

theorem sepKd_le_const (j : ℕ) {D : ℝ} (hD : 0 < D) (x : Space) :
    IIIa.sepKd j D x ≤ ENNReal.ofReal (D ^ (-4 - (j : ℝ))) := by
  unfold IIIa.sepKd
  split_ifs with h
  · apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_nonpos hD h
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  · exact zero_le

theorem sepDom_zero_le (j : ℕ) {D : ℝ} (hD : 0 < D) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ)
    (y : Space) :
    IIIa.sepDom 0 j D g τ y ≤ ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * Kint g τ := by
  calc IIIa.sepDom 0 j D g τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (D ^ (-4 - (j : ℝ))) *
          ∫⁻ z : Space, g (τ + 2 * Real.log l) z := by
        unfold IIIa.sepDom
        refine setLIntegral_mono' measurableSet_Ioo (fun l _ => ?_)
        rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_mono fun z => mul_le_mul' (sepKd_le_const j hD _) le_rfl
    _ = ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * Kint g τ := by
        unfold Kint
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem slice_meas {f : ℝ → Space → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) (y : Space) :
    Measurable (fun τ => f τ y) :=
  hf.comp (measurable_id.prodMk measurable_const)

/-- Minkowski in `z` for the normalised phase norm. -/
theorem ltauAt_minkowski_space {P : ℝ} (hP : 0 < P) {F : ℝ → Space → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    IIIa.ltauAt P (fun τ => ∫⁻ z : Space, F τ z) ≤
      ∫⁻ z : Space, IIIa.ltauAt P (fun τ => F τ z) := by
  have hmink := UnforcedLeray.PlanarBS.Conv.lintegral_lintegral_rpow_le
    (μ := volume.restrict (Ioc (0 : ℝ) P)) (ν := (volume : Measure Space))
    (F := fun τ z => F τ z) hF.aemeasurable (p := (2 : ℝ)) (by norm_num)
  have hc : (ENNReal.ofReal P)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hP).ne'
  have hc' : ((ENNReal.ofReal P)⁻¹) ^ (1 / (2 : ℝ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc
  unfold IIIa.ltauAt
  dsimp only
  calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ z : Space, F τ z) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      = ((ENNReal.ofReal P)⁻¹) ^ (1 / (2 : ℝ)) *
          (∫⁻ τ in Ioc (0 : ℝ) P, (∫⁻ z : Space, F τ z) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ ((ENNReal.ofReal P)⁻¹) ^ (1 / (2 : ℝ)) *
          ∫⁻ z : Space, (∫⁻ τ in Ioc (0 : ℝ) P, F τ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' le_rfl hmink
    _ = ∫⁻ z : Space, ((ENNReal.ofReal P)⁻¹) ^ (1 / (2 : ℝ)) *
          (∫⁻ τ in Ioc (0 : ℝ) P, F τ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        (lintegral_const_mul' _ _ hc').symm
    _ = ∫⁻ z : Space, ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, F τ z ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) :=
        lintegral_congr fun z => (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm

/-- The dilation mass is controlled by the phase norms of the slices. -/
theorem ltauAt_Kint_le {P : ℝ} (hP : 0 < P) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hper : ∀ τ z, g (τ + P) z = g τ z) :
    IIIa.ltauAt P (Kint g) ≤ ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
  have hh : Measurable (fun q : (ℝ × ℝ) × Space => g (q.1.2 + 2 * Real.log q.1.1) q.2) := by
    refine hg.comp (Measurable.prodMk ?_ measurable_snd)
    exact (measurable_snd.comp measurable_fst).add
      (measurable_const.mul (measurable_fst.comp measurable_fst).log)
  have hF : Measurable (Function.uncurry fun (l τ : ℝ) =>
      ∫⁻ z : Space, g (τ + 2 * Real.log l) z) := by
    have := hh.lintegral_prod_right' (ν := (volume : Measure Space))
    exact this
  have hperG : ∀ τ, (fun τ => ∫⁻ z : Space, g τ z) (τ + P) = (fun τ => ∫⁻ z : Space, g τ z) τ := by
    intro τ; simp only [hper]
  calc IIIa.ltauAt P (Kint g)
      = IIIa.ltauAt P (fun τ => ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
        rfl
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, IIIa.ltauAt P (fun τ => ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
        IIIa.ltauAt_lintegral_le P hP (fun l τ => ∫⁻ z : Space, g (τ + 2 * Real.log l) z) hF
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
        refine lintegral_mono fun l => ?_
        exact (IIIa.ltauAt_shift P hP (fun τ => ∫⁻ z : Space, g τ z) hperG
          (2 * Real.log l)).le.trans (ltauAt_minkowski_space hP hg)
    _ = ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]

/-- Order-`j` pointwise kernel step in phase norm. -/
theorem ltauAt_sepDom_le (j : ℕ) {P D : ℝ} (hP : 0 < P) (hD : 0 < D) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hper : ∀ τ z, g (τ + P) z = g τ z) (y : Space) :
    IIIa.ltauAt P (fun τ => IIIa.sepDom 0 j D g τ y) ≤
      ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
  calc IIIa.ltauAt P (fun τ => IIIa.sepDom 0 j D g τ y)
      ≤ IIIa.ltauAt P (fun τ => ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * Kint g τ) :=
        IIIa.ltauAt_mono P (fun τ => sepDom_zero_le j hD g τ y)
    _ = ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * IIIa.ltauAt P (Kint g) :=
        IIIa.ltauAt_const_mul P _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) :=
        mul_le_mul' le_rfl (ltauAt_Kint_le hP hg hper)

/-- Gap kernel at order zero, with the sup taken over `|x| ≥ u`. -/
theorem sepKd_zero_le_of_geo {D u : ℝ} (hu : 0 < u) (x : Space) (hx : u ≤ ‖x‖) :
    IIIa.sepKd 0 D x ≤ ENNReal.ofReal (u ^ (-4 : ℝ)) := by
  unfold IIIa.sepKd
  split_ifs with h
  · apply ENNReal.ofReal_le_ofReal
    simp only [Nat.cast_zero, sub_zero]
    exact Real.rpow_le_rpow_of_nonpos hu hx (by norm_num)
  · exact zero_le

/-- The geometric lower bound `|(ρ,0,z) - l w| ≥ ρ - r_o` for `ϱ w ≤ r_o`, `0 ≤ l ≤ 1`. -/
theorem geo_norm_ge (ρ r_o l z : ℝ) (w : Space) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr0 : 0 ≤ r_o)
    (hρ : r_o ≤ ρ) (hw : ϱ w ≤ r_o) :
    ρ - r_o ≤ ‖(!₂[ρ, 0, z] : Space) - l • w‖ := by
  have hs0 : 0 ≤ ϱ w := Real.sqrt_nonneg _
  have hsq : ϱ w ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    unfold ϱ; exact Real.sq_sqrt (by positivity)
  have ha : w 0 ≤ ϱ w := by
    have h := Real.abs_le_sqrt (x := w 0) (y := w 0 ^ 2 + w 1 ^ 2) (by nlinarith [sq_nonneg (w 1)])
    exact (le_abs_self _).trans (by unfold ϱ; exact h)
  have hρ0 : 0 ≤ ρ := by linarith
  have h1 : l * ϱ w ≤ ϱ w := by nlinarith
  have h2 : ρ - r_o ≤ ρ - l * ϱ w := by linarith
  have h3 : 0 ≤ ρ - r_o := by linarith
  have h4 : (ρ - r_o) ^ 2 ≤ (ρ - l * ϱ w) ^ 2 := by nlinarith
  have h6 : 0 ≤ 2 * ρ * l * (ϱ w - w 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) hl0) (sub_nonneg.2 ha)
  have hz : w 0 ^ 2 + w 1 ^ 2 - ϱ w ^ 2 = 0 := by linarith
  have hz2 : l ^ 2 * (w 0 ^ 2 + w 1 ^ 2 - ϱ w ^ 2) = 0 := by rw [hz, mul_zero]
  have e1 : (ρ - l * w 0) ^ 2 + (0 - l * w 1) ^ 2 =
      (ρ - l * ϱ w) ^ 2 + 2 * ρ * l * (ϱ w - w 0) + l ^ 2 * (w 0 ^ 2 + w 1 ^ 2 - ϱ w ^ 2) := by
    ring
  have hnorm : (ρ - r_o) ^ 2 ≤ ∑ i : Fin 3, ‖((!₂[ρ, 0, z] : Space) - l • w) i‖ ^ 2 := by
    rw [Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp
    nlinarith [sq_nonneg (z - l * w 2)]
  calc ρ - r_o = Real.sqrt ((ρ - r_o) ^ 2) := (Real.sqrt_sq h3).symm
    _ ≤ Real.sqrt (∑ i : Fin 3, ‖((!₂[ρ, 0, z] : Space) - l • w) i‖ ^ 2) :=
        Real.sqrt_le_sqrt hnorm
    _ = ‖(!₂[ρ, 0, z] : Space) - l • w‖ := by
        rw [EuclideanSpace.norm_eq]

theorem lintegral_Ioi_rpow_neg3 (r : ℝ) (hr : 0 < r) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ (-3 : ℝ)) =
      ENNReal.ofReal (1 / 2 * r ^ (-2 : ℝ)) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi r) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
      Real.rpow_nonneg (hr.le.trans (le_of_lt hx)) _)]
  rw [integral_Ioi_rpow_of_lt (by norm_num) hr]
  congr 1
  have : (-3 : ℝ) + 1 = -2 := by norm_num
  rw [this]
  ring

theorem sepDom_halfline_zero_le {s L D ρ : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hL : 0 < L)
    (hρ : L ≤ ρ) (g : ℝ → Space → ℝ≥0∞)
    (hgs : ∀ τ (z : Space), s * L < ϱ z → g τ z = 0) (τ z : ℝ) :
    IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z] ≤
      ENNReal.ofReal (((1 - s) * ρ) ^ (-4 : ℝ)) * Kint g τ := by
  have hρ0 : 0 < ρ := hL.trans_le hρ
  have hu : 0 < (1 - s) * ρ := mul_pos (by linarith) hρ0
  calc IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z]
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (((1 - s) * ρ) ^ (-4 : ℝ)) *
          ∫⁻ z' : Space, g (τ + 2 * Real.log l) z' := by
        unfold IIIa.sepDom
        refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
        rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun z' => ?_
        by_cases hg : g (τ + 2 * Real.log l) z' = 0
        · simp [hg]
        · have hw : ϱ z' ≤ s * L := by
            by_contra hcon
            exact hg (hgs _ z' (not_le.1 hcon))
          have hsL : 0 ≤ s * L := mul_nonneg hs0 hL.le
          have hρ' : s * L ≤ ρ := by nlinarith
          have hge := geo_norm_ge ρ (s * L) l z z' hl.1.le hl.2.le hsL hρ' hw
          have h1 : (1 - s) * ρ ≤ ‖(!₂[ρ, 0, z] : Space) - l • z'‖ := by nlinarith
          exact mul_le_mul' (sepKd_zero_le_of_geo hu _ h1) le_rfl
    _ = ENNReal.ofReal (((1 - s) * ρ) ^ (-4 : ℝ)) * Kint g τ := by
        unfold Kint
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem outMaj_zero_le {s L D r : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hL : 0 < L)
    (hr : L ≤ r) (g : ℝ → Space → ℝ≥0∞)
    (hgs : ∀ τ (z : Space), s * L < ϱ z → g τ z = 0) (τ z : ℝ) :
    outMaj 0 D g τ r z ≤
      ENNReal.ofReal ((1 - s) ^ (-4 : ℝ) * (1 / 2) * L ^ (-2 : ℝ)) * Kint g τ := by
  have hr0 : 0 < r := hL.trans_le hr
  have hκ : 0 < 1 - s := by linarith
  unfold outMaj
  calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z]
      ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal ((1 - s) ^ (-4 : ℝ)) *
          (ENNReal.ofReal (ρ ^ (-3 : ℝ)) * Kint g τ) := by
        refine setLIntegral_mono' measurableSet_Ioi (fun ρ hρ => ?_)
        have hρL : L ≤ ρ := hr.trans (le_of_lt hρ)
        have hρ0 : 0 < ρ := hL.trans_le hρL
        refine (mul_le_mul' le_rfl
          (sepDom_halfline_zero_le hs0 hs1 hL hρL g hgs τ z)).trans_eq ?_
        have hreal : ρ * ((1 - s) * ρ) ^ (-4 : ℝ) = (1 - s) ^ (-4 : ℝ) * ρ ^ (-3 : ℝ) := by
          rw [Real.mul_rpow hκ.le hρ0.le]
          have : ρ ^ (-3 : ℝ) = ρ * ρ ^ (-4 : ℝ) := by
            rw [← Real.rpow_one_add' hρ0.le (by norm_num)]; norm_num
          rw [this]; ring
        rw [← mul_assoc, ← ENNReal.ofReal_mul hρ0.le, hreal,
          ENNReal.ofReal_mul (Real.rpow_nonneg hκ.le _), mul_assoc]
    _ = ENNReal.ofReal ((1 - s) ^ (-4 : ℝ)) *
          ((∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ (-3 : ℝ))) * Kint g τ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_mul_const'' (Kint g τ)
          (f := fun a : ℝ => ENNReal.ofReal (a ^ (-3 : ℝ)))
          (μ := volume.restrict (Ioi r))
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).aemeasurable
    _ = ENNReal.ofReal ((1 - s) ^ (-4 : ℝ) * (1 / 2) * r ^ (-2 : ℝ)) * Kint g τ := by
        rw [lintegral_Ioi_rpow_neg3 r hr0, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hκ.le _), mul_assoc]
    _ ≤ ENNReal.ofReal ((1 - s) ^ (-4 : ℝ) * (1 / 2) * L ^ (-2 : ℝ)) * Kint g τ := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hL hr (by norm_num)) (by positivity)

theorem Lpow {ν R : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hR : 0 < R) {e : ℝ} (_he0 : e ≤ 0)
    (he6 : -6 ≤ e) : (R * Real.sqrt ν) ^ e ≤ ν⁻¹ ^ 3 * R ^ e := by
  rw [Real.mul_rpow hR.le (Real.sqrt_nonneg _), mul_comm, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hν.le]
  have h1 : ν ^ (1 / 2 * e) ≤ ν ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
  have h2 : ν ^ (-3 : ℝ) = ν⁻¹ ^ 3 := by
    rw [Real.rpow_neg hν.le, inv_pow]; norm_num
  rw [h2] at h1
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hR.le _)

end PmStep

/-- **The pointwise kernel step from the mass** (source 5346-5347, 3640-3648, 3683-3701). -/
theorem transMajPointMass : TransMajPointMass := by
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ s = Real.sqrt (5 / 6) := by
    refine ⟨_, Real.sqrt_nonneg _, ?_, rfl⟩
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hκ : 0 < 1 - s := by linarith
  have a4 := Real.rpow_nonneg hκ.le (-4 : ℝ)
  have a5 := Real.rpow_nonneg hκ.le (-5 : ℝ)
  refine ⟨(1 - s) ^ (-4 : ℝ) + (1 - s) ^ (-5 : ℝ) + (1 - s) ^ (-4 : ℝ) * (1 / 2), 3,
    by positivity, ?_⟩
  intro ν R P hν hν1 hR1 hP g hgm hgp hgs y
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  by_cases hy : y ∈ streamAnn ν R
  swap
  · have : (fun τ => transMaj ν R g τ y) = fun _ => 0 := by
      funext τ
      simp [transMaj, transMajW, transMajD, transMajS, Set.indicator, hy]
    rw [this]
    simp [IIIa.ltauAt]
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := mul_pos hR hsq
  have hyL : L ≤ ϱ y := hy.1
  have hro : R * Real.sqrt (5 * ν / 6) = s * L := by
    rw [hLdef, hs, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hgs' : ∀ τ (z : Space), s * L < ϱ z → g τ z = 0 := by
    intro τ z hz; exact hgs τ z (by rw [hro]; exact hz)
  have hD : transGap ν R = (1 - s) * L := by
    unfold transGap; rw [hro]; ring
  have hDpos : 0 < transGap ν R := by rw [hD]; positivity
  set A : ℝ := ν⁻¹ ^ 3 * R ^ (-4 : ℝ) with hAdef
  have hA : 0 ≤ A := mul_nonneg (by positivity) (Real.rpow_nonneg hR.le _)
  have hpt : ∀ τ, transMaj ν R g τ y ≤
      ENNReal.ofReal (((1 - s) ^ (-4 : ℝ) + (1 - s) ^ (-5 : ℝ) +
        (1 - s) ^ (-4 : ℝ) * (1 / 2)) * A) * PmStep.Kint g τ := by
    intro τ
    have bW : transMajW ν R g τ y ≤ ENNReal.ofReal ((1 - s) ^ (-4 : ℝ) * A) * PmStep.Kint g τ := by
      simp only [transMajW, Set.indicator_of_mem hy]
      have h0 := PmStep.sepDom_zero_le 0 hDpos g τ y
      simp only [Nat.cast_zero, sub_zero] at h0
      refine h0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      rw [hD, Real.mul_rpow hκ.le hL.le]
      exact mul_le_mul_of_nonneg_left (PmStep.Lpow hν hν1 hR (by norm_num) (by norm_num)) a4
    have bD : transMajD ν R g τ y ≤ ENNReal.ofReal ((1 - s) ^ (-5 : ℝ) * A) * PmStep.Kint g τ := by
      simp only [transMajD, Set.indicator_of_mem hy, transLen]
      have h1 := PmStep.sepDom_zero_le 1 hDpos g τ y
      have e5 : (-4 - ((1 : ℕ) : ℝ) : ℝ) = -5 := by norm_num
      rw [e5] at h1
      refine (mul_le_mul' le_rfl h1).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have e0 : L⁻¹ * L ^ (-5 : ℝ) = L ^ (-6 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hL]; norm_num
      have e3 := PmStep.Lpow hν hν1 hR (e := -6) (by norm_num) (by norm_num)
      have eR : R ^ (-6 : ℝ) ≤ R ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
      rw [hD, Real.mul_rpow hκ.le hL.le]
      calc L⁻¹ * ((1 - s) ^ (-5 : ℝ) * L ^ (-5 : ℝ))
          = (1 - s) ^ (-5 : ℝ) * (L⁻¹ * L ^ (-5 : ℝ)) := by ring
        _ = (1 - s) ^ (-5 : ℝ) * L ^ (-6 : ℝ) := by rw [e0]
        _ ≤ (1 - s) ^ (-5 : ℝ) * A := mul_le_mul_of_nonneg_left
            (e3.trans (mul_le_mul_of_nonneg_left eR (by positivity))) a5
    have bS : transMajS ν R g τ y ≤
        ENNReal.ofReal ((1 - s) ^ (-4 : ℝ) * (1 / 2) * A) * PmStep.Kint g τ := by
      simp only [transMajS, Set.indicator_of_mem hy, transLen]
      have hS := PmStep.outMaj_zero_le (D := transGap ν R) hs0 hs1 hL hyL g hgs' τ (y 2)
      refine (mul_le_mul' le_rfl hS).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have e1 : L⁻¹ ^ 2 * L ^ (-2 : ℝ) = L ^ (-4 : ℝ) := by
        rw [show L⁻¹ ^ 2 = L ^ (-2 : ℝ) by rw [Real.rpow_neg hL.le, inv_pow]; norm_num,
          ← Real.rpow_add hL]
        norm_num
      have e3 := PmStep.Lpow hν hν1 hR (e := -4) (by norm_num) (by norm_num)
      calc L⁻¹ ^ 2 * ((1 - s) ^ (-4 : ℝ) * (1 / 2) * L ^ (-2 : ℝ))
          = (1 - s) ^ (-4 : ℝ) * (1 / 2) * (L⁻¹ ^ 2 * L ^ (-2 : ℝ)) := by ring
        _ = (1 - s) ^ (-4 : ℝ) * (1 / 2) * L ^ (-4 : ℝ) := by rw [e1]
        _ ≤ (1 - s) ^ (-4 : ℝ) * (1 / 2) * A :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
    have hna : 0 ≤ (1 - s) ^ (-4 : ℝ) * A := mul_nonneg a4 hA
    have hnb : 0 ≤ (1 - s) ^ (-5 : ℝ) * A := mul_nonneg a5 hA
    have hnc : 0 ≤ (1 - s) ^ (-4 : ℝ) * (1 / 2) * A := mul_nonneg (by positivity) hA
    unfold transMaj
    refine (add_le_add (add_le_add bW bD) bS).trans_eq ?_
    rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hna hnb,
      ← ENNReal.ofReal_add (add_nonneg hna hnb) hnc]
    congr 2
    ring
  calc IIIa.ltauAt P (fun τ => transMaj ν R g τ y)
      ≤ IIIa.ltauAt P (fun τ =>
          ENNReal.ofReal (((1 - s) ^ (-4 : ℝ) + (1 - s) ^ (-5 : ℝ) +
            (1 - s) ^ (-4 : ℝ) * (1 / 2)) * A) * PmStep.Kint g τ) :=
        IIIa.ltauAt_mono P hpt
    _ = ENNReal.ofReal (((1 - s) ^ (-4 : ℝ) + (1 - s) ^ (-5 : ℝ) +
          (1 - s) ^ (-4 : ℝ) * (1 / 2)) * A) * IIIa.ltauAt P (PmStep.Kint g) :=
        IIIa.ltauAt_const_mul P _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (((1 - s) ^ (-4 : ℝ) + (1 - s) ^ (-5 : ℝ) +
          (1 - s) ^ (-4 : ℝ) * (1 / 2)) * A) *
        ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) :=
        mul_le_mul' le_rfl (PmStep.ltauAt_Kint_le hP hgm hgp)
    _ = _ := by
        congr 2
        rw [hAdef]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
