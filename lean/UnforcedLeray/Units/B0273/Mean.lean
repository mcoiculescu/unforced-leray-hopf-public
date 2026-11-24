import UnforcedLeray.Units.B0581
import UnforcedLeray.Units.B0582
import UnforcedLeray.Units.B0592

/-!
# B0273 helper: the horizontal mean mode

Blueprint unit **B0273** (`unlabeled:4683`), `paper/main.tex` lines 4683–4695. This file treats
the mean (`k = 0`) horizontal mode of a vorticity `ω ∈ X_c` (lines 4688–4693):

* `meanVort c ω` is the horizontal mean `ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq`; slice
  Cauchy–Schwarz gives `∫ w(η) |ω̄(η)|² dη ≤ c⁻¹ ∫_cell w(η) |ω|²` (`lintegral_mul_meanVort_sq_le`).
* `meanHat c ω ξ = ∫ e^{-iηξ} ω̄(η) dη` is the mean-mode Fourier transform `ω̂(0, ξ)`;
  `norm_meanHat_le` is the display of lines 4689–4691,
  `|ω̂(0, ξ)| ≤ |ξ| ∫ |η ω̄(η)| dη`, under zero circulation `∫ ω̄ = 0`.
* `lintegral_moment_le`: the weighted Cauchy bound of line 4693,
  `∫ |η ω̄(η)| dη ≤ c⁻¹ C_m ‖ω‖_{X_c}` with `C_m = (∫_{ℝ²} ⟨y⟩^{-2(m-1)})^{1/2}` (`m > 2`).
* The mean-mode Biot–Savart velocity. For the mean mode `K_c = ∇^⊥Δ^{-1}`, `∇^⊥ = (-∂_η, ∂_q)`,
  is the velocity `(-F(η), 0)` with `F(η) = ∫_{-∞}^η ω̄`, the primitive that vanishes at both
  ends under zero circulation (B0582, `paper/main.tex:9412-9425`): in Fourier variables this is
  `û₁ = i ω̂(0, ξ)/ξ` of line 4691 (with `e^{-iηξ}`). `meanVel c ω` is this field; its weak
  derivatives on the cylinder are `∂_q = 0` and `∂_η = (-ω̄, 0)` (`hasWeakCellDerivV_meanVel_q`,
  `hasWeakCellDerivV_meanVel_eta`), and its `L²(cell)` norms are bounded by `2‖ω‖_{X_c}` and
  `‖ω‖_{X_c}` (Hardy's inequality, B0582), uniformly in `c`.

`HasWeakCellDerivV` is the weak cylinder derivative of B0579 (`HasWeakCellDeriv`) for
`ℂ²`-valued fields (the velocity space `Vel` of B0581).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal Real ComplexConjugate InnerProductSpace

namespace UnforcedLeray.B0273

open UnforcedLeray.B0579 (Plane cell X IsCylTest pd)
open UnforcedLeray.B0581 (qInt μq cellVol cellVol_eq Vel)

/-! ### Weak derivatives of `ℂ²`-valued fields on the cylinder -/

/-- Weak cylinder derivative of a vector field (B0579 `HasWeakCellDeriv`, componentwise):
`g = ∂_j u` when `∫_cell (∂_j φ) u = -∫_cell φ g` for every cylinder test function `φ`. -/
def HasWeakCellDerivV (c : ℝ) (j : Fin 2) (u g : Plane → Vel) : Prop :=
  ∀ φ : Plane → ℝ, IsCylTest c φ →
    ∫ x in cell c, (pd j φ x : ℂ) • u x = -∫ x in cell c, (φ x : ℂ) • g x

/-- The unit vector `e₁ = (1, 0) ∈ ℂ²`. -/
def e1 : Vel := EuclideanSpace.single 0 1

theorem norm_smul_e1 (a : ℝ) : ‖(a : ℂ) • e1‖ = ‖a‖ := by
  rw [norm_smul, e1, PiLp.norm_single, norm_one, mul_one, Complex.norm_real]

theorem enorm_smul_e1 (a : ℝ) : ‖(a : ℂ) • e1‖ₑ = ‖a‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_smul_e1]

theorem integral_smul_e1 {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) :
    ∫ x, (g x : ℂ) • e1 ∂μ = ((∫ x, g x ∂μ : ℝ) : ℂ) • e1 := by
  rw [integral_smul_const, integral_complex_ofReal]

/-- `‖f‖²_{L²} = ∫ ‖f‖²` in `[0, ∞]`. -/
theorem eLpNorm_two_sq' {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    (f : α → E) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact B0592.ennreal_rpow_half_sq _

/-! ### The horizontal mean `ω̄` -/

/-- **The horizontal mean** `ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq` (`paper/main.tex:4689`). -/
def meanVort (c : ℝ) (ω : Plane → ℝ) (η : ℝ) : ℝ := c⁻¹ * ∫ q in qInt c, ω (q, η)

theorem measurable_meanVort (c : ℝ) {ω : Plane → ℝ} (hω : Measurable ω) :
    Measurable (meanVort c ω) :=
  ((hω.stronglyMeasurable.integral_prod_left' (μ := μq c)).measurable).const_mul _

theorem volume_qInt (c : ℝ) : volume (qInt c) = ENNReal.ofReal c := by
  rw [qInt, Real.volume_Ico]
  congr 1
  ring

/-- Slice Cauchy–Schwarz: `|ω̄(η)|² ≤ c⁻¹ ∫_{-c/2}^{c/2} |ω(q, η)|² dq`. -/
theorem enorm_meanVort_sq_le {c : ℝ} (hc : 0 < c) {ω : Plane → ℝ} (hω : Measurable ω) (η : ℝ) :
    ‖meanVort c ω η‖ₑ ^ 2 ≤ ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2 := by
  have hsl : Measurable fun q : ℝ => ω (q, η) := hω.comp (measurable_id.prodMk measurable_const)
  have h1 : ‖meanVort c ω η‖ₑ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ := by
    rw [meanVort, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.2 hc.le)]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  have h2 : (∫⁻ q in qInt c, ‖ω (q, η)‖ₑ) ^ 2 ≤
      ENNReal.ofReal c * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2 := by
    have := B0592.lintegral_mul_sq_le (μ := volume.restrict (qInt c)) (f := fun _ => (1 : ℝ≥0∞))
      (g := fun q => ‖ω (q, η)‖ₑ) aemeasurable_const hsl.enorm.aemeasurable
    simpa only [one_mul, one_pow, lintegral_const, Measure.restrict_apply_univ, volume_qInt]
      using this
  calc ‖meanVort c ω η‖ₑ ^ 2 ≤ (ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ) ^ 2 :=
        pow_le_pow_left₀ (zero_le) h1 2
    _ = ENNReal.ofReal c⁻¹ ^ 2 * (∫⁻ q in qInt c, ‖ω (q, η)‖ₑ) ^ 2 := mul_pow _ _ _
    _ ≤ ENNReal.ofReal c⁻¹ ^ 2 * (ENNReal.ofReal c * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2) := by
        gcongr
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_pow (inv_nonneg.2 hc.le),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- Tonelli on the cell for a weight depending on `η` only. -/
theorem lintegral_cell_eq {c : ℝ} (G : Plane → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x in cell c, G x = ∫⁻ η, ∫⁻ q in qInt c, G (q, η) := by
  rw [show volume.restrict (cell c) = cellVol c from rfl, cellVol_eq,
    lintegral_prod_symm _ hG.aemeasurable]

/-- **Weighted slice bound**: `∫ w(η)|ω̄(η)|² dη ≤ c⁻¹ ∫_cell w(η)|ω(q, η)|²`. -/
theorem lintegral_mul_meanVort_sq_le {c : ℝ} (hc : 0 < c) {ω : Plane → ℝ} (hω : Measurable ω)
    (w : ℝ → ℝ) (hw : Measurable w) :
    ∫⁻ η, ENNReal.ofReal (w η) * ‖meanVort c ω η‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ x in cell c, ENNReal.ofReal (w x.2) * ‖ω x‖ₑ ^ 2 := by
  have hG : Measurable fun x : Plane => ENNReal.ofReal (w x.2) * ‖ω x‖ₑ ^ 2 :=
    (ENNReal.measurable_ofReal.comp (hw.comp measurable_snd)).mul (hω.enorm.pow_const 2)
  rw [lintegral_cell_eq _ hG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  calc ENNReal.ofReal (w η) * ‖meanVort c ω η‖ₑ ^ 2
      ≤ ENNReal.ofReal (w η) * (ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2) := by
        gcongr
        exact enorm_meanVort_sq_le hc hω η
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ENNReal.ofReal (w η) * ‖ω (q, η)‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring

/-! ### Vorticities in `X_c` -/

theorem measurable_X {c m : ℝ} (ω : X c m) : Measurable (ω : Plane → ℝ) :=
  (Lp.stronglyMeasurable ω).measurable

theorem one_le_jb (y : Plane) : 1 ≤ B0579.jb y := by
  unfold B0579.jb
  nlinarith [sq_nonneg y.1, sq_nonneg y.2]

/-- `∫_cell v |ω|² ≤ ‖ω‖²_{X_m}` for every weight `v ≤ ⟨y⟩^{2m}`. -/
theorem lintegral_weight_le {c m : ℝ} (ω : X c m) (v : Plane → ℝ)
    (hv : ∀ y, v y ≤ B0579.jb y ^ m) :
    ∫⁻ y in cell c, ENNReal.ofReal (v y) * ‖ω y‖ₑ ^ 2 ≤ ENNReal.ofReal ‖ω‖ ^ 2 := by
  rw [B0592.ofReal_norm_X_sq]
  refine lintegral_mono fun y => ?_
  have h0 : 0 ≤ B0579.jb y ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
  rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0, ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos y).le]
  gcongr
  convert hv y using 2
  push_cast
  ring

/-- For `m ≥ 1`: `‖⟨η⟩ ω̄‖²_{L²(ℝ)} ≤ c⁻¹ ‖ω‖²_{X_m}`. -/
theorem lintegral_jb_meanVort_sq_le {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (ω : X c m) :
    ∫⁻ η, ‖B0582.jb η * meanVort c ω η‖ₑ ^ 2 ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal ‖ω‖ ^ 2 := by
  have hpt : ∀ η, ‖B0582.jb η * meanVort c ω η‖ₑ ^ 2 =
      ENNReal.ofReal (1 + η ^ 2) * ‖meanVort c ω η‖ₑ ^ 2 := by
    intro η
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal (B0582.jb_pos η).le,
      ← ENNReal.ofReal_pow (B0582.jb_pos η).le, B0582.jb_sq]
  simp_rw [hpt]
  refine (lintegral_mul_meanVort_sq_le hc (measurable_X ω) (fun η => 1 + η ^ 2)
    (by fun_prop)).trans ?_
  gcongr
  refine lintegral_weight_le ω _ fun y => ?_
  have h1 : 1 + y.2 ^ 2 ≤ B0579.jb y := by unfold B0579.jb; nlinarith [sq_nonneg y.1]
  exact h1.trans (Real.self_le_rpow_of_one_le (one_le_jb y) hm)

/-- For `m ≥ 0`: `‖ω̄‖²_{L²(ℝ)} ≤ c⁻¹ ‖ω‖²_{L²(cell)} ≤ c⁻¹ ‖ω‖²_{X_m}`. -/
theorem lintegral_meanVort_sq_le {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (ω : X c m) :
    ∫⁻ η, ‖meanVort c ω η‖ₑ ^ 2 ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal ‖ω‖ ^ 2 := by
  have h := lintegral_mul_meanVort_sq_le hc (measurable_X ω) (fun _ => (1 : ℝ)) measurable_const
  simp only [ENNReal.ofReal_one, one_mul] at h
  refine h.trans ?_
  gcongr
  exact B0592.lintegral_cell_sq_le hm c ω

theorem memLp_jb_meanVort {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (ω : X c m) :
    MemLp (fun η => B0582.jb η * meanVort c ω η) 2 volume := by
  refine ⟨(B0582.continuous_jb.measurable.mul
    (measurable_meanVort c (measurable_X ω))).aestronglyMeasurable, ?_⟩
  have h := eLpNorm_two_sq' (μ := (volume : Measure ℝ)) (fun η => B0582.jb η * meanVort c ω η)
  have hlt : eLpNorm (fun η => B0582.jb η * meanVort c ω η) 2 volume ^ 2 < ∞ := by
    rw [h]
    exact (lintegral_jb_meanVort_sq_le hc hm ω).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
  exact (ENNReal.pow_lt_top_iff.1 hlt).resolve_right two_ne_zero

/-- For `m > 1`, `ω ∈ X_m` is integrable on the cell (`B0592.lintegral_cell_le`). -/
theorem integrableOn_cell_X {c m : ℝ} (hm : 1 < m) (ω : X c m) :
    IntegrableOn (ω : Plane → ℝ) (cell c) :=
  ⟨(measurable_X ω).aestronglyMeasurable,
    (B0592.lintegral_cell_le c ω).trans_lt
      (ENNReal.mul_lt_top (B0592.weightConst_lt_top hm) ENNReal.ofReal_lt_top)⟩

/-- Zero circulation transfers to the mean: `∫ ω̄ = c⁻¹ ∫_cell ω`. -/
theorem integral_meanVort {c m : ℝ} (hm : 1 < m) (ω : X c m) :
    ∫ η, meanVort c ω η = c⁻¹ * ∫ x in cell c, ω x := by
  have hint := integrableOn_cell_X hm ω
  unfold IntegrableOn at hint
  rw [show volume.restrict (cell c) = cellVol c from rfl, cellVol_eq] at hint ⊢
  rw [integral_prod_symm _ hint, ← integral_const_mul]
  rfl

theorem integral_meanVort_eq_zero {c m : ℝ} (hm : 1 < m) (ω : X c m)
    (hcirc : ∫ x in cell c, ω x = 0) : ∫ η, meanVort c ω η = 0 := by
  rw [integral_meanVort hm ω, hcirc, mul_zero]

theorem integrable_meanVort {c m : ℝ} (hc : 0 < c) (hm : 1 < m) (ω : X c m) :
    Integrable (meanVort c ω) :=
  B0582.integrable_of_weighted (memLp_jb_meanVort hc hm.le ω)

/-! ### The mean-mode Fourier transform (`paper/main.tex:4689-4692`) -/

/-- **The mean-mode Fourier transform** `ω̂(0, ξ) = ∫ e^{-iηξ} ω̄(η) dη`
(`paper/main.tex:4690`). -/
def meanHat (c : ℝ) (ω : Plane → ℝ) (ξ : ℝ) : ℂ :=
  ∫ η, Complex.exp (I * ((-(η * ξ) : ℝ) : ℂ)) * (meanVort c ω η : ℂ)

/-- **The display of `paper/main.tex:4689-4691`**: under zero circulation `∫ ω̄ = 0`,
`|ω̂(0, ξ)| ≤ |ξ| ∫ |η ω̄(η)| dη`, because `|e^{-iηξ} - 1| ≤ |η ξ|`. The integrability hypotheses
make both integrals genuine (no Bochner junk value); they hold for `ω ∈ X_c`
(`integrable_meanVort`, `integrable_moment`). -/
theorem norm_meanHat_le {c : ℝ} {ω : Plane → ℝ} (hω : Measurable ω)
    (hint : Integrable (meanVort c ω)) (hcirc : ∫ η, meanVort c ω η = 0)
    (hmom : Integrable fun η => η * meanVort c ω η) (ξ : ℝ) :
    ‖meanHat c ω ξ‖ ≤ |ξ| * ∫ η, |η * meanVort c ω η| := by
  have hf : Measurable (meanVort c ω) := measurable_meanVort c hω
  have he : Continuous fun η : ℝ => Complex.exp (I * ((-(η * ξ) : ℝ) : ℂ)) := by fun_prop
  have hfc : Integrable fun η => (meanVort c ω η : ℂ) := hint.ofReal
  have h1 : Integrable fun η => Complex.exp (I * ((-(η * ξ) : ℝ) : ℂ)) * (meanVort c ω η : ℂ) := by
    refine hint.norm.mono' (he.measurable.mul (Complex.measurable_ofReal.comp hf)).aestronglyMeasurable
      (Eventually.of_forall fun η => ?_)
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real]
  have hsplit : meanHat c ω ξ =
      ∫ η, (Complex.exp (I * ((-(η * ξ) : ℝ) : ℂ)) - 1) * (meanVort c ω η : ℂ) := by
    have h0 : ∫ η, (meanVort c ω η : ℂ) = 0 := by rw [integral_complex_ofReal, hcirc]; simp
    simp_rw [sub_mul, one_mul]
    rw [integral_sub h1 hfc, h0, sub_zero]
    rfl
  rw [hsplit, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hmom.norm.const_mul _) (Eventually.of_forall fun η => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hb : ‖Complex.exp (I * ((-(η * ξ) : ℝ) : ℂ)) - 1‖ ≤ |η| * |ξ| := by
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
  calc ‖Complex.exp (I * ((-(η * ξ) : ℝ) : ℂ)) - 1‖ * |meanVort c ω η|
      ≤ |η| * |ξ| * |meanVort c ω η| := by gcongr
    _ = |ξ| * (|η| * |meanVort c ω η|) := by ring

/-! ### The weighted Cauchy bound of the moment (`paper/main.tex:4693`) -/

theorem enorm_meanVort_le {c : ℝ} (hc : 0 < c) (ω : Plane → ℝ) (η : ℝ) :
    ‖meanVort c ω η‖ₑ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ := by
  rw [meanVort, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.2 hc.le)]
  gcongr
  exact enorm_integral_le_lintegral_enorm _

/-- Cauchy–Schwarz against `⟨y⟩^{-m}`: `∫_cell |η ω| ≤ C_m ‖ω‖_{X_m}`,
`C_m = (∫_{ℝ²} ⟨y⟩^{-2(m-1)})^{1/2}` (`B0592.weightConst (m - 1)`, finite for `m > 2`). -/
theorem lintegral_cell_snd_mul_le {c m : ℝ} (ω : X c m) :
    ∫⁻ y in cell c, ‖y.2 * ω y‖ₑ ≤ B0592.weightConst (m - 1) * ENNReal.ofReal ‖ω‖ := by
  have hω := measurable_X ω
  have hpt : ∀ y : Plane, ‖y.2 * ω y‖ₑ =
      ENNReal.ofReal (|y.2| * B0579.jb y ^ (-m / 2)) * ‖B0579.jb y ^ (m / 2) * ω y‖ₑ := by
    intro y
    have hj := B0579.jb_pos y
    rw [enorm_mul, enorm_mul, Real.enorm_eq_ofReal (Real.rpow_nonneg hj.le _), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.rpow_add hj,
      show -m / 2 + m / 2 = 0 by ring, Real.rpow_zero, mul_one, Real.enorm_eq_ofReal_abs]
  have hF : Measurable fun y : Plane => ENNReal.ofReal (|y.2| * B0579.jb y ^ (-m / 2)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.comp continuous_snd).mul (B0579.continuous_jb_rpow _)).measurable
  have hG : Measurable fun y : Plane => ‖B0579.jb y ^ (m / 2) * ω y‖ₑ :=
    ((B0579.continuous_jb_rpow _).measurable.mul hω).enorm
  have hcs := B0592.lintegral_mul_sq_le (μ := volume.restrict (cell c)) hF.aemeasurable
    hG.aemeasurable
  have hF2 : ∫⁻ y in cell c, ENNReal.ofReal (|y.2| * B0579.jb y ^ (-m / 2)) ^ 2 ≤
      B0592.weightConst (m - 1) ^ 2 := by
    rw [B0592.weightConst, B0592.ennreal_rpow_half_sq]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
    have hj := B0579.jb_pos y
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (|y.2| * B0579.jb y ^ (-m / 2)) ^ 2 = y.2 ^ 2 * B0579.jb y ^ (-m) := by
      rw [mul_pow, sq_abs, ← Real.rpow_mul_natCast hj.le]
      congr 2
      push_cast
      ring
    have e2 : B0579.jb y ^ (-(m - 1)) = B0579.jb y * B0579.jb y ^ (-m) := by
      rw [show -(m - 1) = 1 + -m by ring, Real.rpow_add hj, Real.rpow_one]
    rw [e1, e2]
    have : y.2 ^ 2 ≤ B0579.jb y := by unfold B0579.jb; nlinarith [sq_nonneg y.1]
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hj.le _)
  rw [lintegral_congr hpt]
  apply B0592.ennreal_le_of_sq_le_sq
  calc (∫⁻ y in cell c, ENNReal.ofReal (|y.2| * B0579.jb y ^ (-m / 2)) *
        ‖B0579.jb y ^ (m / 2) * ω y‖ₑ) ^ 2
      ≤ (∫⁻ y in cell c, ENNReal.ofReal (|y.2| * B0579.jb y ^ (-m / 2)) ^ 2) *
          ∫⁻ y in cell c, ‖B0579.jb y ^ (m / 2) * ω y‖ₑ ^ 2 := hcs
    _ ≤ B0592.weightConst (m - 1) ^ 2 * ENNReal.ofReal ‖ω‖ ^ 2 := by
        rw [← B0592.ofReal_norm_X_sq]
        gcongr
    _ = (B0592.weightConst (m - 1) * ENNReal.ofReal ‖ω‖) ^ 2 := by ring

/-- **Weighted Cauchy bound of the moment** (`paper/main.tex:4693`):
`∫ |η ω̄(η)| dη ≤ c⁻¹ C_m ‖ω‖_{X_c}`, `C_m = B0592.weightConst (m - 1)` independent of `c`. -/
theorem lintegral_moment_le {c m : ℝ} (hc : 0 < c) (ω : X c m) :
    ∫⁻ η, ‖η * meanVort c ω η‖ₑ ≤
      ENNReal.ofReal c⁻¹ * (B0592.weightConst (m - 1) * ENNReal.ofReal ‖ω‖) := by
  have hω := measurable_X ω
  have hG : Measurable fun x : Plane => ‖x.2 * ω x‖ₑ := (measurable_snd.mul hω).enorm
  refine le_trans (b := ENNReal.ofReal c⁻¹ * ∫⁻ x in cell c, ‖x.2 * ω x‖ₑ) ?_
    (by gcongr; exact lintegral_cell_snd_mul_le ω)
  rw [lintegral_cell_eq _ hG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  calc ‖η * meanVort c ω η‖ₑ = ‖η‖ₑ * ‖meanVort c ω η‖ₑ := enorm_mul _ _
    _ ≤ ‖η‖ₑ * (ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ) := by
        gcongr
        exact enorm_meanVort_le hc ω η
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖(q, η).2 * ω (q, η)‖ₑ := by
        simp only [enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        ring

theorem integrable_moment {c m : ℝ} (hc : 0 < c) (hm : 2 < m) (ω : X c m) :
    Integrable fun η => η * meanVort c ω η :=
  ⟨(measurable_id.mul (measurable_meanVort c (measurable_X ω))).aestronglyMeasurable,
    (lintegral_moment_le hc ω).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (B0592.weightConst_lt_top (by linarith)) ENNReal.ofReal_lt_top))⟩

/-- The moment bound for the real integral: `∫ |η ω̄| ≤ c⁻¹ C_m ‖ω‖_{X_c}`. -/
theorem integral_moment_le {c m : ℝ} (hc : 0 < c) (hm : 2 < m) (ω : X c m) :
    ∫ η, |η * meanVort c ω η| ≤
      c⁻¹ * ((B0592.weightConst (m - 1)).toReal * ‖ω‖) := by
  have hfin : B0592.weightConst (m - 1) ≠ ∞ := (B0592.weightConst_lt_top (by linarith)).ne
  have h := lintegral_moment_le hc ω
  simp_rw [← Real.norm_eq_abs]
  rw [integral_norm_eq_lintegral_enorm (f := fun η => η * meanVort c ω η)
    (measurable_id.mul (measurable_meanVort c (measurable_X ω))).aestronglyMeasurable]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le),
    ENNReal.toReal_ofReal (norm_nonneg _)] at this

/-! ### The mean-mode velocity `(-F(η), 0)` -/

/-- The primitive `F(η) = ∫_{-∞}^η ω̄` of the mean vorticity (B0582). -/
def meanPrim (c : ℝ) (ω : Plane → ℝ) : ℝ → ℝ := B0582.zeroModePrimitive (meanVort c ω)

/-- **The mean-mode Biot–Savart velocity** `K_c ω̄ = (-F(η), 0)`: `∇^⊥ψ` for the stream function
`ψ'' = ω̄`, `ψ' = F → 0` at both ends (`paper/main.tex:4688-4692`; in Fourier variables
`û₁ = i ω̂(0, ξ)/ξ`). -/
def meanVel (c : ℝ) (ω : Plane → ℝ) (x : Plane) : Vel := ((-meanPrim c ω x.2 : ℝ) : ℂ) • e1

/-- Its `η`-derivative `(-ω̄(η), 0)` (so `curl = ∂_q u₂ - ∂_η u₁ = ω̄` and `div = 0`). -/
def meanVelDeta (c : ℝ) (ω : Plane → ℝ) (x : Plane) : Vel := ((-meanVort c ω x.2 : ℝ) : ℂ) • e1

/-- Tonelli on the cell for a function of `η` only. -/
theorem lintegral_cell_snd {c : ℝ} (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in cell c, g x.2 = ENNReal.ofReal c * ∫⁻ η, g η := by
  rw [lintegral_cell_eq (fun x => g x.2) (hg.comp measurable_snd)]
  simp only [lintegral_const, Measure.restrict_apply_univ, volume_qInt]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

theorem lintegral_cellVol_snd {c : ℝ} (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x.2 ∂cellVol c = ENNReal.ofReal c * ∫⁻ η, g η :=
  lintegral_cell_snd g hg

/-- **`L²` bound of the mean-mode velocity** (Hardy, B0582): for `ω ∈ X_m`, `m > 1`, with zero
circulation, `(-F, 0) ∈ L²(cell)` and `‖(-F, 0)‖_{L²(cell)} ≤ 2‖ω‖_{X_m}`, uniformly in `c`. -/
theorem meanVel_memLp_and_le {c m : ℝ} (hc : 0 < c) (hm : 1 < m) (ω : X c m)
    (hcirc : ∫ x in cell c, ω x = 0) :
    Continuous (meanPrim c ω) ∧ MemLp (meanVel c ω) 2 (cellVol c) ∧
      eLpNorm (meanVel c ω) 2 (cellVol c) ≤ ENNReal.ofReal (2 * ‖ω‖) := by
  have hj := memLp_jb_meanVort hc hm.le ω
  have hmean := integral_meanVort_eq_zero hm ω hcirc
  obtain ⟨hint, -, -, hFm, hFle⟩ := B0582.hardy_zero_mode (meanVort c ω) hj hmean
  have hFc : Continuous (meanPrim c ω) := B0582.continuous_zeroModePrimitive hint
  have hvc : Continuous (meanVel c ω) :=
    (Complex.continuous_ofReal.comp ((hFc.comp continuous_snd).neg)).smul continuous_const
  have hsq : eLpNorm (meanVel c ω) 2 (cellVol c) ^ 2 ≤ ENNReal.ofReal (2 * ‖ω‖) ^ 2 := by
    rw [eLpNorm_two_sq']
    have hpt : ∀ x : Plane, ‖meanVel c ω x‖ₑ ^ 2 = ‖meanPrim c ω x.2‖ₑ ^ 2 := by
      intro x
      rw [meanVel, enorm_smul_e1, enorm_neg]
    simp_rw [hpt]
    rw [lintegral_cellVol_snd (fun η => ‖meanPrim c ω η‖ₑ ^ 2) (hFc.measurable.enorm.pow_const 2),
      ← eLpNorm_two_sq']
    calc ENNReal.ofReal c * eLpNorm (meanPrim c ω) 2 volume ^ 2
        ≤ ENNReal.ofReal c * (2 * eLpNorm (fun η => B0582.jb η * meanVort c ω η) 2 volume) ^ 2 := by
          gcongr
          exact hFle
      _ = ENNReal.ofReal c * 4 * ∫⁻ η, ‖B0582.jb η * meanVort c ω η‖ₑ ^ 2 := by
          rw [mul_pow, eLpNorm_two_sq']
          norm_num
          ring
      _ ≤ ENNReal.ofReal c * 4 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal ‖ω‖ ^ 2) := by
          gcongr
          exact lintegral_jb_meanVort_sq_le hc hm.le ω
      _ = ENNReal.ofReal (2 * ‖ω‖) ^ 2 := by
          rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (by positivity),
            show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
            ← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          ring
  have hle := B0592.ennreal_le_of_sq_le_sq hsq
  exact ⟨hFc, ⟨hvc.aestronglyMeasurable, hle.trans_lt ENNReal.ofReal_lt_top⟩, hle⟩

/-- `‖(-ω̄, 0)‖_{L²(cell)} ≤ ‖ω‖_{L²(cell)} ≤ ‖ω‖_{X_m}` (`m ≥ 0`). -/
theorem meanVelDeta_memLp_and_le {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (ω : X c m) :
    MemLp (meanVelDeta c ω) 2 (cellVol c) ∧
      eLpNorm (meanVelDeta c ω) 2 (cellVol c) ≤ ENNReal.ofReal ‖ω‖ := by
  have hf := measurable_meanVort c (measurable_X ω)
  have hvm : Measurable (meanVelDeta c ω) :=
    (Complex.measurable_ofReal.comp ((hf.comp measurable_snd).neg)).smul measurable_const
  have hsq : eLpNorm (meanVelDeta c ω) 2 (cellVol c) ^ 2 ≤ ENNReal.ofReal ‖ω‖ ^ 2 := by
    rw [eLpNorm_two_sq']
    have hpt : ∀ x : Plane, ‖meanVelDeta c ω x‖ₑ ^ 2 = ‖meanVort c ω x.2‖ₑ ^ 2 := by
      intro x
      rw [meanVelDeta, enorm_smul_e1, enorm_neg]
    simp_rw [hpt]
    rw [lintegral_cellVol_snd (fun η => ‖meanVort c ω η‖ₑ ^ 2) (hf.enorm.pow_const 2)]
    calc ENNReal.ofReal c * ∫⁻ η, ‖meanVort c ω η‖ₑ ^ 2
        ≤ ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal ‖ω‖ ^ 2) := by
          gcongr
          exact lintegral_meanVort_sq_le hc hm ω
      _ = ENNReal.ofReal ‖ω‖ ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
            one_mul]
  have hle := B0592.ennreal_le_of_sq_le_sq hsq
  exact ⟨⟨hvm.aestronglyMeasurable, hle.trans_lt ENNReal.ofReal_lt_top⟩, hle⟩

/-! ### Weak derivatives of the mean-mode velocity -/

theorem IsCylTest.exists_bound_cell {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ cell c, |φ x| ≤ K := by
  obtain ⟨R, hR⟩ := hφ.band
  obtain ⟨K, hK⟩ := B0579.exists_bound_cell_band c R hφ.continuous
  refine ⟨max K 0, le_max_right _ _, fun x hx => ?_⟩
  by_cases hxR : |x.2| ≤ R
  · exact (hK x hx hxR).trans (le_max_left _ _)
  · rw [hR x (not_le.1 hxR), abs_zero]
    exact le_max_right _ _

/-- `∫_{-c/2}^{c/2} ∂_q φ(q, η) dq = 0` by periodicity. -/
theorem integral_qInt_pd_zero {c : ℝ} (hc : 0 < c) {φ : Plane → ℝ} (hφ : IsCylTest c φ)
    (η : ℝ) : ∫ q in qInt c, pd 0 φ (q, η) = 0 := by
  have hle : -(c / 2) ≤ c / 2 := by linarith
  rw [qInt, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _ => B0579.hasDerivAt_fst hφ.differentiable q η)
      (((hφ.pd 0).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
  have h := hφ.periodic (-(c / 2), η)
  rw [show -(c / 2) + c = c / 2 by ring] at h
  rw [h, sub_self]

/-- `∫_cell (∂_q φ) G(η) = 0` for continuous `G`. -/
theorem integral_pd_zero_mul_snd {c : ℝ} (hc : 0 < c) {φ : Plane → ℝ} (hφ : IsCylTest c φ)
    {G : ℝ → ℝ} (hG : Continuous G) : ∫ x in cell c, pd 0 φ x * G x.2 = 0 := by
  obtain ⟨R, hR⟩ := (hφ.pd 0).vanish
  have hint : IntegrableOn (fun x => pd 0 φ x * G x.2) (cell c) :=
    B0579.integrableOn_cell_of_continuous ((hφ.pd 0).continuous.mul (hG.comp continuous_snd))
      (B0579.isCompact_box c R) (fun x hx hxK => by simp [hR x hx hxK])
  unfold IntegrableOn at hint
  rw [show volume.restrict (cell c) = cellVol c from rfl, cellVol_eq] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun η => ?_)).trans (integral_zero _ _)
  simp only
  rw [integral_mul_const, integral_qInt_pd_zero hc hφ η, zero_mul]

/-- One-dimensional integration by parts against the primitive `F = ∫_{-∞}^η f`:
`∫ ψ' F = -∫ ψ f` for `ψ ∈ C¹_c(ℝ)` and `f ∈ L¹(ℝ)` (Fubini; `F` need not be differentiable). -/
theorem integral_deriv_mul_primitive {f : ℝ → ℝ} (hf : Integrable f) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ t, deriv ψ t * B0582.zeroModePrimitive f t = -∫ t, ψ t * f t := by
  have hd : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hdi : Integrable (deriv ψ) := hd.integrable_of_hasCompactSupport hψc.deriv
  set S : Set (ℝ × ℝ) := {z | z.2 ≤ z.1} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_snd measurable_fst
  set H : ℝ × ℝ → ℝ := S.indicator (fun z => deriv ψ z.1 * f z.2) with hHdef
  have hH : Integrable H ((volume : Measure ℝ).prod volume) := (hdi.mul_prod hf).indicator hS
  have e1 : ∀ t, deriv ψ t * B0582.zeroModePrimitive f t = ∫ y, H (t, y) := by
    intro t
    rw [B0582.zeroModePrimitive, ← integral_indicator measurableSet_Iic, ← integral_const_mul]
    congr 1
    funext y
    simp only [hHdef, hSdef, Set.indicator, Set.mem_Iic, Set.mem_ofPred_eq]
    split_ifs <;> simp
  have e2 : ∀ y, ∫ t, H (t, y) = -(ψ y * f y) := by
    intro y
    have : (fun t => H (t, y)) = (Ici y).indicator (fun t => deriv ψ t * f y) := by
      funext t
      simp only [hHdef, hSdef, Set.indicator, Set.mem_Ici, Set.mem_ofPred_eq]
    rw [this, integral_indicator measurableSet_Ici, integral_mul_const,
      integral_Ici_eq_integral_Ioi, hψc.integral_Ioi_deriv_eq hψ y]
    ring
  calc ∫ t, deriv ψ t * B0582.zeroModePrimitive f t = ∫ t, ∫ y, H (t, y) := by simp_rw [e1]
    _ = ∫ z, H z ∂((volume : Measure ℝ).prod volume) := (integral_prod H hH).symm
    _ = ∫ y, ∫ t, H (t, y) := integral_prod_symm H hH
    _ = ∫ y, -(ψ y * f y) := by simp_rw [e2]
    _ = -∫ t, ψ t * f t := integral_neg _

/-- `φ(x) f(η)` is integrable on the cell for a cylinder test `φ` and `f ∈ L¹(ℝ)`. -/
theorem integrable_test_mul_snd {c : ℝ} {φ : Plane → ℝ} (hφ : IsCylTest c φ) {f : ℝ → ℝ}
    (hf : Integrable f) : Integrable (fun x : Plane => φ x * f x.2) (cellVol c) := by
  obtain ⟨K, -, hK⟩ := IsCylTest.exists_bound_cell hφ
  have hb : Integrable (fun z : Plane => K * |f z.2|) (cellVol c) := by
    rw [cellVol_eq]
    exact (integrable_const K).mul_prod hf.norm
  refine hb.mono' (hφ.continuous.aestronglyMeasurable.mul
    (hf.aestronglyMeasurable.comp_quasiMeasurePreserving ?_)) ?_
  · rw [cellVol_eq]
    exact Measure.quasiMeasurePreserving_snd
  · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK x hx) (abs_nonneg _)

/-- `∫_cell (∂_η φ) F(η) = -∫_cell φ ω̄(η)`: the weak `η`-derivative of `F(η)` is `ω̄`. -/
theorem integral_pd_one_mul_meanPrim {c m : ℝ} (hc : 0 < c) (hm : 1 < m) (ω : X c m)
    (hFc : Continuous (meanPrim c ω)) {φ : Plane → ℝ} (hφ : IsCylTest c φ) :
    ∫ x in cell c, pd 1 φ x * meanPrim c ω x.2 = -∫ x in cell c, φ x * meanVort c ω x.2 := by
  have hint := integrable_meanVort hc hm ω
  obtain ⟨R, hR⟩ := (hφ.pd 1).vanish
  have hL : IntegrableOn (fun x => pd 1 φ x * meanPrim c ω x.2) (cell c) :=
    B0579.integrableOn_cell_of_continuous ((hφ.pd 1).continuous.mul (hFc.comp continuous_snd))
      (B0579.isCompact_box c R) (fun x hx hxK => by simp [hR x hx hxK])
  have hRi := integrable_test_mul_snd hφ hint
  unfold IntegrableOn at hL
  rw [show volume.restrict (cell c) = cellVol c from rfl, cellVol_eq] at hL ⊢
  rw [cellVol_eq] at hRi
  rw [integral_prod _ hL, integral_prod _ hRi, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only
  have hsm : ContDiff ℝ 1 fun t => φ (q, t) :=
    (hφ.smooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_cast)
  have hderiv : deriv (fun t => φ (q, t)) = fun t => pd 1 φ (q, t) := by
    funext t
    exact (B0579.hasDerivAt_snd hφ.differentiable q t).deriv
  have h := integral_deriv_mul_primitive hint hsm (hφ.hasCompactSupport_slice q)
  rw [hderiv] at h
  exact h

/-- **Weak `∂_q` of the mean-mode velocity is `0`.** -/
theorem hasWeakCellDerivV_meanVel_q {c m : ℝ} (hc : 0 < c) (hm : 1 < m) (ω : X c m)
    (hcirc : ∫ x in cell c, ω x = 0) : HasWeakCellDerivV c 0 (meanVel c ω) 0 := by
  intro φ hφ
  have hFc := (meanVel_memLp_and_le hc hm ω hcirc).1
  have e : ∀ x : Plane, (pd 0 φ x : ℂ) • meanVel c ω x = ((pd 0 φ x * -meanPrim c ω x.2 : ℝ) : ℂ) • e1 := by
    intro x
    rw [meanVel, smul_smul, Complex.ofReal_mul]
  simp_rw [e, Pi.zero_apply, smul_zero, integral_zero, neg_zero]
  rw [integral_smul_e1]
  have h0 := integral_pd_zero_mul_snd hc hφ hFc.neg
  simp only [Pi.neg_apply] at h0
  rw [h0, Complex.ofReal_zero, zero_smul]

/-- **Weak `∂_η` of the mean-mode velocity is `(-ω̄, 0)`.** -/
theorem hasWeakCellDerivV_meanVel_eta {c m : ℝ} (hc : 0 < c) (hm : 1 < m) (ω : X c m)
    (hcirc : ∫ x in cell c, ω x = 0) : HasWeakCellDerivV c 1 (meanVel c ω) (meanVelDeta c ω) := by
  intro φ hφ
  have hFc := (meanVel_memLp_and_le hc hm ω hcirc).1
  have e : ∀ x : Plane, (pd 1 φ x : ℂ) • meanVel c ω x =
      ((-(pd 1 φ x * meanPrim c ω x.2) : ℝ) : ℂ) • e1 := by
    intro x
    rw [meanVel, smul_smul, ← Complex.ofReal_mul, mul_neg]
  have e' : ∀ x : Plane, (φ x : ℂ) • meanVelDeta c ω x =
      ((-(φ x * meanVort c ω x.2) : ℝ) : ℂ) • e1 := by
    intro x
    rw [meanVelDeta, smul_smul, ← Complex.ofReal_mul, mul_neg]
  simp_rw [e, e']
  rw [integral_smul_e1, integral_smul_e1, integral_neg, integral_neg,
    integral_pd_one_mul_meanPrim hc hm ω hFc hφ, neg_neg, ← neg_smul, ← Complex.ofReal_neg,
    neg_neg]

end UnforcedLeray.B0273
