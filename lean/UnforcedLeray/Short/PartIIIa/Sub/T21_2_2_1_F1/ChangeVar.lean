import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.PdScale

/-!
# Part III-a, `PartIII-a:T21/2/2/1/3/org`: the energies of the moving adjoint on the fixed cell

Source of record: `the November 2 reference manuscript` (SP), lines 2854-2865
(`x = √a y`, `d = c/√a`), 3036-3037 (`Φ = a⁻¹φ(r, √a ·)`), 3044-3047 (the periodic weight),
3060-3071 (the energies `E_j`).

The moving cell `C_d`, `d(r) = c/√a(r)`, and the weight `p_d⁻¹` move with the age. The substitution
`x = √a y` puts `E_0`, `E_1` on the fixed cell `C_c`:

* `integral_moving_weight`: `∫_{C_d} p_d⁻¹(y) F(√a y) dy = a⁻¹ ∫_{C_c} wtF0(a, x) F(x) dx`, for every
  `F`, with `wtF0(a, x) = p_d⁻¹(x/√a)` (`wtF0_eq_periodicWeight`);
* `adjF0Ident_direct`: `E_0 = a⁻³ ∫_{C_c} wtF0 |φ(r)|²` (this is `AdjF0Ident`);
* `adjF1_eq_coreF1`, `adjF1_eq_fixed`: `E_1 = a⁻² Σ_k ∫_{C_c} wtF0 |∂_kφ(r)|²`, from the chain rule
  `∂_kΦ(y) = a⁻¹√a ∂_kφ(r, √a y)` (`mpPdScale`). The same identity is `E1ChangeVar`
  (`Sub/PartIIIa_T21_2_2_3_5.lean`), where the right-hand side is called `physE1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Pointwise

namespace UnforcedLeray.Short.IIIa

/-- The dilation by `√a` maps the moving cell of length `c/√a` onto the fixed cell of length `c`. -/
theorem sqrt_smul_cell (c a : ℝ) (ha : 0 < a) :
    Real.sqrt a • B0579.cell (cellLen c a) = B0579.cell c := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs' : Real.sqrt a ≠ 0 := hs.ne'
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs']
  have e1 : c / Real.sqrt a / 2 = (Real.sqrt a)⁻¹ * (c / 2) := by field_simp
  have e2 : -((Real.sqrt a)⁻¹ * (c / 2)) = (Real.sqrt a)⁻¹ * (-(c / 2)) := by ring
  have hinv : 0 < (Real.sqrt a)⁻¹ := inv_pos.mpr hs
  simp only [B0579.cell, cellLen, mem_prod, mem_Ico, mem_univ, and_true, Prod.smul_fst, smul_eq_mul]
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_mul_le_mul_left h1 hinv, lt_of_mul_lt_mul_left h2 hinv.le⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_le_mul_of_nonneg_left h1 hinv.le, mul_lt_mul_of_pos_left h2 hinv⟩

/-- Change of variables `x = √a y` on the moving cell, with no hypothesis on `G`. -/
theorem integral_cell_scale (c a : ℝ) (ha : 0 < a) (G : ℝ × ℝ → ℝ) :
    ∫ y in B0579.cell (cellLen c a), G (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      a⁻¹ * ∫ x in B0579.cell c, G x := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (ℝ × ℝ))) G
    (B0579.cell (cellLen c a)) hs
  rw [sqrt_smul_cell c a ha] at h
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin, Real.sq_sqrt ha.le, smul_eq_mul] at h
  exact h

/-- The fixed-cell weight at the dilated point is the moving weight `p_d⁻¹`, `d = c/√a`. -/
theorem wtF0_scale (c m a : ℝ) (hc : 0 < c) (ha : 0 < a) (y : ℝ × ℝ) :
    wtF0 c m a (Real.sqrt a * y.1, Real.sqrt a * y.2) = periodicWeight (-m) (cellLen c a) y := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : Real.pi * (Real.sqrt a * y.1) / c = Real.pi * y.1 / (c / Real.sqrt a) := by
    field_simp
  have h2 : (Real.sqrt a * y.2) ^ 2 / a = y.2 ^ 2 := by
    rw [mul_pow, hsq]
    field_simp
  have h3 : (c / Real.sqrt a / Real.pi) ^ 2 = (c / Real.pi) ^ 2 / a := by
    rw [div_right_comm, div_pow, hsq]
  unfold wtF0 periodicWeight cellLen
  simp only
  rw [h1, h2, h3]
  congr 2
  ring

/-- `wtF0(a, x) = p_d⁻¹(x/√a)`: the fixed-cell weight is the moving weight at the moving point. -/
theorem wtF0_eq_periodicWeight (c m a : ℝ) (hc : 0 < c) (ha : 0 < a) (x : ℝ × ℝ) :
    wtF0 c m a x =
      periodicWeight (-m) (cellLen c a) (x.1 / Real.sqrt a, x.2 / Real.sqrt a) := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  rw [← wtF0_scale c m a hc ha]
  simp only
  rw [mul_div_cancel₀ _ hs, mul_div_cancel₀ _ hs]

/-- **The change of variables with the weight** (SP 2854-2865, 3044-3047): for every `F`,
`∫_{C_d} p_d⁻¹(y) F(√a y) dy = a⁻¹ ∫_{C_c} wtF0(a, x) F(x) dx`, `d = c/√a`. -/
theorem integral_moving_weight (c m a : ℝ) (hc : 0 < c) (ha : 0 < a) (F : ℝ × ℝ → ℝ) :
    ∫ y in B0579.cell (cellLen c a), periodicWeight (-m) (cellLen c a) y *
        F (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      a⁻¹ * ∫ x in B0579.cell c, wtF0 c m a x * F x := by
  rw [← integral_cell_scale c a ha (fun x => wtF0 c m a x * F x)]
  simp only [wtF0_scale c m a hc ha]

/-- `|Φ(y)|² = a⁻²|φ(r, √a y)|²` for the moving adjoint `Φ = a⁻¹φ(r, √a ·)` (SP 3036-3037). -/
theorem norm_movingPhi_sq {ν : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} {r : ℝ} (ha : 0 < clockA ν r)
    (y : ℝ × ℝ) :
    ‖movingPhi ν φ r y‖ ^ 2 =
      (clockA ν r)⁻¹ ^ 2 *
        ‖φ r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ ^ 2 := by
  unfold movingPhi
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]

/-- **`AdjF0Ident`** (SP 2854-2865, 3060-3071): `E_0 = a⁻³ ∫_{C_c} wtF0 |φ(r)|²`. -/
theorem adjF0Ident_direct : AdjF0Ident := by
  intro ν c m φ r hc ha
  unfold adjF0 adjE0 coreF0
  simp only [norm_movingPhi_sq ha]
  have h := integral_moving_weight c m (clockA ν r) hc ha
    (fun x => (clockA ν r)⁻¹ ^ 2 * ‖φ r x‖ ^ 2)
  rw [h]
  have e : ∀ x : ℝ × ℝ, wtF0 c m (clockA ν r) x * ((clockA ν r)⁻¹ ^ 2 * ‖φ r x‖ ^ 2) =
      (clockA ν r)⁻¹ ^ 2 * (wtF0 c m (clockA ν r) x * ‖φ r x‖ ^ 2) := fun x => by ring
  simp only [e]
  rw [integral_const_mul]
  ring

/-- The fixed-cell gradient energy `Σ_k ∫_{C_c} wtF0(a(r), x) |∂_kφ(r, x)|² dx`. -/
def coreF1 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  ∑ k : Fin 2, ∫ x in B0579.cell c, wtF0 c m (clockA ν r) x * ‖pdCx k (φ r) x‖ ^ 2

/-- `|∂_kΦ(y)|² = a⁻¹|∂_kφ(r, √a y)|²` (chain rule, `mpPdScale`). -/
theorem norm_pdCx_movingPhi_sq {ν : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} {r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hφ : ContDiff ℝ ∞ (φ r)) (k : Fin 2) (y : ℝ × ℝ) :
    ‖pdCx k (movingPhi ν φ r) y‖ ^ 2 =
      (clockA ν r)⁻¹ *
        ‖pdCx k (φ r) (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ ^ 2 := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have hsq : Real.sqrt (clockA ν r) ^ 2 = clockA ν r := Real.sq_sqrt ha.le
  have hc : 0 ≤ (clockA ν r)⁻¹ * Real.sqrt (clockA ν r) := by positivity
  rw [mpPdScale ν hν r hr φ hφ k y, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hc,
    mul_pow, hsq]
  congr 1
  field_simp

/-- **`E_1` on the fixed cell** (SP 2854-2865, 3036-3037, 3060-3071): for `r ≥ 0` and `φ(r)` smooth,
`E_1 = a⁻² Σ_k ∫_{C_c} wtF0(a, x) |∂_kφ(r, x)|² dx`. -/
theorem adjF1_eq_coreF1 {ν c m : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} {r : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hr : 0 ≤ r) (hφ : ContDiff ℝ ∞ (φ r)) :
    adjF1 ν c m φ r = (clockA ν r)⁻¹ ^ 2 * coreF1 ν c m φ r := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  unfold adjF1 adjE1 coreF1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [norm_pdCx_movingPhi_sq hν hr hφ k]
  have h := integral_moving_weight c m (clockA ν r) hc ha
    (fun x => (clockA ν r)⁻¹ * ‖pdCx k (φ r) x‖ ^ 2)
  rw [h]
  have e : ∀ x : ℝ × ℝ, wtF0 c m (clockA ν r) x * ((clockA ν r)⁻¹ * ‖pdCx k (φ r) x‖ ^ 2) =
      (clockA ν r)⁻¹ * (wtF0 c m (clockA ν r) x * ‖pdCx k (φ r) x‖ ^ 2) := fun x => by ring
  simp only [e]
  rw [integral_const_mul]
  ring

/-- `E_1` on the fixed cell with the weight written out: `wtF0(a, x) = p_d⁻¹(x/√a)`, `d = c/√a`. This
is the identity `E1ChangeVar` of `Sub/PartIIIa_T21_2_2_3_5.lean`, whose right-hand side is `physE1`. -/
theorem adjF1_eq_fixed {ν c m : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} {r : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hr : 0 ≤ r) (hφ : ContDiff ℝ ∞ (φ r)) :
    adjE1 (cellLen c (clockA ν r)) m (movingPhi ν φ r) =
      (clockA ν r)⁻¹ ^ 2 * ∑ k : Fin 2, ∫ x in B0579.cell c,
        periodicWeight (-m) (cellLen c (clockA ν r))
          (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)) * ‖pdCx k (φ r) x‖ ^ 2 := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have h := adjF1_eq_coreF1 (m := m) hν hc hr hφ
  unfold adjF1 coreF1 at h
  rw [h]
  simp only [wtF0_eq_periodicWeight c m (clockA ν r) hc ha]

end UnforcedLeray.Short.IIIa
