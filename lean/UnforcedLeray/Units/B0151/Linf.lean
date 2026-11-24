import UnforcedLeray.Units.B0151.Ladyzhenskaya

/-!
# B0151, part 4: `H² ⊂ L^∞` and `H^{k+2} ⊂ C^k` on the cylinder, uniform for periods `L ≥ 1`

Blueprint unit **B0151** (`unlabeled:2291`), `paper/main.tex` lines 2291–2294 (the smoothing
bootstrap uses the `H^k → L^∞` and `C^k` embeddings) and 2510–2511.

Proof. For every `(q, η)` the circle bound gives
`h(q,η)² ≤ L⁻¹ a(η) + ∫₀ᴸ |2 h ∂_q h|(s,η) ds ≤ 2 a(η) + c(η)` when `L ≥ 1`, where
`a(η) = ∫₀ᴸ h(s,η)² ds` and `c(η) = ∫₀ᴸ (∂_q h)(s,η)² ds`. The line bound applied on almost every
`η`-line of `h` and of `∂_q h` gives `a(η) ≤ 2‖h‖₂‖∂_η h‖₂` and
`c(η) ≤ 2‖∂_q h‖₂‖∂_η∂_q h‖₂` for every `η`. Hence
`|h| ≤ 3 (‖h‖₂ + ‖∂_q h‖₂ + ‖∂_η h‖₂ + ‖∂_η ∂_q h‖₂)` everywhere, with no dependence on `L`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.B0151

open UnforcedLeray.GaussianVortex (partialX partialY)

/-- `|2ab| ≤ a² + b²`. -/
theorem enorm_two_mul_le (a b : ℝ) : ‖2 * a * b‖ₑ ≤ ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 := by
  rw [enorm_sq_eq, enorm_sq_eq, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
  exact abs_le.2 ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩

/-- Every circle integral of `h²` is bounded by the cell integral of `|2 h ∂_η h|`. -/
theorem circle_sq_le {L : ℝ} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (h2 : MemLp h 2 (cellMeasure L)) (hy : MemLp (partialY h) 2 (cellMeasure L)) (η : ℝ) :
    ∫⁻ s in Ioc 0 L, ‖h (s, η)‖ₑ ^ 2 ≤ ∫⁻ z, ‖2 * h z * partialY h z‖ₑ ∂cellMeasure L := by
  have hc0 : Continuous h := hh.continuous
  have hcy : Continuous (partialY h) := continuous_partialY hh
  have m3 : Measurable fun z : ℝ × ℝ => ‖2 * h z * partialY h z‖ₑ := by fun_prop
  rw [lintegral_cell L m3]
  exact lintegral_mono_ae ((ae_sq_le_line hh h2 hy).mono fun q hq => hq η)

/-- **`H² ⊂ L^∞` on the cylinder**, uniform for periods `L ≥ 1` (B0151, tex 2291–2294): every
value of `h` is bounded by `3 (‖h‖₂ + ‖∂_q h‖₂ + ‖∂_η h‖₂ + ‖∂_η ∂_q h‖₂)` over one cell. -/
theorem enorm_le_H2 {L : ℝ} (hL : 1 ≤ L) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hp : IsPeriodicQ L h) (h2 : MemLp h 2 (cellMeasure L))
    (hx : MemLp (partialX h) 2 (cellMeasure L)) (hy : MemLp (partialY h) 2 (cellMeasure L))
    (hxy : MemLp (partialY (partialX h)) 2 (cellMeasure L)) (z : ℝ × ℝ) :
    ‖h z‖ₑ ≤ 3 * (eLpNorm h 2 (cellMeasure L) + eLpNorm (partialX h) 2 (cellMeasure L) +
      eLpNorm (partialY h) 2 (cellMeasure L) +
        eLpNorm (partialY (partialX h)) 2 (cellMeasure L)) := by
  have hL0 : 0 < L := by linarith
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hgx : ContDiff ℝ 1 (partialX h) :=
    contDiff_partialX (n := 1) (by rw [one_add_one_eq_two]; exact hh)
  have hc0 : Continuous h := hh.continuous
  have hcx : Continuous (partialX h) := continuous_partialX hh1
  set A := eLpNorm h 2 (cellMeasure L)
  set Bx := eLpNorm (partialX h) 2 (cellMeasure L)
  set By := eLpNorm (partialY h) 2 (cellMeasure L)
  set Bxy := eLpNorm (partialY (partialX h)) 2 (cellMeasure L)
  set S := A + Bx + By + Bxy
  obtain ⟨q, η⟩ := z
  set a := ∫⁻ s in Ioc 0 L, ‖h (s, η)‖ₑ ^ 2
  set c := ∫⁻ s in Ioc 0 L, ‖partialX h (s, η)‖ₑ ^ 2
  have hcirc := sq_le_circle hL0 hh1 hp q η
  have hmix : ∫⁻ s in Ioc 0 L, ‖2 * h (s, η) * partialX h (s, η)‖ₑ ≤ a + c := by
    have hcs : Continuous fun s : ℝ => h (s, η) :=
      hc0.comp (continuous_id.prodMk continuous_const)
    have m : Measurable fun s : ℝ => ‖h (s, η)‖ₑ ^ 2 := hcs.measurable.enorm.pow_const 2
    rw [← lintegral_add_left m]
    exact lintegral_mono fun s => enorm_two_mul_le _ _
  have ha : a ≤ 2 * (A * By) :=
    (circle_sq_le hh1 h2 hy η).trans (lintegral_two_mul_le h2.1 hy.1)
  have hc : c ≤ 2 * (Bx * Bxy) :=
    (circle_sq_le hgx hx hxy η).trans (lintegral_two_mul_le hx.1 hxy.1)
  have hAS : A ≤ S := (le_self_add.trans le_self_add).trans le_self_add
  have hBxS : Bx ≤ S := (le_add_self.trans le_self_add).trans le_self_add
  have hByS : By ≤ S := le_add_self.trans le_self_add
  have hBxyS : Bxy ≤ S := le_add_self
  have hLinv : ENNReal.ofReal L⁻¹ ≤ 1 := ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀ hL)
  have hsq : ‖h (q, η)‖ₑ ^ 2 ≤ (3 * S) ^ 2 := by
    calc ‖h (q, η)‖ₑ ^ 2 ≤ ENNReal.ofReal L⁻¹ * a + (a + c) := hcirc.trans (by gcongr)
      _ ≤ 1 * a + (a + c) := by gcongr
      _ ≤ 1 * (2 * (A * By)) + (2 * (A * By) + 2 * (Bx * Bxy)) := by gcongr
      _ ≤ 1 * (2 * (S * S)) + (2 * (S * S) + 2 * (S * S)) := by gcongr
      _ ≤ 1 * (2 * (S * S)) + (2 * (S * S) + 2 * (S * S)) + 3 * (S * S) := le_self_add
      _ = (3 * S) ^ 2 := by ring
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

/-! ### `H^{k+2} ⊂ C^k` -/

/-- Iterated classical partial derivatives along a word: `true` is `∂_q`, `false` is `∂_η`; the
head of the list is applied last. -/
def derivWord : List Bool → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], h => h
  | true :: w, h => partialX (derivWord w h)
  | false :: w, h => partialY (derivWord w h)

theorem contDiff_partialX_infty {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (partialX h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialX h = fun z => fderiv ℝ h z (1, 0) from funext (partialX_eq_fderiv hd)]
  exact (contDiff_infty_iff_fderiv.1 hh).2.clm_apply contDiff_const

theorem contDiff_partialY_infty {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (partialY h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialY h = fun z => fderiv ℝ h z (0, 1) from funext (partialY_eq_fderiv hd)]
  exact (contDiff_infty_iff_fderiv.1 hh).2.clm_apply contDiff_const

theorem contDiff_derivWord {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ∀ w : List Bool, ContDiff ℝ ∞ (derivWord w h)
  | [] => hh
  | true :: w => contDiff_partialX_infty (contDiff_derivWord hh w)
  | false :: w => contDiff_partialY_infty (contDiff_derivWord hh w)

theorem periodic_derivWord {L : ℝ} {h : ℝ × ℝ → ℝ} (hp : IsPeriodicQ L h) :
    ∀ w : List Bool, IsPeriodicQ L (derivWord w h)
  | [] => hp
  | true :: w => (periodic_derivWord hp w).partialX
  | false :: w => (periodic_derivWord hp w).partialY

/-- **`H^{k+2} ⊂ C^k` on the cylinder**, uniform for periods `L ≥ 1`: every derivative
`D_w h` of a smooth periodic field is bounded everywhere by `3` times the sum of the cell `L²`
norms of `D_w h`, `∂_q D_w h`, `∂_η D_w h` and `∂_η ∂_q D_w h`, derivatives of `h` of order at
most `|w| + 2`. -/
theorem enorm_derivWord_le {L : ℝ} (hL : 1 ≤ L) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : IsPeriodicQ L h) (w : List Bool)
    (h0 : MemLp (derivWord w h) 2 (cellMeasure L))
    (hq : MemLp (derivWord (true :: w) h) 2 (cellMeasure L))
    (hη : MemLp (derivWord (false :: w) h) 2 (cellMeasure L))
    (hqη : MemLp (derivWord (false :: true :: w) h) 2 (cellMeasure L)) (z : ℝ × ℝ) :
    ‖derivWord w h z‖ₑ ≤ 3 * (eLpNorm (derivWord w h) 2 (cellMeasure L) +
      eLpNorm (derivWord (true :: w) h) 2 (cellMeasure L) +
      eLpNorm (derivWord (false :: w) h) 2 (cellMeasure L) +
      eLpNorm (derivWord (false :: true :: w) h) 2 (cellMeasure L)) :=
  enorm_le_H2 hL (by simpa using contDiff_infty.1 (contDiff_derivWord hh w) 2)
    (periodic_derivWord hp w) h0 hq hη hqη z

end UnforcedLeray.B0151
