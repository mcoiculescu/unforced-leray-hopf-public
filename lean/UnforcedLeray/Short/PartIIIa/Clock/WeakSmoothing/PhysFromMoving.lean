import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing

/-!
# Physical weak smoothing from the moving weak-to-strong bound (SP 3030-3036, 3077-3084)

`weakSmoothingPhys_of_moving`: `MovingWeakStrong m` and `ScalingBounds` imply `WeakSmoothingPhys m`.
The scaling bounds of `ScalingBounds` are stated for measurable representatives; the helper
lemmas below transfer them to `MemLp` functions via `AEStronglyMeasurable.mk` and the
rescaling of null sets (`addHaar_smul`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal Pointwise

namespace UnforcedLeray.Short.IIIa

/-- `J_a (J_a⁻¹ F) = F` for `a > 0`. -/
theorem jscale_jscaleInv {a : ℝ} (ha : 0 < a) (F : ℝ × ℝ → ℂ) : Jscale a (JscaleInv a F) = F := by
  funext x
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have h1 : a ^ (-2 : ℝ) * a ^ 2 = 1 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')
  have e1 : Real.sqrt a * (x.1 / Real.sqrt a) = x.1 := by field_simp
  have e2 : Real.sqrt a * (x.2 / Real.sqrt a) = x.2 := by field_simp
  dsimp only [Jscale, JscaleInv]
  rw [e1, e2, ← mul_assoc, ← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

/-- `J_a⁻¹ F` is measurable when `F` is. -/
theorem measurable_jscaleInv (a : ℝ) {F : ℝ × ℝ → ℂ} (hF : Measurable F) :
    Measurable (JscaleInv a F) := by
  unfold JscaleInv
  have hm : Measurable (fun y : ℝ × ℝ => (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by fun_prop
  exact (hF.comp hm).const_mul _

/-- Rescaling transfers `ae`-equality on the cell: if `f = g` a.e. on `cell (d√a)` then
`J_a⁻¹ f = J_a⁻¹ g` a.e. on `cell d`. -/
theorem jscaleInv_ae_volume {a d c : ℝ} (ha : 0 < a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    {f g : ℝ × ℝ → ℂ} (h : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    JscaleInv a f =ᵐ[volume.restrict (B0579.cell d)] JscaleInv a g := by
  subst hdc
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hN : volume ({x | ¬ f x = g x} ∩ B0579.cell (d * Real.sqrt a)) = 0 := by
    have h' := ae_iff.1 h
    rwa [Measure.restrict_apply' (B0579.measurableSet_cell _)] at h'
  have hsub : {y | ¬ JscaleInv a f y = JscaleInv a g y} ∩ B0579.cell d ⊆
      (Real.sqrt a)⁻¹ • ({x | ¬ f x = g x} ∩ B0579.cell (d * Real.sqrt a)) := by
    rintro y ⟨hy1, hy2⟩
    have hsmul : (Real.sqrt a) • y = (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      ext <;> simp [smul_eq_mul]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hs.ne'), inv_inv]
    refine ⟨?_, ?_⟩
    · intro hfg
      apply hy1
      rw [hsmul] at hfg
      dsimp only [JscaleInv]
      rw [hfg]
    · rw [hsmul]
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hy2 ⊢
      constructor <;> nlinarith [hy2.1, hy2.2, hs]
  have hT0 : volume ((Real.sqrt a)⁻¹ • ({x | ¬ f x = g x} ∩ B0579.cell (d * Real.sqrt a))) = 0 := by
    rw [MeasureTheory.Measure.addHaar_smul, hN, mul_zero]
  rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' (B0579.measurableSet_cell d)]
  exact measure_mono_null hsub hT0

/-- `negNorm` only depends on `f` up to `ae`-equality on the cell. -/
theorem negNorm_congr_ae {c m : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) : negNorm c m f = negNorm c m g := by
  have key : ∀ φ : ℝ × ℝ → ℂ, (∫ x in B0579.cell c, f x * φ x) = ∫ x in B0579.cell c, g x * φ x :=
    fun φ => integral_congr_ae (by filter_upwards [h] with x hx; simp only [hx])
  unfold negNorm
  simp only [key]

/-- The first scaling bound for a `MemLp` function, via a measurable representative. -/
theorem xNorm_scale_le (hS : ScalingBounds) {a d c m : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    (hdc : d * Real.sqrt a = c) {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (B0579.cellMeasure c m)) :
    xNorm c m w ≤ ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m (JscaleInv a w) := by
  have ha0 : 0 < a := by linarith
  have hF0 : AEStronglyMeasurable w (B0579.cellMeasure c m) := hw.1
  have hF : Measurable (hF0.mk w) := hF0.stronglyMeasurable_mk.measurable
  have hae : w =ᵐ[B0579.cellMeasure c m] hF0.mk w := hF0.ae_eq_mk
  have hvol : w =ᵐ[volume.restrict (B0579.cell c)] hF0.mk w :=
    (B0579.ac_cellMeasure c m).ae_le hae
  have hT : JscaleInv a (hF0.mk w) =ᵐ[volume.restrict (B0579.cell d)] JscaleInv a w :=
    jscaleInv_ae_volume ha0 hd hdc hvol.symm
  have hT' : JscaleInv a (hF0.mk w) =ᵐ[B0579.cellMeasure d m] JscaleInv a w :=
    (B0579.cellMeasure_ac d m).ae_le hT
  have hxF : xNorm c m w = xNorm c m (hF0.mk w) := eLpNorm_congr_ae hae
  have hxJ : xNorm d m (JscaleInv a (hF0.mk w)) = xNorm d m (JscaleInv a w) :=
    eLpNorm_congr_ae hT'
  have h1 := (hS m hm a d ha hd).1 (JscaleInv a (hF0.mk w)) (measurable_jscaleInv a hF)
  rw [jscale_jscaleInv ha0, hdc] at h1
  rw [hxF, ← hxJ]
  exact h1

/-- The third scaling bound for a `MemLp` function, via a measurable representative. -/
theorem negNorm_scale_le (hS : ScalingBounds) {a d c m : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    (hdc : d * Real.sqrt a = c) {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    negNorm d m (JscaleInv a f) ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * negNorm c m f := by
  have ha0 : 0 < a := by linarith
  have hF0 : AEStronglyMeasurable f (B0579.cellMeasure c m) := hf.1
  have hF : Measurable (hF0.mk f) := hF0.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[B0579.cellMeasure c m] hF0.mk f := hF0.ae_eq_mk
  have hvol : f =ᵐ[volume.restrict (B0579.cell c)] hF0.mk f :=
    (B0579.ac_cellMeasure c m).ae_le hae
  have h3 := (hS m hm a d ha hd).2.2 (hF0.mk f) hF
  rw [hdc] at h3
  have e1 : negNorm d m (JscaleInv a f) = negNorm d m (JscaleInv a (hF0.mk f)) :=
    negNorm_congr_ae (jscaleInv_ae_volume ha0 hd hdc hvol)
  have e2 : negNorm c m f = negNorm c m (hF0.mk f) := negNorm_congr_ae hvol
  rw [e1, e2]
  exact h3

theorem ennreal_chain (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (N : ℝ≥0∞) :
    ENNReal.ofReal p * (ENNReal.ofReal q * (ENNReal.ofReal r * N)) =
      ENNReal.ofReal (p * q * r) * N := by
  rw [ENNReal.ofReal_mul (mul_nonneg hp hq), ENNReal.ofReal_mul hp]
  ring

/-- The real exponent arithmetic: `A^{(m-3)/2} (ν(s-t)/A)^{-1/2} B^{3/2} ≤ C_b ν^{-(m+2)/2}(s-t)^{-1/2}`
with `A = a(s)`, `B = a(t)`, `b b ≤ θ(s)`. -/
theorem key_real {m ν s t b C : ℝ} (hm : 0 ≤ m) (hν : 0 < ν) (hts : t < s) (hb : 1 ≤ b)
    (hkey : b * (ν * clockA ν s) ≤ 1) (hA : 1 ≤ clockA ν s) (hBA : clockA ν t ≤ clockA ν s)
    (hB : 1 ≤ clockA ν t) :
    clockA ν s ^ ((m - 3) / 2) * (|C| * (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ)) *
        clockA ν t ^ (3 / 2 : ℝ) ≤
      |C| * b ^ (-((m + 1) / 2)) * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ) := by
  have hE : 0 < s - t := by linarith
  have hA0 : 0 < clockA ν s := by linarith
  have hB0 : 0 < clockA ν t := by linarith
  have hb0 : 0 < b := by linarith
  have hZ : (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ) =
      ν ^ (-1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) * clockA ν s ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow (mul_nonneg hν.le hE.le) hA0.le, Real.mul_rpow hν.le hE.le]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hA0.le, div_inv_eq_mul]
  have hp : 0 ≤ (m + 1) / 2 := by linarith
  have hY : 0 < ν * b := mul_pos hν hb0
  have hAle : clockA ν s ^ ((m + 1) / 2) ≤ ν ^ (-((m + 1) / 2)) * b ^ (-((m + 1) / 2)) := by
    have e : clockA ν s * (ν * b) = b * (ν * clockA ν s) := by ring
    have hA' : clockA ν s ≤ 1 / (ν * b) := (le_div_iff₀ hY).2 (by rw [e]; exact hkey)
    calc clockA ν s ^ ((m + 1) / 2) ≤ (1 / (ν * b)) ^ ((m + 1) / 2) :=
          Real.rpow_le_rpow hA0.le hA' hp
      _ = ν ^ (-((m + 1) / 2)) * b ^ (-((m + 1) / 2)) := by
          rw [one_div, Real.inv_rpow hY.le, Real.mul_rpow hν.le hb0.le, Real.rpow_neg hν.le,
            Real.rpow_neg hb0.le, mul_inv]
  have hBA3 : clockA ν t ^ (3 / 2 : ℝ) ≤ clockA ν s ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hB0.le hBA (by norm_num)
  have hpre : 0 ≤ |C| * (ν ^ (-1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) * clockA ν s ^ (1 / 2 : ℝ)) :=
    mul_nonneg (abs_nonneg C)
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hν.le _) (Real.rpow_nonneg hE.le _))
        (Real.rpow_nonneg hA0.le _))
  have hAp : clockA ν s ^ ((m - 3) / 2) * clockA ν s ^ (1 / 2 : ℝ) * clockA ν s ^ (3 / 2 : ℝ) =
      clockA ν s ^ ((m + 1) / 2) := by
    rw [← Real.rpow_add hA0, ← Real.rpow_add hA0]
    congr 1
    ring
  have hnu : ν ^ (-1 / 2 : ℝ) * ν ^ (-((m + 1) / 2)) = ν ^ (-((m + 2) / 2)) := by
    rw [← Real.rpow_add hν]
    congr 1
    ring
  calc clockA ν s ^ ((m - 3) / 2) * (|C| * (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ)) *
        clockA ν t ^ (3 / 2 : ℝ)
      = clockA ν s ^ ((m - 3) / 2) *
          (|C| * (ν ^ (-1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) * clockA ν s ^ (1 / 2 : ℝ))) *
          clockA ν t ^ (3 / 2 : ℝ) := by rw [hZ]
    _ ≤ clockA ν s ^ ((m - 3) / 2) *
          (|C| * (ν ^ (-1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) * clockA ν s ^ (1 / 2 : ℝ))) *
          clockA ν s ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hBA3 (mul_nonneg (Real.rpow_nonneg hA0.le _) hpre)
    _ = |C| * ν ^ (-1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) * clockA ν s ^ ((m + 1) / 2) := by
          rw [← hAp]
          ring
    _ ≤ |C| * ν ^ (-1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) *
          (ν ^ (-((m + 1) / 2)) * b ^ (-((m + 1) / 2))) :=
        mul_le_mul_of_nonneg_left hAle
          (mul_nonneg (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hν.le _))
            (Real.rpow_nonneg hE.le _))
    _ = |C| * b ^ (-((m + 1) / 2)) * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ) := by
          rw [← hnu]
          ring

/-- **Physical weak smoothing from the moving bound** (SP 3030-3036, 3077-3084). -/
theorem weakSmoothingPhys_of_moving (m : ℝ) (hm : 0 ≤ m) (hS : ScalingBounds)
    (hM : MovingWeakStrong m) : WeakSmoothingPhys m := by
  obtain ⟨b₀, hb₀⟩ := hM
  refine ⟨max b₀ 1, fun b hb => ?_⟩
  have hbb₀ : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  obtain ⟨C, ν₀, hν₀, hC⟩ := hb₀ b hbb₀
  refine ⟨|C| * b ^ (-((m + 1) / 2)), ν₀, hν₀, fun ν hν tr htr t s ht hts hst hbθ f hf hz w u hlin => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hs0 : 0 ≤ s := by linarith
  have hA : 1 ≤ clockA ν s := by
    have := mul_nonneg hν0.le hs0
    unfold clockA
    linarith
  have hB : 1 ≤ clockA ν t := by
    have := mul_nonneg hν0.le ht
    unfold clockA
    linarith
  have hBA : clockA ν t ≤ clockA ν s := by
    have := mul_le_mul_of_nonneg_left hts.le hν0.le
    unfold clockA
    linarith
  have hA0 : 0 < clockA ν s := by linarith
  have hkey : b * (ν * clockA ν s) ≤ 1 := by
    have hpos : 0 < ν * clockA ν s := mul_pos hν0 hA0
    have h := mul_le_mul_of_nonneg_right hbθ hpos.le
    unfold clockTheta at h
    rwa [inv_mul_cancel₀ hpos.ne'] at h
  have hdS : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := div_pos hc (Real.sqrt_pos.2 hA0)
  have hdT : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t) :=
    div_pos hc (Real.sqrt_pos.2 (by linarith))
  have hdcS : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) * Real.sqrt (clockA ν s) = ν ^ (-2 : ℝ) := by
    unfold cellLen
    field_simp [(Real.sqrt_pos.2 hA0).ne']
  have hdcT : cellLen (ν ^ (-2 : ℝ)) (clockA ν t) * Real.sqrt (clockA ν t) = ν ^ (-2 : ℝ) := by
    unfold cellLen
    field_simp [(Real.sqrt_pos.2 (by linarith : (0 : ℝ) < clockA ν t)).ne']
  have hwMem : MemLp (w s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hlin.memX s hts.le
  have s1 := xNorm_scale_le hS hm hA hdS hdcS hwMem
  have s2 := hC ν hν tr htr t s ht hts hst hbθ f hf hz w u hlin
  have s3 := negNorm_scale_le hS hm hB hdT hdcT hf
  have hZ : 0 ≤ ν * (s - t) / clockA ν s :=
    div_nonneg (mul_nonneg hν0.le (by linarith)) hA0.le
  have hCZ : C * (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ) ≤
      |C| * (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hZ _)
  have s2' := le_trans s2 (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCZ) zero_le)
  have s23 := le_trans s2' (mul_le_mul_of_nonneg_left s3 zero_le)
  have s123 := le_trans s1 (mul_le_mul_of_nonneg_left s23 zero_le)
  have hreal := key_real (C := C) hm hν0 hts hb1 hkey hA hBA hB
  have hp : 0 ≤ clockA ν s ^ ((m - 3) / 2) := Real.rpow_nonneg hA0.le _
  have hq : 0 ≤ |C| * (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ) :=
    mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hZ _)
  have hr : 0 ≤ clockA ν t ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  exact le_trans (le_trans s123 (le_of_eq (ennreal_chain _ _ _ hp hq _)))
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) zero_le)

end UnforcedLeray.Short.IIIa
