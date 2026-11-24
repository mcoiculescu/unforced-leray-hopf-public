import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf1Wit

/-!
# Leaf (a) of `PartIII-a:T21/c3/3/1/1`, part 2: Pythagoras, bound and uniqueness for witnesses

Source `the November 2 reference manuscript` (SP) lines 2937-2958.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf1Aux

variable {ν m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {s₁ : ℝ}

theorem jscaleInv_real (a : ℝ) (f : B0579.Plane → ℝ) (y : ℝ × ℝ) :
    JscaleInv a (fun x => ((f x : ℝ) : ℂ)) y =
      (((a ^ 2 * f (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ)) : ℂ) := by
  simp [JscaleInv]

theorem enorm_sq_cx (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (z.re ^ 2 + z.im ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem eLpNorm_sq_eq (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    xNorm c m f ^ (2 : ℝ) = ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c m) := by
  have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := B0579.cellMeasure c m) (p := 2)
    two_ne_zero
  simpa [xNorm] using this

/-- Pythagoras in `X_{m,c}` for a complex function whose real and imaginary parts are measurable. -/
theorem xNorm_sq_re_im (c m : ℝ) (f : ℝ × ℝ → ℂ)
    (hre : AEStronglyMeasurable (fun y => ((f y).re : ℂ)) (B0579.cellMeasure c m)) :
    xNorm c m f ^ (2 : ℝ) =
      xNorm c m (fun y => ((f y).re : ℂ)) ^ (2 : ℝ) +
        xNorm c m (fun y => ((f y).im : ℂ)) ^ (2 : ℝ) := by
  rw [eLpNorm_sq_eq, eLpNorm_sq_eq, eLpNorm_sq_eq]
  rw [← lintegral_add_left' (hre.enorm.pow_const _)]
  refine lintegral_congr fun y => ?_
  rw [enorm_sq_cx, enorm_sq_cx, enorm_sq_cx]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem cx_re_aux (u v : ℝ) : ((((u : ℂ) + Complex.I * (v : ℂ)).re : ℝ) : ℂ) = u := by simp

theorem cx_im_aux (u v : ℝ) : ((((u : ℂ) + Complex.I * (v : ℂ)).im : ℝ) : ℂ) = v := by simp

theorem movCx_re (a : ℝ) (f₁ f₂ : B0579.Plane → ℝ) (y : ℝ × ℝ) :
    (((movCx a f₁ f₂ y).re : ℝ) : ℂ) = JscaleInv a (fun x => ((f₁ x : ℝ) : ℂ)) y := by
  simp only [movCx, jscaleInv_real]
  exact cx_re_aux _ _

theorem movCx_im (a : ℝ) (f₁ f₂ : B0579.Plane → ℝ) (y : ℝ × ℝ) :
    (((movCx a f₁ f₂ y).im : ℝ) : ℂ) = JscaleInv a (fun x => ((f₂ x : ℝ) : ℂ)) y := by
  simp only [movCx, jscaleInv_real]
  exact cx_im_aux _ _

theorem memLp_jscale_real {a c m : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) {f : B0579.Plane → ℝ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    MemLp (JscaleInv a (fun x => ((f x : ℝ) : ℂ))) 2 (B0579.cellMeasure (cellLen c a) m) :=
  ComplCouplingSub.memLp_JscaleInv hm ha hf.ofReal

theorem memLp_movCx {a c m : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) {f₁ f₂ : B0579.Plane → ℝ}
    (h₁ : MemLp f₁ 2 (B0579.cellMeasure c m)) (h₂ : MemLp f₂ 2 (B0579.cellMeasure c m)) :
    MemLp (movCx a f₁ f₂) 2 (B0579.cellMeasure (cellLen c a) m) :=
  (memLp_jscale_real hm ha h₁).add ((memLp_jscale_real hm ha h₂).const_mul Complex.I)

theorem Wit.memLp_inp (W : Wit ν m tr s₁) (hm : 0 ≤ m) (ha : 1 ≤ clockA ν s₁) :
    MemLp W.inp 2 (B0579.cellMeasure (dd ν s₁) m) :=
  memLp_movCx hm ha W.hω₁.memLp_initial W.hω₂.memLp_initial

theorem Wit.memLp_out (W : Wit ν m tr s₁) {s₂ : ℝ} (h12 : s₁ ≤ s₂) (hm : 0 ≤ m)
    (ha : 1 ≤ clockA ν s₂) : MemLp (W.out s₂) 2 (B0579.cellMeasure (dd ν s₂) m) :=
  memLp_movCx hm ha (W.hω₁.memX s₂ h12) (W.hω₂.memX s₂ h12)

/-- The free energy bound for a witness (Pythagoras for the real and imaginary parts). -/
theorem Wit.bound {t₁ t₂ : ℝ} (hFree : FreeEnergyHyp ν m tr t₁ t₂) (W : Wit ν m tr s₁)
    {s₂ : ℝ} (h1 : t₁ ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ t₂) (hm : 0 ≤ m)
    (ha1 : 1 ≤ clockA ν s₁) (ha2 : 1 ≤ clockA ν s₂) :
    xNorm (dd ν s₂) m (W.out s₂) ≤
      ENNReal.ofReal (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁))) *
        xNorm (dd ν s₁) m W.inp := by
  set C := ENNReal.ofReal (Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁)))
  have hb1 := hFree s₁ s₂ h1 h12 h2 _ W.hf₁ _ W.hω₁
  have hb2 := hFree s₁ s₂ h1 h12 h2 _ W.hf₂ _ W.hω₂
  have hI : (fun y => (((W.inp y).re : ℝ) : ℂ)) =
      JscaleInv (clockA ν s₁) (fun x => ((W.f₁ x : ℝ) : ℂ)) := funext fun y => movCx_re _ _ _ _
  have hI' : (fun y => (((W.inp y).im : ℝ) : ℂ)) =
      JscaleInv (clockA ν s₁) (fun x => ((W.f₂ x : ℝ) : ℂ)) := funext fun y => movCx_im _ _ _ _
  have hO : (fun y => (((W.out s₂ y).re : ℝ) : ℂ)) =
      JscaleInv (clockA ν s₂) (fun x => ((W.ω₁ s₂ x : ℝ) : ℂ)) :=
    funext fun y => movCx_re _ _ _ _
  have hO' : (fun y => (((W.out s₂ y).im : ℝ) : ℂ)) =
      JscaleInv (clockA ν s₂) (fun x => ((W.ω₂ s₂ x : ℝ) : ℂ)) :=
    funext fun y => movCx_im _ _ _ _
  have hre1 : AEStronglyMeasurable (fun y => (((W.inp y).re : ℝ) : ℂ))
      (B0579.cellMeasure (dd ν s₁) m) := by
    rw [hI]
    exact (memLp_jscale_real (a := clockA ν s₁) hm ha1 W.hω₁.memLp_initial).aestronglyMeasurable
  have hre2 : AEStronglyMeasurable (fun y => (((W.out s₂ y).re : ℝ) : ℂ))
      (B0579.cellMeasure (dd ν s₂) m) := by
    rw [hO]
    exact (memLp_jscale_real (a := clockA ν s₂) hm ha2
      (W.hω₁.memX s₂ h12)).aestronglyMeasurable
  have e1 := xNorm_sq_re_im _ _ W.inp hre1
  have e2 := xNorm_sq_re_im _ _ (W.out s₂) hre2
  rw [hI, hI'] at e1
  rw [hO, hO'] at e2
  have hsq : xNorm (dd ν s₂) m (W.out s₂) ^ (2 : ℝ) ≤ (C * xNorm (dd ν s₁) m W.inp) ^ (2 : ℝ) := by
    rw [e2, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1, mul_add]
    refine add_le_add ?_ ?_
    · rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      exact ENNReal.rpow_le_rpow hb1 (by norm_num)
    · rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      exact ENNReal.rpow_le_rpow hb2 (by norm_num)
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 hsq

/-- Uniqueness: witnesses with a.e. equal inputs have a.e. equal outputs. -/
theorem Wit.out_ae_eq {t₁ t₂ : ℝ} (hFree : FreeEnergyHyp ν m tr t₁ t₂) (W W' : Wit ν m tr s₁)
    {s₂ : ℝ} (h1 : t₁ ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ t₂) (hm : 0 ≤ m)
    (ha1 : 1 ≤ clockA ν s₁) (ha2 : 1 ≤ clockA ν s₂)
    (hae : W.inp =ᵐ[B0579.cellMeasure (dd ν s₁) m] W'.inp) :
    W.out s₂ =ᵐ[B0579.cellMeasure (dd ν s₂) m] W'.out s₂ := by
  set V := W.add (W'.smul (-1))
  have hVin : V.inp =ᵐ[B0579.cellMeasure (dd ν s₁) m] 0 := by
    have hV : V.inp = fun y => W.inp y + (-1 : ℂ) * W'.inp y := by
      show (W.add (W'.smul (-1))).inp = _
      rw [Wit.inp_add, Wit.inp_smul]
    rw [hV]
    filter_upwards [hae] with y hy
    simp [hy]
  have h0 : xNorm (dd ν s₁) m V.inp = 0 := by
    unfold xNorm
    rw [eLpNorm_congr_ae hVin]
    simp
  have hb := V.bound hFree h1 h12 h2 hm ha1 ha2
  rw [h0, mul_zero, nonpos_iff_eq_zero] at hb
  have hmeas := (V.memLp_out h12 hm ha2).aestronglyMeasurable
  have hz := (eLpNorm_eq_zero_iff hmeas two_ne_zero).1 hb
  have hVout : V.out s₂ = fun y => W.out s₂ y + (-1 : ℂ) * W'.out s₂ y := by
    show (W.add (W'.smul (-1))).out s₂ = _
    rw [Wit.out_add, Wit.out_smul]
  rw [hVout] at hz
  filter_upwards [hz] with y hy
  simp only [Pi.zero_apply] at hy
  linear_combination hy

end Leaf1Aux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
