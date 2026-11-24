import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.WeakDerivRiesz

/-!
# `PartIII-a:T21/2/7/2/1/1/5/13`: the weighted weak derivative from a bounded pairing

Source of record: `the November 2 reference manuscript` (SP), lines 3056-3057
(the bounded pairing gives the derivative), 3044-3047 (the weights).

This is the weighted analogue of `weakDerivOfBoundedPairing` (`Sub/T21_2_1/Kernel/WeakDerivRiesz.lean`):
the Hilbert space is `L²(cellMeasure c (-m))`, and the embedding of a real cylinder test `ψ` is
`ι ψ = ⟨x⟩^m ψ`, which has `‖ι ψ‖ = ‖ψ‖_{X_{m,c}}` (`eLpNorm_mulFun`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The embedding of real cylinder tests into `X_{m,c}`. -/
def wwdJ (c m : ℝ) : wdrW c →ₗ[ℝ] B0579.X c m where
  toFun w := (B0579.IsCylTest.memLp w.2 m).toLp (w : ℝ × ℝ → ℝ)
  map_add' a b := by
    have := MemLp.toLp_add (B0579.IsCylTest.memLp a.2 m) (B0579.IsCylTest.memLp b.2 m)
    simpa using this
  map_smul' c' a := by
    have := MemLp.toLp_const_smul c' (B0579.IsCylTest.memLp a.2 m)
    simpa using this

/-- The weighted embedding `ψ ↦ ⟨x⟩^m ψ` of real cylinder tests into `X_{-m,c}`. -/
def wwdI (c m : ℝ) : wdrW c →ₗ[ℝ] B0579.X c (-m) :=
  (B0579.mulW c m (-m)).toLinearMap ∘ₗ wwdJ c m

theorem wwdI_apply (c m : ℝ) (w : wdrW c) :
    wwdI c m w = B0579.mulW c m (-m) (wwdJ c m w) := rfl

theorem wwdJ_apply (c m : ℝ) (w : wdrW c) :
    wwdJ c m w = (B0579.IsCylTest.memLp w.2 m).toLp (w : ℝ × ℝ → ℝ) := rfl

theorem wwd_exp (m : ℝ) : (m - -m) / 2 = m := by ring

theorem wwd_jb_inv_mul (x : B0579.Plane) (m : ℝ) :
    B0579.jb x ^ (-m) * B0579.jb x ^ m = 1 := by
  rw [B0579.jb_rpow_mul, show -m + m = 0 by ring, Real.rpow_zero]

/-- A.e. on the cell, `ι ψ = ⟨x⟩^m ψ`. -/
theorem wwdI_ae (c m : ℝ) (w : wdrW c) :
    (wwdI c m w : ℝ × ℝ → ℝ) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => B0579.jb x ^ m * (w : ℝ × ℝ → ℝ) x := by
  have h1 : (wwdI c m w : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c (-m)]
      fun x => B0579.jb x ^ ((m - -m) / 2) * (wwdJ c m w : ℝ × ℝ → ℝ) x :=
    B0579.coeFn_mulW c m (-m) (wwdJ c m w)
  have h2 : (wwdJ c m w : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c m] (w : ℝ × ℝ → ℝ) := by
    rw [wwdJ_apply]
    exact MemLp.coeFn_toLp _
  have h1' := (B0579.ac_cellMeasure c (-m)).ae_le h1
  have h2' := (B0579.ac_cellMeasure c m).ae_le h2
  filter_upwards [h1', h2'] with x hx1 hx2
  rw [hx1, hx2, wwd_exp]

theorem wwdI_norm (c m : ℝ) (w : wdrW c) :
    ‖wwdI c m w‖ = (eLpNorm (w : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c m)).toReal := by
  rw [wwdI_apply, LinearIsometry.norm_map, wwdJ_apply, Lp.norm_toLp]

/-- The pairing with the weighted embedding is the cell integral. -/
theorem wwd_inner (c m : ℝ) (g : B0579.X c (-m)) (w : wdrW c) :
    inner ℝ g (wwdI c m w) = ∫ x in B0579.cell c, g x * (w : ℝ × ℝ → ℝ) x := by
  rw [L2.inner_def]
  have hae : (wwdI c m w : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c (-m)]
      fun x => B0579.jb x ^ m * (w : ℝ × ℝ → ℝ) x :=
    (B0579.cellMeasure_ac c (-m)).ae_le (wwdI_ae c m w)
  have h1 : (fun x => inner ℝ (g x) ((wwdI c m w : ℝ × ℝ → ℝ) x)) =ᵐ[B0579.cellMeasure c (-m)]
      fun x => g x * (B0579.jb x ^ m * (w : ℝ × ℝ → ℝ) x) := by
    filter_upwards [hae] with x hx
    rw [Real.inner_apply, hx]
  rw [integral_congr_ae h1, B0579.integral_cellMeasure]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, B0579.coe_density]
  linear_combination (g x * (w : ℝ × ℝ → ℝ) x) * wwd_jb_inv_mul x m

theorem wwd_integrableOn (c m : ℝ) (g : B0579.X c (-m)) (w : wdrW c) :
    IntegrableOn (fun x => g x * (w : ℝ × ℝ → ℝ) x) (B0579.cell c) := by
  have h := (Lp.memLp g).integrable_mul (Lp.memLp (wwdI c m w))
  rw [B0579.integrable_cellMeasure_iff] at h
  refine h.congr_fun_ae ?_
  filter_upwards [wwdI_ae c m w] with x hx
  simp only [Pi.mul_apply, NNReal.smul_def, smul_eq_mul, B0579.coe_density]
  rw [hx]
  linear_combination (g x * (w : ℝ × ℝ → ℝ) x) * wwd_jb_inv_mul x m

theorem weightedWeakDerivOfPairing : WeightedWeakDerivOfPairing := by
  intro c m hc f j M hM hbd
  let Iχ : wdrW c → ℂ := fun w =>
    ∫ x in B0579.cell c, f x * (B0579.pd j (w : ℝ × ℝ → ℝ) x : ℂ)
  have hIadd : ∀ w1 w2 : wdrW c, Iχ (w1 + w2) = Iχ w1 + Iχ w2 := by
    intro w1 w2
    have h1 := (hbd _ w1.2).1
    have h2 := (hbd _ w2.2).1
    show ∫ x in B0579.cell c, f x * (B0579.pd j ((w1 : ℝ × ℝ → ℝ) + (w2 : ℝ × ℝ → ℝ)) x : ℂ) = _
    simp_rw [wdr_pd_add j w1.2 w2.2, Complex.ofReal_add, mul_add]
    exact integral_add h1 h2
  have hIsmul : ∀ (a : ℝ) (w : wdrW c), Iχ (a • w) = (a : ℂ) * Iχ w := by
    intro a w
    show ∫ x in B0579.cell c, f x * (B0579.pd j (a • (w : ℝ × ℝ → ℝ)) x : ℂ) = _
    simp_rw [wdr_pd_smul j a w.2, Complex.ofReal_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  let ℓr : wdrW c →ₗ[ℝ] ℝ :=
    { toFun := fun w => -(Iχ w).re
      map_add' := fun a b => by simp [hIadd]; ring
      map_smul' := fun c' a => by
        have := hIsmul c' a
        simp only [this, Complex.re_ofReal_mul, smul_eq_mul, RingHom.id_apply]; ring }
  let ℓi : wdrW c →ₗ[ℝ] ℝ :=
    { toFun := fun w => -(Iχ w).im
      map_add' := fun a b => by simp [hIadd]; ring
      map_smul' := fun c' a => by
        have := hIsmul c' a
        simp only [this, Complex.im_ofReal_mul, smul_eq_mul, RingHom.id_apply]; ring }
  have hnorm : ∀ w : wdrW c, ‖Iχ w‖ ≤ M.toReal * ‖wwdI c m w‖ := by
    intro w
    have hfin : eLpNorm (w : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c m) ≠ ⊤ :=
      (B0579.IsCylTest.memLp w.2 m).2.ne
    have h := (hbd _ w.2).2
    have hne : M * eLpNorm (w : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c m) ≠ ⊤ :=
      ENNReal.mul_ne_top hM hfin
    have h2 := ENNReal.toReal_mono hne h
    rw [toReal_enorm, ENNReal.toReal_mul] at h2
    rw [wwdI_norm]
    exact h2
  have hC0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  obtain ⟨gr, hgr, hgr'⟩ := exists_riesz_of_linear (wwdI c m) ℓr hC0 (fun w =>
    (show |-(Iχ w).re| ≤ _ by rw [abs_neg]; exact (Complex.abs_re_le_norm _).trans (hnorm w)))
  obtain ⟨gi, hgi, hgi'⟩ := exists_riesz_of_linear (wwdI c m) ℓi hC0 (fun w =>
    (show |-(Iχ w).im| ≤ _ by rw [abs_neg]; exact (Complex.abs_im_le_norm _).trans (hnorm w)))
  let g : ℝ × ℝ → ℂ := fun x => ((gr x : ℝ) : ℂ) + ((gi x : ℝ) : ℂ) * Complex.I
  have hgrL : MemLp (fun x => (gr : ℝ × ℝ → ℝ) x) 2 (B0579.cellMeasure c (-m)) := Lp.memLp gr
  have hgiL : MemLp (fun x => (gi : ℝ × ℝ → ℝ) x) 2 (B0579.cellMeasure c (-m)) := Lp.memLp gi
  have hgrc : MemLp (fun x => (((gr : ℝ × ℝ → ℝ) x : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) :=
    hgrL.ofReal
  have hgic : MemLp (fun x => (((gi : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I) 2
      (B0579.cellMeasure c (-m)) :=
    hgiL.ofReal.mul_const Complex.I
  have hgL : MemLp g 2 (B0579.cellMeasure c (-m)) := hgrc.add hgic
  have hint : ∀ w : wdrW c, IntegrableOn (fun x => g x * (w : ℝ × ℝ → ℝ) x : ℝ × ℝ → ℂ) (B0579.cell c) := by
    intro w
    have hr := wwd_integrableOn c m gr w
    have hi := wwd_integrableOn c m gi w
    have e : (fun x => g x * ((w : ℝ × ℝ → ℝ) x : ℂ)) = fun x =>
        (((gr : ℝ × ℝ → ℝ) x * (w : ℝ × ℝ → ℝ) x : ℝ) : ℂ) +
        (((gi : ℝ × ℝ → ℝ) x * (w : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I := by
      funext x
      simp only [g]
      push_cast
      ring
    rw [e]
    exact hr.ofReal.add (hi.ofReal.mul_const Complex.I)
  refine ⟨g, ⟨fun ψ hψ => ⟨(hbd ψ hψ).1, hint ⟨ψ, hψ⟩⟩, fun ψ hψ => ?_⟩, hgL, ?_⟩
  · have hr := hgr' ⟨ψ, hψ⟩
    have hi := hgi' ⟨ψ, hψ⟩
    rw [wwd_inner] at hr hi
    have hsplit : ∫ x in B0579.cell c, g x * (ψ x : ℂ) =
        ((∫ x in B0579.cell c, (gr : ℝ × ℝ → ℝ) x * ψ x : ℝ) : ℂ) +
        ((∫ x in B0579.cell c, (gi : ℝ × ℝ → ℝ) x * ψ x : ℝ) : ℂ) * Complex.I := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_mul_const,
        ← integral_add]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [g]; push_cast; ring
      · exact (wwd_integrableOn c m gr ⟨ψ, hψ⟩).ofReal
      · exact ((wwd_integrableOn c m gi ⟨ψ, hψ⟩).ofReal).mul_const _
    rw [hsplit]
    apply Complex.ext
    · simp only [ℓr] at hr
      simp [Iχ] at hr ⊢
      linarith
    · simp only [ℓi] at hi
      simp [Iχ] at hi ⊢
      linarith
  · show eLpNorm g 2 (B0579.cellMeasure c (-m)) ≤ 2 * M
    have hle : ∀ h : Lp ℝ 2 (B0579.cellMeasure c (-m)), ‖h‖ ≤ M.toReal →
        eLpNorm (h : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c (-m)) ≤ M := by
      intro h hh
      have hfin : eLpNorm (h : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c (-m)) ≠ ⊤ :=
        (Lp.memLp h).2.ne
      rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hM]
      exact ENNReal.ofReal_le_ofReal (by rw [← Lp.norm_def]; exact hh)
    have e1 : eLpNorm (fun x => (((gr : ℝ × ℝ → ℝ) x : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) ≤ M := by
      have : eLpNorm (fun x => (((gr : ℝ × ℝ → ℝ) x : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) =
          eLpNorm (gr : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c (-m)) :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
      rw [this]; exact hle gr hgr
    have e2 : eLpNorm (fun x => (((gi : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I) 2
        (B0579.cellMeasure c (-m)) ≤ M := by
      have : eLpNorm (fun x => (((gi : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I) 2
          (B0579.cellMeasure c (-m)) = eLpNorm (gi : ℝ × ℝ → ℝ) 2 (B0579.cellMeasure c (-m)) :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
      rw [this]; exact hle gi hgi
    calc eLpNorm g 2 (B0579.cellMeasure c (-m)) ≤ _ := eLpNorm_add_le hgrc.1 hgic.1 (by norm_num)
      _ ≤ M + M := add_le_add e1 e2
      _ = 2 * M := (two_mul M).symm

end UnforcedLeray.Short.IIIa
