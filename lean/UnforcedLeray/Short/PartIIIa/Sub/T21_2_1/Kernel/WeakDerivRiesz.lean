import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# Part III-a, `PartIII-a:T21/2/1/2/12`: the weak derivative from a bounded pairing

Source of record: `the November 2 reference manuscript` (SP), lines 3056-3057
(the multiplier bound gives `∇χ ∈ L²`); generic functional analysis, no source objects.

This file proves the abstract Hahn-Banach / Riesz step used by `weakDerivOfBoundedPairing`:
a real linear functional on a subspace `S` of a real Hilbert space `H`, bounded by `C‖·‖`, is
represented by some `g ∈ H` with `‖g‖ ≤ C`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Bounded functionals on a subspace of a real Hilbert space** (Hahn-Banach, then Riesz):
a real linear functional `ℓ` on a subspace `S` with `|ℓ s| ≤ C‖s‖` (`0 ≤ C`) is the pairing
with some `g ∈ H` of norm `≤ C`. -/
theorem exists_riesz_extension {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : Submodule ℝ H) (ℓ : S →ₗ[ℝ] ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : S, |ℓ s| ≤ C * ‖(s : H)‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ s : S, ℓ s = @inner ℝ H _ g (s : H) := by
  let L : S →L[ℝ] ℝ := LinearMap.mkContinuous ℓ C (fun s => by
    rw [Real.norm_eq_abs]
    exact hC s)
  obtain ⟨G, hGext, hGnorm⟩ := exists_extension_norm_eq S L
  refine ⟨(InnerProductSpace.toDual ℝ H).symm G, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    calc ‖G‖ = ‖L‖ := hGnorm
      _ ≤ C := LinearMap.mkContinuous_norm_le ℓ hC0 _
  · intro s
    rw [InnerProductSpace.toDual_symm_apply, hGext s]
    rfl


/-- Riesz representation of a functional dominated by a linear map into a Hilbert space. -/
theorem exists_riesz_of_linear {W H : Type*} [AddCommGroup W] [Module ℝ W]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : W →ₗ[ℝ] H) (ℓ : W →ₗ[ℝ] ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w, |ℓ w| ≤ C * ‖ι w‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ w, ℓ w = @inner ℝ H _ g (ι w) := by
  have hker : LinearMap.ker ι ≤ LinearMap.ker ℓ := fun w hw => by
    have h0 : ι w = 0 := hw
    have := hC w
    rw [h0, norm_zero, mul_zero] at this
    exact abs_nonpos_iff.1 this
  let ℓ' : LinearMap.range ι →ₗ[ℝ] ℝ :=
    ((LinearMap.ker ι).liftQ ℓ hker).comp ι.quotKerEquivRange.symm.toLinearMap
  have hℓ' : ∀ w, ℓ' ⟨ι w, ⟨w, rfl⟩⟩ = ℓ w := fun w => by
    have : ι.quotKerEquivRange.symm ⟨ι w, ⟨w, rfl⟩⟩ = Submodule.Quotient.mk w := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk ι w).symm
    show ((LinearMap.ker ι).liftQ ℓ hker) (ι.quotKerEquivRange.symm ⟨ι w, ⟨w, rfl⟩⟩) = _
    rw [this]
    rfl
  obtain ⟨g, hg, hgs⟩ := exists_riesz_extension (LinearMap.range ι) ℓ' hC0 (fun s => by
    obtain ⟨_, w, hw⟩ := s
    have : (⟨_, ⟨w, hw⟩⟩ : LinearMap.range ι) = ⟨ι w, ⟨w, rfl⟩⟩ := by
      subst hw; rfl
    rw [this, hℓ']
    exact hC w)
  refine ⟨g, hg, fun w => ?_⟩
  rw [← hℓ' w, hgs]


/-! ## The concrete assembly -/

section Concrete

theorem wdr_zero (d : ℝ) : B0579.IsCylTest d (0 : ℝ × ℝ → ℝ) where
  smooth := contDiff_const
  periodic _ := rfl
  band := ⟨0, fun _ _ => rfl⟩

theorem wdr_add {d : ℝ} {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest d f) (hg : B0579.IsCylTest d g) :
    B0579.IsCylTest d (f + g) where
  smooth := hf.smooth.add hg.smooth
  periodic x := by simp only [Pi.add_apply, hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R1, h1⟩ := hf.band
    obtain ⟨R2, h2⟩ := hg.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    simp [h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)]

theorem wdr_smul {d : ℝ} (a : ℝ) {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest d f) :
    B0579.IsCylTest d (a • f) where
  smooth := contDiff_const.smul hf.smooth
  periodic x := by simp only [Pi.smul_apply, hf.periodic x]
  band := by
    obtain ⟨R, h⟩ := hf.band
    exact ⟨R, fun x hx => by simp [h x hx]⟩

theorem wdr_pd_add {d : ℝ} (k : Fin 2) {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest d f)
    (hg : B0579.IsCylTest d g) (x : ℝ × ℝ) :
    B0579.pd k (f + g) x = B0579.pd k f x + B0579.pd k g x := by
  unfold B0579.pd
  have : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
    fderiv_add (hf.differentiable x) (hg.differentiable x)
  rw [this]; rfl

theorem wdr_pd_smul {d : ℝ} (k : Fin 2) (a : ℝ) {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest d f)
    (x : ℝ × ℝ) : B0579.pd k (a • f) x = a * B0579.pd k f x := by
  unfold B0579.pd
  have : fderiv ℝ (a • f) x = a • fderiv ℝ f x := fderiv_const_smul (hf.differentiable x) a
  rw [this]; simp

theorem wdr_memLp {d : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) :
    MemLp ψ 2 (volume.restrict (B0579.cell d)) := by
  obtain ⟨R, hR⟩ := hψ.vanish
  exact B0579.memLp_cell_of_continuous hψ.continuous (B0579.isCompact_box d R)
    (fun x hx hxK => hR x hx hxK)

/-- The submodule of real cylinder tests. -/
def wdrW (d : ℝ) : Submodule ℝ (ℝ × ℝ → ℝ) where
  carrier := {ψ | B0579.IsCylTest d ψ}
  add_mem' := fun ha hb => wdr_add ha hb
  zero_mem' := wdr_zero d
  smul_mem' := fun a _ hf => wdr_smul a hf

/-- The embedding of tests into `L²(cell)`. -/
def wdrIota (d : ℝ) : wdrW d →ₗ[ℝ] Lp ℝ 2 (volume.restrict (B0579.cell d)) where
  toFun w := (wdr_memLp w.2).toLp w
  map_add' a b := by
    have := MemLp.toLp_add (wdr_memLp a.2) (wdr_memLp b.2)
    simpa using this
  map_smul' c a := by
    have := MemLp.toLp_const_smul c (wdr_memLp a.2)
    simpa using this


theorem wdr_inner_eq {d : ℝ} (g : Lp ℝ 2 (volume.restrict (B0579.cell d))) (w : wdrW d) :
    @inner ℝ _ _ g (wdrIota d w) = ∫ x in B0579.cell d, g x * (w : ℝ × ℝ → ℝ) x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h := (wdr_memLp w.2).coeFn_toLp
  filter_upwards [h] with x hx
  show inner ℝ (g x) ((wdrIota d w) x) = _
  have : (wdrIota d w) x = (w : ℝ × ℝ → ℝ) x := hx
  rw [this]
  simp [mul_comm]

theorem weakDerivOfBoundedPairing : WeakDerivOfBoundedPairing := by
  intro d hd χ k M hM hbd
  set μ := volume.restrict (B0579.cell d) with hμ
  let Iχ : wdrW d → ℂ := fun w => ∫ x in B0579.cell d, χ x * (B0579.pd k (w : ℝ × ℝ → ℝ) x : ℂ)
  have hIadd : ∀ w1 w2 : wdrW d, Iχ (w1 + w2) = Iχ w1 + Iχ w2 := by
    intro w1 w2
    have h1 := (hbd _ w1.2).1
    have h2 := (hbd _ w2.2).1
    show ∫ x in B0579.cell d, χ x * (B0579.pd k ((w1 : ℝ × ℝ → ℝ) + (w2 : ℝ × ℝ → ℝ)) x : ℂ) = _
    simp_rw [wdr_pd_add k w1.2 w2.2, Complex.ofReal_add, mul_add]
    exact integral_add h1 h2
  have hIsmul : ∀ (a : ℝ) (w : wdrW d), Iχ (a • w) = (a : ℂ) * Iχ w := by
    intro a w
    show ∫ x in B0579.cell d, χ x * (B0579.pd k (a • (w : ℝ × ℝ → ℝ)) x : ℂ) = _
    simp_rw [wdr_pd_smul k a w.2, Complex.ofReal_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  let ℓr : wdrW d →ₗ[ℝ] ℝ :=
    { toFun := fun w => -(Iχ w).re
      map_add' := fun a b => by simp [hIadd]; ring
      map_smul' := fun c a => by
        have := hIsmul c a
        simp only [this, Complex.re_ofReal_mul, smul_eq_mul, RingHom.id_apply]; ring }
  let ℓi : wdrW d →ₗ[ℝ] ℝ :=
    { toFun := fun w => -(Iχ w).im
      map_add' := fun a b => by simp [hIadd]; ring
      map_smul' := fun c a => by
        have := hIsmul c a
        simp only [this, Complex.im_ofReal_mul, smul_eq_mul, RingHom.id_apply]; ring }
  have hnorm : ∀ w : wdrW d, ‖Iχ w‖ ≤ M.toReal * ‖wdrIota d w‖ := by
    intro w
    have hfin : eLpNorm (w : ℝ × ℝ → ℝ) 2 μ ≠ ⊤ := (wdr_memLp w.2).2.ne
    have h := (hbd _ w.2).2
    have hne : M * eLpNorm (w : ℝ × ℝ → ℝ) 2 μ ≠ ⊤ := ENNReal.mul_ne_top hM hfin
    have h2 := ENNReal.toReal_mono hne h
    rw [toReal_enorm, ENNReal.toReal_mul] at h2
    have : ‖wdrIota d w‖ = (eLpNorm (w : ℝ × ℝ → ℝ) 2 μ).toReal := Lp.norm_toLp _ (wdr_memLp w.2)
    rw [this]; exact h2
  have hC0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  obtain ⟨gr, hgr, hgr'⟩ := exists_riesz_of_linear (wdrIota d) ℓr hC0 (fun w =>
    (show |-(Iχ w).re| ≤ _ by rw [abs_neg]; exact (Complex.abs_re_le_norm _).trans (hnorm w)))
  obtain ⟨gi, hgi, hgi'⟩ := exists_riesz_of_linear (wdrIota d) ℓi hC0 (fun w =>
    (show |-(Iχ w).im| ≤ _ by rw [abs_neg]; exact (Complex.abs_im_le_norm _).trans (hnorm w)))
  let g : ℝ × ℝ → ℂ := fun x => ((gr x : ℝ) : ℂ) + ((gi x : ℝ) : ℂ) * Complex.I
  have hgrL : MemLp (fun x => (gr : ℝ × ℝ → ℝ) x) 2 μ := Lp.memLp gr
  have hgiL : MemLp (fun x => (gi : ℝ × ℝ → ℝ) x) 2 μ := Lp.memLp gi
  have hgrc : MemLp (fun x => (((gr : ℝ × ℝ → ℝ) x : ℝ) : ℂ)) 2 μ := hgrL.ofReal
  have hgic : MemLp (fun x => (((gi : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I) 2 μ :=
    hgiL.ofReal.mul_const Complex.I
  have hgL : MemLp g 2 μ := hgrc.add hgic
  have hint : ∀ ψ, B0579.IsCylTest d ψ → Integrable (fun x => g x * (ψ x : ℂ)) μ := by
    intro ψ hψ
    have hψc : MemLp (fun x => (ψ x : ℂ)) 2 μ := (wdr_memLp hψ).ofReal
    exact hgL.integrable_mul hψc
  have hintr : ∀ ψ, B0579.IsCylTest d ψ → Integrable (fun x => (gr : ℝ × ℝ → ℝ) x * ψ x) μ :=
    fun ψ hψ => hgrL.integrable_mul (wdr_memLp hψ)
  have hinti : ∀ ψ, B0579.IsCylTest d ψ → Integrable (fun x => (gi : ℝ × ℝ → ℝ) x * ψ x) μ :=
    fun ψ hψ => hgiL.integrable_mul (wdr_memLp hψ)
  refine ⟨g, ⟨fun ψ hψ => ⟨(hbd ψ hψ).1, hint ψ hψ⟩, fun ψ hψ => ?_⟩, hgL, ?_⟩
  · have hr := hgr' ⟨ψ, hψ⟩
    have hi := hgi' ⟨ψ, hψ⟩
    rw [wdr_inner_eq] at hr hi
    have hsplit : ∫ x in B0579.cell d, g x * (ψ x : ℂ) =
        ((∫ x in B0579.cell d, (gr : ℝ × ℝ → ℝ) x * ψ x : ℝ) : ℂ) +
        ((∫ x in B0579.cell d, (gi : ℝ × ℝ → ℝ) x * ψ x : ℝ) : ℂ) * Complex.I := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_mul_const, ← integral_add]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [g]; push_cast; ring
      · exact (hintr ψ hψ).ofReal
      · exact (hinti ψ hψ).ofReal.mul_const _
    rw [hsplit]
    apply Complex.ext
    · simp only [ℓr] at hr
      simp [Iχ] at hr ⊢
      linarith
    · simp only [ℓi] at hi
      simp [Iχ] at hi ⊢
      linarith
  · have hle : ∀ h : Lp ℝ 2 μ, ‖h‖ ≤ M.toReal → eLpNorm (h : ℝ × ℝ → ℝ) 2 μ ≤ M := by
      intro h hh
      have hfin : eLpNorm (h : ℝ × ℝ → ℝ) 2 μ ≠ ⊤ := (Lp.memLp h).2.ne
      rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hM]
      exact ENNReal.ofReal_le_ofReal (by rw [← Lp.norm_def]; exact hh)
    have e1 : eLpNorm (fun x => (((gr : ℝ × ℝ → ℝ) x : ℝ) : ℂ)) 2 μ ≤ M := by
      have : eLpNorm (fun x => (((gr : ℝ × ℝ → ℝ) x : ℝ) : ℂ)) 2 μ = eLpNorm (gr : ℝ × ℝ → ℝ) 2 μ :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
      rw [this]; exact hle gr hgr
    have e2 : eLpNorm (fun x => (((gi : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I) 2 μ ≤ M := by
      have : eLpNorm (fun x => (((gi : ℝ × ℝ → ℝ) x : ℝ) : ℂ) * Complex.I) 2 μ =
          eLpNorm (gi : ℝ × ℝ → ℝ) 2 μ :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
      rw [this]; exact hle gi hgi
    calc eLpNorm g 2 μ ≤ _ := eLpNorm_add_le hgrc.1 hgic.1 (by norm_num)
      _ ≤ M + M := add_le_add e1 e2
      _ = 2 * M := (two_mul M).symm

end Concrete

end UnforcedLeray.Short.IIIa
