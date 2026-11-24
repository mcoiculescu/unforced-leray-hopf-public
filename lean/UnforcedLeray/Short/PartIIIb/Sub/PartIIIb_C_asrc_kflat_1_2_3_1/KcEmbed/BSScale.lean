import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.VelNormScale

/-!


Source of record: `the November 2 reference manuscript`, lines 3228-3240
(`eq:ct-embeddings`) and 3176-3184.

Proof. Write `s = √a`, `ψ_s(z) = ψ(s⁻¹ z)` for a test `ψ` of the cell `c/s`; then `ψ_s` is a test of
the cell `c`, `pd ψ(y) = s pd ψ_s(s y)`, and every integral over `cell (c/s)` of an integrand of the
form `G(s y)` is `a⁻¹` times the integral over `cell c` of `G` (`cv_cell`). The three conjuncts
of `IsBiotSavart` then follow from those of `IsBiotSavart c f u` applied to `ψ_s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- Change of variables `x = √a y` from `cell (c/√a)` to `cell c`, for a Bochner integral. -/
lemma cv_cell {c a : ℝ} (ha : 0 < a) (G : ℝ × ℝ → ℂ) :
    a • ∫ y in B0579.cell (cellLen c a), G (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      ∫ z in B0579.cell c, G z := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hgc : ⇑(MeasurableEquiv.smul₀ (Real.sqrt a)⁻¹ (inv_ne_zero hs) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ)) =
      fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z := rfl
  have h1 := integral_map_equiv (μ := volume.restrict (B0579.cell c))
    (MeasurableEquiv.smul₀ (Real.sqrt a)⁻¹ (inv_ne_zero hs) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ))
    (fun y : ℝ × ℝ => G (Real.sqrt a * y.1, Real.sqrt a * y.2))
  rw [hgc, E0.RsDil.map_dilate_restrict ha, integral_smul_measure,
    ENNReal.toReal_ofReal ha.le] at h1
  refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  show G (Real.sqrt a * ((Real.sqrt a)⁻¹ * x.1), Real.sqrt a * ((Real.sqrt a)⁻¹ * x.2)) = G x
  congr 1
  exact Prod.ext (mul_inv_cancel_left₀ hs x.1) (mul_inv_cancel_left₀ hs x.2)

/-- The dilation `y ↦ √a y` is quasi measure preserving from `cell (c/√a)` to `cell c`. -/
lemma qmp_cell_smul {c a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ => Real.sqrt a • y)
      (volume.restrict (B0579.cell (cellLen c a))) (volume.restrict (B0579.cell c)) := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hT : Measurable (fun y : ℝ × ℝ => Real.sqrt a • y) := measurable_const_smul _
  have key : ∀ y : ℝ × ℝ, y ∈ B0579.cell (cellLen c a) ↔ Real.sqrt a • y ∈ B0579.cell c := by
    intro y
    have h := E0.RsDil.smul_inv_mem_cell_iff (c := c) ha (Real.sqrt a • y)
    rwa [inv_smul_smul₀ hs] at h
  refine ⟨hT, ?_⟩
  apply E0.RsDil.ac_of_preimage hT
  intro S hS hS0
  rw [Measure.restrict_apply hS] at hS0
  rw [Measure.restrict_apply (hT hS)]
  refine measure_mono_null ?_ (?_ : volume ((fun y : ℝ × ℝ => Real.sqrt a • y)⁻¹' (S ∩ B0579.cell c)) = 0)
  · intro y hy
    exact ⟨hy.1, (key y).1 hy.2⟩
  · rw [Measure.addHaar_preimage_smul volume hs, hS0, mul_zero]

end UnforcedLeray.Short.IIIa

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeasureTheory Set Filter Topology

/-- **`isBiotSavart_jscaleInv`** (source 3228-3240, `eq:ct-embeddings`): the rescaled pair
`(J_a⁻¹ f, a^{3/2} u(√a ·))` is a Biot-Savart pair on the cell `c/√a`. -/
theorem isBiotSavart_jscaleInv (c a : ℝ) (hc : 0 < c) (ha : 0 < a) (f : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (h : IIIa.IsBiotSavart c f u) :
    IIIa.IsBiotSavart (IIIa.cellLen c a) (IIIa.JscaleInv a f)
      (fun y j => ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsne : Real.sqrt a ≠ 0 := hs.ne'
  have hcoef : a ^ ((3 : ℝ) / 2) * Real.sqrt a = a ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha, show (3 : ℝ) / 2 + 1 / 2 = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
  have hc' : ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = ((a ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hcoef]
  have e1 : ∀ y : ℝ × ℝ, ((Real.sqrt a)⁻¹ * (Real.sqrt a * y.1),
      (Real.sqrt a)⁻¹ * (Real.sqrt a * y.2)) = y :=
    fun y => Prod.ext (inv_mul_cancel_left₀ hsne _) (inv_mul_cancel_left₀ hsne _)
  have e2 : IIIa.cellLen c a / (Real.sqrt a)⁻¹ = c := by
    unfold IIIa.cellLen; field_simp
  have htest : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (IIIa.cellLen c a) ψ →
      B0579.IsCylTest c (fun z : ℝ × ℝ => ψ ((Real.sqrt a)⁻¹ * z.1, (Real.sqrt a)⁻¹ * z.2)) := by
    intro ψ hψ
    have h' := IIIa.E0.RsDil.isCylTest_dilate (inv_pos.2 hs) hψ
    rw [e2] at h'
    exact h'
  have hpd : ∀ (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest (IIIa.cellLen c a) ψ → ∀ (j : Fin 2) (y : ℝ × ℝ),
      B0579.pd j ψ y = Real.sqrt a * B0579.pd j
        (fun z : ℝ × ℝ => ψ ((Real.sqrt a)⁻¹ * z.1, (Real.sqrt a)⁻¹ * z.2))
        (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
    intro ψ hψ j y
    have h := IIIa.E0.RsDil.pd_dilate (Real.sqrt a)⁻¹ j ψ hψ.differentiable
      (Real.sqrt a * y.1, Real.sqrt a * y.2)
    rw [e1 y] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hsne, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · -- integrability of the scaled velocity components
    intro j
    have hT := IIIa.qmp_cell_smul (c := c) ha
    have hcomp := IIIa.eLpNorm_component_scale (c := c) ha (fun x => u x j)
    beta_reduce at hcomp
    have hu := h1 j
    refine ⟨?_, ?_⟩
    · exact (hu.aestronglyMeasurable.comp_quasiMeasurePreserving hT).const_mul _
    · rw [hcomp]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.eLpNorm_lt_top
  · -- divergence
    intro ψ hψ
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ × ℝ → ℝ,
        P = fun z => ψ ((Real.sqrt a)⁻¹ * z.1, (Real.sqrt a)⁻¹ * z.2) := ⟨_, rfl⟩
    have hP : B0579.IsCylTest c P := by rw [hPdef]; exact htest ψ hψ
    have hpdP : ∀ (j : Fin 2) (y : ℝ × ℝ), B0579.pd j ψ y =
        Real.sqrt a * B0579.pd j P (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      intro j y; subst hPdef; exact hpd ψ hψ j y
    obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun z => ((a ^ 2 : ℝ) : ℂ) *
        (u z 0 * ((B0579.pd 0 P z : ℝ) : ℂ) + u z 1 * ((B0579.pd 1 P z : ℝ) : ℂ)) := ⟨_, rfl⟩
    have hGint : ∫ z in B0579.cell c, G z = 0 := by
      simp only [hGdef]
      rw [integral_const_mul, h2 P hP, mul_zero]
    have hmain := IIIa.cv_cell (c := c) ha G
    rw [hGint] at hmain
    have hG : ∀ y : ℝ × ℝ,
        ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
            ((B0579.pd 0 ψ y : ℝ) : ℂ) +
          ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
            ((B0579.pd 1 ψ y : ℝ) : ℂ) =
        G (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      intro y
      simp only [hGdef, hpdP 0 y, hpdP 1 y, Complex.ofReal_mul]
      linear_combination
        (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
            ((B0579.pd 0 P (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) +
          u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
            ((B0579.pd 1 P (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) * hc'
    refine (integral_congr_ae (Filter.Eventually.of_forall hG)).trans ?_
    exact (smul_eq_zero.1 hmain).resolve_left ha.ne'
  · -- curl
    intro ψ hψ
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ × ℝ → ℝ,
        P = fun z => ψ ((Real.sqrt a)⁻¹ * z.1, (Real.sqrt a)⁻¹ * z.2) := ⟨_, rfl⟩
    have hP : B0579.IsCylTest c P := by rw [hPdef]; exact htest ψ hψ
    have hpdP : ∀ (j : Fin 2) (y : ℝ × ℝ), B0579.pd j ψ y =
        Real.sqrt a * B0579.pd j P (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      intro j y; subst hPdef; exact hpd ψ hψ j y
    have hPy : ∀ y : ℝ × ℝ, P (Real.sqrt a * y.1, Real.sqrt a * y.2) = ψ y := by
      intro y
      rw [hPdef]
      show ψ ((Real.sqrt a)⁻¹ * (Real.sqrt a * y.1), (Real.sqrt a)⁻¹ * (Real.sqrt a * y.2)) = ψ y
      rw [e1 y]
    obtain ⟨GLf, hGLdef⟩ : ∃ GLf : ℝ × ℝ → ℂ, GLf = fun z => ((a ^ 2 : ℝ) : ℂ) *
        (f z * ((P z : ℝ) : ℂ)) := ⟨_, rfl⟩
    obtain ⟨GRf, hGRdef⟩ : ∃ GRf : ℝ × ℝ → ℂ, GRf = fun z => ((a ^ 2 : ℝ) : ℂ) *
        (u z 0 * ((B0579.pd 1 P z : ℝ) : ℂ) - u z 1 * ((B0579.pd 0 P z : ℝ) : ℂ)) := ⟨_, rfl⟩
    have hL : ∀ y : ℝ × ℝ, IIIa.JscaleInv a f y * ((ψ y : ℝ) : ℂ) =
        GLf (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      intro y
      simp only [hGLdef, IIIa.JscaleInv]
      rw [hPy y]
      ring
    have hR : ∀ y : ℝ × ℝ,
        ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
            ((B0579.pd 1 ψ y : ℝ) : ℂ) -
          ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
            ((B0579.pd 0 ψ y : ℝ) : ℂ) =
        GRf (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      intro y
      simp only [hGRdef, hpdP 1 y, hpdP 0 y, Complex.ofReal_mul]
      linear_combination
        (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
            ((B0579.pd 1 P (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ) -
          u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
            ((B0579.pd 0 P (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) * hc'
    have hGLR : ∫ z in B0579.cell c, GLf z = ∫ z in B0579.cell c, GRf z := by
      simp only [hGLdef, hGRdef]
      rw [integral_const_mul, integral_const_mul, h3 P hP]
    have hcvL := IIIa.cv_cell (c := c) ha GLf
    have hcvR := IIIa.cv_cell (c := c) ha GRf
    refine (integral_congr_ae (Filter.Eventually.of_forall hL)).trans ?_
    refine Eq.trans ?_ (integral_congr_ae (Filter.Eventually.of_forall hR)).symm
    refine smul_right_injective ℂ ha.ne' ?_
    exact hcvL.trans (hGLR.trans hcvR.symm)

end UnforcedLeray.Short.PartIIIb.Concrete
