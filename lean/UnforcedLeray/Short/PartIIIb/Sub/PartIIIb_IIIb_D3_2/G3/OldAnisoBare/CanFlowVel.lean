import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBareOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.RealBridge

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4/2`: canonical linearised flow and Biot-Savart velocity of `xiBareOf`

Source of record: `the November 2 reference manuscript` (lines 4416-4426, 4520-4543).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst

private theorem isBS_const_mul {c : ℝ} {ω : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (z : ℂ) (h : IIIa.IsBiotSavart c ω u) :
    IIIa.IsBiotSavart c (fun x => z * ω x) (fun x j => z * u x j) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).const_mul z, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have heq : (fun x => z * u x 0 * (B0579.pd 0 ψ x : ℂ) + z * u x 1 * (B0579.pd 1 ψ x : ℂ)) =
        fun x => z * (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      ext x; ring
    rw [heq, integral_const_mul, h2 ψ hψ, mul_zero]
  · have heq1 : (fun x => z * ω x * (ψ x : ℂ)) = fun x => z * (ω x * (ψ x : ℂ)) := by
      ext x; ring
    have heq2 : (fun x => z * u x 0 * (B0579.pd 1 ψ x : ℂ) - z * u x 1 * (B0579.pd 0 ψ x : ℂ)) =
        fun x => z * (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      ext x; ring
    rw [heq1, heq2, integral_const_mul, integral_const_mul, h3 ψ hψ]

private theorem isBS_re_of_memLp {c : ℝ} {ω : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hω : MemLp ω 2 (volume.restrict (B0579.cell c))) (h : IIIa.IsBiotSavart c ω u) :
    IIIa.IsBiotSavart c (fun x => (((ω x).re : ℝ) : ℂ))
      (fun x j => (((u x j).re : ℝ) : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => ((h1 j).re).ofReal, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hI : Integrable (fun x => u x 0 * (B0579.pd 0 ψ x : ℂ) +
        u x 1 * (B0579.pd 1 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
      (IIIa.BSAux.integrable_u_mul (fun x => u x 0) (h1 0) (hψ.pd 0)).add
        (IIIa.BSAux.integrable_u_mul (fun x => u x 1) (h1 1) (hψ.pd 1))
    calc ∫ x in B0579.cell c,
          ((((u x 0).re : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ) +
            (((u x 1).re : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ))
        = ∫ x in B0579.cell c,
            ((((u x 0 * (B0579.pd 0 ψ x : ℂ) +
              u x 1 * (B0579.pd 1 ψ x : ℂ)).re : ℝ)) : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp [Complex.add_re, Complex.mul_re]
      _ = (((∫ x in B0579.cell c,
              (u x 0 * (B0579.pd 0 ψ x : ℂ) +
                u x 1 * (B0579.pd 1 ψ x : ℂ))).re : ℝ) : ℂ) := by
          rw [integral_complex_ofReal, IIIa.BSAux.integral_re' hI]
      _ = 0 := by rw [h2 ψ hψ]; simp
  · have hf0 : Integrable (fun x => u x 0 * (B0579.pd 1 ψ x : ℂ))
        (volume.restrict (B0579.cell c)) :=
      IIIa.BSAux.integrable_u_mul (fun x => u x 0) (h1 0) (hψ.pd 1)
    have hf1 : Integrable (fun x => u x 1 * (B0579.pd 0 ψ x : ℂ))
        (volume.restrict (B0579.cell c)) :=
      IIIa.BSAux.integrable_u_mul (fun x => u x 1) (h1 1) (hψ.pd 0)
    have hf : Integrable (fun x => u x 0 * (B0579.pd 1 ψ x : ℂ) -
        u x 1 * (B0579.pd 0 ψ x : ℂ)) (volume.restrict (B0579.cell c)) := hf0.sub hf1
    have hωψ : Integrable (fun x => ω x * (ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
      IIIa.BSAux.integrable_u_mul ω hω hψ
    calc ∫ x in B0579.cell c, (((ω x).re : ℝ) : ℂ) * (ψ x : ℂ)
        = ∫ x in B0579.cell c, ((((ω x * (ψ x : ℂ)).re : ℝ)) : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp [Complex.mul_re]
      _ = ((((∫ x in B0579.cell c, ω x * (ψ x : ℂ)).re : ℝ)) : ℂ) := by
          rw [integral_complex_ofReal, IIIa.BSAux.integral_re' hωψ]
      _ = ((((∫ x in B0579.cell c,
              (u x 0 * (B0579.pd 1 ψ x : ℂ) -
                u x 1 * (B0579.pd 0 ψ x : ℂ))).re : ℝ)) : ℂ) := by
          rw [h3 ψ hψ]
      _ = ∫ x in B0579.cell c,
            ((((u x 0 * (B0579.pd 1 ψ x : ℂ) -
              u x 1 * (B0579.pd 0 ψ x : ℂ)).re : ℝ)) : ℂ) := by
          rw [← IIIa.BSAux.integral_re' hf, ← integral_complex_ofReal]
      _ = ∫ x in B0579.cell c,
            ((((u x 0).re : ℝ) : ℂ) * (B0579.pd 1 ψ x : ℂ) -
              (((u x 1).re : ℝ) : ℂ) * (B0579.pd 0 ψ x : ℂ)) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp [Complex.sub_re, Complex.mul_re]

/-- **Leaf 2 (`G3/1/4/2`): canonical linearised flow and cell Biot-Savart velocity of `xiBareOf`**. -/
theorem bareCanFlowVel : G3.BareCanFlowVel := by
  intro P κ ν hν _ m _ tr FI χo ε μ qc hqc_ae
  let q0 : Xmc (cOf ν) m := qc
  obtain ⟨u, hflow0⟩ := FI.ev.flow 0 le_rfl q0
  set w : ℝ → ℝ × ℝ → ℂ := fun s => xFn (FI.ev.U s 0 q0)
  have hflow : IIIa.IsLinearisedFlow ν (cOf ν) m tr 0 (IIIa.preparedDatum P ν) w u :=
    { initial := hflow0.initial.trans hqc_ae
      memX := hflow0.memX
      strongCont := hflow0.strongCont
      biotSavart := hflow0.biotSavart
      integrable := hflow0.integrable
      timeIntegrable := hflow0.timeIntegrable
      weak := fun φ hφ s hs => by
        rw [hflow0.weak φ hφ s hs]
        congr 1
        refine integral_congr_ae (hqc_ae.mono fun x hx => ?_)
        change xFn qc x * (φ x : ℂ) = IIIa.preparedDatum P ν x * (φ x : ℂ)
        rw [hx] }
  refine ⟨w, u, hflow, fun a s hs => ?_⟩
  let y : Xmc (cOf ν) m := FI.ev.U s 0 q0
  let sc : ℂ := (s : ℂ) ^ (-(μ : ℂ))
  let ξ : Xmc (cOf ν) m := sc • (a • y + (starRingEnd ℂ a) • conjX y)
  have hsc_conj : (starRingEnd ℂ) sc = sc := by
    change (starRingEnd ℂ) ((s : ℂ) ^ (-(μ : ℂ))) = (s : ℂ) ^ (-(μ : ℂ))
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hs, Complex.conj_ofReal]
  have hξ_real : conjX ξ = ξ := by
    change conjX (sc • (a • y + (starRingEnd ℂ a) • conjX y)) =
      sc • (a • y + (starRingEnd ℂ a) • conjX y)
    rw [conjX_smul, hsc_conj, conjX_add, conjX_smul, conjX_smul, conjX_conjX,
      RingHomCompTriple.comp_apply, RingHom.id_apply, add_comm]
  have hbs_kc : IIIa.IsBiotSavart (cOf ν) (xFn ξ) (kcC ξ) := isBiotSavart_kc hξ_real
  let Z : ℂ := 2 * (a * sc)
  have hξ_ae : xFn ξ =ᵐ[volume.restrict (B0579.cell (cOf ν))]
      fun p => (((Z * w s p).re : ℝ) : ℂ) := by
    filter_upwards [xFn_smul sc (a • y + (starRingEnd ℂ a) • conjX y),
      xFn_add (a • y) ((starRingEnd ℂ a) • conjX y),
      xFn_smul a y, xFn_smul (starRingEnd ℂ a) (conjX y), xFn_conjX y] with p h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
    change sc * (a * w s p + (starRingEnd ℂ a) * (starRingEnd ℂ (w s p))) =
      (((2 * (a * sc) * w s p).re : ℝ) : ℂ)
    have hconj : (starRingEnd ℂ) (a * sc * w s p) =
        sc * ((starRingEnd ℂ a) * (starRingEnd ℂ (w s p))) := by
      rw [map_mul, map_mul, hsc_conj]
      ring
    have halg : sc * (a * w s p + (starRingEnd ℂ a) * (starRingEnd ℂ (w s p))) =
        (a * sc * w s p) + (starRingEnd ℂ) (a * sc * w s p) := by
      rw [hconj]; ring
    rw [halg]
    apply Complex.ext <;> simp [mul_assoc] <;> ring
  have hw_lp : MemLp (w s) 2 (volume.restrict (B0579.cell (cOf ν))) :=
    (xFn_memLp y).mono_measure
      (UnforcedLeray.B0581.cellVol_le_cellMeasure (cOf ν) (zero_le_one.trans one_le_of_fact))
  have hbs_Z : IIIa.IsBiotSavart (cOf ν) (fun p => (((Z * w s p).re : ℝ) : ℂ))
      (fun p j => (((Z * u s p j).re : ℝ) : ℂ)) :=
    isBS_re_of_memLp (hw_lp.const_mul Z) (isBS_const_mul Z (hflow0.biotSavart s hs))
  have hbs_can : IIIa.IsBiotSavart (cOf ν) (xFn ξ)
      (fun p j => ((canVelRe a μ s (u s) p j : ℝ) : ℂ)) := by
    refine isBS_congr_omega (IIIa.BSAux.isBS_congr hbs_Z fun j => Eventually.of_forall fun p => ?_)
      hξ_ae.symm
    congr 1
    fin_cases j
    · simp only [canVelRe, Z, sc]
      rw [mul_assoc, mul_assoc, Complex.mul_re]
      simp
    · simp only [canVelRe, Z, sc]
      rw [mul_assoc, mul_assoc, Complex.mul_re]
      simp
  have huniq := IIIa.CTE.isBiotSavart_unique (cOf ν) (cOf_pos hν) (xFn ξ) (kcC ξ)
    (fun p j => ((canVelRe a μ s (u s) p j : ℝ) : ℂ)) hbs_kc hbs_can
  filter_upwards [huniq] with p hp
  ext j
  exact Complex.ofReal_injective (congrFun hp j)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

end
