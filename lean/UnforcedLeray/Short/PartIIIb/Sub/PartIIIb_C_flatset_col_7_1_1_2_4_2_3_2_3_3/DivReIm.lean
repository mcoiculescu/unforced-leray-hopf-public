import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_3.OrthCell

/-!
# `Re v, Im v ∈ Cyl.divFree c` for a periodic weakly divergence-free field

Helper for `pepsC0SliceOrthCell` (source `the November 2 reference manuscript`
1650-1656, 1676).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (toL2v reVec imVec)

theorem pair_grad (c : ℝ) (g : UnforcedLeray.Cyl.L2v c) (ψ : ℝ × ℝ → ℝ)
    (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    Integrable (fun x : ℝ × ℝ => (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 *
        UnforcedLeray.B0579.pd 0 ψ x +
        (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 * UnforcedLeray.B0579.pd 1 ψ x)
      (UnforcedLeray.Cyl.cellμ c) ∧
    ∀ hS : UnforcedLeray.Sob.IsCylTest c ψ,
      ⟪UnforcedLeray.Cyl.gradL hS, g⟫_ℝ = ∫ x, ((g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 *
        UnforcedLeray.B0579.pd 0 ψ x +
        (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 * UnforcedLeray.B0579.pd 1 ψ x)
        ∂(UnforcedLeray.Cyl.cellμ c) := by
  have hS0 : UnforcedLeray.Sob.IsCylTest c ψ := (UnforcedLeray.Short.IIIa.testBridge c ψ).1.mp hψ
  have hpd := (UnforcedLeray.Short.IIIa.testBridge c ψ).2 hψ
  have hae : (fun x => ⟪UnforcedLeray.Cyl.gradL hS0 x, g x⟫_ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      fun x => (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 * UnforcedLeray.B0579.pd 0 ψ x +
        (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 * UnforcedLeray.B0579.pd 1 ψ x := by
    filter_upwards [(UnforcedLeray.Cyl.memLp_gradT hS0).coeFn_toLp] with x hx
    have hx' : UnforcedLeray.Cyl.gradL hS0 x = UnforcedLeray.Cyl.gradT ψ x := hx
    rw [hx', UnforcedLeray.Short.IIIa.inner_gradT_aux_p0div, (hpd x).1, (hpd x).2]
  refine ⟨(L2.integrable_inner (UnforcedLeray.Cyl.gradL hS0) g).congr hae, fun hS => ?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae hae

theorem reim_mem_divFree {c : ℝ} (hc : 0 < c) (w : ℝ × ℝ → Fin 2 → ℂ)
    (hper : ∀ q η, w (q + c, η) = w (q, η))
    (hL : MemLp (fun x => toMC (w x)) 2 (UnforcedLeray.Cyl.cellμ c))
    (hdiv : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in stripSet c, (w x 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
        w x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0) :
    toL2v c (reVec w) ∈ UnforcedLeray.Cyl.divFree c ∧
      toL2v c (imVec w) ∈ UnforcedLeray.Cyl.divFree c := by
  obtain ⟨hre, him⟩ := memLp_reVec_imVec hL
  have key : ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
      (∫ x, ((reVec w x 0) * UnforcedLeray.B0579.pd 0 ψ x +
          (reVec w x 1) * UnforcedLeray.B0579.pd 1 ψ x) ∂(UnforcedLeray.Cyl.cellμ c) = 0) ∧
      (∫ x, ((imVec w x 0) * UnforcedLeray.B0579.pd 0 ψ x +
          (imVec w x 1) * UnforcedLeray.B0579.pd 1 ψ x) ∂(UnforcedLeray.Cyl.cellμ c) = 0) := by
    intro ψ hψ
    obtain ⟨hI1, -⟩ := pair_grad c (toL2v c (reVec w)) ψ hψ
    obtain ⟨hI2, -⟩ := pair_grad c (toL2v c (imVec w)) ψ hψ
    have e1 := toL2v_ae hre
    have e2 := toL2v_ae him
    have hI1' : Integrable (fun x : ℝ × ℝ => (reVec w x 0) * UnforcedLeray.B0579.pd 0 ψ x +
        (reVec w x 1) * UnforcedLeray.B0579.pd 1 ψ x) (UnforcedLeray.Cyl.cellμ c) :=
      hI1.congr (by filter_upwards [e1] with x hx; simp only [hx])
    have hI2' : Integrable (fun x : ℝ × ℝ => (imVec w x 0) * UnforcedLeray.B0579.pd 0 ψ x +
        (imVec w x 1) * UnforcedLeray.B0579.pd 1 ψ x) (UnforcedLeray.Cyl.cellμ c) :=
      hI2.congr (by filter_upwards [e2] with x hx; simp only [hx])
    have hperC : UnforcedLeray.Cyl.IsPeriodic c (fun x : ℝ × ℝ => (w x 0 *
        (UnforcedLeray.B0579.pd 0 ψ x : ℂ) + w x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ))) := by
      intro z
      show w (z.1 + c, z.2) 0 * (UnforcedLeray.B0579.pd 0 ψ (z.1 + c, z.2) : ℂ) +
        w (z.1 + c, z.2) 1 * (UnforcedLeray.B0579.pd 1 ψ (z.1 + c, z.2) : ℂ) = _
      rw [hper z.1 z.2, (hψ.pd 0).periodic z, (hψ.pd 1).periodic z]
    have h0 := hdiv ψ hψ
    have hcell : ∫ x in stripSet c, (w x 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
        w x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) =
        ∫ x, (w x 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
        w x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) ∂(UnforcedLeray.Cyl.cellμ c) :=
      UnforcedLeray.B0224.integral_strip_eq_cell hc hperC
    have hpt : ∀ x : ℝ × ℝ, (w x 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
        w x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) =
        ((((reVec w x 0) * UnforcedLeray.B0579.pd 0 ψ x +
          (reVec w x 1) * UnforcedLeray.B0579.pd 1 ψ x : ℝ)) : ℂ) +
        Complex.I * ((((imVec w x 0) * UnforcedLeray.B0579.pd 0 ψ x +
          (imVec w x 1) * UnforcedLeray.B0579.pd 1 ψ x : ℝ)) : ℂ) := by
      intro x
      have e0 : w x 0 = ((w x 0).re : ℂ) + Complex.I * ((w x 0).im : ℂ) := by
        apply Complex.ext <;> simp
      have e1' : w x 1 = ((w x 1).re : ℂ) + Complex.I * ((w x 1).im : ℂ) := by
        apply Complex.ext <;> simp
      have r0 : reVec w x 0 = (w x 0).re := UnforcedLeray.Short.IIIa.reVec_apply_p0orth w x 0
      have r1 : reVec w x 1 = (w x 1).re := UnforcedLeray.Short.IIIa.reVec_apply_p0orth w x 1
      have i0 : imVec w x 0 = (w x 0).im := UnforcedLeray.Short.IIIa.imVec_apply_p0orth w x 0
      have i1 : imVec w x 1 = (w x 1).im := UnforcedLeray.Short.IIIa.imVec_apply_p0orth w x 1
      rw [r0, r1, i0, i1]
      push_cast
      linear_combination ((UnforcedLeray.B0579.pd 0 ψ x : ℂ)) * e0 +
        ((UnforcedLeray.B0579.pd 1 ψ x : ℂ)) * e1'
    rw [hcell, integral_congr_ae (Eventually.of_forall hpt), integral_add,
      integral_const_mul] at h0
    · simp only [integral_complex_ofReal] at h0
      have hre0 := congrArg Complex.re h0
      have him0 := congrArg Complex.im h0
      simp at hre0 him0
      exact ⟨hre0, him0⟩
    · exact Integrable.ofReal hI1'
    · exact (Integrable.ofReal hI2').const_mul _
  constructor
  · rw [UnforcedLeray.Cyl.mem_divFree]
    intro φ hφ
    have hB : UnforcedLeray.B0579.IsCylTest c φ := (UnforcedLeray.Short.IIIa.testBridge c φ).1.mpr hφ
    obtain ⟨-, hin⟩ := pair_grad c (toL2v c (reVec w)) φ hB
    rw [hin hφ]
    have e1 := toL2v_ae hre
    rw [← (key φ hB).1]
    exact integral_congr_ae (by filter_upwards [e1] with x hx; simp only [hx])
  · rw [UnforcedLeray.Cyl.mem_divFree]
    intro φ hφ
    have hB : UnforcedLeray.B0579.IsCylTest c φ := (UnforcedLeray.Short.IIIa.testBridge c φ).1.mpr hφ
    obtain ⟨-, hin⟩ := pair_grad c (toL2v c (imVec w)) φ hB
    rw [hin hφ]
    have e2 := toL2v_ae him
    rw [← (key φ hB).2]
    exact integral_congr_ae (by filter_upwards [e2] with x hx; simp only [hx])

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
