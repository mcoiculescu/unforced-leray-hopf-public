import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5

/-!
# `PartIII-b:C/near/pins/5/3`: `SWDensity` from the real density of smooth tensor tests in `H_T`

Source `the November 2 reference manuscript`
1678 ("the tensor map means completion from smooth tensors"), 2698-2700, 2700 and 3874 (the
stress inverse acts on the sum `F₁ + F₂` of the components).

Reduction.  `F = (F₁, F₂) ∈ Z`.  Leave `F₁` unchanged and move only `F₂` by `D ∈ ρ_b^{-1/2}H_T`
with `F₁ + F₂ + D = M` a.e.  Then `‖F' - F‖_Z = ‖D‖_{ρ_b^{-1/2}H_T} ≤ ρ_b^{-1/2}‖M - (F₁+F₂)‖_{H_T}`,
so it suffices that smooth band tests `M` are dense in `H_T` (`SWRealDense`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (zsumL zsumL_ae ageμ_le_z1Measure ageμ_le_htRho)

/-- The pointwise lift of a `tv4`-quadruple `(T_rr, T_rz, T_zz, T_φφ)` (real parts) to the symmetric
tensor with those components in the order `(r, φ, z)`. -/
def tvLift (a : UnforcedLeray.Short.PartIIa.TensorVal) : Ten3 :=
  ten3Of !![(a 0).re, 0, (a 1).re; 0, (a 3).re, 0; (a 1).re, 0, (a 2).re]

theorem tv4_tvLift (a : UnforcedLeray.Short.PartIIa.TensorVal) (i : Fin 4) :
    tv4 (tvLift a) i = ((a i).re : ℂ) := by
  fin_cases i <;> simp [tv4, tvLift, ten3Of, symRZ] <;> ring

/-- **Leaf A** (the real part of a complex test is a test, source 1660-1665, 1678): if `M₀` is a
smooth, `c`-periodic, band-supported `TensorVal`-valued function then so is
`x ↦ tv4 (tvLift (M₀ x))`, the componentwise real part of `M₀` (`Complex.re` is a continuous
real-linear map, so smoothness, periodicity and the support condition pass to it). -/
def SWTestLift : Prop :=
  ∀ (c : ℝ) (M0 : Profile → UnforcedLeray.Short.PartIIa.TensorVal),
    UnforcedLeray.Short.PartIIa.IsTensorTest c M0 →
      UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (tvLift (M0 x)))

/-- **Leaf B (real density of smooth tensor tests in `H_T`)** (source 1678: completion from smooth
tensors).  Every `T ∈ H_T = L²(s^{-1/2} dς; Ten3)` is an `H_T`-limit of chart fields `M` whose
`tv4`-components `(M_rr, sym M_rz, M_zz, M_φφ)` form a smooth, `c`-periodic, band-supported tensor
test (the remaining components of `M` are arbitrary: e.g. `M = T - tvLift(tv4 T) + tvLift(M₀)`, with `tvLift` as above, and `M₀` the complex test supplied by
`Masked.TensorTestDense`, transferred by `cplxT`/`cellPt` (`Masked.CellPtHT`) and periodicity). -/
def SWRealDense : Prop :=
  SWHyp →
  ∀ c : ℝ, 0 < c → ∀ (T : HTsp c) (η : ℝ), 0 < η →
    ∃ (M : Chart → Ten3) (hM : MemLp M 2 (ageμ c (-1 / 2))),
      UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) ∧ ‖T - hM.toLp M‖ < η

theorem swDensity_of (h : SWRealDense) : SWDensity := by
  intro hyp p mZ ρb hmZ hρ F η hη
  have hc := p.c_pos
  let L : HTsp p.c →L[ℝ] HTrho p.c ρb :=
    Lp.LpToLpOfMeasureLeSMul (E := Ten3) (p := 2) ENNReal.ofReal_ne_top
      (show htRhoMeasure p.c ρb ≤ ENNReal.ofReal ρb⁻¹ • ageμ p.c (-1 / 2) from le_rfl)
  have hL : ∀ u : HTsp p.c, L u =ᵐ[ageμ p.c (-1 / 2)] (u : Chart → Ten3) := by
    intro u
    have h1 := Lp.coeFn_LpToLpOfMeasureLeSMul (E := Ten3) (p := 2) ENNReal.ofReal_ne_top
      (show htRhoMeasure p.c ρb ≤ ENNReal.ofReal ρb⁻¹ • ageμ p.c (-1 / 2) from le_rfl) u
    exact (Measure.absolutelyContinuous_of_le_smul (ageμ_le_htRho hρ)).ae_le h1
  have hLpos : 0 < ‖L‖ + 1 := by positivity
  obtain ⟨M, hM, hMt, hnorm⟩ := h hyp p.c hc (zsumL p.c mZ ρb hmZ hρ F) (η / (‖L‖ + 1))
    (by positivity)
  set D : HTrho p.c ρb := L (hM.toLp M - zsumL p.c mZ ρb hmZ hρ F) with hD
  have hDn : ‖D‖ < η := by
    have h1 : ‖D‖ ≤ ‖L‖ * ‖hM.toLp M - zsumL p.c mZ ρb hmZ hρ F‖ := L.le_opNorm _
    have h2 : ‖hM.toLp M - zsumL p.c mZ ρb hmZ hρ F‖ < η / (‖L‖ + 1) := by
      rw [← norm_neg, neg_sub]; exact hnorm
    have h3 : ‖L‖ * ‖hM.toLp M - zsumL p.c mZ ρb hmZ hρ F‖ ≤ (‖L‖ + 1) * ‖hM.toLp M - zsumL p.c mZ ρb hmZ hρ F‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h4 : (‖L‖ + 1) * ‖hM.toLp M - zsumL p.c mZ ρb hmZ hρ F‖ < η := by
      have := (lt_div_iff₀ hLpos).1 (show ‖hM.toLp M - zsumL p.c mZ ρb hmZ hρ F‖ < η / (‖L‖ + 1) from h2)
      linarith
    linarith
  refine ⟨M, F + (WithLp.toLp 1 ((0 : Z1sp p.c mZ), D) : Zsp p.c mZ ρb), hMt, ?_, ?_⟩
  · have ac1 : ageμ p.c (-1 / 2) ≪ z1Measure p.c mZ :=
      Measure.absolutelyContinuous_of_le_smul (ageμ_le_z1Measure (c := p.c) hmZ)
    have hA1 := ac1.ae_le (Lp.coeFn_add F.fst (0 : Z1sp p.c mZ))
    have hA2 : ∀ᵐ x ∂ageμ p.c (-1 / 2),
        (F.snd + D : HTrho p.c ρb) x = (F.snd : Chart → Ten3) x + (D : Chart → Ten3) x := by
      have := Lp.coeFn_add F.snd D
      have this' := (Measure.absolutelyContinuous_of_le_smul (ageμ_le_htRho hρ)).ae_le this
      filter_upwards [this'] with x hx
      exact hx
    have hA3 := Lp.coeFn_zero (E := Ten3) (p := 2) (μ := z1Measure p.c mZ)
    have hA3' := ac1.ae_le hA3
    have hz := zsumL_ae p.c mZ ρb hmZ hρ F
    have hc1 := hM.coeFn_toLp
    have hs := Lp.coeFn_sub (hM.toLp M) (zsumL p.c mZ ρb hmZ hρ F)
    have hd := hL (hM.toLp M - zsumL p.c mZ ρb hmZ hρ F)
    filter_upwards [hA1, hA2, hA3', hz, hc1, hs, hd] with x h1 h2 h3 h4 h5 h6 h7
    have key : zsum (F + WithLp.toLp 1 ((0 : Z1sp p.c mZ), D) : Zsp p.c mZ ρb) x = M x := by
      unfold zsum at h4 ⊢
      change (F.fst + (0 : Z1sp p.c mZ) : Z1sp p.c mZ) x + (F.snd + D : HTrho p.c ρb) x = M x
      rw [h1, h2, Pi.add_apply, h3]
      rw [hD, h7, h6, Pi.sub_apply, h5, h4]
      simp only [Pi.zero_apply]
      abel
    rw [key]
  · rw [add_sub_cancel_left, WithLp.prod_norm_eq_of_L1]
    simpa using hDn

end UnforcedLeray.Short.PartIIIb.NearInst
