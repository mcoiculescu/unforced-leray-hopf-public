import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic

/-!
# `PartIII-b:C/near/pins/5`: `StressMapWeakSol` from four leaves

Source `the November 2 reference manuscript`
3888-3890 (the finite-curvature free inverse is the conjugate of the Cartesian weak-stress
inverse), 1675-1679 (`S_ε = T_ε s div_ε`, "completion from smooth tensors"), 1556-1572
(`free:weak-stress`).

Plan: for a real smooth band tensor test `M` and `F ∈ Z` with `tv4 (zsum F) = tv4 M` a.e.,
`TepsWeakSol` + `ChartDivPair` + `IsStressMap` + `IsStressTransport` give the weak equation with
right side `-⟨𝒩_T M, ∇Φ⟩` (`SWSmooth`); the stress pairing sees only `tv4` (`SWStrTv4`); such `F`
are dense in `Z` (`SWDensity`); and the weak equation passes to `Z`-limits since `Seps` is
continuous and both pairings are continuous in the `H`, `H_T` norms (`SWClosed`).
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

/-- The standing hypotheses of `stressMapWeakSol_of`. -/
def SWHyp : Prop :=
  TepsWeakSol ∧ ChartDivPair ∧ Masked.TensorTestDense ∧ Masked.TensorTestDivMem ∧
    (∀ c : ℝ, 0 < c → Masked.CellPtHT c) ∧ (∀ c : ℝ, 0 < c → Masked.CellPtH c) ∧
    (∀ c : ℝ, 0 < c → Masked.CellPtInvH c)

/-- **Leaf 1** (source 1645-1646, 2675, 2683): the stress pairing sees only the components
`tv4 = (T_rr, sym T_rz, T_zz, T_φφ)` of `nsSym`, a.e. for `ageμ c (-1/2)`; `cartLift` reads only
`nsSym (T (chartOf ..))`, and `StressPairAE` pulls null sets back. -/
def SWStrTv4 : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ (g g' : Chart → Ten3),
    (∀ᵐ x ∂ageμ c (-1 / 2), tv4 (g x) = tv4 (g' x)) →
    ∀ Φ : ℝ × Space → CVec3,
      stressPair (2 * ε * c) (strPhys ε⁻¹ c g) Φ = stressPair (2 * ε * c) (strPhys ε⁻¹ c g') Φ

/-- **Leaf 2, smooth case** (source 1660-1679, 3888-3897): for a smooth band tensor test `M`
(`tv4 ∘ M` an `IsTensorTest`) and `F ∈ Z` with `tv4 (zsum F) = tv4 M` a.e., and a chart field `v`
equal a.e. to `Seps F`, the lifted `v` solves `D_μ w = ℙ div 𝒩_T M` weakly.  Proof: `IsStressMap`
with `G = s div_ε M` (real chart form, in `H` by `TensorTestDivMem`) gives `Seps' F' = T_ε G`;
`IsStressTransport` gives its chart form `= Seps F`; `TepsWeakSol` gives the weak equation with
right side `⟨Φ, 𝒩_v(s div_ε M)⟩`; `ChartDivPair` rewrites it as `-⟨𝒩_T M, ∇Φ⟩`. -/
def SWSmooth : Prop :=
  SWHyp →
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ → ∀ (mZ ρb : ℝ), 0 ≤ mZ → 0 < ρb →
    ∀ (Seps : Zsp p.c mZ ρb →L[ℝ] Hsp p.c)
      (Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ] HSpace p.c MeridC),
      UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
          Seps' →
      IsStressTransport Seps Seps' →
      ∀ (M : Chart → Ten3),
        UnforcedLeray.Short.PartIIa.IsTensorTest p.c (fun x => tv4 (M x)) →
        ∀ (F : Zsp p.c mZ ρb) (v : Chart → Merid),
          (∀ᵐ x ∂ageμ p.c (-1 / 2), tv4 (zsum F x) = tv4 (M x)) →
          v =ᵐ[ageμ p.c (-3 / 2)] (Seps F : Chart → Merid) →
          IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c v)
            (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c M) Φ)

/-- **Leaf 3, density** (source 1678, "completion from smooth tensors"): every `F ∈ Z` is a
`Z`-limit of `F'` whose `tv4 (zsum F')` is a.e. a smooth band tensor test (approximate the `tv4`
parts of `F₁` in `Z₁` and of `F₂` in `ρ_b^{-1/2}H_T` by smooth tests, `Masked.TensorTestDense`,
keeping the other components). -/
def SWDensity : Prop :=
  SWHyp →
  ∀ (p : Params) (mZ ρb : ℝ), 0 ≤ mZ → 0 < ρb → ∀ (F : Zsp p.c mZ ρb) (η : ℝ), 0 < η →
    ∃ (M : Chart → Ten3) (F' : Zsp p.c mZ ρb),
      UnforcedLeray.Short.PartIIa.IsTensorTest p.c (fun x => tv4 (M x)) ∧
        (∀ᵐ x ∂ageμ p.c (-1 / 2), tv4 (zsum F' x) = tv4 (M x)) ∧ ‖F' - F‖ < η

/-- **Leaf 4, closure** (source 3888-3890): the weak equation passes to `Z`-limits: `Seps` is a
continuous linear map into `H`, `Φ ↦ ⟨Φ, 𝒩_v b⟩` is continuous in `‖b‖_H` for a phase test (the
`eLpNorm_liftFun` estimate, Cauchy-Schwarz on `L²(phaseμ)`), `F ↦ ⟨𝒩_T zsum F, ∇Φ⟩` is continuous
since `zsum : Z → H_T` is, and the solenoidal clause is a fixed weak condition on `b`. -/
def SWClosed : Prop :=
  SWHyp →
  ∀ (p : Params) (μ : ℝ) (mZ ρb : ℝ), 0 ≤ mZ → 0 < ρb →
    ∀ (Seps : Zsp p.c mZ ρb →L[ℝ] Hsp p.c) (Fs : ℕ → Zsp p.c mZ ρb) (F : Zsp p.c mZ ρb)
      (vs : ℕ → Chart → Merid) (v : Chart → Merid),
      Filter.Tendsto Fs Filter.atTop (nhds F) →
      (∀ n, vs n =ᵐ[ageμ p.c (-3 / 2)] (Seps (Fs n) : Chart → Merid)) →
      v =ᵐ[ageμ p.c (-3 / 2)] (Seps F : Chart → Merid) →
      (∀ n, IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c (vs n))
        (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum (Fs n))) Φ)) →
      IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c v)
        (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum F)) Φ)

theorem stressMapWeakSol_assemble (h1 : SWStrTv4) (h2 : SWSmooth) (h3 : SWDensity) (h4 : SWClosed)
    (hT : TepsWeakSol) (hC : ChartDivPair) (hD : Masked.TensorTestDense)
    (hM : Masked.TensorTestDivMem) (hHT : ∀ c : ℝ, 0 < c → Masked.CellPtHT c)
    (hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c) (hHi : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c) :
    StressMapWeakSol := by
  have hyp : SWHyp := ⟨hT, hC, hD, hM, hHT, hH, hHi⟩
  intro p μ hP hμ mZ ρb γ hmZ hρ Seps Seps' hS hSt F w hw
  have hex := fun n : ℕ => h3 hyp p mZ ρb hmZ hρ F (1 / ((n : ℝ) + 1)) (by positivity)
  choose M Fs hMt hMae hFs using hex
  have hlim : Filter.Tendsto Fs Filter.atTop (nhds F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hFs n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine h4 hyp p μ mZ ρb hmZ hρ Seps Fs F (fun n => (Seps (Fs n) : Chart → Merid)) w hlim
    (fun n => Filter.EventuallyEq.rfl) hw (fun n => ?_)
  have hsm := h2 hyp p μ hP hμ mZ ρb hmZ hρ Seps Seps' hS hSt (M n) (hMt n) (Fs n)
    (Seps (Fs n) : Chart → Merid) (hMae n) Filter.EventuallyEq.rfl
  have hst : (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (M n)) Φ) =
      (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum (Fs n))) Φ) := by
    funext Φ
    rw [h1 p.c p.ε p.c_pos p.ε_pos (M n) (zsum (Fs n))
      ((hMae n).mono fun x hx => hx.symm) Φ]
  rw [hst] at hsm
  exact hsm

end UnforcedLeray.Short.PartIIIb.NearInst
