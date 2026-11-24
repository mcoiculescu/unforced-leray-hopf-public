import UnforcedLeray.Units.B0222.Generator

/-!


Source of record: `the November 2 reference manuscript`, lines 1824-1844.
The operator `Λ = K + 1` is defined at line 1824, the identity
`Λ² = 4S² + 4Sη∂_η + 4S + η²∂_η² + 3η∂_η + 1` at line 1831, and the exact generator
difference `A_ε - A_0 = νs[-2εΛ∂_q + ε²Λ² - ε²E]` at lines 1838-1840.

Objects (`Units/B0221/Generators.lean`, `Units/B0222/Generator.lean`): `dS, dQ, dEta` are the
partial derivatives along `eS, eQ, eEta`, `opS = s∂_s`, `opK = 2S + η∂_η`, `opQ ε = ∂_q - ε(K+1)`,
the scalar generators `Aeps` and `A0`, and the meridional vector generator `AepsVec`.
The `pdS, pdQ, pdEta` of `StatementsNear.lean` are the same derivatives
(`pdS f p = fderiv f p (1,0,0)`, and `eS = (1,0,0)`).

Results, for profiles of class `C²` at the point `p` (the source's "smooth" profiles):

* `generatorDifference` (scalar): `A_ε b - A_0 b = νs(-2ε Λ(∂_q b) + ε² Λ² b)`.
* `generatorDifference_vec` (componentwise `(b_r, b_z)` form): the same identity for
  `AepsVec`, with the additional term `-ε² E b`, where `E = radialSel = diag(1,0)`.
  The source writes `E = diag(1,1,0)`; on the two meridional components of this file the
  radial selector is `diag(1,0)`, which is the one `AepsVec` (B0222) uses.
* `lambda_sq_expansion`: `Λ² b = 4S²b + 4S(η∂_η b) + 4Sb + η²∂_η²b + 3η∂_η b + b`.

The adjoint form of the difference (source line 1840, "also for adjoints") is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open UnforcedLeray.B0220 UnforcedLeray.B0221 UnforcedLeray.B0222

namespace UnforcedLeray.Short.PartIIa

/-! ### Symmetry of second derivatives and derivatives of `Λb` -/

/-- Symmetry of the second derivative of a `C²` profile at `p`. -/
theorem gen_symm {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) (v w : Profile) :
    fderiv ℝ (fderiv ℝ b) p v w = fderiv ℝ (fderiv ℝ b) p w v :=
  (hb.isSymmSndFDerivAt (by simp)).eq v w

/-- The derivative of `Λb = K b + b` in a direction `w`. -/
theorem gen_fderiv_Lam {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) (w : Profile) :
    fderiv ℝ (fun q => opK b q + b q) p w =
      2 * w.1 * fderiv ℝ b p eS + 2 * p.1 * fderiv ℝ (fderiv ℝ b) p w eS +
        (w.2.2 * fderiv ℝ b p eEta + p.2.2 * fderiv ℝ (fderiv ℝ b) p w eEta) +
        fderiv ℝ b p w := by
  have hD := differentiableAt_fderiv_of_contDiffAt hb
  have hb1 : HasFDerivAt b (fderiv ℝ b p) p := (hb.differentiableAt (by norm_num)).hasFDerivAt
  have hfst : HasFDerivAt (fun p' : Profile => 2 * p'.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hasFDerivAt_fst).const_mul 2
  have hsnd : HasFDerivAt (fun p' : Profile => p'.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_snd).snd
  have h := ((hfst.mul (hasFDerivAt_fderiv_apply hD eS)).add
    (hsnd.mul (hasFDerivAt_fderiv_apply hD eEta))).add hb1
  have hL : HasFDerivAt (fun q => opK b q + b q) _ p := h
  rw [hL.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

theorem gen_dS_Lam {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dS (fun q => opK b q + b q) p = 3 * dS b p + 2 * p.1 * fderiv ℝ (fderiv ℝ b) p eS eS +
      p.2.2 * fderiv ℝ (fderiv ℝ b) p eS eEta := by
  unfold dS
  rw [gen_fderiv_Lam hb eS]
  simp only [eS_fst, eS_snd_snd]
  ring

theorem gen_dEta_Lam {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dEta (fun q => opK b q + b q) p = 2 * dEta b p + 2 * p.1 * fderiv ℝ (fderiv ℝ b) p eS eEta +
      p.2.2 * fderiv ℝ (fderiv ℝ b) p eEta eEta := by
  unfold dEta
  rw [gen_fderiv_Lam hb eEta, gen_symm hb eEta eS]
  simp only [eEta_fst, eEta_snd_snd]
  ring

/-! ### Derivatives of `∂_q b` and of `opS b` -/

theorem gen_dS_dQ {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dS (dQ b) p = fderiv ℝ (fderiv ℝ b) p eS eQ :=
  UnforcedLeray.B0221.fderiv_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hb) eQ eS

theorem gen_dEta_dQ {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dEta (dQ b) p = fderiv ℝ (fderiv ℝ b) p eEta eQ :=
  UnforcedLeray.B0221.fderiv_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hb) eQ eEta

theorem gen_dQ_dQ {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dQ (dQ b) p = fderiv ℝ (fderiv ℝ b) p eQ eQ :=
  UnforcedLeray.B0221.fderiv_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hb) eQ eQ

theorem gen_dEta_dEta {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dEta (dEta b) p = fderiv ℝ (fderiv ℝ b) p eEta eEta :=
  UnforcedLeray.B0221.fderiv_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hb) eEta eEta

/-- `Λ(∂_q b) = (K + 1)∂_q b` written through the second derivatives of `b`. -/
theorem gen_Lam_dQ {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    opK (dQ b) p + dQ b p = 2 * p.1 * fderiv ℝ (fderiv ℝ b) p eS eQ +
      p.2.2 * fderiv ℝ (fderiv ℝ b) p eEta eQ + fderiv ℝ b p eQ := by
  simp only [opK]
  rw [gen_dS_dQ hb, gen_dEta_dQ hb]
  rfl

theorem gen_dS_opS {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    dS (opS b) p = dS b p + p.1 * fderiv ℝ (fderiv ℝ b) p eS eS := by
  have hD := differentiableAt_fderiv_of_contDiffAt hb
  have h : HasFDerivAt (opS b) _ p := (hasFDerivAt_fst).mul (hasFDerivAt_fderiv_apply hD eS)
  rw [show dS (opS b) p = fderiv ℝ (opS b) p eS from rfl, h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
    smul_eq_mul, eS_fst]
  unfold dS
  ring

theorem gen_opS_eta {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    opS (fun q => q.2.2 * dEta b q) p = p.1 * (p.2.2 * fderiv ℝ (fderiv ℝ b) p eS eEta) := by
  have hD := differentiableAt_fderiv_of_contDiffAt hb
  have hsnd : HasFDerivAt (fun q : Profile => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_snd).snd
  have h : HasFDerivAt (fun q : Profile => q.2.2 * dEta b q) _ p :=
    hsnd.mul (hasFDerivAt_fderiv_apply hD eEta)
  rw [show opS (fun q => q.2.2 * dEta b q) p =
      p.1 * fderiv ℝ (fun q => q.2.2 * dEta b q) p eS from rfl, h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, eS_snd_snd]
  ring

/-! ### Λ² expansion (source line 1831) -/

theorem gen_Lam2 {b : Profile → ℝ} {p : Profile} (hb : ContDiffAt ℝ 2 b p) :
    opK (fun q => opK b q + b q) p + (opK b p + b p) =
      2 * p.1 * (3 * dS b p + 2 * p.1 * fderiv ℝ (fderiv ℝ b) p eS eS +
        p.2.2 * fderiv ℝ (fderiv ℝ b) p eS eEta) +
      p.2.2 * (2 * dEta b p + 2 * p.1 * fderiv ℝ (fderiv ℝ b) p eS eEta +
        p.2.2 * fderiv ℝ (fderiv ℝ b) p eEta eEta) +
      (2 * p.1 * dS b p + p.2.2 * dEta b p + b p) := by
  rw [show opK (fun q => opK b q + b q) p =
      2 * p.1 * dS (fun q => opK b q + b q) p + p.2.2 * dEta (fun q => opK b q + b q) p from rfl,
    gen_dS_Lam hb, gen_dEta_Lam hb]
  simp only [opK]

/-- **Λ² expansion** (source line 1831): `Λ² b = 4S²b + 4S(η∂_η b) + 4Sb + η²∂_η²b + 3η∂_η b + b`,
with `Λ = K + 1`, `S = s∂_s`, `K = 2S + η∂_η`, for a profile `b` of class `C²` at `p`. -/
theorem lambda_sq_expansion (b : Profile → ℝ) (p : Profile) (hb : ContDiffAt ℝ 2 b p) :
    opK (fun q => opK b q + b q) p + (opK b p + b p) =
      4 * opS (opS b) p + 4 * opS (fun q => q.2.2 * dEta b q) p + 4 * opS b p +
        p.2.2 ^ 2 * dEta (dEta b) p + 3 * (p.2.2 * dEta b p) + b p := by
  rw [gen_Lam2 hb]
  rw [show opS (opS b) p = p.1 * dS (opS b) p from rfl, gen_dS_opS hb, gen_opS_eta hb,
    show opS b p = p.1 * dS b p from rfl, gen_dEta_dEta hb]
  ring

/-! ### The exact generator difference (source lines 1838-1840) -/

/-- **Exact generator difference, scalar form** (source lines 1838-1840):
`A_ε b - A_0 b = νs(-2ε Λ(∂_q b) + ε² Λ² b)` at `p`, for `b` of class `C²` at `p`. -/
theorem generatorDifference (nu eps : ℝ) (b : Profile → ℝ) (p : Profile)
    (hb : ContDiffAt ℝ 2 b p) :
    Aeps nu eps b p - A0 nu b p =
      nu * p.1 * (-2 * eps * (opK (dQ b) p + dQ b p) +
        eps ^ 2 * (opK (fun q => opK b q + b q) p + (opK b p + b p))) := by
  have hA0 : A0 nu b p = -(p.1 * fderiv ℝ b p eS) +
      nu * p.1 * (fderiv ℝ (fderiv ℝ b) p eQ eQ + fderiv ℝ (fderiv ℝ b) p eEta eEta) := by
    unfold A0 opS
    rw [gen_dQ_dQ hb, gen_dEta_dEta hb]
    unfold dS
    rfl
  rw [Aeps_expand nu eps hb, hA0, gen_Lam_dQ hb, gen_Lam2 hb]
  simp only [dS, dEta]
  simp only [gen_symm hb eS eQ, gen_symm hb eEta eQ, gen_symm hb eEta eS]
  ring

/-! ### The vector generator `AepsVec` (componentwise, tex lines 1838-1840 with `E`) -/

/-- Componentwise form of `AepsVec`: the `i`-th component is the scalar `A_ε` of the `i`-th
component minus the radial frame term. -/
theorem AepsVec_component (nu eps : ℝ) (b : Profile → Merid) (p : Profile) (i : Fin 2) :
    AepsVec nu eps b p i =
      Aeps nu eps (fun q => b q i) p - nu * p.1 * (radialSel i * eps ^ 2 * b p i) := by
  simp only [AepsVec, Aeps, PiLp.toLp_apply]
  ring

/-- **Exact generator difference, meridional vector form** (source lines 1838-1840):
`A_ε^vec b - A_0^vec b = νs(-2ε Λ∂_q b + ε² Λ² b - ε² E b)` componentwise in `(b_r, b_z)`,
with `E = radialSel = diag(1,0)`. -/
theorem generatorDifference_vec (nu eps : ℝ) (b : Profile → Merid) (p : Profile)
    (hb : ∀ i : Fin 2, ContDiffAt ℝ 2 (fun q => b q i) p) (i : Fin 2) :
    AepsVec nu eps b p i - AepsVec nu 0 b p i =
      nu * p.1 * (-2 * eps * (opK (dQ (fun q => b q i)) p + dQ (fun q => b q i) p) +
        eps ^ 2 * (opK (fun q => opK (fun q => b q i) q + b q i) p +
          (opK (fun q => b q i) p + b p i)) -
        radialSel i * eps ^ 2 * b p i) := by
  rw [AepsVec_component nu eps b p i, AepsVec_component nu 0 b p i, Aeps_zero]
  have h := generatorDifference nu eps (fun q => b q i) p (hb i)
  linear_combination h

end UnforcedLeray.Short.PartIIa
