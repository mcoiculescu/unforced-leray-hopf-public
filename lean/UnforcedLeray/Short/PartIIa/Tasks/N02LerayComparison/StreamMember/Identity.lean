import UnforcedLeray.Short.PartIIa.Sub.N02
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.


profile functions (`fderiv_mul_apply'`, `contDiff_fderiv_apply`, `pdQ_pdEta_comm`,
`pdS_pdEta_comm`, `opK_eq`, `differentiable_opK`, `pdEta_opK`, `fderiv_ofReal_fst_apply`,
`fderiv_ofReal_snd_snd_apply`) and the pointwise splitting of the integrand of
`⟪cgrad ε Φ, streamC ε ψ⟫` into divergence terms (`integrand_identity`).  The integrals of the
divergence terms and the `L²` membership are the leaves of `Sub/N02_2.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace NearStreamMemberAux

/-! ### Calculus on `ℂ`-valued profile functions -/

/-- Product rule for a directional derivative of a product of `ℂ`-valued functions. -/
theorem fderiv_mul_apply' (f g : Profile → ℂ) (v p : Profile)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    fderiv ℝ (fun x => f x * g x) p v = f p * fderiv ℝ g p v + g p * fderiv ℝ f p v := by
  have h : HasFDerivAt (fun x => f x * g x) (f p • fderiv ℝ g p + g p • fderiv ℝ f p) p :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem contDiff_fderiv_apply {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (v : Profile) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem differentiable_fderiv_apply {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (v : Profile) :
    Differentiable ℝ (fun x => fderiv ℝ f x v) :=
  (contDiff_fderiv_apply hf v).differentiable (by simp)

/-- The second directional derivative of `f`, with the outer direction `w` differentiated. -/
theorem fderiv_fderiv_apply {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (v w p : Profile) :
    fderiv ℝ (fun x => fderiv ℝ f x w) p v = fderiv ℝ (fderiv ℝ f) p v w := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) p
  have h := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ => w) hc (differentiableAt_const w)
  rw [h]
  simp

/-- Symmetry of mixed second derivatives of a `C^2` profile function. -/
theorem fderiv_comm_apply {f : Profile → ℂ} (hf : ContDiff ℝ ∞ f) (v w p : Profile) :
    fderiv ℝ (fun x => fderiv ℝ f x w) p v = fderiv ℝ (fun x => fderiv ℝ f x v) p w := by
  rw [fderiv_fderiv_apply hf, fderiv_fderiv_apply hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) v w

/-- `∂_q ∂_η = ∂_η ∂_q`. -/
theorem pdQ_pdEta_comm {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    pdQ (pdEta Φ) p = pdEta (pdQ Φ) p :=
  fderiv_comm_apply hΦ (0, 1, 0) (0, 0, 1) p

/-- `∂_s ∂_η = ∂_η ∂_s`. -/
theorem pdS_pdEta_comm {ψ : Profile → ℂ} (hψ : ContDiff ℝ ∞ ψ) (p : Profile) :
    pdS (pdEta ψ) p = pdEta (pdS ψ) p :=
  fderiv_comm_apply hψ (1, 0, 0) (0, 0, 1) p

theorem hasFDerivAt_ofReal_fst (p : Profile) :
    HasFDerivAt (fun x : Profile => (x.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) p :=
  Complex.ofRealCLM.hasFDerivAt.comp p hasFDerivAt_fst

theorem fderiv_ofReal_fst_apply (p v : Profile) :
    fderiv ℝ (fun x : Profile => (x.1 : ℂ)) p v = (v.1 : ℂ) := by
  rw [(hasFDerivAt_ofReal_fst p).fderiv]
  simp

theorem hasFDerivAt_ofReal_snd_snd (p : Profile) :
    HasFDerivAt (fun x : Profile => (x.2.2 : ℂ))
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) p := by
  have hin : HasFDerivAt (fun x : Profile => x.2) (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_snd
  have hout : HasFDerivAt (fun y : ℝ × ℝ => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (p.2) :=
    hasFDerivAt_snd
  have hcomp : HasFDerivAt (fun x : Profile => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hout.comp p hin
  exact Complex.ofRealCLM.hasFDerivAt.comp p hcomp

theorem fderiv_ofReal_snd_snd_apply (p v : Profile) :
    fderiv ℝ (fun x : Profile => (x.2.2 : ℂ)) p v = (v.2.2 : ℂ) := by
  rw [(hasFDerivAt_ofReal_snd_snd p).fderiv]
  simp

/-- Derivative of a coefficient `η`-free `s` multiple: `∂_v (s · g) = s ∂_v g + v_s g`. -/
theorem fderiv_fst_mul {g : Profile → ℂ} (hg : Differentiable ℝ g) (p v : Profile) :
    fderiv ℝ (fun x : Profile => (x.1 : ℂ) * g x) p v =
      (p.1 : ℂ) * fderiv ℝ g p v + (v.1 : ℂ) * g p := by
  have h := fderiv_mul_apply' (fun x : Profile => (x.1 : ℂ)) g v p
    (hasFDerivAt_ofReal_fst p).differentiableAt (hg p)
  rw [h, fderiv_ofReal_fst_apply]
  ring

/-- Derivative of a coefficient `η`-multiple: `∂_v (η · g) = η ∂_v g + v_η g`. -/
theorem fderiv_snd_snd_mul {g : Profile → ℂ} (hg : Differentiable ℝ g) (p v : Profile) :
    fderiv ℝ (fun x : Profile => (x.2.2 : ℂ) * g x) p v =
      (p.2.2 : ℂ) * fderiv ℝ g p v + (v.2.2 : ℂ) * g p := by
  have h := fderiv_mul_apply' (fun x : Profile => (x.2.2 : ℂ)) g v p
    (hasFDerivAt_ofReal_snd_snd p).differentiableAt (hg p)
  rw [h, fderiv_ofReal_snd_snd_apply]
  ring

/-! ### The operator `K = 2 s ∂_s + η ∂_η` on `ℂ`-valued profile functions -/

theorem opK_eq (f : Profile → ℂ) (p : Profile) :
    opK f p = (p.1 : ℂ) * (2 * pdS f p) + (p.2.2 : ℂ) * pdEta f p := by
  simp only [opK, opS, Complex.real_smul, Complex.ofReal_ofNat]
  ring

theorem differentiable_opK {ψ : Profile → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    Differentiable ℝ (opK ψ) := by
  have hfun : opK ψ = fun x => (x.1 : ℂ) * (2 * pdS ψ x) + (x.2.2 : ℂ) * pdEta ψ x :=
    funext fun x => opK_eq ψ x
  have h2 : Differentiable ℝ (fun x => (2 : ℂ) * pdS ψ x) :=
    (differentiable_fderiv_apply hψ (1, 0, 0)).const_mul 2
  have h4 : Differentiable ℝ (pdEta ψ) := differentiable_fderiv_apply hψ (0, 0, 1)
  rw [hfun]
  intro p
  exact ((hasFDerivAt_ofReal_fst p).differentiableAt.mul (h2 p)).add
    ((hasFDerivAt_ofReal_snd_snd p).differentiableAt.mul (h4 p))

/-- `∂_η K ψ = K ∂_η ψ + ∂_η ψ`: the commutator of `∂_η` and `K` (`η` is the only coefficient
that depends on `η`, and `∂_s, ∂_η` commute). -/
theorem pdEta_opK {ψ : Profile → ℂ} (hψ : ContDiff ℝ ∞ ψ) (p : Profile) :
    pdEta (opK ψ) p = opK (pdEta ψ) p + pdEta ψ p := by
  have hfun : opK ψ = fun x => (x.1 : ℂ) * (2 * pdS ψ x) + (x.2.2 : ℂ) * pdEta ψ x :=
    funext fun x => opK_eq ψ x
  have h2 : Differentiable ℝ (fun x => (2 : ℂ) * pdS ψ x) :=
    (differentiable_fderiv_apply hψ (1, 0, 0)).const_mul 2
  have h4 : Differentiable ℝ (pdEta ψ) := differentiable_fderiv_apply hψ (0, 0, 1)
  have h1 : DifferentiableAt ℝ (fun x : Profile => (x.1 : ℂ) * (2 * pdS ψ x)) p :=
    (hasFDerivAt_ofReal_fst p).differentiableAt.mul (h2 p)
  have h3 : DifferentiableAt ℝ (fun x : Profile => (x.2.2 : ℂ) * pdEta ψ x) p :=
    (hasFDerivAt_ofReal_snd_snd p).differentiableAt.mul (h4 p)
  have e1 := fderiv_fst_mul h2 p (0, 0, 1)
  have e3 := fderiv_snd_snd_mul h4 p (0, 0, 1)
  have hd : DifferentiableAt ℝ (pdS ψ) p := differentiable_fderiv_apply hψ (1, 0, 0) p
  have e2 : fderiv ℝ (fun x => (2 : ℂ) * pdS ψ x) p (0, 0, 1) = 2 * pdEta (pdS ψ) p := by
    rw [fderiv_const_mul hd 2]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  have hc : pdS (pdEta ψ) p = pdEta (pdS ψ) p := pdS_pdEta_comm hψ p
  rw [hfun]
  show fderiv ℝ (fun x : Profile => (x.1 : ℂ) * (2 * pdS ψ x) + (x.2.2 : ℂ) * pdEta ψ x) p
      (0, 0, 1) = opK (pdEta ψ) p + pdEta ψ p
  have hA : HasFDerivAt (fun x : Profile => (x.1 : ℂ) * (2 * pdS ψ x) + (x.2.2 : ℂ) * pdEta ψ x)
      (fderiv ℝ (fun x : Profile => (x.1 : ℂ) * (2 * pdS ψ x)) p
        + fderiv ℝ (fun x : Profile => (x.2.2 : ℂ) * pdEta ψ x) p) p :=
    h1.hasFDerivAt.add h3.hasFDerivAt
  rw [hA.fderiv, ContinuousLinearMap.add_apply, e1, e3, e2, opK_eq (pdEta ψ) p, hc]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add, one_mul]
  rw [show pdEta (pdEta ψ) p = (fderiv ℝ (pdEta ψ) p) (0, 0, 1) from rfl]
  ring

/-! ### The pointwise integrand identity -/

/-- **Pointwise splitting of the stream pairing.** For `ℂ`-valued `C^∞` profile functions
`Φ, ψ`,
`(∂_qΦ - εKΦ)(-∂_ηψ) + ∂_ηΦ (∂_qψ - εKψ + εψ)`
`= ∂_q(∂_ηΦ ψ) - ∂_η(∂_qΦ ψ) + ε (K(Φ ∂_ηψ) + ∂_η(Φ(ψ - Kψ)))`.
The two `∂_q, ∂_η` terms are divergences in `q` and `η`, the `ε` part is a `K`-divergence plus
an `η`-divergence; each one integrates to zero against `s^{-3/2} ds dq dη` over the cell. -/
theorem integrand_identity (ε : ℝ) {Φ ψ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hψ : ContDiff ℝ ∞ ψ) (p : Profile) :
    (pdQ Φ p - (ε : ℂ) * opK Φ p) * (-pdEta ψ p)
        + pdEta Φ p * (pdQ ψ p - (ε : ℂ) * opK ψ p + (ε : ℂ) * ψ p)
      = pdQ (fun x => pdEta Φ x * ψ x) p - pdEta (fun x => pdQ Φ x * ψ x) p
        + (ε : ℂ) * (opK (fun x => Φ x * pdEta ψ x) p
            + pdEta (fun x => Φ x * (ψ x - opK ψ x)) p) := by
  have dΦ : DifferentiableAt ℝ Φ p := (hΦ.differentiable (by simp)) p
  have dψ : DifferentiableAt ℝ ψ p := (hψ.differentiable (by simp)) p
  have dΦe : DifferentiableAt ℝ (pdEta Φ) p := differentiable_fderiv_apply hΦ (0, 0, 1) p
  have dΦq : DifferentiableAt ℝ (pdQ Φ) p := differentiable_fderiv_apply hΦ (0, 1, 0) p
  have dψe : DifferentiableAt ℝ (pdEta ψ) p := differentiable_fderiv_apply hψ (0, 0, 1) p
  have dKψ : DifferentiableAt ℝ (opK ψ) p := differentiable_opK hψ p
  have R1 : pdQ (fun x => pdEta Φ x * ψ x) p = pdEta Φ p * pdQ ψ p + ψ p * pdQ (pdEta Φ) p :=
    fderiv_mul_apply' (pdEta Φ) ψ (0, 1, 0) p dΦe dψ
  have R2 : pdEta (fun x => pdQ Φ x * ψ x) p = pdQ Φ p * pdEta ψ p + ψ p * pdEta (pdQ Φ) p :=
    fderiv_mul_apply' (pdQ Φ) ψ (0, 0, 1) p dΦq dψ
  have R3 : pdS (fun x => Φ x * pdEta ψ x) p = Φ p * pdS (pdEta ψ) p + pdEta ψ p * pdS Φ p :=
    fderiv_mul_apply' Φ (pdEta ψ) (1, 0, 0) p dΦ dψe
  have R4 : pdEta (fun x => Φ x * pdEta ψ x) p = Φ p * pdEta (pdEta ψ) p + pdEta ψ p * pdEta Φ p :=
    fderiv_mul_apply' Φ (pdEta ψ) (0, 0, 1) p dΦ dψe
  have R5 : pdEta (fun x => Φ x * (ψ x - opK ψ x)) p
      = Φ p * (pdEta ψ p - pdEta (opK ψ) p) + (ψ p - opK ψ p) * pdEta Φ p := by
    have h := fderiv_mul_apply' Φ (fun x => ψ x - opK ψ x) (0, 0, 1) p dΦ (dψ.sub dKψ)
    have hsub : HasFDerivAt (fun x => ψ x - opK ψ x)
        (fderiv ℝ ψ p - fderiv ℝ (opK ψ) p) p :=
      dψ.hasFDerivAt.sub dKψ.hasFDerivAt
    have hs : fderiv ℝ (fun x => ψ x - opK ψ x) p (0, 0, 1)
        = pdEta ψ p - pdEta (opK ψ) p := by
      rw [hsub.fderiv, ContinuousLinearMap.sub_apply]
      rfl
    show fderiv ℝ (fun x => Φ x * (ψ x - opK ψ x)) p (0, 0, 1) = _
    rw [h, hs] <;> rfl
  have hK : opK Φ p = (p.1 : ℂ) * (2 * pdS Φ p) + (p.2.2 : ℂ) * pdEta Φ p := opK_eq Φ p
  have hKψ : opK ψ p = (p.1 : ℂ) * (2 * pdS ψ p) + (p.2.2 : ℂ) * pdEta ψ p := opK_eq ψ p
  have hKE : opK (fun x => Φ x * pdEta ψ x) p
      = (p.1 : ℂ) * (2 * pdS (fun x => Φ x * pdEta ψ x) p)
        + (p.2.2 : ℂ) * pdEta (fun x => Φ x * pdEta ψ x) p := opK_eq _ p
  rw [R1, R2, R5, hKE, R3, R4, hK, hKψ, pdEta_opK hψ p, opK_eq (pdEta ψ) p,
    pdQ_pdEta_comm hΦ p, pdS_pdEta_comm hψ p]
  ring

end NearStreamMemberAux

end UnforcedLeray.Short.PartIIa
