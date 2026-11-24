import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Part II-b, task `PartII-b:T13/1/4/2/2` (`ChmLeibniz`)

Source `the November 2 reference manuscript` lines 1933-1935. For smooth `w`, `ζ`
and a space-time test `φ` the cut-off identity `∫ ζ w · (-∂_s φ - ν Δ φ) = ∫ chmF φ` follows from
integration by parts in `s`, `q`, `η` (smooth integrands, compact support of `φ`) and the pointwise
product rule `(∂_s - νΔ)(ζ w) = chmF` in the classical sense.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace ChmLeib

lemma cdir_snd_fst : (cdir 0).2.1 = 0 ∧ (cdir 1).2.1 = 1 ∧ (cdir 2).2.1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cdir]

lemma cdv_contDiff {w : Coord → ℂ} (hw : ContDiff ℝ ∞ w) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j w) := by
  unfold cdv
  exact ContDiff.clm_apply (f := fun x => fderiv ℝ w x) (g := fun _ : Coord => cdir j)
    (contDiff_infty_iff_fderiv.1 hw).2 (contDiff_const (c := cdir j))

lemma cpd_contDiff {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    ContDiff ℝ ∞ (cpd j φ) := by
  unfold cpd
  exact ContDiff.clm_apply (f := fun x => fderiv ℝ φ x) (g := fun _ : Coord => cdir j)
    (contDiff_infty_iff_fderiv.1 hφ).2 (contDiff_const (c := cdir j))

lemma cpd_hcs {φ : Coord → ℝ} (hφc : HasCompactSupport φ) (j : Fin 3) :
    HasCompactSupport (cpd j φ) := by
  unfold cpd
  exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hφc (cdir j)

lemma cdv_mul {f g : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin 3)
    (x : Coord) : cdv j (fun y => f y * g y) x = f x * cdv j g x + g x * cdv j f x := by
  unfold cdv
  have hd : HasFDerivAt (fun y => f y * g y)
      (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x :=
    ((hf.differentiable (by simp)) x).hasFDerivAt.mul
      ((hg.differentiable (by simp)) x).hasFDerivAt
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

lemma cdv_add {f g : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin 3)
    (x : Coord) : cdv j (fun y => f y + g y) x = cdv j f x + cdv j g x := by
  unfold cdv
  have hd : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    ((hf.differentiable (by simp)) x).hasFDerivAt.add
      ((hg.differentiable (by simp)) x).hasFDerivAt
  rw [hd.fderiv]
  simp

lemma cdv_ofReal {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin 3) (x : Coord) :
    cdv j (fun y => (ψ y : ℂ)) x = (cpd j ψ x : ℂ) := by
  unfold cdv cpd
  have hd : HasFDerivAt (fun y => (ψ y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ ψ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x ((hψ.differentiable (by simp)) x).hasFDerivAt
  rw [hd.fderiv]
  simp

lemma cpd_q (ζ : ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (j : Fin 3) (x : Coord) :
    cpd j (fun y => ζ y.2.1) x = deriv ζ x.2.1 * (cdir j).2.1 := by
  unfold cpd
  have hL : HasFDerivAt (fun y : Coord => y.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    hasFDerivAt_fst.comp x hasFDerivAt_snd
  have hz := (hζ.differentiable (by simp) x.2.1).hasDerivAt.comp_hasFDerivAt x hL
  rw [show (fun y : Coord => ζ y.2.1) = ζ ∘ (fun y : Coord => y.2.1) from rfl, hz.fderiv]
  simp

lemma integrable_mul_ofReal {V : Coord → ℂ} (hV : Continuous V) {ψ : Coord → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => V x * (ψ x : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport (hV.mul (Complex.continuous_ofReal.comp hψ))
  have h1 : HasCompactSupport (fun x => (ψ x : ℂ)) :=
    HasCompactSupport.comp_left (f := ψ) (g := fun t : ℝ => (t : ℂ)) hψc (by simp)
  exact h1.mul_left

/-- Integration by parts in one coordinate direction (SP 1933-1935 integrands). -/
lemma ibp_cpd (U : Coord → ℂ) (hU : ContDiff ℝ ∞ U) (ψ : Coord → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (j : Fin 3) :
    ∫ x, U x * (cpd j ψ x : ℂ) = -∫ x, cdv j U x * (ψ x : ℂ) := by
  have hdg : ∀ x, fderiv ℝ (fun y => (ψ y : ℂ)) x (cdir j) = (cpd j ψ x : ℂ) :=
    fun x => cdv_ofReal hψ j x
  have e1 : (fun x => U x * fderiv ℝ (fun y => (ψ y : ℂ)) x (cdir j)) =
      fun x => U x * (cpd j ψ x : ℂ) := funext fun x => by rw [hdg x]
  have hf'g : Integrable (fun x => fderiv ℝ U x (cdir j) * (ψ x : ℂ)) :=
    integrable_mul_ofReal (cdv_contDiff hU j).continuous (hψ.continuous) hψc
  have hfg' : Integrable (fun x => U x * fderiv ℝ (fun y => (ψ y : ℂ)) x (cdir j)) := by
    rw [e1]
    exact integrable_mul_ofReal hU.continuous (cpd_contDiff hψ j).continuous (cpd_hcs hψc j)
  have hfg : Integrable (fun x => U x * (ψ x : ℂ)) :=
    integrable_mul_ofReal hU.continuous hψ.continuous hψc
  have hf : ∀ x ∈ tsupport (fun y => (ψ y : ℂ)), DifferentiableAt ℝ U x :=
    fun x _ => (hU.differentiable (by simp)) x
  have hg : ∀ x ∈ tsupport U, DifferentiableAt ℝ (fun y => (ψ y : ℂ)) x :=
    fun x _ => Complex.ofRealCLM.differentiableAt.comp x ((hψ.differentiable (by simp)) x)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := U)
    (g := fun y => (ψ y : ℂ)) (v := cdir j) hf'g hfg' hfg hf hg
  rw [e1] at key
  exact key


lemma chmU_contDiff {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ) {w : Coord → ℂ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (chmU ζ w) := by
  have hζq : ContDiff ℝ ∞ (fun y : Coord => ζ y.2.1) :=
    hζ.comp (contDiff_fst.comp contDiff_snd)
  have hP : ContDiff ℝ ∞ (fun y : Coord => (ζ y.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hζq
  exact hP.mul hw

/-- Pointwise identity `(∂_s - ν Δ_{q,η})(ζ w) = chmF` (SP 1933-1935). -/
lemma leib_pt (ν : ℝ) (w : Coord → ℂ) (ζ : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hζ : ContDiff ℝ ∞ ζ) (x : Coord) :
    cdv 0 (chmU ζ w) x - (ν : ℂ) * (cdv 1 (cdv 1 (chmU ζ w)) x + cdv 2 (cdv 2 (chmU ζ w)) x)
      = chmF ν ζ w x := by
  have hζq : ContDiff ℝ ∞ (fun y : Coord => ζ y.2.1) :=
    hζ.comp (contDiff_fst.comp contDiff_snd)
  have hdζ : ContDiff ℝ ∞ (deriv ζ) := (contDiff_infty_iff_deriv.1 hζ).2
  have hdζq : ContDiff ℝ ∞ (fun y : Coord => deriv ζ y.2.1) :=
    hdζ.comp (contDiff_fst.comp contDiff_snd)
  have hP : ContDiff ℝ ∞ (fun y : Coord => (ζ y.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hζq
  have hZ : ContDiff ℝ ∞ (fun y : Coord => ((deriv ζ y.2.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hdζq
  have hPd : ∀ (j : Fin 3) (y : Coord),
      cdv j (fun z : Coord => (ζ z.2.1 : ℂ)) y = ((deriv ζ y.2.1 * (cdir j).2.1 : ℝ) : ℂ) :=
    fun j y => (cdv_ofReal hζq j y).trans (by rw [cpd_q ζ hζ j y])
  have hZd : ∀ (j : Fin 3) (y : Coord),
      cdv j (fun z : Coord => ((deriv ζ z.2.1 : ℝ) : ℂ)) y =
        ((deriv (deriv ζ) y.2.1 * (cdir j).2.1 : ℝ) : ℂ) :=
    fun j y => (cdv_ofReal hdζq j y).trans (by rw [cpd_q (deriv ζ) hdζ j y])
  have hP0 : ∀ y, cdv 0 (fun z : Coord => (ζ z.2.1 : ℂ)) y = 0 := fun y => by
    rw [hPd, (cdir_snd_fst).1]; simp
  have hP1 : ∀ y, cdv 1 (fun z : Coord => (ζ z.2.1 : ℂ)) y = ((deriv ζ y.2.1 : ℝ) : ℂ) := fun y => by
    rw [hPd, (cdir_snd_fst).2.1]; simp
  have hP2 : ∀ y, cdv 2 (fun z : Coord => (ζ z.2.1 : ℂ)) y = 0 := fun y => by
    rw [hPd, (cdir_snd_fst).2.2]; simp
  have hU2 : cdv 2 (chmU ζ w) = fun y => (ζ y.2.1 : ℂ) * cdv 2 w y := by
    funext y
    have hm := cdv_mul hP hw 2 y
    beta_reduce at hm
    rw [show chmU ζ w = fun z => (ζ z.2.1 : ℂ) * w z from rfl, hm, hP2 y]
    ring
  have hU1 : cdv 1 (chmU ζ w) = fun y => (ζ y.2.1 : ℂ) * cdv 1 w y + w y * ((deriv ζ y.2.1 : ℝ) : ℂ) := by
    funext y
    have hm := cdv_mul hP hw 1 y
    beta_reduce at hm
    rw [show chmU ζ w = fun z => (ζ z.2.1 : ℂ) * w z from rfl, hm, hP1 y]
  have hsplit : cdv 1 (cdv 1 (chmU ζ w)) x =
      cdv 1 (fun y => (ζ y.2.1 : ℂ) * cdv 1 w y) x +
        cdv 1 (fun y => w y * ((deriv ζ y.2.1 : ℝ) : ℂ)) x := by
    rw [hU1]
    exact cdv_add (hP.mul (cdv_contDiff hw 1)) (hw.mul hZ) 1 x
  have hT1 : cdv 1 (fun y => (ζ y.2.1 : ℂ) * cdv 1 w y) x =
      (ζ x.2.1 : ℂ) * cdv 1 (cdv 1 w) x + cdv 1 w x * ((deriv ζ x.2.1 : ℝ) : ℂ) := by
    have hm := cdv_mul hP (cdv_contDiff hw 1) 1 x
    beta_reduce at hm
    rw [hm, hP1 x]
  have hT2 : cdv 1 (fun y => w y * ((deriv ζ y.2.1 : ℝ) : ℂ)) x =
      w x * ((deriv (deriv ζ) x.2.1 : ℝ) : ℂ) + ((deriv ζ x.2.1 : ℝ) : ℂ) * cdv 1 w x := by
    have hm := cdv_mul hw hZ 1 x
    beta_reduce at hm
    rw [hm, hZd 1 x, (cdir_snd_fst).2.1]
    push_cast
    ring
  have hT3 : cdv 2 (cdv 2 (chmU ζ w)) x = (ζ x.2.1 : ℂ) * cdv 2 (cdv 2 w) x := by
    rw [hU2]
    have hm := cdv_mul hP (cdv_contDiff hw 2) 2 x
    beta_reduce at hm
    rw [hm, hP2 x]
    ring
  have hT0 : cdv 0 (chmU ζ w) x = (ζ x.2.1 : ℂ) * cdv 0 w x := by
    have hm := cdv_mul hP hw 0 x
    beta_reduce at hm
    rw [show chmU ζ w = fun z => (ζ z.2.1 : ℂ) * w z from rfl, hm, hP0 x]
    ring
  unfold chmF chmRhs chmComm
  rw [hT0, hsplit, hT1, hT2, hT3]
  ring

/-- The cut-off identity against a space-time test (SP 1933-1935). -/
lemma leib_integral (ν : ℝ) (w : Coord → ℂ) (ζ : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hζ : ContDiff ℝ ∞ ζ) (φ : Coord → ℝ) (hφ : IsSTTestCoord φ) :
    ∫ x, chmU ζ w x * (cylHeatT ν φ x : ℂ) = ∫ x, chmF ν ζ w x * (φ x : ℂ) := by
  have hUs : ContDiff ℝ ∞ (chmU ζ w) := chmU_contDiff hζ hw
  have hφs := hφ.smooth
  have hφc := hφ.compact
  have hφ1 : ContDiff ℝ ∞ (cpd 1 φ) := cpd_contDiff hφs 1
  have hφ1c : HasCompactSupport (cpd 1 φ) := cpd_hcs hφc 1
  have hφ2 : ContDiff ℝ ∞ (cpd 2 φ) := cpd_contDiff hφs 2
  have hφ2c : HasCompactSupport (cpd 2 φ) := cpd_hcs hφc 2
  have hexp : (fun x => chmU ζ w x * (cylHeatT ν φ x : ℂ)) = fun x =>
      -(chmU ζ w x * (cpd 0 φ x : ℂ)) - (ν : ℂ) * (chmU ζ w x * (cpd 1 (cpd 1 φ) x : ℂ))
        - (ν : ℂ) * (chmU ζ w x * (cpd 2 (cpd 2 φ) x : ℂ)) := by
    funext x
    unfold cylHeatT
    push_cast
    ring
  have I1 : Integrable (fun x => chmU ζ w x * (cpd 0 φ x : ℂ)) :=
    integrable_mul_ofReal hUs.continuous (cpd_contDiff hφs 0).continuous (cpd_hcs hφc 0)
  have I2 : Integrable (fun x => chmU ζ w x * (cpd 1 (cpd 1 φ) x : ℂ)) :=
    integrable_mul_ofReal hUs.continuous (cpd_contDiff hφ1 1).continuous (cpd_hcs hφ1c 1)
  have I3 : Integrable (fun x => chmU ζ w x * (cpd 2 (cpd 2 φ) x : ℂ)) :=
    integrable_mul_ofReal hUs.continuous (cpd_contDiff hφ2 2).continuous (cpd_hcs hφ2c 2)
  have IA : Integrable (fun x => -(chmU ζ w x * (cpd 0 φ x : ℂ)) -
      (ν : ℂ) * (chmU ζ w x * (cpd 1 (cpd 1 φ) x : ℂ))) :=
    I1.neg.sub (I2.const_mul (ν : ℂ))
  have IB : Integrable (fun x => -(chmU ζ w x * (cpd 0 φ x : ℂ))) := I1.neg
  have IC : Integrable (fun x => (ν : ℂ) * (chmU ζ w x * (cpd 1 (cpd 1 φ) x : ℂ))) :=
    I2.const_mul (ν : ℂ)
  have ID : Integrable (fun x => (ν : ℂ) * (chmU ζ w x * (cpd 2 (cpd 2 φ) x : ℂ))) :=
    I3.const_mul (ν : ℂ)
  rw [hexp, integral_sub IA ID, integral_sub IB IC, integral_neg, integral_const_mul,
    integral_const_mul]
  have i0 := ibp_cpd (chmU ζ w) hUs φ hφs hφc 0
  have i1 : ∫ x, chmU ζ w x * (cpd 1 (cpd 1 φ) x : ℂ) =
      -∫ x, cdv 1 (chmU ζ w) x * (cpd 1 φ x : ℂ) :=
    ibp_cpd (chmU ζ w) hUs (cpd 1 φ) hφ1 hφ1c 1
  have i1' : ∫ x, cdv 1 (chmU ζ w) x * (cpd 1 φ x : ℂ) =
      -∫ x, cdv 1 (cdv 1 (chmU ζ w)) x * (φ x : ℂ) :=
    ibp_cpd (cdv 1 (chmU ζ w)) (cdv_contDiff hUs 1) φ hφs hφc 1
  have i2 : ∫ x, chmU ζ w x * (cpd 2 (cpd 2 φ) x : ℂ) =
      -∫ x, cdv 2 (chmU ζ w) x * (cpd 2 φ x : ℂ) :=
    ibp_cpd (chmU ζ w) hUs (cpd 2 φ) hφ2 hφ2c 2
  have i2' : ∫ x, cdv 2 (chmU ζ w) x * (cpd 2 φ x : ℂ) =
      -∫ x, cdv 2 (cdv 2 (chmU ζ w)) x * (φ x : ℂ) :=
    ibp_cpd (cdv 2 (chmU ζ w)) (cdv_contDiff hUs 2) φ hφs hφc 2
  have hpt : ∀ x, chmF ν ζ w x * (φ x : ℂ) =
      cdv 0 (chmU ζ w) x * (φ x : ℂ) - (ν : ℂ) * (cdv 1 (cdv 1 (chmU ζ w)) x * (φ x : ℂ))
        - (ν : ℂ) * (cdv 2 (cdv 2 (chmU ζ w)) x * (φ x : ℂ)) := by
    intro x
    rw [← leib_pt ν w ζ hw hζ x]
    ring
  have J0 : Integrable (fun x => cdv 0 (chmU ζ w) x * (φ x : ℂ)) :=
    integrable_mul_ofReal (cdv_contDiff hUs 0).continuous hφs.continuous hφc
  have J1 : Integrable (fun x => cdv 1 (cdv 1 (chmU ζ w)) x * (φ x : ℂ)) :=
    integrable_mul_ofReal (cdv_contDiff (cdv_contDiff hUs 1) 1).continuous hφs.continuous hφc
  have J2 : Integrable (fun x => cdv 2 (cdv 2 (chmU ζ w)) x * (φ x : ℂ)) :=
    integrable_mul_ofReal (cdv_contDiff (cdv_contDiff hUs 2) 2).continuous hφs.continuous hφc
  have JA : Integrable (fun x => cdv 0 (chmU ζ w) x * (φ x : ℂ) -
      (ν : ℂ) * (cdv 1 (cdv 1 (chmU ζ w)) x * (φ x : ℂ))) :=
    J0.sub (J1.const_mul (ν : ℂ))
  have JC : Integrable (fun x => (ν : ℂ) * (cdv 2 (cdv 2 (chmU ζ w)) x * (φ x : ℂ))) :=
    J2.const_mul (ν : ℂ)
  have hR : ∫ x, chmF ν ζ w x * (φ x : ℂ) =
      (∫ x, cdv 0 (chmU ζ w) x * (φ x : ℂ)) -
        (ν : ℂ) * (∫ x, cdv 1 (cdv 1 (chmU ζ w)) x * (φ x : ℂ)) -
        (ν : ℂ) * (∫ x, cdv 2 (cdv 2 (chmU ζ w)) x * (φ x : ℂ)) := by
    simp_rw [hpt]
    rw [integral_sub JA JC, integral_sub J0 (J1.const_mul (ν : ℂ)), integral_const_mul,
      integral_const_mul]
  rw [i0, i1, i1', i2, i2', hR]
  ring

end ChmLeib

/-- **Lemma 2 (Leibniz, SP 1933-1935).** -/
theorem chmLeibniz : UnforcedLeray.Short.IIb.ChmLeibniz := by
  intro ν w ζ hw hζ _ φ hφ
  exact ChmLeib.leib_integral ν w ζ hw hζ φ hφ

end UnforcedLeray.Short.IIb
