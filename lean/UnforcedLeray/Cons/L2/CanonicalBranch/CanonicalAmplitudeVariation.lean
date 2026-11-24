import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeDyson


/-!
# The normalized amplitude differential identity

This downstream leaf applies the actual adjoint-mode weak Dyson derivative to the normalized
amplitude. The closed-domain D-pairing is kept explicit until the radial identification with the
profile-level definition of `kapMode` is proved.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.ComplexODEC


/-- Derivative of the actual scalar gauge on the positive real half-line. -/
theorem gauge_hasDerivAt {lam κ : ℂ} {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (gauge lam κ)
      (lam * gauge lam κ θ +
        Complex.exp (lam * (θ : ℂ)) *
          (κ * (θ : ℂ) ^ (κ - 1))) θ := by
  unfold gauge
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (lam * (x : ℂ)))
      (lam * Complex.exp (lam * (θ : ℂ))) θ := by
    have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * lam) lam θ := by
      simpa only [one_mul] using hid.mul_const lam
    have h := (Complex.hasDerivAt_exp ((θ : ℂ) * lam)).comp θ hlin
    have h' : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * lam))
        (Complex.exp ((θ : ℂ) * lam) * lam) θ := h
    convert h' using 1
    · funext x
      congr 1
      exact mul_comm _ _
    · ring
  by_cases hκ : κ = 0
  · subst κ
    simpa only [Complex.cpow_zero, sub_zero, mul_zero, zero_mul, mul_one, add_zero] using hexp
  · have hpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ κ)
        (κ * (θ : ℂ) ^ (κ - 1)) θ :=
      hasDerivAt_ofReal_cpow_const hθ.ne' hκ
    have hprod := hexp.mul hpow
    apply hprod.congr_deriv
    ring

/-- Logarithmic derivative of the scalar gauge. -/
theorem gauge_hasDerivAt_log {lam κ : ℂ} {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (gauge lam κ)
      ((lam + κ / (θ : ℂ)) * gauge lam κ θ) θ := by
  have h := gauge_hasDerivAt (lam := lam) (κ := κ) hθ
  have hpow : (θ : ℂ) ^ (κ - 1) = (θ : ℂ) ^ κ / (θ : ℂ) := by
    rw [Complex.cpow_sub κ 1 (Complex.ofReal_ne_zero.mpr hθ.ne'), Complex.cpow_one]
  convert h using 1
  rw [hpow, gauge]
  field_simp [Complex.ofReal_ne_zero.mpr hθ.ne']


/-- Shift the actual weak Dyson derivative from negative evolution time to the canonical turnover
coordinate `t`, keeping the positive coefficient `(R-t)⁻¹` explicit. -/
theorem inner_qdag_S_turnover_hasDerivWithinAt {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {R b₀ t : ℝ} (hb₀ : 0 < b₀)
    (ht0 : 0 ≤ t) (htt : t ≤ R - b₀) (f : XG) :
    HasDerivWithinAt
      (fun u => inner ℂ (qdagMode hF) (S (R - u) R f))
      (((((R - t)⁻¹ : ℝ) : ℂ) *
          inner ℂ (B0094.D ⟨qdagMode hF, qdagMode_mem_Ddomain hF⟩)
            (S (R - t) R f)) +
        lamMode c * inner ℂ (qdagMode hF) (S (R - t) R f))
      (Icc 0 (R - b₀)) t := by
  have hS := S_hasWeakDerivative_qdagMode (a := -R) (b := -b₀)
    (by linarith) hF (s := -R) (t := t - R) le_rfl (by linarith) (by linarith) f
  have hshift : HasDerivWithinAt (fun u : ℝ => u - R) 1 (Icc 0 (R - b₀)) t :=
    ((hasDerivAt_id t).sub_const R).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ => u - R) (Icc 0 (R - b₀)) (Icc (-R) (-b₀)) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hcomp := hS.scomp t hshift hmaps
  have hβ : backwardCanonicalBeta (-b₀) (t - R) = (R - t)⁻¹ := by
    rw [backwardCanonicalBeta_eq_neg_inv (by linarith : t - R ≤ -b₀)]
    have hden : t - R = -(R - t) := by ring
    rw [hden, inv_neg, neg_neg]
  rw [hβ] at hcomp
  simpa [Function.comp_def, neg_sub] using hcomp


/-- The normalized scalar gauge factor has the logarithmic derivative dictated by the turnover
coordinate. -/
theorem gaugeFactor_turnover_hasDerivWithinAt {lam κ : ℂ} {R b₀ t : ℝ}
    (hb₀ : 0 < b₀) (htt : t ≤ R - b₀) :
    HasDerivWithinAt
      (fun u => gauge lam κ (R - u) * gaugeInv lam κ R)
      (-((lam + κ / ((R - t : ℝ) : ℂ)) *
        (gauge lam κ (R - t) * gaugeInv lam κ R)))
      (Icc 0 (R - b₀)) t := by
  have hθ : 0 < R - t := by linarith
  have hshift : HasDerivWithinAt (fun u : ℝ => R - u) (-1) (Icc 0 (R - b₀)) t :=
    ((hasDerivAt_id' t).const_sub R).hasDerivWithinAt
  have hcomp := (gauge_hasDerivAt_log (lam := lam) (κ := κ) hθ).scomp_hasDerivWithinAt t hshift
  have hprod := hcomp.mul_const (gaugeInv lam κ R)
  have hcoeff' :
      ((-1 : ℝ) • ((lam + κ / ((R - t : ℝ) : ℂ)) * gauge lam κ (R - t))) *
          gaugeInv lam κ R =
        -((lam + κ / ((R - t : ℝ) : ℂ)) *
          (gauge lam κ (R - t) * gaugeInv lam κ R)) := by
    calc
      ((-1 : ℝ) • ((lam + κ / ((R - t : ℝ) : ℂ)) * gauge lam κ (R - t))) *
          gaugeInv lam κ R =
        (-((lam + κ / ((R - t : ℝ) : ℂ)) * gauge lam κ (R - t))) *
          gaugeInv lam κ R := by simp
      _ = -((lam + κ / ((R - t : ℝ) : ℂ)) *
          (gauge lam κ (R - t) * gaugeInv lam κ R)) := by ring
  have hprod' := hprod.congr_deriv hcoeff'
  simpa only [Function.comp_def] using hprod'


/-- Real derivative predicate on the complex Hilbert space with its canonical realification. -/
private abbrev TurnoverHasDerivWithinAt (f : ℝ → ℂ) (f' : ℂ) (s : Set ℝ) (t : ℝ) : Prop :=
  @HasDerivWithinAt ℝ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
    instInnerProductSpaceRealComplex.toModule _ _ f f' s t

/-- The actual normalized amplitude obeys its scalar ODE with the closed-domain D-pairing. The
remaining conversion of the q-component to `kapMode` is a separate concrete profile identity. -/
theorem amp_hasDerivWithinAt_Dpairing {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {R b₀ t : ℝ} (hb₀ : 0 < b₀)
    (ht0 : 0 ≤ t) (htt : t ≤ R - b₀) (f : XG) :
    TurnoverHasDerivWithinAt
      (fun u => amp (lamMode c) (kapMode c F) (qdagMode hF) R f u)
      ((gauge (lamMode c) (kapMode c F) (R - t) *
          gaugeInv (lamMode c) (kapMode c F) R) *
        ((((R - t)⁻¹ : ℝ) : ℂ) *
          (inner ℂ (B0094.D ⟨qdagMode hF, qdagMode_mem_Ddomain hF⟩)
              (S (R - t) R f) -
            kapMode c F * inner ℂ (qdagMode hF) (S (R - t) R f))))
      (Icc 0 (R - b₀)) t := by
  let α : ℝ → ℂ := fun u =>
    gauge (lamMode c) (kapMode c F) (R - u) * gaugeInv (lamMode c) (kapMode c F) R
  let y : ℝ → ℂ := fun u => inner ℂ (qdagMode hF) (S (R - u) R f)
  let d : ℝ → ℂ := fun u =>
    inner ℂ (B0094.D ⟨qdagMode hF, qdagMode_mem_Ddomain hF⟩) (S (R - u) R f)
  have hα := gaugeFactor_turnover_hasDerivWithinAt (lam := lamMode c)
    (κ := kapMode c F) hb₀ htt
  have hy := inner_qdag_S_turnover_hasDerivWithinAt hF hb₀ ht0 htt f
  have hprod := hα.mul hy
  have hβ :
      kapMode c F / ((R - t : ℝ) : ℂ) =
        kapMode c F * (((R - t)⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    congr 1
    simp
  have hcoeff :
      (-((lamMode c + kapMode c F / ((R - t : ℝ) : ℂ)) * α t) * y t) +
        α t * ((((R - t)⁻¹ : ℝ) : ℂ) * d t + lamMode c * y t) =
      α t * ((((R - t)⁻¹ : ℝ) : ℂ) * (d t - kapMode c F * y t)) := by
    rw [hβ]
    ring
  have hprod' := hprod.congr_deriv hcoeff
  have hAmp :
      (fun u => amp (lamMode c) (kapMode c F) (qdagMode hF) R f u) =
        fun u => α u * y u := by
    funext u
    simp [amp, normState, normProp_apply, α, y, inner_smul_right]
  have hprod'' : TurnoverHasDerivWithinAt (fun u => α u * y u)
      (α t * ((((R - t)⁻¹ : ℝ) : ℂ) * (d t - kapMode c F * y t)))
      (Icc 0 (R - b₀)) t := by
    apply hprod'.congr_of_mem
    · intro u hu
      simp [α, y, Pi.mul_apply]
    · exact ⟨ht0, htt⟩
  rw [hAmp]
  simpa [α, y, d] using hprod''

end UnforcedLeray.Cons.G3b
