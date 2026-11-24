import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeVariation

/-!
# Weak generator of the actual normalized evolution

On a finite turnover block, the normalized state has the weak generator
`β D + L₀ − λ − βκ`, tested against every vector in the closed Gaussian D-domain. This provides
the actual time/gauge bridge without a regularity assumption on the evolving state.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Topology InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
  UnforcedLeray.ComplexODEC

/-- The actual backward Dyson evolution, tested against an arbitrary closed-domain functional. -/
theorem S_hasWeakDerivative_Ddomain {a b : ℝ} (hb : b < 0)
    (z : B0094.D.domain) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (x : XG) :
    HasDerivWithinAt
      (fun u => inner ℂ (z : XG) (S (-u) (-s) x))
      (((backwardCanonicalBeta b t : ℝ) : ℂ) *
          inner ℂ (B0094.D z) (S (-t) (-s) x) +
        inner ℂ (z : XG) (B0012.L0 (S (-t) (-s) x)))
      (Icc s b) t := by
  let ℓ : XG →L[ℂ] ℂ := innerSL ℂ (z : XG)
  let β := backwardCanonicalBeta b
  let E := freeFam a b hb
  let A := pertL0 a b
  let U := Evolution.dyson E A
  let G : ℝ → (XG →L[ℂ] ℂ) → (XG →L[ℂ] ℂ) :=
    fun r φ => ((β r : ℝ) : ℂ) • innerSL ℂ (B0094.D z)
  have hβc : Continuous β := continuous_backwardCanonicalBeta b hb
  have hG : ∀ φ ∈ ({ℓ} : Set (XG →L[ℂ] ℂ)),
      ContinuousOn (fun r => G r φ) (Icc a b) := by
    intro φ hφ
    simp only [Set.mem_singleton_iff] at hφ
    subst φ
    exact (Complex.continuous_ofReal.comp hβc).continuousOn.smul continuousOn_const
  have hAc : ContinuousOn A.A (Icc a b) := continuousOn_const
  have hEweak : E.HasWeakGenerator {ℓ} G := by
    have h := freeFam_hasWeakGenerator_domain (a := a) hb z
    intro φ hφ s' x' hs' t' ht'
    have hφeq : φ = innerSL ℂ (z : XG) := by
      simpa [ℓ] using hφ
    subst φ
    simpa [E, G, β, ℓ, backwardCanonicalBeta] using
      h (innerSL ℂ (z : XG)) (by simp) s' x' hs' t' ht'
  have hUweak := Evolution.dyson_hasWeakGenerator E A hEweak hG hAc
  have hUder := hUweak ℓ (Set.mem_singleton _) s x has t ⟨hst, htb⟩
  have hSeq : ∀ u ∈ Icc s b, S (-u) (-s) = U.U u s := by
    intro u hu
    have huPos : 0 < -u := by linarith [hu.2, hb]
    have hsu : -u ≤ -s := by linarith [hu.1]
    have hEq := S_eq_dyson (a := a) hb huPos hsu (by simpa using has)
      (by simpa using hu.2)
    simpa [U, E, A, freeFam, pertL0] using hEq
  have hSeqx : ∀ u ∈ Icc s b,
      inner ℂ (z : XG) (S (-u) (-s) x) = inner ℂ (z : XG) (U.U u s x) := by
    intro u hu
    exact congrArg (fun V : XG →L[ℂ] XG => inner ℂ (z : XG) (V x)) (hSeq u hu)
  have hder := hUder.congr_of_mem hSeqx ⟨hst, htb⟩
  change HasDerivWithinAt _
      (G t ℓ (U.U t s x) + ℓ (B0012.L0 (U.U t s x))) (Icc s b) t at hder
  simpa [ℓ, G, β, innerSL_apply_apply, hSeq t ⟨hst, htb⟩] using hder


/-- Real derivative on the canonical realification of the complex Hilbert space. -/
private abbrev TurnoverHasDerivWithinAt (f : ℝ → ℂ) (f' : ℂ) (s : Set ℝ) (t : ℝ) : Prop :=
  @HasDerivWithinAt ℝ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
    instInnerProductSpaceRealComplex.toModule _ _ f f' s t

/-- On any finite turnover block bounded away from `R`, the actual normalized path has the weak
generator `βD + T − λ − βκ + A`, tested against every vector in the closed D-domain. Here
`β(t)=1/(R−t)`, `T=−2iΩ`, and `A=2ikR`; no regularity of the evolving state is assumed. -/
theorem normState_hasWeakGenerator_Ddomain {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {R b₀ t : ℝ} (hb₀ : 0 < b₀)
    (ht0 : 0 ≤ t) (htt : t ≤ R - b₀) (f : XG) (z : B0094.D.domain) :
    TurnoverHasDerivWithinAt
      (fun u => inner ℂ (z : XG) (normState (lamMode c) (kapMode c F) R f u))
      (((((R - t)⁻¹ : ℝ) : ℂ) *
          inner ℂ (B0094.D z)
            (normState (lamMode c) (kapMode c F) R f t)) +
        inner ℂ (z : XG)
          ((((-2 * Complex.I) • B0012.omegaOp -
              lamMode c • (1 : XG →L[ℂ] XG) -
              (((((R - t)⁻¹ : ℝ) : ℂ) * kapMode c F) •
                (1 : XG →L[ℂ] XG)) +
              (2 * Complex.I) • B0012.kROp)
            (normState (lamMode c) (kapMode c F) R f t))))
      (Icc 0 (R - b₀)) t := by
  let lam := lamMode c
  let κ := kapMode c F
  let α : ℝ → ℂ := fun u => gauge lam κ (R - u) * gaugeInv lam κ R
  let y : ℝ → ℂ := fun u => inner ℂ (z : XG) (S (R - u) R f)
  let dD : ℝ → ℂ := fun u => inner ℂ (B0094.D z) (S (R - u) R f)
  let dL : ℝ → ℂ := fun u => inner ℂ (z : XG) (B0012.L0 (S (R - u) R f))
  let β : ℝ → ℝ := fun u => (R - u)⁻¹
  have hα := gaugeFactor_turnover_hasDerivWithinAt (lam := lam) (κ := κ) hb₀ htt
  have hSturn : TurnoverHasDerivWithinAt y
      (((β t : ℝ) : ℂ) * dD t + dL t) (Icc 0 (R - b₀)) t := by
    have hS := S_hasWeakDerivative_Ddomain (a := -R) (b := -b₀)
      (by linarith) z (s := -R) (t := t - R) le_rfl (by linarith) (by linarith) f
    have hshift : HasDerivWithinAt (fun u : ℝ => u - R) 1 (Icc 0 (R - b₀)) t :=
      ((hasDerivAt_id t).sub_const R).hasDerivWithinAt
    have hmaps : MapsTo (fun u : ℝ => u - R) (Icc 0 (R - b₀)) (Icc (-R) (-b₀)) := by
      intro u hu
      change -R ≤ u - R ∧ u - R ≤ -b₀
      constructor <;> linarith [hu.1, hu.2]
    have hcomp := hS.scomp t hshift hmaps
    have hβeq : backwardCanonicalBeta (-b₀) (t - R) = (R - t)⁻¹ := by
      rw [backwardCanonicalBeta_eq_neg_inv (by linarith : t - R ≤ -b₀)]
      have hden : t - R = -(R - t) := by ring
      rw [hden, inv_neg, neg_neg]
    rw [hβeq] at hcomp
    simpa [y, dD, dL, β, Function.comp_def, neg_sub] using hcomp
  have hprod := hα.mul hSturn
  have hβ : kapMode c F / ((R - t : ℝ) : ℂ) =
      kapMode c F * (((R - t)⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    congr 1
    simp
  have hcoeff :
      (-((lam + κ / ((R - t : ℝ) : ℂ)) * α t) * y t) +
        α t * ((((R - t)⁻¹ : ℝ) : ℂ) * dD t + dL t) =
      (((R - t)⁻¹ : ℝ) : ℂ) * (α t * dD t) + α t * dL t -
        lam * (α t * y t) - (((R - t)⁻¹ : ℝ) : ℂ) * κ * (α t * y t) := by
    rw [hβ]
    ring
  have hprod' := hprod.congr_deriv hcoeff
  have hstate : (fun u => normState lam κ R f u) =
      fun u => α u • S (R - u) R f := by
    funext u
    simp [normState, normProp_apply, α, lam, κ]
  have hstate_t := congrFun hstate t
  have hpairD : ((R - t)⁻¹ : ℂ) * (α t * dD t) =
      ((R - t)⁻¹ : ℂ) * inner ℂ (B0094.D z) (normState lam κ R f t) := by
    rw [hstate_t]
    simp [dD, inner_smul_right]
  have hpairL : α t * dL t = inner ℂ (z : XG)
      (B0012.L0 (normState lam κ R f t)) := by
    rw [hstate_t]
    simp [dL, inner_smul_right, map_smul]
  have hpairY : α t * y t = inner ℂ (z : XG) (normState lam κ R f t) := by
    rw [hstate_t]
    simp [y, inner_smul_right]
  have hcoefL0 :
      ((R - t)⁻¹ : ℂ) * inner ℂ (B0094.D z) (normState lam κ R f t) +
        inner ℂ (z : XG) (B0012.L0 (normState lam κ R f t)) -
          lam * inner ℂ (z : XG) (normState lam κ R f t) -
            ((R - t)⁻¹ : ℂ) * κ * inner ℂ (z : XG) (normState lam κ R f t) =
      ((R - t)⁻¹ : ℂ) * inner ℂ (B0094.D z) (normState lam κ R f t) +
        inner ℂ (z : XG)
          (((B0012.L0 - lam • (1 : XG →L[ℂ] XG) -
              (((R - t)⁻¹ : ℂ) * κ) • (1 : XG →L[ℂ] XG))
            (normState lam κ R f t))) := by
    simp [map_sub, map_smul, inner_sub_right, inner_smul_right]
    ring
  have hL0 : B0012.L0 =
      (-2 * Complex.I) • B0012.omegaOp + (2 * Complex.I) • B0012.kROp := rfl
  have hsplit :
      inner ℂ (z : XG)
          (((B0012.L0 - lam • (1 : XG →L[ℂ] XG) -
              (((R - t)⁻¹ : ℂ) * κ) • (1 : XG →L[ℂ] XG))
            (normState lam κ R f t))) =
        inner ℂ (z : XG)
          ((((-2 * Complex.I) • B0012.omegaOp -
              lam • (1 : XG →L[ℂ] XG) -
              (((R - t)⁻¹ : ℂ) * κ) • (1 : XG →L[ℂ] XG) +
              (2 * Complex.I) • B0012.kROp)
            (normState lam κ R f t))) := by
    rw [hL0]
    congr 1
    abel
  have hder := hprod'.congr_of_mem (fun u hu => by
    change inner ℂ (z : XG) (normState lam κ R f u) = α u * y u
    simp [normState, α, y, lam, κ, normProp_apply, inner_smul_right])
    ⟨ht0, htt⟩
  have hderCast := hder
  simp only [Complex.ofReal_inv, Complex.ofReal_sub] at hderCast
  rw [hpairD, hpairL, hpairY, hcoefL0, hsplit] at hderCast
  simpa [α, y, lam, κ] using hderCast

end UnforcedLeray.Cons.G3b

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123
  UnforcedLeray.ComplexODEC

/-- The bounded part of the normalized Gaussian generator at turnover time `u`. -/
def normalizedTurnoverGenerator (c : ℂ) (F : ℝ → ℂ) (R u : ℝ) : XG →L[ℂ] XG :=
  (-2 * Complex.I) • B0012.omegaOp -
    lamMode c • (1 : XG →L[ℂ] XG) -
    (((((R - u)⁻¹ : ℝ) : ℂ) * kapMode c F) • (1 : XG →L[ℂ] XG)) +
    (2 * Complex.I) • B0012.kROp

/-- The scalar weak-generator integrand, including the closed-D term tested on its domain. -/
def normalizedTurnoverWeakIntegrand (c : ℂ) (F : ℝ → ℂ) (R : ℝ)
    (f : XG) (z : B0094.D.domain) (u : ℝ) : ℂ :=
  (((R - u)⁻¹ : ℝ) : ℂ) *
      inner ℂ (B0094.D z) (normState (lamMode c) (kapMode c F) R f u) +
    inner ℂ (z : XG)
      (normalizedTurnoverGenerator c F R u
        (normState (lamMode c) (kapMode c F) R f u))

/-- The integrated weak equation for the actual normalized state on any finite turnover
subinterval. This is the interval mild identity tested against an arbitrary vector in `D.domain`;
no domain assumption is imposed on `normState`. -/
theorem normState_integral_weakGenerator_Ddomain {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) {R b₀ s t : ℝ} (hb₀ : 0 < b₀)
    (hs : 0 ≤ s) (hst : s ≤ t) (htt : t ≤ R - b₀)
    (f : XG) (z : B0094.D.domain) :
    inner ℂ (z : XG) (normState (lamMode c) (kapMode c F) R f t) =
      inner ℂ (z : XG) (normState (lamMode c) (kapMode c F) R f s) +
        ∫ u in s..t, normalizedTurnoverWeakIntegrand c F R f z u := by
  let T := R - b₀
  let Y : ℝ → ℂ := fun u =>
    inner ℂ (z : XG) (normState (lamMode c) (kapMode c F) R f u)
  let H : ℝ → ℂ := normalizedTurnoverWeakIntegrand c F R f z
  have hYc : ContinuousOn Y (Icc s t) := by
    have hstate := continuousOn_normState (lam := lamMode c) (κ := kapMode c F)
      (R := R) hb₀ f
    have hsub : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs htt
    exact (continuousOn_const.inner hstate).mono hsub
  have hβc : ContinuousOn
      (fun u : ℝ => (((R - u)⁻¹ : ℝ) : ℂ)) (Icc s t) := by
    have hreal : ContinuousOn (fun u : ℝ => (R - u)⁻¹) (Icc s t) :=
      (continuous_sub_left R).continuousOn.inv₀ (by
        intro u hu
        apply sub_ne_zero.mpr
        exact ne_of_gt (by linarith [hu.2, htt, hb₀]))
    exact Complex.continuous_ofReal.comp_continuousOn hreal
  have hstate : ContinuousOn (fun u : ℝ => normState (lamMode c) (kapMode c F) R f u)
      (Icc s t) := by
    exact (continuousOn_normState (lam := lamMode c) (κ := kapMode c F)
      (R := R) hb₀ f).mono (Icc_subset_Icc hs htt)
  have hDtest : ContinuousOn (fun x : XG => inner ℂ (B0094.D z) x) Set.univ := by
    exact (innerSL ℂ (B0094.D z)).continuous.continuousOn
  have hGcont : ContinuousOn
      (fun u : ℝ => normalizedTurnoverGenerator c F R u) (Icc s t) := by
    have hscalar : ContinuousOn
        (fun u : ℝ => (((R - u)⁻¹ : ℝ) : ℂ) * kapMode c F) (Icc s t) :=
      hβc.mul continuousOn_const
    exact continuousOn_const.sub (hscalar.smul continuousOn_const) |>.add continuousOn_const
  have hGapply : ContinuousOn
      (fun u : ℝ => normalizedTurnoverGenerator c F R u
        (normState (lamMode c) (kapMode c F) R f u)) (Icc s t) := by
    exact hGcont.clm_apply hstate
  have hHc : ContinuousOn H (Icc s t) := by
    have hD := hDtest.comp hstate (by intro u hu; trivial)
    exact (hβc.mul hD).add (continuousOn_const.inner hGapply)
  have hderiv : ∀ u ∈ Ioo s t, HasDerivWithinAt Y (H u) (Ioi u) u := by
    intro u hu
    have hgen := normState_hasWeakGenerator_Ddomain hF (R := R) (b₀ := b₀)
      (t := u) hb₀ (le_trans hs (le_of_lt hu.1)) (le_trans (le_of_lt hu.2) htt) f z
    have huBlock : u ∈ Ico 0 T := ⟨le_trans hs (le_of_lt hu.1),
      lt_of_lt_of_le hu.2 htt⟩
    have hright := hgen.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem huBlock)
    have hright' := hright.mono Ioi_subset_Ici_self
    simpa [Y, H, normalizedTurnoverWeakIntegrand, normalizedTurnoverGenerator,
      TurnoverHasDerivWithinAt] using hright'
  have hint : IntervalIntegrable H volume s t := hHc.intervalIntegrable_of_Icc hst
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hst hYc hderiv hint
  have hresult : (∫ u in s..t, H u) = Y t - Y s := by rw [hFTC]
  change Y t = Y s + ∫ u in s..t, H u
  rw [hresult]
  ring

end UnforcedLeray.Cons.G3b
