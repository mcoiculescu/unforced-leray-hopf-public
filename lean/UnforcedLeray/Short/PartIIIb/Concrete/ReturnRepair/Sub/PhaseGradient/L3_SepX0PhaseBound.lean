import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L2_SepWPhaseSup
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2

/-!
# `PartIII-b:C/rep/2/3` (task L3): `SepX0PhaseBound`

Source `the November 2 reference manuscript` 4171-4174 (`X0 = W_mu - W_{mu+1}`)
and 3622-3647.  For `rIn <= rho y` (inside the open set `rOut < rho y`), `sepX0` is the real part
`reL` of `W_mu - W_{mu+1}`, where `reL : C^3 -> R^3` is a continuous real-linear map.  The
components of `W_m` are `C^2` on the open set (`sepWSmoothOn_of`), so `iteratedFDeriv` commutes
with `reL` and the difference, giving the pointwise bound
`|D^j X0| <= ||reL|| (|D^j W_mu| + |D^j W_{mu+1}|)`.  Minkowski in `L^{22/3}_y` and the phase
supremum `sepWPhaseSup` (S1, task L2) with the compact set `K = {mu, mu+1 : mu in [s1, s2]}`
finish the proof.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The real-part map `C^3 -> R^3` (Cartesian components), real-linear. -/
def reLin : (Fin 3 → ℂ) →ₗ[ℝ] Space where
  toFun v := WithLp.toLp 2 (fun i => (v i).re)
  map_add' v w := by
    ext i
    simp
  map_smul' c v := by
    ext i
    simp

/-- `reLin` as a continuous linear map (finite-dimensional domain). -/
def reL : (Fin 3 → ℂ) →L[ℝ] Space := LinearMap.toContinuousLinearMap reLin

theorem sepX0_eq_reL (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) :
    sepX0 ν μ T τ = fun z => reL (IIIa.sepW ν (μ : ℂ) T z τ - IIIa.sepW ν ((μ : ℂ) + 1) T z τ) := by
  funext z
  rfl

/-- Pointwise derivative bound for `reL` composed with a difference of `C^2` maps on an open set. -/
theorem iteratedFDeriv_reL_le {U : Set Space} (hU : IsOpen U)
    {f g : Space → (Fin 3 → ℂ)} (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    {j : ℕ} (hj : j ≤ 2) {y : Space} (hy : y ∈ U) :
    ‖iteratedFDeriv ℝ j (fun z => reL (f z - g z)) y‖ₑ ≤
      ENNReal.ofReal ‖reL‖ * (‖iteratedFDeriv ℝ j f y‖ₑ + ‖iteratedFDeriv ℝ j g y‖ₑ) := by
  have hfy : ContDiffWithinAt ℝ j f U y := (hf.of_le (by exact_mod_cast hj)).contDiffWithinAt hy
  have hgy : ContDiffWithinAt ℝ j g U y := (hg.of_le (by exact_mod_cast hj)).contDiffWithinAt hy
  have hfg2 : ContDiffWithinAt ℝ 2 (f - g) U y := (hf.sub hg).contDiffWithinAt hy
  have h1 := reL.norm_iteratedFDerivWithin_comp_left (n := j) hfg2 hU.uniqueDiffOn hy
    (by exact_mod_cast hj)
  have h2 : iteratedFDerivWithin ℝ j (f - g) U y =
      iteratedFDerivWithin ℝ j f U y - iteratedFDerivWithin ℝ j g U y :=
    iteratedFDerivWithin_sub_apply hfy hgy hU.uniqueDiffOn hy
  have e0 : iteratedFDeriv ℝ j (fun z => reL (f z - g z)) y =
      iteratedFDeriv ℝ j (reL ∘ (f - g)) y := rfl
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := reL ∘ (f - g)) j hU hy
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hU hy
  have e3 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) j hU hy
  have hreal : ‖iteratedFDeriv ℝ j (reL ∘ (f - g)) y‖ ≤
      ‖reL‖ * (‖iteratedFDeriv ℝ j f y‖ + ‖iteratedFDeriv ℝ j g y‖) := by
    rw [← e1, ← e2, ← e3]
    calc ‖iteratedFDerivWithin ℝ j (reL ∘ (f - g)) U y‖
        ≤ ‖reL‖ * ‖iteratedFDerivWithin ℝ j (f - g) U y‖ := h1
      _ = ‖reL‖ * ‖iteratedFDerivWithin ℝ j f U y - iteratedFDerivWithin ℝ j g U y‖ := by
          rw [h2]
      _ ≤ ‖reL‖ * (‖iteratedFDerivWithin ℝ j f U y‖ + ‖iteratedFDerivWithin ℝ j g U y‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  rw [e0, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _)
    (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The continuous real-part map `ϱ`-level continuity of the open set `{rOut < ϱ y}`. -/
theorem measurable_youngDerivNorm (ν : ℝ) (m : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (j : ℕ) (rOut rIn P τ : ℝ) (hj : j ≤ 2) (hν : 0 < ν) (hm : -(1 / 4) < m.re) (hrO : 0 ≤ rOut)
    (hrr : rOut < rIn) (hP : 0 < P) (hT : IIIa.IsSepSource P rOut T) (hS : SepMoment P T) :
    Measurable (IIIa.youngDerivNorm ν m T j rIn τ) := by
  classical
  set U : Set Space := {y : Space | rOut < ϱ y} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hW : ContDiffOn ℝ 2 (fun y => IIIa.sepW ν m T y τ) U :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν m rOut P T hν hm hrO hP hT hS τ i)
  have hcont : ContinuousOn (fun y => ‖iteratedFDeriv ℝ j (fun y => IIIa.sepW ν m T y τ) y‖ₑ) U := by
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ j (fun y => IIIa.sepW ν m T y τ) U) U :=
      hW.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj) hU.uniqueDiffOn
    refine (h1.enorm).congr ?_
    intro y hy
    simp only
    rw [iteratedFDerivWithin_of_isOpen j hU hy]
  set G : Space → ℝ≥0∞ := U.piecewise
    (fun y => ‖iteratedFDeriv ℝ j (fun y => IIIa.sepW ν m T y τ) y‖ₑ) (fun _ => 0) with hGdef
  have hG : Measurable G :=
    ContinuousOn.measurable_piecewise hcont continuousOn_const hU.measurableSet
  have heq : IIIa.youngDerivNorm ν m T j rIn τ = fun y => if rIn ≤ ϱ y then G y else 0 := by
    funext y
    by_cases h : rIn ≤ ϱ y
    · have hy : y ∈ U := lt_of_lt_of_le hrr h
      have h' : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := h
      simp only [IIIa.youngDerivNorm, IIIa.wDerivNorm, hGdef, h, h', hy, ite_true,
        Set.piecewise_eq_of_mem]
    · have h' : ¬ rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := h
      simp only [IIIa.youngDerivNorm, h', ite_false, h]
  rw [heq]
  exact Measurable.ite (measurableSet_le measurable_const continuous_ϱ.measurable) hG
    measurable_const

/-- **(S2) Transfer to `X0 = W_mu - W_{mu+1}`** (source 4171-4174, 4192-4194). -/
theorem sepX0PhaseBound : SepX0PhaseBound := by
  classical
  intro σ₁ σ₂ hσ j hj
  set K : Set ℂ := ((fun x : ℝ => (x : ℂ)) '' Icc σ₁ σ₂) ∪
    ((fun x : ℝ => (x : ℂ) + 1) '' Icc σ₁ σ₂) with hKdef
  have hKc : IsCompact K :=
    (isCompact_Icc.image Complex.continuous_ofReal).union
      (isCompact_Icc.image (by fun_prop))
  have hKre : ∀ m ∈ K, -(1 / 4) < m.re := by
    rintro m (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · simp only [Complex.ofReal_re]
      linarith [hx.1]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
      linarith [hx.1]
  obtain ⟨C, hC0, hB⟩ := sepWPhaseSup K hKc hKre j
  refine ⟨‖reL‖ * (C + C), by positivity, ?_⟩
  intro ν μ rOut rIn P hν hμ hrO hrr hP hP1 T hT hS τ
  have hμre : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hm1 : (μ : ℂ) ∈ K := Or.inl ⟨μ, hμ, rfl⟩
  have hm2 : (μ : ℂ) + 1 ∈ K := Or.inr ⟨μ, hμ, rfl⟩
  have hm1re : -(1 / 4) < ((μ : ℂ)).re := by
    simp only [Complex.ofReal_re]
    exact hμre
  have hm2re : -(1 / 4) < ((μ : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hB1 := hB ν hν (μ : ℂ) hm1 rOut rIn P hrO hrr hP hP1 T hT τ
  have hB2 := hB ν hν ((μ : ℂ) + 1) hm2 rOut rIn P hrO hrr hP hP1 T hT τ
  have hF1 := measurable_youngDerivNorm ν (μ : ℂ) T j rOut rIn P τ hj hν hm1re hrO hrr hP hT hS
  have hF2 := measurable_youngDerivNorm ν ((μ : ℂ) + 1) T j rOut rIn P τ hj hν hm2re hrO hrr hP
    hT hS
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hpt : ∀ y : Space,
      (if rIn ≤ ϱ y then ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ else 0) ≤
        ENNReal.ofReal ‖reL‖ * (IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ y +
          IIIa.youngDerivNorm ν ((μ : ℂ) + 1) T j rIn τ y) := by
    intro y
    by_cases h : rIn ≤ ϱ y
    · have hy : y ∈ {y : Space | rOut < ϱ y} := lt_of_lt_of_le hrr h
      have hW1 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
        contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
          hm1re hrO hP hT hS τ i)
      have hW2 : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
          {y : Space | rOut < ϱ y} :=
        contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T
          hν hm2re hrO hP hT hS τ i)
      have key := iteratedFDeriv_reL_le hU hW1 hW2 hj hy
      have h' : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := h
      rw [if_pos h, sepX0_eq_reL]
      simp only [IIIa.youngDerivNorm, IIIa.wDerivNorm, h', ite_true]
      exact key
    · rw [if_neg h]
      exact zero_le
  have hMink : lqNorm (22 / 3)
      (fun y => IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ y +
        IIIa.youngDerivNorm ν ((μ : ℂ) + 1) T j rIn τ y) ≤
      lqNorm (22 / 3) (IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ) +
        lqNorm (22 / 3) (IIIa.youngDerivNorm ν ((μ : ℂ) + 1) T j rIn τ) := by
    unfold lqNorm
    exact ENNReal.lintegral_Lp_add_le hF1.aemeasurable hF2.aemeasurable (by norm_num)
  have ht : 0 ≤ C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11) :=
    mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  calc lqNorm (22 / 3)
        (fun y => if rIn ≤ ϱ y then ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ else 0)
      ≤ lqNorm (22 / 3) (fun y => ENNReal.ofReal ‖reL‖ * (IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ y +
          IIIa.youngDerivNorm ν ((μ : ℂ) + 1) T j rIn τ y)) :=
        lqNorm_mono (by norm_num) hpt
    _ = ENNReal.ofReal ‖reL‖ * lqNorm (22 / 3)
          (fun y => IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ y +
            IIIa.youngDerivNorm ν ((μ : ℂ) + 1) T j rIn τ y) :=
        lqNorm_const_mul (by norm_num) _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal ‖reL‖ * (lqNorm (22 / 3) (IIIa.youngDerivNorm ν (μ : ℂ) T j rIn τ) +
          lqNorm (22 / 3) (IIIa.youngDerivNorm ν ((μ : ℂ) + 1) T j rIn τ)) :=
        mul_le_mul_of_nonneg_left hMink zero_le
    _ ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) +
          ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) :=
        mul_le_mul_of_nonneg_left (add_le_add hB1 hB2) zero_le
    _ = ENNReal.ofReal (‖reL‖ * (C + C) * (rIn - rOut) ^ (-4 - (j : ℝ) + 9 / 11)) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
        rw [← add_mul, ← ENNReal.ofReal_add ht ht, ← mul_assoc, ← ENNReal.ofReal_mul
          (norm_nonneg _)]
        congr 2
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
