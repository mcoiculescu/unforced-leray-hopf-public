import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Lib.PhaseTrace.Comoving
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak-to-strong comoving derivative (helper of `PartII-b:S3/1/1/2/1/2`)

Source of record: `the November 2 reference manuscript`,
lines 2559-2562 ("the resulting $C_\tau W^{k,4}$ regularity and the projected equation give all
time derivatives").

`hasDerivAt_comoving_of_weak`: let `u, b ∈ Y_q` (`q < ∞`) with `T₀u = b` in distributions
(`HasPhaseOp driftT u b`), let `F` be a jointly continuous representative of `Re u`
(`IsContRep u F`) and let `H` be jointly continuous with `b = H` almost everywhere on
`ℝ × ℝ³`. Then along every comoving ray `t ↦ (τ + t, e^{-t/2} y)` the function `F` is
differentiable at `t = 0` with derivative `H τ y`.

Proof: the comoving pullback `t ↦ u(τ + t)(e^{-t/2} ·)` has weak time derivative
`t ↦ b(τ + t)(e^{-t/2} ·)` tested against `x ↦ ψ(x) e_i` (`PhaseTrace.hasWeakDerivTime_ell`);
continuity of the tested pullback of `F` gives the integrated identity
`∫ψ(F(τ+t, e^{-t/2}x) - F(τ, x))_i = ∫ψ ∫₀ᵗ H(τ+r, e^{-r/2}x)_i dr` (`HasWeakDerivTime.eqOn_rep`,
`rep_sub_rep`, Fubini), hence pointwise (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, continuity),
and the fundamental theorem of calculus at `r = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.CorrComovingSub

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace
  UnforcedLeray.BochnerTime UnforcedLeray.B0412

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The slices of the comoving pullback, as functions. -/
theorem coeFn_comoving_ae (f : Yq P q) (τ₀ t : ℝ) :
    (comoving f τ₀ t : Space → CVec3) =ᵐ[volume]
      fun x => rep f (τ₀ + t) (dilScale t • x) := by
  have h1 := coeFn_dil t (f ((τ₀ + t : ℝ) : AddCircle P))
  have h2 := (qmp_dilScale t).ae_eq_comp (rep_slice f (τ₀ + t)).symm
  exact h1.trans h2

/-- The real part of the separating functional with the `i`-th coordinate vector. -/
theorem re_integral_smul_dotL_single {g : Space → CVec3} (hg : LocallyIntegrable g volume)
    {ψ : Space → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (i : Fin 3) :
    (∫ x, ψ x • dotL (EuclideanSpace.single i (1 : ℂ)) (g x)).re =
      ∫ x, ψ x * (g x i).re := by
  have hint : Integrable (fun x => ψ x • g x) :=
    hg.integrable_smul_left_of_hasCompactSupport hψ hψc
  have hint' : Integrable (fun x => ψ x • dotL (EuclideanSpace.single i (1 : ℂ)) (g x)) := by
    refine ((dotL (EuclideanSpace.single i (1 : ℂ))).integrable_comp hint).congr
      (Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.map_smul_of_tower]
  have h := Complex.reCLM.integral_comp_comm hint'
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [dotL_apply]

/-- An almost-everywhere identity on `ℝ × ℝ³` holds, for almost every `t`, almost everywhere
along the comoving slice `x ↦ (τ₀ + t, e^{-t/2} x)`. -/
theorem ae_comoving_slice {E : Type*} {f g : ℝ → Space → E}
    (h : ∀ᵐ x : ℝ × Space ∂volume, f x.1 x.2 = g x.1 x.2) (τ₀ : ℝ) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ x : Space ∂volume,
      f (τ₀ + t) (dilScale t • x) = g (τ₀ + t) (dilScale t • x) := by
  have h1 : ∀ᵐ τ : ℝ ∂volume, ∀ᵐ y : Space ∂volume, f τ y = g τ y := by
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod (p := fun x : ℝ × Space => f x.1 x.2 = g x.1 x.2) h
  have h2 : ∀ᵐ t : ℝ ∂volume, ∀ᵐ y : Space ∂volume, f (τ₀ + t) y = g (τ₀ + t) y :=
    (measurePreserving_add_left (volume : Measure ℝ) τ₀).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with t ht
  exact (qmp_dilScale t).ae ht

/-- Continuity of `t ↦ ∫ ψ(x) Φ(t, x) dx` for compactly supported continuous `ψ`. -/
theorem continuous_integral_mul {ψ : Space → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {Φ : ℝ → Space → ℝ} (hΦ : Continuous (Function.uncurry Φ)) :
    Continuous fun t => ∫ x, ψ x * Φ t x := by
  have heq : (fun t => ∫ x, ψ x * Φ t x) = fun t => ∫ x in tsupport ψ, ψ x * Φ t x := by
    funext t
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [heq]
  have hc : Continuous (Function.uncurry fun t x => ψ x * Φ t x) :=
    (hψ.comp continuous_snd).mul hΦ
  exact continuous_parametric_integral_of_continuous hc hψc

/-- Integrability on `uIoc a b × ℝ³` of a continuous function supported in `ℝ × S`, `S`
compact. -/
theorem integrable_prod_uIoc {Φ : ℝ → Space → ℝ} (hΦ : Continuous (Function.uncurry Φ))
    {S : Set Space} (hS : IsCompact S) (hΦS : ∀ r x, x ∉ S → Φ r x = 0) (a b : ℝ) :
    Integrable (Function.uncurry Φ) ((volume.restrict (Set.uIoc a b)).prod volume) := by
  have hK : IsCompact (uIcc a b ×ˢ S) := isCompact_uIcc.prod hS
  have h1 : IntegrableOn (Function.uncurry Φ) (uIcc a b ×ˢ S)
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    hΦ.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (Function.uncurry Φ) (uIcc a b ×ˢ univ)
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    refine h1.of_forall_sdiff_eq_zero (measurableSet_uIcc.prod MeasurableSet.univ) ?_
    rintro ⟨r, x⟩ ⟨⟨hr, -⟩, hx⟩
    have hxS : x ∉ S := fun hxS => hx ⟨hr, hxS⟩
    exact hΦS r x hxS
  have h3 : IntegrableOn (Function.uncurry Φ) (Set.uIoc a b ×ˢ univ)
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    h2.mono_set (prod_mono uIoc_subset_uIcc subset_rfl)
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h3
  exact h3

/-- **Integrated comoving identity on `[-T, T]`.** If `T₀u = b` in distributions on `Y_q`,
`q < ∞`, `F` is a jointly continuous representative of `Re u`, and `b` agrees almost everywhere
with a jointly continuous real field `H`, then
`F(τ₀ + t, e^{-t/2}x) - F(τ₀, x) = ∫₀ᵗ H(τ₀ + r, e^{-r/2}x) dr` for `|t| ≤ T` and every `x`. -/
theorem integral_identity_Icc (hq : q ≠ ⊤) {u b : Yq P q} (hub : HasPhaseOp driftT u b)
    {F H : ℝ → SpatialField} (hF : IsContRep u F)
    (hH : Continuous (fun x : ℝ × Space => H x.1 x.2))
    (hbH : ∀ᵐ x : ℝ × Space ∂volume, rep b x.1 x.2 = realC (H x.1 x.2))
    (τ₀ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc (-T) T, ∀ x : Space,
      F (τ₀ + t) (dilScale t • x) - F (τ₀ + 0) (dilScale 0 • x) =
        ∫ r in (0 : ℝ)..t, H (τ₀ + r) (dilScale r • x) := by
  -- the comoving pullbacks of `F` and `H`
  set G : ℝ → Space → Space := fun t x => F (τ₀ + t) (dilScale t • x) with hG
  set K : ℝ → Space → Space := fun t x => H (τ₀ + t) (dilScale t • x) with hK
  have hray : Continuous (fun p : ℝ × Space => ((τ₀ + p.1, dilScale p.1 • p.2) : ℝ × Space)) :=
    (continuous_const.add continuous_fst).prodMk
      ((continuous_dilScale.comp continuous_fst).smul continuous_snd)
  have hGc : Continuous (Function.uncurry G) := hF.1.comp hray
  have hKc : Continuous (Function.uncurry K) := hH.comp hray
  have hGi : ∀ i : Fin 3, Continuous (Function.uncurry fun t x => G t x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hGc
  have hKi : ∀ i : Fin 3, Continuous (Function.uncurry fun t x => K t x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hKc
  have h0mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
  -- Step 1: the tested identity
  have hscalar : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ (i : Fin 3),
      ∀ t ∈ Icc (-T) T,
      (∫ x, ψ x * G t x i) - (∫ x, ψ x * G 0 x i) =
        ∫ r in (0 : ℝ)..t, ∫ x, ψ x * K r x i := by
    intro ψ hψ hψc i t ht
    obtain ⟨L, hL⟩ := exists_ell (q := q) hψ.continuous hψc (EuclideanSpace.single i (1 : ℂ))
    have hW := (hasWeakDerivTime_ell hq hub τ₀ (-T) T hψ hψc
      (EuclideanSpace.single i (1 : ℂ)) L hL).map Complex.reCLM
    have hcomp : ∀ (f : Yq P q) (t : ℝ), Complex.reCLM (L (comoving f τ₀ t)) =
        ∫ x, ψ x * ((rep f (τ₀ + t) (dilScale t • x)) i).re := by
      intro f t
      rw [Complex.reCLM_apply, hL, re_integral_smul_dotL_single
        ((Lp.memLp (comoving f τ₀ t)).locallyIntegrable Fact.out) hψ.continuous hψc i]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_comoving_ae f τ₀ t] with x hx
      rw [hx]
    have hu_ae : ∀ᵐ t : ℝ ∂volume,
        Complex.reCLM (L (comoving u τ₀ t)) = ∫ x, ψ x * G t x i := by
      have h0 := ae_comoving_slice (f := F) (g := fun τ y => reP (rep u τ y)) hF.2 τ₀
      filter_upwards [h0] with t ht
      rw [hcomp u t]
      refine integral_congr_ae ?_
      filter_upwards [ht] with x hx
      simp only [hG]
      rw [hx]
      simp [reP]
    have hb_ae : ∀ᵐ t : ℝ ∂volume,
        Complex.reCLM (L (comoving b τ₀ t)) = ∫ x, ψ x * K t x i := by
      have h0 := ae_comoving_slice (f := fun τ y => rep b τ y)
        (g := fun τ y => realC (H τ y)) hbH τ₀
      filter_upwards [h0] with t ht
      rw [hcomp b t]
      refine integral_congr_ae ?_
      filter_upwards [ht] with x hx
      simp only [hK]
      rw [hx, realC_apply]
      simp
    have hWgk : HasWeakDerivTime (-T) T (fun t => ∫ x, ψ x * G t x i)
        (fun r => ∫ x, ψ x * K r x i) :=
      hW.congr_ae (ae_restrict_of_ae hu_ae) (ae_restrict_of_ae hb_ae)
    have hgc : Continuous fun t => ∫ x, ψ x * G t x i :=
      continuous_integral_mul hψ.continuous hψc (hGi i)
    have hEq := hWgk.eqOn_rep (by linarith : -T < T) hgc.continuousOn
      Filter.EventuallyEq.rfl
    have e1 : (fun t => ∫ x, ψ x * G t x i) t = hWgk.rep t := hEq ht
    have e0 : (fun t => ∫ x, ψ x * G t x i) 0 = hWgk.rep 0 := hEq h0mem
    simp only at e1 e0
    rw [e1, e0]
    exact hWgk.rep_sub_rep h0mem ht
  -- Step 2: the pointwise integrated identity
  have hvec : ∀ t ∈ Icc (-T) T, ∀ x, G t x - G 0 x = ∫ r in (0 : ℝ)..t, K r x := by
    intro t ht
    set M : Space → Space := fun x => G t x - G 0 x - ∫ r in (0 : ℝ)..t, K r x with hM
    have hKx : ∀ x, Continuous fun r => K r x := fun x =>
      hKc.comp (continuous_id.prodMk continuous_const)
    have hMc : Continuous M := by
      have h1 : Continuous (G t) := hGc.comp (continuous_const.prodMk continuous_id)
      have h2 : Continuous (G 0) := hGc.comp (continuous_const.prodMk continuous_id)
      have h3 : Continuous (fun x => ∫ r in (0 : ℝ)..t, K r x) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun x r => K r x) (hKc.comp continuous_swap) continuous_const
      exact (h1.sub h2).sub h3
    have hae : ∀ᵐ x ∂(volume : Measure Space), M x = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hMc.locallyIntegrable
        fun ψ hψ hψc => ?_
      have hint : Integrable (fun x => ψ x • M x) :=
        (hψ.continuous.smul hMc).integrable_of_hasCompactSupport hψc.smul_right
      ext i
      have hcoord := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hint
      simp only [EuclideanSpace.proj, PiLp.proj_apply] at hcoord
      rw [← hcoord]
      simp only [PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
      have hMi : ∀ x, M x i = G t x i - G 0 x i - ∫ r in (0 : ℝ)..t, K r x i := by
        intro x
        have hcomm := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).intervalIntegral_comp_comm
          ((hKx x).intervalIntegrable (μ := volume) 0 t)
        simp only [EuclideanSpace.proj, PiLp.proj_apply] at hcomm
        simp only [hM, PiLp.sub_apply]
        rw [hcomm]
      simp_rw [hMi]
      have hiG : ∀ s : ℝ, Integrable (fun x => ψ x * G s x i) := fun s =>
        (hψ.continuous.mul ((hGi i).comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
          (hψc.mul_right)
      have hcI : Continuous fun x => ∫ r in (0 : ℝ)..t, K r x i :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun x r => K r x i) ((hKi i).comp continuous_swap) continuous_const
      have hiI : Integrable (fun x => ψ x * ∫ r in (0 : ℝ)..t, K r x i) :=
        (hψ.continuous.mul hcI).integrable_of_hasCompactSupport hψc.mul_right
      have hsplit : (fun x => ψ x * (G t x i - G 0 x i - ∫ r in (0 : ℝ)..t, K r x i)) =
          fun x => ψ x * G t x i - ψ x * G 0 x i - ψ x * ∫ r in (0 : ℝ)..t, K r x i := by
        funext x
        ring
      rw [hsplit, integral_sub (f := fun x => ψ x * G t x i - ψ x * G 0 x i)
        ((hiG t).sub (hiG 0)) hiI, integral_sub (hiG t) (hiG 0),
        hscalar ψ hψ hψc i t ht]
      have hswap : ∫ r in (0 : ℝ)..t, ∫ x, ψ x * K r x i =
          ∫ x, ∫ r in (0 : ℝ)..t, ψ x * K r x i := by
        refine intervalIntegral_integral_swap ?_
        refine integrable_prod_uIoc (Φ := fun r x => ψ x * K r x i)
          ((hψ.continuous.comp continuous_snd).mul (hKi i)) hψc ?_ 0 t
        intro r x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      rw [hswap, sub_eq_zero]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [intervalIntegral.integral_const_mul]
    have hM0 : M = fun _ => 0 :=
      (Continuous.ae_eq_iff_eq volume hMc continuous_const).mp hae
    intro x
    have := congrFun hM0 x
    simp only [hM] at this
    exact sub_eq_zero.mp this
  exact hvec

/-- **Integrated comoving identity.** Under the hypotheses of `integral_identity_Icc`,
`F(τ₀ + t, e^{-t/2}x) - F(τ₀, x) = ∫₀ᵗ H(τ₀ + r, e^{-r/2}x) dr` for all `t` and `x`. -/
theorem integral_identity_comoving_of_weak (hq : q ≠ ⊤) {u b : Yq P q}
    (hub : HasPhaseOp driftT u b) {F H : ℝ → SpatialField} (hF : IsContRep u F)
    (hH : Continuous (fun x : ℝ × Space => H x.1 x.2))
    (hbH : ∀ᵐ x : ℝ × Space ∂volume, rep b x.1 x.2 = realC (H x.1 x.2))
    (τ₀ t : ℝ) (x : Space) :
    F (τ₀ + t) (Real.exp (-t / 2) • x) - F τ₀ x =
      ∫ r in (0 : ℝ)..t, H (τ₀ + r) (Real.exp (-r / 2) • x) := by
  have h := integral_identity_Icc hq hub hF hH hbH τ₀ (T := |t| + 1) (by positivity) t
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩ x
  simpa only [dilScale, add_zero, neg_zero, zero_div, Real.exp_zero, one_smul] using h

/-- **Weak-to-strong comoving derivative.** Under the hypotheses of `integral_identity_Icc`,
`t ↦ F(τ₀ + t, e^{-t/2} y)` has derivative `H τ₀ y` at `t = 0`. -/
theorem hasDerivAt_comoving_of_weak (hq : q ≠ ⊤) {u b : Yq P q} (hub : HasPhaseOp driftT u b)
    {F H : ℝ → SpatialField} (hF : IsContRep u F)
    (hH : Continuous (fun x : ℝ × Space => H x.1 x.2))
    (hbH : ∀ᵐ x : ℝ × Space ∂volume, rep b x.1 x.2 = realC (H x.1 x.2))
    (τ₀ : ℝ) (y : Space) :
    HasDerivAt (fun t : ℝ => F (τ₀ + t) (Real.exp (-t / 2) • y)) (H τ₀ y) 0 := by
  have hK0 : Continuous fun r : ℝ => H (τ₀ + r) (Real.exp (-r / 2) • y) :=
    hH.comp ((continuous_const.add continuous_id).prodMk
      ((Real.continuous_exp.comp (continuous_neg.div_const 2)).smul continuous_const))
  have hderiv : HasDerivAt
      (fun t => F τ₀ y + ∫ r in (0 : ℝ)..t, H (τ₀ + r) (Real.exp (-r / 2) • y))
      (H (τ₀ + 0) (Real.exp (-0 / 2) • y)) 0 :=
    (intervalIntegral.integral_hasDerivAt_right (hK0.intervalIntegrable 0 0)
      (hK0.stronglyMeasurableAtFilter _ _) hK0.continuousAt).const_add _
  have hfun : (fun t : ℝ => F (τ₀ + t) (Real.exp (-t / 2) • y)) =
      fun t => F τ₀ y + ∫ r in (0 : ℝ)..t, H (τ₀ + r) (Real.exp (-r / 2) • y) := by
    funext t
    rw [← integral_identity_comoving_of_weak hq hub hF hH hbH τ₀ t y]
    abel
  rw [hfun]
  simpa using hderiv

end UnforcedLeray.Short.IIb.CorrComovingSub

end
