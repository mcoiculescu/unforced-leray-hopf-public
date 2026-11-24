import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.Diff.Common

/-!


Proves `DDiff` (`Sub/T22_1_10_1.lean`). For `τ ∈ [s,T]`, the Duhamel integral
`x ↦ ∫_s^τ e^{ν(τ-r)Δ} g(r)(x) dr` is differentiable with
`∂_i G(x) = ∫_s^τ (∂_i K_{ν(τ-r)}) * g(r)(x) dr`. The proof differentiates under the integral sign
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`): the pointwise derivative of
`e^{aΔ} g(r)` is `α • fst + β • snd` with `α, β` the derivative kernels (`heatGradFormula`), and
the majorant is `4 e^{ν(T-s)} M0 (1 + ν^{-1/2}(τ-r)^{-1/2})` from `heatWBounds`.
Source `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace DiffC

/-- The derivative of the scaled semigroup at `x`, at age `t`, as a functional on `ℝ × ℝ`. -/
def Dcl (ν τ : ℝ) (g : ℝ → Pl → ℝ) (x : Pl) (t : ℝ) : Pl →L[ℝ] ℝ :=
  heatSGd 0 (ν * (τ - t)) (g t) x • ContinuousLinearMap.fst ℝ ℝ ℝ +
    heatSGd 1 (ν * (τ - t)) (g t) x • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Evaluating the derivative at the coordinate direction `dir i` gives the partial kernel. -/
lemma Dcl_dir (ν τ : ℝ) (g : ℝ → Pl → ℝ) (x : Pl) (t : ℝ) (i : Fin 2) :
    Dcl ν τ g x t (B0579.dir i) = heatSGd i (ν * (τ - t)) (g t) x := by
  fin_cases i <;> simp [Dcl, B0579.dir]

/-- The fderiv of a plane function is the combination of its partials. -/
lemma fderiv_eq_pd (f : Pl → ℝ) (x : Pl) :
    fderiv ℝ f x = (B0579.pd 0 f x) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (B0579.pd 1 f x) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  ext v
  · simp [B0579.pd, B0579.dir]
  · simp [B0579.pd, B0579.dir]

/-- Pointwise bound on the derivative of the Duhamel integrand. -/
lemma Dcl_norm_le {ν s T τ t : ℝ} (hν : 0 < ν) (hτT : τ ≤ T) (hst : s ≤ t) (htτ : t < τ)
    {g : ℝ → Pl → ℝ} {b M0 : ℝ} (hbM : b ≤ M0) (hb0 : 0 ≤ b) (hg : WB b (g t)) (x : Pl) :
    ‖Dcl ν τ g x t‖ ≤ 4 * Real.exp (ν * (T - s)) * M0 +
      4 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ)) * (τ - t) ^ (-(1 / 2 : ℝ)) := by
  have h := norm_clm_le (heatSGd 0 (ν * (τ - t)) (g t) x) (heatSGd 1 (ν * (τ - t)) (g t) x)
  have h0 := heatSGd_bound_int hν hτT hst htτ hbM hb0 hg 0 x
  have h1 := heatSGd_bound_int hν hτT hst htτ hbM hb0 hg 1 x
  unfold Dcl
  linarith

/-- The Duhamel integrand as a function of `x`, for fixed `t`, has the derivative `Dcl`. -/
lemma hasFDerivAt_slice {ν s T τ t : ℝ} (hν : 0 < ν) (hsT : s ≤ T) {g : ℝ → Pl → ℝ}
    {b : ℝ → ℝ} (hgc : ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ))
    (hbc : ContinuousOn b (Icc s T)) (hb0 : ∀ r ∈ Icc s T, 0 ≤ b r)
    (hgb : ∀ r ∈ Icc s T, WB (b r) (g r)) (hτ : τ ∈ Icc s T) (ht : t ∈ Ioc s τ) (htτ : t < τ)
    (x : Pl) :
    HasFDerivAt (fun y => heatSG (ν * (τ - t)) (g t) y) (Dcl ν τ g x t) x := by
  have hts : t ∈ Icc s T := ⟨ht.1.le, ht.2.trans hτ.2⟩
  have ha : 0 < ν * (τ - t) := mul_pos hν (by linarith)
  obtain ⟨hdiff, hpd, _⟩ := heatGradFormula (b t) (g t) (cont_slice hgc hts)
    (hgb t hts) (ν * (τ - t)) ha
  have h := (hdiff x).hasFDerivAt
  rw [fderiv_eq_pd, hpd 0 x, hpd 1 x] at h
  exact h

end DiffC

open DiffC in
/-- **`PartII-b:T22/1/10/1/2`** Differentiation of the Duhamel integral (`DDiff`). -/
theorem dDiff : UnforcedLeray.Short.IIb.CylPDE.DDiff := by
  intro ν s T hν hsT g b hH τ hτ
  have hH' := hH
  obtain ⟨hgc, hbc, hb0, hgb⟩ := hH'
  obtain ⟨hDc, hDd⟩ := dParamCont ν s T hν hsT g b hH τ hτ
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := s) (b := T)).exists_bound_of_continuousOn hbc
  have hbM : ∀ t ∈ Icc s T, b t ≤ M0 := fun t ht =>
    (le_abs_self (b t)).trans (by simpa [Real.norm_eq_abs] using hM0 t ht)
  have hτs : s ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hne := ae_ne_point τ
  -- the bound majorant
  set bnd : ℝ → ℝ := fun t => 4 * Real.exp (ν * (T - s)) * M0 +
    4 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ)) * (τ - t) ^ (-(1 / 2 : ℝ)) with hbnd
  have hbnd_int : IntervalIntegrable bnd volume s τ :=
    affine_kernel_intInt _ _ τ s
  have hmeasD : ∀ x : Pl, AEStronglyMeasurable (fun t => Dcl ν τ g x t)
      (volume.restrict (Ioc s τ)) := fun x =>
    aesm_clm (aesm_slice (fun t y => heatSGd 0 (ν * (τ - t)) (g t) y) (hDd 0) x)
      (aesm_slice (fun t y => heatSGd 1 (ν * (τ - t)) (g t) y) (hDd 1) x)
  have hmeasF : ∀ x : Pl, AEStronglyMeasurable (fun t => heatSG (ν * (τ - t)) (g t) x)
      (volume.restrict (Ioc s τ)) := fun x =>
    aesm_slice (fun t y => heatSG (ν * (τ - t)) (g t) y) hDc x
  have hbd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc s τ → ∀ x ∈ (univ : Set Pl),
      ‖Dcl ν τ g x t‖ ≤ bnd t := by
    filter_upwards [hne] with t ht hmem x _
    rw [uIoc_of_le hτs] at hmem
    have htτ : t < τ := lt_of_le_of_ne hmem.2 ht
    exact Dcl_norm_le hν hτT hmem.1.le htτ (hbM t ⟨hmem.1.le, htτ.le.trans hτT⟩)
      (hb0 t ⟨hmem.1.le, htτ.le.trans hτT⟩) (hgb t ⟨hmem.1.le, htτ.le.trans hτT⟩) x
  have hint : ∀ x : Pl, IntervalIntegrable (fun t => Dcl ν τ g x t) volume s τ := by
    intro x
    refine IntervalIntegrable.mono_fun' hbnd_int ?_ ?_
    · rw [uIoc_of_le hτs]
      exact hmeasD x
    · rw [uIoc_of_le hτs]
      refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards [hbd] with t ht hmem
      exact ht (by rw [uIoc_of_le hτs]; exact hmem) x (mem_univ _)
  have hFint : ∀ x : Pl, IntervalIntegrable (fun t => heatSG (ν * (τ - t)) (g t) x) volume s τ := by
    intro x
    refine intInt_of_bdd (F := fun t => heatSG (ν * (τ - t)) (g t) x)
      (K := 2 * Real.exp (ν * (T - s)) * M0) hτs (hmeasF x) ?_
    intro t ht
    have hts : t ∈ Icc s T := ⟨ht.1.le, ht.2.trans hτT⟩
    exact heatSG_bound_aux hν hτT ht.1.le ht.2 (hbM t hts) (hb0 t hts) (hgb t hts) x
  have hderiv : ∀ x : Pl, HasFDerivAt (fun y : Pl => ∫ t in s..τ, heatSG (ν * (τ - t)) (g t) y)
      (∫ t in s..τ, Dcl ν τ g x t) x := by
    intro x
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y t => heatSG (ν * (τ - t)) (g t) y)
      (F' := fun y t => Dcl ν τ g y t) (bound := bnd) univ_mem ?_ (hFint x) ?_ hbd hbnd_int ?_
    · exact Filter.Eventually.of_forall (fun y => by
        rw [uIoc_of_le hτs]; exact hmeasF y)
    · rw [uIoc_of_le hτs]; exact hmeasD x
    · filter_upwards [hne] with t ht hmem y _
      rw [uIoc_of_le hτs] at hmem
      exact hasFDerivAt_slice hν hsT hgc hbc hb0 hgb hτ hmem (lt_of_le_of_ne hmem.2 ht) y
  have hfd : ∀ x : Pl, fderiv ℝ (duhamelConv ν s g τ) x = ∫ t in s..τ, Dcl ν τ g x t :=
    fun x => (hderiv x).fderiv
  refine ⟨fun x => (hderiv x).differentiableAt, fun i x => ?_⟩
  show fderiv ℝ (duhamelConv ν s g τ) x (B0579.dir i) = _
  rw [hfd x, ContinuousLinearMap.intervalIntegral_apply (hint x)]
  simp only [Dcl_dir]

end UnforcedLeray.Short.IIb.CylPDE
