import UnforcedLeray.Lib.PhaseTrace.ChartTest
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2

/-!
# Global comoving chart for phase tests (helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

The comoving chart `(s, x) ↦ (s, e^{-s/2} x)` straightens the rays of `T₀ = ∂_τ - ½ y·∇`.
For a test `k(s, x)` in chart coordinates, `chartLift k (τ, y) = e^{3τ/2} k(τ, e^{τ/2} y)`; then
* `driftT_chartLift`: `T₀ᵗ (chartLift k) = chartLift (-∂_s k)`;
* `integral_chartLift`: `∫ chartLift k (s, y) · u(y) dy = ∫ k(s, x) · u(e^{-s/2} x) dx`;
* `chartLift_chartPull`: every test is a chart lift;
* `sum_dy_chartLift`: the spatial divergence of `chartLift k` is `e^{2τ}` times that of `k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete

/-- The chart lift `K(τ, y) = e^{3τ/2} k(τ, e^{τ/2} y)`. -/
def chartLift (k : ℝ × Space → CVec3) (p : ℝ × Space) : CVec3 :=
  Real.exp (3 * p.1 / 2) • k (p.1, Real.exp (p.1 / 2) • p.2)

/-- The chart pull `k(s, x) = e^{-3s/2} K(s, e^{-s/2} x)`. -/
def chartPull (K : ℝ × Space → CVec3) (p : ℝ × Space) : CVec3 :=
  Real.exp (-(3 * p.1 / 2)) • K (p.1, dilScale p.1 • p.2)

theorem dilScale_smul_exp_half_smul (s : ℝ) (x : Space) :
    dilScale s • Real.exp (s / 2) • x = x := by
  rw [smul_smul, dilScale, ← Real.exp_add]
  have : -s / 2 + s / 2 = 0 := by ring
  rw [this, Real.exp_zero, one_smul]

theorem exp_half_smul_dilScale_smul (s : ℝ) (x : Space) :
    Real.exp (s / 2) • dilScale s • x = x := by
  rw [smul_smul, dilScale, ← Real.exp_add]
  have : s / 2 + -s / 2 = 0 := by ring
  rw [this, Real.exp_zero, one_smul]

theorem dilScale_mul_exp_half (s : ℝ) : dilScale s * Real.exp (s / 2) = 1 := by
  rw [dilScale, ← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]

theorem chartLift_chartPull (K : ℝ × Space → CVec3) : chartLift (chartPull K) = K := by
  funext p
  simp only [chartLift, chartPull, smul_smul, dilScale_mul_exp_half, one_smul]
  rw [← Real.exp_add]
  have : 3 * p.1 / 2 + -(3 * p.1 / 2) = 0 := by ring
  rw [this, Real.exp_zero, one_smul]

/-! ## Smoothness and supports -/

theorem contDiff_mLift : ContDiff ℝ ∞ (fun p : ℝ × Space => (p.1, Real.exp (p.1 / 2) • p.2)) :=
  contDiff_fst.prodMk ((Real.contDiff_exp.comp (contDiff_fst.div_const 2)).smul contDiff_snd)

theorem contDiff_mPull : ContDiff ℝ ∞ (fun p : ℝ × Space => (p.1, dilScale p.1 • p.2)) := by
  unfold dilScale
  exact contDiff_fst.prodMk ((Real.contDiff_exp.comp (contDiff_fst.neg.div_const 2)).smul
    contDiff_snd)

theorem contDiff_chartLift {k : ℝ × Space → CVec3} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (chartLift k) :=
  (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).div_const 2)).smul
    (hk.comp contDiff_mLift)

theorem contDiff_chartPull {K : ℝ × Space → CVec3} (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (chartPull K) :=
  (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).div_const 2).neg).smul
    (hK.comp contDiff_mPull)

theorem hasCompactSupport_chartLift {k : ℝ × Space → CVec3} (hk : HasCompactSupport k) :
    HasCompactSupport (chartLift k) := by
  refine HasCompactSupport.intro (K := (fun p : ℝ × Space => (p.1, dilScale p.1 • p.2)) ''
    tsupport k) (hk.image contDiff_mPull.continuous) fun p hp => ?_
  have hz : k (p.1, Real.exp (p.1 / 2) • p.2) = 0 := by
    by_contra hne
    apply hp
    refine ⟨(p.1, Real.exp (p.1 / 2) • p.2), subset_tsupport _ hne, ?_⟩
    simp only [dilScale_smul_exp_half_smul]
  simp [chartLift, hz]

theorem hasCompactSupport_chartPull {K : ℝ × Space → CVec3} (hK : HasCompactSupport K) :
    HasCompactSupport (chartPull K) := by
  refine HasCompactSupport.intro (K := (fun p : ℝ × Space => (p.1, Real.exp (p.1 / 2) • p.2)) ''
    tsupport K) (hK.image contDiff_mLift.continuous) fun p hp => ?_
  have hz : K (p.1, dilScale p.1 • p.2) = 0 := by
    by_contra hne
    apply hp
    refine ⟨(p.1, dilScale p.1 • p.2), subset_tsupport _ hne, ?_⟩
    simp only [exp_half_smul_dilScale_smul]
  simp [chartPull, hz]

/-- A smooth compactly supported field is a phase test of period `0`. -/
theorem isPhaseTest_zero_of_compact {K : ℝ × Space → CVec3} (hK : ContDiff ℝ ∞ K)
    (hKc : HasCompactSupport K) : IsPhaseTest 0 K where
  smooth := hK
  periodic τ y := by simp
  bounded_support := by
    obtain ⟨R, -, hR⟩ := exists_bound_of_hasCompactSupport hKc
    exact ⟨R, fun τ y hy => hR (τ, y) (lt_of_lt_of_le hy (norm_snd_le (τ, y)))⟩

/-- A compactly supported field has bounded phase support. -/
theorem exists_timeSupp_of_compact {K : ℝ × Space → CVec3} (hKc : HasCompactSupport K) :
    ∃ R : ℝ, 0 ≤ R ∧ TimeSupp (-R) R K := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hKc
  refine ⟨R, hR0, fun τ y hτ => hR (τ, y) ?_⟩
  have h1 : R < |τ| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hτ
    rcases hτ with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  exact lt_of_lt_of_le h1 (by simpa using norm_fst_le (τ, y))

/-! ## Calculus -/

/-- A directional derivative read off from the derivative along the line `s ↦ p + s v`. -/
theorem fderiv_apply_of_hasDerivAt' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × Space → F} {p v : ℝ × Space} (hg : DifferentiableAt ℝ g p) {D : F}
    (h : HasDerivAt (fun s : ℝ => g (p + s • v)) D 0) : fderiv ℝ g p v = D := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add p
  have h2 := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  rw [one_smul] at h2
  exact h2.unique h

theorem fderiv_chartLift_time {k : ℝ × Space → CVec3} (hk : ContDiff ℝ ∞ k) (p : ℝ × Space) :
    fderiv ℝ (chartLift k) p (1, 0) =
      Real.exp (3 * p.1 / 2) • fderiv ℝ k (p.1, Real.exp (p.1 / 2) • p.2)
          (1, (Real.exp (p.1 / 2) * (1 / 2)) • p.2) +
        (Real.exp (3 * p.1 / 2) * (3 * 1 / 2)) • k (p.1, Real.exp (p.1 / 2) • p.2) := by
  refine fderiv_apply_of_hasDerivAt' ((contDiff_chartLift hk).differentiable (by simp) p) ?_
  have hc : HasDerivAt (fun s : ℝ => Real.exp (3 * (p.1 + s) / 2))
      (Real.exp (3 * (p.1 + 0) / 2) * (3 * 1 / 2)) 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).const_add p.1).const_mul 3).div_const 2).exp
  have hγ : HasDerivAt (fun s : ℝ => ((p.1 + s, Real.exp ((p.1 + s) / 2) • p.2) : ℝ × Space))
      ((1 : ℝ), (Real.exp ((p.1 + 0) / 2) * (1 / 2)) • p.2) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add p.1).prodMk
      ((((hasDerivAt_id' (0 : ℝ)).const_add p.1).div_const 2).exp.smul_const p.2)
  have hk' := (hk.differentiable (by simp) (p.1, Real.exp (p.1 / 2) • p.2)).hasFDerivAt
  have hkγ := hk'.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hprod := hc.smul hkγ
  have hval : (k ∘ fun s : ℝ => ((p.1 + s, Real.exp ((p.1 + s) / 2) • p.2) : ℝ × Space)) 0 =
      k (p.1, Real.exp (p.1 / 2) • p.2) := by simp
  rw [hval] at hprod
  simp only [add_zero] at hprod
  refine hprod.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [chartLift, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
    smul_zero, add_zero]
  rfl

theorem fderiv_chartLift_space {k : ℝ × Space → CVec3} (hk : ContDiff ℝ ∞ k) (p : ℝ × Space)
    (w : Space) :
    fderiv ℝ (chartLift k) p (0, w) =
      Real.exp (3 * p.1 / 2) • fderiv ℝ k (p.1, Real.exp (p.1 / 2) • p.2)
        (0, Real.exp (p.1 / 2) • w) := by
  refine fderiv_apply_of_hasDerivAt' ((contDiff_chartLift hk).differentiable (by simp) p) ?_
  have hγ : HasDerivAt (fun s : ℝ => ((p.1, Real.exp (p.1 / 2) • (p.2 + s • w)) : ℝ × Space))
      ((0 : ℝ), Real.exp (p.1 / 2) • ((1 : ℝ) • w)) 0 :=
    (hasDerivAt_const (0 : ℝ) p.1).prodMk
      ((((hasDerivAt_id' (0 : ℝ)).smul_const w).const_add p.2).const_smul (Real.exp (p.1 / 2)))
  have hk' := (hk.differentiable (by simp) (p.1, Real.exp (p.1 / 2) • p.2)).hasFDerivAt
  have hkγ := hk'.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hprod := hkγ.const_smul (Real.exp (3 * p.1 / 2))
  rw [one_smul] at hprod
  refine hprod.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [chartLift, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_zero, add_zero,
    Function.comp_apply, Pi.smul_apply]

/-- **Transpose drift of a chart lift.** `T₀ᵗ (chartLift k) = chartLift (-∂_s k)`. -/
theorem driftT_chartLift {k : ℝ × Space → CVec3} (hk : ContDiff ℝ ∞ k) :
    driftT (chartLift k) = chartLift (fun q => -dτ k q) := by
  funext p
  set e : ℝ := Real.exp (p.1 / 2) with he
  set E : ℝ := Real.exp (3 * p.1 / 2) with hE
  set L := fderiv ℝ k (p.1, e • p.2) with hL
  have ht := fderiv_chartLift_time hk p
  have hsp : ∀ j : Fin 3, fderiv ℝ (chartLift k) p (0, coordinateVector j) =
      E • L (0, e • coordinateVector j) := fun j => fderiv_chartLift_space hk p _
  have hrad : ∑ j : Fin 3, p.2 j • (E • L (0, e • coordinateVector j)) =
      E • L (0, e • p.2) := by
    have hv : ((0 : ℝ), e • p.2) = ∑ j : Fin 3, p.2 j • ((0 : ℝ), e • coordinateVector j) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        conv_lhs => rw [← sum_smul_coordinateVector p.2]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm]
    rw [hv, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_comm]
  have hsplit : L (1, (e * (1 / 2)) • p.2) = L (1, 0) + (1 / 2 : ℝ) • L (0, e • p.2) := by
    rw [← map_smul, ← map_add]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simp [smul_smul, mul_comm]
  simp only [driftT, dτ, radialT, dy, ht, hsp, chartLift]
  rw [hrad, hsplit, ← he, ← hE]
  simp only [smul_add, smul_neg, smul_smul]
  module

/-! ## Change of variables -/

theorem abs_inv_dilScale_pow (s : ℝ) :
    |(dilScale s ^ Module.finrank ℝ Space)⁻¹| = Real.exp (3 * s / 2) := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hdim, dilScale, abs_of_pos (by positivity), ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  push_cast
  ring

/-- **Slice change of variables.** `∫ chartLift k (s, y) · u(y) dy = ∫ k(s, x) · u(e^{-s/2}x) dx`. -/
theorem integral_chartLift (k : ℝ × Space → CVec3) (s : ℝ) (u : Space → CVec3) :
    ∫ y, dotL (chartLift k (s, y)) (u y) = ∫ x, dotL (k (s, x)) (u (dilScale s • x)) := by
  have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space)
    (fun y => dotL (chartLift k (s, y)) (u y)) (dilScale s)
  rw [abs_inv_dilScale_pow] at h
  have hfun : (fun x : Space => dotL (chartLift k (s, dilScale s • x)) (u (dilScale s • x))) =
      fun x => Real.exp (3 * s / 2) • dotL (k (s, x)) (u (dilScale s • x)) := by
    funext x
    simp only [chartLift, exp_half_smul_dilScale_smul]
    rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply]
  rw [hfun, integral_smul] at h
  exact (smul_right_injective ℂ (Real.exp_pos (3 * s / 2)).ne' h).symm

/-! ## Divergence -/

theorem sum_dy_chartLift {k : ℝ × Space → CVec3} (hk : ContDiff ℝ ∞ k) (p : ℝ × Space) :
    ∑ j : Fin 3, dy j (chartLift k) p j =
      (Real.exp (3 * p.1 / 2) * Real.exp (p.1 / 2)) •
        ∑ j : Fin 3, dy j k (p.1, Real.exp (p.1 / 2) • p.2) j := by
  have h : ∀ j : Fin 3, dy j (chartLift k) p =
      (Real.exp (3 * p.1 / 2) * Real.exp (p.1 / 2)) • dy j k (p.1, Real.exp (p.1 / 2) • p.2) := by
    intro j
    simp only [dy]
    rw [fderiv_chartLift_space hk p]
    have hv : ((0 : ℝ), Real.exp (p.1 / 2) • coordinateVector j) =
        Real.exp (p.1 / 2) • ((0 : ℝ), coordinateVector j) := by simp
    rw [hv, map_smul, smul_smul]
  simp only [h, PiLp.smul_apply, Finset.smul_sum]

/-! ## Product tests `k(s, x) = φ(s) Ψ(x)` -/

/-- The product test `(s, x) ↦ φ(s) Ψ(x)`. -/
def prodTestV (φ : ℝ → ℝ) (Ψ : Space → CVec3) (q : ℝ × Space) : CVec3 := φ q.1 • Ψ q.2

theorem contDiff_prodTestV {φ : ℝ → ℝ} {Ψ : Space → CVec3} (hφ : ContDiff ℝ ∞ φ)
    (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (prodTestV φ Ψ) :=
  (hφ.comp contDiff_fst).smul (hΨ.comp contDiff_snd)

theorem hasCompactSupport_prodTestV {φ : ℝ → ℝ} {Ψ : Space → CVec3} (hφ : HasCompactSupport φ)
    (hΨ : HasCompactSupport Ψ) : HasCompactSupport (prodTestV φ Ψ) := by
  refine HasCompactSupport.intro (hφ.isCompact.prod hΨ.isCompact) fun q hq => ?_
  rw [mem_prod, not_and_or] at hq
  rcases hq with h | h
  · simp [prodTestV, image_eq_zero_of_notMem_tsupport h]
  · simp [prodTestV, image_eq_zero_of_notMem_tsupport h]

theorem dτ_prodTestV {φ : ℝ → ℝ} {Ψ : Space → CVec3} (hφ : ContDiff ℝ ∞ φ)
    (hΨ : ContDiff ℝ ∞ Ψ) (q : ℝ × Space) :
    dτ (prodTestV φ Ψ) q = deriv φ q.1 • Ψ q.2 := by
  refine fderiv_apply_of_hasDerivAt' ((contDiff_prodTestV hφ hΨ).differentiable (by simp) q) ?_
  have h1 : HasDerivAt (fun s : ℝ => φ (q.1 + s)) (deriv φ (q.1 + 0)) 0 :=
    ((hφ.differentiable (by simp)) (q.1 + 0)).hasDerivAt.comp_const_add q.1 0
  simp only [add_zero] at h1
  have h2 := h1.smul_const (Ψ q.2)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp [prodTestV]

theorem dy_prodTestV {φ : ℝ → ℝ} {Ψ : Space → CVec3} (hφ : ContDiff ℝ ∞ φ)
    (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3) (q : ℝ × Space) :
    dy j (prodTestV φ Ψ) q = φ q.1 • fderiv ℝ Ψ q.2 (coordinateVector j) := by
  refine fderiv_apply_of_hasDerivAt' ((contDiff_prodTestV hφ hΨ).differentiable (by simp) q) ?_
  have hl : HasDerivAt (fun s : ℝ => q.2 + s • coordinateVector j) ((1 : ℝ) • coordinateVector j)
      0 := ((hasDerivAt_id' (0 : ℝ)).smul_const _).const_add q.2
  have h1 := ((hΨ.differentiable (by simp)) q.2).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl
    (by simp)
  rw [one_smul] at h1
  have h2 := h1.const_smul (φ q.1)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp [prodTestV]

/-- The chart lift of `φ ⊗ Ψ` for a spatial solenoidal `Ψ` is spatially solenoidal. -/
theorem sum_dy_chartLift_prodTestV {φ : ℝ → ℝ} {Ψ : Space → CVec3} (hφ : ContDiff ℝ ∞ φ)
    (hΨ : SpatialSolTest Ψ) (p : ℝ × Space) :
    ∑ j : Fin 3, dy j (chartLift (prodTestV φ Ψ)) p j = 0 := by
  rw [sum_dy_chartLift (contDiff_prodTestV hφ hΨ.1) p]
  simp only [dy_prodTestV hφ hΨ.1]
  have h0 := hΨ.2.2 (Real.exp (p.1 / 2) • p.2)
  have : ∑ j : Fin 3, (φ p.1 • fderiv ℝ Ψ (Real.exp (p.1 / 2) • p.2) (coordinateVector j)) j =
      φ p.1 • ∑ j : Fin 3, fderiv ℝ Ψ (Real.exp (p.1 / 2) • p.2)
        (EuclideanSpace.single j (1 : ℝ)) j := by
    simp only [PiLp.smul_apply, Finset.smul_sum]
    rfl
  rw [this, h0, smul_zero, smul_zero]

end UnforcedLeray.Short.IIb.BaseRepSub

end
