import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs

/-!
# Part III-a, `PartIII-a:T21/2/2/2/4`: the rescaled train velocity is regular, periodic and
divergence free (SP 2861-2873, 2954-2955).

For `r ≥ 0`, `a = clockA ν r ≥ 1`, `s = √a`, `k = a^{3/2}`, the field
`movingTrainV tr r y = k · v_r(s · y)` is `C^∞`, `cellLen c a`-periodic in `y.1` (since
`s (y.1 + c/s) = s y.1 + c`), and `div_y (k v_r(s ·)) = k s (div v_r)(s ·) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- `∂_j` of a scaled function: `∂_j [k f(s·)] (y) = k s (∂_j f)(s y)`. -/
theorem pd_comp_smul_E0 (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (s k : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) :
    B0579.pd j (fun x => k * f (s • x)) y = k * s * B0579.pd j f (s • y) := by
  have hL : HasFDerivAt (fun x : ℝ × ℝ => s • x) (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul s
  have hc : HasFDerivAt (fun x : ℝ × ℝ => f (s • x))
      ((fderiv ℝ f (s • y)).comp (s • ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hf (s • y)).hasFDerivAt.comp y hL
  unfold B0579.pd
  rw [(hc.const_mul k).fderiv]
  simp [ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  ring

/-- Partial derivative in `q` equals `pd 0` for differentiable functions. -/
theorem partialQ_eq_pd0_E0 (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ f z = B0579.pd 0 f z := by
  unfold UnforcedLeray.Cyl.partialQ B0579.pd
  have h1 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id' z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h2 : HasDerivAt (fun q : ℝ => f (q, z.2)) ((fderiv ℝ f z) ((1 : ℝ), (0 : ℝ))) z.1 :=
    (hf z).hasFDerivAt.comp_hasDerivAt z.1 h1
  rw [h2.deriv]
  simp [B0579.dir]

/-- Partial derivative in `η` equals `pd 1` for differentiable functions. -/
theorem partialEta_eq_pd1_E0 (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta f z = B0579.pd 1 f z := by
  unfold UnforcedLeray.Cyl.partialEta B0579.pd
  have h1 : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id' z.2)
  have h2 : HasDerivAt (fun η : ℝ => f (z.1, η)) ((fderiv ℝ f z) ((0 : ℝ), (1 : ℝ))) z.2 :=
    (hf z).hasFDerivAt.comp_hasDerivAt z.2 h1
  rw [h2.deriv]
  simp [B0579.dir]

theorem movingTrainReg : UnforcedLeray.Short.IIIa.E0.MovingTrainReg := by
  intro ν c hν hc tr r hr
  have ha : 0 < clockA ν r := by
    unfold clockA
    nlinarith
  have hs : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.mpr ha
  -- smoothness of the slice `z ↦ tr.v r z`
  have hslice : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => tr.v r z) univ :=
    tr.isTrain.smooth_v.comp ((contDiffOn_const (c := r)).prodMk contDiffOn_id)
      (fun z _ => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × ℝ × ℝ) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
  have hS : ContDiff ℝ ∞ (fun z : ℝ × ℝ => tr.v r z) := contDiffOn_univ.1 hslice
  have hproj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun f : Fin 2 → ℝ => f j) := fun j => by fun_prop
  have hcoordS : ∀ j : Fin 2, ContDiff ℝ ∞ (fun z : ℝ × ℝ => tr.v r z j) := fun j =>
    ((hproj j).comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (n := ∞))).comp hS
  have hdiff : ∀ j : Fin 2, Differentiable ℝ (fun z : ℝ × ℝ => tr.v r z j) := fun j =>
    (hcoordS j).differentiable (by simp)
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    have hL : ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
        ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ)) := by
      fun_prop
    have hcoord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
        (tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) j) := fun j =>
      (hcoordS j).comp hL
    have hfin : ContDiff ℝ ∞ (movingTrainV tr r) := by
      refine contDiff_pi.2 fun j => ?_
      exact contDiff_const.mul (hcoord j)
    exact hfin.of_le (mod_cast le_top)
  · -- `cellLen c a`-periodicity in `y.1`
    intro y
    have hL' : Real.sqrt (clockA ν r) * (y.1 + cellLen c (clockA ν r))
        = Real.sqrt (clockA ν r) * y.1 + c := by
      unfold cellLen
      have hs' : Real.sqrt (clockA ν r) ≠ 0 := hs.ne'
      field_simp
    have key : tr.v r (Real.sqrt (clockA ν r) * y.1 + c, Real.sqrt (clockA ν r) * y.2)
        = tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
      tr.isTrain.periodic_v r hr (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)
    funext j
    simp only [movingTrainV]
    rw [hL', key]
  · -- divergence free
    intro y
    have e0 : (fun x : ℝ × ℝ => movingTrainV tr r x 0) =
        fun x => clockA ν r ^ (3 / 2 : ℝ) * (fun z : ℝ × ℝ => tr.v r z 0) (Real.sqrt (clockA ν r) • x) := by
      funext x
      rfl
    have e1 : (fun x : ℝ × ℝ => movingTrainV tr r x 1) =
        fun x => clockA ν r ^ (3 / 2 : ℝ) * (fun z : ℝ × ℝ => tr.v r z 1) (Real.sqrt (clockA ν r) • x) := by
      funext x
      rfl
    rw [e0, e1, pd_comp_smul_E0 _ (hdiff 0) _ _ 0 y, pd_comp_smul_E0 _ (hdiff 1) _ _ 1 y]
    have hdiv := tr.isTrain.solenoidal r hr (Real.sqrt (clockA ν r) • y)
    unfold UnforcedLeray.Cyl.divergence at hdiv
    rw [partialQ_eq_pd0_E0 _ (hdiff 0), partialEta_eq_pd1_E0 _ (hdiff 1)] at hdiv
    linear_combination (clockA ν r ^ (3 / 2 : ℝ) * Real.sqrt (clockA ν r)) * hdiv

end UnforcedLeray.Short.IIIa.E0
