import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3

/-!
# `kf3HeatDiv` (source 3617-3618): integrate the tensor divergence by parts

For `x` and `θ > 0`, with `G = heatG θ` smooth, and `M(·, τ)` smooth with compact support,
`∫ G(y) (div M)_i(x - y, τ) dy = ∫ Σ_k ∂_kG(x - z) M_{ik}(z, τ) dz`.
Route: substitute `y = x - z` (`integral_sub_left_eq_self`), split `div M` into its `j`-summands,
and integrate each by parts in `z` (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), using
`∂_{z_j}[G(x - z)] = -(∂_jG)(x - z)`.  All integrands are continuous with compact support.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Compact support of a single entry `x ↦ M(x, τ)_{ij}` of a smooth outer tensor. -/
theorem kf3_entry_cs {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hM : IsOuterTest P M)
    (τ : ℝ) (i j : Fin 3) : HasCompactSupport (fun x : Space => M (x, τ) i j) := by
  obtain ⟨r, hr⟩ := hM.bounded
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) r) (fun x hx => ?_)
  by_contra hne
  have hM0 : M (x, τ) ≠ 0 := fun h => hne (by simp [h])
  have h1 := hr (x, τ) hM0
  exact hx (by simpa using h1)

/-- Smoothness of the heat kernel for positive time. -/
theorem kf3_heatG_contDiff {θ : ℝ} :
    ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.heatG θ) := by
  unfold UnforcedLeray.Short.IIIa.heatG
  apply contDiff_const.mul
  apply Real.contDiff_exp.comp
  apply ContDiff.div_const
  exact (contDiff_norm_sq ℝ).neg

/-- Integrability of a continuous function times a continuous compactly supported one. -/
theorem kf3_integrable_mul_cs {F K : Space → ℝ} (hF : Continuous F) (hK : Continuous K)
    (hKc : HasCompactSupport K) : Integrable (fun z => F z * K z) := by
  have hc : HasCompactSupport (fun z => F z * K z) := hKc.mul_left
  exact (hF.mul hK).integrable_of_hasCompactSupport hc

theorem kf3_cs_sub {F : Space → ℝ} (hF : HasCompactSupport F) (x : Space) :
    HasCompactSupport (fun y : Space => F (x - y)) :=
  hF.comp_homeomorph (Homeomorph.subLeft x)

set_option maxHeartbeats 1600000 in
theorem kf3HeatDiv : KF3HeatDiv := by
  intro P M hM τ x θ hθ i
  set G := UnforcedLeray.Short.IIIa.heatG θ with hGdef
  have hGs : ContDiff ℝ ∞ G := kf3_heatG_contDiff
  have hGc : Continuous G := hGs.continuous
  have hGd : Continuous (fun z => fderiv ℝ G z) := hGs.continuous_fderiv (by simp)
  -- the `j`-th entry as a function of `z`
  set g : Fin 3 → Space → ℝ := fun j z => M (z, τ) i j with hgdef
  have hgc : ∀ j, Continuous (g j) := fun j =>
    ((hM.smooth i j).comp (contDiff_id.prodMk contDiff_const)).continuous
  have hgcs : ∀ j, HasCompactSupport (g j) := fun j => kf3_entry_cs hM τ i j
  have hgs : ∀ j, ContDiff ℝ ∞ (g j) := fun j =>
    (hM.smooth i j).comp (contDiff_id.prodMk contDiff_const)
  -- the divergence in the `z`-variable
  have hcd : ∀ z : Space, cartDiv M (z, τ) i = ∑ j : Fin 3,
      fderiv ℝ (g j) z (UnforcedLeray.coordinateVector j) := by
    intro z
    simp [cartDiv, hgdef]
  -- the reflected factor
  set f : Space → ℝ := fun z => G (x - z) with hfdef
  have hfs : ContDiff ℝ ∞ f := hGs.comp (contDiff_const.sub contDiff_id)
  have hfc : Continuous f := hfs.continuous
  have hfderiv : ∀ (z : Space) (v : Space), fderiv ℝ f z v = -fderiv ℝ G (x - z) v := by
    intro z v
    have h1 : HasFDerivAt (fun z : Space => x - z) (-(ContinuousLinearMap.id ℝ Space)) z :=
      (hasFDerivAt_id z).const_sub x
    have h2 : HasFDerivAt f ((fderiv ℝ G (x - z)).comp (-(ContinuousLinearMap.id ℝ Space))) z :=
      HasFDerivAt.comp z ((hGs.differentiable (by simp)) (x - z)).hasFDerivAt h1
    rw [h2.fderiv]
    simp
  -- continuity of the directional derivatives
  have hfdc : ∀ v : Space, Continuous (fun z => fderiv ℝ f z v) := fun v =>
    (hfs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgdc : ∀ j, Continuous (fun z => fderiv ℝ (g j) z (UnforcedLeray.coordinateVector j)) :=
    fun j => ((hgs j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hgdcs : ∀ j, HasCompactSupport
      (fun z => fderiv ℝ (g j) z (UnforcedLeray.coordinateVector j)) :=
    fun j => HasCompactSupport.fderiv_apply ℝ (hgcs j) (UnforcedLeray.coordinateVector j)
  -- (1) the left integrand after the substitution: a compactly supported continuous function
  have hDz : ∀ w : Space, Continuous (fun y : Space => cartDiv M (w - y, τ) i) := by
    intro w
    have : (fun y : Space => cartDiv M (w - y, τ) i) =
        fun y => ∑ j : Fin 3, fderiv ℝ (g j) (w - y) (UnforcedLeray.coordinateVector j) :=
      funext fun y => hcd (w - y)
    rw [this]
    refine continuous_finsetSum _ fun j _ => ?_
    exact (hgdc j).comp (continuous_const.sub continuous_id)
  have hDzcs : HasCompactSupport (fun z : Space => cartDiv M (z, τ) i) := by
    have : (fun z : Space => cartDiv M (z, τ) i) =
        fun z => ∑ j : Fin 3, fderiv ℝ (g j) z (UnforcedLeray.coordinateVector j) :=
      funext fun z => hcd z
    rw [this]
    have hs := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun j z => fderiv ℝ (g j) z (UnforcedLeray.coordinateVector j)) fun j _ => hgdcs j
    simpa only [Finset.sum_fn] using hs
  have hK1cs : HasCompactSupport (fun y : Space => cartDiv M (x - y, τ) i) :=
    kf3_cs_sub hDzcs x
  have hI1 : Integrable (fun y : Space => G y * cartDiv M (x - y, τ) i) :=
    kf3_integrable_mul_cs hGc (hDz x) hK1cs
  -- (2) the right integrand
  have hI2 : Integrable (fun z : Space => ∑ k : Fin 3,
      fderiv ℝ G (x - z) (UnforcedLeray.coordinateVector k) * M (z, τ) i k) := by
    refine integrable_finsetSum _ fun k _ => ?_
    exact kf3_integrable_mul_cs (F := fun z => fderiv ℝ G (x - z) (UnforcedLeray.coordinateVector k))
      ((hGd.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)
      (hgc k) (hgcs k)
  refine ⟨hI1, hI2, ?_⟩
  -- (3) the substitution `y = x - z`
  have hsub := integral_sub_left_eq_self (μ := volume)
    (fun z : Space => G (x - z) * cartDiv M (z, τ) i) x
  simp only [sub_sub_cancel] at hsub
  rw [hsub]
  simp_rw [hcd]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  swap
  · intro j _
    exact kf3_integrable_mul_cs hfc (hgdc j) (hgdcs j)
  rw [integral_finsetSum]
  swap
  · intro k _
    exact kf3_integrable_mul_cs (F := fun z => fderiv ℝ G (x - z) (UnforcedLeray.coordinateVector k))
      ((hGd.comp (continuous_const.sub continuous_id)).clm_apply continuous_const)
      (hgc k) (hgcs k)
  refine Finset.sum_congr rfl fun j _ => ?_
  -- integration by parts in the `j`-th direction
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := f) (g := g j) (v := UnforcedLeray.coordinateVector j)
    (kf3_integrable_mul_cs (hfdc _) (hgc j) (hgcs j))
    (kf3_integrable_mul_cs hfc (hgdc j) (hgdcs j))
    (kf3_integrable_mul_cs hfc (hgc j) (hgcs j))
    (fun z _ => (hfs.differentiable (by simp)) z)
    (fun z _ => (hgs j).differentiable (by simp) z)
  rw [hIBP]
  simp only [hfderiv, neg_mul, integral_neg, neg_neg]
  rfl
