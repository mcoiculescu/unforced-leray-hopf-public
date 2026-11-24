import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.TailSmooth

/-!
# `kf3TailIBP : KF3TailIBP` (source 3617-3618)

Integrate the tensor divergence by parts against the heat tail `H = heatTail θ`, which is smooth
by `kf3TailSmooth`.  For `M(·, τ)` smooth with compact support and `g_j = (div M)_j(·, τ)`
(`cartDiv`, `(div M)_j = Σ_k ∂_k M_{jk}`), two integrations by parts in `z` give
`∫ ∂_jH(x - z) ∂_i g_j(z) dz = ∫ ∂_i∂_jH(x - z) g_j(z) dz = Σ_k ∫ ∂_k(∂_i∂_jH)(x - z) M_{jk}(z, τ) dz`,
using `∂_{z_l}[F(x - z)] = -(∂_lF)(x - z)`.  All integrands are continuous with compact support
(`HasCompactSupport.fderiv_apply`, `HasCompactSupport.finset_sum`), so Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Compact support of a single entry `x ↦ M(x, τ)_{ij}` of a smooth outer tensor. -/
theorem kf3ti_entry_cs {P : ℝ} {M : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hM : IsOuterTest P M)
    (τ : ℝ) (i j : Fin 3) : HasCompactSupport (fun x : Space => M (x, τ) i j) := by
  obtain ⟨r, hr⟩ := hM.bounded
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) r) (fun x hx => ?_)
  by_contra hne
  have hM0 : M (x, τ) ≠ 0 := fun h => hne (by simp [h])
  have h1 := hr (x, τ) hM0
  exact hx (by simpa using h1)

/-- Integrability of a continuous function times a continuous compactly supported one. -/
theorem kf3ti_integrable_mul_cs {F K : Space → ℝ} (hF : Continuous F) (hK : Continuous K)
    (hKc : HasCompactSupport K) : Integrable (fun z => F z * K z) := by
  have hc : HasCompactSupport (fun z => F z * K z) := hKc.mul_left
  exact (hF.mul hK).integrable_of_hasCompactSupport hc

/-- Reflection rule: `∂_z[P(x - z)] v = -(∂P)(x - z) v`. -/
theorem kf3ti_reflect {P : Space → ℝ} (hP : Differentiable ℝ P) (x z v : Space) :
    fderiv ℝ (fun z : Space => P (x - z)) z v = -fderiv ℝ P (x - z) v := by
  have h1 : HasFDerivAt (fun z : Space => x - z) (-(ContinuousLinearMap.id ℝ Space)) z :=
    (hasFDerivAt_id z).const_sub x
  have h2 : HasFDerivAt (fun z : Space => P (x - z))
      ((fderiv ℝ P (x - z)).comp (-(ContinuousLinearMap.id ℝ Space))) z :=
    HasFDerivAt.comp z (hP (x - z)).hasFDerivAt h1
  rw [h2.fderiv]
  simp

/-- Integration by parts in one direction for smooth `F` and compactly supported smooth `G`. -/
theorem kf3ti_ibp {F G : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (v : Space) :
    ∫ z, F z * fderiv ℝ G z v = -∫ z, fderiv ℝ F z v * G z := by
  have hGd : Continuous (fun z => fderiv ℝ G z v) :=
    (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  have hFd : Continuous (fun z => fderiv ℝ F z v) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGdc : HasCompactSupport (fun z => fderiv ℝ G z v) :=
    HasCompactSupport.fderiv_apply ℝ hGc v
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F) (g := G) (v := v)
    (kf3ti_integrable_mul_cs hFd hG.continuous hGc)
    (kf3ti_integrable_mul_cs hF.continuous hGd hGdc)
    (kf3ti_integrable_mul_cs hF.continuous hG.continuous hGc)
    (fun z _ => (hF.differentiable (by simp)) z)
    (fun z _ => (hG.differentiable (by simp)) z)

/-- The second partial `∂_i∂_jH` of a smooth function is smooth. -/
theorem kf3ti_part2_smooth {H : Space → ℝ} (hH : ContDiff ℝ ∞ H) (i j : Fin 3) :
    ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.part2 H i j) := by
  unfold UnforcedLeray.Short.IIIa.part2
  have hD : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)
  have hφ : ContDiff ℝ ∞ (fun y : Space => fderiv ℝ H y (UnforcedLeray.coordinateVector j)) :=
    hD.clm_apply contDiff_const
  have hD2 : ContDiff ℝ ∞
      (fderiv ℝ (fun y : Space => fderiv ℝ H y (UnforcedLeray.coordinateVector j))) :=
    hφ.fderiv_right (m := ∞) (by simp)
  exact hD2.clm_apply contDiff_const

set_option maxHeartbeats 1600000 in
theorem kf3TailIBP : KF3TailIBP := by
  intro Per M hM τ x θ hθ i
  have hHs0 : ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.heatTail θ) := kf3TailSmooth θ hθ
  set H : Space → ℝ := UnforcedLeray.Short.IIIa.heatTail θ with hHdef
  -- the entries of `M(·, τ)` and their derivatives
  have hms : ∀ j k : Fin 3, ContDiff ℝ ∞ (fun z : Space => M (z, τ) j k) := fun j k =>
    (hM.smooth j k).comp (contDiff_id.prodMk contDiff_const)
  have hmcont : ∀ j k : Fin 3, Continuous (fun z : Space => M (z, τ) j k) := fun j k =>
    (hms j k).continuous
  have hmc : ∀ j k : Fin 3, HasCompactSupport (fun z : Space => M (z, τ) j k) := fun j k =>
    kf3ti_entry_cs hM τ j k
  -- the divergence in the `z`-variable
  have hsplit : ∀ j : Fin 3, ∀ z : Space, cartDiv M (z, τ) j = ∑ k : Fin 3,
      fderiv ℝ (fun z : Space => M (z, τ) j k) z (UnforcedLeray.coordinateVector k) := by
    intro j z
    simp [cartDiv]
  have hgs : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z : Space => cartDiv M (z, τ) j) := by
    intro j
    have hfun : (fun z : Space => cartDiv M (z, τ) j) = fun z : Space => ∑ k : Fin 3,
        fderiv ℝ (fun z : Space => M (z, τ) j k) z (UnforcedLeray.coordinateVector k) :=
      funext (hsplit j)
    rw [hfun]
    exact ContDiff.sum (fun k _ => ((hms j k).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const)
  have hgcs : ∀ j : Fin 3, HasCompactSupport (fun z : Space => cartDiv M (z, τ) j) := by
    intro j
    have hfun : (fun z : Space => cartDiv M (z, τ) j) = fun z : Space => ∑ k : Fin 3,
        fderiv ℝ (fun z : Space => M (z, τ) j k) z (UnforcedLeray.coordinateVector k) :=
      funext (hsplit j)
    rw [hfun]
    have hs := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun k z => fderiv ℝ (fun z : Space => M (z, τ) j k) z
        (UnforcedLeray.coordinateVector k))
      (fun k _ => HasCompactSupport.fderiv_apply ℝ (hmc j k) (UnforcedLeray.coordinateVector k))
    simpa only [Finset.sum_fn] using hs
  -- smoothness of the heat tail and its derivatives
  have hDH : ContDiff ℝ ∞ (fderiv ℝ H) := hHs0.fderiv_right (m := ∞) (by simp)
  have hFj : ∀ j : Fin 3, ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ H (x - z) (UnforcedLeray.coordinateVector j)) := fun j =>
    (hDH.comp (contDiff_const.sub contDiff_id)).clm_apply contDiff_const
  have hφs : ∀ j : Fin 3, ContDiff ℝ ∞
      (fun y : Space => fderiv ℝ H y (UnforcedLeray.coordinateVector j)) := fun j =>
    hDH.clm_apply contDiff_const
  have hPs : ∀ j : Fin 3, ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.part2 H i j) := fun j =>
    kf3ti_part2_smooth hHs0 i j
  have hPdiff : ∀ j : Fin 3, Differentiable ℝ (UnforcedLeray.Short.IIIa.part2 H i j) := fun j =>
    (hPs j).differentiable (by simp)
  have hPc : ∀ j : Fin 3, Continuous (fun z : Space =>
      fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z)) := fun j =>
    ((hPs j).continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)
  -- Step A: the first derivative of `∂_jH(x - ·)` in direction `e_i`
  have hA : ∀ j : Fin 3, ∀ z : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ H (x - z) (UnforcedLeray.coordinateVector j)) z
        (UnforcedLeray.coordinateVector i) = -UnforcedLeray.Short.IIIa.part2 H i j (x - z) := by
    intro j z
    exact kf3ti_reflect ((hφs j).differentiable (by simp)) x z (UnforcedLeray.coordinateVector i)
  -- Step B: the first integration by parts in `z`
  have hB : ∀ j : Fin 3,
      ∫ z : Space, fderiv ℝ H (x - z) (UnforcedLeray.coordinateVector j) *
          fderiv ℝ (fun z : Space => cartDiv M (z, τ) j) z (UnforcedLeray.coordinateVector i) =
        ∫ z : Space, UnforcedLeray.Short.IIIa.part2 H i j (x - z) * cartDiv M (z, τ) j := by
    intro j
    have h := kf3ti_ibp (hFj j) (hgs j) (hgcs j) (UnforcedLeray.coordinateVector i)
    simp only [hA j, neg_mul, integral_neg, neg_neg] at h
    exact h
  -- Step C: the second integration by parts, against the entries of `M`
  have hR : ∀ j k : Fin 3, ∀ z : Space,
      fderiv ℝ (fun z : Space => UnforcedLeray.Short.IIIa.part2 H i j (x - z)) z
        (UnforcedLeray.coordinateVector k) =
        -fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z)
          (UnforcedLeray.coordinateVector k) := fun j k z =>
    kf3ti_reflect (hPdiff j) x z (UnforcedLeray.coordinateVector k)
  have hC : ∀ j : Fin 3,
      ∫ z : Space, UnforcedLeray.Short.IIIa.part2 H i j (x - z) * cartDiv M (z, τ) j =
        ∫ z : Space, ∑ k : Fin 3,
          fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z) (UnforcedLeray.coordinateVector k) *
            M (z, τ) j k := by
    intro j
    have hPs' : ContDiff ℝ ∞ (fun z : Space => UnforcedLeray.Short.IIIa.part2 H i j (x - z)) :=
      (hPs j).comp (contDiff_const.sub contDiff_id)
    have hIBP : ∀ k : Fin 3,
        ∫ z : Space, UnforcedLeray.Short.IIIa.part2 H i j (x - z) *
            fderiv ℝ (fun z : Space => M (z, τ) j k) z (UnforcedLeray.coordinateVector k) =
          ∫ z : Space, fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z)
              (UnforcedLeray.coordinateVector k) * M (z, τ) j k := by
      intro k
      have h := kf3ti_ibp hPs' (hms j k) (hmc j k) (UnforcedLeray.coordinateVector k)
      simp only [hR j k, neg_mul, integral_neg, neg_neg] at h
      exact h
    have hint : ∀ k : Fin 3, Integrable (fun z : Space =>
        UnforcedLeray.Short.IIIa.part2 H i j (x - z) *
          fderiv ℝ (fun z : Space => M (z, τ) j k) z (UnforcedLeray.coordinateVector k)) := by
      intro k
      exact kf3ti_integrable_mul_cs (F := fun z : Space => UnforcedLeray.Short.IIIa.part2 H i j (x - z))
        hPs'.continuous
        (((hms j k).continuous_fderiv (by simp)).clm_apply continuous_const)
        (HasCompactSupport.fderiv_apply ℝ (hmc j k) (UnforcedLeray.coordinateVector k))
    have hint2 : ∀ k : Fin 3, Integrable (fun z : Space =>
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z) (UnforcedLeray.coordinateVector k) *
          M (z, τ) j k) := by
      intro k
      exact kf3ti_integrable_mul_cs
        (F := fun z : Space => fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z)
          (UnforcedLeray.coordinateVector k))
        ((hPc j).clm_apply continuous_const) (hmcont j k) (hmc j k)
    have hsplit_int : ∀ z : Space, UnforcedLeray.Short.IIIa.part2 H i j (x - z) * cartDiv M (z, τ) j =
        ∑ k : Fin 3, UnforcedLeray.Short.IIIa.part2 H i j (x - z) *
          fderiv ℝ (fun z : Space => M (z, τ) j k) z (UnforcedLeray.coordinateVector k) := by
      intro z
      rw [hsplit j z, Finset.mul_sum]
    simp_rw [hsplit_int]
    rw [integral_finsetSum]
    swap
    · intro k _
      exact hint k
    rw [integral_finsetSum]
    swap
    · intro k _
      exact hint2 k
    exact Finset.sum_congr rfl (fun k _ => hIBP k)
  -- assembly
  refine ⟨?_, ?_⟩
  · refine integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => ?_))
    exact kf3ti_integrable_mul_cs
      (F := fun z : Space => fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z)
        (UnforcedLeray.coordinateVector k))
      ((hPc j).clm_apply continuous_const) (hmcont j k) (hmc j k)
  · have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z : Space => ∑ k : Fin 3,
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z) (UnforcedLeray.coordinateVector k) *
          M (z, τ) j k) := by
      intro j _
      refine integrable_finsetSum _ (fun k _ => ?_)
      exact kf3ti_integrable_mul_cs
        (F := fun z : Space => fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z)
          (UnforcedLeray.coordinateVector k))
        ((hPc j).clm_apply continuous_const) (hmcont j k) (hmc j k)
    have hsum : ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z) (UnforcedLeray.coordinateVector k) *
          M (z, τ) j k =
        ∑ j : Fin 3, ∫ z : Space, ∑ k : Fin 3,
          fderiv ℝ (UnforcedLeray.Short.IIIa.part2 H i j) (x - z) (UnforcedLeray.coordinateVector k) *
            M (z, τ) j k :=
      integral_finsetSum _ hint
    rw [hsum]
    simp only [hB, hC]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
