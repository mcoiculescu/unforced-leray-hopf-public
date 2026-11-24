import UnforcedLeray.Short.PartIIb.Sub.T22_4
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Lib.Cylinder.Weight

/-!
# Shared helpers for the leaves `PartII-b:T22/4/1-4` (diffusion bound)

Integrability on the centred cell of the decay-weighted integrands of `DbInt1`, `DbInt2`
(`dbS` is the four-term decay sum of `CylSmoothDecay`), and the smooth-slice calculus used by
`DbCutId`. Source: `the November 2 reference manuscript` lines 2092-2104.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

namespace DbCommon

theorem jb_split (x : B0579.Plane) (m : ℝ) :
    B0579.jb x ^ m = B0579.jb x ^ ((m + 4) / 2) * B0579.jb x ^ ((m + 4) / 2) *
      B0579.jb x ^ (-4 : ℝ) := by
  rw [← Real.rpow_add (B0579.jb_pos x), ← Real.rpow_add (B0579.jb_pos x)]
  congr 1
  ring

theorem integrable_jb_neg4 : Integrable (fun x : B0579.Plane => B0579.jb x ^ (-4 : ℝ)) :=
  UnforcedLeray.Cyl.integrable_rpow_neg_ρc (m := 4) (by norm_num)

/-- The four-term decay sum `|g| + |∂_q g| + |∂_η g| + |Δg|`. -/
def dbS (g : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  |g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|

theorem dbS_nonneg (g : B0579.Plane → ℝ) (x : B0579.Plane) : 0 ≤ dbS g x := by
  unfold dbS; positivity

theorem abs_le_dbS (g : B0579.Plane → ℝ) (x : B0579.Plane) :
    |g x| ≤ dbS g x ∧ |B0579.pd 0 g x| ≤ dbS g x ∧ |B0579.pd 1 g x| ≤ dbS g x ∧
      |lapP g x| ≤ dbS g x := by
  unfold dbS
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    linarith [abs_nonneg (g x), abs_nonneg (B0579.pd 0 g x), abs_nonneg (B0579.pd 1 g x),
      abs_nonneg (lapP g x)]

theorem sq_le_dbS_mul {a S : ℝ} (h : |a| ≤ S) : a ^ 2 ≤ S * S := by
  have h0 : 0 ≤ S := (abs_nonneg a).trans h
  have h2 : a ^ 2 = |a| * |a| := by rw [sq, abs_mul_abs_self]
  rw [h2]
  exact mul_le_mul h h (abs_nonneg a) h0

/-- On the strip `|q| ≤ c/2` the decay sum times `jb^m` is dominated by `C jb^{-4}`. -/
theorem dbS_bound_cell {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (m : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      dbS g x * dbS g x * B0579.jb x ^ m ≤ C * B0579.jb x ^ (-4 : ℝ) := by
  obtain ⟨C0, hC0⟩ := hg.cell_decay ((m + 4) / 2)
  refine ⟨max C0 0 * max C0 0, mul_nonneg (le_max_right _ _) (le_max_right _ _),
    fun x hx => ?_⟩
  have hT0 : 0 ≤ dbS g x * B0579.jb x ^ ((m + 4) / 2) :=
    mul_nonneg (dbS_nonneg g x) (Real.rpow_nonneg (B0579.jb_pos x).le _)
  have hT : dbS g x * B0579.jb x ^ ((m + 4) / 2) ≤ max C0 0 :=
    (hC0 x hx).trans (le_max_left _ _)
  have hTT : (dbS g x * B0579.jb x ^ ((m + 4) / 2)) * (dbS g x * B0579.jb x ^ ((m + 4) / 2))
      ≤ max C0 0 * max C0 0 :=
    mul_le_mul hT hT hT0 (le_max_right _ _)
  have hQ0 : 0 ≤ B0579.jb x ^ (-4 : ℝ) := Real.rpow_nonneg (B0579.jb_pos x).le _
  calc dbS g x * dbS g x * B0579.jb x ^ m
      = (dbS g x * B0579.jb x ^ ((m + 4) / 2)) * (dbS g x * B0579.jb x ^ ((m + 4) / 2)) *
          B0579.jb x ^ (-4 : ℝ) := by
        rw [jb_split x m]; ring
    _ ≤ max C0 0 * max C0 0 * B0579.jb x ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right hTT hQ0

theorem cell_integrable_of_bound {c : ℝ} {f Q : B0579.Plane → ℝ}
    (hQ : IntegrableOn Q (B0579.cell c)) (hf : Continuous f)
    (hb : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → ‖f x‖ ≤ Q x) :
    IntegrableOn f (B0579.cell c) :=
  Integrable.mono' hQ hf.aestronglyMeasurable
    ((ae_restrict_iff' (B0579.measurableSet_cell c)).2
      (ae_of_all _ fun x hx => hb x (abs_fst_le_of_mem_cell hx)))

/-- Cell integrability of a continuous integrand dominated by `K · dbS² · jb^m`. -/
theorem cell_int_dbS {c m K : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g) (hK : 0 ≤ K)
    {f : B0579.Plane → ℝ} (hf : Continuous f)
    (hb : ∀ x : B0579.Plane, |x.1| ≤ c / 2 → |f x| ≤ K * (dbS g x * dbS g x * B0579.jb x ^ m)) :
    IntegrableOn f (B0579.cell c) := by
  obtain ⟨C, hC0, hC⟩ := dbS_bound_cell hg m
  refine cell_integrable_of_bound (Q := fun x => (K * C) * B0579.jb x ^ (-4 : ℝ))
    (integrable_jb_neg4.const_mul (K * C)).integrableOn hf (fun x hx => ?_)
  rw [Real.norm_eq_abs]
  calc |f x| ≤ K * (dbS g x * dbS g x * B0579.jb x ^ m) := hb x hx
    _ ≤ K * (C * B0579.jb x ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left (hC x hx) hK
    _ = (K * C) * B0579.jb x ^ (-4 : ℝ) := by ring

/-! ## Continuity and slices -/

theorem contDiff_pd_of {n : WithTop ℕ∞} {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ (n + 1) φ)
    (j : Fin 2) : ContDiff ℝ n (B0579.pd j φ) := by
  unfold B0579.pd
  exact (hφ.fderiv_right (m := n) le_rfl).clm_apply contDiff_const

theorem pd_contDiff_one {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ 2 φ) (j : Fin 2) :
    ContDiff ℝ 1 (B0579.pd j φ) := by
  have h : ContDiff ℝ (1 + 1) φ := by rwa [one_add_one_eq_two]
  exact contDiff_pd_of h j

theorem continuous_pd_pd {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ 2 φ) (j k : Fin 2) :
    Continuous (B0579.pd j (B0579.pd k φ)) := by
  have h1 : ContDiff ℝ (0 + 1) (B0579.pd k φ) := by
    rw [zero_add]; exact pd_contDiff_one hφ k
  exact (contDiff_pd_of h1 j).continuous

theorem continuous_lapP {g : B0579.Plane → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (lapP g) := by
  unfold lapP
  exact (continuous_pd_pd hg 0 0).add (continuous_pd_pd hg 1 1)

theorem continuous_pd_of_c2 {g : B0579.Plane → ℝ} (hg : ContDiff ℝ 2 g) (j : Fin 2) :
    Continuous (B0579.pd j g) :=
  (pd_contDiff_one hg j).continuous

theorem continuous_pd0_jb (m : ℝ) : Continuous (B0579.pd 0 (fun y => B0579.jb y ^ m)) := by
  have e : B0579.pd 0 (fun y => B0579.jb y ^ m) = fun x => 2 * x.1 * m * B0579.jb x ^ (m - 1) :=
    funext fun x => B0579.pd_zero_jb_rpow m x
  rw [e]
  exact ((continuous_const.mul continuous_fst).mul continuous_const).mul
    (B0579.contDiff_jb_rpow (m - 1)).continuous

theorem continuous_pd1_jb (m : ℝ) : Continuous (B0579.pd 1 (fun y => B0579.jb y ^ m)) := by
  have e : B0579.pd 1 (fun y => B0579.jb y ^ m) = fun x => 2 * x.2 * m * B0579.jb x ^ (m - 1) :=
    funext fun x => B0579.pd_one_jb_rpow m x
  rw [e]
  exact ((continuous_const.mul continuous_snd).mul continuous_const).mul
    (B0579.contDiff_jb_rpow (m - 1)).continuous

theorem continuous_dens (m : ℝ) : Continuous (fun x : B0579.Plane => (B0579.density m x : ℝ)) := by
  simp only [B0579.coe_density]
  exact B0579.continuous_jb_rpow m

/-- Derivative of a differentiable function along `q` at fixed `η`. -/
theorem hasDerivAt_slice_q {φ : B0579.Plane → ℝ} (hφ : Differentiable ℝ φ) (q η : ℝ) :
    HasDerivAt (fun t => φ (t, η)) (B0579.pd 0 φ (q, η)) q := by
  have h0 : HasDerivAt (fun t : ℝ => (t, η)) ((1 : ℝ), (0 : ℝ)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
  exact (hφ (q, η)).hasFDerivAt.comp_hasDerivAt q h0

/-- Derivative of a differentiable function along `η` at fixed `q`. -/
theorem hasDerivAt_slice_eta {φ : B0579.Plane → ℝ} (hφ : Differentiable ℝ φ) (q η : ℝ) :
    HasDerivAt (fun t => φ (q, t)) (B0579.pd 1 φ (q, η)) η := by
  have h0 : HasDerivAt (fun t : ℝ => (q, t)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
  exact (hφ (q, η)).hasFDerivAt.comp_hasDerivAt η h0

/-- A `c`-periodic `C²` function has `c`-periodic `∂_q`. -/
theorem pd0_periodic {c : ℝ} {g : B0579.Plane → ℝ} (hg : ContDiff ℝ 2 g)
    (hper : ∀ x : B0579.Plane, g (x.1 + c, x.2) = g x) (q η : ℝ) :
    B0579.pd 0 g (q + c, η) = B0579.pd 0 g (q, η) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have e : (fun t : ℝ => g (t + c, η)) = fun t => g (t, η) := funext fun t => hper (t, η)
  have h2 : HasDerivAt (fun t : ℝ => g (t + c, η)) (B0579.pd 0 g (q + c, η)) q :=
    (hasDerivAt_slice_q hgd (q + c) η).comp_add_const q c
  rw [e] at h2
  exact h2.unique (hasDerivAt_slice_q hgd q η)

/-- Integrability on the cell of a continuous function vanishing for `|η| > R`. -/
theorem integrableOn_cell_of_eta {c R : ℝ} {f : B0579.Plane → ℝ} (hf : Continuous f)
    (h0 : ∀ x : B0579.Plane, R < |x.2| → f x = 0) :
    IntegrableOn f (B0579.cell c) := by
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn f (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    hf.continuousOn.integrableOn_compact hK
  have h2 : Integrable ((Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator f) :=
    h1.integrable_indicator hK.measurableSet
  refine (h2.integrableOn).congr_fun (fun x hx => ?_) (B0579.measurableSet_cell c)
  by_cases hxK : x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  · rw [indicator_of_mem hxK]
  · rw [indicator_of_notMem hxK]
    have hx2 : x.2 ∉ Icc (-R) R := fun h =>
      hxK (Set.mk_mem_prod ⟨hx.1.1, hx.1.2.le⟩ h)
    have hlt : R < |x.2| := by
      by_contra hle
      push Not at hle
      exact hx2 (Set.mem_Icc.mpr (abs_le.mp hle))
    exact (h0 x hlt).symm

/-- A compactly supported function has a uniform support radius. -/
theorem exists_support_radius {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) :
    ∃ R : ℝ, ∀ t : ℝ, R < |t| → χ t = 0 := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun t ht => ?_⟩
  by_contra hne
  have hmem : t ∈ tsupport χ := subset_tsupport χ hne
  have h := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
  linarith

end DbCommon

end UnforcedLeray.Short.IIb
