import UnforcedLeray.Short.PartIIa.Tasks.R09InletScalingNonzero

/-!
# Part II-a, task `PartII-a:R10`, helper: homogeneity gives the derivative bounds

Target `homogDerivBound_proof` is the proposition `HomogDerivBound` of
`Tasks/R10InletBounds.lean`, stated verbatim. Source of record:
`the November 2 reference manuscript`, lines 1226-1229 and 1328-1336.

Proof outline.
* `homogDeriv_scale`: for `z ≠ 0`, `D^j a (l • z) = ((l^j)⁻¹ * l⁻¹) • D^j a z`, from the
  chain rule for the linear map `l • id` on the open set `{x ≠ 0}`.
* The ratio `‖D^j a x‖ / ‖x‖^p`, `p = -(1+j)`, is invariant under all `l^n • ·`, `n : ℤ`.
* A compact annulus `1 ≤ ‖y‖ ≤ l` in `{x ≠ 0}` bounds the ratio; every `x ≠ 0` is `l^n • y`
  with `y` in the annulus.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The chain rule for the dilation `x ↦ l • x` on the open set `{x ≠ 0}`. -/
theorem homogDeriv_scale {l : ℝ} (hl : 1 < l) (a : Space → Space)
    (ha : ContDiffOn ℝ ∞ a {x : Space | x ≠ 0})
    (hhom : ∀ x : Space, x ≠ 0 → a (l • x) = l⁻¹ • a x) (j : ℕ) (z : Space) (hz : z ≠ 0) :
    iteratedFDeriv ℝ j a (l • z) = (((l : ℝ) ^ j)⁻¹ * l⁻¹) • iteratedFDeriv ℝ j a z := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hlne : l ≠ 0 := hl0.ne'
  have hU : IsOpen {x : Space | x ≠ 0} := isOpen_ne
  have hUu : UniqueDiffOn ℝ {x : Space | x ≠ 0} := hU.uniqueDiffOn
  obtain ⟨g, hg⟩ : ∃ g : Space →L[ℝ] Space, ∀ x, g x = l • x :=
    ⟨l • ContinuousLinearMap.id ℝ Space, fun x => by simp⟩
  have hpre : g ⁻¹' {x : Space | x ≠ 0} = {x : Space | x ≠ 0} := by
    ext x
    simp [hg, hlne]
  have hUu' : UniqueDiffOn ℝ (g ⁻¹' {x : Space | x ≠ 0}) := by
    rw [hpre]; exact hUu
  have hgz : g z ∈ {x : Space | x ≠ 0} := by
    show g z ≠ 0
    rw [hg]
    exact smul_ne_zero hlne hz
  have hjle : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hA := ContinuousLinearMap.iteratedFDerivWithin_comp_right g ha hUu hUu' hgz hjle
  rw [hpre] at hA
  have heq : EqOn (a ∘ g) (l⁻¹ • a) {x : Space | x ≠ 0} := by
    intro x hx
    show a (g x) = (l⁻¹ • a) x
    rw [hg]
    exact hhom x hx
  have hB : iteratedFDerivWithin ℝ j (a ∘ g) {x : Space | x ≠ 0} z =
      iteratedFDerivWithin ℝ j (l⁻¹ • a) {x : Space | x ≠ 0} z :=
    iteratedFDerivWithin_congr heq hz j
  have hC : iteratedFDerivWithin ℝ j (l⁻¹ • a) {x : Space | x ≠ 0} z =
      l⁻¹ • iteratedFDerivWithin ℝ j a {x : Space | x ≠ 0} z :=
    iteratedFDerivWithin_const_smul_apply ((ha.of_le hjle) z hz) hUu hz
  have e1 : iteratedFDerivWithin ℝ j a {x : Space | x ≠ 0} z = iteratedFDeriv ℝ j a z :=
    iteratedFDerivWithin_of_isOpen j hU hz
  have e2 : iteratedFDerivWithin ℝ j a {x : Space | x ≠ 0} (g z) = iteratedFDeriv ℝ j a (g z) :=
    iteratedFDerivWithin_of_isOpen j hU hgz
  rw [hB, hC, e1] at hA
  rw [e2] at hA
  rw [hg] at hA
  have hfin : (iteratedFDeriv ℝ j a (l • z)).compContinuousLinearMap (fun _ => g) =
      l⁻¹ • iteratedFDeriv ℝ j a z := hA.symm
  have hlj : (l : ℝ) ^ j ≠ 0 := pow_ne_zero _ hlne
  ext m
  have hm := congrArg (fun F : ContinuousMultilinearMap ℝ (fun _ : Fin j => Space) Space => F m)
    hfin
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg,
    ContinuousMultilinearMap.smul_apply] at hm
  simp only [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hm
  rw [ContinuousMultilinearMap.smul_apply]
  rw [show iteratedFDeriv ℝ j a (l • z) m = ((l : ℝ) ^ j)⁻¹ • ((l : ℝ) ^ j • iteratedFDeriv ℝ j a (l • z) m) by
    rw [smul_smul, inv_mul_cancel₀ hlj, one_smul], hm, smul_smul]

/-- The exponent identity `((l^j)⁻¹ * l⁻¹) = l^(-(1+j))` for `l > 0`. -/
theorem homogCoef_eq {l : ℝ} (hl0 : 0 < l) (j : ℕ) :
    ((l : ℝ) ^ j)⁻¹ * l⁻¹ = l ^ (-(1 + (j : ℝ))) := by
  rw [Real.rpow_neg hl0.le, Real.rpow_add hl0, Real.rpow_one, Real.rpow_natCast, mul_inv]
  ring

/-- **`PartII-a:R10`, homogeneity to derivative bounds.** -/
theorem homogDerivBound_proof : ∀ l : ℝ, 1 < l → ∀ a : Space → Space, ContDiffOn ℝ ∞ a {x : Space | x ≠ 0} → (∀ x : Space, x ≠ 0 → a (l • x) = l⁻¹ • a x) → ∀ j : ℕ, ∃ C : ℝ, ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ j a x‖ ≤ C * ‖x‖ ^ (-(1 + (j : ℝ))) := by
  intro l hl a ha hhom j
  have hl0 : (0 : ℝ) < l := by linarith
  have hlne : l ≠ 0 := hl0.ne'
  have hU : IsOpen {x : Space | x ≠ 0} := isOpen_ne
  have hp_nonpos : -(1 + (j : ℝ)) ≤ 0 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  set p : ℝ := -(1 + (j : ℝ)) with hp
  -- scaling of the norm of the derivative
  have hnorm_scale : ∀ z : Space, z ≠ 0 →
      ‖iteratedFDeriv ℝ j a (l • z)‖ = l ^ p * ‖iteratedFDeriv ℝ j a z‖ := by
    intro z hz
    rw [homogDeriv_scale hl a ha hhom j z hz, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hl0.le j)) (inv_nonneg.2 hl0.le)),
      hp, homogCoef_eq hl0 j]
  -- invariance of the ratio under one dilation
  have hinv : ∀ z : Space, z ≠ 0 →
      ‖iteratedFDeriv ℝ j a (l • z)‖ / ‖l • z‖ ^ p = ‖iteratedFDeriv ℝ j a z‖ / ‖z‖ ^ p := by
    intro z hz
    have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [hnorm_scale z hz, norm_smul, Real.norm_of_nonneg hl0.le, Real.mul_rpow hl0.le hnz.le]
    exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos hl0 p).ne'
  -- invariance under all integer powers
  have hzp : ∀ n : ℤ, ∀ z : Space, z ≠ 0 →
      ‖iteratedFDeriv ℝ j a (((l : ℝ) ^ n) • z)‖ / ‖((l : ℝ) ^ n) • z‖ ^ p
        = ‖iteratedFDeriv ℝ j a z‖ / ‖z‖ ^ p := by
    intro n
    induction n using Int.induction_on with
    | zero => intro z hz; simp
    | succ k ih =>
        intro z hz
        have hlz : l • z ≠ 0 := smul_ne_zero hlne hz
        rw [zpow_add_one₀ hlne, mul_smul, ih (l • z) hlz, hinv z hz]
    | pred k ih =>
        intro z hz
        have hw : (l : ℝ) ^ (-(k : ℤ) - 1) • z ≠ 0 := smul_ne_zero (zpow_ne_zero _ hlne) hz
        have e : l • ((l : ℝ) ^ (-(k : ℤ) - 1) • z) = (l : ℝ) ^ (-(k : ℤ)) • z := by
          rw [smul_smul, ← zpow_one_add₀ hlne, show (1 : ℤ) + (-(k : ℤ) - 1) = -(k : ℤ) by ring]
        have hstep := hinv ((l : ℝ) ^ (-(k : ℤ) - 1) • z) hw
        rw [e] at hstep
        rw [← hstep]
        exact ih z hz
  -- continuity of the derivative on the open set
  have hjle : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcontW := ha.continuousOn_iteratedFDerivWithin hjle hU.uniqueDiffOn
  have hcont : ContinuousOn (iteratedFDeriv ℝ j a) {x : Space | x ≠ 0} :=
    hcontW.congr (fun x hx => (iteratedFDerivWithin_of_isOpen j hU hx).symm)
  -- the compact annulus
  set A : Set Space := {y : Space | 1 ≤ ‖y‖} ∩ {y : Space | ‖y‖ ≤ l} with hAdef
  have hAclosed : IsClosed A :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hAsub : A ⊆ Metric.closedBall (0 : Space) l := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy.2
  have hAcompact : IsCompact A :=
    (isCompact_closedBall (0 : Space) l).of_isClosed_subset hAclosed hAsub
  have hAU : A ⊆ {x : Space | x ≠ 0} := by
    intro y hy h0
    have h1 : (1 : ℝ) ≤ ‖y‖ := hy.1
    rw [h0, norm_zero] at h1
    linarith
  have hcn : ContinuousOn (fun y : Space => ‖iteratedFDeriv ℝ j a y‖) A :=
    (hcont.mono hAU).norm
  obtain ⟨M, hM0⟩ := hAcompact.exists_bound_of_continuousOn hcn
  have hM : ∀ y ∈ A, ‖iteratedFDeriv ℝ j a y‖ ≤ M := fun y hy => by
    simpa only [norm_norm] using hM0 y hy
  -- bound for every point via the annulus
  refine ⟨M / l ^ p, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hl
  have hln : (0 : ℝ) < (l : ℝ) ^ n := zpow_pos hl0 n
  set y : Space := ((l : ℝ) ^ n)⁻¹ • x with hydef
  have hy0 : y ≠ 0 := smul_ne_zero (inv_ne_zero hln.ne') hx
  have hynorm : ‖y‖ = ‖x‖ / (l : ℝ) ^ n := by
    rw [hydef, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hln.le), inv_mul_eq_div]
  have hy1 : 1 ≤ ‖y‖ := by
    rw [hynorm, one_le_div hln]
    exact hn1
  have hy2 : ‖y‖ ≤ l := by
    rw [hynorm, div_le_iff₀ hln, mul_comm]
    rw [zpow_add_one₀ hlne] at hn2
    exact hn2.le
  have hyA : y ∈ A := ⟨hy1, hy2⟩
  have hxy : ((l : ℝ) ^ n) • y = x := by
    rw [hydef, smul_smul, mul_inv_cancel₀ hln.ne', one_smul]
  have hrat := hzp n y hy0
  rw [hxy] at hrat
  have hMy : ‖iteratedFDeriv ℝ j a y‖ ≤ M := hM y hyA
  have hlp_le : (l : ℝ) ^ p ≤ ‖y‖ ^ p :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hy2 hp_nonpos
  have hbound : ‖iteratedFDeriv ℝ j a x‖ / ‖x‖ ^ p ≤ M / l ^ p := by
    rw [hrat]
    exact div_le_div₀ (le_trans (norm_nonneg _) hMy) hMy (Real.rpow_pos_of_pos hl0 p) hlp_le
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hxpos p)).1 hbound

end UnforcedLeray.Short.PartIIa
