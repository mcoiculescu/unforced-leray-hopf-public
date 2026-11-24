import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Core

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the comparison function in physical variables

Source: SP 2861 (`w = J_a W`), SP 2962-2964.

With `P(y) = (1+|y|²)^m` and `g = φ P`, the comparison function at the exit age is
`cmp = a³ ψ p_a` with `ψ = J_a[T(z_t - z_s) φ]` (`cmp_eq_psiT`, `jscaleInv_psiT`), and at the
entrance age `cmp = a³ f p_a` on the cell when `J_a⁻¹ f = φ` there (`cmp_entrance`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

/-- The weight `P(y) = (1+|y|²)^m`. -/
def wP (m : ℝ) (y : ℝ × ℝ) : ℝ := (1 + (y.1 ^ 2 + y.2 ^ 2)) ^ m

/-- The weighted test `g = φ P`. -/
def gP (m : ℝ) (φ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ := φ y * wP m y

/-- The transported test in physical variables at the exit age `t`:
`ψ(x) = a_t⁻² φ(flow(z_t - z_s, x/√a_t))`. -/
def psiT (φ : ℝ × ℝ → ℝ) (ν s t : ℝ) (x : ℝ × ℝ) : ℝ :=
  (clockA ν t)⁻¹ ^ 2 * φ (flowP (movingZ ν t - movingZ ν s) ((Real.sqrt (clockA ν t))⁻¹ • x))

theorem contDiff_wP (m : ℝ) : ContDiff ℝ ∞ (wP m) := by
  unfold wP
  refine ContDiff.rpow_const_of_ne (by fun_prop) fun y => ?_
  have : 0 ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
  linarith

theorem wP_flowP (m z : ℝ) (y : ℝ × ℝ) : wP m (flowP z y) = wP m y := by
  simp only [wP, flowP_normSq]

theorem wP_smul (m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    wP m ((Real.sqrt a)⁻¹ • x) = movWeight m a x := by
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hs0 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  simp only [wP, movWeight, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  congr 1
  field_simp
  rw [hsq]
  ring

theorem smul_sqrt_smul {a : ℝ} (ha : 0 < a) (y : ℝ × ℝ) :
    (Real.sqrt a)⁻¹ • ((Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ × ℝ) = y := by
  have hs0 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  refine Prod.ext ?_ ?_ <;> simp [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs0]

theorem contDiff_gP (m : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (gP m φ) :=
  hφ.mul (contDiff_wP m)

theorem gP_eq_zero {m R : ℝ} {φ : ℝ × ℝ → ℝ}
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (y : ℝ × ℝ)
    (hy : R ^ 2 < y.1 ^ 2 + y.2 ^ 2) : gP m φ y = 0 := by
  simp [gP, hφR y hy]

/-- At the exit age, `cmp = a³ ψ p_a`. -/
theorem cmp_eq_psiT (m : ℝ) (φ : ℝ × ℝ → ℝ) {ν s t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (x : ℝ × ℝ) :
    cmp (tprof (gP m φ)) ν s t x =
      clockA ν t ^ 3 * psiT φ ν s t x * movWeight m (clockA ν t) x := by
  have ha := clockA_pos hν ht
  unfold cmp cpt psiT
  simp only [tprof, gP, wP_flowP]
  rw [wP_smul m ha]
  field_simp

/-- `J_a⁻¹ ψ = T(z_t - z_s) φ`. -/
theorem jscaleInv_psiT (φ : ℝ × ℝ → ℝ) {ν s t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (y : ℝ × ℝ) :
    JscaleInv (clockA ν t) (fun x => ((psiT φ ν s t x : ℝ) : ℂ)) y =
      ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ) := by
  have ha := clockA_pos hν ht
  have ha' : ((clockA ν t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [JscaleInv, psiT]
  rw [smul_sqrt_smul ha]
  push_cast
  field_simp

theorem psiT_eq_zero {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) {ν s t : ℝ} (hν : 0 ≤ ν)
    (ht : 0 ≤ t) {x : ℝ × ℝ}
    (hx : x ∉ Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t))) :
    psiT φ ν s t x = 0 := by
  have hp := cpt_outside (s := s) hν ht le_rfl hR hx
  simp only [cpt] at hp
  unfold psiT
  rw [hφR _ (by rw [flowP_normSq]; exact hp), mul_zero]

theorem continuous_psiT {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ν s t : ℝ) :
    Continuous (psiT φ ν s t) := by
  have e : psiT φ ν s t = fun x => (clockA ν t)⁻¹ ^ 2 * tprof φ (cpt ν s t x) := rfl
  rw [e]
  exact continuous_const.mul ((contDiff_tprof hφ).continuous.comp (continuous_cpt ν s t))

/-- At the entrance age, `cmp = a³ f p_a` on the cell when `J_a⁻¹ f = φ` on the moving cell. -/
theorem cmp_entrance (m : ℝ) (φ : ℝ × ℝ → ℝ) {ν s c : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s)
    {f : ℝ × ℝ → ℝ}
    (hfφ : ∀ y ∈ B0579.cell (cellLen c (clockA ν s)),
      JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) y = ((φ y : ℝ) : ℂ))
    {x : ℝ × ℝ} (hx : x ∈ B0579.cell c) :
    cmp (tprof (gP m φ)) ν s s x = clockA ν s ^ 3 * f x * movWeight m (clockA ν s) x := by
  have ha := clockA_pos hν hs
  have hsa := Real.sqrt_pos.2 ha
  set y := (Real.sqrt (clockA ν s))⁻¹ • x with hy
  have hymem : y ∈ B0579.cell (cellLen c (clockA ν s)) := by
    obtain ⟨⟨h1, h2⟩, -⟩ := hx
    have hr : 0 < (Real.sqrt (clockA ν s))⁻¹ := inv_pos.2 hsa
    have e : cellLen c (clockA ν s) / 2 = (Real.sqrt (clockA ν s))⁻¹ * (c / 2) := by
      unfold cellLen; field_simp
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · show -(cellLen c (clockA ν s) / 2) ≤ (Real.sqrt (clockA ν s))⁻¹ * x.1
      rw [e, ← mul_neg]
      exact mul_le_mul_of_nonneg_left h1 hr.le
    · show (Real.sqrt (clockA ν s))⁻¹ * x.1 < cellLen c (clockA ν s) / 2
      rw [e]
      exact mul_lt_mul_of_pos_left h2 hr
  have hJ := hfφ y hymem
  simp only [JscaleInv] at hJ
  have hxy : ((Real.sqrt (clockA ν s) * y.1, Real.sqrt (clockA ν s) * y.2) : ℝ × ℝ) = x := by
    simp only [hy, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hsa.ne', one_mul]
  rw [hxy] at hJ
  have hφy : φ y = clockA ν s ^ 2 * f x := by
    have h := hJ.symm
    rw [← Complex.ofReal_mul] at h
    exact Complex.ofReal_injective h
  unfold cmp cpt
  simp only [sub_self, tprof, flowP_zero, gP]
  rw [← hy, hφy, wP_smul m ha]
  ring

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
