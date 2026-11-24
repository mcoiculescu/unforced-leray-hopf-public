import UnforcedLeray.Lib.Gaussian.IteratedDeriv
import UnforcedLeray.Lib.Gaussian.LpNorm

/-!
# The causal heat Hessian kernel: pointwise bounds (INF02 T5, part 1)


target T5; Wave 2 block 2C of `scoping/README.md` §5 (decision D4: the parabolic instance of the
Calderón–Zygmund core `Lib/CZCore`; decision D14: the Gaussian facts come from `Lib/Gaussian`).

Manuscript: the lemma eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit
B0423) applies the singular-integral theorem to the causal kernel `1_{θ>0} ∂_{ij} H_θ`, which has
dilation weights `(1,…,1,2)` (line 7466). This file proves the pointwise facts about that kernel
that the Calderón–Zygmund argument uses.

* `PS d = ℝ × ℝ^d` (time first), `ev i` the `i`-th unit vector of `ℝ^d`.
* `hessG i j t x = ∂_i∂_j G_t(x)`; `hessG_eq_scale`: `∂_i∂_j G_t(x) = t^{-(d+2)/2} φ(t^{-1/2}x)`
  with `φ = ∂_i∂_j G_1`.
* `causalKernel i j (t, x) = 1_{t>0} ∂_i∂_j G_t(x)`; `measurable_causalKernel`,
  `causalKernel_neg_space` (evenness in `x`).
* `abs_hessG_le`: `|∂_i∂_j G_t(x)| ≤ C (t + |x|²)^{-(d+2)/2}` (size bound);
  `abs_hessG_le_mul`: `|∂_i∂_j G_t(x)| ≤ C t (t + |x|²)^{-(d+4)/2}` (small times);
  `exists_hasDerivAt_hessG`: `|∂_t ∂_i∂_j G_t(x)| ≤ C (t + |x|²)^{-(d+4)/2}`;
  `abs_hessG_sub_le`: the spatial mean-value bound with `(t + |x|²)^{-(d+3)/2}`.
* `abs_causalKernel_time_sub_le`: the time-Lipschitz bound across `t = 0`.
* `abs_causalKernel_sub_le` (pointwise Hörmander bound): if `R ≤ |τ| + |x|²` along the time
  path and `R ≤ |t-s| + |x - θy|²` along the space path, then
  `|K(X - Y) - K(X)| ≤ C₁ |y| R^{-(d+3)/2} + C₂ |s| R^{-(d+4)/2}`.

No statement concerns `t ≤ 0` values of the Gaussian formula, which are Lean junk values: the
kernel is set to `0` there, as in the manuscript's indicator `1_{θ>0}`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set
open scoped ENNReal NNReal

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- Space-time `ℝ × ℝ^d`, time first (INF02 §5 `PS`). -/
abbrev PS (d : ℕ) := ℝ × Euc d

/-- The `i`-th unit vector of `ℝ^d`. -/
abbrev ev {d : ℕ} (i : Fin d) : Euc d := EuclideanSpace.single i 1

theorem norm_ev {d : ℕ} (i : Fin d) : ‖ev i‖ = 1 := by simp [ev]

variable {d : ℕ}

/-- The Hessian entry `∂_i∂_j G_t(x)` of the heat kernel (meaningful for `t > 0`). -/
def hessG (i j : Fin d) (t : ℝ) (x : Euc d) : ℝ :=
  iteratedFDeriv ℝ 2 (gaussKernel d t) x ![ev i, ev j]

/-- The profile `φ = ∂_i∂_j G_1`. -/
def hessProfile (i j : Fin d) (z : Euc d) : ℝ := hessG i j 1 z

/-- **INF02 T5.** The causal Hessian kernel `K_{ij}(t,x) = 1_{t>0} ∂_i∂_j G_t(x)` (tex 7466,
B0423). -/
def causalKernel (i j : Fin d) (X : PS d) : ℝ :=
  if 0 < X.1 then hessG i j X.1 X.2 else 0

theorem causalKernel_of_pos (i j : Fin d) {X : PS d} (h : 0 < X.1) :
    causalKernel i j X = hessG i j X.1 X.2 := by simp [causalKernel, h]

theorem causalKernel_of_nonpos (i j : Fin d) {X : PS d} (h : X.1 ≤ 0) :
    causalKernel i j X = 0 := by simp [causalKernel, not_lt.2 h]

section Scale

theorem rpow_neg_half_sq {t : ℝ} (ht : 0 < t) : (t ^ (-(1 : ℝ) / 2)) ^ 2 = t⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num [Real.rpow_neg_one]

/-- `t^{-a} (1 + |t^{-1/2}x|²)^{-a} = (t + |x|²)^{-a}`. -/
theorem rpow_mul_one_add_scale {t : ℝ} (ht : 0 < t) (x : Euc d) (a : ℝ) :
    t ^ (-a) * (1 + ‖t ^ (-(1 : ℝ) / 2) • x‖ ^ 2) ^ (-a) = (t + ‖x‖ ^ 2) ^ (-a) := by
  rw [← Real.mul_rpow ht.le (by positivity)]
  congr 1
  rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow, rpow_neg_half_sq ht]
  field_simp

/-- Parabolic scaling of the Hessian: `∂_i∂_j G_t(x) = t^{-(d+2)/2} φ(t^{-1/2}x)`. -/
theorem hessG_eq_scale (i j : Fin d) {t : ℝ} (ht : 0 < t) (x : Euc d) :
    hessG i j t x = t ^ (-(((d : ℝ) + 2) / 2)) * hessProfile i j (t ^ (-(1 : ℝ) / 2) • x) := by
  unfold hessG hessProfile hessG
  rw [Gaussian.gaussKernel_eq_scale ht, Gaussian.iteratedFDeriv_comp_smul]
  simp only [smul_apply, smul_eq_mul]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1; push_cast; ring

/-- Gaussian decay of the profile derivatives in polynomial form. -/
theorem exists_norm_iteratedFDeriv_gaussKernel_one_le (n : ℕ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Euc d,
      ‖iteratedFDeriv ℝ n (gaussKernel d 1) z‖ ≤ C * (1 + ‖z‖ ^ 2) ^ (-m / 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le d n
  obtain ⟨C₂, hC₂, h₂⟩ := Gaussian.rpow_mul_exp_le_parabolic hm
  refine ⟨C₁ * C₂, by positivity, fun z => ?_⟩
  have h1 := h₁ (t := 1) one_pos z
  have h2 := h₂ 1 ‖z‖ one_pos
  rw [Real.one_rpow, one_mul] at h2
  rw [Real.one_rpow, mul_one] at h1
  calc ‖iteratedFDeriv ℝ n (gaussKernel d 1) z‖ ≤ C₁ * Real.exp (-‖z‖ ^ 2 / (8 * 1)) := h1
    _ ≤ C₁ * (C₂ * (1 + ‖z‖ ^ 2) ^ (-m / 2)) := by gcongr
    _ = C₁ * C₂ * (1 + ‖z‖ ^ 2) ^ (-m / 2) := by ring

theorem abs_apply_ev_le (L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ)
    (i j : Fin d) : |L ![ev i, ev j]| ≤ ‖L‖ := by
  have h := L.le_opNorm ![ev i, ev j]
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  simp [Fin.prod_univ_two]

theorem abs_hessG_le_norm (i j : Fin d) (t : ℝ) (x : Euc d) :
    |hessG i j t x| ≤ ‖iteratedFDeriv ℝ 2 (gaussKernel d t) x‖ :=
  abs_apply_ev_le _ i j

end Scale

section Size

/-- **Size bound.** `|∂_i∂_j G_t(x)| ≤ C (t + |x|²)^{-(d+2)/2}` for `t > 0`. -/
theorem abs_hessG_le (i j : Fin d) : ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, 0 < t → ∀ x : Euc d,
    |hessG i j t x| ≤ C * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 2) / 2)) := by
  obtain ⟨C, hC, h⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le_parabolic d 2
  refine ⟨C, hC, fun {t} ht x => (abs_hessG_le_norm i j t x).trans ?_⟩
  have := h ht x
  simpa using this

/-- **Small-time bound.** `|∂_i∂_j G_t(x)| ≤ C t (t + |x|²)^{-(d+4)/2}` for `t > 0`. -/
theorem abs_hessG_le_mul (i j : Fin d) : ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, 0 < t → ∀ x : Euc d,
    |hessG i j t x| ≤ C * t * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_gaussKernel_one_le (d := d) 2
    (m := (d : ℝ) + 4) (by positivity)
  refine ⟨C, hC, fun {t} ht x => ?_⟩
  set z := t ^ (-(1 : ℝ) / 2) • x
  have hz : |hessProfile i j z| ≤ C * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2) :=
    (abs_hessG_le_norm i j 1 z).trans (h z)
  have hsplit : t ^ (-(((d : ℝ) + 2) / 2)) = t * t ^ (-(((d : ℝ) + 4) / 2)) := by
    rw [show -(((d : ℝ) + 2) / 2) = 1 + -(((d : ℝ) + 4) / 2) by ring, Real.rpow_add ht,
      Real.rpow_one]
  rw [hessG_eq_scale i j ht, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), hsplit]
  calc t * t ^ (-(((d : ℝ) + 4) / 2)) * |hessProfile i j z|
      ≤ t * t ^ (-(((d : ℝ) + 4) / 2)) * (C * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2)) := by
        gcongr
    _ = C * t * (t ^ (-(((d : ℝ) + 4) / 2)) * (1 + ‖z‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2))) := by
        rw [neg_div]; ring
    _ = C * t * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := by
        rw [rpow_mul_one_add_scale ht x]

end Size

section TimeDeriv

theorem differentiable_iteratedFDeriv_gaussKernel (n : ℕ) (t : ℝ) :
    Differentiable ℝ (iteratedFDeriv ℝ n (gaussKernel d t)) :=
  (Gaussian.contDiff_gaussKernel (n := ⊤) t).differentiable_iteratedFDeriv
    (by exact_mod_cast WithTop.coe_lt_top (n : ℕ∞))

/-- The profile `φ` has derivative `(D³G₁(z) v)[eᵢ, eⱼ]`. -/
theorem hasFDerivAt_hessProfile (i j : Fin d) (z : Euc d) :
    HasFDerivAt (hessProfile i j)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ ![ev i, ev j]).comp
        (fderiv ℝ (iteratedFDeriv ℝ 2 (gaussKernel d 1)) z)) z := by
  have h := ((differentiable_iteratedFDeriv_gaussKernel (d := d) 2 1) z).hasFDerivAt
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ ![ev i, ev j]).hasFDerivAt.comp
    z h

theorem norm_fderiv_hessProfile_apply_le (i j : Fin d) (z v : Euc d) :
    |((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ ![ev i, ev j]).comp
        (fderiv ℝ (iteratedFDeriv ℝ 2 (gaussKernel d 1)) z)) v| ≤
      ‖iteratedFDeriv ℝ 3 (gaussKernel d 1) z‖ * ‖v‖ := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
  refine (abs_apply_ev_le _ i j).trans ?_
  rw [← norm_fderiv_iteratedFDeriv]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **Time derivative bound.** For `t > 0`, `t ↦ ∂_i∂_j G_t(x)` is differentiable with
`|∂_t ∂_i∂_j G_t(x)| ≤ C (t + |x|²)^{-(d+4)/2}`. -/
theorem exists_hasDerivAt_hessG (i j : Fin d) : ∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, ∀ {t : ℝ}, 0 < t →
    ∃ g' : ℝ, HasDerivAt (fun τ => hessG i j τ x) g' t ∧
      |g'| ≤ C * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := by
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_iteratedFDeriv_gaussKernel_one_le (d := d) 2
    (m := (d : ℝ) + 4) (by positivity)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_iteratedFDeriv_gaussKernel_one_le (d := d) 3
    (m := (d : ℝ) + 5) (by positivity)
  refine ⟨((d : ℝ) + 2) / 2 * C₂ + 1 / 2 * C₃, by positivity, fun x {t} ht => ?_⟩
  set a : ℝ := ((d : ℝ) + 2) / 2 with ha
  set L := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ ![ev i, ev j]).comp
        (fderiv ℝ (iteratedFDeriv ℝ 2 (gaussKernel d 1)) (t ^ (-(1 : ℝ) / 2) • x)) with hL
  -- derivatives of the two scalar factors
  have hp : HasDerivAt (fun τ : ℝ => τ ^ (-a)) (-a * t ^ (-a - 1)) t := by
    simpa using Real.hasDerivAt_rpow_const (p := -a) (x := t) (Or.inl ht.ne')
  have hc : HasDerivAt (fun τ : ℝ => τ ^ (-(1 : ℝ) / 2)) (-(1 : ℝ) / 2 * t ^ (-(1 : ℝ) / 2 - 1))
      t := Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hφ : HasDerivAt (fun τ : ℝ => hessProfile i j (τ ^ (-(1 : ℝ) / 2) • x))
      (L ((-(1 : ℝ) / 2 * t ^ (-(1 : ℝ) / 2 - 1)) • x)) t :=
    (hasFDerivAt_hessProfile i j _).comp_hasDerivAt t (hc.smul_const x)
  have hprod := hp.mul hφ
  refine ⟨_, hprod.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [lt_mem_nhds ht] with τ hτ
    exact hessG_eq_scale i j hτ x
  -- the bound
  set z := t ^ (-(1 : ℝ) / 2) • x with hz
  have hz2 : |hessProfile i j z| ≤ C₂ * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2) :=
    (abs_hessG_le_norm i j 1 z).trans (h₂ z)
  have hz3 : |L ((-(1 : ℝ) / 2 * t ^ (-(1 : ℝ) / 2 - 1)) • x)| ≤
      ‖iteratedFDeriv ℝ 3 (gaussKernel d 1) z‖ * ‖(-(1 : ℝ) / 2 * t ^ (-(1 : ℝ) / 2 - 1)) • x‖ :=
    norm_fderiv_hessProfile_apply_le i j z _
  have hnorm : ‖(-(1 : ℝ) / 2 * t ^ (-(1 : ℝ) / 2 - 1)) • x‖ = 1 / 2 * t⁻¹ * ‖z‖ := by
    rw [hz, norm_smul, norm_smul, Real.norm_eq_abs, abs_mul, Real.norm_of_nonneg (by positivity),
      abs_of_pos (Real.rpow_pos_of_pos ht _)]
    rw [show (-(1 : ℝ) / 2 - 1) = -1 + -(1 : ℝ) / 2 by ring, Real.rpow_add ht, Real.rpow_neg_one]
    norm_num; ring
  have hzle : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hw : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have h3z : ‖iteratedFDeriv ℝ 3 (gaussKernel d 1) z‖ * ‖z‖ ≤
      C₃ * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2) := by
    calc ‖iteratedFDeriv ℝ 3 (gaussKernel d 1) z‖ * ‖z‖
        ≤ C₃ * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 5) / 2) * (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) :=
          mul_le_mul (h₃ z) hzle (norm_nonneg _) (by positivity)
      _ = C₃ * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2) := by
          rw [mul_assoc, ← Real.rpow_add hw]; congr 2; ring
  have hta : t ^ (-a - 1) = t ^ (-(((d : ℝ) + 4) / 2)) := by congr 1; rw [ha]; ring
  have hta' : t ^ (-a) * t⁻¹ = t ^ (-(((d : ℝ) + 4) / 2)) := by
    rw [← hta, show -a - 1 = -a + -1 by ring, Real.rpow_add ht, Real.rpow_neg_one]
  have hpos : 0 < t ^ (-(((d : ℝ) + 4) / 2)) := Real.rpow_pos_of_pos ht _
  have hfin : t ^ (-(((d : ℝ) + 4) / 2)) * (1 + ‖z‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) =
      (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := rpow_mul_one_add_scale ht x _
  calc |-a * t ^ (-a - 1) * hessProfile i j z + t ^ (-a) * L ((-(1 : ℝ) / 2 *
        t ^ (-(1 : ℝ) / 2 - 1)) • x)|
      ≤ a * t ^ (-(((d : ℝ) + 4) / 2)) * |hessProfile i j z| +
          t ^ (-a) * (‖iteratedFDeriv ℝ 3 (gaussKernel d 1) z‖ * (1 / 2 * t⁻¹ * ‖z‖)) := by
        refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
        · rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < a),
            abs_of_pos (Real.rpow_pos_of_pos ht _), hta]
        · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), ← hnorm]
          gcongr
    _ = a * t ^ (-(((d : ℝ) + 4) / 2)) * |hessProfile i j z| +
          1 / 2 * t ^ (-(((d : ℝ) + 4) / 2)) *
            (‖iteratedFDeriv ℝ 3 (gaussKernel d 1) z‖ * ‖z‖) := by
        rw [← hta']; ring
    _ ≤ a * t ^ (-(((d : ℝ) + 4) / 2)) * (C₂ * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2)) +
          1 / 2 * t ^ (-(((d : ℝ) + 4) / 2)) * (C₃ * (1 + ‖z‖ ^ 2) ^ (-((d : ℝ) + 4) / 2)) := by
        gcongr
    _ = (a * C₂ + 1 / 2 * C₃) *
          (t ^ (-(((d : ℝ) + 4) / 2)) * (1 + ‖z‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2))) := by
        rw [neg_div]; ring
    _ = _ := by rw [hfin]

end TimeDeriv

section Lipschitz

/-- **Spatial mean-value bound.** If `R ≤ t + |x - θy|²` for `θ ∈ [0,1]`, then
`|∂_i∂_j G_t(x - y) - ∂_i∂_j G_t(x)| ≤ C |y| R^{-(d+3)/2}`. -/
theorem abs_hessG_sub_le (i j : Fin d) : ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, 0 < t →
    ∀ (x y : Euc d) {R : ℝ}, 0 < R → (∀ θ ∈ Icc (0 : ℝ) 1, R ≤ t + ‖x - θ • y‖ ^ 2) →
      |hessG i j t (x - y) - hessG i j t x| ≤ C * ‖y‖ * R ^ (-(((d : ℝ) + 3) / 2)) := by
  obtain ⟨C, hC, h⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le_parabolic d 3
  refine ⟨C, hC, fun {t} ht x y {R} hR hpath => ?_⟩
  have hmv : ‖iteratedFDeriv ℝ 2 (gaussKernel d t) (x - y) -
      iteratedFDeriv ℝ 2 (gaussKernel d t) x‖ ≤ C * R ^ (-(((d : ℝ) + 3) / 2)) * ‖(x - y) - x‖ := by
    refine Convex.norm_image_sub_le_of_norm_fderiv_le (s := segment ℝ x (x - y))
      (fun w _ => (differentiable_iteratedFDeriv_gaussKernel 2 t) w) (fun w hw => ?_)
      (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    rw [norm_fderiv_iteratedFDeriv]
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    have hw' : x + θ • (x - y - x) = x - θ • y := by
      rw [show x - y - x = -y by abel, smul_neg]; abel
    dsimp only
    rw [hw']
    refine (h ht _).trans ?_
    have hRle := hpath θ hθ
    have : (t + ‖x - θ • y‖ ^ 2) ^ (-(((d : ℝ) + 3) / 2)) ≤ R ^ (-(((d : ℝ) + 3) / 2)) :=
      Real.rpow_le_rpow_of_nonpos hR hRle (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
    norm_num at this ⊢
    gcongr
  have hsub : hessG i j t (x - y) - hessG i j t x =
      (iteratedFDeriv ℝ 2 (gaussKernel d t) (x - y) -
        iteratedFDeriv ℝ 2 (gaussKernel d t) x) ![ev i, ev j] := by
    simp [hessG]
  rw [hsub]
  refine (abs_apply_ev_le _ i j).trans (hmv.trans (le_of_eq ?_))
  rw [show x - y - x = -y by abel, norm_neg]; ring

/-- The kernel vanishes at nonpositive times, and the small-time bound in kernel form. -/
theorem abs_causalKernel_le_mul (i j : Fin d) : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (x : Euc d), 0 < t →
    |causalKernel i j (t, x)| ≤ C * t * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := by
  obtain ⟨C, hC, h⟩ := abs_hessG_le_mul (d := d) i j
  exact ⟨C, hC, fun t x ht => by rw [causalKernel_of_pos i j (X := (t, x)) ht]; exact h ht x⟩

/-- **Time-Lipschitz bound across `t = 0`.** If `R ≤ |τ| + |x|²` for every `τ` between `t₁`
and `t₂`, then `|K(t₂,x) - K(t₁,x)| ≤ C |t₂ - t₁| R^{-(d+4)/2}`. -/
theorem abs_causalKernel_time_sub_le (i j : Fin d) : ∃ C : ℝ, 0 < C ∧
    ∀ (x : Euc d) (t₁ t₂ : ℝ) {R : ℝ}, 0 < R → (∀ τ ∈ uIcc t₁ t₂, R ≤ |τ| + ‖x‖ ^ 2) →
      |causalKernel i j (t₂, x) - causalKernel i j (t₁, x)| ≤
        C * |t₂ - t₁| * R ^ (-(((d : ℝ) + 4) / 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_hasDerivAt_hessG (d := d) i j
  obtain ⟨C₂, hC₂, h₂⟩ := abs_causalKernel_le_mul (d := d) i j
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  have hexp : -(((d : ℝ) + 4) / 2) ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the ordered case
  have key : ∀ (x : Euc d) (t₁ t₂ : ℝ) {R : ℝ}, 0 < R → t₁ ≤ t₂ →
      (∀ τ ∈ Icc t₁ t₂, R ≤ |τ| + ‖x‖ ^ 2) →
      |causalKernel i j (t₂, x) - causalKernel i j (t₁, x)| ≤
        max C₁ C₂ * |t₂ - t₁| * R ^ (-(((d : ℝ) + 4) / 2)) := by
    intro x t₁ t₂ R hR h12 hpath
    have hRpos : 0 ≤ R ^ (-(((d : ℝ) + 4) / 2)) := (Real.rpow_pos_of_pos hR _).le
    rcases le_or_gt t₂ 0 with h2 | h2
    · rw [causalKernel_of_nonpos i j (X := (t₂, x)) h2,
        causalKernel_of_nonpos i j (X := (t₁, x)) (h12.trans h2), sub_zero, abs_zero]
      positivity
    rcases le_or_gt t₁ 0 with h1 | h1
    · -- straddling case
      rw [causalKernel_of_nonpos i j (X := (t₁, x)) h1, sub_zero]
      have hR0 : R ≤ ‖x‖ ^ 2 := by
        have := hpath 0 ⟨h1, h2.le⟩
        simpa using this
      have hb := h₂ t₂ x h2
      have hmono : (t₂ + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) ≤ R ^ (-(((d : ℝ) + 4) / 2)) :=
        Real.rpow_le_rpow_of_nonpos hR (by linarith) hexp
      have ht : t₂ ≤ |t₂ - t₁| := by rw [abs_of_nonneg (by linarith)]; linarith
      calc |causalKernel i j (t₂, x)| ≤ C₂ * t₂ * (t₂ + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := hb
        _ ≤ max C₁ C₂ * |t₂ - t₁| * R ^ (-(((d : ℝ) + 4) / 2)) := by
          gcongr
          exact le_max_right _ _
    · -- both positive: mean value theorem
      have hder : ∀ τ ∈ Icc t₁ t₂, HasDerivWithinAt (fun s => causalKernel i j (s, x))
          (deriv (fun s => hessG i j s x) τ) (Icc t₁ t₂) τ := by
        intro τ hτ
        have hτ0 : 0 < τ := h1.trans_le hτ.1
        obtain ⟨g', hg', -⟩ := h₁ x hτ0
        have hd : HasDerivAt (fun s => hessG i j s x) (deriv (fun s => hessG i j s x) τ) τ := by
          rw [hg'.deriv]; exact hg'
        refine (hd.congr_of_eventuallyEq ?_).hasDerivWithinAt
        filter_upwards [lt_mem_nhds hτ0] with s hs
        exact causalKernel_of_pos i j (X := (s, x)) hs
      have hbd : ∀ τ ∈ Icc t₁ t₂, ‖deriv (fun s => hessG i j s x) τ‖ ≤
          max C₁ C₂ * R ^ (-(((d : ℝ) + 4) / 2)) := by
        intro τ hτ
        have hτ0 : 0 < τ := h1.trans_le hτ.1
        obtain ⟨g', hg', hb⟩ := h₁ x hτ0
        rw [hg'.deriv, Real.norm_eq_abs]
        have hRτ : R ≤ τ + ‖x‖ ^ 2 := by
          have := hpath τ hτ
          rwa [abs_of_pos hτ0] at this
        calc |g'| ≤ C₁ * (τ + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 4) / 2)) := hb
          _ ≤ max C₁ C₂ * R ^ (-(((d : ℝ) + 4) / 2)) :=
            mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_nonpos hR hRτ hexp)
              (by positivity) (hC₁.le.trans (le_max_left _ _))
      have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Icc t₁ t₂)
        (left_mem_Icc.2 h12) (right_mem_Icc.2 h12)
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
      calc _ ≤ _ := this
        _ = _ := by ring
  intro x t₁ t₂ R hR hpath
  rcases le_total t₁ t₂ with h12 | h21
  · exact key x t₁ t₂ hR h12 (fun τ hτ => hpath τ (Icc_subset_uIcc hτ))
  · have := key x t₂ t₁ hR h21 (fun τ hτ => hpath τ (Icc_subset_uIcc' hτ))
    rw [abs_sub_comm (causalKernel i j (t₂, x)), abs_sub_comm t₂ t₁]
    exact this

/-- **Pointwise Hörmander bound.** Let `X = (t,x)`, `Y = (s,y)` and `R > 0`. If
`R ≤ |τ| + |x|²` for `τ` between `t - s` and `t`, and `R ≤ |t - s| + |x - θy|²` for
`θ ∈ [0,1]`, then `|K(X - Y) - K(X)| ≤ C₁ |y| R^{-(d+3)/2} + C₂ |s| R^{-(d+4)/2}`. -/
theorem abs_causalKernel_sub_le (i j : Fin d) : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (X Y : PS d) {R : ℝ}, 0 < R →
      (∀ τ ∈ uIcc (X.1 - Y.1) X.1, R ≤ |τ| + ‖X.2‖ ^ 2) →
      (∀ θ ∈ Icc (0 : ℝ) 1, R ≤ |X.1 - Y.1| + ‖X.2 - θ • Y.2‖ ^ 2) →
      |causalKernel i j (X - Y) - causalKernel i j X| ≤
        C₁ * ‖Y.2‖ * R ^ (-(((d : ℝ) + 3) / 2)) + C₂ * |Y.1| * R ^ (-(((d : ℝ) + 4) / 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := abs_hessG_sub_le (d := d) i j
  obtain ⟨C₂, hC₂, h₂⟩ := abs_causalKernel_time_sub_le (d := d) i j
  refine ⟨C₁, C₂, hC₁, hC₂, fun X Y R hR htime hspace => ?_⟩
  obtain ⟨t, x⟩ := X
  obtain ⟨s, y⟩ := Y
  simp only at htime hspace ⊢
  have hXY : (t, x) - (s, y) = (t - s, x - y) := rfl
  rw [hXY]
  have hsplit : causalKernel i j (t - s, x - y) - causalKernel i j (t, x) =
      (causalKernel i j (t - s, x - y) - causalKernel i j (t - s, x)) +
        (causalKernel i j (t - s, x) - causalKernel i j (t, x)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rcases le_or_gt (t - s) 0 with hts | hts
    · rw [causalKernel_of_nonpos i j (X := (t - s, x - y)) hts,
        causalKernel_of_nonpos i j (X := (t - s, x)) hts, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hC₁.le (norm_nonneg _)) (Real.rpow_pos_of_pos hR _).le
    · rw [causalKernel_of_pos i j (X := (t - s, x - y)) hts,
        causalKernel_of_pos i j (X := (t - s, x)) hts]
      refine h₁ hts x y hR fun θ hθ => ?_
      have := hspace θ hθ
      rwa [abs_of_pos hts] at this
  · have := h₂ x t (t - s) hR (fun τ hτ => htime τ (by rwa [uIcc_comm] at hτ))
    rwa [show t - s - t = -s by ring, abs_neg] at this

end Lipschitz

section Symmetry

/-- `∂_i∂_j G_t` is even in `x`. -/
theorem hessG_neg (i j : Fin d) (t : ℝ) (x : Euc d) : hessG i j t (-x) = hessG i j t x := by
  have h := Gaussian.iteratedFDeriv_comp_smul 2 (gaussKernel d t) 1 (-1) x
  have hfun : (fun z : Euc d => (1 : ℝ) • gaussKernel d t ((-1 : ℝ) • z)) = gaussKernel d t := by
    funext z; rw [one_smul, neg_one_smul, Gaussian.gaussKernel_neg]
  rw [hfun] at h
  unfold hessG
  rw [h, neg_one_smul]
  simp

theorem causalKernel_neg_space (i j : Fin d) (t : ℝ) (x : Euc d) :
    causalKernel i j (t, -x) = causalKernel i j (t, x) := by
  unfold causalKernel
  simp only
  split_ifs
  · exact hessG_neg i j t x
  · rfl

end Symmetry

section Measurability

theorem continuous_hessProfile (i j : Fin d) : Continuous (hessProfile i j) :=
  (hasFDerivAt_hessProfile (d := d) i j · |>.continuousAt) |> continuous_iff_continuousAt.2

theorem measurable_causalKernel (i j : Fin d) : Measurable (causalKernel i j) := by
  have heq : causalKernel i j = fun X : PS d => if 0 < X.1 then
      X.1 ^ (-(((d : ℝ) + 2) / 2)) * hessProfile i j (X.1 ^ (-(1 : ℝ) / 2) • X.2) else 0 := by
    funext X
    unfold causalKernel
    split_ifs with h
    · exact hessG_eq_scale i j h X.2
    · rfl
  rw [heq]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  exact (measurable_fst.pow_const _).mul ((continuous_hessProfile i j).measurable.comp
    ((measurable_fst.pow_const _).smul measurable_snd))

end Measurability

end UnforcedLeray.Parabolic
