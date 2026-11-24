import UnforcedLeray.Lib.Train.PeriodizedVortex
import UnforcedLeray.Lib.Gaussian.IteratedDeriv
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# The Gaussian stream vortex `v₀ = ∇^⊥ψ₀` and its derivative bounds (INF16 T1, profile part)


target T1; blueprint unit **B0140** (`eq:st18-t00139`, `paper/main.tex` lines 2131–2140):
`ψ₀(q,η) = -2 e^{-(q²+η²)/4}`, `v₀ = ∇^⊥ψ₀ = e^{-(q²+η²)/4}(-η, q)` with
`∇^⊥ = (-∂_η, ∂_q)`, vorticity `ω₀ = (2 - |x|²/2) e^{-|x|²/4}`.

**Route.** `ψ₀ = -8π G₁ ∘ toVecL` with the heat kernel `G₁` of `Lib/Gaussian` (G1), so
`‖D^n ψ₀(w)‖ ≤ C_n e^{-|w|²/8}` (`norm_iteratedFDeriv_gaussKernel_le`, composed with the linear
coordinate map); `v₀ = perpL ∘ Dψ₀` for the continuous linear map `perpL φ = (-φ(0,1), φ(1,0))`,
so `‖D^j v₀(w)‖ ≤ C_j e^{-|w|²/8}` (`norm_iteratedFDeriv_v0_le`). Derivatives are Fréchet
derivatives on `ℝ × ℝ`, whose norm is the sup norm; the constants absorb the norm equivalence.

Main declarations: `gauss0`, `psi0`, `v0`, `omega0`, `perpL`, `v0_eq_perpL`,
`psi0_eq_gaussKernel`, `contDiff_psi0`, `contDiff_v0`, `norm_iteratedFDeriv_psi0_le`,
`norm_iteratedFDeriv_v0_le`, `v0_translate_bound`, `isoV_zero` (`V(·,0) = v₀`),
`omega0_abs_le` (`|ω₀| ≤ 4 e^{-|x|²/8}`), `weight_mul_exp_le` (polynomial weight absorption).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Train

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open Real

/-- The Gaussian factor `e^{-(q²+η²)/4}`. -/
def gauss0 (w : Plane) : ℝ := Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 4)

/-- The stream function `ψ₀(q,η) = -2 e^{-(q²+η²)/4}` (tex line 2134). -/
def psi0 (w : Plane) : ℝ := -2 * gauss0 w

/-- The velocity `v₀ = e^{-(q²+η²)/4}(-η, q)` (tex lines 2134–2136). -/
def v0 (w : Plane) : Vec := gauss0 w • toVec (-w.2, w.1)

/-- The vorticity `ω₀ = (2 - |x|²/2) e^{-|x|²/4}` (tex lines 2138–2139). -/
def omega0 (w : Plane) : ℝ := (2 - (w.1 ^ 2 + w.2 ^ 2) / 2) * gauss0 w

/-- The perpendicular gradient on covectors: `perpL φ = (-φ(0,1), φ(1,0))`, so that
`perpL (Dψ(w)) = ∇^⊥ψ(w) = (-∂_ηψ, ∂_qψ)`. -/
def perpL : (Plane →L[ℝ] ℝ) →L[ℝ] Vec :=
  (toVecL : (ℝ × ℝ) →L[ℝ] Vec).comp
    ((-(ContinuousLinearMap.apply ℝ ℝ ((0, 1) : Plane))).prod
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : Plane)))

theorem perpL_apply (φ : Plane →L[ℝ] ℝ) : perpL φ = toVec (-φ (0, 1), φ (1, 0)) := rfl

theorem gauss0_pos (w : Plane) : 0 < gauss0 w := Real.exp_pos _

theorem gauss0_neg (w : Plane) : gauss0 (-w) = gauss0 w := by
  simp [gauss0]

theorem psi0_eq_aux : psi0 = fun y : Plane =>
    -2 * Real.exp (-(1 / 4) * ((fun x : Plane => x.1 ^ 2) + fun x : Plane => x.2 ^ 2) y) := by
  funext y; simp only [psi0, gauss0, Pi.add_apply]; congr 2; ring

/-- The derivative of `ψ₀`: `Dψ₀(w) v = (q v₁ + η v₂) e^{-|w|²/4}`. -/
theorem fderiv_psi0_apply (w v : Plane) :
    fderiv ℝ psi0 w v = (w.1 * v.1 + w.2 * v.2) * gauss0 w := by
  have h1 := ((((hasFDerivAt_fst (p := w) (𝕜 := ℝ)).pow 2).add
    ((hasFDerivAt_snd (p := w) (𝕜 := ℝ)).pow 2)).const_mul (-(1 / 4) : ℝ)).exp.const_mul
      (-2 : ℝ)
  rw [psi0_eq_aux, h1.fderiv]
  have hg : gauss0 w = Real.exp (-(1 / 4) * (w.1 ^ 2 + w.2 ^ 2)) := by
    simp only [gauss0]; congr 1; ring
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, nsmul_eq_mul,
    Pi.add_apply, hg]
  norm_num; ring

theorem fderiv_psi0_apply_fst (w : Plane) : fderiv ℝ psi0 w (1, 0) = w.1 * gauss0 w := by
  rw [fderiv_psi0_apply]; ring

theorem fderiv_psi0_apply_snd (w : Plane) : fderiv ℝ psi0 w (0, 1) = w.2 * gauss0 w := by
  rw [fderiv_psi0_apply]; ring

/-- `v₀ = ∇^⊥ψ₀` (tex line 2135). -/
theorem v0_eq_perpL : v0 = fun w => perpL (fderiv ℝ psi0 w) := by
  funext w
  rw [perpL_apply, fderiv_psi0_apply_fst, fderiv_psi0_apply_snd, v0, ← toVec_smul]
  congr 1
  ext <;> simp only [Prod.smul_mk, smul_eq_mul] <;> ring

/-- `ψ₀ = -8π G₁ ∘ toVecL` with the heat kernel `G_t(x) = (4πt)^{-1} e^{-|x|²/(4t)}`. -/
theorem psi0_eq_gaussKernel :
    psi0 = (-8 * π) • (Gaussian.gaussKernel 2 1 ∘ (toVecL : (ℝ × ℝ) →L[ℝ] Vec)) := by
  funext w
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Gaussian.gaussKernel, psi0,
    gauss0, ContinuousLinearEquiv.coe_coe, toVecL_apply, norm_toVec_sq]
  have h : (4 * π * 1) ^ (-((2 : ℕ) : ℝ) / 2) = (4 * π)⁻¹ := by
    rw [show (-((2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one, mul_one]
  rw [h, mul_one]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring_nf

theorem contDiff_psi0 {n : WithTop ℕ∞} : ContDiff ℝ n psi0 := by
  rw [psi0_eq_gaussKernel]
  exact ContDiff.const_smul (-8 * π : ℝ) ((Gaussian.contDiff_gaussKernel 1).comp
    (toVecL : (ℝ × ℝ) →L[ℝ] Vec).contDiff)

theorem contDiff_fderiv_psi0 {n : WithTop ℕ∞} : ContDiff ℝ n (fderiv ℝ psi0) :=
  (contDiff_psi0 (n := ⊤)).fderiv_right le_top

theorem contDiff_v0 {n : WithTop ℕ∞} : ContDiff ℝ n v0 := by
  rw [v0_eq_perpL]
  exact perpL.contDiff.comp contDiff_fderiv_psi0

/-- **Gaussian bounds for every derivative of `ψ₀`:** `‖D^n ψ₀(w)‖ ≤ A_n e^{-(q²+η²)/8}`. -/
theorem norm_iteratedFDeriv_psi0_le (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ w : Plane,
    ‖iteratedFDeriv ℝ n psi0 w‖ ≤ A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) := by
  obtain ⟨C, hC, hb⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le 2 n
  set e : (ℝ × ℝ) →L[ℝ] Vec := (toVecL : (ℝ × ℝ) →L[ℝ] Vec)
  refine ⟨8 * π * (C * ‖e‖ ^ n), by positivity, fun w => ?_⟩
  have hG : ContDiff ℝ ⊤ (Gaussian.gaussKernel 2 1) := Gaussian.contDiff_gaussKernel 1
  rw [psi0_eq_gaussKernel, iteratedFDeriv_const_smul_apply
    ((hG.comp e.contDiff).contDiffAt.of_le le_top),
    e.iteratedFDeriv_comp_right hG w le_top, norm_smul]
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (Gaussian.gaussKernel 2 1) (e w)) (fun _ : Fin n => e)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := hb (t := 1) one_pos (e w)
  have hew : ‖e w‖ ^ 2 = w.1 ^ 2 + w.2 ^ 2 := norm_toVec_sq w
  rw [Real.one_rpow, mul_one, hew, mul_one] at h2
  have hnorm : ‖(-8 * π : ℝ)‖ = 8 * π := by
    rw [Real.norm_eq_abs, abs_of_neg (by nlinarith [Real.pi_pos])]; ring
  rw [hnorm]
  have hE := Real.exp_pos (-(w.1 ^ 2 + w.2 ^ 2) / 8)
  have hen : 0 ≤ ‖e‖ ^ n := by positivity
  calc 8 * π * ‖(iteratedFDeriv ℝ n (Gaussian.gaussKernel 2 1) (e w)).compContinuousLinearMap
        fun _ => e‖
      ≤ 8 * π * (‖iteratedFDeriv ℝ n (Gaussian.gaussKernel 2 1) (e w)‖ * ‖e‖ ^ n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 8 * π * (C * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) * ‖e‖ ^ n) := by gcongr
    _ = 8 * π * (C * ‖e‖ ^ n) * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) := by ring

/-- **Gaussian bounds for every derivative of `v₀`:** `‖D^j v₀(w)‖ ≤ A_j e^{-(q²+η²)/8}`. -/
theorem norm_iteratedFDeriv_v0_le (j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ w : Plane,
    ‖iteratedFDeriv ℝ j v0 w‖ ≤ A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) := by
  obtain ⟨A, hA, hb⟩ := norm_iteratedFDeriv_psi0_le (j + 1)
  refine ⟨‖perpL‖ * A, by positivity, fun w => ?_⟩
  have h1 := perpL.norm_iteratedFDeriv_comp_left (f := fderiv ℝ psi0) (x := w) (n := j)
    (N := ⊤) (contDiff_fderiv_psi0.contDiffAt) le_top
  rw [norm_iteratedFDeriv_fderiv] at h1
  have hv : v0 = perpL ∘ fderiv ℝ psi0 := v0_eq_perpL
  rw [hv]
  calc ‖iteratedFDeriv ℝ j (⇑perpL ∘ fderiv ℝ psi0) w‖
      ≤ ‖perpL‖ * ‖iteratedFDeriv ℝ (j + 1) psi0 w‖ := h1
    _ ≤ ‖perpL‖ * (A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8)) :=
        mul_le_mul_of_nonneg_left (hb w) (norm_nonneg perpL)
    _ = ‖perpL‖ * A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) := by ring

/-- `e^{-x²/8} ≤ K (1+|x|)^{-2}`. -/
theorem exp_neg_sq_div_eight_le_rpow : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
    Real.exp (-x ^ 2 / 8) ≤ K * (1 + |x|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := 2) (b := 1 / 8) (by norm_num)
    (by norm_num)
  refine ⟨4 * (1 + C), by positivity, fun x => ?_⟩
  have hx := hb |x| (abs_nonneg x)
  rw [sq_abs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hx
  have h1 : 0 < 1 + |x| := by positivity
  rw [Real.rpow_neg h1.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have he : Real.exp (-x ^ 2 / 8) = Real.exp (-(1 / 8 * x ^ 2)) := by congr 1; ring
  rw [he]
  have hE := Real.exp_pos (-(1 / 8 * x ^ 2))
  have hE1 : Real.exp (-(1 / 8 * x ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have hsq : (1 + |x|) ^ 2 ≤ 2 + 2 * |x| ^ 2 := by nlinarith [sq_nonneg (1 - |x|)]
  nlinarith [mul_le_mul_of_nonneg_right hsq hE.le, abs_nonneg x]

/-- The translate bound required by the periodization calculus (`Gaussian.contDiff_periodize`):
every derivative of `v₀` is `O((1+|q|)^{-2})`. -/
theorem v0_translate_bound (k : ℕ) : ∃ C : ℝ, ∀ z : Plane,
    ‖iteratedFDeriv ℝ k v0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := norm_iteratedFDeriv_v0_le k
  obtain ⟨K, hK, hk⟩ := exp_neg_sq_div_eight_le_rpow
  refine ⟨A * K, fun z => (hb z).trans ?_⟩
  have h1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ Real.exp (-z.1 ^ 2 / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg z.2])
  calc A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ A * (K * (1 + |z.1|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans (hk z.1)) hA
    _ = A * K * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

/-- At age `0` the isolated heat vortex is the datum profile: `V(·, 0) = v₀`. -/
theorem isoV_zero (ν : ℝ) : isoV ν 0 = v0 := by
  funext w
  rw [isoV_apply, v0, gauss0]
  simp [width]

theorem omega0_eq_eExp (w : Plane) : omega0 w = B0113.eExp 1 w := by
  simp only [omega0, gauss0, B0113.eExp, B0113.gw, GaussianVortex.radiusSq]
  congr 1
  · ring
  · congr 1; ring

/-- `|ω₀(x)| ≤ 4 e^{-|x|²/8}`. -/
theorem omega0_abs_le (w : Plane) :
    |omega0 w| ≤ 4 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * 2)) := by
  set r := w.1 ^ 2 + w.2 ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hsplit : gauss0 w = Real.exp (-r / 8) * Real.exp (-r / 8) := by
    rw [gauss0, ← Real.exp_add]; congr 1; ring
  have h8 : 1 + r / 8 ≤ Real.exp (r / 8) := by
    have := Real.add_one_le_exp (r / 8); linarith
  have hinv : Real.exp (-r / 8) * Real.exp (r / 8) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  have hE := Real.exp_pos (-r / 8)
  rw [omega0, abs_mul, abs_of_pos (gauss0_pos w), hsplit,
    show -r / (4 * 2) = -r / 8 by ring]
  have habs : |2 - r / 2| ≤ 2 + r / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hkey : |2 - r / 2| * Real.exp (-r / 8) ≤ 4 := by
    calc |2 - r / 2| * Real.exp (-r / 8) ≤ (4 * (1 + r / 8)) * Real.exp (-r / 8) :=
          mul_le_mul_of_nonneg_right (by linarith) hE.le
      _ ≤ (4 * Real.exp (r / 8)) * Real.exp (-r / 8) := by gcongr
      _ = 4 := by rw [mul_assoc, mul_comm (Real.exp _), hinv, mul_one]
  calc |2 - r / 2| * (Real.exp (-r / 8) * Real.exp (-r / 8))
      = (|2 - r / 2| * Real.exp (-r / 8)) * Real.exp (-r / 8) := by ring
    _ ≤ 4 * Real.exp (-r / 8) := mul_le_mul_of_nonneg_right hkey hE.le

/-- Polynomial weight absorption: `⟨η⟩^m e^{-η²/16} ≤ K_m` with `⟨η⟩^m = √((1+η²)^m)`. -/
theorem weight_mul_exp_le (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ,
    Real.sqrt ((1 + η ^ 2) ^ m) * Real.exp (-η ^ 2 / 16) ≤ K := by
  refine ⟨16 ^ m * (Real.exp 1 * m.factorial), by positivity, fun η => ?_⟩
  set t := η ^ 2 / 16 with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 : 1 ≤ (1 + η ^ 2) ^ m := one_le_pow₀ (by nlinarith [sq_nonneg η])
  have hsq : Real.sqrt ((1 + η ^ 2) ^ m) ≤ (1 + η ^ 2) ^ m := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h2 : (1 + η ^ 2) ^ m ≤ 16 ^ m * (1 + t) ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [ht]; nlinarith) m
  have h3 := Gaussian.pow_mul_exp_neg_le_factorial m (s := 1 + t) (by linarith)
  have he : Real.exp (-η ^ 2 / 16) = Real.exp 1 * Real.exp (-(1 + t)) := by
    rw [← Real.exp_add]; congr 1; rw [ht]; ring
  have hE := Real.exp_pos (-η ^ 2 / 16)
  calc Real.sqrt ((1 + η ^ 2) ^ m) * Real.exp (-η ^ 2 / 16)
      ≤ (16 ^ m * (1 + t) ^ m) * Real.exp (-η ^ 2 / 16) :=
        mul_le_mul_of_nonneg_right (hsq.trans h2) hE.le
    _ = 16 ^ m * (Real.exp 1 * ((1 + t) ^ m * Real.exp (-(1 + t)))) := by rw [he]; ring
    _ ≤ 16 ^ m * (Real.exp 1 * m.factorial) := by gcongr

end UnforcedLeray.Train
