import UnforcedLeray.Lib.Gaussian.IteratedDeriv

/-!
# `L^p` norms of heat-kernel derivatives (INF22 G3, INF04 T2)


target G3, and `scoping/INF04-INF05-Heat.md` §5 T2 (`eLpNorm_iteratedDeriv_lineGauss`, there in
1D; here in every dimension and for every order). Decision D14.

The parabolic scaling `G_t(x) = t^{-d/2} G_1(t^{-1/2}x)` gives the exact identity
`‖D^n G_t‖_{L^p} = t^{-(d+n)/2 + d/(2p)} ‖D^n G_1‖_{L^p}` (`eLpNorm_iteratedFDeriv_gaussKernel`)
and `‖D^n G_1‖_{L^p} < ∞` by G1, hence the bound
`‖D^n G_t‖_{L^p(ℝ^d)} ≤ C t^{-n/2 - d(1-1/p)/2}` for every `p ∈ (0, ∞]`
(`eLpNorm_iteratedFDeriv_gaussKernel_le`). Uses: B0163/B0164 (tex 2454–2467, `d = 1`,
`p ∈ {2, ∞}`), B0181, B0448–B0450 (tex 7618–7690), B0722 (tex 466–492).

Exponent convention: `(1/p).toReal` is `1/p` for `0 < p < ∞`, and `0` for `p = ∞`
(`1/∞ = 0` in `ℝ≥0∞`), which is the correct exponent for `L^∞`.

The scaling rule `iteratedFDeriv_comp_smul` is copied from the NonUniqueEuler reference,
`NonUniqueEuler/P/Infra/CkNorm/Scaling.lean` (lines 28–80, namespace renamed).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real Set
open scoped ENNReal Nat

section Scaling
-- Copied from `NonUniqueEuler/P/Infra/CkNorm/Scaling.lean` (NonUniqueEuler reference clone).

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Right composition with `z ↦ c • z`, `c ≠ 0`. -/
theorem iteratedFDeriv_comp_smul_right_of_ne (q : ℕ) (h : E → F) {c : ℝ} (hc : c ≠ 0) (y : E) :
    iteratedFDeriv ℝ q (fun z => h (c • z)) y = c ^ q • iteratedFDeriv ℝ q h (c • y) := by
  set g : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc) with hgdef
  have hg : ∀ z, g z = c • z := fun z => rfl
  have hfun : (fun z => h (c • z)) = h ∘ g := by
    funext z
    simp [hg]
  have key := g.iteratedFDerivWithin_comp_right h uniqueDiffOn_univ (mem_univ (g y)) q
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at key
  rw [hfun, key, hg]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearEquiv.coe_coe, hg]
  rw [show (fun i => c • m i) = fun i => (fun _ : Fin q => c) i • m i from rfl,
    ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

/-- Left multiplication by a scalar commutes with `iteratedFDeriv` (no regularity needed). -/
theorem iteratedFDeriv_const_smul_left (q : ℕ) (f : E → F) (a : ℝ) (y : E) :
    iteratedFDeriv ℝ q (fun z => a • f z) y = a • iteratedFDeriv ℝ q f y := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul]
    cases q with
    | zero => ext m; simp
    | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; rfl
  · set g : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 a ha) with hgdef
    have hg : ∀ v, g v = a • v := fun v => rfl
    have hfun : (fun z => a • f z) = g ∘ f := by
      funext z
      simp [hg]
    rw [hfun, g.iteratedFDeriv_comp_left]
    ext m
    simp [hg]

/-- The scaling rule `∇^q (a V(c ·))(y) = a c^q (∇^q V)(c y)` (no regularity hypothesis). -/
theorem iteratedFDeriv_comp_smul (q : ℕ) (h : E → F) (a c : ℝ) (y : E) :
    iteratedFDeriv ℝ q (fun z => a • h (c • z)) y =
      (a * c ^ q) • iteratedFDeriv ℝ q h (c • y) := by
  rw [iteratedFDeriv_const_smul_left q (fun z => h (c • z)) a y, mul_smul]
  congr 1
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul]
    cases q with
    | zero => ext m; simp
    | succ n =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp
  · exact iteratedFDeriv_comp_smul_right_of_ne q h hc y

end Scaling

variable {d : ℕ}

/-- Parabolic scaling of the heat kernel: `G_t(x) = t^{-d/2} G_1(t^{-1/2} x)` for `t > 0`. -/
theorem gaussKernel_eq_scale {t : ℝ} (ht : 0 < t) :
    gaussKernel d t = fun x => t ^ (-(d : ℝ) / 2) • gaussKernel d 1 (t ^ (-(1 : ℝ) / 2) • x) := by
  funext x
  have hc : (t ^ (-(1 : ℝ) / 2)) ^ 2 = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num [Real.rpow_neg_one]
  simp only [gaussKernel, smul_eq_mul, norm_smul, Real.norm_of_nonneg
    (Real.rpow_pos_of_pos ht _).le, mul_pow, hc]
  rw [show 4 * π * t = t * (4 * π * 1) by ring, Real.mul_rpow ht.le (by positivity)]
  have : -‖x‖ ^ 2 / (4 * t) = -(t⁻¹ * ‖x‖ ^ 2) / (4 * 1) := by field_simp
  rw [this]; ring

/-- Pointwise scaling of the derivatives:
`‖D^n G_t(x)‖ = t^{-(d+n)/2} ‖D^n G_1(t^{-1/2}x)‖`. -/
theorem norm_iteratedFDeriv_gaussKernel_eq_scale (n : ℕ) {t : ℝ} (ht : 0 < t) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (gaussKernel d t) x‖ =
      t ^ (-(((d : ℝ) + n) / 2)) *
        ‖iteratedFDeriv ℝ n (gaussKernel d 1) (t ^ (-(1 : ℝ) / 2) • x)‖ := by
  rw [gaussKernel_eq_scale ht, iteratedFDeriv_comp_smul, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1; ring

/-- `D^n G_t ∈ L^p(ℝ^d)` for every `p` and `t > 0` (it is dominated by a multiple of `G_{2t}`). -/
theorem memLp_iteratedFDeriv_gaussKernel (n : ℕ) {t : ℝ} (ht : 0 < t) (p : ℝ≥0∞) :
    MemLp (iteratedFDeriv ℝ n (gaussKernel d t)) p volume := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_gaussKernel_le d n
  have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ n (gaussKernel d t)) volume :=
    ((contDiff_gaussKernel (n := n) t).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
  set K := C * t ^ (-(((d : ℝ) + n) / 2)) * (4 * π * (2 * t)) ^ ((d : ℝ) / 2)
  refine ((memLp_gaussKernel (d := d) (by positivity : 0 < 2 * t) p).const_mul K).of_le hmeas
    (Filter.Eventually.of_forall fun x => ?_)
  refine (hC ht x).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (gaussKernel_nonneg (by positivity) x)),
    gaussKernel]
  have h1 : (4 * π * (2 * t)) ^ ((d : ℝ) / 2) * (4 * π * (2 * t)) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity)]; simp [neg_div]
  have h2 : -‖x‖ ^ 2 / (8 * t) = -‖x‖ ^ 2 / (4 * (2 * t)) := by ring_nf
  rw [h2]
  calc C * t ^ (-(((d : ℝ) + n) / 2)) * Real.exp (-‖x‖ ^ 2 / (4 * (2 * t)))
      = C * t ^ (-(((d : ℝ) + n) / 2)) * ((4 * π * (2 * t)) ^ ((d : ℝ) / 2) *
          (4 * π * (2 * t)) ^ (-(d : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (4 * (2 * t))) := by
        rw [h1, mul_one]
    _ = _ := by ring

/-- Dilation of `L^p` norms on `ℝ^d`: `‖F(c ·)‖_p = c^{-d/p} ‖F‖_p` for `c > 0`. -/
theorem eLpNorm_comp_smul_of_pos {G : Type*} [NormedAddCommGroup G] (F : Euc d → G)
    (hF : Continuous F) {c : ℝ} (hc : 0 < c) (p : ℝ≥0∞) :
    eLpNorm (fun x => F (c • x)) p volume =
      ENNReal.ofReal (c ^ (-(d : ℝ) * (1 / p).toReal)) * eLpNorm F p volume := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure (Euc d))) hc.ne'
  have hm : AEMeasurable (fun x : Euc d => c • x) volume := (continuous_const_smul c).aemeasurable
  have hne : ENNReal.ofReal |(c ^ Module.finrank ℝ (Euc d))⁻¹| ≠ 0 := by
    rw [finrank_euc]; simp [hc.ne']
  rw [show (fun x => F (c • x)) = F ∘ (fun x => c • x) from rfl,
    ← eLpNorm_map_measure hF.aestronglyMeasurable hm, hmap,
    eLpNorm_smul_measure_of_ne_zero hne, smul_eq_mul, finrank_euc,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hc.le,
    ← Real.rpow_mul hc.le]

/-- **INF04 T2 / INF22 G3, exact form.** For `t > 0` and every `p`,
`‖D^n G_t‖_{L^p} = t^{-(d+n)/2 + (d/2)(1/p)} ‖D^n G_1‖_{L^p}`. -/
theorem eLpNorm_iteratedFDeriv_gaussKernel (n : ℕ) {t : ℝ} (ht : 0 < t) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ n (gaussKernel d t)) p volume =
      ENNReal.ofReal (t ^ (-(((d : ℝ) + n) / 2) + (d : ℝ) / 2 * (1 / p).toReal)) *
        eLpNorm (iteratedFDeriv ℝ n (gaussKernel d 1)) p volume := by
  have hcont : Continuous (fun y => ‖iteratedFDeriv ℝ n (gaussKernel d 1) y‖) :=
    ((contDiff_gaussKernel (n := n) 1).continuous_iteratedFDeriv le_rfl).norm
  have hc : 0 < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos ht _
  rw [← eLpNorm_norm (iteratedFDeriv ℝ n (gaussKernel d t)), ← eLpNorm_norm (iteratedFDeriv ℝ n
    (gaussKernel d 1))]
  simp_rw [norm_iteratedFDeriv_gaussKernel_eq_scale n ht]
  rw [show (fun x : Euc d => t ^ (-(((d : ℝ) + n) / 2)) *
      ‖iteratedFDeriv ℝ n (gaussKernel d 1) (t ^ (-(1 : ℝ) / 2) • x)‖) =
      (t ^ (-(((d : ℝ) + n) / 2))) • (fun x : Euc d =>
        ‖iteratedFDeriv ℝ n (gaussKernel d 1) (t ^ (-(1 : ℝ) / 2) • x)‖) from rfl,
    eLpNorm_const_smul, eLpNorm_comp_smul_of_pos _ hcont hc, ← mul_assoc,
    Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 3; ring

/-- `‖D^n G_1‖_{L^p} < ∞`. -/
theorem eLpNorm_iteratedFDeriv_gaussKernel_one_lt_top (n : ℕ) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ n (gaussKernel d 1)) p volume < ∞ :=
  (memLp_iteratedFDeriv_gaussKernel n one_pos p).eLpNorm_lt_top

/-- The constant `‖D^n G_1‖_{L^p(ℝ^d)}` (INF04 T2's `lineConst` for `d = 1`). -/
def derivLpConst (d n : ℕ) (p : ℝ≥0∞) : ℝ :=
  (eLpNorm (iteratedFDeriv ℝ n (gaussKernel d 1)) p volume).toReal

/-- **INF22 G3 / INF04 T2.** `‖D^n G_t‖_{L^p(ℝ^d)} = C t^{-n/2 - (d/2)(1 - 1/p)}` with
`C = derivLpConst d n p`, for `t > 0` and every `p ∈ [0, ∞]` (real-valued form). -/
theorem eLpNorm_iteratedFDeriv_gaussKernel_toReal (n : ℕ) {t : ℝ} (ht : 0 < t) (p : ℝ≥0∞) :
    (eLpNorm (iteratedFDeriv ℝ n (gaussKernel d t)) p volume).toReal =
      derivLpConst d n p * t ^ (-(n : ℝ) / 2 - (d : ℝ) / 2 * (1 - (1 / p).toReal)) := by
  rw [eLpNorm_iteratedFDeriv_gaussKernel n ht, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), derivLpConst, mul_comm]
  congr 2; ring

/-- **INF22 G3** in the scoping note's form:
`‖D^n G_t‖_{L^p(ℝ^d)} ≤ C t^{-n/2 - d(1-1/p)/2}` uniformly in `t > 0`. -/
theorem eLpNorm_iteratedFDeriv_gaussKernel_le (d n : ℕ) (p : ℝ≥0∞) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {t : ℝ}, 0 < t → eLpNorm (iteratedFDeriv ℝ n (gaussKernel d t)) p volume ≤
      ENNReal.ofReal (C * t ^ (-(n : ℝ) / 2 - (d : ℝ) / 2 * (1 - (1 / p).toReal))) := by
  refine ⟨derivLpConst d n p, ENNReal.toReal_nonneg, fun {t} ht => le_of_eq ?_⟩
  rw [← eLpNorm_iteratedFDeriv_gaussKernel_toReal n ht p, ENNReal.ofReal_toReal]
  exact ((memLp_iteratedFDeriv_gaussKernel n ht p).eLpNorm_lt_top).ne

end UnforcedLeray.Gaussian
