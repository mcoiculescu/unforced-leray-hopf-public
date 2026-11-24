import UnforcedLeray.Lib.Gaussian.HeatDilation
import UnforcedLeray.Lib.Gaussian.LpNorm
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# The heat-dilation flow through the periodization (INF22 G7, item 5, second half)


target G7 item 5 and §2.10 rows B0317 (tex 6138–6147) and B0333 (tex 6317–6330): the exact
identity `(Δ - ∂_a)[a^{-2}q(x/√a)] = a^{-3}(Dq)(x/√a)`, `D = Δ + ½ y·∇ + 2` (tex 722, B0099),
passes through the periodization `P_c` (tex 6037–6045, B0314).

Conventions (decision D1): the plane is `ℝ × ℝ` with its sup norm, so the Laplacian is the
classical `Cyl.laplacian f = ∂_q²f + ∂_η²f` of `Lib/Cylinder/IBP.lean`, and `y·∇q(y)` is the
directional derivative `fderiv ℝ q y y`, which does not depend on the norm.

Main results:
* `laplacian_eq_iteratedFDeriv`: for `C²` functions, `Δf(z) = D²f(z)(e₁,e₁) + D²f(z)(e₂,e₂)`;
* `laplacian_heatDilation`, `hasDerivAt_heatDilation_param`, `laplacian_sub_deriv_heatDilation`:
  the single-function identities `Δ[a^{-2}q(·/√a)] = a^{-3}(Δq)(·/√a)`,
  `∂_a[a^{-2}q(x/√a)] = -a^{-3}(2q + ½y·∇q)(x/√a)` and their difference (B0317);
* `laplacian_periodize`: `Δ(P_c g) = P_c(Δg)` under translate bounds on `g`, `Dg`, `D²g`;
* `hasDerivAt_periodize_heatDilation`: `∂_a P_c[a^{-2}q(·/√a)] = P_c[∂_a(a^{-2}q(·/√a))]`,
  i.e. the `a`-derivative commutes with the periodization (dominated termwise differentiation on
  the window `a/2 < b < 2a`);
* `laplacian_sub_deriv_periodize_heatDilation` (**B0317, B0333**):
  `(Δ - ∂_a) P_c[a^{-2}q(·/√a)] = a^{-1} P_c[a^{-2}(Dq)(·/√a)]`, i.e. `P_c[a^{-3}(Dq)(x/√a)]`.

Decay hypotheses. The manuscript applies the identity to "smooth decaying" `q` (tex 6328): the
heat-scaled Gaussian vectors and the adjoint kernels with harmonic `r^{-2}` tail (tex 6119–6121).
The hypotheses used here are translate bounds `C(1+|q|)^{-s}`, `s > 1`, on `q`, on
`(1+‖y‖)‖Dq(y)‖` and on `‖D²q‖`; all these kernels satisfy them with `s = 2`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The operators `D` and the dilation drift -/

/-- The dilation drift `2q + ½ y·∇q` (so that `∂_a[a^{-2}q(x/√a)] = -a^{-3}(2q + ½y·∇q)(x/√a)`,
blueprint note of B0317). -/
def dilationDrift (q : ℝ × ℝ → E) (y : ℝ × ℝ) : E :=
  (2 : ℝ) • q y + (1 / 2 : ℝ) • fderiv ℝ q y y

/-- The operator `D = Δ + ½ y·∇ + 2` of tex 722 (B0099), used in B0317 (tex 6138–6147). -/
def dilationGen (q : ℝ × ℝ → E) (y : ℝ × ℝ) : E :=
  Cyl.laplacian q y + dilationDrift q y

theorem dilationGen_eq (q : ℝ × ℝ → E) (y : ℝ × ℝ) :
    dilationGen q y = Cyl.laplacian q y + (1 / 2 : ℝ) • fderiv ℝ q y y + (2 : ℝ) • q y := by
  unfold dilationGen dilationDrift; abel

theorem heatDilation_apply (a : ℝ) (f : ℝ × ℝ → E) (z : ℝ × ℝ) :
    heatDilation a f z = (a⁻¹ ^ 2) • f ((Real.sqrt a)⁻¹ • z) := rfl

theorem heatDilation_eq_fun (a : ℝ) (f : ℝ × ℝ → E) :
    heatDilation a f = fun z => (a⁻¹ ^ 2) • f ((Real.sqrt a)⁻¹ • z) := rfl

theorem heatDilation_add (a : ℝ) (f g : ℝ × ℝ → E) (z : ℝ × ℝ) :
    heatDilation a (fun y => f y + g y) z = heatDilation a f z + heatDilation a g z := by
  simp [heatDilation_apply, smul_add]

theorem contDiff_heatDilation {n : WithTop ℕ∞} {f : ℝ × ℝ → E} (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ n (heatDilation a f) :=
  (hf.comp (contDiff_id.const_smul _)).const_smul _

/-! ### The Laplacian through second derivatives -/

/-- For a `C²` function, the classical Laplacian is the trace of the second derivative in the
coordinate directions. -/
theorem laplacian_eq_iteratedFDeriv {f : ℝ × ℝ → E} (hf : ContDiff ℝ 2 f) (z : ℝ × ℝ) :
    Cyl.laplacian f z = iteratedFDeriv ℝ 2 f z ![((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] +
      iteratedFDeriv ℝ 2 f z ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hQ : Cyl.partialQ f = fun w => fderiv ℝ f w ((1 : ℝ), (0 : ℝ)) :=
    funext (Cyl.partialQ_eq_fderiv hd)
  have hE : Cyl.partialEta f = fun w => fderiv ℝ f w ((0 : ℝ), (1 : ℝ)) :=
    funext (Cyl.partialEta_eq_fderiv hd)
  have hdQ : Differentiable ℝ (fun w => fderiv ℝ f w ((1 : ℝ), (0 : ℝ))) :=
    fun w => (hd2 w).clm_apply (differentiableAt_const _)
  have hdE : Differentiable ℝ (fun w => fderiv ℝ f w ((0 : ℝ), (1 : ℝ))) :=
    fun w => (hd2 w).clm_apply (differentiableAt_const _)
  unfold Cyl.laplacian
  rw [hQ, hE, Cyl.partialQ_eq_fderiv hdQ, Cyl.partialEta_eq_fderiv hdE,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply (hd2 z) (differentiableAt_const _),
    fderiv_clm_apply (hd2 z) (differentiableAt_const _)]
  simp

/-- `‖Δf(z)‖ ≤ 2‖D²f(z)‖` (the coordinate vectors have sup norm `1`). -/
theorem norm_laplacian_le {f : ℝ × ℝ → E} (hf : ContDiff ℝ 2 f) (z : ℝ × ℝ) :
    ‖Cyl.laplacian f z‖ ≤ 2 * ‖iteratedFDeriv ℝ 2 f z‖ := by
  rw [laplacian_eq_iteratedFDeriv hf]
  have h1 := (iteratedFDeriv ℝ 2 f z).le_opNorm ![((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))]
  have h2 := (iteratedFDeriv ℝ 2 f z).le_opNorm ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Prod.norm_mk,
    norm_one, norm_zero, max_eq_left zero_le_one, max_eq_right zero_le_one, mul_one] at h1 h2
  refine (norm_add_le _ _).trans ?_
  linarith

/-! ### The single-function identities (B0317) -/

/-- The derivatives of a heat dilation: `D^k[a^{-2}f(·/√a)](z) = a^{-2}a^{-k/2}(D^kf)(z/√a)`. -/
theorem iteratedFDeriv_heatDilation (k : ℕ) (a : ℝ) (f : ℝ × ℝ → E) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ k (heatDilation a f) z =
      (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ k) • iteratedFDeriv ℝ k f ((Real.sqrt a)⁻¹ • z) := by
  rw [heatDilation_eq_fun]
  exact iteratedFDeriv_comp_smul k f (a⁻¹ ^ 2) (Real.sqrt a)⁻¹ z

/-- **B0317 (spatial half).** `Δ[a^{-2}q(·/√a)] = a^{-1}·a^{-2}(Δq)(·/√a)` for `a > 0`. -/
theorem laplacian_heatDilation {q : ℝ × ℝ → E} (hq : ContDiff ℝ 2 q) {a : ℝ} (ha : 0 < a)
    (z : ℝ × ℝ) :
    Cyl.laplacian (heatDilation a q) z = a⁻¹ • heatDilation a (Cyl.laplacian q) z := by
  rw [laplacian_eq_iteratedFDeriv (contDiff_heatDilation hq a), iteratedFDeriv_heatDilation,
    heatDilation_apply, laplacian_eq_iteratedFDeriv hq]
  have hsa : (Real.sqrt a)⁻¹ ^ 2 = a⁻¹ := by rw [inv_pow, Real.sq_sqrt ha.le]
  simp only [hsa, smul_add, smul_smul]
  rw [smul_apply, smul_apply, mul_comm (a⁻¹ ^ 2) a⁻¹]

/-- **B0317 (time half).** `∂_a[a^{-2}q(x/√a)] = -a^{-1}·a^{-2}(2q + ½y·∇q)(x/√a)` for
`a > 0` and differentiable `q`. -/
theorem hasDerivAt_heatDilation_param {q : ℝ × ℝ → E} (hq : Differentiable ℝ q) {a : ℝ}
    (ha : 0 < a) (z : ℝ × ℝ) :
    HasDerivAt (fun b => heatDilation b q z) (-(a⁻¹) • heatDilation a (dilationDrift q) z) a := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr : HasDerivAt (fun b => (Real.sqrt b)⁻¹)
      (-(1 / (2 * Real.sqrt a)) / Real.sqrt a ^ 2) a :=
    (Real.hasDerivAt_sqrt ha.ne').inv hsa.ne'
  have hv := hr.smul_const z
  have hqv : HasDerivAt (fun b => q ((Real.sqrt b)⁻¹ • z))
      (fderiv ℝ q ((Real.sqrt a)⁻¹ • z)
        ((-(1 / (2 * Real.sqrt a)) / Real.sqrt a ^ 2) • z)) a :=
    (hq _).hasFDerivAt.comp_hasDerivAt a hv
  have hs : HasDerivAt (fun b : ℝ => b⁻¹ ^ 2) ((2 : ℕ) * a⁻¹ ^ (2 - 1) * -(a ^ 2)⁻¹) a :=
    (hasDerivAt_inv ha.ne').pow 2
  have htot := hs.smul hqv
  refine htot.congr_deriv ?_
  set y : ℝ × ℝ := (Real.sqrt a)⁻¹ • z with hy
  have hz : fderiv ℝ q y z = Real.sqrt a • fderiv ℝ q y y := by
    rw [← ContinuousLinearMap.map_smul, hy, smul_inv_smul₀ hsa.ne']
  rw [ContinuousLinearMap.map_smul, hz, heatDilation_apply, dilationDrift, ← hy]
  have ha2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have ha0 : a ≠ 0 := ha.ne'
  match_scalars
  · field_simp
    rw [ha2]
  · field_simp
    norm_num [ha0]

/-- **B0317 (exact dilation identity, tex 6145–6146).** For `C²` `q` and `a > 0`,
`(Δ - ∂_a)[a^{-2}q(·/√a)] = a^{-1}·a^{-2}(Dq)(·/√a) = a^{-3}(Dq)(x/√a)`. -/
theorem laplacian_sub_deriv_heatDilation {q : ℝ × ℝ → E} (hq : ContDiff ℝ 2 q) {a : ℝ}
    (ha : 0 < a) (z : ℝ × ℝ) :
    Cyl.laplacian (heatDilation a q) z - deriv (fun b => heatDilation b q z) a =
      a⁻¹ • heatDilation a (dilationGen q) z := by
  rw [(hasDerivAt_heatDilation_param (hq.differentiable (by norm_num)) ha z).deriv,
    laplacian_heatDilation hq ha, neg_smul, sub_neg_eq_add, ← smul_add]
  congr 1
  unfold dilationGen
  rw [heatDilation_add]

/-! ### Translate bounds for heat dilations -/

/-- `(1 + |r t|)^{-s} ≤ (min 1 r₀)^{-s}(1+|t|)^{-s}` for `0 < r₀ ≤ r`, `s ≥ 0`. -/
theorem one_add_abs_mul_rpow_neg_le {s r₀ r : ℝ} (hs : 0 ≤ s) (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (t : ℝ) : (1 + |r * t|) ^ (-s) ≤ (min 1 r₀) ^ (-s) * (1 + |t|) ^ (-s) := by
  have hm : 0 < min 1 r₀ := lt_min one_pos hr₀
  have h1 : min 1 r₀ * (1 + |t|) ≤ 1 + |r * t| := by
    rw [abs_mul, abs_of_pos (hr₀.trans_le hr)]
    have := min_le_left 1 r₀
    have := min_le_right 1 r₀
    have ht : 0 ≤ |t| := abs_nonneg t
    nlinarith
  rw [← Real.mul_rpow hm.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)

/-- A translate bound `‖g(z)‖ ≤ C(1+|z₁|)^{-s}` forces `C ≥ 0`. -/
theorem nonneg_of_translate_bound {F : Type*} [NormedAddCommGroup F] {g : ℝ × ℝ → F} {C s : ℝ}
    (hg : ∀ z, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-s)) : 0 ≤ C := by
  have h := hg 0
  simp only [Prod.fst_zero, abs_zero, add_zero, Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

/-- Translate bounds survive the dilation `z ↦ r z`, uniformly for `r ≥ r₀ > 0`. -/
theorem translate_bound_comp_smul {F : Type*} [NormedAddCommGroup F] {g : ℝ × ℝ → F} {C s r₀ r : ℝ}
    (hs : 0 ≤ s) (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hg : ∀ z, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (z : ℝ × ℝ) : ‖g (r • z)‖ ≤ C * (min 1 r₀) ^ (-s) * (1 + |z.1|) ^ (-s) := by
  have hC := nonneg_of_translate_bound hg
  refine (hg _).trans ?_
  rw [Prod.smul_fst, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (one_add_abs_mul_rpow_neg_le hs hr₀ hr z.1) hC

/-- Translate bounds for the derivatives of a heat dilation. -/
theorem norm_iteratedFDeriv_heatDilation_le {f : ℝ × ℝ → E} {C s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a)
    (k : ℕ) (hk : ∀ z, ‖iteratedFDeriv ℝ k f z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (heatDilation a f) z‖ ≤
      (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ k * (C * (min 1 (Real.sqrt a)⁻¹) ^ (-s))) *
        (1 + |z.1|) ^ (-s) := by
  have hr : 0 < (Real.sqrt a)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ha)
  calc ‖iteratedFDeriv ℝ k (heatDilation a f) z‖
      = (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ k) *
          ‖iteratedFDeriv ℝ k f ((Real.sqrt a)⁻¹ • z)‖ := by
        rw [iteratedFDeriv_heatDilation, norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (a⁻¹ ^ 2 * (Real.sqrt a)⁻¹ ^ k) *
          (C * (min 1 (Real.sqrt a)⁻¹) ^ (-s) * (1 + |z.1|) ^ (-s)) :=
        mul_le_mul_of_nonneg_left (translate_bound_comp_smul hs hr le_rfl hk z) (by positivity)
    _ = _ := by ring

/-- Translate bounds for a heat dilation. -/
theorem norm_heatDilation_le {f : ℝ × ℝ → E} {C s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a)
    (hf : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    ‖heatDilation a f z‖ ≤ (a⁻¹ ^ 2 * (C * (min 1 (Real.sqrt a)⁻¹) ^ (-s))) *
      (1 + |z.1|) ^ (-s) := by
  have h := norm_iteratedFDeriv_heatDilation_le (f := f) hs ha 0
    (fun z => by rw [norm_iteratedFDeriv_zero]; exact hf z) z
  simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using h

/-- The drift `2q + ½y·∇q` obeys a translate bound when `q` and `(1+‖y‖)‖Dq(y)‖` do. -/
theorem norm_dilationDrift_le {q : ℝ × ℝ → E} {C s : ℝ}
    (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    ‖dilationDrift q z‖ ≤ 3 * C * (1 + |z.1|) ^ (-s) := by
  have hC := nonneg_of_translate_bound h0
  have hw : 0 ≤ C * (1 + |z.1|) ^ (-s) := by positivity
  have hD : ‖fderiv ℝ q z z‖ ≤ C * (1 + |z.1|) ^ (-s) := by
    refine ((fderiv ℝ q z).le_opNorm z).trans ?_
    refine le_trans ?_ (h1 z)
    have := norm_nonneg (fderiv ℝ q z)
    have := norm_nonneg z
    nlinarith
  unfold dilationDrift
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have := h0 z
  nlinarith

/-- The Laplacian obeys a translate bound when `D²q` does. -/
theorem norm_laplacian_le_translate {q : ℝ × ℝ → E} (hq : ContDiff ℝ 2 q) {C s : ℝ}
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    ‖Cyl.laplacian q z‖ ≤ 2 * C * (1 + |z.1|) ^ (-s) := by
  refine (norm_laplacian_le hq z).trans ?_
  have := h2 z
  linarith

/-! ### The Laplacian commutes with the periodization -/

section Periodized

variable [CompleteSpace E]

/-- **G7 item 5 (spatial part).** `Δ(P_c g) = P_c(Δg)` for `C²` `g` whose derivatives of order
`≤ 2` obey translate bounds `C_k(1+|q|)^{-s}`, `s > 1`. -/
theorem laplacian_periodize {g : ℝ × ℝ → E} (hg : ContDiff ℝ 2 g) {s c : ℝ} (hs : 1 < s)
    (hc : c ≠ 0)
    (hD : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C : ℝ, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (x : ℝ × ℝ) :
    Cyl.laplacian (periodize c g) x = periodize c (Cyl.laplacian g) x := by
  have hg' : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) g := hg
  have hP : ContDiff ℝ 2 (periodize c g) := contDiff_periodize hs hc hg' hD
  rw [laplacian_eq_iteratedFDeriv hP, iteratedFDeriv_periodize hs hc hg' hD (m := 2) le_rfl]
  obtain ⟨C, hC⟩ := hD 2 le_rfl
  have hsum : Summable fun n : ℤ => iteratedFDeriv ℝ 2 g (x - shiftVec c n) :=
    Summable.of_norm_bounded ((summable_translate hs hc x.1).mul_left C)
      fun n => by rw [sub_shiftVec]; exact hC _
  have h1 := ContinuousMultilinearMap.hasSum_eval hsum.hasSum
    ![((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))]
  have h2 := ContinuousMultilinearMap.hasSum_eval hsum.hasSum
    ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  rw [← (h1.add h2).tsum_eq, periodize_eq]
  congr 1
  funext n
  rw [laplacian_eq_iteratedFDeriv hg]

/-! ### The `a`-derivative commutes with the periodization -/

/-- **G7 item 5 (time part; B0317, B0333).** For differentiable `q` with translate bounds on `q`
and on `(1+‖y‖)‖Dq(y)‖`, the map `a ↦ P_c[a^{-2}q(·/√a)](x)` is differentiable at every `a > 0`,
with derivative `P_c[∂_a(a^{-2}q(·/√a))](x) = -a^{-1} P_c[a^{-2}(2q + ½y·∇q)(·/√a)](x)`. -/
theorem hasDerivAt_periodize_heatDilation {q : ℝ × ℝ → E} (hq : Differentiable ℝ q)
    {C s c a : ℝ} (hs : 1 < s) (hc : c ≠ 0) (ha : 0 < a)
    (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (x : ℝ × ℝ) :
    HasDerivAt (fun b => periodize c (heatDilation b q) x)
      (-(a⁻¹) • periodize c (heatDilation a (dilationDrift q)) x) a := by
  have hs0 : 0 ≤ s := by linarith
  have hC := nonneg_of_translate_bound h0
  set r₀ : ℝ := (Real.sqrt (2 * a))⁻¹ with hr₀
  have hr₀0 : 0 < r₀ := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  set K : ℝ := (a / 2)⁻¹ * (a / 2)⁻¹ ^ 2 * (3 * C * (min 1 r₀) ^ (-s)) with hK
  set t : Set ℝ := Ioo (a / 2) (2 * a) with ht
  have hat : a ∈ t := ⟨by linarith, by linarith⟩
  -- the derivative bound on the window
  have hbound : ∀ (n : ℤ) (b : ℝ), b ∈ t →
      ‖-(b⁻¹) • heatDilation b (dilationDrift q) (x.1 - n * c, x.2)‖ ≤
        K * (1 + |x.1 - n * c|) ^ (-s) := by
    intro n b hb
    have hb0 : 0 < b := by linarith [hb.1]
    have hrb : r₀ ≤ (Real.sqrt b)⁻¹ := by
      rw [hr₀]
      exact inv_anti₀ (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt hb.2.le)
    have hbinv : b⁻¹ ≤ (a / 2)⁻¹ := inv_anti₀ (by linarith) hb.1.le
    have hdr := translate_bound_comp_smul hs0 hr₀0 hrb (norm_dilationDrift_le h0 h1)
      ((x.1 - n * c, x.2) : ℝ × ℝ)
    rw [norm_smul, heatDilation_apply, norm_smul, norm_neg,
      Real.norm_of_nonneg (inv_pos.2 hb0).le, Real.norm_of_nonneg (by positivity)]
    have hw : 0 ≤ 3 * C * (min 1 r₀) ^ (-s) * (1 + |x.1 - n * c|) ^ (-s) := by positivity
    calc b⁻¹ * (b⁻¹ ^ 2 * ‖dilationDrift q ((Real.sqrt b)⁻¹ • (x.1 - n * c, x.2))‖)
        ≤ (a / 2)⁻¹ * ((a / 2)⁻¹ ^ 2 *
            (3 * C * (min 1 r₀) ^ (-s) * (1 + |x.1 - n * c|) ^ (-s))) := by
          gcongr
      _ = K * (1 + |x.1 - n * c|) ^ (-s) := by rw [hK]; ring
  have hu : Summable fun n : ℤ => K * (1 + |x.1 - n * c|) ^ (-s) :=
    (summable_translate hs hc x.1).mul_left K
  have hsum0 : Summable fun n : ℤ => heatDilation a q (x.1 - n * c, x.2) :=
    summable_periodize hs hc (norm_heatDilation_le hs0 ha h0) x
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun (n : ℤ) b =>
      heatDilation b q (x.1 - n * c, x.2))
    (g' := fun (n : ℤ) b => -(b⁻¹) • heatDilation b (dilationDrift q) (x.1 - n * c, x.2))
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n b hb => hasDerivAt_heatDilation_param hq (by linarith [hb.1]) _)
    hbound hat hsum0 hat
  unfold periodize
  rw [← tsum_const_smul'']
  exact key

/-- **B0317, B0333: `(Δ - ∂_a)` passes through `P_c`.** For `C²` `q` with translate bounds on
`q`, `(1+‖y‖)‖Dq(y)‖` and `‖D²q‖` (exponent `s > 1`), every `c ≠ 0`, `a > 0` and `x`:
`(Δ - ∂_a) P_c[a^{-2}q(·/√a)](x) = a^{-1} P_c[a^{-2}(Dq)(·/√a)](x)`,
i.e. `P_c[a^{-3}(Dq)(·/√a)](x)`, with `D = Δ + ½y·∇ + 2` (tex 722, 6145–6146). -/
theorem laplacian_sub_deriv_periodize_heatDilation {q : ℝ × ℝ → E} (hq : ContDiff ℝ 2 q)
    {C s c a : ℝ} (hs : 1 < s) (hc : c ≠ 0) (ha : 0 < a)
    (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (x : ℝ × ℝ) :
    Cyl.laplacian (periodize c (heatDilation a q)) x -
        deriv (fun b => periodize c (heatDilation b q) x) a =
      a⁻¹ • periodize c (heatDilation a (dilationGen q)) x := by
  have hs0 : 0 ≤ s := by linarith
  have hC := nonneg_of_translate_bound h0
  -- translate bounds for the derivatives of `q` up to order 2
  have hq' : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∀ z, ‖iteratedFDeriv ℝ k q z‖ ≤ C * (1 + |z.1|) ^ (-s) := by
    intro k hk z
    have hk' : k ≤ 2 := by exact_mod_cast hk
    interval_cases k
    · rw [norm_iteratedFDeriv_zero]; exact h0 z
    · rw [norm_iteratedFDeriv_one]
      refine le_trans ?_ (h1 z)
      have := norm_nonneg (fderiv ℝ q z)
      have := norm_nonneg z
      nlinarith
    · exact h2 z
  have hD : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z,
      ‖iteratedFDeriv ℝ k (heatDilation a q) z‖ ≤ C' * (1 + |z.1|) ^ (-s) :=
    fun k hk => ⟨_, norm_iteratedFDeriv_heatDilation_le hs0 ha k (hq' k hk)⟩
  -- the spatial part
  have hlap : Cyl.laplacian (periodize c (heatDilation a q)) x =
      a⁻¹ • periodize c (heatDilation a (Cyl.laplacian q)) x := by
    rw [laplacian_periodize (contDiff_heatDilation hq a) hs hc hD x]
    unfold periodize
    rw [← tsum_const_smul'']
    congr 1
    funext n
    exact laplacian_heatDilation hq ha _
  -- the time part
  rw [hlap, (hasDerivAt_periodize_heatDilation (hq.differentiable (by norm_num)) hs hc ha h0 h1
    x).deriv, neg_smul, sub_neg_eq_add, ← smul_add]
  congr 1
  -- additivity of the periodization
  have hsL : Summable fun n : ℤ => heatDilation a (Cyl.laplacian q) (x.1 - n * c, x.2) :=
    summable_periodize hs hc (norm_heatDilation_le hs0 ha (norm_laplacian_le_translate hq h2)) x
  have hsD : Summable fun n : ℤ => heatDilation a (dilationDrift q) (x.1 - n * c, x.2) :=
    summable_periodize hs hc (norm_heatDilation_le hs0 ha (norm_dilationDrift_le h0 h1)) x
  unfold periodize
  rw [← hsL.tsum_add hsD]
  congr 1
  funext n
  unfold dilationGen
  rw [heatDilation_add]

end Periodized

end UnforcedLeray.Gaussian
