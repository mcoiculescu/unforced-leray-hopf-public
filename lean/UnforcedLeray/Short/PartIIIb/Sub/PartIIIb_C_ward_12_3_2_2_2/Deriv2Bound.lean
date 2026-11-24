import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.DerivBound

/-!
# `inletSrcDeriv2Bound : InletSrcDeriv2Bound`

Source `the November 2 reference manuscript`
lines 2545-2551, 2563-2569.  Order-2 product-rule bound for
`inletFn2 p i j l = -∂_j(inletFn p i l) = ∂_j∂_l(inletSrc p i)`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params advT)
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412 (realC)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace Jets2

open Jets

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Directional derivative along `ek k`. -/
def D1 (k : Fin 3) (F : UnforcedLeray.Space → V) (x : UnforcedLeray.Space) : V :=
  fderiv ℝ F x (ek k)

/-- Second directional derivative along `ek l` then `ek j`. -/
def D2 (j l : Fin 3) (F : UnforcedLeray.Space → V) (x : UnforcedLeray.Space) : V :=
  D1 j (D1 l F) x

theorem contDiff_D1 {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (k : Fin 3) :
    ContDiff ℝ ∞ (D1 k F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_D2 {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (j l : Fin 3) :
    ContDiff ℝ ∞ (D2 j l F) :=
  contDiff_D1 (contDiff_D1 hF l) j

theorem D1_add {F G : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (k : Fin 3) : D1 k (fun x => F x + G x) = fun x => D1 k F x + D1 k G x := by
  funext x
  have hh := ((hF.differentiable (by simp) x).hasFDerivAt.add
    (hG.differentiable (by simp) x).hasFDerivAt).fderiv
  change (fderiv ℝ (F + G) x) (ek k) = _
  rw [hh]
  rfl

theorem D1_sub {F G : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (k : Fin 3) : D1 k (fun x => F x - G x) = fun x => D1 k F x - D1 k G x := by
  funext x
  have hh := ((hF.differentiable (by simp) x).hasFDerivAt.sub
    (hG.differentiable (by simp) x).hasFDerivAt).fderiv
  change (fderiv ℝ (F - G) x) (ek k) = _
  rw [hh]
  rfl

theorem D1_neg {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (k : Fin 3) :
    D1 k (fun x => -F x) = fun x => -D1 k F x := by
  funext x
  have hh := (hF.differentiable (by simp) x).hasFDerivAt.neg.fderiv
  change (fderiv ℝ (-F) x) (ek k) = _
  rw [hh]
  rfl

theorem D1_const_smul {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (c : ℝ) (k : Fin 3) :
    D1 k (fun x => c • F x) = fun x => c • D1 k F x := by
  funext x
  have hh := ((hF.differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv
  change (fderiv ℝ (c • F) x) (ek k) = _
  rw [hh]
  rfl

theorem D1_sum {F : Fin 3 → UnforcedLeray.Space → V} (hF : ∀ m, ContDiff ℝ ∞ (F m)) (k : Fin 3) :
    D1 k (fun x => ∑ m : Fin 3, F m x) = fun x => ∑ m : Fin 3, D1 k (F m) x := by
  funext x
  have hh : HasFDerivAt (fun x => ∑ m : Fin 3, F m x) (∑ m : Fin 3, fderiv ℝ (F m) x) x :=
    HasFDerivAt.fun_sum fun m _ => ((hF m).differentiable (by simp) x).hasFDerivAt
  unfold D1
  rw [hh.fderiv, sum_apply]

theorem D2_add {F G : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (j l : Fin 3) (y : UnforcedLeray.Space) :
    D2 j l (fun x => F x + G x) y = D2 j l F y + D2 j l G y := by
  unfold D2
  rw [D1_add hF hG l, D1_add (contDiff_D1 hF l) (contDiff_D1 hG l) j]

theorem D2_sub {F G : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (j l : Fin 3) (y : UnforcedLeray.Space) :
    D2 j l (fun x => F x - G x) y = D2 j l F y - D2 j l G y := by
  unfold D2
  rw [D1_sub hF hG l, D1_sub (contDiff_D1 hF l) (contDiff_D1 hG l) j]

theorem D2_const_smul {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (c : ℝ)
    (j l : Fin 3) (y : UnforcedLeray.Space) :
    D2 j l (fun x => c • F x) y = c • D2 j l F y := by
  unfold D2
  rw [D1_const_smul hF c l, D1_const_smul (contDiff_D1 hF l) c j]

theorem D2_sum {F : Fin 3 → UnforcedLeray.Space → V} (hF : ∀ m, ContDiff ℝ ∞ (F m))
    (j l : Fin 3) (y : UnforcedLeray.Space) :
    D2 j l (fun x => ∑ m : Fin 3, F m x) y = ∑ m : Fin 3, D2 j l (F m) y := by
  unfold D2
  rw [D1_sum hF l, D1_sum (fun m => contDiff_D1 (hF m) l) j]

/-- Jet norm of `D1 k F` is bounded by the jet norm of `F` one order up. -/
theorem norm_iteratedFDeriv_D1_le {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F)
    (k : Fin 3) (n : ℕ) (y : UnforcedLeray.Space) :
    ‖iteratedFDeriv ℝ n (D1 k F) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) F y‖ := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have hcomp : D1 k F = (ContinuousLinearMap.apply ℝ V (ek k)) ∘ (fderiv ℝ F) := rfl
  have h1 := (ContinuousLinearMap.apply ℝ V (ek k)).norm_iteratedFDeriv_comp_left
    (hdf.contDiffAt (x := y)) (n := n) (by exact_mod_cast le_top)
  rw [← hcomp] at h1
  have hn : ‖ContinuousLinearMap.apply ℝ V (ek k)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
      simpa [one_mul, norm_single_one k] using f.le_opNorm (ek k)
  have h2 : ‖iteratedFDeriv ℝ n (fderiv ℝ F) y‖ = ‖iteratedFDeriv ℝ (n + 1) F y‖ :=
    norm_iteratedFDeriv_fderiv
  calc ‖iteratedFDeriv ℝ n (D1 k F) y‖
      ≤ ‖ContinuousLinearMap.apply ℝ V (ek k)‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ F) y‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ F) y‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) F y‖ := by rw [one_mul, h2]

theorem norm_D1_le {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (k : Fin 3)
    (y : UnforcedLeray.Space) : ‖D1 k F y‖ ≤ ‖iteratedFDeriv ℝ 1 F y‖ := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := D1 k F)]
  exact norm_iteratedFDeriv_D1_le hF k 0 y

theorem norm_D2_le {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (j l : Fin 3)
    (y : UnforcedLeray.Space) : ‖D2 j l F y‖ ≤ ‖iteratedFDeriv ℝ 2 F y‖ :=
  (norm_D1_le (contDiff_D1 hF l) j y).trans (norm_iteratedFDeriv_D1_le hF l 1 y)

theorem norm_D2_D1_le {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (j l k : Fin 3)
    (y : UnforcedLeray.Space) : ‖D2 j l (D1 k F) y‖ ≤ ‖iteratedFDeriv ℝ 3 F y‖ :=
  (norm_D2_le (contDiff_D1 hF k) j l y).trans (norm_iteratedFDeriv_D1_le hF k 2 y)

theorem norm_D2_D2_le {F : UnforcedLeray.Space → V} (hF : ContDiff ℝ ∞ F) (j l k m : Fin 3)
    (y : UnforcedLeray.Space) : ‖D2 j l (D2 k m F) y‖ ≤ ‖iteratedFDeriv ℝ 4 F y‖ :=
  (norm_D2_D1_le (contDiff_D1 hF m) j l k y).trans (norm_iteratedFDeriv_D1_le hF m 3 y)

/-- Second-order Leibniz rule bound for `D2 j l (f • g)`. -/
theorem norm_D2_smul_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] {f : UnforcedLeray.Space → 𝕜}
    {g : UnforcedLeray.Space → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (j l : Fin 3) (y : UnforcedLeray.Space) :
    ‖D2 j l (fun x => f x • g x) y‖ ≤
      ‖f y‖ * ‖D2 j l g y‖ + ‖D1 j f y‖ * ‖D1 l g y‖ +
      (‖D1 l f y‖ * ‖D1 j g y‖ + ‖D2 j l f y‖ * ‖g y‖) := by
  have h1 : D1 l (fun x => f x • g x) =
      fun z => f z • D1 l g z + D1 l f z • g z := by
    funext z
    have hh : HasFDerivAt (fun x => f x • g x)
        (f z • fderiv ℝ g z + (fderiv ℝ f z).smulRight (g z)) z :=
      (hf.differentiable (by simp) z).hasFDerivAt.smul
        (hg.differentiable (by simp) z).hasFDerivAt
    unfold D1
    rw [hh.fderiv]
    rfl
  have h2 : D2 j l (fun x => f x • g x) y =
      D1 j (fun z => f z • D1 l g z) y + D1 j (fun z => D1 l f z • g z) y := by
    unfold D2
    rw [h1, D1_add (F := fun z => f z • D1 l g z) (G := fun z => D1 l f z • g z)
      (hf.smul (contDiff_D1 hg l)) ((contDiff_D1 hf l).smul hg) j]
  rw [h2]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_fderiv_smul_le (hf.differentiable (by simp) y)
      ((contDiff_D1 hg l).differentiable (by simp) y) (ek j)
  · exact norm_fderiv_smul_le ((contDiff_D1 hf l).differentiable (by simp) y)
      (hg.differentiable (by simp) y) (ek j)

theorem D1_proj (k l : Fin 3) :
    D1 l (fun x : UnforcedLeray.Space => x k) = fun _ => ek l k := by
  funext z
  unfold D1
  have h := fderiv_coord (𝕜 := ℝ) (f := fun w : UnforcedLeray.Space => w) (y := z)
    differentiableAt_id k (ek l)
  simp only [fderiv_fun_id, ContinuousLinearMap.id_apply] at h
  exact h

theorem norm_D1_proj_le (k l : Fin 3) (y : UnforcedLeray.Space) :
    ‖D1 l (fun x : UnforcedLeray.Space => x k) y‖ ≤ 1 := by
  rw [D1_proj]
  exact (abs_coord_le (𝕜 := ℝ) (ek l) k).trans (le_of_eq (norm_single_one l))

theorem norm_D2_proj_eq_zero (j l k : Fin 3) (y : UnforcedLeray.Space) :
    ‖D2 j l (fun x : UnforcedLeray.Space => x k) y‖ = 0 := by
  unfold D2
  rw [D1_proj]
  unfold D1
  simp

theorem norm_D1_coord_le {𝕜 : Type*} [RCLike 𝕜] {f : UnforcedLeray.Space → EuclideanSpace 𝕜 (Fin 3)}
    (hf : ContDiff ℝ ∞ f) (k l : Fin 3) (y : UnforcedLeray.Space) :
    ‖D1 l (fun z => f z k) y‖ ≤ ‖D1 l f y‖ := by
  unfold D1
  rw [fderiv_coord (hf.differentiable (by simp) y) k (ek l)]
  exact abs_coord_le (𝕜 := 𝕜) _ k

theorem norm_D2_coord_le {𝕜 : Type*} [RCLike 𝕜] {f : UnforcedLeray.Space → EuclideanSpace 𝕜 (Fin 3)}
    (hf : ContDiff ℝ ∞ f) (j l k : Fin 3) (y : UnforcedLeray.Space) :
    ‖D2 j l (fun z => f z k) y‖ ≤ ‖D2 j l f y‖ := by
  have h1 : D1 l (fun z => f z k) = fun z => D1 l f z k := by
    funext z; exact fderiv_coord (hf.differentiable (by simp) z) k (ek l)
  unfold D2
  rw [h1]
  exact norm_D1_coord_le (contDiff_D1 hf l) k j y

theorem norm_D1_ofReal_coord_le {R : UnforcedLeray.Space → UnforcedLeray.Space}
    (hR : ContDiff ℝ ∞ R) (k l : Fin 3) (y : UnforcedLeray.Space) :
    ‖D1 l (fun z => ((R z k : ℝ) : ℂ)) y‖ ≤ ‖D1 l R y‖ := by
  unfold D1
  rw [fderiv_ofReal_coord (hR.differentiable (by simp) y) k (ek l), Complex.norm_real]
  exact abs_coord_le (𝕜 := ℝ) _ k

theorem norm_D2_ofReal_coord_le {R : UnforcedLeray.Space → UnforcedLeray.Space}
    (hR : ContDiff ℝ ∞ R) (j l k : Fin 3) (y : UnforcedLeray.Space) :
    ‖D2 j l (fun z => ((R z k : ℝ) : ℂ)) y‖ ≤ ‖D2 j l R y‖ := by
  have h1 : D1 l (fun z => ((R z k : ℝ) : ℂ)) = fun z => ((D1 l R z k : ℝ) : ℂ) := by
    funext z; exact fderiv_ofReal_coord (hR.differentiable (by simp) z) k (ek l)
  unfold D2
  rw [h1]
  exact norm_D1_ofReal_coord_le (contDiff_D1 hR l) k j y

theorem norm_D1_realC {F : UnforcedLeray.Space → UnforcedLeray.Space} (hF : ContDiff ℝ ∞ F)
    (l : Fin 3) (y : UnforcedLeray.Space) :
    ‖D1 l (fun z => realC (F z)) y‖ = ‖D1 l F y‖ := by
  unfold D1
  rw [fderiv_realC (hF.differentiable (by simp) y) (ek l), norm_realC]

theorem norm_D2_realC {F : UnforcedLeray.Space → UnforcedLeray.Space} (hF : ContDiff ℝ ∞ F)
    (j l : Fin 3) (y : UnforcedLeray.Space) :
    ‖D2 j l (fun z => realC (F z)) y‖ = ‖D2 j l F y‖ := by
  have h1 : D1 l (fun z => realC (F z)) = fun z => realC (D1 l F z) := by
    funext z; exact fderiv_realC (hF.differentiable (by simp) z) (ek l)
  unfold D2
  rw [h1, norm_D1_realC (contDiff_D1 hF l) j y]

theorem term_le_YBA {Y B A y b a : ℝ} (hY : 0 ≤ Y) (hB : 0 ≤ B) (_hy : 0 ≤ y) (hb : 0 ≤ b)
    (ha : 0 ≤ a) (hyY : y ≤ Y) (hbB : b ≤ B) (haA : a ≤ A) :
    y * b * a ≤ Y * B * A :=
  mul_le_mul (mul_le_mul hyY hbB hb hY) haA ha (mul_nonneg hY hB)

theorem arith2_bound (ny a0 a1 a2 a3 a4 d0 d1 d2 b0 b1 b2 b3 ν : ℝ)
    (hny : 0 ≤ ny) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) (hν : |ν| ≤ 1) :
    d2 + (1 / 2) * (3 * (ny * a3 + a2 + (a2 + 0))) + |ν| * (3 * a4) + (1 / 2) * a2 +
      3 * (b0 * a3 + b1 * a2 + (b1 * a2 + b2 * a1)) +
      3 * (a0 * b3 + a1 * b2 + (a1 * b2 + a2 * b1)) ≤
    40 * (1 + ny) * (1 + (b0 + b1 + b2 + b3)) *
      ((a0 + a1 + a2 + a3 + a4) + (d0 + d1 + d2)) := by
  set Y := 1 + ny
  set B := 1 + (b0 + b1 + b2 + b3)
  set A := (a0 + a1 + a2 + a3 + a4) + (d0 + d1 + d2)
  have hY : 0 ≤ Y := by positivity
  have hB : 0 ≤ B := by positivity
  have h1 : |ν| * (3 * a4) ≤ 3 * a4 := by nlinarith [abs_nonneg ν]
  have t1 : d2 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one zero_le_one hd2 (by linarith) (by linarith) (by linarith)
  have t2 : ny * a3 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB hny zero_le_one ha3 (by linarith) (by linarith) (by linarith)
  have t3 : a2 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one zero_le_one ha2 (by linarith) (by linarith) (by linarith)
  have t4 : a4 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one zero_le_one ha4 (by linarith) (by linarith) (by linarith)
  have t5 : b0 * a3 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one hb0 ha3 (by linarith) (by linarith) (by linarith)
  have t6 : b1 * a2 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one hb1 ha2 (by linarith) (by linarith) (by linarith)
  have t7 : b2 * a1 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one hb2 ha1 (by linarith) (by linarith) (by linarith)
  have t8 : b3 * a0 ≤ Y * B * A := by
    simpa using term_le_YBA hY hB zero_le_one hb3 ha0 (by linarith) (by linarith) (by linarith)
  have t8' : a0 * b3 ≤ Y * B * A := by linarith
  have t9 : a1 * b2 ≤ Y * B * A := by linarith
  have t10 : a2 * b1 ≤ Y * B * A := by linarith
  have hYBA : 0 ≤ Y * B * A := mul_nonneg (mul_nonneg hY hB) (by positivity)
  linarith

theorem norm_D2_Sfun_le {e d : UnforcedLeray.Space → CVec3}
    {r : UnforcedLeray.Space → UnforcedLeray.Space}
    (he : ContDiff ℝ ∞ e) (hd : ContDiff ℝ ∞ d) (hr : ContDiff ℝ ∞ r) {ν : ℝ} (hν : |ν| ≤ 1)
    (y : UnforcedLeray.Space) (j l : Fin 3) :
    ‖D2 j l (Sfun e d r ν) y‖ ≤ 40 * (1 + ‖y‖) *
      (1 + ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k r y‖) *
      ((∑ k ∈ Finset.range 5, ‖iteratedFDeriv ℝ k e y‖) +
        ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k d y‖) := by
  have hGk : ∀ k : Fin 3, ContDiff ℝ ∞ (D1 k e) := fun k => contDiff_D1 he k
  have hHk : ∀ k : Fin 3, ContDiff ℝ ∞ (D2 k k e) := fun k => contDiff_D2 he k k
  have hRk : ∀ k : Fin 3, ContDiff ℝ ∞ (D1 k r) := fun k => contDiff_D1 hr k
  have hrk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => ((r z k : ℝ) : ℂ)) := fun k =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply (p := 2) (i := k)).comp hr)
  have hek : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => e z k) := fun k =>
    (contDiff_piLp_apply (p := 2) (i := k)).comp he
  have hxk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => z k) := fun k =>
    contDiff_piLp_apply (p := 2) (i := k)
  have hrealR : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => realC (D1 k r z)) := fun k => by
    have : (fun z => realC (D1 k r z)) = fun z => realCL (D1 k r z) := by
      funext z; rw [realCL_apply]
    rw [this]; exact realCL.contDiff.comp (hRk k)
  have hc2 : ContDiff ℝ ∞ (fun x => ∑ k : Fin 3, (x k) • D1 k e x) :=
    ContDiff.sum fun k _ => (hxk k).smul (hGk k)
  have hc3 : ContDiff ℝ ∞ (fun x => ∑ k : Fin 3, D2 k k e x) :=
    ContDiff.sum fun k _ => hHk k
  have hc5 : ContDiff ℝ ∞ (fun x => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • D1 k e x) :=
    ContDiff.sum fun k _ => (hrk k).smul (hGk k)
  have hc6 : ContDiff ℝ ∞ (fun x => ∑ k : Fin 3, e x k • realC (D1 k r x)) :=
    ContDiff.sum fun k _ => (hek k).smul (hrealR k)
  have hS_eq : Sfun e d r ν = fun x =>
      d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k e x
        - ν • ∑ k : Fin 3, D2 k k e x
        - (1 / 2 : ℝ) • e x
        + ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • D1 k e x
        + ∑ k : Fin 3, e x k • realC (D1 k r x) := rfl
  have h12 : ContDiff ℝ ∞ (fun x => d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k e x) :=
    hd.sub (hc2.const_smul _)
  have h123 : ContDiff ℝ ∞ (fun x =>
      d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k e x - ν • ∑ k : Fin 3, D2 k k e x) :=
    h12.sub (hc3.const_smul _)
  have h1234 : ContDiff ℝ ∞ (fun x =>
      d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k e x - ν • ∑ k : Fin 3, D2 k k e x -
        (1 / 2 : ℝ) • e x) :=
    h123.sub (he.const_smul _)
  have h12345 : ContDiff ℝ ∞ (fun x =>
      d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k e x - ν • ∑ k : Fin 3, D2 k k e x -
        (1 / 2 : ℝ) • e x + ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • D1 k e x) :=
    h1234.add hc5
  have hD2_S : D2 j l (Sfun e d r ν) y =
      D2 j l d y
        - (1 / 2 : ℝ) • ∑ k : Fin 3, D2 j l (fun x => (x k) • D1 k e x) y
        - ν • ∑ k : Fin 3, D2 j l (D2 k k e) y
        - (1 / 2 : ℝ) • D2 j l e y
        + ∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y
        + ∑ k : Fin 3, D2 j l (fun x => e x k • realC (D1 k r x)) y := by
    rw [hS_eq,
      D2_add h12345 hc6 j l y,
      D2_add h1234 hc5 j l y,
      D2_sub h123 (he.const_smul _) j l y,
      D2_sub h12 (hc3.const_smul _) j l y,
      D2_sub hd (hc2.const_smul _) j l y,
      D2_const_smul hc2 (1 / 2 : ℝ) j l y,
      D2_const_smul hc3 ν j l y,
      D2_const_smul he (1 / 2 : ℝ) j l y,
      D2_sum (F := fun k x => (x k) • D1 k e x) (fun k => (hxk k).smul (hGk k)) j l y,
      D2_sum (F := fun k => D2 k k e) hHk j l y,
      D2_sum (F := fun k x => ((r x k : ℝ) : ℂ) • D1 k e x) (fun k => (hrk k).smul (hGk k)) j l y,
      D2_sum (F := fun k x => e x k • realC (D1 k r x)) (fun k => (hek k).smul (hrealR k)) j l y]
  rw [hD2_S]
  set a0 := ‖iteratedFDeriv ℝ 0 e y‖ with ha0
  set a1 := ‖iteratedFDeriv ℝ 1 e y‖
  set a2 := ‖iteratedFDeriv ℝ 2 e y‖
  set a3 := ‖iteratedFDeriv ℝ 3 e y‖
  set a4 := ‖iteratedFDeriv ℝ 4 e y‖
  set d0 := ‖iteratedFDeriv ℝ 0 d y‖
  set d1 := ‖iteratedFDeriv ℝ 1 d y‖
  set d2 := ‖iteratedFDeriv ℝ 2 d y‖
  set b0 := ‖iteratedFDeriv ℝ 0 r y‖ with hb0
  set b1 := ‖iteratedFDeriv ℝ 1 r y‖
  set b2 := ‖iteratedFDeriv ℝ 2 r y‖
  set b3 := ‖iteratedFDeriv ℝ 3 r y‖
  have e0 : ‖e y‖ = a0 := by rw [ha0, norm_iteratedFDeriv_zero]
  have r0 : ‖r y‖ = b0 := by rw [hb0, norm_iteratedFDeriv_zero]
  have bD2 : ‖D2 j l d y‖ ≤ d2 := norm_D2_le hd j l y
  have bE1 : ∀ k : Fin 3, ‖D1 k e y‖ ≤ a1 := fun k => norm_D1_le he k y
  have bE2 : ∀ m k : Fin 3, ‖D2 m k e y‖ ≤ a2 := fun m k => norm_D2_le he m k y
  have bE3 : ∀ k : Fin 3, ‖D2 j l (D1 k e) y‖ ≤ a3 := fun k => norm_D2_D1_le he j l k y
  have bE4 : ∀ k : Fin 3, ‖D2 j l (D2 k k e) y‖ ≤ a4 := fun k => norm_D2_D2_le he j l k k y
  have bR1 : ∀ k : Fin 3, ‖D1 k r y‖ ≤ b1 := fun k => norm_D1_le hr k y
  have bR2 : ∀ m k : Fin 3, ‖D2 m k r y‖ ≤ b2 := fun m k => norm_D2_le hr m k y
  have bR3 : ∀ k : Fin 3, ‖D2 j l (D1 k r) y‖ ≤ b3 := fun k => norm_D2_D1_le hr j l k y
  have P2 : ∀ k : Fin 3, ‖D2 j l (fun x => (x k) • D1 k e x) y‖ ≤
      ‖y‖ * a3 + a2 + (a2 + 0) := fun k => by
    refine (norm_D2_smul_le (𝕜 := ℝ) (hxk k) (hGk k) j l y).trans ?_
    have c1 : ‖y k‖ ≤ ‖y‖ := abs_coord_le (𝕜 := ℝ) y k
    have c2 : ‖D1 j (fun x : UnforcedLeray.Space => x k) y‖ ≤ 1 := norm_D1_proj_le k j y
    have c3 : ‖D1 l (fun x : UnforcedLeray.Space => x k) y‖ ≤ 1 := norm_D1_proj_le k l y
    have c4 : ‖D2 j l (fun x : UnforcedLeray.Space => x k) y‖ = 0 := norm_D2_proj_eq_zero j l k y
    have g0 := bE1 k
    have g1l : ‖D1 l (D1 k e) y‖ ≤ a2 := bE2 l k
    have g1j : ‖D1 j (D1 k e) y‖ ≤ a2 := bE2 j k
    have g2 := bE3 k
    rw [c4, zero_mul]
    calc _ ≤ ‖y‖ * a3 + 1 * a2 + (1 * a2 + 0) := by gcongr
      _ = _ := by ring
  have P5 : ∀ k : Fin 3, ‖D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y‖ ≤
      b0 * a3 + b1 * a2 + (b1 * a2 + b2 * a1) := fun k => by
    refine (norm_D2_smul_le (𝕜 := ℂ) (hrk k) (hGk k) j l y).trans ?_
    have c1 : ‖((r y k : ℝ) : ℂ)‖ ≤ b0 := by
      rw [← r0, Complex.norm_real]; exact abs_coord_le (𝕜 := ℝ) (r y) k
    have c2 : ‖D1 j (fun z => ((r z k : ℝ) : ℂ)) y‖ ≤ b1 :=
      (norm_D1_ofReal_coord_le hr k j y).trans (bR1 j)
    have c3 : ‖D1 l (fun z => ((r z k : ℝ) : ℂ)) y‖ ≤ b1 :=
      (norm_D1_ofReal_coord_le hr k l y).trans (bR1 l)
    have c4 : ‖D2 j l (fun z => ((r z k : ℝ) : ℂ)) y‖ ≤ b2 :=
      (norm_D2_ofReal_coord_le hr j l k y).trans (bR2 j l)
    have g0 := bE1 k
    have g1l : ‖D1 l (D1 k e) y‖ ≤ a2 := bE2 l k
    have g1j : ‖D1 j (D1 k e) y‖ ≤ a2 := bE2 j k
    have g2 := bE3 k
    gcongr
  have P6 : ∀ k : Fin 3, ‖D2 j l (fun x => e x k • realC (D1 k r x)) y‖ ≤
      a0 * b3 + a1 * b2 + (a1 * b2 + a2 * b1) := fun k => by
    refine (norm_D2_smul_le (𝕜 := ℂ) (hek k) (hrealR k) j l y).trans ?_
    have c1 : ‖e y k‖ ≤ a0 := by rw [← e0]; exact abs_coord_le (𝕜 := ℂ) (e y) k
    have c2 : ‖D1 j (fun z => e z k) y‖ ≤ a1 :=
      (norm_D1_coord_le he k j y).trans (bE1 j)
    have c3 : ‖D1 l (fun z => e z k) y‖ ≤ a1 :=
      (norm_D1_coord_le he k l y).trans (bE1 l)
    have c4 : ‖D2 j l (fun z => e z k) y‖ ≤ a2 :=
      (norm_D2_coord_le he j l k y).trans (bE2 j l)
    have g0 : ‖realC (D1 k r y)‖ ≤ b1 := by rw [norm_realC]; exact bR1 k
    have g1l : ‖D1 l (fun z => realC (D1 k r z)) y‖ ≤ b2 := by
      rw [norm_D1_realC (hRk k) l y]; exact bR2 l k
    have g1j : ‖D1 j (fun z => realC (D1 k r z)) y‖ ≤ b2 := by
      rw [norm_D1_realC (hRk k) j y]; exact bR2 j k
    have g2 : ‖D2 j l (fun z => realC (D1 k r z)) y‖ ≤ b3 := by
      rw [norm_D2_realC (hRk k) j l y]; exact bR3 k
    gcongr
  have n2 : ‖∑ k : Fin 3, D2 j l (fun x => (x k) • D1 k e x) y‖ ≤
      3 * (‖y‖ * a3 + a2 + (a2 + 0)) := (norm_sum_le _ _).trans (sum3_le _ _ P2)
  have n3 : ‖∑ k : Fin 3, D2 j l (D2 k k e) y‖ ≤ 3 * a4 :=
    (norm_sum_le _ _).trans (sum3_le a4 _ bE4)
  have n4 : ‖D2 j l e y‖ ≤ a2 := bE2 j l
  have n5 : ‖∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y‖ ≤
      3 * (b0 * a3 + b1 * a2 + (b1 * a2 + b2 * a1)) := (norm_sum_le _ _).trans (sum3_le _ _ P5)
  have n6 : ‖∑ k : Fin 3, D2 j l (fun x => e x k • realC (D1 k r x)) y‖ ≤
      3 * (a0 * b3 + a1 * b2 + (a1 * b2 + a2 * b1)) := (norm_sum_le _ _).trans (sum3_le _ _ P6)
  have total : ‖D2 j l d y
        - (1 / 2 : ℝ) • ∑ k : Fin 3, D2 j l (fun x => (x k) • D1 k e x) y
        - ν • ∑ k : Fin 3, D2 j l (D2 k k e) y
        - (1 / 2 : ℝ) • D2 j l e y
        + ∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y
        + ∑ k : Fin 3, D2 j l (fun x => e x k • realC (D1 k r x)) y‖ ≤
      d2 + (1 / 2) * (3 * (‖y‖ * a3 + a2 + (a2 + 0))) + |ν| * (3 * a4) + (1 / 2) * a2 +
        3 * (b0 * a3 + b1 * a2 + (b1 * a2 + b2 * a1)) +
        3 * (a0 * b3 + a1 * b2 + (a1 * b2 + a2 * b1)) := by
    refine (norm6_le _ _ _ _ _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := mul_le_mul_of_nonneg_left n2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have := mul_le_mul_of_nonneg_left n3 (abs_nonneg ν)
    have := mul_le_mul_of_nonneg_left n4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  refine total.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact arith2_bound ‖y‖ a0 a1 a2 a3 a4 d0 d1 d2 b0 b1 b2 b3 ν
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hν

end Jets2

open Jets Jets2 in
theorem inletFn2_slice_eq (p : Params) (i : Fin 2) (j l : Fin 3)
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2))
    (τ : ℝ) (y : UnforcedLeray.Space)
    {S : UnforcedLeray.Space → CVec3} (hSfun : ContDiff ℝ ∞ S)
    (hslice : ∀ x, inletSrc p i (τ, x) = S x) :
    inletFn2 p i j l (τ, y) = D2 j l S y := by
  have hS : ContDiff ℝ ∞ (inletSrc p i) := inletSrc_contDiff hE hR
  have hF1 : ContDiff ℝ ∞ (inletFn p i l) := (UnforcedLeray.PhaseSpace.contDiff_dy hS l).neg
  have e_src : (fun x : UnforcedLeray.Space => inletSrc p i (τ, x)) = S := funext hslice
  have e_fn1 : (fun z : UnforcedLeray.Space => inletFn p i l (τ, z)) = fun z => -D1 l S z := by
    funext z
    unfold inletFn D1
    simp only [Pi.neg_apply]
    rw [dy_slice _ (hS.differentiable (by simp)) l τ z, e_src]
  unfold inletFn2
  simp only [Pi.neg_apply]
  rw [dy_slice _ (hF1.differentiable (by simp)) j τ y, e_fn1,
    show fderiv ℝ (fun z => -D1 l S z) y (ek j) = D1 j (fun z => -D1 l S z) y from rfl,
    congrFun (D1_neg (contDiff_D1 hSfun l) j) y, neg_neg]
  rfl

open Jets Jets2 in
/-- **`inletSrcDeriv2Bound : InletSrcDeriv2Bound`** (source 2545-2551, 2563-2569). -/
theorem inletSrcDeriv2Bound : InletSrcDeriv2Bound := by
  refine ⟨40, by norm_num, fun p i j l hν hE hR τ y => ?_⟩
  have hν1 : |p.ν| ≤ 1 := by rw [abs_of_pos p.ν_pos]; exact hν
  have hsl : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk contDiff_id
  have he : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => p.Efun i (τ, z)) := by
    have := ContDiff.comp (g := p.Efun i) hE hsl
    exact this
  have hr : ContDiff ℝ ∞ (p.raw τ) := by
    have := ContDiff.comp (g := fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) hR hsl
    exact this
  have hd : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => dτ (p.Efun i) (τ, z)) := by
    have := ContDiff.comp (g := dτ (p.Efun i)) (contDiff_dτ hE) hsl
    exact this
  have hS : ContDiff ℝ ∞ (inletSrc p i) := inletSrc_contDiff hE hR
  have hSfun : ContDiff ℝ ∞
      (Sfun (fun z => p.Efun i (τ, z)) (fun z => dτ (p.Efun i) (τ, z)) (p.raw τ) p.ν) := by
    have e1 : Sfun (fun z => p.Efun i (τ, z)) (fun z => dτ (p.Efun i) (τ, z)) (p.raw τ) p.ν =
        (inletSrc p i) ∘ (fun x : UnforcedLeray.Space => (τ, x)) :=
      funext fun x => (inletSrc_slice p i hE τ x).symm
    rw [e1]
    have := ContDiff.comp (g := inletSrc p i) hS hsl
    exact this
  rw [inletFn2_slice_eq p i j l hE hR τ y hSfun (inletSrc_slice p i hE τ)]
  exact norm_D2_Sfun_le he hd hr hν1 y j l

end UnforcedLeray.Short.PartIIIb.Concrete
