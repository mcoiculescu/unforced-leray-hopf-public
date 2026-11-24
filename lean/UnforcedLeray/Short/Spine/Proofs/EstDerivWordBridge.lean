import UnforcedLeray.Units.B0151.Linf
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Spine: the generic word-derivative bridge (task `Spine:EstDerivWordBridge`)

No counterpart in the source. This is the generic bridge behind the sup bound
`‖D^j V_c^p‖_∞ ≤ C_j a^{-(3+j)/2}` (source `the November 2 reference manuscript`,
line 332). If every iterated word derivative of length `j` of a smooth `f` is bounded by `M` at a
point `z` (`true = ∂_q`, `false = ∂_η`, `B0151.derivWord`), then the norm of the `j`-th Fréchet
derivative of `f` at `z` is at most `2 ^ j * M`.

Proof. The Fréchet derivative of order `j + 1` of `f` is the order-`j` derivative of `fderiv ℝ f`,
and `fderiv ℝ f = Φ ∘ (∂_q f, ∂_η f)` for the fixed continuous linear map
`Φ (u, v) = u • fst + v • snd`, which has norm at most `2`. Induction on `j` (for all smooth `f` at
once) bounds the two components by `2 ^ j * M`, the norm of a pair of multilinear maps is the
maximum of the two norms, and the composition bound closes the step.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.Spine

/-- The words of `∂_q f` are the words of `f` followed by the letter `true`. -/
theorem estDW_derivWord_partialX (f : ℝ × ℝ → ℝ) :
    ∀ w : List Bool, UnforcedLeray.B0151.derivWord w (UnforcedLeray.GaussianVortex.partialX f) =
      UnforcedLeray.B0151.derivWord (w ++ [true]) f
  | [] => rfl
  | true :: w => by
    simp only [List.cons_append, UnforcedLeray.B0151.derivWord, estDW_derivWord_partialX f w]
  | false :: w => by
    simp only [List.cons_append, UnforcedLeray.B0151.derivWord, estDW_derivWord_partialX f w]

/-- The words of `∂_η f` are the words of `f` followed by the letter `false`. -/
theorem estDW_derivWord_partialY (f : ℝ × ℝ → ℝ) :
    ∀ w : List Bool, UnforcedLeray.B0151.derivWord w (UnforcedLeray.GaussianVortex.partialY f) =
      UnforcedLeray.B0151.derivWord (w ++ [false]) f
  | [] => rfl
  | true :: w => by
    simp only [List.cons_append, UnforcedLeray.B0151.derivWord, estDW_derivWord_partialY f w]
  | false :: w => by
    simp only [List.cons_append, UnforcedLeray.B0151.derivWord, estDW_derivWord_partialY f w]

/-- The derivative in coordinates: `fderiv ℝ f z v = v.1 ∂_q f(z) + v.2 ∂_η f(z)`. -/
theorem estDW_fderiv_apply {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z v : ℝ × ℝ) :
    fderiv ℝ f z v = v.1 * UnforcedLeray.GaussianVortex.partialX f z +
      v.2 * UnforcedLeray.GaussianVortex.partialY f z := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [UnforcedLeray.B0151.partialX_eq_fderiv hf z, UnforcedLeray.B0151.partialY_eq_fderiv hf z]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The continuous linear map `(u, v) ↦ u • fst + v • snd` from `ℝ × ℝ` to its dual. -/
def estDW_Phi : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem estDW_Phi_apply (a v : ℝ × ℝ) : estDW_Phi a v = a.1 * v.1 + a.2 * v.2 := by
  simp [estDW_Phi]

theorem estDW_Phi_eq (u : ℝ × ℝ) :
    estDW_Phi u = u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [estDW_Phi_apply]

theorem estDW_norm_Phi_le : ‖estDW_Phi‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun u => ?_
  rw [estDW_Phi_eq]
  have h1 : ‖u.1‖ ≤ ‖u‖ := norm_fst_le u
  have h2 : ‖u.2‖ ≤ ‖u‖ := norm_snd_le u
  have hf : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have hs : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  calc ‖u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ ‖u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ‖ + ‖u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ‖ :=
        norm_add_le _ _
    _ = ‖u.1‖ * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ + ‖u.2‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ := by
        rw [norm_smul, norm_smul]
    _ ≤ ‖u‖ * 1 + ‖u‖ * 1 :=
        add_le_add (mul_le_mul h1 hf (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul h2 hs (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖u‖ := by ring

/-- Induction on the order `j`, for all smooth `f` at once, at a fixed point `z` and bound `M`. -/
theorem estDW_norm_aux (j : ℕ) (z : ℝ × ℝ) (M : ℝ) :
    ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ ∞ f →
      (∀ w : List Bool, w.length = j → |UnforcedLeray.B0151.derivWord w f z| ≤ M) →
      ‖iteratedFDeriv ℝ j f z‖ ≤ 2 ^ j * M := by
  induction j with
  | zero =>
    intro f _ hM
    have h : |f z| ≤ M := hM [] rfl
    rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_eq_abs]
    exact h
  | succ j ih =>
    intro f hf hM
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    have hX : ContDiff ℝ ∞ (UnforcedLeray.GaussianVortex.partialX f) :=
      UnforcedLeray.B0151.contDiff_partialX_infty hf
    have hY : ContDiff ℝ ∞ (UnforcedLeray.GaussianVortex.partialY f) :=
      UnforcedLeray.B0151.contDiff_partialY_infty hf
    have hG : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
        (UnforcedLeray.GaussianVortex.partialX f x, UnforcedLeray.GaussianVortex.partialY f x)) :=
      hX.prodMk hY
    have hGz : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ =>
        (UnforcedLeray.GaussianVortex.partialX f x, UnforcedLeray.GaussianVortex.partialY f x)) z :=
      hG.contDiffAt
    have hjle : (j : WithTop ℕ∞) ≤ ∞ := by simp
    have hfd : fderiv ℝ f = estDW_Phi ∘ (fun x : ℝ × ℝ =>
        (UnforcedLeray.GaussianVortex.partialX f x, UnforcedLeray.GaussianVortex.partialY f x)) := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp only [Function.comp_apply, estDW_Phi_apply]
      rw [estDW_fderiv_apply hd x v]
      ring
    have hsucc : ‖iteratedFDeriv ℝ (j + 1) f z‖ = ‖iteratedFDeriv ℝ j (fderiv ℝ f) z‖ :=
      norm_iteratedFDeriv_fderiv.symm
    have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (n := j) estDW_Phi hGz hjle
    have hprod : iteratedFDeriv ℝ j (fun x : ℝ × ℝ =>
        (UnforcedLeray.GaussianVortex.partialX f x, UnforcedLeray.GaussianVortex.partialY f x)) z =
        (iteratedFDeriv ℝ j (UnforcedLeray.GaussianVortex.partialX f) z).prod
          (iteratedFDeriv ℝ j (UnforcedLeray.GaussianVortex.partialY f) z) :=
      iteratedFDeriv_prodMk hX.contDiffAt hY.contDiffAt hjle
    have hIH : ‖iteratedFDeriv ℝ j (fun x : ℝ × ℝ =>
        (UnforcedLeray.GaussianVortex.partialX f x, UnforcedLeray.GaussianVortex.partialY f x)) z‖
          ≤ 2 ^ j * M := by
      rw [hprod, ContinuousMultilinearMap.opNorm_prod]
      refine max_le (ih _ hX ?_) (ih _ hY ?_)
      · intro w hw
        rw [estDW_derivWord_partialX f w]
        exact hM (w ++ [true]) (by simp [hw])
      · intro w hw
        rw [estDW_derivWord_partialY f w]
        exact hM (w ++ [false]) (by simp [hw])
    calc ‖iteratedFDeriv ℝ (j + 1) f z‖ = ‖iteratedFDeriv ℝ j (fderiv ℝ f) z‖ := hsucc
      _ = ‖iteratedFDeriv ℝ j (estDW_Phi ∘ (fun x : ℝ × ℝ =>
            (UnforcedLeray.GaussianVortex.partialX f x,
              UnforcedLeray.GaussianVortex.partialY f x))) z‖ := by rw [hfd]
      _ ≤ ‖estDW_Phi‖ * ‖iteratedFDeriv ℝ j (fun x : ℝ × ℝ =>
            (UnforcedLeray.GaussianVortex.partialX f x,
              UnforcedLeray.GaussianVortex.partialY f x)) z‖ := hcomp
      _ ≤ 2 * (2 ^ j * M) := mul_le_mul estDW_norm_Phi_le hIH (norm_nonneg _) (by norm_num)
      _ = 2 ^ (j + 1) * M := by ring

/-- **Generic bridge.** If every word derivative `derivWord w f z` with `w.length = j` is bounded by
`M`, then the `j`-th Fréchet derivative of the smooth field `f` at `z` has norm at most `2 ^ j * M`
(B0151 word derivatives; `true = ∂_q`, `false = ∂_η`). Used for the sup bound at source line 332. -/
theorem norm_iteratedFDeriv_le_of_derivWord {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ)
    (z : ℝ × ℝ) {M : ℝ} (hM : ∀ w : List Bool, w.length = j → |B0151.derivWord w f z| ≤ M) :
    ‖iteratedFDeriv ℝ j f z‖ ≤ 2 ^ j * M :=
  estDW_norm_aux j z M f hf hM

end UnforcedLeray.Short.Spine
