import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Residual
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.Lattice
import UnforcedLeray.Units.B0151.OneDim

/-!
# Part III-a, task `PartIII-a:T22/2/2/3`: Gaussian-cylinder defect and periodic jet bounds

Source of record: `the November 2 reference manuscript` (SP), lines 3141-3160 and
3211-3214 (`ResidualBoundAux.CanonicalGaussAndJetBound` in `Sub/PartIII-a_T22_2_2.lean`).

Given `m > 8` (`k_w = ⌈m⌉ + 2`), `d ≥ 1`, and an angular-two radial profile `f` (`MemXG f`,
`ContDiffOn ℝ ∞ f (Ioi 0)`) representing `u ∈ X_{G,8}` (`G₈ = √(graphNormSq 8 u)`):
1. **Zero-loss Gaussian `C²` Hermite synthesis**:
   Every Schwartz function `χ ∈ 𝓢(ℝ², ℂ)` obeys the 2D `H² ↪ L^∞` bound
   `‖χ(z)‖² ≤ ‖χ‖₂² + ‖A₁ χ‖₂² + ‖A₀ χ‖₂² + ‖A₁ A₀ χ‖₂²`. Applied to `A_w (φS ℓ)` (`|w| ≤ 2`),
   the conjugated Hermite level `gS (φS ℓ)` and its first two Fréchet derivatives retain full
   `O((1 + ℓ)² e^{-|z|²/8})` decay. Summing against `⟪oscBasis ℓ, u⟫` (`u ∈ X_{G,8}`) yields a
   `C²` planar function `F_∞` matching `planarMode f` everywhere on `ℝ²` with `C²` jet bounded by
   `O(G₈ e^{-|z|²/8})` and `L²(G⁻¹ dy)` norm `√(2π) ‖u‖`.
2. **Exponential lattice tails and periodic jet/velocity bounds**:
   Periodizing `e = planarMode f` on period `d ≥ 1` gives `ContDiff ℝ 2 W`, exponential cell
   tail `O(e^{-d²/128} G₈ e^{-|y|²/16})` for `W - e` and `pdCx k W - pdCx k e`, and uniform cell
   bounds `jb(y)^{k_w} ‖pdCx k W(y)‖ ≤ C G₈` and `‖kerVelCx d W y k‖ ≤ C G₈`.
3. **Even zero-mass zero-dipole image expansion (`O(d⁻⁴) ‖u‖ + O(e^{-2 a_g d²}) G₈`)**:
   Splitting `kerVelCx d W - kerVelPlanarCx e` at radius `d / 4` (for `|y| ≤ d / 8`), the `O(d⁻²)`
   linear image term of `cylinderBS_image_expansion'` integrates to `0` on `{|z| < d / 4}` by
   quarter-turn (`e(-z₂, z₁) = -e(z)`) and central (`e(-z) = e(z)`) symmetries of `planarMode f`,
   leaving only the `O(|y - z|³ / d⁴)` remainder controlled by `‖u‖`, while all cross-cell and far
   contributions decay exponentially as `O(e^{-d²/1024}) G₈`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Polynomial
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate SchwartzMap

namespace UnforcedLeray.Short.IIIa.T22Sub

namespace GaussAndJetBoundAux

open UnforcedLeray.Short.IIIa
open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0121

/-! ### 1. Two-dimensional Schwartz sup bound and `Aop` dominance -/

private theorem norm_J_sq_eq_integral (ψ : S2) :
    ‖J ψ‖ ^ 2 = ∫ z : ℝ × ℝ, ‖ψ z‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_J]
  have h : pairS ψ ψ = ((∫ z : ℝ × ℝ, ‖ψ z‖ ^ 2 : ℝ) : ℂ) := by
    rw [pairS, ← integral_complex_ofReal]
    congr 1
    funext z
    rw [Complex.conj_mul']
    norm_cast
  simp [h]

private theorem norm_J_dop_sq_le_Aop (i : Fin 2) (φ : S2) :
    ‖J (dop i φ)‖ ^ 2 ≤ ‖J (Aop i φ)‖ ^ 2 := by
  have hre_norm : ∀ ψ : S2, (⟪J ψ, J ψ⟫_ℂ).re = ‖J ψ‖ ^ 2 := fun ψ => by
    simpa using (@norm_sq_eq_re_inner ℂ _ _ _ _ (J ψ)).symm
  have hexp : ‖J (Aop i φ)‖ ^ 2 =
      ‖J (dop i φ)‖ ^ 2 + 4⁻¹ * ‖J φ‖ ^ 2 + 16⁻¹ * ‖J (B0121.X i φ)‖ ^ 2 := by
    rw [← hre_norm (Aop i φ), inner_Aop, Bop_Aop, map_add, map_add, map_neg,
      map_smul, map_smul, inner_add_right, inner_add_right, inner_neg_right,
      inner_smul_right, inner_smul_right]
    have h1 : (⟪J φ, J (dop i (dop i φ))⟫_ℂ).re = -‖J (dop i φ)‖ ^ 2 := by
      have hp : pairS φ (dop i (dop i φ)) = -pairS (dop i φ) (dop i φ) := by
        linear_combination pairS_dop i φ (dop i φ)
      rw [inner_J, hp, Complex.neg_re, ← inner_J, hre_norm]
    have h2 : (⟪J φ, J φ⟫_ℂ).re = ‖J φ‖ ^ 2 := hre_norm φ
    have h3 : (⟪J φ, J (B0121.X i (B0121.X i φ))⟫_ℂ).re = ‖J (B0121.X i φ)‖ ^ 2 := by
      rw [inner_J, ← pairS_X i φ (B0121.X i φ), ← inner_J, hre_norm]
    have hc4 : (4⁻¹ : ℂ) = ((4⁻¹ : ℝ) : ℂ) := by norm_num
    have hc16 : (16⁻¹ : ℂ) = ((16⁻¹ : ℝ) : ℂ) := by norm_num
    rw [hc4, hc16]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [h1, h2, h3]
    ring
  rw [hexp]
  have hnn : 0 ≤ 4⁻¹ * ‖J φ‖ ^ 2 + 16⁻¹ * ‖J (B0121.X i φ)‖ ^ 2 := by positivity
  linarith

private theorem Aop_zero_dop_one (φ : S2) :
    Aop 0 (dop 1 φ) = dop 1 (Aop 0 φ) := by
  rw [Aop_apply, Aop_apply, map_sub, map_smul, dop_comm 0 1 φ, dop_X 1 0 φ,
    crdL_zero_ev_one, Complex.ofReal_zero, zero_smul, zero_add]

private theorem norm_J_dop_dop_sq_le (φ : S2) :
    ‖J (dop 0 (dop 1 φ))‖ ^ 2 ≤ ‖J (Aop 1 (Aop 0 φ))‖ ^ 2 := by
  calc ‖J (dop 0 (dop 1 φ))‖ ^ 2
      ≤ ‖J (Aop 0 (dop 1 φ))‖ ^ 2 := norm_J_dop_sq_le_Aop 0 (dop 1 φ)
    _ = ‖J (dop 1 (Aop 0 φ))‖ ^ 2 := by rw [Aop_zero_dop_one]
    _ ≤ ‖J (Aop 1 (Aop 0 φ))‖ ^ 2 := norm_J_dop_sq_le_Aop 1 (Aop 0 φ)

private theorem schwartz_norm_bound (ψ : S2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ, (1 + ‖z‖ ^ 2) * ‖ψ z‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := ψ.decay' 0 0
  obtain ⟨C₂, hC₂⟩ := ψ.decay' 2 0
  refine ⟨max C₀ 0 + max C₂ 0, by positivity, fun z => ?_⟩
  have b0 := hC₀ z
  have b2 := hC₂ z
  rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at b0
  rw [norm_iteratedFDeriv_zero] at b2
  change ‖ψ z‖ ≤ C₀ at b0
  change ‖z‖ ^ 2 * ‖ψ z‖ ≤ C₂ at b2
  have m0 : C₀ ≤ max C₀ 0 := le_max_left _ _
  have m2 : C₂ ≤ max C₂ 0 := le_max_left _ _
  calc (1 + ‖z‖ ^ 2) * ‖ψ z‖ = ‖ψ z‖ + ‖z‖ ^ 2 * ‖ψ z‖ := by ring
    _ ≤ max C₀ 0 + max C₂ 0 := by linarith

private theorem integrable_slice_fst (ψ : S2) (y : ℝ) :
    Integrable (fun s : ℝ => ‖ψ (s, y)‖) := by
  obtain ⟨C, hC, hb⟩ := schwartz_norm_bound ψ
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_norm.comp (ψ.continuous.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hs : s ^ 2 ≤ ‖(s, y)‖ ^ 2 := by
    have hle : |s| ≤ ‖(s, y)‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_left _ _
    nlinarith [sq_abs s, abs_nonneg s]
  have h1 : 0 < 1 + s ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h1]
  calc ‖ψ (s, y)‖ * (1 + s ^ 2)
      = (1 + s ^ 2) * ‖ψ (s, y)‖ := mul_comm _ _
    _ ≤ (1 + ‖(s, y)‖ ^ 2) * ‖ψ (s, y)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ C := hb (s, y)

private theorem integrable_slice_snd (ψ : S2) (x : ℝ) :
    Integrable (fun t : ℝ => ‖ψ (x, t)‖) := by
  obtain ⟨C, hC, hb⟩ := schwartz_norm_bound ψ
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_norm.comp (ψ.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have ht : t ^ 2 ≤ ‖(x, t)‖ ^ 2 := by
    have hle : |t| ≤ ‖(x, t)‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_right _ _
    nlinarith [sq_abs t, abs_nonneg t]
  have h1 : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h1]
  calc ‖ψ (x, t)‖ * (1 + t ^ 2)
      = (1 + t ^ 2) * ‖ψ (x, t)‖ := mul_comm _ _
    _ ≤ (1 + ‖(x, t)‖ ^ 2) * ‖ψ (x, t)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ C := hb (x, t)

private theorem integrable_re_mul_slice_fst (ψ₁ ψ₂ : S2) (y : ℝ) :
    Integrable (fun s : ℝ => (ψ₁ (s, y)).re * (ψ₂ (s, y)).re) := by
  obtain ⟨C, hC, hb⟩ := schwartz_norm_bound ψ₁
  have hsup : ∀ z, ‖ψ₁ z‖ ≤ C := fun z =>
    (le_mul_of_one_le_left (norm_nonneg _) (by linarith [sq_nonneg ‖z‖])).trans (hb z)
  refine Integrable.mono' ((integrable_slice_fst ψ₂ y).const_mul C)
    (((Complex.continuous_re.comp (ψ₁.continuous.comp (continuous_id.prodMk continuous_const))).mul
      (Complex.continuous_re.comp (ψ₂.continuous.comp (continuous_id.prodMk continuous_const))))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((Complex.abs_re_le_norm _).trans (hsup _))
    (Complex.abs_re_le_norm _) (abs_nonneg _) hC

private theorem integrable_re_mul_slice_snd (ψ₁ ψ₂ : S2) (x : ℝ) :
    Integrable (fun t : ℝ => (ψ₁ (x, t)).re * (ψ₂ (x, t)).re) := by
  obtain ⟨C, hC, hb⟩ := schwartz_norm_bound ψ₁
  have hsup : ∀ z, ‖ψ₁ z‖ ≤ C := fun z =>
    (le_mul_of_one_le_left (norm_nonneg _) (by linarith [sq_nonneg ‖z‖])).trans (hb z)
  refine Integrable.mono' ((integrable_slice_snd ψ₂ x).const_mul C)
    (((Complex.continuous_re.comp (ψ₁.continuous.comp (continuous_const.prodMk continuous_id))).mul
      (Complex.continuous_re.comp (ψ₂.continuous.comp (continuous_const.prodMk continuous_id))))
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((Complex.abs_re_le_norm _).trans (hsup _))
    (Complex.abs_re_le_norm _) (abs_nonneg _) hC

private theorem integrable_re_sq (ψ : S2) :
    Integrable (fun z : ℝ × ℝ => (ψ z).re ^ 2) := by
  refine Integrable.mono' (integrable_conj_mul ψ ψ).norm
    ((Complex.continuous_re.comp ψ.continuous).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_conj, ← sq, ← sq_abs ((ψ z).re)]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (ψ z)) 2

private theorem hasDerivAt_re_fst (ψ : S2) (s y : ℝ) :
    HasDerivAt (fun x : ℝ => (ψ (x, y)).re) ((dop 0 ψ (s, y)).re) s := by
  have hp : HasDerivAt (fun x : ℝ => (x, y)) (ev 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have hψ : HasDerivAt (fun x : ℝ => ψ (x, y)) (dop 0 ψ (s, y)) s :=
    (ψ.hasFDerivAt (s, y)).comp_hasDerivAt s hp
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hψ

private theorem hasDerivAt_re_snd (ψ : S2) (x t : ℝ) :
    HasDerivAt (fun y : ℝ => (ψ (x, y)).re) ((dop 1 ψ (x, t)).re) t := by
  have hp : HasDerivAt (fun y : ℝ => (x, y)) (ev 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hψ : HasDerivAt (fun y : ℝ => ψ (x, y)) (dop 1 ψ (x, t)) t :=
    (ψ.hasFDerivAt (x, t)).comp_hasDerivAt t hp
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hψ

private theorem re_sq_le_slice_snd (ψ : S2) (x y : ℝ) :
    (ψ (x, y)).re ^ 2 ≤ ∫ t : ℝ, ((ψ (x, t)).re ^ 2 + (dop 1 ψ (x, t)).re ^ 2) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (ψ (x, u)).re ^ 2)
      (2 * (ψ (x, t)).re * (dop 1 ψ (x, t)).re) t := fun t => by
    simpa [pow_one, mul_assoc] using! (hasDerivAt_re_snd ψ x t).fun_pow 2
  have hi0 : Integrable (fun u : ℝ => (ψ (x, u)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd ψ ψ x
  have hi1 : Integrable (fun u : ℝ => 2 * (ψ (x, u)).re * (dop 1 ψ (x, u)).re) := by
    simpa [mul_assoc] using (integrable_re_mul_slice_snd ψ (dop 1 ψ) x).const_mul 2
  have hi_rhs : Integrable (fun t : ℝ => (ψ (x, t)).re ^ 2 + (dop 1 ψ (x, t)).re ^ 2) :=
    hi0.add (by simpa [sq] using integrable_re_mul_slice_snd (dop 1 ψ) (dop 1 ψ) x)
  have h1 := UnforcedLeray.B0151.abs_le_integral_deriv hd hi1 hi0 y
  rw [abs_of_nonneg (sq_nonneg _)] at h1
  refine h1.trans (integral_mono hi1.abs hi_rhs fun t => ?_)
  dsimp only
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg (|(ψ (x, t)).re| - |(dop 1 ψ (x, t)).re|),
    sq_abs (ψ (x, t)).re, sq_abs (dop 1 ψ (x, t)).re]

private theorem re_sq_le_integral_2d (ψ : S2) (z : ℝ × ℝ) :
    (ψ z).re ^ 2 ≤ ∫ w : ℝ × ℝ,
      ((ψ w).re ^ 2 + (dop 1 ψ w).re ^ 2 + (dop 0 ψ w).re ^ 2 + (dop 1 (dop 0 ψ) w).re ^ 2) := by
  rcases z with ⟨x, y⟩
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => (ψ (u, y)).re ^ 2)
      (2 * (ψ (s, y)).re * (dop 0 ψ (s, y)).re) s := fun s => by
    simpa [pow_one, mul_assoc] using! (hasDerivAt_re_fst ψ s y).fun_pow 2
  have hi0 : Integrable (fun s : ℝ => (ψ (s, y)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_fst ψ ψ y
  have hi1 : Integrable (fun s : ℝ => 2 * (ψ (s, y)).re * (dop 0 ψ (s, y)).re) := by
    simpa [mul_assoc] using (integrable_re_mul_slice_fst ψ (dop 0 ψ) y).const_mul 2
  have hi_mid : Integrable (fun s : ℝ => (ψ (s, y)).re ^ 2 + (dop 0 ψ (s, y)).re ^ 2) :=
    hi0.add (by simpa [sq] using integrable_re_mul_slice_fst (dop 0 ψ) (dop 0 ψ) y)
  have hstep1 : (ψ (x, y)).re ^ 2 ≤ ∫ s : ℝ, ((ψ (s, y)).re ^ 2 + (dop 0 ψ (s, y)).re ^ 2) := by
    have h1 := UnforcedLeray.B0151.abs_le_integral_deriv hd hi1 hi0 x
    rw [abs_of_nonneg (sq_nonneg _)] at h1
    refine h1.trans (integral_mono hi1.abs hi_mid fun s => ?_)
    dsimp only
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_nonneg (|(ψ (s, y)).re| - |(dop 0 ψ (s, y)).re|),
      sq_abs (ψ (s, y)).re, sq_abs (dop 0 ψ (s, y)).re]
  set G : ℝ × ℝ → ℝ := fun w =>
    (ψ w).re ^ 2 + (dop 1 ψ w).re ^ 2 + (dop 0 ψ w).re ^ 2 + (dop 1 (dop 0 ψ) w).re ^ 2
  have hG_int : Integrable G :=
    (((integrable_re_sq ψ).add (integrable_re_sq (dop 1 ψ))).add
      (integrable_re_sq (dop 0 ψ))).add (integrable_re_sq (dop 1 (dop 0 ψ)))
  have hslice_int : Integrable (fun s : ℝ => ∫ t : ℝ, G (s, t)) := hG_int.integral_prod_left
  refine hstep1.trans ?_
  change _ ≤ ∫ z : ℝ × ℝ, G z ∂(volume.prod volume)
  rw [integral_prod G hG_int]
  refine integral_mono hi_mid hslice_int fun s => ?_
  have ha := re_sq_le_slice_snd ψ s y
  have hb := re_sq_le_slice_snd (dop 0 ψ) s y
  have ia1 : Integrable (fun t : ℝ => (ψ (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd ψ ψ s
  have ia2 : Integrable (fun t : ℝ => (dop 1 ψ (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd (dop 1 ψ) (dop 1 ψ) s
  have ia : Integrable (fun t : ℝ => (ψ (s, t)).re ^ 2 + (dop 1 ψ (s, t)).re ^ 2) := ia1.add ia2
  have ib1 : Integrable (fun t : ℝ => (dop 0 ψ (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd (dop 0 ψ) (dop 0 ψ) s
  have ib2 : Integrable (fun t : ℝ => (dop 1 (dop 0 ψ) (s, t)).re ^ 2) := by
    simpa [sq] using integrable_re_mul_slice_snd (dop 1 (dop 0 ψ)) (dop 1 (dop 0 ψ)) s
  have ib : Integrable (fun t : ℝ => (dop 0 ψ (s, t)).re ^ 2 + (dop 1 (dop 0 ψ) (s, t)).re ^ 2) :=
    ib1.add ib2
  calc (ψ (s, y)).re ^ 2 + (dop 0 ψ (s, y)).re ^ 2
      ≤ (∫ t : ℝ, ((ψ (s, t)).re ^ 2 + (dop 1 ψ (s, t)).re ^ 2)) +
          ∫ t : ℝ, ((dop 0 ψ (s, t)).re ^ 2 + (dop 1 (dop 0 ψ) (s, t)).re ^ 2) := add_le_add ha hb
    _ = ∫ t : ℝ, G (s, t) := by
        rw [← integral_add ia ib]
        congr 1; funext t; dsimp [G]; ring

private theorem norm_sq_schwartz_le_Aop (ψ : S2) (z : ℝ × ℝ) :
    ‖ψ z‖ ^ 2 ≤ ‖J ψ‖ ^ 2 + ‖J (Aop 1 ψ)‖ ^ 2 + ‖J (Aop 0 ψ)‖ ^ 2 +
      ‖J (Aop 1 (Aop 0 ψ))‖ ^ 2 := by
  have hre := re_sq_le_integral_2d ψ z
  have him := re_sq_le_integral_2d ((-Complex.I) • ψ) z
  have hI_re : ∀ (φ : S2) (w : ℝ × ℝ), (((-Complex.I) • φ) w).re = (φ w).im := fun φ w => by
    simp [smul_eq_mul]
  have hdop_smul : ∀ (i : Fin 2) (φ : S2), dop i ((-Complex.I) • φ) = (-Complex.I) • dop i φ :=
    fun i φ => map_smul (dop i) (-Complex.I) φ
  simp only [hdop_smul, hI_re] at him
  set G_re : ℝ × ℝ → ℝ := fun w =>
    (ψ w).re ^ 2 + (dop 1 ψ w).re ^ 2 + (dop 0 ψ w).re ^ 2 + (dop 1 (dop 0 ψ) w).re ^ 2
  set G_im : ℝ × ℝ → ℝ := fun w =>
    (ψ w).im ^ 2 + (dop 1 ψ w).im ^ 2 + (dop 0 ψ w).im ^ 2 + (dop 1 (dop 0 ψ) w).im ^ 2
  have hi_re : Integrable G_re :=
    (((integrable_re_sq ψ).add (integrable_re_sq (dop 1 ψ))).add
      (integrable_re_sq (dop 0 ψ))).add (integrable_re_sq (dop 1 (dop 0 ψ)))
  have hi_im : Integrable G_im := by
    have eqf : G_im = fun w => (((-Complex.I) • ψ) w).re ^ 2 +
        (dop 1 ((-Complex.I) • ψ) w).re ^ 2 + (dop 0 ((-Complex.I) • ψ) w).re ^ 2 +
        (dop 1 (dop 0 ((-Complex.I) • ψ)) w).re ^ 2 := by
      funext w; simp only [G_im, hdop_smul, hI_re]
    rw [eqf]
    exact (((integrable_re_sq _).add (integrable_re_sq _)).add (integrable_re_sq _)).add
      (integrable_re_sq _)
  have hnorm_sq : ∀ ζ : ℂ, ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := fun ζ => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hint_norm : ∀ φ : S2, Integrable (fun w : ℝ × ℝ => ‖φ w‖ ^ 2) := fun φ =>
    Integrable.mono' (integrable_conj_mul φ φ).norm
      ((continuous_norm.comp φ.continuous).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_conj, ← sq])
  have hsum_z : ‖ψ z‖ ^ 2 ≤ ∫ w : ℝ × ℝ,
      (‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2 + ‖dop 0 ψ w‖ ^ 2 + ‖dop 1 (dop 0 ψ) w‖ ^ 2) := by
    rw [← hnorm_sq (ψ z)]
    refine (add_le_add hre him).trans ?_
    rw [← integral_add hi_re hi_im]
    refine le_of_eq (congrArg (integral volume) (funext fun w => ?_))
    simp only [G_re, G_im, ← hnorm_sq]; ring
  have i12 : Integrable (fun w : ℝ × ℝ => ‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2) :=
    (hint_norm ψ).add (hint_norm (dop 1 ψ))
  have i123 : Integrable (fun w : ℝ × ℝ => ‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2 + ‖dop 0 ψ w‖ ^ 2) :=
    i12.add (hint_norm (dop 0 ψ))
  have hsplit : (∫ w : ℝ × ℝ,
      (‖ψ w‖ ^ 2 + ‖dop 1 ψ w‖ ^ 2 + ‖dop 0 ψ w‖ ^ 2 + ‖dop 1 (dop 0 ψ) w‖ ^ 2)) =
      ‖J ψ‖ ^ 2 + ‖J (dop 1 ψ)‖ ^ 2 + ‖J (dop 0 ψ)‖ ^ 2 + ‖J (dop 0 (dop 1 ψ))‖ ^ 2 := by
    rw [integral_add i123 (hint_norm _), integral_add i12 (hint_norm _),
      integral_add (hint_norm ψ) (hint_norm _),
      ← norm_J_sq_eq_integral, ← norm_J_sq_eq_integral,
      ← norm_J_sq_eq_integral, ← norm_J_sq_eq_integral, dop_comm 1 0 ψ]
  refine hsum_z.trans ?_
  rw [hsplit]
  linarith [norm_J_dop_sq_le_Aop 1 ψ, norm_J_dop_sq_le_Aop 0 ψ, norm_J_dop_dop_sq_le ψ]

/-! ### 2. Hermite-level `C²` Gaussian bounds and smooth series synthesis -/

private theorem norm_J_Aw_φS_sq_le {k : ℕ} (hk : k ≤ 4) (w : Fin k → Fin 2) (ℓ : ℕ) :
    ‖J (Aw k w (φS ℓ))‖ ^ 2 ≤ 2592 * Real.pi * (1 + (ℓ : ℝ)) ^ 4 := by
  have hchi : chi {ℓ} (fun _ => 1) = φS ℓ := by simp [chi]
  have h1 : ‖J (Aw k w (φS ℓ))‖ ^ 2 ≤ ∑ w' : Fin k → Fin 2, ‖J (Aw k w' (φS ℓ))‖ ^ 2 :=
    Finset.single_le_sum (f := fun w' => ‖J (Aw k w' (φS ℓ))‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
  have h2 := sum_norm_sq_Aw_chi k {ℓ} (fun _ => 1)
  simp only [hchi, Finset.sum_singleton, norm_one, one_pow, mul_one] at h2
  have h3 := qpoly_le hk ℓ
  norm_num at h3
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  nlinarith

private theorem norm_Aw_φS_le {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 2) (ℓ : ℕ) (z : ℝ × ℝ) :
    ‖Aw k w (φS ℓ) z‖ ≤ 204 * (1 + (ℓ : ℝ)) ^ 2 := by
  set ψ := Aw k w (φS ℓ)
  have e1 : Aop 1 ψ = Aw (k + 1) (Fin.cons 1 w) (φS ℓ) := by
    simp [ψ, Aw_succ]
  have e0 : Aop 0 ψ = Aw (k + 1) (Fin.cons 0 w) (φS ℓ) := by
    simp [ψ, Aw_succ]
  have e10 : Aop 1 (Aop 0 ψ) = Aw (k + 2) (Fin.cons 1 (Fin.cons 0 w)) (φS ℓ) := by
    rw [e0]; simp [Aw_succ]
  have b0 := norm_J_Aw_φS_sq_le (by omega : k ≤ 4) w ℓ
  have b1 := norm_J_Aw_φS_sq_le (by omega : k + 1 ≤ 4) (Fin.cons 1 w) ℓ
  have b2 := norm_J_Aw_φS_sq_le (by omega : k + 1 ≤ 4) (Fin.cons 0 w) ℓ
  have b3 := norm_J_Aw_φS_sq_le (by omega : k + 2 ≤ 4) (Fin.cons 1 (Fin.cons 0 w)) ℓ
  have hsup := norm_sq_schwartz_le_Aop ψ z
  rw [e10, e1, e0] at hsup
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hℓ4 : 0 ≤ (1 + (ℓ : ℝ)) ^ 4 := by positivity
  have hsq : ‖ψ z‖ ^ 2 ≤ (204 * (1 + (ℓ : ℝ)) ^ 2) ^ 2 := by
    calc ‖ψ z‖ ^ 2 ≤ 4 * (2592 * Real.pi * (1 + (ℓ : ℝ)) ^ 4) := by linarith
      _ ≤ 4 * (2592 * 4 * (1 + (ℓ : ℝ)) ^ 4) := by nlinarith
      _ ≤ (204 * (1 + (ℓ : ℝ)) ^ 2) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (ψ z), (by positivity : (0 : ℝ) ≤ 204 * (1 + (ℓ : ℝ)) ^ 2)]

private theorem norm_gS_Aw_φS_le {k : ℕ} (hk : k ≤ 2) (w : Fin k → Fin 2) (ℓ : ℕ) (z : ℝ × ℝ) :
    ‖gS (Aw k w (φS ℓ)) z‖ ≤
      (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  rw [gS_apply, norm_mul, sqGc, Complex.norm_real, Real.norm_of_nonneg (sqG_pos z).le,
    sqG_eq, gaussS_apply]
  have hb := norm_Aw_φS_le hk w ℓ z
  have hc := B0093.sqrtConst_pos.le
  have he := (Real.exp_pos (-((z.1 ^ 2 + z.2 ^ 2) / 8))).le
  rw [show -((z.1 ^ 2 + z.2 ^ 2) / 8) = -(z.1 ^ 2 + z.2 ^ 2) / 8 by ring] at he ⊢
  calc B0093.sqrtConst * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) * ‖Aw k w (φS ℓ) z‖
      ≤ B0093.sqrtConst * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) * (204 * (1 + (ℓ : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hc he)
    _ = (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        ring

private theorem vec_decomp_ev (v : ℝ × ℝ) : v = v.1 • ev 0 + v.2 • ev 1 := by
  ext <;> simp [ev, e1, e2]

private theorem abs_coord_le_norm (v : ℝ × ℝ) : |v.1| ≤ ‖v‖ ∧ |v.2| ≤ ‖v‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

private theorem norm_fderiv_schwartz_le (ψ : S2) (z : ℝ × ℝ) :
    ‖fderiv ℝ (⇑ψ) z‖ ≤ ‖dop 0 ψ z‖ + ‖dop 1 ψ z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  conv_lhs => rw [vec_decomp_ev v]
  rw [map_add, map_smul, map_smul]
  obtain ⟨h1, h2⟩ := abs_coord_le_norm v
  calc ‖v.1 • fderiv ℝ (⇑ψ) z (ev 0) + v.2 • fderiv ℝ (⇑ψ) z (ev 1)‖
      ≤ ‖v.1 • fderiv ℝ (⇑ψ) z (ev 0)‖ + ‖v.2 • fderiv ℝ (⇑ψ) z (ev 1)‖ := norm_add_le _ _
    _ = |v.1| * ‖dop 0 ψ z‖ + |v.2| * ‖dop 1 ψ z‖ := by
        simp [Real.norm_eq_abs, dop_apply]
    _ ≤ ‖v‖ * ‖dop 0 ψ z‖ + ‖v‖ * ‖dop 1 ψ z‖ := by gcongr
    _ = (‖dop 0 ψ z‖ + ‖dop 1 ψ z‖) * ‖v‖ := by ring

private theorem norm_iteratedFDeriv_two_schwartz_le (ψ : S2) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ 2 (⇑ψ) z‖ ≤
      ‖dop 0 (dop 0 ψ) z‖ + ‖dop 0 (dop 1 ψ) z‖ +
        ‖dop 1 (dop 0 ψ) z‖ + ‖dop 1 (dop 1 ψ) z‖ := by
  have hsm : ContDiff ℝ ∞ (⇑ψ) := ψ.smooth ⊤
  have hdf : ContDiff ℝ (2 : ℕ∞) (fderiv ℝ (⇑ψ)) := hsm.fderiv_right (by simp)
  refine (iteratedFDeriv ℝ 2 (⇑ψ) z).opNorm_le_bound (by positivity) fun m => ?_
  rw [iteratedFDeriv_two_apply, Fin.prod_univ_two]
  have hu_ev : ∀ j : Fin 2, ‖fderiv ℝ (fderiv ℝ (⇑ψ)) z (m 0) (ev j)‖ ≤
      (‖dop 0 (dop j ψ) z‖ + ‖dop 1 (dop j ψ) z‖) * ‖m 0‖ := fun j => by
    set L : (ℝ × ℝ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (ev j)
    have hcomp := (L.hasFDerivAt.comp z ((hdf.differentiable (by norm_num)) z).hasFDerivAt).fderiv
    have hev : fderiv ℝ (⇑(dop j ψ)) z (m 0) = fderiv ℝ (fderiv ℝ (⇑ψ)) z (m 0) (ev j) :=
      congrArg (fun T => T (m 0)) hcomp
    rw [← hev]
    exact ((fderiv ℝ (⇑(dop j ψ)) z).le_opNorm (m 0)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_schwartz_le (dop j ψ) z) (norm_nonneg (m 0)))
  conv_lhs => rw [vec_decomp_ev (m 1)]
  rw [map_add, map_smul, map_smul]
  obtain ⟨hv1, hv2⟩ := abs_coord_le_norm (m 1)
  calc ‖(m 1).1 • fderiv ℝ (fderiv ℝ (⇑ψ)) z (m 0) (ev 0) +
          (m 1).2 • fderiv ℝ (fderiv ℝ (⇑ψ)) z (m 0) (ev 1)‖
      ≤ |(m 1).1| * ‖fderiv ℝ (fderiv ℝ (⇑ψ)) z (m 0) (ev 0)‖ +
          |(m 1).2| * ‖fderiv ℝ (fderiv ℝ (⇑ψ)) z (m 0) (ev 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        simp [Real.norm_eq_abs]
    _ ≤ ‖m 1‖ * ((‖dop 0 (dop 0 ψ) z‖ + ‖dop 1 (dop 0 ψ) z‖) * ‖m 0‖) +
          ‖m 1‖ * ((‖dop 0 (dop 1 ψ) z‖ + ‖dop 1 (dop 1 ψ) z‖) * ‖m 0‖) :=
        add_le_add (mul_le_mul hv1 (hu_ev 0) (norm_nonneg _) (norm_nonneg (m 1)))
          (mul_le_mul hv2 (hu_ev 1) (norm_nonneg _) (norm_nonneg (m 1)))
    _ = (‖dop 0 (dop 0 ψ) z‖ + ‖dop 0 (dop 1 ψ) z‖ +
          ‖dop 1 (dop 0 ψ) z‖ + ‖dop 1 (dop 1 ψ) z‖) * (‖m 0‖ * ‖m 1‖) := by ring

private def lvlJetConst : ℝ := 816 * B0093.sqrtConst

private theorem lvlJetConst_pos : 0 < lvlJetConst := by
  unfold lvlJetConst; have := B0093.sqrtConst_pos; positivity

private theorem norm_iteratedFDeriv_gS_φS_le {m : ℕ} (hm : m ≤ 2) (ℓ : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ m (⇑(gS (φS ℓ))) z‖ ≤
      lvlJetConst * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  have hc0 : 0 ≤ (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 *
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    have := B0093.sqrtConst_pos.le; positivity
  interval_cases m
  · rw [norm_iteratedFDeriv_zero]
    have h0 : φS ℓ = Aw 0 ![] (φS ℓ) := rfl
    have hb := norm_gS_Aw_φS_le (by norm_num : 0 ≤ 2) ![] ℓ z
    rw [← h0] at hb
    unfold lvlJetConst
    linarith
  · rw [norm_iteratedFDeriv_one]
    have hstep := norm_fderiv_schwartz_le (gS (φS ℓ)) z
    have hd : ∀ i : Fin 2, ‖dop i (gS (φS ℓ)) z‖ ≤
        (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
      intro i
      have heq : dop i (gS (φS ℓ)) = gS (Aw 1 ![i] (φS ℓ)) := by
        rw [dop_gS]; rfl
      rw [heq]
      exact norm_gS_Aw_φS_le (by norm_num : 1 ≤ 2) ![i] ℓ z
    have b0 := hd 0
    have b1 := hd 1
    unfold lvlJetConst
    linarith
  · have hstep := norm_iteratedFDeriv_two_schwartz_le (gS (φS ℓ)) z
    have hd2 : ∀ i j : Fin 2, ‖dop i (dop j (gS (φS ℓ))) z‖ ≤
        (204 * B0093.sqrtConst) * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
      intro i j
      have heq : dop i (dop j (gS (φS ℓ))) = gS (Aw 2 ![i, j] (φS ℓ)) := by
        rw [dop_gS, dop_gS]; rfl
      rw [heq]
      exact norm_gS_Aw_φS_le le_rfl ![i, j] ℓ z
    have b00 := hd2 0 0
    have b01 := hd2 0 1
    have b10 := hd2 1 0
    have b11 := hd2 1 1
    unfold lvlJetConst
    linarith

private theorem summable_inv_one_add_pow_four :
    Summable (fun ℓ : ℕ => ((1 + (ℓ : ℝ)) ^ 2)⁻¹ ^ 2) := by
  have hs : Summable (fun ℓ : ℕ => (((ℓ + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hs
  have h1 : (1 : ℝ) ≤ 1 + (ℓ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hpos : (0 : ℝ) < (1 + (ℓ : ℝ)) ^ 2 := by positivity
  have hcast : ((ℓ + 1 : ℕ) : ℝ) = 1 + (ℓ : ℝ) := by push_cast; ring
  rw [hcast, inv_pow, ← pow_mul]
  exact inv_anti₀ hpos (pow_le_pow_right₀ h1 (by norm_num : 2 ≤ 2 * 2))

private def sumInvFour : ℝ := ∑' ℓ : ℕ, ((1 + (ℓ : ℝ)) ^ 2)⁻¹ ^ 2

private theorem sumInvFour_pos : 0 < sumInvFour := by
  unfold sumInvFour
  exact summable_inv_one_add_pow_four.tsum_pos (fun _ => by positivity) 0 (by norm_num)

private theorem coef_weighted_summable_and_le (u : XG) (hu : u ∈ (fracPow 8).domain) :
    Summable (fun ℓ : ℕ => ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ∧
      (∑' ℓ : ℕ, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ≤
        Real.sqrt sumInvFour * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) := by
  set G₈ := Real.sqrt (graphNormSq 8 ⟨u, hu⟩)
  have hG_nn : 0 ≤ graphNormSq 8 ⟨u, hu⟩ := by unfold graphNormSq; positivity
  have hG_sq : G₈ ^ 2 = ∑' ℓ : ℕ, (1 + (1 + (ℓ : ℝ)) ^ 8) * ‖⟪oscBasis ℓ, u⟫_ℂ‖ ^ 2 := by
    rw [Real.sq_sqrt hG_nn, graphNormSq_eq 8 ⟨u, hu⟩]
  have hsum8 : Summable (fun ℓ : ℕ => (1 + (1 + (ℓ : ℝ)) ^ 8) * ‖⟪oscBasis ℓ, u⟫_ℂ‖ ^ 2) :=
    (summable_coef_sq u).add ((mem_XGj_iff 8 u).1 hu) |>.congr fun ℓ => by ring
  have hN : ∀ N : ℕ, ∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2 ≤
      Real.sqrt sumInvFour * G₈ := by
    intro N
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun ℓ => ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 4)
      (fun ℓ => ((1 + (ℓ : ℝ)) ^ 2)⁻¹)
    have hrew : ∑ ℓ ∈ Finset.range N,
        (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 4) * ((1 + (ℓ : ℝ)) ^ 2)⁻¹ =
        ∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have hpos : (1 + (ℓ : ℝ)) ≠ 0 := by positivity
      field_simp
    rw [hrew] at hcs
    have hA : ∑ ℓ ∈ Finset.range N, (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 4) ^ 2 ≤ G₈ ^ 2 := by
      rw [hG_sq]
      refine (Finset.sum_le_sum fun ℓ _ => ?_).trans
        (hsum8.sum_le_tsum (Finset.range N) fun _ _ => by positivity)
      nlinarith [sq_nonneg ‖⟪oscBasis ℓ, u⟫_ℂ‖]
    have hB : ∑ ℓ ∈ Finset.range N, (((1 + (ℓ : ℝ)) ^ 2)⁻¹) ^ 2 ≤ sumInvFour :=
      summable_inv_one_add_pow_four.sum_le_tsum (Finset.range N) fun _ _ => by positivity
    have hsq : (∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ^ 2 ≤
        (Real.sqrt sumInvFour * G₈) ^ 2 := by
      calc (∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) ^ 2
          ≤ G₈ ^ 2 * sumInvFour := hcs.trans (mul_le_mul hA hB
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg G₈))
        _ = (Real.sqrt sumInvFour * G₈) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt sumInvFour_pos.le, mul_comm]
    have hS_nn : 0 ≤ ∑ ℓ ∈ Finset.range N, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hR_nn : 0 ≤ Real.sqrt sumInvFour * G₈ := by positivity
    nlinarith
  have hs := summable_of_sum_range_le (fun _ => by positivity) hN
  exact ⟨hs, hs.tsum_le_of_sum_range_le hN⟩

private def synthPlanar (u : XG) (z : ℝ × ℝ) : ℂ :=
  ∑' ℓ : ℕ, ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z

private def synthSchwartzSum (u : XG) (z : ℝ × ℝ) : ℂ :=
  ∑' ℓ : ℕ, ⟪oscBasis ℓ, u⟫_ℂ * φS ℓ z

private def jetSynthConst : ℝ := lvlJetConst * Real.sqrt sumInvFour

private theorem jetSynthConst_pos : 0 < jetSynthConst := by
  unfold jetSynthConst
  exact mul_pos lvlJetConst_pos (Real.sqrt_pos.2 sumInvFour_pos)

private theorem contDiff_and_jet_synthPlanar (u : XG) (hu : u ∈ (fracPow 8).domain) :
    ContDiff ℝ 2 (synthPlanar u) ∧
      ∀ {m : ℕ}, m ≤ 2 → ∀ z : ℝ × ℝ,
        ‖iteratedFDeriv ℝ m (synthPlanar u) z‖ ≤
          jetSynthConst * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  obtain ⟨hsum_w, hle_w⟩ := coef_weighted_summable_and_le u hu
  set g : ℕ → ℝ × ℝ → ℂ := fun ℓ z => ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z
  set v : ℕ → ℕ → ℝ := fun _ ℓ => lvlJetConst * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2)
  have hg_sm : ∀ ℓ : ℕ, ContDiff ℝ (2 : ℕ∞) (g ℓ) := fun ℓ =>
    contDiff_const.mul ((gS (φS ℓ)).smooth 2)
  have hv_sum : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → Summable (v k) := fun _ _ =>
    hsum_w.mul_left lvlJetConst
  have hterm_gauss : ∀ (k : ℕ), k ≤ 2 → ∀ (ℓ : ℕ) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ k (g ℓ) z‖ ≤
        v k ℓ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro k hk ℓ z
    have heq : g ℓ = (ContinuousLinearMap.lsmul ℝ ℂ ⟪oscBasis ℓ, u⟫_ℂ) ∘ ⇑(gS (φS ℓ)) := rfl
    rw [heq, ContinuousLinearMap.iteratedFDeriv_comp_left _ ((gS (φS ℓ)).smooth ⊤).contDiffAt
      (by exact_mod_cast le_top)]
    have hclm : ‖(ContinuousLinearMap.lsmul ℝ ℂ ⟪oscBasis ℓ, u⟫_ℂ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z)‖ ≤
        ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z‖ := by
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
      simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul]
      calc ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z m‖
          ≤ ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (‖iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z‖ * ∏ i, ‖m i‖) :=
            mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z).le_opNorm m)
              (norm_nonneg _)
        _ = ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z‖ * ∏ i, ‖m i‖ := by ring
    refine hclm.trans ?_
    calc ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖iteratedFDeriv ℝ k (⇑(gS (φS ℓ))) z‖
        ≤ ‖⟪oscBasis ℓ, u⟫_ℂ‖ *
            (lvlJetConst * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_gS_φS_le hk ℓ z) (norm_nonneg _)
      _ = v k ℓ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by dsimp [v]; ring
  have h'f : ∀ (k : ℕ) (ℓ : ℕ) (z : ℝ × ℝ), (k : ℕ∞) ≤ 2 →
      ‖iteratedFDeriv ℝ k (g ℓ) z‖ ≤ v k ℓ := by
    intro k ℓ z hk
    have hk' : k ≤ 2 := by exact_mod_cast hk
    have hexp1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
    have hv_nn : 0 ≤ v k ℓ := mul_nonneg lvlJetConst_pos.le (by positivity)
    exact (hterm_gauss k hk' ℓ z).trans (mul_le_of_le_one_right hv_nn hexp1)
  refine ⟨contDiff_tsum hg_sm hv_sum h'f, fun {m} hm z => ?_⟩
  have hm' : (m : ℕ∞) ≤ 2 := by exact_mod_cast hm
  change ‖iteratedFDeriv ℝ m (fun y => ∑' ℓ, g ℓ y) z‖ ≤ _
  rw [iteratedFDeriv_tsum_apply hg_sm hv_sum h'f hm' z]
  have hsum_norm : Summable (fun ℓ : ℕ => ‖iteratedFDeriv ℝ m (g ℓ) z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => h'f m ℓ z hm') (hv_sum m hm')
  have hsum_rhs : Summable (fun ℓ : ℕ => v m ℓ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
    (hv_sum m hm').mul_right _
  calc ‖∑' ℓ : ℕ, iteratedFDeriv ℝ m (g ℓ) z‖
      ≤ ∑' ℓ : ℕ, ‖iteratedFDeriv ℝ m (g ℓ) z‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' ℓ : ℕ, v m ℓ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
        hsum_norm.tsum_le_tsum (fun ℓ => hterm_gauss m hm ℓ z) hsum_rhs
    _ = lvlJetConst * (∑' ℓ : ℕ, ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        dsimp only [v]
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ jetSynthConst * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        unfold jetSynthConst
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hle_w lvlJetConst_pos.le

/-! ### 3. Pointwise identification `planarMode f = synthPlanar u` and `L¹` moment bound -/

private theorem gS_φS_eq_angF (ℓ : ℕ) (z : ℝ × ℝ) :
    gS (φS ℓ) z = angF (qp (lev ℓ)) z := by
  rw [gS_apply, φS, coe_coreS, sqGc_mul_conjG, angularTwoField_profFun]

private theorem gS_φS_zero (ℓ : ℕ) : gS (φS ℓ) (0, 0) = 0 := by
  rw [gS_φS_eq_angF]
  simp [angF, wz]

private theorem gS_φS_eq_axis_mul_angTwo (ℓ : ℕ) {z : ℝ × ℝ} (hz : z ≠ (0, 0)) :
    gS (φS ℓ) z = gS (φS ℓ) (Real.sqrt (z.1 ^ 2 + z.2 ^ 2), 0) * angTwo z := by
  have hs_pos : 0 < z.1 ^ 2 + z.2 ^ 2 := by
    by_contra hle
    have h1 : z.1 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    have h2 : z.2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    exact hz (Prod.ext h1 h2)
  have hsq : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 = z.1 ^ 2 + z.2 ^ 2 := Real.sq_sqrt hs_pos.le
  rw [gS_φS_eq_angF, gS_φS_eq_angF]
  unfold angF angTwo wz sz
  simp only [ zero_pow (by norm_num : 2 ≠ 0), add_zero, Complex.ofReal_zero, zero_mul]
  rw [← Complex.ofReal_pow, hsq]
  have hne : ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs_pos.ne'
  field_simp [hne]

private theorem oscBasis_ae_eq_gS_axis (ℓ : ℕ) :
    (oscBasis ℓ : ℝ → ℂ) =ᵐ[xGMeasure] fun r : ℝ => gS (φS ℓ) (r, 0) := by
  have h1 : (oscBasis ℓ : ℝ → ℂ) =ᵐ[xGMeasure] schProf (φS ℓ) := by
    rw [← toXG_φS ℓ, toXG]
    exact (memLp_schProf (φS ℓ)).coeFn_toLp
  filter_upwards [h1, UnforcedLeray.B0012.ae_xG_pos] with r hr1 hr_pos
  rw [hr1]
  have h2 := congrFun (angularTwoField_schProf_eq_gS (isAngularTwo_φS ℓ)) (r, 0)
  rw [← h2]
  unfold angularTwoField
  simp only [polarCoord_apply, zero_pow (by norm_num : 2 ≠ 0), add_zero,
    Real.sqrt_sq hr_pos.le]
  have harg : Complex.arg (Complex.equivRealProd.symm (r, 0)) = 0 := by
    have heq : Complex.equivRealProd.symm (r, 0) = (r : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq]
    exact Complex.arg_ofReal_of_nonneg hr_pos.le
  rw [harg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

private theorem planarMode_eq_synthPlanar {f : UnforcedLeray.Blueprint.Planar.Profile}
    (hfc : ContDiffOn ℝ ∞ f (Ioi 0)) {u : XG}
    (hfu : f =ᵐ[xGMeasure] (u : ℝ → ℂ)) (hu : u ∈ (fracPow 8).domain) :
    planarMode f = synthPlanar u := by
  obtain ⟨hsm, _⟩ := contDiff_and_jet_synthPlanar u hu
  obtain ⟨hsum_w, _⟩ := coef_weighted_summable_and_le u hu
  have hsum_pt : ∀ z : ℝ × ℝ, Summable (fun ℓ : ℕ => ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) z) := by
    intro z
    refine Summable.of_norm_bounded (hsum_w.mul_left lvlJetConst) fun ℓ => ?_
    rw [norm_mul]
    have hb := norm_iteratedFDeriv_gS_φS_le (by norm_num : 0 ≤ 2) ℓ z
    rw [norm_iteratedFDeriv_zero] at hb
    have hexp1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
    calc ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖gS (φS ℓ) z‖
        ≤ ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (lvlJetConst * (1 + (ℓ : ℝ)) ^ 2) := by
          gcongr
          refine hb.trans (mul_le_of_le_one_right ?_ hexp1)
          exact mul_nonneg lvlJetConst_pos.le (by positivity)
      _ = lvlJetConst * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) := by ring
  have hS : HasSum (fun ℓ : ℕ => ⟪oscBasis ℓ, u⟫_ℂ • oscBasis ℓ) u := by
    simpa only [HilbertBasis.repr_apply_apply] using oscBasis.hasSum_repr u
  have hcoe : ∀ N : ℕ,
      (⇑(∑ ℓ ∈ Finset.range N, ⟪oscBasis ℓ, u⟫_ℂ • oscBasis ℓ) : ℝ → ℂ) =ᵐ[xGMeasure]
        fun r : ℝ => ∑ ℓ ∈ Finset.range N, ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) (r, 0) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 xGMeasure
    | succ N ih =>
      filter_upwards [ih,
        Lp.coeFn_add (∑ ℓ ∈ Finset.range N, ⟪oscBasis ℓ, u⟫_ℂ • oscBasis ℓ)
          (⟪oscBasis N, u⟫_ℂ • oscBasis N),
        Lp.coeFn_smul ⟪oscBasis N, u⟫_ℂ (oscBasis N),
        oscBasis_ae_eq_gS_axis N] with r h1 h2 h3 h4
      simp only [Finset.sum_range_succ]
      rw [h2, Pi.add_apply, h1, h3, Pi.smul_apply, smul_eq_mul, h4]
  obtain ⟨ns, hns, hae_sub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hS.tendsto_sum_nat).exists_seq_tendsto_ae
  have hae_u : (u : ℝ → ℂ) =ᵐ[xGMeasure] fun r : ℝ => synthPlanar u (r, 0) := by
    filter_upwards [hae_sub, ae_all_iff.2 hcoe] with r hr1 hr2
    have hlim : Tendsto (fun i : ℕ =>
        ∑ ℓ ∈ Finset.range (ns i), ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) (r, 0))
        atTop (𝓝 ((u : ℝ → ℂ) r)) :=
      Tendsto.congr (fun i => hr2 (ns i)) hr1
    have hser : Tendsto (fun i : ℕ =>
        ∑ ℓ ∈ Finset.range (ns i), ⟪oscBasis ℓ, u⟫_ℂ * gS (φS ℓ) (r, 0))
        atTop (𝓝 (synthPlanar u (r, 0))) :=
      (hsum_pt (r, 0)).hasSum.tendsto_sum_nat.comp hns.tendsto_atTop
    exact tendsto_nhds_unique hlim hser
  have hae_vol : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r : ℝ => synthPlanar u (r, 0) :=
    UnforcedLeray.B0012.restrict_ac.ae_le (hfu.trans hae_u)
  have hcont_axis : ContinuousOn (fun r : ℝ => synthPlanar u (r, 0)) (Ioi 0) :=
    (hsm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  have heq_on : EqOn f (fun r : ℝ => synthPlanar u (r, 0)) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae_vol isOpen_Ioi hfc.continuousOn hcont_axis
  funext z
  by_cases hz : z = (0, 0)
  · subst hz
    simp [planarMode, angTwo, synthPlanar, gS_φS_zero]
  · have hs_pos : 0 < z.1 ^ 2 + z.2 ^ 2 := by
      by_contra hle
      exact hz (Prod.ext (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
        (by nlinarith [sq_nonneg z.1, sq_nonneg z.2]))
    have hr_pos : 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := Real.sqrt_pos.2 hs_pos
    unfold planarMode
    rw [heq_on hr_pos]
    unfold synthPlanar
    rw [← tsum_mul_right]
    congr 1
    funext ℓ
    rw [mul_assoc, ← gS_φS_eq_axis_mul_angTwo ℓ hz]

private theorem synthPlanar_eq_sqGc_mul (u : XG) (hu : u ∈ (fracPow 8).domain) (z : ℝ × ℝ) :
    synthPlanar u z = sqGc z * synthSchwartzSum u z := by
  obtain ⟨hsum_w, _⟩ := coef_weighted_summable_and_le u hu
  have hs : Summable (fun ℓ : ℕ => ⟪oscBasis ℓ, u⟫_ℂ * φS ℓ z) := by
    refine Summable.of_norm_bounded (hsum_w.mul_left 204) fun ℓ => ?_
    rw [norm_mul]
    have hb := norm_Aw_φS_le (by norm_num : 0 ≤ 2) ![] ℓ z
    simp only [Aw_zero] at hb
    calc ‖⟪oscBasis ℓ, u⟫_ℂ‖ * ‖φS ℓ z‖
        ≤ ‖⟪oscBasis ℓ, u⟫_ℂ‖ * (204 * (1 + (ℓ : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = 204 * (‖⟪oscBasis ℓ, u⟫_ℂ‖ * (1 + (ℓ : ℝ)) ^ 2) := by ring
  unfold synthPlanar synthSchwartzSum
  rw [← tsum_mul_left]
  congr 1
  funext ℓ
  rw [gS_apply]
  ring

private theorem integrable_and_integral_synthSchwartzSum_sq
    (u : XG) (hu : u ∈ (fracPow 8).domain) :
    Integrable (fun z : ℝ × ℝ => ‖synthSchwartzSum u z‖ ^ 2) ∧
      (∫ z : ℝ × ℝ, ‖synthSchwartzSum u z‖ ^ 2) ≤ 2 * Real.pi * ‖u‖ ^ 2 := by
  obtain ⟨hsm_F, _⟩ := contDiff_and_jet_synthPlanar u hu
  obtain ⟨hsum_w, _⟩ := coef_weighted_summable_and_le u hu
  have hcont_Ψ : Continuous (synthSchwartzSum u) := by
    have heq : synthSchwartzSum u = fun z => (((sqG z)⁻¹ : ℝ) : ℂ) * synthPlanar u z := by
      funext z
      rw [synthPlanar_eq_sqGc_mul u hu z, sqGc, ← mul_assoc, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (sqG_pos z).ne', Complex.ofReal_one, one_mul]
    rw [heq]
    exact (Complex.continuous_ofReal.comp
      (contDiff_sqG.continuous.inv₀ fun z => (sqG_pos z).ne')).mul hsm_F.continuous
  set c : ℕ → ℂ := fun ℓ => ⟪oscBasis ℓ, u⟫_ℂ
  set ΨN : ℕ → S2 := fun N => chi (Finset.range N) c
  have hlim_pt : ∀ z : ℝ × ℝ,
      Tendsto (fun N : ℕ => (‖ΨN N z‖ₑ ^ 2 : ℝ≥0∞)) atTop (𝓝 (‖synthSchwartzSum u z‖ₑ ^ 2)) := by
    intro z
    have hs : Summable (fun ℓ : ℕ => c ℓ * φS ℓ z) := by
      refine Summable.of_norm_bounded (hsum_w.mul_left 204) fun ℓ => ?_
      rw [norm_mul]
      have hb := norm_Aw_φS_le (by norm_num : 0 ≤ 2) ![] ℓ z
      simp only [Aw_zero] at hb
      nlinarith [norm_nonneg (c ℓ)]
    have heq_N : ∀ N : ℕ, ΨN N z = ∑ ℓ ∈ Finset.range N, c ℓ * φS ℓ z := by
      intro N
      simp only [ΨN, chi, sum_apply, smul_apply, smul_eq_mul]
    have ht : Tendsto (fun N : ℕ => ΨN N z) atTop (𝓝 (synthSchwartzSum u z)) := by
      simp_rw [heq_N]
      exact hs.hasSum.tendsto_sum_nat
    exact (ENNReal.continuous_pow 2).continuousAt.tendsto.comp (continuous_enorm.tendsto _ |>.comp ht)
  have hfatou : (∫⁻ z : ℝ × ℝ, ‖synthSchwartzSum u z‖ₑ ^ 2) ≤
      liminf (fun N : ℕ => ∫⁻ z : ℝ × ℝ, ‖ΨN N z‖ₑ ^ 2) atTop := by
    calc ∫⁻ z : ℝ × ℝ, ‖synthSchwartzSum u z‖ₑ ^ 2
        = ∫⁻ z : ℝ × ℝ, liminf (fun N : ℕ => ‖ΨN N z‖ₑ ^ 2) atTop := by
          congr 1; funext z; exact (hlim_pt z).liminf_eq.symm
      _ ≤ liminf (fun N : ℕ => ∫⁻ z : ℝ × ℝ, ‖ΨN N z‖ₑ ^ 2) atTop :=
          lintegral_liminf_le fun N =>
            ((ENNReal.continuous_pow 2).comp (ΨN N).continuous.enorm).measurable
  have hN_le : ∀ N : ℕ, (∫⁻ z : ℝ × ℝ, ‖ΨN N z‖ₑ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi * ‖u‖ ^ 2) := by
    intro N
    have hi : Integrable (fun z : ℝ × ℝ => ‖ΨN N z‖ ^ 2) := by
      refine Integrable.mono' (integrable_conj_mul (ΨN N) (ΨN N)).norm
        (continuous_norm.comp (ΨN N).continuous |>.pow 2).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_conj, sq]
    have heq_lint : (∫⁻ z : ℝ × ℝ, ‖ΨN N z‖ₑ ^ 2) = ENNReal.ofReal (‖J (ΨN N)‖ ^ 2) := by
      rw [norm_J_sq_eq_integral, ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun _ => sq_nonneg _)]
      congr 1; funext z
      rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [heq_lint]
    refine ENNReal.ofReal_le_ofReal ?_
    have hchi0 := sum_norm_sq_Aw_chi 0 (Finset.range N) c
    simp only [Fintype.sum_unique, Aw_zero, qpoly, Finset.range_zero, Finset.prod_empty,
      one_mul] at hchi0
    change ‖J (ΨN N)‖ ^ 2 ≤ _
    rw [hchi0, norm_sq_eq_tsum u]
    exact mul_le_mul_of_nonneg_left
      ((summable_coef_sq u).sum_le_tsum (Finset.range N) fun _ _ => sq_nonneg _)
      (by positivity)
  have hliminf_le : liminf (fun N : ℕ => ∫⁻ z : ℝ × ℝ, ‖ΨN N z‖ₑ ^ 2) atTop ≤
      ENNReal.ofReal (2 * Real.pi * ‖u‖ ^ 2) :=
    liminf_le_of_frequently_le' (Frequently.of_forall hN_le)
  have htot := hfatou.trans hliminf_le
  have hmeas_sq : AEStronglyMeasurable (fun z : ℝ × ℝ => ‖synthSchwartzSum u z‖ ^ 2) volume :=
    ((continuous_norm.comp hcont_Ψ).pow 2).aestronglyMeasurable
  have hfin : HasFiniteIntegral (fun z : ℝ × ℝ => ‖synthSchwartzSum u z‖ ^ 2) volume := by
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (fun z : ℝ × ℝ => ‖‖synthSchwartzSum u z‖ ^ 2‖ₑ) =
        fun z => ‖synthSchwartzSum u z‖ₑ ^ 2 := by
      funext z
      rw [Real.enorm_of_nonneg (sq_nonneg _), ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [heq]
    exact lt_of_le_of_lt htot ENNReal.ofReal_lt_top
  have hint : Integrable (fun z : ℝ × ℝ => ‖synthSchwartzSum u z‖ ^ 2) := ⟨hmeas_sq, hfin⟩
  refine ⟨hint, ?_⟩
  have heq_int : ENNReal.ofReal (∫ z : ℝ × ℝ, ‖synthSchwartzSum u z‖ ^ 2) =
      ∫⁻ z : ℝ × ℝ, ‖synthSchwartzSum u z‖ₑ ^ 2 := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    congr 1; funext z
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← heq_int] at htot
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot

private theorem poly_three_exp_bound (z : ℝ × ℝ) :
    (1 + ‖planeToC z‖ ^ 3) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤
      1024 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
  set r := ‖planeToC z‖
  have hr : 0 ≤ r := norm_nonneg _
  have hsq : z.1 ^ 2 + z.2 ^ 2 = r ^ 2 := (OscillatorForceSub.norm_planeToC_sq z).symm
  rw [hsq]
  have hsplit : Real.exp (-r ^ 2 / 8) = Real.exp (-(r ^ 2 / 16)) * Real.exp (-r ^ 2 / 16) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hcubic : 1 + r ^ 3 ≤ 2 * (1 + r ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (r - 1), sq_nonneg (r ^ 2 - r)]
  have hexp_ge : 1 + (r ^ 2 / 16) + (r ^ 2 / 16) ^ 2 / 2 ≤ Real.exp (r ^ 2 / 16) := by
    have := Real.sum_le_exp_of_nonneg (x := r ^ 2 / 16) (by positivity) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat] at this
    exact this
  have hpoly : 1 + r ^ 3 ≤ 1024 * Real.exp (r ^ 2 / 16) := by
    have : 2 * (1 + r ^ 2) ^ 2 ≤ 1024 * (1 + (r ^ 2 / 16) + (r ^ 2 / 16) ^ 2 / 2) := by
      nlinarith [sq_nonneg r]
    linarith
  have hinv : Real.exp (r ^ 2 / 16) * Real.exp (-(r ^ 2 / 16)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE1 : 0 ≤ Real.exp (-(r ^ 2 / 16)) := (Real.exp_pos _).le
  have hE2 : 0 ≤ Real.exp (-r ^ 2 / 16) := (Real.exp_pos _).le
  calc (1 + r ^ 3) * (Real.exp (-(r ^ 2 / 16)) * Real.exp (-r ^ 2 / 16))
      = ((1 + r ^ 3) * Real.exp (-(r ^ 2 / 16))) * Real.exp (-r ^ 2 / 16) := by ring
    _ ≤ (1024 * Real.exp (r ^ 2 / 16) * Real.exp (-(r ^ 2 / 16))) * Real.exp (-r ^ 2 / 16) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly hE1) hE2
    _ = 1024 * Real.exp (-r ^ 2 / 16) := by rw [mul_assoc 1024, hinv, mul_one]

private theorem moment_three_synthPlanar_le :
    ∃ C_mom : ℝ, 0 < C_mom ∧
      ∀ (u : XG) (hu : u ∈ (fracPow 8).domain),
        Integrable (fun z : ℝ × ℝ => (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖) ∧
        (∫ z : ℝ × ℝ, (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖) ≤ C_mom * ‖u‖ := by
  set w : ℝ × ℝ → ℝ := fun z => (1 + ‖planeToC z‖ ^ 3) * sqG z
  have hw_cont : Continuous w :=
    (continuous_const.add ((continuous_norm.comp EulerErrorTail.continuous_planeToC).pow 3)).mul
      contDiff_sqG.continuous
  have hw_nn : ∀ z, 0 ≤ w z := fun z => by
    dsimp [w]; exact mul_nonneg (by positivity) (sqG_pos z).le
  have hw_bd : ∀ z : ℝ × ℝ,
      w z ≤ (1024 * B0093.sqrtConst) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
    intro z
    dsimp [w]
    rw [sqG_eq, gaussS_apply, show -((z.1 ^ 2 + z.2 ^ 2) / 8) = -(z.1 ^ 2 + z.2 ^ 2) / 8 by ring]
    calc (1 + ‖planeToC z‖ ^ 3) * (B0093.sqrtConst * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
        = B0093.sqrtConst * ((1 + ‖planeToC z‖ ^ 3) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) := by
          ring
      _ ≤ B0093.sqrtConst * (1024 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) :=
          mul_le_mul_of_nonneg_left (poly_three_exp_bound z) B0093.sqrtConst_pos.le
      _ = (1024 * B0093.sqrtConst) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by ring
  have hw_sq_int : Integrable (fun z : ℝ × ℝ => w z ^ 2) := by
    refine Integrable.mono'
      ((EulerErrorTail.integrable_gauss (a := 8) (by norm_num)).const_mul
        ((1024 * B0093.sqrtConst) ^ 2))
      (hw_cont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb := pow_le_pow_left₀ (hw_nn z) (hw_bd z) 2
    refine hb.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  set Iw : ℝ := ∫ z : ℝ × ℝ, w z ^ 2
  have hIw_nn : 0 ≤ Iw := integral_nonneg fun _ => sq_nonneg _
  refine ⟨Iw / 2 + Real.pi + 1, by have := Real.pi_pos; positivity, fun u hu => ?_⟩
  obtain ⟨hsm_F, _⟩ := contDiff_and_jet_synthPlanar u hu
  obtain ⟨hΨ_int, hΨ_le⟩ := integrable_and_integral_synthSchwartzSum_sq u hu
  have hpt_eq : ∀ z : ℝ × ℝ, (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖ =
      w z * ‖synthSchwartzSum u z‖ := by
    intro z
    rw [synthPlanar_eq_sqGc_mul u hu z, norm_mul, sqGc, Complex.norm_real,
      Real.norm_of_nonneg (sqG_pos z).le]
    dsimp [w]; ring
  by_cases hu0 : ‖u‖ = 0
  · have hu_zero : u = 0 := norm_eq_zero.mp hu0
    subst hu_zero
    have hF0 : ∀ z, synthPlanar 0 z = 0 := fun z => by simp [synthPlanar]
    simp [hF0]
  · set R := ‖u‖
    have hR : 0 < R := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
    have hdom_int : Integrable (fun z : ℝ × ℝ =>
        (R / 2) * w z ^ 2 + (1 / (2 * R)) * ‖synthSchwartzSum u z‖ ^ 2) :=
      (hw_sq_int.const_mul (R / 2)).add (hΨ_int.const_mul (1 / (2 * R)))
    have hpt_le : ∀ z : ℝ × ℝ, (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖ ≤
        (R / 2) * w z ^ 2 + (1 / (2 * R)) * ‖synthSchwartzSum u z‖ ^ 2 := by
      intro z
      rw [hpt_eq z]
      have hsq : 2 * R * (w z * ‖synthSchwartzSum u z‖) ≤
          R ^ 2 * w z ^ 2 + ‖synthSchwartzSum u z‖ ^ 2 := by
        nlinarith [sq_nonneg (R * w z - ‖synthSchwartzSum u z‖)]
      rw [← le_div_iff₀' (by positivity : 0 < 2 * R)] at hsq
      refine hsq.trans (le_of_eq ?_)
      field_simp
    have hint : Integrable (fun z : ℝ × ℝ => (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖) := by
      refine Integrable.mono' hdom_int
        ((continuous_const.add
          ((continuous_norm.comp EulerErrorTail.continuous_planeToC).pow 3)).mul
          (continuous_norm.comp hsm_F.continuous)).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
      exact hpt_le z
    refine ⟨hint, ?_⟩
    calc (∫ z : ℝ × ℝ, (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖)
        ≤ ∫ z : ℝ × ℝ, ((R / 2) * w z ^ 2 + (1 / (2 * R)) * ‖synthSchwartzSum u z‖ ^ 2) :=
          integral_mono hint hdom_int hpt_le
      _ = (R / 2) * Iw + (1 / (2 * R)) * ∫ z : ℝ × ℝ, ‖synthSchwartzSum u z‖ ^ 2 := by
          rw [integral_add (hw_sq_int.const_mul _) (hΨ_int.const_mul _),
            integral_const_mul, integral_const_mul]
      _ ≤ (R / 2) * Iw + (1 / (2 * R)) * (2 * Real.pi * R ^ 2) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hΨ_le (by positivity))
      _ = (Iw / 2 + Real.pi) * R := by field_simp
      _ ≤ (Iw / 2 + Real.pi + 1) * R := by nlinarith

/-! ### 4. Exponential Gaussian lattice tails and periodic jet/velocity bounds -/

private theorem exp_lattice_tail_factor {d : ℝ} (hd : 1 ≤ d) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64)) ≤
      Real.exp (-(d ^ 2 / 128)) * (512 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) := by
  have hn1 := EulerErrorTail.one_le_abs_int hn
  have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hsplit_exp : -((n : ℝ) ^ 2 * d ^ 2 / 64) ≤ -(d ^ 2 / 128) + -((n : ℝ) ^ 2 / 128) := by
    nlinarith [mul_le_mul_of_nonneg_left hd2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
      mul_le_mul_of_nonneg_right hn2 (by positivity : (0 : ℝ) ≤ d ^ 2)]
  have h1 : Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64)) ≤
      Real.exp (-(d ^ 2 / 128)) * Real.exp (-((n : ℝ) ^ 2 / 128)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 hsplit_exp
  have h2 : Real.exp (-((n : ℝ) ^ 2 / 128)) ≤ 512 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    have hinv := EulerErrorTail.exp_neg_le_inv (x := (n : ℝ) ^ 2 / 128) (by positivity)
    have hrp : (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) = 1 / (1 + |(n : ℝ)|) ^ 2 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
    rw [hrp]
    have hsq : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
    refine hinv.trans ?_
    have h128 : 1 / ((n : ℝ) ^ 2 / 128) = 128 / (n : ℝ) ^ 2 := by field_simp
    rw [h128, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)

private theorem tail_gauss_exp {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {L : ℝ × ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {d : ℝ} (hd : 1 ≤ d) {y : ℝ × ℝ} (hy : |y.1| ≤ d / 2) :
    ‖(∑' n : ℤ, L (y.1 - n * d, y.2)) - L y‖ ≤
      (512 * EulerErrorTail.sZ) * C * Real.exp (-(d ^ 2 / 128)) *
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  have hd0 : 0 < d := by linarith
  have heq : (∑' n : ℤ, L (y.1 - n * d, y.2)) = ∑' n : ℤ, L (y.1 + n * d, y.2) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => L (y.1 + n * d, y.2))]
    congr 1; funext n
    simp only [Equiv.neg_apply, Int.cast_neg, neg_mul, ← sub_eq_add_neg]
  rw [heq]
  have hs : Summable (fun n : ℤ => L (y.1 + n * d, y.2)) := by
    refine Summable.of_norm_bounded ((UnforcedLeray.Gaussian.summable_translate (s := 2) (c := -d)
      (by norm_num) (neg_ne_zero.2 hd0.ne') y.1).mul_left (16 * C)) fun n => ?_
    calc ‖L (y.1 + n * d, y.2)‖
        ≤ C * Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) := hL (y.1 + n * d, y.2)
      _ ≤ C * (16 * (1 + |y.1 + n * d|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (perCont_exp_le_translate_weight (y.1 + n * d) y.2) hC
      _ = 16 * C * (1 + |y.1 - n * -d|) ^ (-(2 : ℝ)) := by
          rw [show y.1 - (n : ℝ) * -d = y.1 + n * d by ring]; ring
  set A : ℝ := 512 * C * Real.exp (-(d ^ 2 / 128)) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)
  have hA0 : 0 ≤ A := by positivity
  have h := EulerErrorTail.norm_tsum_sub_zero_le hs hA0 fun n hn => by
    have hsq := EulerErrorTail.shift_sq_ge hd0.le hy hn
    have hexp : Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) ≤
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) * Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg y.2]
    calc ‖L (y.1 + n * d, y.2)‖
        ≤ C * Real.exp (-((y.1 + n * d) ^ 2 + y.2 ^ 2) / 8) := hL (y.1 + n * d, y.2)
      _ ≤ C * (Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) *
            Real.exp (-((n : ℝ) ^ 2 * d ^ 2 / 64))) := mul_le_mul_of_nonneg_left hexp hC
      _ ≤ C * (Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) *
            (Real.exp (-(d ^ 2 / 128)) * (512 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (exp_lattice_tail_factor hd hn) (Real.exp_pos _).le) hC
      _ = A * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by dsimp [A]; ring
  simp only [Int.cast_zero, zero_mul, add_zero, Prod.mk.eta] at h
  calc ‖(∑' n : ℤ, L (y.1 + n * d, y.2)) - L y‖ ≤ A * EulerErrorTail.sZ := h
    _ = (512 * EulerErrorTail.sZ) * C * Real.exp (-(d ^ 2 / 128)) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by dsimp [A]; ring

private theorem exp8_le_translate_weight (z : ℝ × ℝ) :
    Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 16 * (1 + |z.1|) ^ (-(2 : ℝ)) :=
  perCont_exp_le_translate_weight z.1 z.2

private theorem contDiff_and_pdCx_periodizeC {e : ℝ × ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (he_sm : ContDiff ℝ 2 e)
    (he_jet : ∀ {m : ℕ}, m ≤ 2 → ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ m e z‖ ≤ M * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {d : ℝ} (hd : 1 ≤ d) :
    ContDiff ℝ 2 (periodizeC d e) ∧
      ∀ (k : Fin 2) (y : ℝ × ℝ), pdCx k (periodizeC d e) y = periodizeC d (pdCx k e) y := by
  have hd0 : d ≠ 0 := by linarith
  have hper_eq : periodizeC d e = UnforcedLeray.Gaussian.periodize d e := rfl
  have hD : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      ∃ C : ℝ, ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ k e z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k hk
    have hk' : k ≤ 2 := by exact_mod_cast hk
    refine ⟨16 * M, fun z => ?_⟩
    calc ‖iteratedFDeriv ℝ k e z‖
        ≤ M * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := he_jet hk' z
      _ ≤ M * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (exp8_le_translate_weight z) hM
      _ = (16 * M) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
  have hcd : ContDiff ℝ 2 (periodizeC d e) := by
    rw [hper_eq]
    exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (N := (2 : ℕ∞))
      one_lt_two hd0 he_sm hD
  refine ⟨hcd, fun k y => ?_⟩
  obtain ⟨C₀, hC₀⟩ := hD 0 (by norm_num)
  obtain ⟨C₁, hC₁⟩ := hD 1 (by norm_num)
  have h0 : ∀ z : ℝ × ℝ, ‖e z‖ ≤ C₀ * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z => by
    simpa [norm_iteratedFDeriv_zero] using hC₀ z
  have h1 : ∀ z : ℝ × ℝ, ‖fderiv ℝ e z‖ ≤ C₁ * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z => by
    simpa [norm_iteratedFDeriv_one] using hC₁ z
  have heq_tsum : periodizeC d e =
      fun x => ∑' n : ℤ, e (x - UnforcedLeray.Gaussian.shiftVec d n) := by
    funext x
    rw [hper_eq, UnforcedLeray.Gaussian.periodize_eq]
  have hF := UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates
    (he_sm.differentiable (by norm_num)) one_lt_two hd0 h0 h1 y
  have hfderiv : fderiv ℝ (periodizeC d e) y =
      ∑' n : ℤ, fderiv ℝ e (y - UnforcedLeray.Gaussian.shiftVec d n) := by
    rw [heq_tsum, hF.fderiv]
    simp_rw [fderiv_comp_sub]
  have hsumD : Summable (fun n : ℤ => fderiv ℝ e (y - UnforcedLeray.Gaussian.shiftVec d n)) :=
    Summable.of_norm_bounded
      ((UnforcedLeray.Gaussian.summable_translate (s := 2) one_lt_two hd0 y.1).mul_left C₁)
      fun n => by rw [UnforcedLeray.Gaussian.sub_shiftVec]; exact h1 _
  unfold pdCx
  rw [hfderiv]
  change (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k))
      (∑' n : ℤ, fderiv ℝ e (y - UnforcedLeray.Gaussian.shiftVec d n)) = _
  rw [(hsumD.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k))).tsum_eq.symm]
  unfold periodizeC
  refine tsum_congr fun n => ?_
  rw [UnforcedLeray.Gaussian.sub_shiftVec]
  rfl

private theorem jb_nonneg (y : ℝ × ℝ) : 0 ≤ B0579.jb y := by
  unfold B0579.jb; positivity

private theorem jb_pow_mul_exp16_le (k : ℕ) (y : ℝ × ℝ) :
    B0579.jb y ^ k * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) ≤
      16 ^ k * (k.factorial : ℝ) * Real.exp (1 / 16) := by
  set s := y.1 ^ 2 + y.2 ^ 2
  have hs : 0 ≤ s := by positivity
  have hjb : B0579.jb y = 1 + s := by unfold B0579.jb; dsimp [s]; ring
  rw [hjb]
  have hpow := Real.pow_div_factorial_le_exp ((1 + s) / 16) (by positivity) k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at hpow
  have hexp : Real.exp ((1 + s) / 16) * Real.exp (-s / 16) = Real.exp (1 / 16) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (1 + s) ^ k * Real.exp (-s / 16)
      ≤ (Real.exp ((1 + s) / 16) * (16 ^ k * (k.factorial : ℝ))) * Real.exp (-s / 16) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 16 ^ k * (k.factorial : ℝ) * (Real.exp ((1 + s) / 16) * Real.exp (-s / 16)) := by ring
    _ = 16 ^ k * (k.factorial : ℝ) * Real.exp (1 / 16) := by rw [hexp]

/-! ### 5. Continuity of `kerVelPlanarCx` and symmetric image-expansion velocity comparison -/

private theorem continuous_kerVelPlanarCx {e : ℝ × ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (he_cont : Continuous e)
    (he_bd : ∀ z : ℝ × ℝ, ‖e z‖ ≤ M * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) (k : Fin 2) :
    Continuous (fun y : ℝ × ℝ => kerVelPlanarCx e y k) := by
  set eC : ℂ → ℂ := fun w => e (B0009.toPlane w)
  have heC_cont : Continuous eC := he_cont.comp (Complex.continuous_re.prodMk Complex.continuous_im)
  have heC_bd : ∀ w : ℂ, ‖eC w‖ ≤ M * Real.exp (-‖w‖ ^ 2 / 8) := by
    intro w
    have hsq : (B0009.toPlane w).1 ^ 2 + (B0009.toPlane w).2 ^ 2 = ‖w‖ ^ 2 := by
      simpa [GaussianVortex.radiusSq] using B0009.radiusSq_toPlane w
    simpa [eC, hsq] using he_bd (B0009.toPlane w)
  have heC_sup : ∀ w : ℂ, ‖eC w‖ ≤ M := fun w =>
    (heC_bd w).trans (mul_le_of_le_one_right hM
      (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖w‖])))
  have he_int : Integrable e :=
    Integrable.mono' ((EulerErrorTail.integrable_gauss (a := 8) (by norm_num)).const_mul M)
      he_cont.aestronglyMeasurable (Eventually.of_forall he_bd)
  have heC_int : Integrable eC := EulerErrorTail.integrable_toPlane he_int
  have hg16_C : Integrable (fun t : ℂ => Real.exp (-‖t‖ ^ 2 / 16)) := by
    have h0 : Integrable (fun z : ℝ × ℝ => ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp (EulerErrorTail.integrable_gauss (a := 16) (by norm_num))
    have h1 := Complex.reCLM.integrable_comp (EulerErrorTail.integrable_toPlane h0)
    refine h1.congr (Eventually.of_forall fun t => ?_)
    dsimp only [Function.comp_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_re]
    have hsq : (B0009.toPlane t).1 ^ 2 + (B0009.toPlane t).2 ^ 2 = ‖t‖ ^ 2 := by
      simpa [GaussianVortex.radiusSq] using B0009.radiusSq_toPlane t
    rw [hsq]
  have hshift_eq : ∀ y : ℝ × ℝ, kerVelPlanarCx e y k =
      ∫ t : ℂ, B0009.kernel k t * eC (planeToC y - t) := by
    intro y
    unfold kerVelPlanarCx
    rw [B0009.biotSavart_apply]
    have hF : (fun z : ℂ => B0009.kernel k (planeToC y - z) * eC z) =
        fun z => (fun t => B0009.kernel k t * eC (planeToC y - t)) (planeToC y - z) := by
      funext z; simp [sub_sub_cancel]
    rw [hF]
    exact integral_sub_left_eq_self (fun t : ℂ => B0009.kernel k t * eC (planeToC y - t))
      volume (planeToC y)
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set s := Metric.ball y₀ 1
  set R₀ : ℝ := ‖planeToC y₀‖ + 2
  have hB : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  set bound : ℂ → ℝ := fun t =>
    (Metric.ball (0 : ℂ) 1).indicator (fun w => ‖B0009.kernel k w‖ * M) t +
      (2 * Real.pi)⁻¹ * M * Real.exp (R₀ ^ 2 / 8) * Real.exp (-‖t‖ ^ 2 / 16)
  have hbound_int : Integrable bound := by
    refine Integrable.add ?_ (hg16_C.const_mul _)
    exact IntegrableOn.integrable_indicator
      ((B0009.integrableOn_kernel_ball k).norm.mul_const M) hB
  have hcont_s : ContinuousOn (fun y : ℝ × ℝ =>
      ∫ t : ℂ, B0009.kernel k t * eC (planeToC y - t)) s := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := bound)
      (fun y _ => (PartI.BiotSavartCurlAux.integrable_kernel_mul
        (heC_cont.comp (continuous_const.sub continuous_id))
        (fun _ => heC_sup _) (heC_int.comp_sub_left (planeToC y))).aestronglyMeasurable)
      (fun y hy => Eventually.of_forall fun t => ?_)
      hbound_int
      (Eventually.of_forall fun t => (continuous_const.mul
        (heC_cont.comp (EulerErrorTail.continuous_planeToC.sub continuous_const))).continuousOn)
    by_cases ht : t ∈ Metric.ball (0 : ℂ) 1
    · dsimp only [bound]
      rw [indicator_of_mem ht, norm_mul]
      have h1 : ‖B0009.kernel k t‖ * ‖eC (planeToC y - t)‖ ≤ ‖B0009.kernel k t‖ * M :=
        mul_le_mul_of_nonneg_left (heC_sup _) (norm_nonneg _)
      have h2 : 0 ≤ (2 * Real.pi)⁻¹ * M * Real.exp (R₀ ^ 2 / 8) * Real.exp (-‖t‖ ^ 2 / 16) := by
        positivity
      linarith
    · dsimp only [bound]
      rw [indicator_of_notMem ht, zero_add, norm_mul]
      have hk_bd : ‖B0009.kernel k t‖ ≤ (2 * Real.pi)⁻¹ := B0009.norm_kernel_le_of_notMem_ball k ht
      have hy_dist : ‖planeToC y‖ ≤ R₀ := by
        have hlt : ‖y - y₀‖ < 1 := by simpa [s, Metric.mem_ball, dist_eq_norm] using hy
        have hp_le : ‖planeToC (y - y₀)‖ ≤ 2 * ‖y - y₀‖ := by
          have hsq : ‖planeToC (y - y₀)‖ ^ 2 = (y - y₀).1 ^ 2 + (y - y₀).2 ^ 2 :=
            OscillatorForceSub.norm_planeToC_sq (y - y₀)
          obtain ⟨c1, c2⟩ := abs_coord_le_norm (y - y₀)
          have c1_sq := pow_le_pow_left₀ (abs_nonneg _) c1 2
          have c2_sq := pow_le_pow_left₀ (abs_nonneg _) c2 2
          have : ‖planeToC (y - y₀)‖ ^ 2 ≤ (2 * ‖y - y₀‖) ^ 2 := by
            nlinarith [sq_abs (y - y₀).1, sq_abs (y - y₀).2, norm_nonneg (y - y₀)]
          nlinarith [norm_nonneg (planeToC (y - y₀)), norm_nonneg (y - y₀)]
        have htri : ‖planeToC y‖ ≤ ‖planeToC y₀‖ + ‖planeToC (y - y₀)‖ := by
          rw [EulerErrorTail.planeToC_sub]
          simpa using norm_add_le (planeToC y₀) (planeToC y - planeToC y₀)
        dsimp [R₀]; linarith
      have hsq_diff : ‖t‖ ^ 2 / 2 - R₀ ^ 2 ≤ ‖planeToC y - t‖ ^ 2 := by
        have hrev : |‖t‖ - ‖planeToC y‖| ≤ ‖planeToC y - t‖ := by
          rw [norm_sub_rev (planeToC y) t]
          exact abs_norm_sub_norm_le t (planeToC y)
        have h1 : (‖t‖ - ‖planeToC y‖) ^ 2 ≤ ‖planeToC y - t‖ ^ 2 := by
          rw [← sq_abs (‖t‖ - ‖planeToC y‖)]
          exact pow_le_pow_left₀ (abs_nonneg _) hrev 2
        have h2 : ‖planeToC y‖ ^ 2 ≤ R₀ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hy_dist 2
        nlinarith [sq_nonneg (‖t‖ - 2 * ‖planeToC y‖)]
      have hexp_shift : Real.exp (-‖planeToC y - t‖ ^ 2 / 8) ≤
          Real.exp (R₀ ^ 2 / 8) * Real.exp (-‖t‖ ^ 2 / 16) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        linarith
      calc ‖B0009.kernel k t‖ * ‖eC (planeToC y - t)‖
          ≤ (2 * Real.pi)⁻¹ * (M * (Real.exp (R₀ ^ 2 / 8) * Real.exp (-‖t‖ ^ 2 / 16))) :=
            mul_le_mul hk_bd ((heC_bd _).trans (mul_le_mul_of_nonneg_left hexp_shift hM))
              (norm_nonneg _) (by positivity)
        _ = (2 * Real.pi)⁻¹ * M * Real.exp (R₀ ^ 2 / 8) * Real.exp (-‖t‖ ^ 2 / 16) := by ring
  simpa only [← hshift_eq] using
    hcont_s.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))

private theorem kerPl_eq_planarBSKernel (w : ℝ × ℝ) (k : Fin 2) :
    EulerSubCore.kerPl w k = IIb.planarBSKernel w k := by
  rw [EulerErrorTail.planarBSKernel_apply]
  by_cases hw : w.1 ^ 2 + w.2 ^ 2 = 0
  · have hw1 : w.1 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    have hw2 : w.2 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    have hw0 : w = (0, 0) := Prod.ext hw1 hw2
    subst hw0
    have hp0 : planeToC (0, 0) = 0 := by apply Complex.ext <;> simp [planeToC]
    fin_cases k
    · simp [EulerSubCore.kerPl_zero, hp0, B0009.kernel, B0009.perpComp]
    · simp [EulerSubCore.kerPl_one, hp0, B0009.kernel, B0009.perpComp]
  · set D : ℝ := 2 * Real.pi * (w.1 ^ 2 + w.2 ^ 2)
    have hD_ne : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (mul_ne_zero (by positivity) hw)
    have hinv : (2 * Real.pi * Complex.I * ((w.1 : ℂ) + (w.2 : ℂ) * Complex.I))⁻¹ =
        ((-w.2 / D : ℝ) : ℂ) + ((-w.1 / D : ℝ) : ℂ) * Complex.I := by
      have hmul : (2 * Real.pi * Complex.I * ((w.1 : ℂ) + (w.2 : ℂ) * Complex.I)) *
          (((-w.2 / D : ℝ) : ℂ) + ((-w.1 / D : ℝ) : ℂ) * Complex.I) = 1 := by
        have h1 : (2 * (Real.pi : ℂ) * Complex.I * ((w.1 : ℂ) + (w.2 : ℂ) * Complex.I)) *
            (-(w.2 : ℂ) + -(w.1 : ℂ) * Complex.I) = (D : ℂ) := by
          dsimp [D]
          push_cast
          calc (2 * (Real.pi : ℂ) * Complex.I * ((w.1 : ℂ) + (w.2 : ℂ) * Complex.I)) *
                (-(w.2 : ℂ) + -(w.1 : ℂ) * Complex.I)
              = 2 * (Real.pi : ℂ) * (-(w.1 : ℂ) ^ 2 * Complex.I ^ 2 -
                  (w.2 : ℂ) ^ 2 * Complex.I ^ 2 -
                  (w.1 : ℂ) * (w.2 : ℂ) * Complex.I * (1 + Complex.I ^ 2)) := by ring
            _ = 2 * (Real.pi : ℂ) * ((w.1 : ℂ) ^ 2 + (w.2 : ℂ) ^ 2) := by
                rw [Complex.I_sq]; ring
        have hrew : (((-w.2 / D : ℝ) : ℂ) + ((-w.1 / D : ℝ) : ℂ) * Complex.I) =
            (-(w.2 : ℂ) + -(w.1 : ℂ) * Complex.I) * (D : ℂ)⁻¹ := by
          push_cast; ring
        rw [hrew, ← mul_assoc, h1, mul_inv_cancel₀ hD_ne]
      exact inv_eq_of_mul_eq_one_right hmul
    have hp_sq : ‖planeToC w‖ ^ 2 = w.1 ^ 2 + w.2 ^ 2 := OscillatorForceSub.norm_planeToC_sq w
    have hp_re : (planeToC w).re = w.1 := by simp [EulerSubCore.planeToC_eq]
    have hp_im : (planeToC w).im = w.2 := by simp [EulerSubCore.planeToC_eq]
    fin_cases k
    · rw [Fin.zero_eta, EulerSubCore.kerPl_zero, hinv]
      simp only [B0009.kernel, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, B0009.perpComp, hp_sq, hp_im, D,
        mul_zero]
      ring
    · rw [Fin.mk_one, EulerSubCore.kerPl_one, hinv]
      simp only [B0009.kernel, Complex.ofReal_re, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, B0009.perpComp, hp_sq, hp_re, D,
        mul_zero, mul_one, add_zero, zero_add]
      ring

private def imgLinC (d : ℝ) (w : ℝ × ℝ) : ℂ :=
  -((2 * Real.pi * Complex.I)⁻¹ * (Real.pi ^ 2 / 3) * planeToC w / d ^ 2)

private def imgLin (d : ℝ) (w : ℝ × ℝ) (k : Fin 2) : ℝ :=
  if k = 0 then (imgLinC d w).re else -(imgLinC d w).im

private theorem imgLin_sub (d : ℝ) (y z : ℝ × ℝ) (k : Fin 2) :
    imgLin d (y - z) k = imgLin d y k - imgLin d z k := by
  have hc : imgLinC d (y - z) = imgLinC d y - imgLinC d z := by
    unfold imgLinC
    rw [EulerErrorTail.planeToC_sub]
    ring
  unfold imgLin
  rw [hc]
  split_ifs
  · exact Complex.sub_re _ _
  · rw [Complex.sub_im]; ring

private theorem imgLin_neg (d : ℝ) (z : ℝ × ℝ) (k : Fin 2) :
    imgLin d (-z) k = -imgLin d z k := by
  have h := imgLin_sub d 0 z k
  have h0 : imgLin d 0 k = 0 := by
    have hp0 : planeToC 0 = 0 := by apply Complex.ext <;> simp [planeToC]
    unfold imgLin imgLinC
    rw [hp0]; simp
  simpa [h0] using h

private theorem abs_imgLin_le {d : ℝ} (hd : 1 ≤ d) (w : ℝ × ℝ) (k : Fin 2) :
    |imgLin d w k| ≤ (Real.pi / 6) * ‖planeToC w‖ / d ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hnorm : ‖imgLinC d w‖ = (Real.pi / 6) * ‖planeToC w‖ / d ^ 2 := by
    unfold imgLinC
    rw [norm_neg, norm_div, norm_mul, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I]
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
    have hd_c : ‖(d : ℂ) ^ 2‖ = d ^ 2 := by simp [abs_of_pos hd0]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h3 : ‖((Real.pi : ℂ) ^ 2 / 3)‖ = Real.pi ^ 2 / 3 := by
      rw [norm_div, norm_pow, hpi]; norm_num
    rw [h2, hpi, h3, hd_c]
    field_simp; ring
  rw [← hnorm]
  unfold imgLin
  split_ifs
  · exact Complex.abs_re_le_norm _
  · rw [abs_neg]; exact Complex.abs_im_le_norm _

private theorem kerD_sub_planarBSKernel_sub_imgLin_le {d : ℝ} (hd : 1 ≤ d) {w : ℝ × ℝ}
    (hw : ‖planeToC w‖ ≤ d / 2) (k : Fin 2) :
    |kerD d w k - IIb.planarBSKernel w k - imgLin d w k| ≤
      EulerSubCore.KerExp.imageConst * ‖planeToC w‖ ^ 3 / d ^ 4 := by
  have hd0 : 0 < d := by linarith
  rw [← kerPl_eq_planarBSKernel]
  set ζ : ℂ := (w.1 : ℂ) + (w.2 : ℂ) * Complex.I with hζ
  have hζ_eq : ζ = planeToC w := (EulerSubCore.planeToC_eq w).symm
  by_cases h0 : ζ = 0
  · have hw_n : ‖planeToC w‖ = 0 := by rw [← hζ_eq, h0, norm_zero]
    have hL : imgLinC d w = 0 := by unfold imgLinC; rw [← hζ_eq, h0]; simp
    have hIL : imgLin d w k = 0 := by unfold imgLin; rw [hL]; simp
    rw [hIL, hw_n]
    fin_cases k
    · simp [EulerSubCore.kerD_zero, EulerSubCore.kerPl_zero, ← hζ, h0,
        Kernels.cylinderBS, Complex.cot]
    · simp [EulerSubCore.kerD_one, EulerSubCore.kerPl_one, ← hζ, h0,
        Kernels.cylinderBS, Complex.cot]
  · set Δ : ℂ := Kernels.cylinderBS d ζ - (2 * Real.pi * Complex.I * ζ)⁻¹ +
        (2 * Real.pi * Complex.I)⁻¹ * (Real.pi ^ 2 / 3) * ζ / d ^ 2 with hΔ
    have hexp := EulerSubCore.KerExp.cylinderBS_image_expansion' hd0 h0 (by rwa [hζ_eq])
    have hcomp : |kerD d w k - EulerSubCore.kerPl w k - imgLin d w k| ≤ ‖Δ‖ := by
      have hΔ' : Δ = Kernels.cylinderBS d ζ - (2 * Real.pi * Complex.I * ζ)⁻¹ - imgLinC d w := by
        rw [hΔ]; unfold imgLinC; rw [← hζ_eq]; ring
      fin_cases k
      · rw [Fin.zero_eta, EulerSubCore.kerD_zero, EulerSubCore.kerPl_zero, ← hζ]
        unfold imgLin
        simp only [ite_true]
        have hre : (Kernels.cylinderBS d ζ).re - ((2 * ↑Real.pi * Complex.I * ζ)⁻¹).re -
            (imgLinC d w).re = Δ.re := by rw [hΔ']; simp only [Complex.sub_re]
        rw [hre]; exact Complex.abs_re_le_norm Δ
      · rw [Fin.mk_one, EulerSubCore.kerD_one, EulerSubCore.kerPl_one, ← hζ]
        unfold imgLin
        have h10 : ((1 : Fin 2) = 0) = False := by decide
        simp only [h10, ite_false]
        have him : -(Kernels.cylinderBS d ζ).im - -((2 * ↑Real.pi * Complex.I * ζ)⁻¹).im -
            -(imgLinC d w).im = -Δ.im := by rw [hΔ']; simp only [Complex.sub_im]; ring
        rw [him, abs_neg]; exact Complex.abs_im_le_norm Δ
    rw [← hζ_eq]
    exact hcomp.trans hexp

private def rot90Equiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ))

private theorem rot90Equiv_apply (z : ℝ × ℝ) : rot90Equiv z = (-z.2, z.1) := rfl

private theorem measurePreserving_rot90 : MeasurePreserving rot90Equiv volume volume :=
  ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))).comp Measure.measurePreserving_swap

private theorem planarMode_rot90 (f : UnforcedLeray.Blueprint.Planar.Profile) (z : ℝ × ℝ) :
    planarMode f (rot90Equiv z) = -planarMode f z := by
  unfold planarMode angTwo
  rw [rot90Equiv_apply]
  simp only [neg_sq, Complex.ofReal_neg]
  have hrad : z.2 ^ 2 + z.1 ^ 2 = z.1 ^ 2 + z.2 ^ 2 := add_comm _ _
  have hnum : (-(z.2 : ℂ) + (z.1 : ℂ) * Complex.I) ^ 2 =
      -((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) ^ 2 := by
    calc (-(z.2 : ℂ) + (z.1 : ℂ) * Complex.I) ^ 2
        = (Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)) ^ 2 := by
          congr 1; linear_combination -(z.2 : ℂ) * Complex.I_sq
      _ = Complex.I ^ 2 * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) ^ 2 := mul_pow _ _ _
      _ = -((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) ^ 2 := by rw [Complex.I_sq, neg_one_mul]
  rw [hrad, hnum, neg_div, mul_neg]

private theorem planarMode_neg' (f : UnforcedLeray.Blueprint.Planar.Profile) (z : ℝ × ℝ) :
    planarMode f (-z) = planarMode f z := by
  unfold planarMode angTwo
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq, Complex.ofReal_neg]
  congr 2; ring

private theorem setIntegral_disk_planarMode_imgLin_zero
    {f : UnforcedLeray.Blueprint.Planar.Profile} (d R : ℝ) {k : Fin 2}
    (he_int : IntegrableOn (planarMode f) {z : ℝ × ℝ | ‖planeToC z‖ < R})
    (hmom_int : IntegrableOn (fun z : ℝ × ℝ => planarMode f z * ((imgLin d z k : ℝ) : ℂ))
      {z : ℝ × ℝ | ‖planeToC z‖ < R})
    (y : ℝ × ℝ) :
    ∫ z in {z : ℝ × ℝ | ‖planeToC z‖ < R},
      planarMode f z * ((imgLin d (y - z) k : ℝ) : ℂ) = 0 := by
  set D : Set (ℝ × ℝ) := {z : ℝ × ℝ | ‖planeToC z‖ < R}
  have hD_meas : MeasurableSet D :=
    measurableSet_lt (continuous_norm.comp EulerErrorTail.continuous_planeToC).measurable
      measurable_const
  -- Step 1: zero total mass on `D` via 90-degree rotation
  have hrot_pre : rot90Equiv ⁻¹' D = D := by
    ext z
    simp only [D, mem_preimage, mem_ofPred]
    have hsq : ‖planeToC (rot90Equiv z)‖ ^ 2 = ‖planeToC z‖ ^ 2 := by
      rw [OscillatorForceSub.norm_planeToC_sq, OscillatorForceSub.norm_planeToC_sq,
        rot90Equiv_apply]
      ring
    have heq : ‖planeToC (rot90Equiv z)‖ = ‖planeToC z‖ := by
      nlinarith [norm_nonneg (planeToC (rot90Equiv z)), norm_nonneg (planeToC z)]
    rw [heq]
  have hmass_zero : ∫ z in D, planarMode f z = 0 := by
    have hpres := measurePreserving_rot90.setIntegral_preimage_emb
      rot90Equiv.measurableEmbedding (planarMode f) D
    rw [hrot_pre] at hpres
    have hneg : ∫ z in D, planarMode f (rot90Equiv z) = -∫ z in D, planarMode f z := by
      simp_rw [planarMode_rot90]
      exact integral_neg (planarMode f)
    rw [hneg] at hpres
    exact CharZero.eq_neg_self_iff.mp hpres.symm
  -- Step 2: zero linear moment on `D` via negation `z ↦ -z`
  set negEq : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.neg (ℝ × ℝ)
  have hneg_pre : Neg.neg ⁻¹' D = D := by
    ext z
    simp only [D, mem_preimage, mem_ofPred]
    have hp : planeToC (-z) = -planeToC z := by
      apply Complex.ext <;> simp [planeToC]
    rw [hp, norm_neg]
  have hmom_zero : ∫ z in D, planarMode f z * ((imgLin d z k : ℝ) : ℂ) = 0 := by
    have hpres := (Measure.measurePreserving_neg (volume : Measure (ℝ × ℝ))).setIntegral_preimage_emb
      negEq.measurableEmbedding (fun z => planarMode f z * ((imgLin d z k : ℝ) : ℂ)) D
    rw [hneg_pre] at hpres
    have hodd : ∫ z in D, planarMode f (-z) * ((imgLin d (-z) k : ℝ) : ℂ) =
        -∫ z in D, planarMode f z * ((imgLin d z k : ℝ) : ℂ) := by
      have hfun : (fun z : ℝ × ℝ => planarMode f (-z) * ((imgLin d (-z) k : ℝ) : ℂ)) =
          fun z => -(planarMode f z * ((imgLin d z k : ℝ) : ℂ)) := by
        funext z
        simp only [planarMode_neg', imgLin_neg, Complex.ofReal_neg, mul_neg]
      rw [hfun]
      exact integral_neg _
    rw [hodd] at hpres
    exact CharZero.eq_neg_self_iff.mp hpres.symm
  -- Step 3: combine `imgLin d (y - z) k = imgLin d y k - imgLin d z k`
  have hlin_split : (fun z : ℝ × ℝ => planarMode f z * ((imgLin d (y - z) k : ℝ) : ℂ)) =
      fun z => planarMode f z * ((imgLin d y k : ℝ) : ℂ) -
        planarMode f z * ((imgLin d z k : ℝ) : ℂ) := by
    funext z
    rw [imgLin_sub, Complex.ofReal_sub, mul_sub]
  rw [hlin_split, integral_sub (he_int.mul_const _) hmom_int, integral_mul_const,
    hmass_zero, zero_mul, hmom_zero, sub_zero]

private theorem vel_compare_canonical :
    ∃ K_vc : ℝ, 0 < K_vc ∧
      ∀ {d : ℝ}, 1 ≤ d →
        ∀ (f : UnforcedLeray.Blueprint.Planar.Profile),
          ContDiffOn ℝ ∞ f (Ioi 0) →
          ∀ (u : XG), f =ᵐ[xGMeasure] (u : ℝ → ℂ) →
            ∀ (hu : u ∈ (fracPow 8).domain),
              let e := planarMode f
              let W := periodizeC d e
              let G₈ := Real.sqrt (graphNormSq 8 ⟨u, hu⟩)
              ∀ {y : ℝ × ℝ}, ‖planeToC y‖ ≤ d / 8 → ∀ k : Fin 2,
                ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ ≤
                  K_vc * ((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖ +
                    Real.exp (-(d ^ 2 / 256)) * G₈) := by
  obtain ⟨C_K, hCK, hKer⟩ := EulerErrorTail.cellKer_bound
  obtain ⟨C_mom, hCmom, hmom⟩ := moment_three_synthPlanar_le
  set I16 : ℝ := ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)
  have hI16_nn : 0 ≤ I16 := integral_nonneg fun _ => (Real.exp_pos _).le
  have hG16 : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) :=
    EulerErrorTail.integrable_gauss (by norm_num)
  set C_tail0 : ℝ := 512 * EulerErrorTail.sZ * jetSynthConst
  have hCtail0_nn : 0 ≤ C_tail0 := by
    dsimp [C_tail0]
    have := EulerErrorTail.sZ_nonneg
    have := jetSynthConst_pos.le
    positivity
  set K_vc : ℝ :=
    4 * EulerSubCore.KerExp.imageConst * C_mom +
      C_K * 1024 * C_tail0 + C_K * 1024 * jetSynthConst + 2 * jetSynthConst * I16 + 1
  have hKvc_pos : 0 < K_vc := by
    dsimp [K_vc]
    have hiC : 0 ≤ EulerSubCore.KerExp.imageConst := by
      unfold EulerSubCore.KerExp.imageConst; positivity
    have := jetSynthConst_pos.le
    positivity
  refine ⟨K_vc, hKvc_pos, fun {d} hd f hfc u hfu hu {y} hy k => ?_⟩
  set e := planarMode f
  set W := periodizeC d e
  set G₈ := Real.sqrt (graphNormSq 8 ⟨u, hu⟩)
  have hd0 : 0 < d := by linarith
  have he_eq : e = synthPlanar u := planarMode_eq_synthPlanar hfc hfu hu
  obtain ⟨hsm_F, hjet_F⟩ := contDiff_and_jet_synthPlanar u hu
  have he_sm : ContDiff ℝ 2 e := by rwa [he_eq]
  have he_cont : Continuous e := he_sm.continuous
  have hG₈_nn : 0 ≤ G₈ := Real.sqrt_nonneg _
  set C_e : ℝ := jetSynthConst * G₈
  have hCe_nn : 0 ≤ C_e := by dsimp [C_e]; have := jetSynthConst_pos.le; positivity
  have he_bd : ∀ z : ℝ × ℝ, ‖e z‖ ≤ C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro z
    rw [he_eq]
    simpa [norm_iteratedFDeriv_zero, C_e] using hjet_F (by norm_num : 0 ≤ 2) z
  have hW_cd : ContDiff ℝ 2 W :=
    (contDiff_and_pdCx_periodizeC hCe_nn he_sm
      (fun {m} hm z => by rw [he_eq]; exact hjet_F hm z) hd).1
  have hW_cont : Continuous W := hW_cd.continuous
  -- Disk `D = {|z| < d / 4} ⊆ cell d`
  set D : Set (ℝ × ℝ) := {z : ℝ × ℝ | ‖planeToC z‖ < d / 4}
  have hD_meas : MeasurableSet D :=
    measurableSet_lt (continuous_norm.comp EulerErrorTail.continuous_planeToC).measurable
      measurable_const
  have hD_cell : D ⊆ B0579.cell d := by
    intro z hz
    simp only [D, mem_ofPred] at hz
    have h1 : |z.1| ≤ ‖planeToC z‖ := by
      simpa [planeToC] using Complex.abs_re_le_norm (planeToC z)
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
    constructor <;> [linarith [neg_abs_le z.1]; linarith [le_abs_self z.1]]
  set eD : ℝ × ℝ → ℂ := D.indicator e
  set eF : ℝ × ℝ → ℂ := Dᶜ.indicator e
  have hsplit : ∀ z, e z = eD z + eF z := fun z => (indicator_self_add_compl_apply D e z).symm
  -- Exponential tail on `W - e`
  have hWe_tail : ∀ w ∈ B0579.cell d,
      ‖W w - e w‖ ≤ C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) *
        Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16) := by
    intro w hw
    have h := tail_gauss_exp hCe_nn he_bd hd (EulerErrorTail.abs_fst_le_of_mem_cell hw)
    refine h.trans (le_of_eq ?_)
    dsimp [C_tail0, C_e]; ring
  have hjb_We : ∀ w ∈ B0579.cell d,
      B0579.jb w ^ 2 * ‖W w - e w‖ ≤ 1024 * C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) := by
    intro w hw
    calc B0579.jb w ^ 2 * ‖W w - e w‖
        ≤ B0579.jb w ^ 2 * (C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) *
            Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) :=
          mul_le_mul_of_nonneg_left (hWe_tail w hw) (by positivity)
      _ = C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) *
            (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) := by ring
      _ ≤ C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) * 1024 :=
          mul_le_mul_of_nonneg_left (EulerErrorTail.jb_sq_exp_le w) (by positivity)
      _ = 1024 * C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) := by ring
  -- Far Gaussian split on `Dᶜ`: `|z| ≥ d / 4` implies `exp(-|z|²/8) ≤ exp(-d²/256) exp(-|z|²/16)`
  have hfar_exp : ∀ z : ℝ × ℝ, z ∉ D →
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤
        Real.exp (-(d ^ 2 / 256)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
    intro z hz
    have hz' : d / 4 ≤ ‖planeToC z‖ := le_of_not_gt (by simpa [D] using hz)
    have hsq : (d / 4) ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
      rw [EulerErrorTail.norm_planeToC_sq' z]
      exact pow_le_pow_left₀ (by positivity) hz' 2
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have hjb_eF : ∀ w ∈ B0579.cell d,
      B0579.jb w ^ 2 * ‖eF w‖ ≤ 1024 * C_e * Real.exp (-(d ^ 2 / 256)) := by
    intro w _
    by_cases hwD : w ∈ D
    · have hnot : w ∉ Dᶜ := by simpa using hwD
      simp only [eF, indicator_of_notMem hnot, norm_zero, mul_zero]; positivity
    · have hmem : w ∈ Dᶜ := hwD
      simp only [eF, indicator_of_mem hmem]
      have hw_bd := (he_bd w).trans (mul_le_mul_of_nonneg_left (hfar_exp w hwD) hCe_nn)
      calc B0579.jb w ^ 2 * ‖e w‖
          ≤ B0579.jb w ^ 2 * (C_e * (Real.exp (-(d ^ 2 / 256)) *
              Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16))) :=
            mul_le_mul_of_nonneg_left hw_bd (by positivity)
        _ = C_e * Real.exp (-(d ^ 2 / 256)) *
              (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) := by ring
        _ ≤ C_e * Real.exp (-(d ^ 2 / 256)) * 1024 :=
            mul_le_mul_of_nonneg_left (EulerErrorTail.jb_sq_exp_le w) (by positivity)
        _ = 1024 * C_e * Real.exp (-(d ^ 2 / 256)) := by ring
  have hjb_eD : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖eD w‖ ≤ C_e * 1024 := fun w _ =>
    (mul_le_mul_of_nonneg_left (norm_indicator_le_norm_self e w) (by positivity)).trans
      (EulerErrorTail.jb_gauss_bound hCe_nn he_bd w)
  have hjb_e : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖e w‖ ≤ C_e * 1024 := fun w _ =>
    EulerErrorTail.jb_gauss_bound hCe_nn he_bd w
  obtain ⟨hI_We, hB_We⟩ := hKer hd (by positivity)
    (hW_cont.sub he_cont).aestronglyMeasurable hjb_We y k
  obtain ⟨hI_eD, -⟩ := hKer hd (by positivity)
    (he_cont.aestronglyMeasurable.indicator hD_meas) hjb_eD y k
  obtain ⟨hI_eF, hB_eF⟩ := hKer hd (by positivity)
    (he_cont.aestronglyMeasurable.indicator hD_meas.compl) hjb_eF y k
  obtain ⟨hI_e, -⟩ := hKer hd (by positivity) he_cont.aestronglyMeasurable hjb_e y k
  -- Planar integrability
  have he_sup : ∀ z, ‖e z‖ ≤ C_e := fun z =>
    (he_bd z).trans (mul_le_of_le_one_right hCe_nn
      (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])))
  have he_int : Integrable e :=
    Integrable.mono' ((EulerErrorTail.integrable_gauss (a := 8) (by norm_num)).const_mul C_e)
      he_cont.aestronglyMeasurable (Eventually.of_forall he_bd)
  have hP : Integrable (fun z => B0009.kernel k (planeToC (y - z)) * e z) :=
    EulerErrorTail.integrable_kernel_planar he_cont he_sup he_int k y
  have hPD : Integrable (fun z => B0009.kernel k (planeToC (y - z)) * eD z) :=
    (hP.indicator hD_meas).congr (Eventually.of_forall fun z =>
      indicator_mul_right D (fun z => B0009.kernel k (planeToC (y - z))) e)
  have hPF : Integrable (fun z => B0009.kernel k (planeToC (y - z)) * eF z) :=
    (hP.indicator hD_meas.compl).congr (Eventually.of_forall fun z =>
      indicator_mul_right Dᶜ (fun z => B0009.kernel k (planeToC (y - z))) e)
  -- Decomposition into 4 integrals
  have hV : kerVelCx d W y k =
      (∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)) +
        ((∫ z in B0579.cell d, eD z * ((kerD d (y - z) k : ℝ) : ℂ)) +
          ∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)) := by
    unfold kerVelCx
    have h1 : ∫ z in B0579.cell d, W z * ((kerD d (y - z) k : ℝ) : ℂ) =
        ∫ z in B0579.cell d, ((W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ) +
          (eD z * ((kerD d (y - z) k : ℝ) : ℂ) + eF z * ((kerD d (y - z) k : ℝ) : ℂ))) := by
      congr 1; funext z; rw [hsplit z]; ring
    have hI_We' : IntegrableOn (fun z => (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ))
        (B0579.cell d) := hI_We
    have hI_eDF' : IntegrableOn
        (fun z => eD z * ((kerD d (y - z) k : ℝ) : ℂ) + eF z * ((kerD d (y - z) k : ℝ) : ℂ))
        (B0579.cell d) := hI_eD.add hI_eF
    rw [h1, integral_add hI_We' hI_eDF', integral_add hI_eD hI_eF]
  have hU : kerVelPlanarCx e y k =
      (∫ z, B0009.kernel k (planeToC (y - z)) * eD z) +
        ∫ z, B0009.kernel k (planeToC (y - z)) * eF z := by
    rw [EulerErrorTail.kerVelPlanarCx_eq, ← integral_add hPD hPF]
    congr 1; funext z; rw [hsplit z]; ring
  have hD1 : ∫ z in B0579.cell d, eD z * ((kerD d (y - z) k : ℝ) : ℂ) =
      ∫ z in D, e z * ((kerD d (y - z) k : ℝ) : ℂ) := by
    have : (fun z => eD z * ((kerD d (y - z) k : ℝ) : ℂ)) =
        D.indicator (fun z => e z * ((kerD d (y - z) k : ℝ) : ℂ)) := by
      funext z; simp only [eD, indicator_apply]; split_ifs <;> simp
    rw [this, setIntegral_indicator hD_meas, inter_eq_right.2 hD_cell]
  have hD2 : ∫ z, B0009.kernel k (planeToC (y - z)) * eD z =
      ∫ z in D, B0009.kernel k (planeToC (y - z)) * e z := by
    have : (fun z => B0009.kernel k (planeToC (y - z)) * eD z) =
        D.indicator (fun z => B0009.kernel k (planeToC (y - z)) * e z) := by
      funext z; simp only [eD, indicator_apply]; split_ifs <;> simp
    rw [this, integral_indicator hD_meas]
  have hdiffD : (∫ z in D, e z * ((kerD d (y - z) k : ℝ) : ℂ)) -
      ∫ z in D, B0009.kernel k (planeToC (y - z)) * e z =
      ∫ z in D, e z * ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k : ℝ) : ℂ) := by
    rw [← integral_sub (hI_e.mono_set hD_cell) hP.integrableOn]
    congr 1; funext z
    rw [EulerErrorTail.kernel_planeToC_eq]
    push_cast; ring
  -- Subtract zero linear image integral on `D`
  have himg_cont : Continuous (fun z : ℝ × ℝ => imgLin d z k) := by
    unfold imgLin imgLinC
    split_ifs
    · exact Complex.continuous_re.comp
        (((continuous_const.mul EulerErrorTail.continuous_planeToC).div_const _).neg)
    · exact (Complex.continuous_im.comp
        (((continuous_const.mul EulerErrorTail.continuous_planeToC).div_const _).neg)).neg
  have hmom_lin_int_all : Integrable (fun z : ℝ × ℝ => e z * ((imgLin d z k : ℝ) : ℂ)) := by
    refine Integrable.mono'
      (hG16.const_mul (C_e * (Real.pi / 6 / d ^ 2) * 4))
      (he_cont.mul (Complex.continuous_ofReal.comp himg_cont)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hl := (abs_imgLin_le hd z k).trans (show (Real.pi / 6) * ‖planeToC z‖ / d ^ 2 ≤
        (Real.pi / 6 / d ^ 2) * (1 + ‖planeToC z‖) by
      rw [mul_div_right_comm]; gcongr; linarith [norm_nonneg (planeToC z)])
    have hsplit_e : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) =
        Real.exp (-(‖planeToC z‖ ^ 2) / 16) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
      rw [← EulerErrorTail.norm_planeToC_sq' z, ← Real.exp_add]; ring_nf
    calc ‖e z‖ * |imgLin d z k|
        ≤ (C_e * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) *
            ((Real.pi / 6 / d ^ 2) * (1 + ‖planeToC z‖)) :=
          mul_le_mul (he_bd z) hl (abs_nonneg _) (by positivity)
      _ = C_e * (Real.pi / 6 / d ^ 2) *
            (((1 + ‖planeToC z‖) * Real.exp (-(‖planeToC z‖ ^ 2) / 16)) *
              Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) := by
          rw [hsplit_e]; ring
      _ ≤ C_e * (Real.pi / 6 / d ^ 2) * (4 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)) := by
          gcongr
          exact EulerErrorTail.one_add_mul_exp_le (norm_nonneg _)
      _ = (C_e * (Real.pi / 6 / d ^ 2) * 4) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by ring
  have hlin_zero : ∫ z in D, e z * ((imgLin d (y - z) k : ℝ) : ℂ) = 0 :=
    setIntegral_disk_planarMode_imgLin_zero d (d / 4) he_int.integrableOn
      hmom_lin_int_all.integrableOn y
  have hlin_yz_int : IntegrableOn (fun z : ℝ × ℝ => e z * ((imgLin d (y - z) k : ℝ) : ℂ)) D := by
    have heq_sub : (fun z : ℝ × ℝ => e z * ((imgLin d (y - z) k : ℝ) : ℂ)) =
        fun z => e z * ((imgLin d y k : ℝ) : ℂ) - e z * ((imgLin d z k : ℝ) : ℂ) := by
      funext z; rw [imgLin_sub, Complex.ofReal_sub, mul_sub]
    rw [heq_sub]
    exact (he_int.integrableOn.mul_const _).sub hmom_lin_int_all.integrableOn
  have hdiffD_rem : ∫ z in D, e z * ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k : ℝ) : ℂ) =
      ∫ z in D, e z *
        ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ) := by
    have hI_kerdiff : IntegrableOn
        (fun z : ℝ × ℝ => e z * ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k : ℝ) : ℂ)) D := by
      refine ((hI_e.mono_set hD_cell).sub hP.integrableOn).congr_fun (fun z _ => ?_) hD_meas
      simp only [Pi.sub_apply]
      rw [EulerErrorTail.kernel_planeToC_eq]; push_cast; ring
    calc ∫ z in D, e z * ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k : ℝ) : ℂ)
        = (∫ z in D, e z * ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k : ℝ) : ℂ)) -
            ∫ z in D, e z * ((imgLin d (y - z) k : ℝ) : ℂ) := by rw [hlin_zero, sub_zero]
      _ = ∫ z in D, e z *
            ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ) := by
          rw [← integral_sub hI_kerdiff hlin_yz_int]
          congr 1; funext z; push_cast; ring
  -- Bound the 4 pieces
  have b1 : ‖∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)‖ ≤
      C_K * 1024 * C_tail0 * Real.exp (-(d ^ 2 / 256)) * G₈ := by
    have hexp_mono : Real.exp (-(d ^ 2 / 128)) ≤ Real.exp (-(d ^ 2 / 256)) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg d])
    calc ‖∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)‖
        ≤ C_K * (1024 * C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128))) := hB_We
      _ ≤ C_K * (1024 * C_tail0 * G₈ * Real.exp (-(d ^ 2 / 256))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_mono (by positivity)) hCK
      _ = C_K * 1024 * C_tail0 * Real.exp (-(d ^ 2 / 256)) * G₈ := by ring
  obtain ⟨hmom_int, hmom_le⟩ := hmom u hu
  have b2 : ‖∫ z in D, e z *
      ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ)‖ ≤
      4 * EulerSubCore.KerExp.imageConst * C_mom *
        ((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖) := by
    set K_y : ℝ := 4 * EulerSubCore.KerExp.imageConst * (1 + ‖planeToC y‖ ^ 3) / d ^ 4
    have hiC_nn : 0 ≤ EulerSubCore.KerExp.imageConst := by
      unfold EulerSubCore.KerExp.imageConst; positivity
    have hKy_nn : 0 ≤ K_y := by dsimp [K_y]; positivity
    set g_dom : ℝ × ℝ → ℝ := fun z => K_y * ((1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖)
    have hg_int : Integrable g_dom := hmom_int.const_mul K_y
    have hg_nn : 0 ≤ᵐ[volume] g_dom := Eventually.of_forall fun z => by
      dsimp [g_dom]; exact mul_nonneg hKy_nn (mul_nonneg (by positivity) (norm_nonneg _))
    have hpt_rem : ∀ z ∈ D, ‖e z *
        ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ)‖ ≤
        g_dom z := by
      intro z hz
      have hz_lt : ‖planeToC z‖ < d / 4 := hz
      have hw_le : ‖planeToC (y - z)‖ ≤ d / 2 := by
        have htri : ‖planeToC (y - z)‖ ≤ ‖planeToC y‖ + ‖planeToC z‖ := by
          rw [EulerErrorTail.planeToC_sub]; exact norm_sub_le _ _
        linarith
      have hrem := kerD_sub_planarBSKernel_sub_imgLin_le hd hw_le k
      have htri : ‖planeToC (y - z)‖ ≤ ‖planeToC y‖ + ‖planeToC z‖ := by
        rw [EulerErrorTail.planeToC_sub]; exact norm_sub_le _ _
      have hcub : ‖planeToC (y - z)‖ ^ 3 ≤
          4 * (1 + ‖planeToC y‖ ^ 3) * (1 + ‖planeToC z‖ ^ 3) := by
        set a := ‖planeToC y‖
        set b := ‖planeToC z‖
        have ha : 0 ≤ a := norm_nonneg _
        have hb : 0 ≤ b := norm_nonneg _
        calc ‖planeToC (y - z)‖ ^ 3 ≤ (a + b) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) htri 3
          _ ≤ 4 * (a ^ 3 + b ^ 3) := by
              nlinarith [mul_nonneg (sq_nonneg (a - b)) (add_nonneg ha hb)]
          _ ≤ 4 * (1 + a ^ 3) * (1 + b ^ 3) := by
              nlinarith [mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 3),
                pow_nonneg ha 3, pow_nonneg hb 3]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he_eq]
      calc ‖synthPlanar u z‖ *
            |kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k|
          ≤ ‖synthPlanar u z‖ *
              (EulerSubCore.KerExp.imageConst *
                (4 * (1 + ‖planeToC y‖ ^ 3) * (1 + ‖planeToC z‖ ^ 3)) / d ^ 4) := by
            refine mul_le_mul_of_nonneg_left (hrem.trans ?_) (norm_nonneg _)
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcub hiC_nn) (by positivity)
        _ = g_dom z := by dsimp [g_dom, K_y]; ring
    have h1 := norm_integral_le_of_norm_le hg_int.integrableOn
      (ae_restrict_of_forall_mem hD_meas hpt_rem)
    have h2 : ∫ z in D, g_dom z ≤ ∫ z, g_dom z := setIntegral_le_integral hg_int hg_nn
    have h3 : ∫ z, g_dom z ≤
        4 * EulerSubCore.KerExp.imageConst * C_mom *
          ((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖) := by
      dsimp [g_dom]
      rw [integral_const_mul]
      calc K_y * ∫ z : ℝ × ℝ, (1 + ‖planeToC z‖ ^ 3) * ‖synthPlanar u z‖
          ≤ K_y * (C_mom * ‖u‖) := mul_le_mul_of_nonneg_left hmom_le hKy_nn
        _ = 4 * EulerSubCore.KerExp.imageConst * C_mom *
              ((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖) := by dsimp [K_y]; ring
    exact (h1.trans h2).trans h3
  have b3 : ‖∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)‖ ≤
      C_K * 1024 * jetSynthConst * Real.exp (-(d ^ 2 / 256)) * G₈ := by
    refine hB_eF.trans (le_of_eq ?_)
    dsimp [C_e]; ring
  have b4 : ‖∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ ≤
      2 * jetSynthConst * I16 * Real.exp (-(d ^ 2 / 256)) * G₈ := by
    have hfar_pt : ∀ z : ℝ × ℝ, ‖B0009.kernel k (planeToC (y - z)) * eF z‖ ≤
        (2 * C_e * Real.exp (-(d ^ 2 / 256))) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
      intro z
      by_cases hzD : z ∈ D
      · have hnot : z ∉ Dᶜ := by simpa using hzD
        simp only [eF, indicator_of_notMem hnot, mul_zero, norm_zero]; positivity
      · have hmem : z ∈ Dᶜ := hzD
        simp only [eF, indicator_of_mem hmem, norm_mul]
        have hz' : d / 4 ≤ ‖planeToC z‖ := le_of_not_gt (by simpa [D] using hzD)
        have hdist : d / 8 ≤ ‖planeToC (y - z)‖ := by
          rw [EulerErrorTail.planeToC_sub]
          have := norm_sub_norm_le (planeToC z) (planeToC y)
          rw [norm_sub_rev] at this
          linarith
        have hk_le : ‖B0009.kernel k (planeToC (y - z))‖ ≤ 2 := by
          refine (B0009.norm_kernel_le k _).trans ?_
          have hpos_yz : 0 < 2 * Real.pi * ‖planeToC (y - z)‖ :=
            mul_pos (by positivity) (by linarith)
          rw [inv_le_comm₀ hpos_yz (by norm_num)]
          have hpi := Real.pi_gt_three
          nlinarith
        have hez := (he_bd z).trans (mul_le_mul_of_nonneg_left (hfar_exp z hzD) hCe_nn)
        calc ‖B0009.kernel k (planeToC (y - z))‖ * ‖e z‖
            ≤ 2 * (C_e * (Real.exp (-(d ^ 2 / 256)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16))) :=
              mul_le_mul hk_le hez (norm_nonneg _) (by norm_num)
          _ = (2 * C_e * Real.exp (-(d ^ 2 / 256))) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
              ring
    have h1 := norm_integral_le_of_norm_le (hG16.const_mul _) (Eventually.of_forall hfar_pt)
    rw [integral_const_mul] at h1
    refine h1.trans (le_of_eq ?_)
    dsimp [C_e, I16]; ring
  -- Combine the 4 bounds
  have hcomb : kerVelCx d W y k - kerVelPlanarCx e y k =
      (∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)) +
        (∫ z in D, e z *
          ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ)) +
        (∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)) -
        ∫ z, B0009.kernel k (planeToC (y - z)) * eF z := by
    rw [hV, hU, hD1, hD2, ← hdiffD_rem, ← hdiffD]
    ring
  rw [hcomb]
  have htri : ‖(∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)) +
        (∫ z in D, e z *
          ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ)) +
        (∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)) -
        ∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ ≤
      ‖∫ z in B0579.cell d, (W z - e z) * ((kerD d (y - z) k : ℝ) : ℂ)‖ +
        ‖∫ z in D, e z *
          ((kerD d (y - z) k - IIb.planarBSKernel (y - z) k - imgLin d (y - z) k : ℝ) : ℂ)‖ +
        ‖∫ z in B0579.cell d, eF z * ((kerD d (y - z) k : ℝ) : ℂ)‖ +
        ‖∫ z, B0009.kernel k (planeToC (y - z)) * eF z‖ := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have hA_nn : 0 ≤ (1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖ := by positivity
  have hB_nn : 0 ≤ Real.exp (-(d ^ 2 / 256)) * G₈ := by positivity
  have hiC_nn : 0 ≤ EulerSubCore.KerExp.imageConst := by
    unfold EulerSubCore.KerExp.imageConst; positivity
  have hCm_nn : 0 ≤ C_mom := hCmom.le
  have hjS_nn : 0 ≤ jetSynthConst := jetSynthConst_pos.le
  dsimp only [K_vc]
  nlinarith [htri, b1, b2, b3, b4,
    mul_nonneg (by positivity : 0 ≤ C_K * 1024 * C_tail0 + C_K * 1024 * jetSynthConst +
      2 * jetSynthConst * I16 + 1) hA_nn,
    mul_nonneg (by positivity : 0 ≤ 4 * EulerSubCore.KerExp.imageConst * C_mom + 1) hB_nn]

/-! ### 6. Main proof assembly -/

private theorem datum_tail_exp :
    ∃ T_v : ℝ, 0 ≤ T_v ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ y ∈ B0579.cell d,
      ‖Train.datum d y - Train.v0 y‖ ≤
        T_v * Real.exp (-(d ^ 2 / 128)) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  obtain ⟨A₀, hA₀, hv0⟩ := EulerErrorTail.v0_gauss
  refine ⟨512 * EulerErrorTail.sZ * A₀, by have := EulerErrorTail.sZ_nonneg; positivity,
    fun {d} hd y hy => ?_⟩
  rw [Train.datum_apply]
  exact tail_gauss_exp hA₀ hv0 hd (EulerErrorTail.abs_fst_le_of_mem_cell hy)

private theorem gradE_tail_exp :
    ∃ T_g : ℝ, 0 ≤ T_g ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ y ∈ B0579.cell d, ∀ k : Fin 2,
      |B0579.pd k (UnforcedLeray.Cyl.curl (Train.datum d)) y - B0579.pd k Train.omega0 y| ≤
        T_g * Real.exp (-(d ^ 2 / 128)) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  obtain ⟨A₂, hA₂, hbA⟩ := Train.norm_iteratedFDeriv_v0_le 2
  refine ⟨2 * (512 * EulerErrorTail.sZ * A₂), by have := EulerErrorTail.sZ_nonneg; positivity,
    fun {d} hd y hy k => ?_⟩
  have hd0 : d ≠ 0 := by positivity
  have hv0 : ContDiff ℝ ∞ Train.v0 := Train.contDiff_v0
  have hdat : ContDiff ℝ ∞ (Train.datum d) := Train.datum_contDiff hd0
  rw [EulerErrorEig.omega0_eq_curl_v0, EulerErrorTail.pd_curl_sub _ _ hdat hv0 k y]
  have hle := TrainBddAux.pd_curl_le (Train.datum d - Train.v0) (hdat.sub hv0) k y
  rw [iteratedFDeriv_sub_apply (hdat.contDiffAt.of_le (by simp))
    (hv0.contDiffAt.of_le (by simp))] at hle
  have hjet : iteratedFDeriv ℝ 2 (Train.datum d) y =
      ∑' n : ℤ, iteratedFDeriv ℝ 2 Train.v0 (y.1 - n * d, y.2) := by
    have h := congrFun (Train.jet_datum hd0 2) y
    simpa only [Train.jet, UnforcedLeray.Gaussian.periodize] using h
  rw [hjet] at hle
  have ht := tail_gauss_exp hA₂ hbA hd (EulerErrorTail.abs_fst_le_of_mem_cell hy)
  calc |B0579.pd k (UnforcedLeray.Cyl.curl (Train.datum d - Train.v0)) y|
      ≤ 2 * ‖(∑' n : ℤ, iteratedFDeriv ℝ 2 Train.v0 (y.1 - n * d, y.2)) -
          iteratedFDeriv ℝ 2 Train.v0 y‖ := hle
    _ ≤ 2 * ((512 * EulerErrorTail.sZ) * A₂ * Real.exp (-(d ^ 2 / 128)) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = 2 * (512 * EulerErrorTail.sZ * A₂) * Real.exp (-(d ^ 2 / 128)) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring

private def aGauss : ℝ := 1 / 2048

private theorem aGauss_pos : 0 < aGauss := by unfold aGauss; norm_num

private theorem norm_sum5_le {E : Type*} [SeminormedAddCommGroup E]
    (a b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ : E) :
    ‖a + ((b₁ + b₂) + (c₁ + c₂) + (d₁ + d₂) + (e₁ + e₂))‖ ≤
      ‖a‖ + (‖b₁‖ + ‖b₂‖) + (‖c₁‖ + ‖c₂‖) + (‖d₁‖ + ‖d₂‖) + (‖e₁‖ + ‖e₂‖) := by
  have h1 := norm_add_le a ((b₁ + b₂) + (c₁ + c₂) + (d₁ + d₂) + (e₁ + e₂))
  have h2 := norm_add_le ((b₁ + b₂) + (c₁ + c₂) + (d₁ + d₂)) (e₁ + e₂)
  have h3 := norm_add_le ((b₁ + b₂) + (c₁ + c₂)) (d₁ + d₂)
  have h4 := norm_add_le (b₁ + b₂) (c₁ + c₂)
  linarith only [h1, h2, h3, h4, norm_add_le b₁ b₂, norm_add_le c₁ c₂,
    norm_add_le d₁ d₂, norm_add_le e₁ e₂]

private theorem movLPlanar_bounds :
    ∃ C_velP C_LP : ℝ, 0 ≤ C_velP ∧ 0 ≤ C_LP ∧
      ∀ {e : ℝ × ℝ → ℂ} {G₈ : ℝ}, 0 ≤ G₈ →
        ContDiff ℝ 2 e →
        (∀ z : ℝ × ℝ, ‖e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) →
        (∀ (k : Fin 2) (z : ℝ × ℝ),
          ‖pdCx k e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) →
        (∀ (k : Fin 2) (y : ℝ × ℝ), ‖kerVelPlanarCx e y k‖ ≤ C_velP * G₈) ∧
        (∀ z : ℝ × ℝ, ‖movLPlanar e z‖ ≤ (C_LP * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) ∧
        (∀ {d : ℝ}, 1 ≤ d → Continuous (periodizeC d (movLPlanar e))) := by
  obtain ⟨A₀, hA₀, hv0⟩ := EulerErrorTail.v0_gauss
  obtain ⟨C_ω, hCω, hg_ω⟩ := EulerErrorTail.g_bound
  obtain ⟨Kb0, hKb0_eq⟩ : ∃ x : ℝ, x = ∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel 0 t‖ := ⟨_, rfl⟩
  obtain ⟨Kb1, hKb1_eq⟩ : ∃ x : ℝ, x = ∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel 1 t‖ := ⟨_, rfl⟩
  obtain ⟨I8, hI8_eq⟩ : ∃ x : ℝ, x = ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb0 := hKb0_eq ▸ integral_nonneg fun _ => norm_nonneg _
  have hKb1 : 0 ≤ Kb1 := hKb1_eq ▸ integral_nonneg fun _ => norm_nonneg _
  have hI8_nn : 0 ≤ I8 := hI8_eq ▸ integral_nonneg fun _ => (Real.exp_pos _).le
  have hjS_nn : 0 ≤ jetSynthConst := jetSynthConst_pos.le
  obtain ⟨C_velP, hCvelP_eq⟩ :
      ∃ x : ℝ, x = jetSynthConst * (Kb0 + Kb1 + (2 * Real.pi)⁻¹ * I8) := ⟨_, rfl⟩
  have hCvelP_nn : 0 ≤ C_velP := by rw [hCvelP_eq]; positivity
  obtain ⟨C_LP, hCLP_eq⟩ : ∃ x : ℝ, x = 2 * A₀ * jetSynthConst + 2 * C_velP * C_ω := ⟨_, rfl⟩
  have hCLP_nn : 0 ≤ C_LP := by rw [hCLP_eq]; positivity
  refine ⟨C_velP, C_LP, hCvelP_nn, hCLP_nn, fun {e G₈} hG₈ he_sm he_bd hpd_e_bd => ?_⟩
  have hCe_nn : 0 ≤ jetSynthConst * G₈ := mul_nonneg hjS_nn hG₈
  have hkerVelP_bd : ∀ (k : Fin 2) (y : ℝ × ℝ), ‖kerVelPlanarCx e y k‖ ≤ C_velP * G₈ := by
    intro k y
    let eC : ℂ → ℂ := fun w => e (B0009.toPlane w)
    have heC_cont : Continuous eC :=
      he_sm.continuous.comp (Complex.continuous_re.prodMk Complex.continuous_im)
    have heC_sup : ∀ w : ℂ, ‖eC w‖ ≤ jetSynthConst * G₈ := fun w =>
      (he_bd (B0009.toPlane w)).trans (mul_le_of_le_one_right hCe_nn
        (Real.exp_le_one_iff.2
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by norm_num))))
    have he_int : Integrable e :=
      Integrable.mono'
        ((EulerErrorTail.integrable_gauss (a := 8) (by norm_num)).const_mul (jetSynthConst * G₈))
        he_sm.continuous.aestronglyMeasurable (Eventually.of_forall he_bd)
    have heC_int : Integrable eC := EulerErrorTail.integrable_toPlane he_int
    have h := EulerErrorTail.norm_biotSavart_le heC_cont heC_sup heC_int k (planeToC y)
    have hInt_le : ∫ t : ℂ, ‖eC t‖ ≤ (jetSynthConst * G₈) * I8 := by
      have heq_plane : ∫ t : ℂ, ‖eC t‖ = ∫ z : ℝ × ℝ, ‖e z‖ := by
        symm
        simpa [eC, B0009.toPlane] using
          (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
            Complex.measurableEquivRealProd.symm.measurableEmbedding (fun t : ℂ => ‖eC t‖)
      rw [heq_plane]
      have hg8 := EulerErrorTail.integrable_gauss (a := 8) (by norm_num)
      calc ∫ z : ℝ × ℝ, ‖e z‖
          ≤ ∫ z : ℝ × ℝ, (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
            integral_mono he_int.norm (hg8.const_mul _) he_bd
        _ = (jetSynthConst * G₈) * I8 := by rw [hI8_eq]; exact integral_const_mul _ _
    have hKb_le : (∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel k t‖) ≤ Kb0 + Kb1 := by
      fin_cases k
      · change (∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel 0 t‖) ≤ Kb0 + Kb1
        linarith only [hKb0_eq, hKb1]
      · change (∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel 1 t‖) ≤ Kb0 + Kb1
        linarith only [hKb1_eq, hKb0]
    unfold kerVelPlanarCx
    refine h.trans ?_
    calc (jetSynthConst * G₈) * (∫ t in Metric.ball (0 : ℂ) 1, ‖B0009.kernel k t‖) +
            (2 * Real.pi)⁻¹ * ∫ t, ‖eC t‖
        ≤ (jetSynthConst * G₈) * (Kb0 + Kb1) +
            (2 * Real.pi)⁻¹ * ((jetSynthConst * G₈) * I8) :=
          add_le_add (mul_le_mul_of_nonneg_left hKb_le hCe_nn)
            (mul_le_mul_of_nonneg_left hInt_le (by positivity))
      _ = C_velP * G₈ := by rw [hCvelP_eq]; ring
  have hLP_cont : Continuous (movLPlanar e) := by
    unfold movLPlanar
    have hv0_sm : ContDiff ℝ ∞ Train.v0 := Train.contDiff_v0
    have hc_pde : ∀ k : Fin 2, Continuous (pdCx k e) := fun k =>
      (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k)).continuous.comp
        (he_sm.continuous_fderiv (by norm_num))
    have hc_v0 : ∀ k : Fin 2, Continuous (fun y : ℝ × ℝ => ((Train.v0 y k : ℝ) : ℂ)) := fun k =>
      Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
          hv0_sm.continuous)
    have hc_om : ∀ k : Fin 2, Continuous (fun y : ℝ × ℝ => ((B0579.pd k Train.omega0 y : ℝ) : ℂ)) :=
      fun k => by
        rw [EulerErrorEig.omega0_eq_curl_v0]
        have hcurl_sm : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl Train.v0) := by
          rw [EulerErrorTail.curl_eq_pd _ (hv0_sm.of_le (by simp))]
          unfold B0579.pd
          exact (((ContinuousLinearMap.apply ℝ ℝ (B0579.dir 0)).contDiff.comp
            (((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
              hv0_sm).fderiv_right (by simp))).sub
            ((ContinuousLinearMap.apply ℝ ℝ (B0579.dir 1)).contDiff.comp
              (((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
                hv0_sm).fderiv_right (by simp))))
        exact Complex.continuous_ofReal.comp
          ((ContinuousLinearMap.apply ℝ ℝ (B0579.dir k)).continuous.comp
            (hcurl_sm.continuous_fderiv (by simp)))
    exact (((hc_v0 0).mul (hc_pde 0) |>.add ((hc_v0 1).mul (hc_pde 1))).neg).sub
      ((continuous_kerVelPlanarCx hCe_nn he_sm.continuous he_bd 0 |>.mul (hc_om 0)).add
        (continuous_kerVelPlanarCx hCe_nn he_sm.continuous he_bd 1 |>.mul (hc_om 1)))
  have hLP_bd : ∀ z : ℝ × ℝ,
      ‖movLPlanar e z‖ ≤ (C_LP * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro z
    unfold movLPlanar
    have hexp1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by norm_num))
    have hv0_sup : ∀ k : Fin 2, ‖((Train.v0 z k : ℝ) : ℂ)‖ ≤ A₀ := fun k =>
      (EulerErrorTail.norm_comp_le (Train.v0 z) k).trans
        ((hv0 z).trans (mul_le_of_le_one_right hA₀ hexp1))
    have ht1 : ‖((Train.v0 z 0 : ℝ) : ℂ) * pdCx 0 e z +
        ((Train.v0 z 1 : ℝ) : ℂ) * pdCx 1 e z‖ ≤
        (2 * A₀ * jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
      calc ‖((Train.v0 z 0 : ℝ) : ℂ) * pdCx 0 e z + ((Train.v0 z 1 : ℝ) : ℂ) * pdCx 1 e z‖
          ≤ ‖((Train.v0 z 0 : ℝ) : ℂ)‖ * ‖pdCx 0 e z‖ +
              ‖((Train.v0 z 1 : ℝ) : ℂ)‖ * ‖pdCx 1 e z‖ := EulerErrorTail.norm_pair _ _ _ _
        _ ≤ A₀ * ((jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) +
              A₀ * ((jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
            add_le_add (mul_le_mul (hv0_sup 0) (hpd_e_bd 0 z) (norm_nonneg _) hA₀)
              (mul_le_mul (hv0_sup 1) (hpd_e_bd 1 z) (norm_nonneg _) hA₀)
        _ = (2 * A₀ * jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by ring
    have ht2 : ‖kerVelPlanarCx e z 0 * ((B0579.pd 0 Train.omega0 z : ℝ) : ℂ) +
        kerVelPlanarCx e z 1 * ((B0579.pd 1 Train.omega0 z : ℝ) : ℂ)‖ ≤
        (2 * C_velP * C_ω * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
      have hom : ∀ k : Fin 2, ‖((B0579.pd k Train.omega0 z : ℝ) : ℂ)‖ ≤
          C_ω * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := fun k => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hg_ω z k
      calc ‖kerVelPlanarCx e z 0 * ((B0579.pd 0 Train.omega0 z : ℝ) : ℂ) +
            kerVelPlanarCx e z 1 * ((B0579.pd 1 Train.omega0 z : ℝ) : ℂ)‖
          ≤ ‖kerVelPlanarCx e z 0‖ * ‖((B0579.pd 0 Train.omega0 z : ℝ) : ℂ)‖ +
              ‖kerVelPlanarCx e z 1‖ * ‖((B0579.pd 1 Train.omega0 z : ℝ) : ℂ)‖ :=
            EulerErrorTail.norm_pair _ _ _ _
        _ ≤ (C_velP * G₈) * (C_ω * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) +
              (C_velP * G₈) * (C_ω * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
            add_le_add (mul_le_mul (hkerVelP_bd 0 z) (hom 0) (norm_nonneg _) (by positivity))
              (mul_le_mul (hkerVelP_bd 1 z) (hom 1) (norm_nonneg _) (by positivity))
        _ = (2 * C_velP * C_ω * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by ring
    calc ‖-(((Train.v0 z 0 : ℝ) : ℂ) * pdCx 0 e z + ((Train.v0 z 1 : ℝ) : ℂ) * pdCx 1 e z) -
            (kerVelPlanarCx e z 0 * ((B0579.pd 0 Train.omega0 z : ℝ) : ℂ) +
              kerVelPlanarCx e z 1 * ((B0579.pd 1 Train.omega0 z : ℝ) : ℂ))‖
        ≤ ‖((Train.v0 z 0 : ℝ) : ℂ) * pdCx 0 e z + ((Train.v0 z 1 : ℝ) : ℂ) * pdCx 1 e z‖ +
            ‖kerVelPlanarCx e z 0 * ((B0579.pd 0 Train.omega0 z : ℝ) : ℂ) +
              kerVelPlanarCx e z 1 * ((B0579.pd 1 Train.omega0 z : ℝ) : ℂ)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
      _ ≤ (2 * A₀ * jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) +
            (2 * C_velP * C_ω * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := add_le_add ht1 ht2
      _ = (C_LP * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by rw [hCLP_eq]; ring
  refine ⟨hkerVelP_bd, hLP_bd, fun {d} hd => ?_⟩
  have hd0 : 0 < d := by linarith
  have heq : periodizeC d (movLPlanar e) =
      fun y => ∑' n : ℤ, movLPlanar e (y - UnforcedLeray.Gaussian.shiftVec d n) := by
    funext y; unfold periodizeC; simp_rw [UnforcedLeray.Gaussian.sub_shiftVec]
  rw [heq]
  refine UnforcedLeray.Gaussian.continuous_tsum_translates hLP_cont (s := 2)
    one_lt_two hd0.ne' (C := 16 * (C_LP * G₈)) fun z => ?_
  calc ‖movLPlanar e z‖ ≤ (C_LP * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := hLP_bd z
    _ ≤ (C_LP * G₈) * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (exp8_le_translate_weight z) (mul_nonneg hCLP_nn hG₈)
    _ = 16 * (C_LP * G₈) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

private theorem movLGauss_bounds :
    ∃ C_W C_velC : ℝ, 0 < C_W ∧ 0 ≤ C_velC ∧
      ∀ {d : ℝ}, 1 ≤ d → ∀ {e : ℝ × ℝ → ℂ} {G₈ : ℝ}, 0 ≤ G₈ →
        ContDiff ℝ 2 e →
        (∀ {k : ℕ}, k ≤ 2 → ∀ z : ℝ × ℝ,
          ‖iteratedFDeriv ℝ k e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) →
        StronglyMeasurable (periodizeC d e) ∧
        (∀ k : Fin 2, StronglyMeasurable (pdCx k (periodizeC d e))) ∧
        StronglyMeasurable (movLGauss d (periodizeC d e)) ∧
        (∀ (k : Fin 2), ∀ y ∈ B0579.cell d,
          ‖pdCx k (periodizeC d e) y - pdCx k e y‖ ≤
            (512 * EulerErrorTail.sZ * jetSynthConst) * G₈ *
              Real.exp (-(d ^ 2 / 128)) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) ∧
        (∀ (k : Fin 2), ∀ y ∈ B0579.cell d,
          ‖pdCx k (periodizeC d e) y‖ ≤ C_W * G₈ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) ∧
        (∀ (k : Fin 2) (y : ℝ × ℝ), ‖kerVelCx d (periodizeC d e) y k‖ ≤ C_velC * G₈) := by
  obtain ⟨C_K, hCK, hKer⟩ := EulerErrorTail.cellKer_bound
  obtain ⟨C_tail0, hCtail0_eq⟩ :
      ∃ x : ℝ, x = 512 * EulerErrorTail.sZ * jetSynthConst := ⟨_, rfl⟩
  have hCtail0_nn : 0 ≤ C_tail0 := by
    rw [hCtail0_eq]; have := EulerErrorTail.sZ_nonneg; have := jetSynthConst_pos.le; positivity
  obtain ⟨C_W, hCW_eq⟩ : ∃ x : ℝ, x = jetSynthConst + C_tail0 := ⟨_, rfl⟩
  have hCW_pos : 0 < C_W := by rw [hCW_eq]; linarith [jetSynthConst_pos]
  obtain ⟨C_velC, hCvelC_eq⟩ : ∃ x : ℝ, x = C_K * (1024 * C_W) := ⟨_, rfl⟩
  have hCvelC_nn : 0 ≤ C_velC := by rw [hCvelC_eq]; have := hCW_pos.le; positivity
  refine ⟨C_W, C_velC, hCW_pos, hCvelC_nn, fun {d} hd {e G₈} hG₈ he_sm he_jet => ?_⟩
  obtain ⟨W, hW_eq⟩ : ∃ x, x = periodizeC d e := ⟨_, rfl⟩
  simp only [← hW_eq, ← hCtail0_eq]
  have hd0 : 0 < d := by linarith
  have hCe_nn : 0 ≤ jetSynthConst * G₈ := mul_nonneg jetSynthConst_pos.le hG₈
  have he_bd : ∀ z : ℝ × ℝ, ‖e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
    fun z => by simpa [norm_iteratedFDeriv_zero] using he_jet (by norm_num : 0 ≤ 2) z
  have hpd_e_bd : ∀ (k : Fin 2) (z : ℝ × ℝ),
      ‖pdCx k e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro k z
    have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
    have h1 : ‖pdCx k e z‖ ≤ ‖fderiv ℝ e z‖ := by
      unfold pdCx
      exact ((fderiv ℝ e z).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hdir)
    exact h1.trans (by simpa [norm_iteratedFDeriv_one] using he_jet (by norm_num : 1 ≤ 2) z)
  obtain ⟨hW_cd, hpd_W_eq⟩ := contDiff_and_pdCx_periodizeC hCe_nn he_sm he_jet hd
  rw [← hW_eq] at hW_cd hpd_W_eq
  have hW_sm : StronglyMeasurable W := hW_cd.continuous.stronglyMeasurable
  have hpdW_sm : ∀ k : Fin 2, StronglyMeasurable (pdCx k W) := fun k => by
    have hcont : Continuous (pdCx k W) := by
      unfold pdCx
      exact (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k)).continuous.comp
        (hW_cd.continuous_fderiv (by norm_num))
    exact hcont.stronglyMeasurable
  have hexp_d1 : Real.exp (-(d ^ 2 / 128)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  have hWe_tail : ∀ y ∈ B0579.cell d,
      ‖W y - e y‖ ≤ C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) *
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro y hy
    rw [hW_eq]
    refine (tail_gauss_exp hCe_nn he_bd hd (EulerErrorTail.abs_fst_le_of_mem_cell hy)).trans
      (le_of_eq ?_)
    rw [hCtail0_eq]; ring
  have hpdWe_tail : ∀ (k : Fin 2), ∀ y ∈ B0579.cell d,
      ‖pdCx k W y - pdCx k e y‖ ≤ C_tail0 * G₈ * Real.exp (-(d ^ 2 / 128)) *
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro k y hy
    rw [hpd_W_eq k y]
    refine (tail_gauss_exp hCe_nn (hpd_e_bd k) hd
      (EulerErrorTail.abs_fst_le_of_mem_cell hy)).trans (le_of_eq ?_)
    rw [hCtail0_eq]; ring
  have hW_cell_bd : ∀ y ∈ B0579.cell d,
      ‖W y‖ ≤ C_W * G₈ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro y hy
    have he16 : ‖e y‖ ≤ (jetSynthConst * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
      (he_bd y).trans (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 y) hCe_nn)
    have htr : ‖W y‖ ≤ ‖W y - e y‖ + ‖e y‖ := by simpa using norm_add_le (W y - e y) (e y)
    calc ‖W y‖ ≤ C_tail0 * G₈ * 1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
            (jetSynthConst * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
          refine htr.trans (add_le_add ?_ he16)
          exact (hWe_tail y hy).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_d1 (mul_nonneg hCtail0_nn hG₈))
            (Real.exp_pos _).le)
      _ = C_W * G₈ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by rw [hCW_eq]; ring
  have hpdW_cell_bd : ∀ (k : Fin 2), ∀ y ∈ B0579.cell d,
      ‖pdCx k W y‖ ≤ C_W * G₈ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro k y hy
    have he16 : ‖pdCx k e y‖ ≤ (jetSynthConst * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
      (hpd_e_bd k y).trans (mul_le_mul_of_nonneg_left (EulerErrorTail.exp8_le_exp16 y) hCe_nn)
    have htr : ‖pdCx k W y‖ ≤ ‖pdCx k W y - pdCx k e y‖ + ‖pdCx k e y‖ := by
      simpa using norm_add_le (pdCx k W y - pdCx k e y) (pdCx k e y)
    calc ‖pdCx k W y‖ ≤ C_tail0 * G₈ * 1 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
            (jetSynthConst * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
          refine htr.trans (add_le_add ?_ he16)
          exact (hpdWe_tail k y hy).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_d1 (mul_nonneg hCtail0_nn hG₈))
            (Real.exp_pos _).le)
      _ = C_W * G₈ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by rw [hCW_eq]; ring
  have hkerVelW_bd : ∀ (k : Fin 2) (y : ℝ × ℝ), ‖kerVelCx d W y k‖ ≤ C_velC * G₈ := by
    intro k y
    have hjbW : ∀ w ∈ B0579.cell d, B0579.jb w ^ 2 * ‖W w‖ ≤ 1024 * C_W * G₈ := by
      intro w hw
      calc B0579.jb w ^ 2 * ‖W w‖
          ≤ B0579.jb w ^ 2 * (C_W * G₈ * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) :=
            mul_le_mul_of_nonneg_left (hW_cell_bd w hw) (by positivity)
        _ = C_W * G₈ * (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) := by ring
        _ ≤ C_W * G₈ * 1024 :=
            mul_le_mul_of_nonneg_left (EulerErrorTail.jb_sq_exp_le w)
              (mul_nonneg hCW_pos.le hG₈)
        _ = 1024 * C_W * G₈ := by ring
    obtain ⟨-, hB⟩ := hKer hd (have := hCW_pos.le; by positivity)
      hW_cd.continuous.aestronglyMeasurable hjbW y k
    refine hB.trans (le_of_eq ?_)
    rw [hCvelC_eq]; ring
  have hLG_sm : StronglyMeasurable (movLGauss d W) := by
    unfold movLGauss
    have hdat_sm : ContDiff ℝ ∞ (Train.datum d) := Train.datum_contDiff hd0.ne'
    have hdat_comp : ∀ k : Fin 2, StronglyMeasurable
        (fun y : ℝ × ℝ => ((Train.datum d y k : ℝ) : ℂ)) := fun k =>
      (Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
          hdat_sm.continuous)).stronglyMeasurable
    have hcurl_dat : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl (Train.datum d)) := by
      rw [EulerErrorTail.curl_eq_pd _ (hdat_sm.of_le (by simp))]
      unfold B0579.pd
      exact (((ContinuousLinearMap.apply ℝ ℝ (B0579.dir 0)).contDiff.comp
        (((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
          hdat_sm).fderiv_right (by simp))).sub
        ((ContinuousLinearMap.apply ℝ ℝ (B0579.dir 1)).contDiff.comp
          (((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
            hdat_sm).fderiv_right (by simp))))
    have hpd_curl_sm : ∀ k : Fin 2, StronglyMeasurable (fun y : ℝ × ℝ =>
        ((B0579.pd k (UnforcedLeray.Cyl.curl (Train.datum d)) y : ℝ) : ℂ)) := fun k =>
      (Complex.continuous_ofReal.comp
        ((ContinuousLinearMap.apply ℝ ℝ (B0579.dir k)).continuous.comp
          (hcurl_dat.continuous_fderiv (by simp)))).stronglyMeasurable
    have hvel_sm : ∀ k : Fin 2, StronglyMeasurable (fun y : ℝ × ℝ => kerVelCx d W y k) :=
      fun k => EulerErrorSub.stronglyMeasurable_kerVelCx d hW_sm k
    exact (((((hdat_comp 0).mul (hpdW_sm 0)).add ((hdat_comp 1).mul (hpdW_sm 1))).neg).sub
      (((hvel_sm 0).mul (hpd_curl_sm 0)).add ((hvel_sm 1).mul (hpd_curl_sm 1))))
  exact ⟨hW_sm, hpdW_sm, hLG_sm, hpdWe_tail, hpdW_cell_bd, hkerVelW_bd⟩

private theorem res_cell_gauss_and_meas :
    ∃ C_W C_velC C_res_u C_res_G : ℝ,
      0 < C_W ∧ 0 ≤ C_velC ∧ 0 ≤ C_res_u ∧ 0 ≤ C_res_G ∧
      ∀ {d : ℝ}, 1 ≤ d → ∀ (f : ℝ → ℂ), ContDiffOn ℝ ∞ f (Ioi 0) →
        ∀ (u : XG), f =ᵐ[xGMeasure] (u : ℝ → ℂ) → ∀ (hu : u ∈ (fracPow 8).domain),
        Continuous (periodizeC d (movLPlanar (planarMode f))) ∧
        StronglyMeasurable (periodizeC d (planarMode f)) ∧
        (∀ k : Fin 2, StronglyMeasurable (pdCx k (periodizeC d (planarMode f)))) ∧
        StronglyMeasurable (movLGauss d (periodizeC d (planarMode f))) ∧
        (∀ (k : Fin 2), ∀ y ∈ B0579.cell d,
          ‖pdCx k (periodizeC d (planarMode f)) y‖ ≤
            C_W * Real.sqrt (graphNormSq 8 ⟨u, hu⟩) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) ∧
        (∀ (k : Fin 2) (y : ℝ × ℝ),
          ‖kerVelCx d (periodizeC d (planarMode f)) y k‖ ≤
            C_velC * Real.sqrt (graphNormSq 8 ⟨u, hu⟩)) ∧
        (∀ y ∈ B0579.cell d,
          ‖periodizeC d (movLPlanar (planarMode f)) y -
              movLGauss d (periodizeC d (planarMode f)) y‖ ≤
            (C_res_u * (d ^ (-4 : ℝ) * ‖u‖) +
              C_res_G * (Real.exp (-2 * aGauss * d ^ 2) * Real.sqrt (graphNormSq 8 ⟨u, hu⟩))) *
              Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by
  obtain ⟨A₀, hA₀, hv0⟩ := EulerErrorTail.v0_gauss
  obtain ⟨C_ω, hCω, hg_ω⟩ := EulerErrorTail.g_bound
  obtain ⟨T_v, hTv, hdat_tail⟩ := datum_tail_exp
  obtain ⟨T_g, hTg, hgrad_tail⟩ := gradE_tail_exp
  obtain ⟨K_vc, hKvc, hvc⟩ := vel_compare_canonical
  obtain ⟨C_velP, C_LP, hCvelP_nn, hCLP_nn, hLP_all⟩ := movLPlanar_bounds
  obtain ⟨C_W, C_velC, hCW_pos, hCvelC_nn, hLG_all⟩ := movLGauss_bounds
  obtain ⟨C_tail0, hCtail0_eq⟩ :
      ∃ x : ℝ, x = 512 * EulerErrorTail.sZ * jetSynthConst := ⟨_, rfl⟩
  have hCtail0_nn : 0 ≤ C_tail0 := by
    rw [hCtail0_eq]; have := EulerErrorTail.sZ_nonneg; have := jetSynthConst_pos.le; positivity
  obtain ⟨C_res_u, hCres_u_eq⟩ : ∃ x : ℝ, x = 2 * (1024 * K_vc * C_ω) := ⟨_, rfl⟩
  obtain ⟨C_res_G, hCres_G_eq⟩ : ∃ x : ℝ, x =
      512 * EulerErrorTail.sZ * C_LP +
        2 * (T_v * C_W + A₀ * C_tail0 + C_velC * T_g +
          K_vc * C_ω + (C_velP + C_velC) * C_ω) := ⟨_, rfl⟩
  have hCres_u_nn : 0 ≤ C_res_u := by rw [hCres_u_eq]; have := hKvc.le; positivity
  have hCres_G_nn : 0 ≤ C_res_G := by
    rw [hCres_G_eq]; have := EulerErrorTail.sZ_nonneg; have := hKvc.le; have := hCW_pos.le; positivity
  refine ⟨C_W, C_velC, C_res_u, C_res_G, hCW_pos, hCvelC_nn, hCres_u_nn, hCres_G_nn,
    fun {d} hd f hfc u hfu hu => ?_⟩
  obtain ⟨e, he_def⟩ : ∃ x, x = planarMode f := ⟨_, rfl⟩
  obtain ⟨W, hW_def⟩ : ∃ x, x = periodizeC d e := ⟨_, rfl⟩
  obtain ⟨G₈, hG₈_def⟩ : ∃ x : ℝ, x = Real.sqrt (graphNormSq 8 ⟨u, hu⟩) := ⟨_, rfl⟩
  simp only [← he_def, ← hW_def, ← hG₈_def]
  have hd0 : 0 < d := by linarith
  have hG₈_nn : 0 ≤ G₈ := hG₈_def ▸ Real.sqrt_nonneg _
  have he_eq : e = synthPlanar u := by rw [he_def]; exact planarMode_eq_synthPlanar hfc hfu hu
  obtain ⟨hsm_F, hjet_F⟩ := contDiff_and_jet_synthPlanar u hu
  have he_sm : ContDiff ℝ 2 e := he_eq ▸ hsm_F
  have he_jet : ∀ {k : ℕ}, k ≤ 2 → ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ k e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro k hk z; rw [he_eq, hG₈_def]; exact hjet_F hk z
  have he_bd : ∀ z : ℝ × ℝ, ‖e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
    fun z => by simpa [norm_iteratedFDeriv_zero] using he_jet (by norm_num : 0 ≤ 2) z
  have hpd_e_bd : ∀ (k : Fin 2) (z : ℝ × ℝ),
      ‖pdCx k e z‖ ≤ (jetSynthConst * G₈) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro k z
    have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
    have h1 : ‖pdCx k e z‖ ≤ ‖fderiv ℝ e z‖ := by
      unfold pdCx
      exact ((fderiv ℝ e z).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hdir)
    exact h1.trans (by simpa [norm_iteratedFDeriv_one] using he_jet (by norm_num : 1 ≤ 2) z)
  obtain ⟨hkerVelP_bd, hLP_bd, hperLP_cont_fn⟩ := hLP_all hG₈_nn he_sm he_bd hpd_e_bd
  have hperLP_cont : Continuous (periodizeC d (movLPlanar e)) := hperLP_cont_fn hd
  obtain ⟨hW_sm, hpdW_sm, hLG_sm, hpdWe_tail, hpdW_cell_bd, hkerVelW_bd⟩ :=
    hLG_all hd hG₈_nn he_sm he_jet
  rw [← hW_def] at hW_sm hpdW_sm hLG_sm hpdWe_tail hpdW_cell_bd hkerVelW_bd
  rw [← hCtail0_eq] at hpdWe_tail
  refine ⟨hperLP_cont, hW_sm, hpdW_sm, hLG_sm, hpdW_cell_bd, hkerVelW_bd, fun y hy => ?_⟩
  have hexp_128_le : Real.exp (-(d ^ 2 / 128)) ≤ Real.exp (-2 * aGauss * d ^ 2) := by
    apply Real.exp_le_exp.2; unfold aGauss; have := sq_nonneg d; linarith
  have hexp_256_le : Real.exp (-(d ^ 2 / 256)) ≤ Real.exp (-2 * aGauss * d ^ 2) := by
    apply Real.exp_le_exp.2; unfold aGauss; have := sq_nonneg d; linarith
  have hd_rpow4 : 1 / d ^ 4 = d ^ (-4 : ℝ) := by
    rw [Real.rpow_neg hd0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have hexp_y1 : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) ≤ 1 :=
    Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by norm_num))
  have hexp_y8_1 : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤ 1 :=
    Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by norm_num))
  have hp0 : ‖periodizeC d (movLPlanar e) y - movLPlanar e y‖ ≤
      (512 * EulerErrorTail.sZ * C_LP) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    have ht := tail_gauss_exp (mul_nonneg hCLP_nn hG₈_nn) hLP_bd hd
      (EulerErrorTail.abs_fst_le_of_mem_cell hy)
    refine ht.trans ?_
    have h1 : (512 * EulerErrorTail.sZ) * (C_LP * G₈) * Real.exp (-(d ^ 2 / 128)) ≤
        (512 * EulerErrorTail.sZ * C_LP) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) := by
      calc (512 * EulerErrorTail.sZ) * (C_LP * G₈) * Real.exp (-(d ^ 2 / 128))
          ≤ (512 * EulerErrorTail.sZ) * (C_LP * G₈) * Real.exp (-2 * aGauss * d ^ 2) :=
            mul_le_mul_of_nonneg_left hexp_128_le
              (by have := EulerErrorTail.sZ_nonneg; positivity)
        _ = (512 * EulerErrorTail.sZ * C_LP) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) := by ring
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hsplit_L : movLPlanar e y - movLGauss d W y =
      ((((Train.datum d y 0 : ℝ) : ℂ) - ((Train.v0 y 0 : ℝ) : ℂ)) * pdCx 0 W y +
        (((Train.datum d y 1 : ℝ) : ℂ) - ((Train.v0 y 1 : ℝ) : ℂ)) * pdCx 1 W y) +
      (((Train.v0 y 0 : ℝ) : ℂ) * (pdCx 0 W y - pdCx 0 e y) +
        ((Train.v0 y 1 : ℝ) : ℂ) * (pdCx 1 W y - pdCx 1 e y)) +
      (kerVelCx d W y 0 * (((B0579.pd 0 (UnforcedLeray.Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
          ((B0579.pd 0 Train.omega0 y : ℝ) : ℂ)) +
        kerVelCx d W y 1 * (((B0579.pd 1 (UnforcedLeray.Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
          ((B0579.pd 1 Train.omega0 y : ℝ) : ℂ))) +
      ((kerVelCx d W y 0 - kerVelPlanarCx e y 0) * ((B0579.pd 0 Train.omega0 y : ℝ) : ℂ) +
        (kerVelCx d W y 1 - kerVelPlanarCx e y 1) * ((B0579.pd 1 Train.omega0 y : ℝ) : ℂ)) := by
    unfold movLPlanar movLGauss; ring
  have hp1 : ∀ k : Fin 2,
      ‖(((Train.datum d y k : ℝ) : ℂ) - ((Train.v0 y k : ℝ) : ℂ)) * pdCx k W y‖ ≤
        (T_v * C_W) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro k
    rw [norm_mul]
    have hd_k : ‖(((Train.datum d y k : ℝ) : ℂ) - ((Train.v0 y k : ℝ) : ℂ))‖ ≤
        T_v * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
      (EulerErrorTail.norm_comp_sub_le _ _ k).trans
        ((hdat_tail hd y hy).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp_128_le hTv) (Real.exp_pos _).le))
    have hw_k : ‖pdCx k W y‖ ≤ C_W * G₈ :=
      (hpdW_cell_bd k y hy).trans
        (mul_le_of_le_one_right (mul_nonneg hCW_pos.le hG₈_nn) hexp_y1)
    calc ‖(((Train.datum d y k : ℝ) : ℂ) - ((Train.v0 y k : ℝ) : ℂ))‖ * ‖pdCx k W y‖
        ≤ (T_v * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) *
            (C_W * G₈) := mul_le_mul hd_k hw_k (norm_nonneg _) (by positivity)
      _ = (T_v * C_W) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  have hp2 : ∀ k : Fin 2,
      ‖((Train.v0 y k : ℝ) : ℂ) * (pdCx k W y - pdCx k e y)‖ ≤
        (A₀ * C_tail0) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro k
    rw [norm_mul]
    have hv_k : ‖((Train.v0 y k : ℝ) : ℂ)‖ ≤ A₀ :=
      (EulerErrorTail.norm_comp_le _ k).trans
        ((hv0 y).trans (mul_le_of_le_one_right hA₀ hexp_y8_1))
    have hpd_k : ‖pdCx k W y - pdCx k e y‖ ≤
        C_tail0 * G₈ * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
      (hpdWe_tail k y hy).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp_128_le (mul_nonneg hCtail0_nn hG₈_nn))
        (Real.exp_pos _).le)
    calc ‖((Train.v0 y k : ℝ) : ℂ)‖ * ‖pdCx k W y - pdCx k e y‖
        ≤ A₀ * (C_tail0 * G₈ * Real.exp (-2 * aGauss * d ^ 2) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
          mul_le_mul hv_k hpd_k (norm_nonneg _) hA₀
      _ = (A₀ * C_tail0) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  have hp3 : ∀ k : Fin 2,
      ‖kerVelCx d W y k * (((B0579.pd k (UnforcedLeray.Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
          ((B0579.pd k Train.omega0 y : ℝ) : ℂ))‖ ≤
        (C_velC * T_g) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro k
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hg_k : |B0579.pd k (UnforcedLeray.Cyl.curl (Train.datum d)) y -
        B0579.pd k Train.omega0 y| ≤
        T_g * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
      (hgrad_tail hd y hy k).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp_128_le hTg) (Real.exp_pos _).le)
    calc ‖kerVelCx d W y k‖ *
          |B0579.pd k (UnforcedLeray.Cyl.curl (Train.datum d)) y - B0579.pd k Train.omega0 y|
        ≤ (C_velC * G₈) *
            (T_g * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
          mul_le_mul (hkerVelW_bd k y) hg_k (abs_nonneg _) (by positivity)
      _ = (C_velC * T_g) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  have hp4 : ∀ k : Fin 2,
      ‖(kerVelCx d W y k - kerVelPlanarCx e y k) * ((B0579.pd k Train.omega0 y : ℝ) : ℂ)‖ ≤
        (1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
          (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hy_near : ‖planeToC y‖ ≤ d / 8
    · have hvc_k := hvc hd f hfc u hfu hu hy_near k
      rw [← he_def, ← hW_def, ← hG₈_def] at hvc_k
      have hom_k := hg_ω y k
      have hmul := mul_le_mul hvc_k hom_k (abs_nonneg _) (by have := hKvc.le; positivity)
      have h1 : ((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
          1024 * (d ^ (-4 : ℝ) * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
        rw [← hd_rpow4]
        calc ((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)
            = (1 / d ^ 4 * ‖u‖) * ((1 + ‖planeToC y‖ ^ 3) *
                Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by ring
          _ ≤ (1 / d ^ 4 * ‖u‖) * (1024 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
              mul_le_mul_of_nonneg_left (poly_three_exp_bound y) (by positivity)
          _ = 1024 * (1 / d ^ 4 * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
      have h2 : (Real.exp (-(d ^ 2 / 256)) * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
          (Real.exp (-2 * aGauss * d ^ 2) * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hexp_256_le hG₈_nn)
          (EulerErrorTail.exp8_le_exp16 y) (Real.exp_pos _).le (by positivity)
      have hextra : 0 ≤ (C_velP + C_velC) * C_ω * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by positivity
      have hsplit : (1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
            (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) =
          K_vc * C_ω *
            (1024 * (d ^ (-4 : ℝ) * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
              (Real.exp (-2 * aGauss * d ^ 2) * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) +
          (C_velP + C_velC) * C_ω * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
      calc ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ * |B0579.pd k Train.omega0 y|
          ≤ K_vc * C_ω *
              (((1 + ‖planeToC y‖ ^ 3) / d ^ 4 * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) +
                (Real.exp (-(d ^ 2 / 256)) * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by
            refine hmul.trans (le_of_eq ?_); ring
        _ ≤ K_vc * C_ω *
              (1024 * (d ^ (-4 : ℝ) * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
                (Real.exp (-2 * aGauss * d ^ 2) * G₈) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2) (mul_nonneg hKvc.le hCω)
        _ ≤ (1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
              (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
              Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by linarith only [hsplit, hextra]
    · have hy_far : d / 8 ≤ ‖planeToC y‖ := le_of_not_ge hy_near
      have hy_sq : (d / 8) ^ 2 ≤ y.1 ^ 2 + y.2 ^ 2 := by
        rw [EulerErrorTail.norm_planeToC_sq' y]
        exact pow_le_pow_left₀ (by positivity) hy_far 2
      have hexp_far : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
          Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        unfold aGauss
        have h64 : (d / 8) ^ 2 = d ^ 2 / 64 := by ring
        linarith only [hy_sq, h64, sq_nonneg d]
      have hvel_sum : ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ ≤ (C_velP + C_velC) * G₈ := by
        have htri_v := norm_sub_le (kerVelCx d W y k) (kerVelPlanarCx e y k)
        have h1 := hkerVelW_bd k y
        have h2 := hkerVelP_bd k y
        have h3 : C_velC * G₈ + C_velP * G₈ = (C_velP + C_velC) * G₈ := by ring
        linarith only [htri_v, h1, h2, h3]
      have hom_far : |B0579.pd k Train.omega0 y| ≤
          C_ω * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
        calc |B0579.pd k Train.omega0 y|
            ≤ C_ω * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := hg_ω y k
          _ ≤ C_ω * (Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
              mul_le_mul_of_nonneg_left hexp_far hCω
          _ = C_ω * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
      have hextra1 : 0 ≤ 1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by have := hKvc.le; positivity
      have hextra2 : 0 ≤ K_vc * C_ω * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by have := hKvc.le; positivity
      have hsplit : (1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
            (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) =
          ((C_velP + C_velC) * G₈) *
            (C_ω * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) +
          1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
          K_vc * C_ω * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
      calc ‖kerVelCx d W y k - kerVelPlanarCx e y k‖ * |B0579.pd k Train.omega0 y|
          ≤ ((C_velP + C_velC) * G₈) *
              (C_ω * Real.exp (-2 * aGauss * d ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
            mul_le_mul hvel_sum hom_far (abs_nonneg _) (by positivity)
        _ ≤ (1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
              (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
              Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
            linarith only [hsplit, hextra1, hextra2]
  have htri_all : ‖periodizeC d (movLPlanar e) y - movLGauss d W y‖ ≤
      ‖periodizeC d (movLPlanar e) y - movLPlanar e y‖ +
        (‖(((Train.datum d y 0 : ℝ) : ℂ) - ((Train.v0 y 0 : ℝ) : ℂ)) * pdCx 0 W y‖ +
          ‖(((Train.datum d y 1 : ℝ) : ℂ) - ((Train.v0 y 1 : ℝ) : ℂ)) * pdCx 1 W y‖) +
        (‖((Train.v0 y 0 : ℝ) : ℂ) * (pdCx 0 W y - pdCx 0 e y)‖ +
          ‖((Train.v0 y 1 : ℝ) : ℂ) * (pdCx 1 W y - pdCx 1 e y)‖) +
        (‖kerVelCx d W y 0 * (((B0579.pd 0 (UnforcedLeray.Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
            ((B0579.pd 0 Train.omega0 y : ℝ) : ℂ))‖ +
          ‖kerVelCx d W y 1 * (((B0579.pd 1 (UnforcedLeray.Cyl.curl (Train.datum d)) y : ℝ) : ℂ) -
            ((B0579.pd 1 Train.omega0 y : ℝ) : ℂ))‖) +
        (‖(kerVelCx d W y 0 - kerVelPlanarCx e y 0) * ((B0579.pd 0 Train.omega0 y : ℝ) : ℂ)‖ +
          ‖(kerVelCx d W y 1 - kerVelPlanarCx e y 1) * ((B0579.pd 1 Train.omega0 y : ℝ) : ℂ)‖) := by
    have h0 : periodizeC d (movLPlanar e) y - movLGauss d W y =
        (periodizeC d (movLPlanar e) y - movLPlanar e y) +
          (movLPlanar e y - movLGauss d W y) := by ring
    rw [h0, hsplit_L]
    exact norm_sum5_le _ _ _ _ _ _ _ _ _
  have b10 := hp1 0; have b11 := hp1 1
  have b20 := hp2 0; have b21 := hp2 1
  have b30 := hp3 0; have b31 := hp3 1
  have b40 := hp4 0; have b41 := hp4 1
  have hsum_eq :
      (512 * EulerErrorTail.sZ * C_LP) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
          Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
        ((T_v * C_W) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
          (T_v * C_W) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) +
        ((A₀ * C_tail0) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
          (A₀ * C_tail0) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) +
        ((C_velC * T_g) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
          (C_velC * T_g) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) +
        ((1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
            (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) +
          (1024 * K_vc * C_ω * (d ^ (-4 : ℝ) * ‖u‖) +
            (K_vc * C_ω + (C_velP + C_velC) * C_ω) * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
            Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) =
      (C_res_u * (d ^ (-4 : ℝ) * ‖u‖) + C_res_G * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    rw [hCres_u_eq, hCres_G_eq]; ring
  linarith only [htri_all, hp0, b10, b11, b20, b21, b30, b31, b40, b41, hsum_eq]

private theorem canonicalGaussAndJetBound_impl : ResidualBoundAux.CanonicalGaussAndJetBound := by
  intro m hm
  dsimp only
  obtain ⟨k_w, hkw_eq⟩ : ∃ k : ℕ, k = Nat.ceil m + 2 := ⟨_, rfl⟩
  simp only [← hkw_eq]
  obtain ⟨K_p, hKp, hxNorm_jb⟩ := EulerErrorSub.xNorm_le_of_jb_pow (m := m) (by linarith)
  rw [← hkw_eq] at hxNorm_jb
  obtain ⟨C_W, C_velC, C_res_u, C_res_G, hCW_pos, hCvelC_nn, hCres_u_nn, hCres_G_nn, hAll⟩ :=
    res_cell_gauss_and_meas
  obtain ⟨J_kw, hJkw_eq⟩ : ∃ x : ℝ, x = 16 ^ k_w * (k_w.factorial : ℝ) * Real.exp (1 / 16) :=
    ⟨_, rfl⟩
  have hJkw_pos : 0 < J_kw := by
    rw [hJkw_eq]
    have : (0 : ℝ) < (k_w.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k_w
    positivity
  obtain ⟨C_g, hCg_eq⟩ : ∃ x : ℝ, x =
      max (max (J_kw * C_W) C_velC) ((C_res_u + C_res_G + 1) * J_kw * (K_p + 1)) + 1 := ⟨_, rfl⟩
  have hCg_pos : 0 < C_g := by
    have h0 : 0 ≤ max (max (J_kw * C_W) C_velC) ((C_res_u + C_res_G + 1) * J_kw * (K_p + 1)) :=
      le_max_of_le_left (le_max_of_le_right hCvelC_nn)
    linarith only [hCg_eq, h0]
  refine ⟨C_g, aGauss, hCg_pos, aGauss_pos, fun d hd f _hf hfc u hfu hu => ?_⟩
  obtain ⟨e, he_def⟩ : ∃ x, x = planarMode f := ⟨_, rfl⟩
  obtain ⟨W, hW_def⟩ : ∃ x, x = periodizeC d e := ⟨_, rfl⟩
  obtain ⟨G₈, hG₈_def⟩ : ∃ x : ℝ, x = Real.sqrt (graphNormSq 8 ⟨u, hu⟩) := ⟨_, rfl⟩
  simp only [← he_def, ← hW_def, ← hG₈_def]
  have hd0 : 0 < d := by linarith
  have hG₈_nn : 0 ≤ G₈ := hG₈_def ▸ Real.sqrt_nonneg _
  obtain ⟨hperLP_cont, hW_sm, hpdW_sm, hLG_sm, hpdW_cell_bd, hkerVelW_bd, hres_cell⟩ :=
    hAll hd f hfc u hfu hu
  rw [← he_def] at hperLP_cont hW_sm hpdW_sm hLG_sm hpdW_cell_bd hkerVelW_bd hres_cell
  rw [← hW_def] at hW_sm hpdW_sm hLG_sm hpdW_cell_bd hkerVelW_bd hres_cell
  rw [← hG₈_def] at hpdW_cell_bd hkerVelW_bd hres_cell
  have haesm_res : AEStronglyMeasurable
      (fun y => periodizeC d (movLPlanar e) y - movLGauss d W y) (B0579.cellMeasure d m) :=
    (hperLP_cont.stronglyMeasurable.sub hLG_sm).aestronglyMeasurable
  have hclause5 : ∀ k : Fin 2, ∀ y ∈ B0579.cell d,
      B0579.jb y ^ k_w * ‖pdCx k W y‖ ≤ C_g * G₈ ∧ ‖kerVelCx d W y k‖ ≤ C_g * G₈ := by
    intro k y hy
    refine ⟨?_, ?_⟩
    · have h1 : B0579.jb y ^ k_w * ‖pdCx k W y‖ ≤ (J_kw * C_W) * G₈ := by
        calc B0579.jb y ^ k_w * ‖pdCx k W y‖
            ≤ B0579.jb y ^ k_w * (C_W * G₈ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
              mul_le_mul_of_nonneg_left (hpdW_cell_bd k y hy) (pow_nonneg (jb_nonneg y) k_w)
          _ = C_W * G₈ * (B0579.jb y ^ k_w * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by ring
          _ ≤ C_W * G₈ * J_kw :=
              mul_le_mul_of_nonneg_left (hJkw_eq ▸ jb_pow_mul_exp16_le k_w y)
                (mul_nonneg hCW_pos.le hG₈_nn)
          _ = (J_kw * C_W) * G₈ := by ring
      have hCg_ge : J_kw * C_W ≤ C_g := by
        have hm : J_kw * C_W ≤ max (max (J_kw * C_W) C_velC)
            ((C_res_u + C_res_G + 1) * J_kw * (K_p + 1)) :=
          le_max_of_le_left (le_max_left _ _)
        linarith only [hCg_eq, hm]
      exact h1.trans (mul_le_mul_of_nonneg_right hCg_ge hG₈_nn)
    · have hCg_ge : C_velC ≤ C_g := by
        have hm : C_velC ≤ max (max (J_kw * C_W) C_velC)
            ((C_res_u + C_res_G + 1) * J_kw * (K_p + 1)) :=
          le_max_of_le_left (le_max_right _ _)
        linarith only [hCg_eq, hm]
      exact (hkerVelW_bd k y).trans (mul_le_mul_of_nonneg_right hCg_ge hG₈_nn)
  obtain ⟨E_amp, hE_amp_eq⟩ :
      ∃ x : ℝ, x = d ^ (-4 : ℝ) * ‖u‖ + Real.exp (-2 * aGauss * d ^ 2) * G₈ := ⟨_, rfl⟩
  rw [← hE_amp_eq]
  have hE_amp_nn : 0 ≤ E_amp := by rw [hE_amp_eq]; positivity
  obtain ⟨M_jb, hM_jb_eq⟩ : ∃ x : ℝ, x = (C_res_u + C_res_G + 1) * J_kw * E_amp := ⟨_, rfl⟩
  have hM_jb_nn : 0 ≤ M_jb := by rw [hM_jb_eq]; positivity
  have hjb_res : ∀ y ∈ B0579.cell d,
      B0579.jb y ^ k_w * ‖periodizeC d (movLPlanar e) y - movLGauss d W y‖ ≤ M_jb := by
    intro y hy
    have hcoeff : C_res_u * (d ^ (-4 : ℝ) * ‖u‖) +
        C_res_G * (Real.exp (-2 * aGauss * d ^ 2) * G₈) ≤
        (C_res_u + C_res_G + 1) * E_amp := by
      have hsplit : (C_res_u + C_res_G + 1) * E_amp =
          C_res_u * (d ^ (-4 : ℝ) * ‖u‖) + C_res_G * (Real.exp (-2 * aGauss * d ^ 2) * G₈) +
            (C_res_G + 1) * (d ^ (-4 : ℝ) * ‖u‖) +
            (C_res_u + 1) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) := by
        rw [hE_amp_eq]; ring
      have hex1 : 0 ≤ (C_res_G + 1) * (d ^ (-4 : ℝ) * ‖u‖) := by positivity
      have hex2 : 0 ≤ (C_res_u + 1) * (Real.exp (-2 * aGauss * d ^ 2) * G₈) := by positivity
      linarith only [hsplit, hex1, hex2]
    calc B0579.jb y ^ k_w * ‖periodizeC d (movLPlanar e) y - movLGauss d W y‖
        ≤ B0579.jb y ^ k_w *
            ((C_res_u * (d ^ (-4 : ℝ) * ‖u‖) +
                C_res_G * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
              Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
          mul_le_mul_of_nonneg_left (hres_cell y hy) (pow_nonneg (jb_nonneg y) k_w)
      _ = (C_res_u * (d ^ (-4 : ℝ) * ‖u‖) +
              C_res_G * (Real.exp (-2 * aGauss * d ^ 2) * G₈)) *
            (B0579.jb y ^ k_w * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by ring
      _ ≤ ((C_res_u + C_res_G + 1) * E_amp) * J_kw :=
          mul_le_mul hcoeff (hJkw_eq ▸ jb_pow_mul_exp16_le k_w y)
            (mul_nonneg (pow_nonneg (jb_nonneg y) k_w) (Real.exp_pos _).le) (by positivity)
      _ = M_jb := by rw [hM_jb_eq]; ring
  have hxnorm_res : xNorm d m (fun y => periodizeC d (movLPlanar e) y - movLGauss d W y) ≤
      ENNReal.ofReal (C_g * E_amp) := by
    refine (hxNorm_jb d M_jb _ hM_jb_nn hjb_res).trans (ENNReal.ofReal_le_ofReal ?_)
    have hCg_ge : (C_res_u + C_res_G + 1) * J_kw * K_p ≤ C_g := by
      have h1 : (C_res_u + C_res_G + 1) * J_kw * K_p ≤
          (C_res_u + C_res_G + 1) * J_kw * (K_p + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only [hKp]) (by positivity)
      have h2 : (C_res_u + C_res_G + 1) * J_kw * (K_p + 1) ≤
          max (max (J_kw * C_W) C_velC) ((C_res_u + C_res_G + 1) * J_kw * (K_p + 1)) :=
        le_max_right _ _
      linarith only [hCg_eq, h1, h2]
    calc M_jb * K_p = ((C_res_u + C_res_G + 1) * J_kw * K_p) * E_amp := by rw [hM_jb_eq]; ring
      _ ≤ C_g * E_amp := mul_le_mul_of_nonneg_right hCg_ge hE_amp_nn
  exact ⟨haesm_res, hxnorm_res, hW_sm, hpdW_sm, hclause5⟩

end GaussAndJetBoundAux

/-- Leaf 2 (`ResidualBoundAux.CanonicalGaussAndJetBound`, `PartIII-a:T22/2/2/3`) proved
unconditionally with `0 sorry`. -/
theorem canonicalGaussAndJetBound_proof : ResidualBoundAux.CanonicalGaussAndJetBound :=
  GaussAndJetBoundAux.canonicalGaussAndJetBound_impl

end UnforcedLeray.Short.IIIa.T22Sub
