import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Part I, `PartI:T04/9/1`: Euclidean jets of a planar scalar (cutoff enstrophy, lines 285-288)

The cutoff enstrophies `G¹_R`, `G²_R` of `the November 2 reference manuscript`,
lines 285-288, use the Euclidean squares `|Dω|² = Σ_i (∂_i ω)²`, `|D²ω|² = Σ_{ij} (∂_i∂_jω)²`.
`Plane = ℝ × ℝ` carries the sup norm, so `‖iteratedFDeriv ℝ 1 f z‖ = |∂_q f| + |∂_η f|`
(non-smooth squares); the Euclidean jets below are the smooth quantities, and are compared with
the operator-norm jets with explicit constants:
`eucJet1 ≤ ‖Df‖² ≤ 2 eucJet1`, `eucJet2 ≤ 4 ‖D²f‖²`, `‖D²f‖² ≤ 4 eucJet2`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- Euclidean square of the gradient of a planar scalar: `(∂_q f)² + (∂_η f)²` (line 286). -/
def eucJet1 (f : Plane → ℝ) (z : Plane) : ℝ :=
  Cyl.partialQ f z ^ 2 + Cyl.partialEta f z ^ 2

/-- Euclidean square of the Hessian of a planar scalar: `Σ_{ij} (∂_i∂_j f)²` (line 286). -/
def eucJet2 (f : Plane → ℝ) (z : Plane) : ℝ :=
  Cyl.partialQ (Cyl.partialQ f) z ^ 2 + Cyl.partialQ (Cyl.partialEta f) z ^ 2 +
    Cyl.partialEta (Cyl.partialQ f) z ^ 2 + Cyl.partialEta (Cyl.partialEta f) z ^ 2

/-- Euclidean jet of order `j` (`j = 1, 2`; otherwise the operator-norm square). -/
def eucJetN (j : ℕ) (f : Plane → ℝ) (z : Plane) : ℝ :=
  if j = 1 then eucJet1 f z else if j = 2 then eucJet2 f z else ‖iteratedFDeriv ℝ j f z‖ ^ 2

theorem eucJet1_nonneg (f : Plane → ℝ) (z : Plane) : 0 ≤ eucJet1 f z := by
  unfold eucJet1; positivity

theorem eucJet2_nonneg (f : Plane → ℝ) (z : Plane) : 0 ≤ eucJet2 f z := by
  unfold eucJet2; positivity

theorem eucJetN_nonneg (j : ℕ) (f : Plane → ℝ) (z : Plane) : 0 ≤ eucJetN j f z := by
  unfold eucJetN
  split_ifs
  · exact eucJet1_nonneg f z
  · exact eucJet2_nonneg f z
  · positivity

/-- The coordinate directions. -/
def eQ : Plane := (1, 0)
def eE : Plane := (0, 1)

theorem partialQ_eq_fderiv {f : Plane → ℝ} {z : Plane} (hf : DifferentiableAt ℝ f z) :
    Cyl.partialQ f z = fderiv ℝ f z eQ := by
  unfold Cyl.partialQ
  have h1 : HasDerivAt (fun q : ℝ => ((q, z.2) : Plane)) eQ z.1 :=
    HasDerivAt.prodMk (hasDerivAt_id z.1) (hasDerivAt_const z.1 z.2)
  have h2 : HasFDerivAt f (fderiv ℝ f z) ((z.1, z.2) : Plane) := hf.hasFDerivAt
  have := h2.comp_hasDerivAt z.1 h1
  exact this.deriv

theorem partialEta_eq_fderiv {f : Plane → ℝ} {z : Plane} (hf : DifferentiableAt ℝ f z) :
    Cyl.partialEta f z = fderiv ℝ f z eE := by
  unfold Cyl.partialEta
  have h1 : HasDerivAt (fun η : ℝ => ((z.1, η) : Plane)) eE z.2 :=
    HasDerivAt.prodMk (hasDerivAt_const z.2 z.1) (hasDerivAt_id z.2)
  have h2 : HasFDerivAt f (fderiv ℝ f z) ((z.1, z.2) : Plane) := hf.hasFDerivAt
  have := h2.comp_hasDerivAt z.2 h1
  exact this.deriv

theorem partialQ_fun {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialQ f = fun w => fderiv ℝ f w eQ :=
  funext fun w => partialQ_eq_fderiv (hf.differentiable (by simp) w)

theorem partialEta_fun {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialEta f = fun w => fderiv ℝ f w eE :=
  funext fun w => partialEta_eq_fderiv (hf.differentiable (by simp) w)

/-- `∂_a ∂_b f = D²f (a,b)` for the directional second derivatives. -/
theorem fderiv_fderiv_apply_euc {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Plane) (z : Plane) :
    fderiv ℝ (fun w => fderiv ℝ f w b) z a = iteratedFDeriv ℝ 2 f z ![a, b] := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : Plane => b) hd
    (differentiableAt_const b)
  have h0 : fderiv ℝ (fun _ : Plane => b) z = 0 := by rw [fderiv_fun_const]; rfl
  rw [this, h0]
  simp

theorem eucJet1_eq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    eucJet1 f z = (iteratedFDeriv ℝ 1 f z ![eQ]) ^ 2 + (iteratedFDeriv ℝ 1 f z ![eE]) ^ 2 := by
  unfold eucJet1
  rw [partialQ_eq_fderiv (hf.differentiable (by simp) z),
    partialEta_eq_fderiv (hf.differentiable (by simp) z), iteratedFDeriv_one_apply,
    iteratedFDeriv_one_apply]
  simp

theorem eucJet2_eq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    eucJet2 f z = (iteratedFDeriv ℝ 2 f z ![eQ, eQ]) ^ 2 + (iteratedFDeriv ℝ 2 f z ![eQ, eE]) ^ 2 +
      (iteratedFDeriv ℝ 2 f z ![eE, eQ]) ^ 2 + (iteratedFDeriv ℝ 2 f z ![eE, eE]) ^ 2 := by
  have hQ := hf
  have h1 : Cyl.partialQ (Cyl.partialQ f) z = iteratedFDeriv ℝ 2 f z ![eQ, eQ] := by
    rw [partialQ_fun hf, partialQ_eq_fderiv ((hf.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const |>.differentiable (by simp) z)]
    exact fderiv_fderiv_apply_euc hf _ _ z
  have h2 : Cyl.partialQ (Cyl.partialEta f) z = iteratedFDeriv ℝ 2 f z ![eQ, eE] := by
    rw [partialEta_fun hf, partialQ_eq_fderiv ((hf.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const |>.differentiable (by simp) z)]
    exact fderiv_fderiv_apply_euc hf _ _ z
  have h3 : Cyl.partialEta (Cyl.partialQ f) z = iteratedFDeriv ℝ 2 f z ![eE, eQ] := by
    rw [partialQ_fun hf, partialEta_eq_fderiv ((hf.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const |>.differentiable (by simp) z)]
    exact fderiv_fderiv_apply_euc hf _ _ z
  have h4 : Cyl.partialEta (Cyl.partialEta f) z = iteratedFDeriv ℝ 2 f z ![eE, eE] := by
    rw [partialEta_fun hf, partialEta_eq_fderiv ((hf.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const |>.differentiable (by simp) z)]
    exact fderiv_fderiv_apply_euc hf _ _ z
  unfold eucJet2
  rw [h1, h2, h3, h4]

theorem norm_eQ : ‖eQ‖ = 1 := by simp [eQ, Prod.norm_def]
theorem norm_eE : ‖eE‖ = 1 := by simp [eE, Prod.norm_def]

/-- Operator norm of a linear functional on the plane in coordinates. -/
theorem opNorm_plane_le (L : Plane →L[ℝ] ℝ) : ‖L‖ ≤ |L eQ| + |L eE| := by
  refine L.opNorm_le_bound (by positivity) fun x => ?_
  have hx : x = x.1 • eQ + x.2 • eE := by ext <;> simp [eQ, eE]
  have h1 : |x.1| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_fst_le x
  have h2 : |x.2| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_snd_le x
  have : L x = x.1 * L eQ + x.2 * L eE := by
    conv_lhs => rw [hx]
    simp
  rw [this, Real.norm_eq_abs]
  calc |x.1 * L eQ + x.2 * L eE| ≤ |x.1 * L eQ| + |x.2 * L eE| := abs_add_le _ _
    _ = |x.1| * |L eQ| + |x.2| * |L eE| := by rw [abs_mul, abs_mul]
    _ ≤ ‖x‖ * |L eQ| + ‖x‖ * |L eE| := by gcongr
    _ = (|L eQ| + |L eE|) * ‖x‖ := by ring

theorem le_opNorm_plane (L : Plane →L[ℝ] ℝ) : |L eQ| + |L eE| ≤ ‖L‖ := by
  set x : Plane := (SignType.sign (L eQ), SignType.sign (L eE)) with hxd
  have hs : ∀ a : ℝ, |(SignType.sign a : ℝ)| ≤ 1 := fun a => by
    rcases lt_trichotomy a 0 with h | h | h <;> simp [h, sign_neg, sign_pos]
  have hxn : ‖x‖ ≤ 1 := by
    rw [hxd, Prod.norm_def]
    exact max_le (by simpa using hs _) (by simpa using hs _)
  have hx : x = (SignType.sign (L eQ) : ℝ) • eQ + (SignType.sign (L eE) : ℝ) • eE := by
    ext <;> simp [eQ, eE, hxd]
  have hL : L x = |L eQ| + |L eE| := by
    rw [hx]
    simp only [map_add, map_smul, smul_eq_mul]
    have e : ∀ a : ℝ, (SignType.sign a : ℝ) * a = |a| := fun a => by
      rcases lt_trichotomy a 0 with h | h | h <;> simp [h, sign_neg, sign_pos, abs_of_neg, abs_of_pos]
    rw [e, e]
  have := L.le_opNorm x
  rw [hL, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
  calc |L eQ| + |L eE| ≤ ‖L‖ * ‖x‖ := this
    _ ≤ ‖L‖ * 1 := by gcongr
    _ = ‖L‖ := mul_one _

theorem eucJet1_le_norm_sq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    eucJet1 f z ≤ ‖iteratedFDeriv ℝ 1 f z‖ ^ 2 := by
  rw [norm_iteratedFDeriv_one]
  unfold eucJet1
  rw [partialQ_eq_fderiv (hf.differentiable (by simp) z),
    partialEta_eq_fderiv (hf.differentiable (by simp) z)]
  have := le_opNorm_plane (fderiv ℝ f z)
  nlinarith [abs_nonneg (fderiv ℝ f z eQ), abs_nonneg (fderiv ℝ f z eE), sq_abs (fderiv ℝ f z eQ),
    sq_abs (fderiv ℝ f z eE)]

theorem norm_sq_le_two_eucJet1 {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    ‖iteratedFDeriv ℝ 1 f z‖ ^ 2 ≤ 2 * eucJet1 f z := by
  rw [norm_iteratedFDeriv_one]
  unfold eucJet1
  rw [partialQ_eq_fderiv (hf.differentiable (by simp) z),
    partialEta_eq_fderiv (hf.differentiable (by simp) z)]
  have h := opNorm_plane_le (fderiv ℝ f z)
  have h0 : 0 ≤ ‖fderiv ℝ f z‖ := norm_nonneg _
  have : ‖fderiv ℝ f z‖ ^ 2 ≤ (|fderiv ℝ f z eQ| + |fderiv ℝ f z eE|) ^ 2 := by gcongr
  nlinarith [sq_abs (fderiv ℝ f z eQ), sq_abs (fderiv ℝ f z eE),
    sq_nonneg (|fderiv ℝ f z eQ| - |fderiv ℝ f z eE|)]

/-- Entries of the Hessian are bounded by its norm. -/
theorem abs_iter2_le {f : Plane → ℝ} (z : Plane) (a b : Plane) :
    |iteratedFDeriv ℝ 2 f z ![a, b]| ≤ ‖iteratedFDeriv ℝ 2 f z‖ * (‖a‖ * ‖b‖) := by
  have := (iteratedFDeriv ℝ 2 f z).le_opNorm ![a, b]
  rw [Real.norm_eq_abs, Fin.prod_univ_two] at this
  simpa using this

theorem eucJet2_le_norm_sq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    eucJet2 f z ≤ 4 * ‖iteratedFDeriv ℝ 2 f z‖ ^ 2 := by
  rw [eucJet2_eq hf]
  have h : ∀ a b : Plane, ‖a‖ = 1 → ‖b‖ = 1 →
      (iteratedFDeriv ℝ 2 f z ![a, b]) ^ 2 ≤ ‖iteratedFDeriv ℝ 2 f z‖ ^ 2 := by
    intro a b ha hb
    have := abs_iter2_le (f := f) z a b
    rw [ha, hb, mul_one, mul_one] at this
    calc _ = |iteratedFDeriv ℝ 2 f z ![a, b]| ^ 2 := (sq_abs _).symm
      _ ≤ _ := by gcongr
  have := h eQ eQ norm_eQ norm_eQ
  have := h eQ eE norm_eQ norm_eE
  have := h eE eQ norm_eE norm_eQ
  have := h eE eE norm_eE norm_eE
  linarith

theorem norm_sq_le_four_eucJet2 {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    ‖iteratedFDeriv ℝ 2 f z‖ ^ 2 ≤ 4 * eucJet2 f z := by
  rw [eucJet2_eq hf]
  set B := iteratedFDeriv ℝ 2 f z with hB
  set L2 := fderiv ℝ (fderiv ℝ f) z with hL2
  have hb : ∀ a b : Plane, B ![a, b] = L2 a b := fun a b => by
    rw [hB, iteratedFDeriv_two_apply]; rfl
  have hdec : ∀ x : Plane, x = x.1 • eQ + x.2 • eE := fun x => by ext <;> simp [eQ, eE]
  have hexp : ∀ x y : Plane, L2 x y = x.1 * y.1 * L2 eQ eQ + x.1 * y.2 * L2 eQ eE +
      x.2 * y.1 * L2 eE eQ + x.2 * y.2 * L2 eE eE := by
    intro x y
    conv_lhs => rw [hdec x, hdec y]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  simp only [hb]
  have hnorm : ‖B‖ ≤ |L2 eQ eQ| + |L2 eQ eE| + |L2 eE eQ| + |L2 eE eE| := by
    refine B.opNorm_le_bound (by positivity) fun m => ?_
    have h0 : |(m 0).1| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 0)
    have h0' : |(m 0).2| ≤ ‖m 0‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 0)
    have h1 : |(m 1).1| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_fst_le (m 1)
    have h1' : |(m 1).2| ≤ ‖m 1‖ := by simpa [Real.norm_eq_abs] using norm_snd_le (m 1)
    have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
    rw [hm, hb, hexp, Fin.prod_univ_two, Real.norm_eq_abs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hp : ∀ (u v : ℝ) (p q : ℝ), |u| ≤ p → |v| ≤ q → ∀ w : ℝ, |u * v * w| ≤ p * q * |w| := by
      intro u v p q hu hv w
      have hp0 : 0 ≤ p := (abs_nonneg u).trans hu
      rw [abs_mul, abs_mul]
      gcongr
    have e1 := hp _ _ _ _ h0 h1 (L2 eQ eQ)
    have e2 := hp _ _ _ _ h0 h1' (L2 eQ eE)
    have e3 := hp _ _ _ _ h0' h1 (L2 eE eQ)
    have e4 := hp _ _ _ _ h0' h1' (L2 eE eE)
    calc _ ≤ |(m 0).1 * (m 1).1 * L2 eQ eQ| + |(m 0).1 * (m 1).2 * L2 eQ eE| +
          |(m 0).2 * (m 1).1 * L2 eE eQ| + |(m 0).2 * (m 1).2 * L2 eE eE| := by
          refine (abs_add_le _ _).trans ?_
          refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by nlinarith [e1, e2, e3, e4]
  have h0 : 0 ≤ ‖B‖ := norm_nonneg _
  have : ‖B‖ ^ 2 ≤ (|L2 eQ eQ| + |L2 eQ eE| + |L2 eE eQ| + |L2 eE eE|) ^ 2 := by gcongr
  nlinarith [sq_abs (L2 eQ eQ), sq_abs (L2 eQ eE), sq_abs (L2 eE eQ), sq_abs (L2 eE eE),
    sq_nonneg (|L2 eQ eQ| - |L2 eQ eE|), sq_nonneg (|L2 eQ eQ| - |L2 eE eQ|),
    sq_nonneg (|L2 eQ eQ| - |L2 eE eE|), sq_nonneg (|L2 eQ eE| - |L2 eE eQ|),
    sq_nonneg (|L2 eQ eE| - |L2 eE eE|), sq_nonneg (|L2 eE eQ| - |L2 eE eE|)]

theorem eucJetN_le_norm_sq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Plane) :
    eucJetN j f z ≤ 4 * ‖iteratedFDeriv ℝ j f z‖ ^ 2 := by
  unfold eucJetN
  split_ifs with h1 h2
  · subst h1
    have := eucJet1_le_norm_sq hf z
    nlinarith [sq_nonneg ‖iteratedFDeriv ℝ 1 f z‖]
  · subst h2
    exact eucJet2_le_norm_sq hf z
  · nlinarith [sq_nonneg ‖iteratedFDeriv ℝ j f z‖]

theorem norm_sq_le_eucJetN {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j f z‖ ^ 2 ≤ 4 * eucJetN j f z := by
  unfold eucJetN
  split_ifs with h1 h2
  · subst h1
    have := norm_sq_le_two_eucJet1 hf z
    nlinarith [eucJet1_nonneg f z]
  · subst h2
    exact norm_sq_le_four_eucJet2 hf z
  · nlinarith [sq_nonneg ‖iteratedFDeriv ℝ j f z‖]

theorem continuous_iter_apply {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (m : Fin j → Plane) :
    Continuous fun z => iteratedFDeriv ℝ j f z m :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Plane) ℝ m).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem eucJet1_continuous {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (eucJet1 f) := by
  have : eucJet1 f = fun z => (iteratedFDeriv ℝ 1 f z ![eQ]) ^ 2 + (iteratedFDeriv ℝ 1 f z ![eE]) ^ 2 :=
    funext (eucJet1_eq hf)
  rw [this]
  exact ((continuous_iter_apply hf 1 _).pow 2).add ((continuous_iter_apply hf 1 _).pow 2)

theorem eucJet2_continuous {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (eucJet2 f) := by
  have : eucJet2 f = fun z => (iteratedFDeriv ℝ 2 f z ![eQ, eQ]) ^ 2 +
      (iteratedFDeriv ℝ 2 f z ![eQ, eE]) ^ 2 + (iteratedFDeriv ℝ 2 f z ![eE, eQ]) ^ 2 +
      (iteratedFDeriv ℝ 2 f z ![eE, eE]) ^ 2 := funext (eucJet2_eq hf)
  rw [this]
  exact ((((continuous_iter_apply hf 2 _).pow 2).add ((continuous_iter_apply hf 2 _).pow 2)).add
    ((continuous_iter_apply hf 2 _).pow 2)).add ((continuous_iter_apply hf 2 _).pow 2)

theorem eucJetN_continuous {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    Continuous (eucJetN j f) := by
  unfold eucJetN
  split_ifs
  · exact eucJet1_continuous hf
  · exact eucJet2_continuous hf
  · exact (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2

end UnforcedLeray.Short.PartI
