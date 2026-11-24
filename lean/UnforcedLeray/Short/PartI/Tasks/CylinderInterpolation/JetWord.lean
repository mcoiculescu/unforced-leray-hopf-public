import UnforcedLeray.Short.PartI.Sub.T07

/-!
# Part I, task `PartI:T07`, target `cylJetWord_proof`: jets versus coordinate words

Source of record: `the November 2 reference manuscript`, lines 355-357 ("the
constants are independent of the period: ... `‖D^l f‖ ≤ ... ‖D^m f‖`"). The Prop is
`CylJetWord` in `Sub/T07.lean` (lines 180-183): for smooth `f` on the plane and every `l`, `z`,
(1) every coordinate derivative `derivWord w f z` with `|w| = l` is bounded by the jet norm
`‖iteratedFDeriv ℝ l f z‖`, and (2) the jet norm is bounded by the sum of the coordinate
derivatives over `wordsOfLength l`.

Proof. Let `e true = (1,0)` and `e false = (0,1)`. By induction on the length, the coordinate
derivative along a word is the jet on the basis vectors of its letters
(`cjw_word_formula`). Part (1) follows from `‖e b‖ = 1` and `le_opNorm`. Part (2) expands each
argument of the jet in the basis (`cjw_decomp`) and applies multilinearity
(`ContinuousMultilinearMap.map_sum`, `map_smul_univ`), then `opNorm_le_bound`.
-/

set_option autoImplicit false

open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The coordinate basis vector of a letter: `true` is `∂_q`, i.e. `(1,0)`; `false` is `∂_η`,
i.e. `(0,1)`. -/
def cjwE : Bool → ℝ × ℝ
  | true => (1, 0)
  | false => (0, 1)

theorem cjwE_norm (b : Bool) : ‖cjwE b‖ = 1 := by
  cases b <;> simp [cjwE, Prod.norm_def]

/-- Expansion of a point of the plane in the coordinate basis. -/
theorem cjw_decomp (x : ℝ × ℝ) :
    x = ∑ b : Bool, (if b then x.1 else x.2) • cjwE b := by
  rw [Fintype.sum_bool]
  ext <;> simp [cjwE]

/-- Prepending a letter: `derivWord (b :: w) h z = D(derivWord w h)(z) · e_b`. -/
theorem cjw_derivWord_cons {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (b : Bool) (w : List Bool)
    (z : ℝ × ℝ) :
    UnforcedLeray.B0151.derivWord (b :: w) h z =
      fderiv ℝ (UnforcedLeray.B0151.derivWord w h) z (cjwE b) := by
  have hd : Differentiable ℝ (UnforcedLeray.B0151.derivWord w h) :=
    (UnforcedLeray.B0151.contDiff_derivWord hh w).differentiable (by simp)
  cases b with
  | false =>
    show UnforcedLeray.GaussianVortex.partialY (UnforcedLeray.B0151.derivWord w h) z = _
    exact UnforcedLeray.B0151.partialY_eq_fderiv hd z
  | true =>
    show UnforcedLeray.GaussianVortex.partialX (UnforcedLeray.B0151.derivWord w h) z = _
    exact UnforcedLeray.B0151.partialX_eq_fderiv hd z

/-- The coordinate derivative along a word of length `n` is the `n`-th jet on the basis vectors
of its letters. -/
theorem cjw_word_formula (h : ℝ × ℝ → ℝ) (hh : ContDiff ℝ ∞ h) :
    ∀ (n : ℕ) (w : Fin n → Bool) (z : ℝ × ℝ),
      UnforcedLeray.B0151.derivWord (List.ofFn w) h z =
        iteratedFDeriv ℝ n h z (fun i => cjwE (w i)) := by
  intro n
  induction n with
  | zero =>
    intro w z
    simp [UnforcedLeray.B0151.derivWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro w z
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n h) :=
      hh.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    have hIH : UnforcedLeray.B0151.derivWord (List.ofFn fun i => w i.succ) h =
        fun y => iteratedFDeriv ℝ n h y (fun i => cjwE (w i.succ)) := by
      funext y
      exact ih (fun i => w i.succ) y
    have key := (hd z).iteratedFDeriv_succ_apply_left' (m := fun i => cjwE (w i))
    rw [List.ofFn_succ, cjw_derivWord_cons hh (w 0) (List.ofFn fun i => w i.succ) z, hIH]
    exact key.symm

/-- The jet norm is bounded by the sum of the coordinate derivatives over all words of length `l`
(conjunct 2 of `CylJetWord`). -/
theorem cjw_norm_le_sum (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (l : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ l f z‖ ≤ ∑ w ∈ wordsOfLength l, |UnforcedLeray.B0151.derivWord w f z| := by
  have hsum : ∑ w ∈ wordsOfLength l, |UnforcedLeray.B0151.derivWord w f z| =
      ∑ r : Fin l → Bool, |iteratedFDeriv ℝ l f z (fun i => cjwE (r i))| := by
    unfold wordsOfLength
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      show |UnforcedLeray.B0151.derivWord (List.ofFn r) f z| = _
      rw [cjw_word_formula f hf l r z]
    · intro x _ y _ hxy
      exact List.ofFn_injective hxy
  rw [hsum]
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun r _ => abs_nonneg _)) ?_
  intro m
  have hexp : iteratedFDeriv ℝ l f z m =
      ∑ r : Fin l → Bool, (∏ i, (if r i then (m i).1 else (m i).2)) *
        iteratedFDeriv ℝ l f z (fun i => cjwE (r i)) := by
    have h1 : iteratedFDeriv ℝ l f z m =
        iteratedFDeriv ℝ l f z (fun i => ∑ b : Bool, (if b then (m i).1 else (m i).2) • cjwE b) := by
      congr 1
      funext i
      exact cjw_decomp (m i)
    rw [h1, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    show iteratedFDeriv ℝ l f z (fun i => (if r i then (m i).1 else (m i).2) • cjwE (r i)) = _
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hbound : ∀ r : Fin l → Bool, |∏ i, (if r i then (m i).1 else (m i).2)| ≤ ∏ i, ‖m i‖ := by
    intro r
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
    split_ifs
    · rw [← Real.norm_eq_abs]
      exact norm_fst_le (m i)
    · rw [← Real.norm_eq_abs]
      exact norm_snd_le (m i)
  rw [hexp, Real.norm_eq_abs]
  calc |∑ r : Fin l → Bool, (∏ i, (if r i then (m i).1 else (m i).2)) *
          iteratedFDeriv ℝ l f z (fun i => cjwE (r i))|
      ≤ ∑ r : Fin l → Bool, |(∏ i, (if r i then (m i).1 else (m i).2)) *
          iteratedFDeriv ℝ l f z (fun i => cjwE (r i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin l → Bool, (∏ i, ‖m i‖) * |iteratedFDeriv ℝ l f z (fun i => cjwE (r i))| := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound r) (abs_nonneg _)
    _ = (∑ r : Fin l → Bool, |iteratedFDeriv ℝ l f z (fun i => cjwE (r i))|) *
          ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring

/-- **Target** `cylJetWord_proof`: jets versus coordinate words (`CylJetWord`, `Sub/T07.lean`). -/
theorem cylJetWord_proof : UnforcedLeray.Short.PartI.CylJetWord := by
  unfold UnforcedLeray.Short.PartI.CylJetWord
  intro f hf l z
  refine ⟨?_, ?_⟩
  · intro w hw
    subst hw
    have e1 := cjw_word_formula f hf w.length w.get z
    rw [List.ofFn_get] at e1
    show |UnforcedLeray.B0151.derivWord w f z| ≤ ‖iteratedFDeriv ℝ w.length f z‖
    rw [e1, ← Real.norm_eq_abs]
    have h1 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ w.length f z)
      (fun i => cjwE (w.get i))
    have h2 : ∏ i, ‖cjwE (w.get i)‖ = 1 := by simp [cjwE_norm]
    rw [h2, mul_one] at h1
    exact h1
  · exact cjw_norm_le_sum f hf l z

end UnforcedLeray.Short.PartI
