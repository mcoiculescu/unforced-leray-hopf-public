import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: generic algebra of the static energy inequality

Source of record: `the November 2 reference manuscript` lines 3060-3071 (the
energies `E_j` and the differentiated weighted energy).  Proved facts used by `Fried.lean`,
`Transport.lean`, `Assembly.lean` and offered to the drafters of the leaves:

* calculus of words on smooth fields: `st_contDiff_adjSpatial`, linearity (`st_adjSpatial_add`,
  `_sub`, `_neg`, `_const_mul`, `_sum2`), `st_adjSpatial_append`, periodicity;
* the real inner product `ipX`: linearity, symmetry, `ipX f f = ‖f‖²`, Cauchy-Schwarz;
* words: `st_sum_wordsLE_succ` (each word of length `1..j+1` is `l :: w'`, `|w'| ≤ j`, once),
  monotonicity of `wordsLE` and `cellEnergy`;
* the Leibniz splittings `stSplits` and the generic word Leibniz rule `st_word_leibniz` for an
  operator `B(a, f)` with the derivation rule `∂_j B(a, f) = B(∂_j a, f) + B(a, ∂_j f)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Calculus of `pdCx` and `adjSpatial` on smooth fields -/

theorem st_contDiff_pdCx {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (l : Fin 2) :
    ContDiff ℝ ∞ (pdCx l F) := by
  unfold pdCx
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem st_contDiff_adjSpatial {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ∀ w : List (Fin 2), ContDiff ℝ ∞ (adjSpatial w F)
  | [] => hF
  | l :: w => st_contDiff_pdCx (st_contDiff_adjSpatial hF w) l

theorem st_differentiable {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) : Differentiable ℝ F :=
  hF.differentiable (by simp)

theorem st_pdCx_add {F H : ℝ × ℝ → ℂ} (hF : Differentiable ℝ F) (hH : Differentiable ℝ H)
    (l : Fin 2) : pdCx l (fun x => F x + H x) = fun x => pdCx l F x + pdCx l H x := by
  funext x
  simp only [pdCx, fderiv_fun_add (hF x) (hH x), ContinuousLinearMap.add_apply]

theorem st_pdCx_sub {F H : ℝ × ℝ → ℂ} (hF : Differentiable ℝ F) (hH : Differentiable ℝ H)
    (l : Fin 2) : pdCx l (fun x => F x - H x) = fun x => pdCx l F x - pdCx l H x := by
  funext x
  simp only [pdCx, fderiv_fun_sub (hF x) (hH x), ContinuousLinearMap.sub_apply]

theorem st_pdCx_neg (F : ℝ × ℝ → ℂ) (l : Fin 2) :
    pdCx l (fun x => -F x) = fun x => -pdCx l F x := by
  funext x
  simp only [pdCx, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

theorem st_pdCx_const_mul (a : ℂ) {F : ℝ × ℝ → ℂ} (hF : Differentiable ℝ F) (l : Fin 2) :
    pdCx l (fun x => a * F x) = fun x => a * pdCx l F x := by
  funext x
  simp only [pdCx, fderiv_const_mul (hF x) a, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem st_adjSpatial_add {F H : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) :
    ∀ w : List (Fin 2),
      adjSpatial w (fun x => F x + H x) = fun x => adjSpatial w F x + adjSpatial w H x
  | [] => rfl
  | l :: w => by
    show pdCx l (adjSpatial w (fun x => F x + H x)) =
      fun x => pdCx l (adjSpatial w F) x + pdCx l (adjSpatial w H) x
    rw [st_adjSpatial_add hF hH w]
    exact st_pdCx_add (st_differentiable (st_contDiff_adjSpatial hF w))
      (st_differentiable (st_contDiff_adjSpatial hH w)) l

theorem st_adjSpatial_sub {F H : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) :
    ∀ w : List (Fin 2),
      adjSpatial w (fun x => F x - H x) = fun x => adjSpatial w F x - adjSpatial w H x
  | [] => rfl
  | l :: w => by
    show pdCx l (adjSpatial w (fun x => F x - H x)) =
      fun x => pdCx l (adjSpatial w F) x - pdCx l (adjSpatial w H) x
    rw [st_adjSpatial_sub hF hH w]
    exact st_pdCx_sub (st_differentiable (st_contDiff_adjSpatial hF w))
      (st_differentiable (st_contDiff_adjSpatial hH w)) l

theorem st_adjSpatial_neg (F : ℝ × ℝ → ℂ) :
    ∀ w : List (Fin 2), adjSpatial w (fun x => -F x) = fun x => -adjSpatial w F x
  | [] => rfl
  | l :: w => by
    show pdCx l (adjSpatial w (fun x => -F x)) = fun x => -pdCx l (adjSpatial w F) x
    rw [st_adjSpatial_neg F w]
    exact st_pdCx_neg _ l

theorem st_adjSpatial_const_mul (a : ℂ) {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ∀ w : List (Fin 2), adjSpatial w (fun x => a * F x) = fun x => a * adjSpatial w F x
  | [] => rfl
  | l :: w => by
    show pdCx l (adjSpatial w (fun x => a * F x)) = fun x => a * pdCx l (adjSpatial w F) x
    rw [st_adjSpatial_const_mul a hF w]
    exact st_pdCx_const_mul a (st_differentiable (st_contDiff_adjSpatial hF w)) l

theorem st_adjSpatial_sum2 {F : Fin 2 → ℝ × ℝ → ℂ} (hF : ∀ l, ContDiff ℝ ∞ (F l))
    (w : List (Fin 2)) :
    adjSpatial w (fun x => ∑ l : Fin 2, F l x) = fun x => ∑ l : Fin 2, adjSpatial w (F l) x := by
  simp only [Fin.sum_univ_two]
  exact st_adjSpatial_add (hF 0) (hF 1) w

theorem st_adjSpatial_append (F : ℝ × ℝ → ℂ) :
    ∀ w u : List (Fin 2), adjSpatial (w ++ u) F = adjSpatial w (adjSpatial u F)
  | [], _ => rfl
  | l :: w, u => by
    show pdCx l (adjSpatial (w ++ u) F) = pdCx l (adjSpatial w (adjSpatial u F))
    rw [st_adjSpatial_append F w u]

theorem st_pdCx_periodic {c : ℝ} {F : ℝ × ℝ → ℂ} (hF : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x)
    (l : Fin 2) : ∀ x : ℝ × ℝ, pdCx l F (x.1 + c, x.2) = pdCx l F x := by
  have hfun : (fun y : ℝ × ℝ => F (y + ((c, 0) : ℝ × ℝ))) = F := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hF y
  intro x
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := x) ((c, 0) : ℝ × ℝ)
  rw [hfun] at h
  have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
  unfold pdCx
  rw [h, hx]

theorem st_adjSpatial_periodic {c : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) :
    ∀ (w : List (Fin 2)) (x : ℝ × ℝ), adjSpatial w F (x.1 + c, x.2) = adjSpatial w F x
  | [] => hF
  | l :: w => st_pdCx_periodic (st_adjSpatial_periodic hF w) l

/-! ## The real inner product of `X_{-m,c}` -/

theorem st_integrable_mul_conj {c m : ℝ} {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hg : MemLp g 2 (B0579.cellMeasure c (-m))) :
    Integrable (fun x => f x * (starRingEnd ℂ) (g x)) (B0579.cellMeasure c (-m)) := by
  have hg' : MemLp (fun x => (starRingEnd ℂ) (g x)) 2 (B0579.cellMeasure c (-m)) := hg.star
  exact hf.integrable_mul hg'

theorem st_ipX_add_right {c m : ℝ} {f g h : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hg : MemLp g 2 (B0579.cellMeasure c (-m)))
    (hh : MemLp h 2 (B0579.cellMeasure c (-m))) :
    ipX c m f (fun x => g x + h x) = ipX c m f g + ipX c m f h := by
  unfold ipX
  rw [← Complex.add_re, ← integral_add (st_integrable_mul_conj hf hg)
    (st_integrable_mul_conj hf hh)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_add, mul_add]

theorem st_ipX_sub_right {c m : ℝ} {f g h : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hg : MemLp g 2 (B0579.cellMeasure c (-m)))
    (hh : MemLp h 2 (B0579.cellMeasure c (-m))) :
    ipX c m f (fun x => g x - h x) = ipX c m f g - ipX c m f h := by
  unfold ipX
  rw [← Complex.sub_re, ← integral_sub (st_integrable_mul_conj hf hg)
    (st_integrable_mul_conj hf hh)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_sub, mul_sub]

theorem st_ipX_neg_right (c m : ℝ) (f g : ℝ × ℝ → ℂ) :
    ipX c m f (fun x => -g x) = -ipX c m f g := by
  unfold ipX
  rw [← Complex.neg_re, ← integral_neg]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_neg, mul_neg]

theorem st_ipX_real_mul_right (c m r : ℝ) (f g : ℝ × ℝ → ℂ) :
    ipX c m f (fun x => (r : ℂ) * g x) = r * ipX c m f g := by
  unfold ipX
  have e : (fun x => f x * (starRingEnd ℂ) ((r : ℂ) * g x)) =
      fun x => (r : ℂ) * (f x * (starRingEnd ℂ) (g x)) := by
    funext x
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [e, integral_const_mul, Complex.re_ofReal_mul]

theorem st_ipX_comm (c m : ℝ) (f g : ℝ × ℝ → ℂ) : ipX c m f g = ipX c m g f := by
  unfold ipX
  have e : (fun x => g x * (starRingEnd ℂ) (f x)) =
      fun x => (starRingEnd ℂ) (f x * (starRingEnd ℂ) (g x)) := by
    funext x
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [e, integral_conj, Complex.conj_re]

/-- `‖f‖²_{X_{-m,c}} = ∫ |f|²`. -/
theorem st_xNorm_toReal_sq {c m : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    (xNorm c (-m) f).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) := by
  unfold xNorm
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have h0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) :=
    integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _)]
  have h := Real.rpow_inv_natCast_pow h0 (n := 2) (by norm_num)
  simpa using h

theorem st_ipX_self {c m : ℝ} {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    ipX c m f f = (xNorm c (-m) f).toReal ^ 2 := by
  rw [st_xNorm_toReal_sq hf]
  unfold ipX
  have e : (fun x => f x * (starRingEnd ℂ) (f x)) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [RCLike.mul_conj]
    push_cast
    rfl
  rw [e, integral_complex_ofReal, Complex.ofReal_re]

/-- `(∫ ‖f‖²)^{1/2} = ‖f‖_{X_{-m,c}}`. -/
theorem st_integral_sq_rpow {c m : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m))) ^ (1 / (2 : ℝ)) =
      (xNorm c (-m) f).toReal := by
  have h0 : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) :=
    integral_nonneg fun x => by positivity
  have hx : 0 ≤ (xNorm c (-m) f).toReal := ENNReal.toReal_nonneg
  have e : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) = (xNorm c (-m) f).toReal ^ 2 := by
    rw [st_xNorm_toReal_sq hf]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    exact Real.rpow_two _
  rw [e, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- Cauchy-Schwarz in `X_{-m,c}`: `|Re⟨f, g⟩| ≤ ‖f‖ ‖g‖`. -/
theorem st_abs_ipX_le {c m : ℝ} {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure c (-m)))
    (hg : MemLp g 2 (B0579.cellMeasure c (-m))) :
    |ipX c m f g| ≤ (xNorm c (-m) f).toReal * (xNorm c (-m) g).toReal := by
  unfold ipX
  have h1 := Complex.abs_re_le_norm (∫ x, f x * (starRingEnd ℂ) (g x) ∂(B0579.cellMeasure c (-m)))
  have h2 := norm_integral_le_integral_norm (μ := B0579.cellMeasure c (-m))
    (fun x => f x * (starRingEnd ℂ) (g x))
  have e : (fun x => ‖f x * (starRingEnd ℂ) (g x)‖) = fun x => ‖f x‖ * ‖g x‖ := by
    funext x
    rw [norm_mul, RCLike.norm_conj]
  rw [e] at h2
  have hfn : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) (B0579.cellMeasure c (-m)) := by
    rw [ENNReal.ofReal_ofNat]; exact hf.norm
  have hgn : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) (B0579.cellMeasure c (-m)) := by
    rw [ENNReal.ofReal_ofNat]; exact hg.norm
  have h3 := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun x => norm_nonneg (f x)) (ae_of_all _ fun x => norm_nonneg (g x)) hfn hgn
  rw [st_integral_sq_rpow hf, st_integral_sq_rpow hg] at h3
  linarith

/-! ## Words -/

theorem st_sum_wordsLE_succ (f : List (Fin 2) → ℝ) (j : ℕ) :
    ∑ u ∈ wordsLE (j + 1), f u = f [] + ∑ w ∈ wordsLE j, ∑ l : Fin 2, f (l :: w) := by
  have hnot : ([] : List (Fin 2)) ∉
      ((Finset.univ : Finset (Fin 2)) ×ˢ wordsLE j).image fun p => p.1 :: p.2 := by
    simp
  have hinj : Set.InjOn (fun p : Fin 2 × List (Fin 2) => p.1 :: p.2)
      ↑((Finset.univ : Finset (Fin 2)) ×ˢ wordsLE j) := by
    intro p _ q _ h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  show ∑ u ∈ insert [] (((Finset.univ : Finset (Fin 2)) ×ˢ wordsLE j).image
      fun p => p.1 :: p.2), f u = _
  rw [Finset.sum_insert hnot, Finset.sum_image hinj, Finset.sum_product, Finset.sum_comm]

theorem st_wordsLE_mono {i j : ℕ} (h : i ≤ j) : wordsLE i ⊆ wordsLE j := by
  intro w hw
  exact mem_wordsLE.2 ((mem_wordsLE.1 hw).trans h)

theorem st_cellEnergy_mono (c m : ℝ) {i j : ℕ} (h : i ≤ j) (F : ℝ × ℝ → ℂ) :
    cellEnergy c m i F ≤ cellEnergy c m j F :=
  Finset.sum_le_sum_of_subset_of_nonneg (st_wordsLE_mono h) fun _ _ _ => sq_nonneg _

theorem st_cellEnergy_zero (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    cellEnergy c m 0 F = (xNorm c (-m) F).toReal ^ 2 := by
  simp [cellEnergy, wordsLE, adjSpatial]

/-! ## Leibniz splittings and the generic word Leibniz rule -/

theorem st_splits_length {w : List (Fin 2)} :
    ∀ p ∈ stSplits w, p.1.length + p.2.length = w.length := by
  induction w with
  | nil => intro p hp; simp [stSplits] at hp; simp [hp]
  | cons j w ih =>
    intro p hp
    simp only [stSplits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    have := ih q hq
    rcases hpq with rfl | rfl <;> simp <;> omega

theorem st_splits_length_le {w : List (Fin 2)} {p : List (Fin 2) × List (Fin 2)}
    (hp : p ∈ stSplits w) : p.1.length ≤ w.length ∧ p.2.length ≤ w.length := by
  have := st_splits_length p hp
  omega

theorem st_splits_card (w : List (Fin 2)) : (stSplits w).length = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [stSplits, List.length_flatMap, List.length_cons, List.length_nil, zero_add,
      List.map_const', List.sum_replicate, smul_eq_mul, ih, pow_succ]

/-- The first splitting of `w` is `([], w)`; all the others have a nonempty first part. -/
theorem st_splits_cons_head (w : List (Fin 2)) : ∃ T : List (List (Fin 2) × List (Fin 2)),
    stSplits w = ([], w) :: T ∧ ∀ p ∈ T, 1 ≤ p.1.length := by
  induction w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons j w ih =>
    obtain ⟨T, hT, hT1⟩ := ih
    refine ⟨([j], w) :: T.flatMap (fun p => [(p.1, j :: p.2), (j :: p.1, p.2)]), ?_, ?_⟩
    · simp only [stSplits, hT, List.flatMap_cons, List.cons_append, List.nil_append]
    · intro p hp
      simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | ⟨q, hq, hpq⟩
      · simp
      · have := hT1 q hq
        rcases hpq with rfl | rfl <;> simp <;> omega

theorem st_differentiable_list_sum {ι : Type*} (L : List ι) (B : ι → ℝ × ℝ → ℂ)
    (hB : ∀ i ∈ L, Differentiable ℝ (B i)) :
    Differentiable ℝ (fun x => (L.map fun i => B i x).sum) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hB i (by simp)).add (ih fun i' hi' => hB i' (by simp [hi']))

theorem st_pdCx_list_sum {ι : Type*} (L : List ι) (B : ι → ℝ × ℝ → ℂ)
    (hB : ∀ i ∈ L, Differentiable ℝ (B i)) (l : Fin 2) :
    pdCx l (fun x => (L.map fun i => B i x).sum) = fun x => (L.map fun i => pdCx l (B i) x).sum := by
  induction L with
  | nil =>
    funext x
    simp [pdCx]
  | cons i L ih =>
    have hi : Differentiable ℝ (B i) := hB i (by simp)
    have hL : ∀ i ∈ L, Differentiable ℝ (B i) := fun i' hi' => hB i' (by simp [hi'])
    simp only [List.map_cons, List.sum_cons]
    rw [st_pdCx_add hi (st_differentiable_list_sum L B hL), ih hL]

theorem st_flatMap_sum (j : Fin 2) (L : List (List (Fin 2) × List (Fin 2)))
    (g : List (Fin 2) × List (Fin 2) → ℂ) :
    ((L.flatMap fun p => [(p.1, j :: p.2), (j :: p.1, p.2)]).map g).sum =
      (L.map fun p => g (j :: p.1, p.2) + g (p.1, j :: p.2)).sum := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ih]
    ring

/-- **The word Leibniz rule.**  For an operator `B(a, f)` (real coefficient fields `a`, complex
fields `f`) and a family `D` (`D (j :: u)` the derivative `∂_j` of `D u` for `|u| < k`) such that
every `B(∂^u a, D u')` with `|u'| ≤ k` is smooth and the derivation rule
`∂_j B(∂^u a, D u') = B(∂_j∂^u a, D u') + B(∂^u a, D (j :: u'))` holds for `|u'| < k`:
`∂^w B(a, D []) = Σ_{p ∈ stSplits w} B(∂^{p.1} a, D p.2)` for `|w| ≤ k`. -/
theorem st_word_leibniz (B : (Fin 2 → ℝ × ℝ → ℝ) → (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ)
    (a : Fin 2 → ℝ × ℝ → ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (k : ℕ)
    (hsm : ∀ u u' : List (Fin 2), u'.length ≤ k → ContDiff ℝ ∞ (B (stCoefWord u a) (D u')))
    (hder : ∀ (j : Fin 2) (u u' : List (Fin 2)), u'.length < k →
      pdCx j (B (stCoefWord u a) (D u')) =
        fun x => B (stCoefWord (j :: u) a) (D u') x + B (stCoefWord u a) (D (j :: u')) x) :
    ∀ w : List (Fin 2), w.length ≤ k →
      adjSpatial w (B a (D [])) =
        fun x => ((stSplits w).map fun p => B (stCoefWord p.1 a) (D p.2) x).sum
  | [], _ => by
    funext x
    simp only [adjSpatial, stSplits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rfl
  | j :: w, hw => by
    have hw' : w.length < k := by simpa using hw
    show pdCx j (adjSpatial w (B a (D []))) = _
    rw [st_word_leibniz B a D k hsm hder w hw'.le]
    rw [st_pdCx_list_sum (stSplits w) (fun p => B (stCoefWord p.1 a) (D p.2))
      (fun p hp => st_differentiable (hsm p.1 p.2 ((st_splits_length_le hp).2.trans hw'.le))) j]
    funext x
    have e : ((stSplits w).map fun p => pdCx j (B (stCoefWord p.1 a) (D p.2)) x) =
        ((stSplits w).map fun p => B (stCoefWord (j :: p.1) a) (D p.2) x +
          B (stCoefWord p.1 a) (D (j :: p.2)) x) := by
      refine List.map_congr_left fun p hp => ?_
      rw [hder j p.1 p.2 (lt_of_le_of_lt (st_splits_length_le hp).2 hw')]
    rw [e]
    show _ = ((stSplits (j :: w)).map fun p => B (stCoefWord p.1 a) (D p.2) x).sum
    simp only [stSplits]
    rw [st_flatMap_sum j (stSplits w) (fun p => B (stCoefWord p.1 a) (D p.2) x)]

end UnforcedLeray.Short.IIIa
