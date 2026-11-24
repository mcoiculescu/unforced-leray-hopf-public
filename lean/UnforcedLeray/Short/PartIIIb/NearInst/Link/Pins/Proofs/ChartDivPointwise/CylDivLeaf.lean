import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.UVDerivLeaf

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The complex coercion of a real function has the coerced real directional derivative. -/
theorem cylDiv_cplx (G : ℝ × Space → ℝ) (x0 : ℝ × Space) (hG : DifferentiableAt ℝ G x0)
    (w : ℝ × Space) :
    fderiv ℝ (fun x => ((G x : ℝ) : ℂ)) x0 w = ((fderiv ℝ G x0 w : ℝ) : ℂ) := by
  have e : (fun x => ((G x : ℝ) : ℂ)) = (Complex.ofRealCLM ∘ G) := by
    funext x; simp
  have h : HasFDerivAt (Complex.ofRealCLM ∘ G) (Complex.ofRealCLM.comp (fderiv ℝ G x0)) x0 :=
    Complex.ofRealCLM.hasFDerivAt.comp x0 hG.hasFDerivAt
  rw [e, h.fderiv]
  simp

/-- Directional derivative of a function of the `y`-component only. -/
theorem cylDiv_snd (τ : ℝ) (y : Space) (g : Space → ℝ) (w : Space)
    (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (fun x : ℝ × Space => g x.2) (τ, y) (0, w) = fderiv ℝ g y w := by
  have h : HasFDerivAt (fun x : ℝ × Space => g x.2)
      ((fderiv ℝ g y).comp (ContinuousLinearMap.snd ℝ ℝ Space)) (τ, y) :=
    hg.hasFDerivAt.comp (τ, y) hasFDerivAt_snd
  rw [h.fderiv]
  simp

theorem cylDivLeaf : CylDivLeaf := by
  intro τ y hy a b c d aρ az bρ bz cρ cz dρ dz ha hb hc hd i
  obtain ⟨ha0, haw⟩ := ha
  obtain ⟨hb0, hbw⟩ := hb
  obtain ⟨hc0, hcw⟩ := hc
  obtain ⟨hd0, hdw⟩ := hd
  obtain ⟨hu0, hv0, huw, hvw⟩ := uVDerivLeaf y hy
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ × Space → ℝ, ∀ x, U x = x.2 0 / hRad x.2 :=
    ⟨fun x => x.2 0 / hRad x.2, fun x => rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ × Space → ℝ, ∀ x, V x = x.2 1 / hRad x.2 :=
    ⟨fun x => x.2 1 / hRad x.2, fun x => rfl⟩
  have hUfun : U = fun x : ℝ × Space => x.2 0 / hRad x.2 := funext hUdef
  have hVfun : V = fun x : ℝ × Space => x.2 1 / hRad x.2 := funext hVdef
  have hsndDiff : DifferentiableAt ℝ (fun x : ℝ × Space => x.2) (τ, y) :=
    (hasFDerivAt_snd).differentiableAt
  have hUd : DifferentiableAt ℝ U (τ, y) := by
    rw [hUfun]; exact hu0.comp (τ, y) hsndDiff
  have hVd : DifferentiableAt ℝ V (τ, y) := by
    rw [hVfun]; exact hv0.comp (τ, y) hsndDiff
  have hUw : ∀ w : Space, fderiv ℝ U (τ, y) (0, w) =
      (y 1 / hRad y) ^ 2 / hRad y * w 0 - (y 0 / hRad y) * (y 1 / hRad y) / hRad y * w 1 := by
    intro w; rw [hUfun]; exact (cylDiv_snd τ y _ w hu0).trans (huw w)
  have hVw : ∀ w : Space, fderiv ℝ V (τ, y) (0, w) =
      -((y 0 / hRad y) * (y 1 / hRad y) / hRad y) * w 0 + (y 0 / hRad y) ^ 2 / hRad y * w 1 := by
    intro w; rw [hVfun]; exact (cylDiv_snd τ y _ w hv0).trans (hvw w)
  have hA : ∀ w : Space, fderiv ℝ a (τ, y) (0, w) =
      (y 0 * w 0 + y 1 * w 1) / hRad y * aρ + w 2 * az := by
    intro w; rw [haw w, Axi.ϱD_apply, ← hRad_eq]
  have hB : ∀ w : Space, fderiv ℝ b (τ, y) (0, w) =
      (y 0 * w 0 + y 1 * w 1) / hRad y * bρ + w 2 * bz := by
    intro w; rw [hbw w, Axi.ϱD_apply, ← hRad_eq]
  have hC : ∀ w : Space, fderiv ℝ c (τ, y) (0, w) =
      (y 0 * w 0 + y 1 * w 1) / hRad y * cρ + w 2 * cz := by
    intro w; rw [hcw w, Axi.ϱD_apply, ← hRad_eq]
  have hD : ∀ w : Space, fderiv ℝ d (τ, y) (0, w) =
      (y 0 * w 0 + y 1 * w 1) / hRad y * dρ + w 2 * dz := by
    intro w; rw [hdw w, Axi.ϱD_apply, ← hRad_eq]
  have hM : ∀ x : ℝ × Space,
      cylFrame x.2 * !![a x, 0, b x; 0, d x, 0; b x, 0, c x] * (cylFrame x.2).transpose =
      !![U x * U x * a x + V x * V x * d x, (a x - d x) * U x * V x, b x * U x;
         (a x - d x) * U x * V x, V x * V x * a x + U x * U x * d x, b x * V x;
         b x * U x, b x * V x, c x] := by
    intro x
    simp only [hUdef, hVdef]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [cylFrame, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have huv : (y 0 / hRad y) ^ 2 + (y 1 / hRad y) ^ 2 = 1 := by
    have hne : hRad y ≠ 0 := hy.ne'
    have h2 : hRad y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      unfold hRad; exact Real.sq_sqrt (by positivity)
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hne), h2]
  have H00 := ((hUd.hasFDerivAt.fun_mul hUd.hasFDerivAt).fun_mul ha0.hasFDerivAt).fun_add
      ((hVd.hasFDerivAt.fun_mul hVd.hasFDerivAt).fun_mul hd0.hasFDerivAt)
  have H01 := ((ha0.hasFDerivAt.fun_sub hd0.hasFDerivAt).fun_mul hUd.hasFDerivAt).fun_mul
    hVd.hasFDerivAt
  have H02 := hb0.hasFDerivAt.fun_mul hUd.hasFDerivAt
  have H11 := ((hVd.hasFDerivAt.fun_mul hVd.hasFDerivAt).fun_mul ha0.hasFDerivAt).fun_add
      ((hUd.hasFDerivAt.fun_mul hUd.hasFDerivAt).fun_mul hd0.hasFDerivAt)
  have H12 := hb0.hasFDerivAt.fun_mul hVd.hasFDerivAt
  have n01 : ¬ ((0 : Fin 3) = 1) := by decide
  have n02 : ¬ ((0 : Fin 3) = 2) := by decide
  have n10 : ¬ ((1 : Fin 3) = 0) := by decide
  have n12 : ¬ ((1 : Fin 3) = 2) := by decide
  have n20 : ¬ ((2 : Fin 3) = 0) := by decide
  have n21 : ¬ ((2 : Fin 3) = 1) := by decide
  simp only [PhaseSpace.dy]
  simp only [hM]
  rw [Fin.sum_univ_three]
  fin_cases i
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.reduceFinMk]
    rw [cylDiv_cplx _ _ H00.differentiableAt, cylDiv_cplx _ _ H01.differentiableAt,
      cylDiv_cplx _ _ H02.differentiableAt, ← Complex.ofReal_add, ← Complex.ofReal_add,
      Complex.ofReal_inj, H00.fderiv, H01.fderiv, H02.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul,
      hUw, hVw, hA, hB, hC, hD, hUdef, hVdef]
    norm_num [coordinateVector, EuclideanSpace.single_apply, n01, n02, n10, n12, n20, n21]
    linear_combination (aρ * (y 0 / hRad y) + (a (τ, y) - d (τ, y)) * (y 0 / hRad y) / hRad y) * huv
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    rw [cylDiv_cplx _ _ H01.differentiableAt, cylDiv_cplx _ _ H11.differentiableAt,
      cylDiv_cplx _ _ H12.differentiableAt, ← Complex.ofReal_add, ← Complex.ofReal_add,
      Complex.ofReal_inj, H01.fderiv, H11.fderiv, H12.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul,
      hUw, hVw, hA, hB, hC, hD, hUdef, hVdef]
    norm_num [coordinateVector, EuclideanSpace.single_apply, n01, n02, n10, n12, n20, n21]
    linear_combination (aρ * (y 1 / hRad y) + (a (τ, y) - d (τ, y)) * (y 1 / hRad y) / hRad y) * huv
  · simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk]
    rw [cylDiv_cplx _ _ H02.differentiableAt, cylDiv_cplx _ _ H12.differentiableAt,
      cylDiv_cplx _ _ hc0, ← Complex.ofReal_add, ← Complex.ofReal_add,
      Complex.ofReal_inj, H02.fderiv, H12.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul,
      hUw, hVw, hA, hB, hC, hD, hUdef, hVdef]
    norm_num [coordinateVector, EuclideanSpace.single_apply, n01, n02, n10, n12, n20, n21]
    linear_combination (bρ + b (τ, y) / hRad y) * huv

end UnforcedLeray.Short.PartIIIb.NearInst
