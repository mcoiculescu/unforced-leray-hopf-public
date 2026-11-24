import UnforcedLeray.Units.B0062.Flow
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# B0062 helper: the weak chain rule for smooth area-preserving diffeomorphisms

Helper file of blueprint unit **B0062** (`paper/main.tex` lines 1228–1237, label
`eq:st18-t00051`): "The chain rule gives `‖T(t)‖_{H^j_M → H^j_M} ≤ C_j(1+|t|)^j`"
(`paper/main.tex:1233`). The manuscript applies the chain rule to distributional derivatives;
this file proves the first-order distributional chain rule for composition with a smooth
diffeomorphism `Φ` with smooth inverse `Ψ` that preserves Lebesgue measure (`SmoothMP`):

* `hasWeakDeriv_comp`: if `H, ∂₁H, ∂₂H ∈ L¹_loc`, then
  `∂_v (H ∘ Φ) = Re(DΦ v) (∂₁H) ∘ Φ + Im(DΦ v) (∂₂H) ∘ Φ` weakly.
  Proof: change variables by `Φ`, write `(∂_v φ) ∘ Ψ = a · ∇(φ ∘ Ψ)` with `a = (DΦ v) ∘ Ψ`,
  and use `div a = 0`, which follows from area preservation (`div_free_ae`).
* `hasWeakDeriv_mul_smooth`: Leibniz rule for a weak derivative times a smooth function.

Weak derivatives are those of `NonUniqueEuler.Sob` (`HasWeakDerivOn univ [v]`), the convention
of B0008.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal
open Set MeasureTheory NonUniqueEuler.Sob NonUniqueEuler.Sob.WeakDerivAux

namespace UnforcedLeray.B0062

/-- `Φ` is a smooth diffeomorphism of the plane with smooth inverse `Ψ`, preserving area. -/
structure SmoothMP (Φ Ψ : ℂ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  smooth_inv : ContDiff ℝ ∞ Ψ
  left : ∀ y, Ψ (Φ y) = y
  right : ∀ x, Φ (Ψ x) = x
  mp : MeasurePreserving Φ volume volume

namespace SmoothMP

variable {Φ Ψ : ℂ → ℂ}

/-- The homeomorphism `Φ`. -/
def homeo (h : SmoothMP Φ Ψ) : ℂ ≃ₜ ℂ where
  toFun := Φ
  invFun := Ψ
  left_inv := h.left
  right_inv := h.right
  continuous_toFun := h.smooth.continuous
  continuous_invFun := h.smooth_inv.continuous

theorem measurableEmbedding (h : SmoothMP Φ Ψ) : MeasurableEmbedding Φ :=
  h.homeo.isClosedEmbedding.measurableEmbedding

/-- Change of variables `∫ k(Φ y) dy = ∫ k(x) dx`. -/
theorem integral_comp (h : SmoothMP Φ Ψ) (k : ℂ → ℂ) : ∫ y, k (Φ y) = ∫ x, k x :=
  h.mp.integral_comp h.measurableEmbedding k

theorem locallyIntegrable_comp (h : SmoothMP Φ Ψ) {H : ℂ → ℂ} (hH : LocallyIntegrable H) :
    LocallyIntegrable (fun y => H (Φ y)) := by
  rw [locallyIntegrable_iff] at hH ⊢
  intro K hK
  have := (hH _ (hK.image h.smooth.continuous))
  exact (h.mp.integrableOn_image h.measurableEmbedding).1 this

theorem testFn_comp (h : SmoothMP Φ Ψ) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun y => φ (Φ y)) :=
  ⟨hφ.smooth.comp h.smooth, hφ.compact.comp_homeomorph h.homeo, subset_univ _⟩

theorem testFn_comp_inv (h : SmoothMP Φ Ψ) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun x => φ (Ψ x)) :=
  ⟨hφ.smooth.comp h.smooth_inv, hφ.compact.comp_homeomorph h.homeo.symm, subset_univ _⟩

/-- `DΨ(x) (DΦ(Ψ x) v) = v`. -/
theorem fderiv_inv_fderiv (h : SmoothMP Φ Ψ) (x v : ℂ) :
    fderiv ℝ Ψ x (fderiv ℝ Φ (Ψ x) v) = v := by
  have hΦd : DifferentiableAt ℝ Φ (Ψ x) := h.smooth.differentiable (by simp) _
  have hΨd : DifferentiableAt ℝ Ψ (Φ (Ψ x)) := h.smooth_inv.differentiable (by simp) _
  have hc := fderiv_comp (Ψ x) hΨd hΦd
  have hid : Ψ ∘ Φ = id := funext h.left
  rw [hid, fderiv_id, h.right] at hc
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hc
  simpa using this.symm

end SmoothMP

theorem dirDeriv_mul {a b : ℂ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (v x : ℂ) :
    dirDeriv v (fun y => a y * b y) x = dirDeriv v a x * b x + a x * dirDeriv v b x := by
  have hd : HasFDerivAt (fun y => a y * b y) (a x • fderiv ℝ b x + b x • fderiv ℝ a x) x :=
    (ha.differentiable (by simp) x).hasFDerivAt.mul (hb.differentiable (by simp) x).hasFDerivAt
  simp only [dirDeriv]
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem locallyIntegrable_cont_mul {b k : ℂ → ℂ} (hb : Continuous b) (hk : LocallyIntegrable k) :
    LocallyIntegrable (fun y => b y * k y) := by
  rw [← locallyIntegrableOn_univ] at hk ⊢
  exact hk.continuousOn_mul hb.continuousOn isClosed_univ.isLocallyClosed

theorem iterDirDeriv_single (v : ℂ) (φ : ℂ → ℂ) : iterDirDeriv [v] φ = dirDeriv v φ := rfl

/-- **Leibniz rule with a smooth factor**: `∂_v (c f) = (∂_v c) f + c ∂_v f` weakly. -/
theorem hasWeakDeriv_mul_smooth {f g c : ℂ → ℂ} (hf : LocallyIntegrable f)
    (hg : LocallyIntegrable g) (hc : ContDiff ℝ ∞ c) {v : ℂ}
    (h : HasWeakDerivOn univ [v] f g) :
    HasWeakDerivOn univ [v] (fun y => c y * f y) (fun y => dirDeriv v c y * f y + c y * g y) := by
  intro φ hφ
  have hcφ : IsTestFn univ (fun y => c y * φ y) :=
    ⟨hc.mul hφ.smooth, hφ.compact.mul_left, subset_univ _⟩
  have hdcφ : IsTestFn univ (fun y => dirDeriv v c y * φ y) :=
    ⟨(contDiff_dirDeriv hc v).mul hφ.smooth, hφ.compact.mul_left, subset_univ _⟩
  have hf' := hf.locallyIntegrableOn univ
  have hg' := hg.locallyIntegrableOn univ
  have e1 := h _ hcφ
  rw [iterDirDeriv_single] at e1 ⊢
  simp only [List.length_singleton, pow_one] at e1 ⊢
  have i1 := integrable_mul_testFn hf' (hcφ.dirDeriv v)
  have i2 := integrable_mul_testFn hf' hdcφ
  have i3 := integrable_mul_testFn hg' hcφ
  calc ∫ y, c y * f y * dirDeriv v φ y
      = ∫ y, (f y * dirDeriv v (fun y => c y * φ y) y - f y * (dirDeriv v c y * φ y)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [dirDeriv_mul hc hφ.smooth]
        ring
    _ = (-1 : ℂ) * (∫ y, g y * (c y * φ y)) - ∫ y, f y * (dirDeriv v c y * φ y) := by
        rw [integral_sub i1 i2, e1]
    _ = -1 * ∫ y, (dirDeriv v c y * f y + c y * g y) * φ y := by
        have : ∫ y, (dirDeriv v c y * f y + c y * g y) * φ y =
            (∫ y, f y * (dirDeriv v c y * φ y)) + ∫ y, g y * (c y * φ y) := by
          rw [← integral_add i2 i3]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only
          ring
        rw [this]
        ring

namespace SmoothMP

variable {Φ Ψ : ℂ → ℂ}

/-- The vector field `a = (DΦ v) ∘ Ψ` (pushforward of the constant field `v`), its components
`a₁ = Re a`, `a₂ = Im a` as complex functions. -/
def a1 (_h : SmoothMP Φ Ψ) (v : ℂ) (x : ℂ) : ℂ := ((fderiv ℝ Φ (Ψ x) v).re : ℂ)

def a2 (_h : SmoothMP Φ Ψ) (v : ℂ) (x : ℂ) : ℂ := ((fderiv ℝ Φ (Ψ x) v).im : ℂ)

theorem contDiff_fderiv_comp_apply (h : SmoothMP Φ Ψ) (v : ℂ) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ Φ (Ψ x) v) :=
  ((h.smooth.fderiv_right (m := ∞) (by simp)).comp h.smooth_inv).clm_apply contDiff_const

theorem contDiff_a1 (h : SmoothMP Φ Ψ) (v : ℂ) : ContDiff ℝ ∞ (h.a1 v) :=
  Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (h.contDiff_fderiv_comp_apply v))

theorem contDiff_a2 (h : SmoothMP Φ Ψ) (v : ℂ) : ContDiff ℝ ∞ (h.a2 v) :=
  Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp (h.contDiff_fderiv_comp_apply v))

/-- For any smooth `χ`, `Dχ(x)(a(x)) = a₁ ∂₁χ + a₂ ∂₂χ`. -/
theorem fderiv_apply_a (h : SmoothMP Φ Ψ) (v : ℂ) (χ : ℂ → ℂ) (x : ℂ) :
    fderiv ℝ χ x (fderiv ℝ Φ (Ψ x) v) = h.a1 v x * dirDeriv 1 χ x + h.a2 v x * dirDeriv Complex.I χ x := by
  rw [clm_apply_eq (fderiv ℝ χ x) (fderiv ℝ Φ (Ψ x) v), Complex.real_smul, Complex.real_smul]
  rfl

/-- `(∂_v φ)(Ψ x) = a₁ ∂₁(φ ∘ Ψ) + a₂ ∂₂(φ ∘ Ψ)`. -/
theorem dirDeriv_comp_inv (h : SmoothMP Φ Ψ) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (v x : ℂ) :
    dirDeriv v φ (Ψ x) = h.a1 v x * dirDeriv 1 (fun x => φ (Ψ x)) x +
      h.a2 v x * dirDeriv Complex.I (fun x => φ (Ψ x)) x := by
  rw [← h.fderiv_apply_a v]
  have hc : fderiv ℝ (fun x => φ (Ψ x)) x = (fderiv ℝ φ (Ψ x)).comp (fderiv ℝ Ψ x) :=
    fderiv_comp x (hφ.differentiable (by simp) _) (h.smooth_inv.differentiable (by simp) _)
  rw [hc, ContinuousLinearMap.comp_apply, h.fderiv_inv_fderiv]
  rfl

/-- The pushforward field `a` is divergence free (a.e.), by area preservation. -/
theorem div_free_ae (h : SmoothMP Φ Ψ) (v : ℂ) :
    ∀ᵐ x, x ∈ univ → dirDeriv 1 (h.a1 v) x + dirDeriv Complex.I (h.a2 v) x = 0 := by
  have hd1 := contDiff_dirDeriv (h.contDiff_a1 v) 1
  have hd2 := contDiff_dirDeriv (h.contDiff_a2 v) Complex.I
  have hdiv : Continuous fun x => dirDeriv 1 (h.a1 v) x + dirDeriv Complex.I (h.a2 v) x :=
    hd1.continuous.add hd2.continuous
  have key := ae_eq_of_integral_testFn isOpen_univ
    (hdiv.locallyIntegrable.locallyIntegrableOn univ)
    ((continuous_const : Continuous fun _ : ℂ => (0 : ℂ)).locallyIntegrable.locallyIntegrableOn univ)
    (fun χ hχ => ?_)
  · exact key
  have i1 := integrable_continuousOn_mul_testFn isOpen_univ hd1.continuous.continuousOn hχ
  have i2 := integrable_continuousOn_mul_testFn isOpen_univ hd2.continuous.continuousOn hχ
  have j1 := integrable_continuousOn_mul_testFn isOpen_univ (h.contDiff_a1 v).continuous.continuousOn
    (hχ.dirDeriv 1)
  have j2 := integrable_continuousOn_mul_testFn isOpen_univ (h.contDiff_a2 v).continuous.continuousOn
    (hχ.dirDeriv Complex.I)
  have p1 := integral_mul_dirDeriv isOpen_univ ((h.contDiff_a1 v).of_le (by simp)).contDiffOn hχ 1
  have p2 := integral_mul_dirDeriv isOpen_univ ((h.contDiff_a2 v).of_le (by simp)).contDiffOn hχ
    Complex.I
  -- the integral of `Dχ(a)` vanishes after the change of variables `x = Φ y`
  have hζ := h.testFn_comp hχ
  have hz := integral_mul_dirDeriv isOpen_univ (F := fun _ => (1 : ℂ)) contDiffOn_const hζ v
  have hzero : ∫ y, dirDeriv v (fun y => χ (Φ y)) y = 0 := by
    have e : dirDeriv v (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := by
      funext x
      simp [dirDeriv]
    simpa [e] using hz
  have hchain : ∀ y, dirDeriv v (fun y => χ (Φ y)) y = fderiv ℝ χ (Φ y) (fderiv ℝ Φ y v) := by
    intro y
    have hc : fderiv ℝ (fun y => χ (Φ y)) y = (fderiv ℝ χ (Φ y)).comp (fderiv ℝ Φ y) :=
      fderiv_comp y (hχ.smooth.differentiable (by simp) _) (h.smooth.differentiable (by simp) _)
    simp only [dirDeriv, hc, ContinuousLinearMap.comp_apply]
  have hcv : ∫ x, fderiv ℝ χ x (fderiv ℝ Φ (Ψ x) v) = 0 := by
    rw [← h.integral_comp (fun x => fderiv ℝ χ x (fderiv ℝ Φ (Ψ x) v))]
    simp only [h.left, ← hchain]
    exact hzero
  have hsplit : ∫ x, fderiv ℝ χ x (fderiv ℝ Φ (Ψ x) v) =
      (∫ x, h.a1 v x * dirDeriv 1 χ x) + ∫ x, h.a2 v x * dirDeriv Complex.I χ x := by
    rw [← integral_add j1 j2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => h.fderiv_apply_a v χ x)
  simp only [zero_mul, integral_zero]
  rw [show (fun x => (dirDeriv 1 (h.a1 v) x + dirDeriv Complex.I (h.a2 v) x) * χ x) =
      fun x => dirDeriv 1 (h.a1 v) x * χ x + dirDeriv Complex.I (h.a2 v) x * χ x from
      funext fun x => add_mul _ _ _, integral_add i1 i2]
  have : (∫ x, dirDeriv 1 (h.a1 v) x * χ x) + ∫ x, dirDeriv Complex.I (h.a2 v) x * χ x =
      -(∫ x, fderiv ℝ χ x (fderiv ℝ Φ (Ψ x) v)) := by
    rw [hsplit, p1, p2]
    ring
  rw [this, hcv, neg_zero]

/-- **First-order weak chain rule** for a smooth area-preserving diffeomorphism. -/
theorem hasWeakDeriv_comp (h : SmoothMP Φ Ψ) {H H1 H2 : ℂ → ℂ} (hH : LocallyIntegrable H)
    (hH1 : LocallyIntegrable H1) (hH2 : LocallyIntegrable H2)
    (d1 : HasWeakDerivOn univ [1] H H1) (d2 : HasWeakDerivOn univ [Complex.I] H H2) (v : ℂ) :
    HasWeakDerivOn univ [v] (fun y => H (Φ y))
      (fun y => ((fderiv ℝ Φ y v).re : ℂ) * H1 (Φ y) + ((fderiv ℝ Φ y v).im : ℂ) * H2 (Φ y)) := by
  intro φ hφ
  rw [iterDirDeriv_single]
  simp only [List.length_singleton, pow_one]
  set ψ : ℂ → ℂ := fun x => φ (Ψ x) with hψdef
  have hψ : IsTestFn univ ψ := h.testFn_comp_inv hφ
  have ht1 : IsTestFn univ (fun x => h.a1 v x * ψ x) :=
    ⟨(h.contDiff_a1 v).mul hψ.smooth, hψ.compact.mul_left, subset_univ _⟩
  have ht2 : IsTestFn univ (fun x => h.a2 v x * ψ x) :=
    ⟨(h.contDiff_a2 v).mul hψ.smooth, hψ.compact.mul_left, subset_univ _⟩
  have hHl := hH.locallyIntegrableOn univ
  have e1 := d1 _ ht1
  have e2 := d2 _ ht2
  rw [iterDirDeriv_single] at e1 e2
  simp only [List.length_singleton, pow_one] at e1 e2
  have i1 := integrable_mul_testFn hHl (ht1.dirDeriv 1)
  have i2 := integrable_mul_testFn hHl (ht2.dirDeriv Complex.I)
  have k1 := integrable_mul_testFn (hH1.locallyIntegrableOn univ) ht1
  have k2 := integrable_mul_testFn (hH2.locallyIntegrableOn univ) ht2
  have hdiv := h.div_free_ae v
  -- Step 1: change variables `y = Ψ x`.
  have s1 : ∫ y, H (Φ y) * dirDeriv v φ y = ∫ x, H x * dirDeriv v φ (Ψ x) := by
    rw [← h.integral_comp (fun x => H x * dirDeriv v φ (Ψ x))]
    simp only [h.left]
  -- Step 2: `(∂_v φ) ∘ Ψ = ∂₁(a₁ψ) + ∂₂(a₂ψ)` a.e. (divergence free).
  have s2 : ∫ x, H x * dirDeriv v φ (Ψ x) =
      ∫ x, (H x * dirDeriv 1 (fun x => h.a1 v x * ψ x) x +
        H x * dirDeriv Complex.I (fun x => h.a2 v x * ψ x) x) := by
    refine integral_congr_ae ?_
    filter_upwards [hdiv] with x hx
    have hx' := hx (mem_univ x)
    rw [h.dirDeriv_comp_inv hφ.smooth v x, dirDeriv_mul (h.contDiff_a1 v) hψ.smooth,
      dirDeriv_mul (h.contDiff_a2 v) hψ.smooth]
    have : dirDeriv 1 (h.a1 v) x * ψ x + dirDeriv Complex.I (h.a2 v) x * ψ x = 0 := by
      rw [← add_mul, hx', zero_mul]
    linear_combination (-H x) * this
  -- Step 3: weak derivatives of `H`.
  have s3 : ∫ x, (H x * dirDeriv 1 (fun x => h.a1 v x * ψ x) x +
        H x * dirDeriv Complex.I (fun x => h.a2 v x * ψ x) x) =
      -1 * ∫ x, (h.a1 v x * H1 x + h.a2 v x * H2 x) * ψ x := by
    rw [integral_add i1 i2, e1, e2, ← mul_add, ← integral_add k1 k2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  -- Step 4: change variables back.
  have s4 : ∫ x, (h.a1 v x * H1 x + h.a2 v x * H2 x) * ψ x =
      ∫ y, (((fderiv ℝ Φ y v).re : ℂ) * H1 (Φ y) + ((fderiv ℝ Φ y v).im : ℂ) * H2 (Φ y)) * φ y := by
    rw [← h.integral_comp (fun x => (h.a1 v x * H1 x + h.a2 v x * H2 x) * ψ x)]
    simp only [a1, a2, hψdef, h.left]
  rw [s1, s2, s3, s4]

end SmoothMP

end UnforcedLeray.B0062
