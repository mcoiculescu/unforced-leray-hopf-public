import UnforcedLeray.Short.PartI.Sub.T02_4

/-!
# Part I, task `PartI:T02/4`: comparison theorem `parabolicSechBarrier_of`

Source of record: `the November 2 reference manuscript`, lines 276-288 (comparison
for the vorticity equation with a bounded drift).  Conditional on `ParabolicMinPrinciple` and
`SechSupersolution` (both in `Sub/T02_4.lean`).

Route: for `ε > 0` the barrier is `pbF = B + Φ_ε` with `B = sechBarrier A K a`,
`Φ_ε = coshBarrier ε K a`.  The minimum principle applied to `B + Φ_ε ∓ ω` gives `|ω| ≤ B + Φ_ε`
on `[0,T)`; continuity gives the value at `T`; letting `ε → 0` gives the claim.
Helper names carry the prefix `pb`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The barrier `B + Φ_ε = sechBarrier A K a + coshBarrier ε K a`. -/
def pbF (A ε K a : ℝ) (t : ℝ) (w : Plane) : ℝ :=
  sechBarrier A K a t w + coshBarrier ε K a t w

/-! ### Smoothness of the barriers -/

theorem pbExpK_contDiff (K : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ × Plane => Real.exp (K * x.1)) :=
  Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)

theorem pbCoshA_contDiff (a : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ × Plane => Real.cosh (a * x.2.2)) := by
  have hl : ContDiff ℝ 2 (fun x : ℝ × Plane => a * x.2.2) :=
    (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ × Plane => a)).mul
      (contDiff_snd.comp contDiff_snd)
  exact Real.contDiff_cosh.comp hl

theorem pbF_contDiff (A ε K a : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ × Plane => pbF A ε K a x.1 x.2) := by
  have hA : ContDiff ℝ 2 (fun x : ℝ × Plane => A * Real.exp (K * x.1)) :=
    (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ × Plane => A)).mul (pbExpK_contDiff K)
  have hE : ContDiff ℝ 2 (fun x : ℝ × Plane => ε * Real.exp (K * x.1)) :=
    (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ × Plane => ε)).mul (pbExpK_contDiff K)
  have hinv : ContDiff ℝ 2 (fun x : ℝ × Plane => (Real.cosh (a * x.2.2))⁻¹) :=
    (pbCoshA_contDiff a).inv (fun x => (Real.cosh_pos _).ne')
  have hsech : ContDiff ℝ 2 (fun x : ℝ × Plane => sechBarrier A K a x.1 x.2) :=
    hA.mul hinv
  have hcosh : ContDiff ℝ 2 (fun x : ℝ × Plane => coshBarrier ε K a x.1 x.2) :=
    hE.mul (pbCoshA_contDiff a)
  exact hsech.add hcosh

/-- Slice of a `C²` function on `ℝ × Plane` at a fixed time. -/
theorem pb_slice_contDiff {G : ℝ × Plane → ℝ} (hG : ContDiff ℝ 2 G) (s : ℝ) :
    ContDiff ℝ 2 (fun w : Plane => G (s, w)) :=
  hG.comp ((contDiff_const : ContDiff ℝ 2 (fun _ : Plane => s)).prodMk contDiff_id)

/-- Slice at a fixed time of a function that is `C²` on `(0,T) × ℝ²`. -/
theorem pb_slice_contDiff_om {om : ℝ → Plane → ℝ} {T s : ℝ}
    (hC2 : ContDiffOn ℝ 2 (fun x : ℝ × Plane => om x.1 x.2) (Ioo 0 T ×ˢ univ))
    (hs : s ∈ Ioo 0 T) : ContDiff ℝ 2 (om s) := by
  have h2 : ContDiffOn ℝ 2 (fun w : Plane => (s, w)) univ :=
    ((contDiff_const : ContDiff ℝ 2 (fun _ : Plane => s)).prodMk contDiff_id).contDiffOn
  have h3 : ContDiffOn ℝ 2 (fun w : Plane => om s w) univ :=
    hC2.comp h2 (fun w _ => mk_mem_prod hs (mem_univ w))
  exact contDiffOn_univ.mp h3

/-- Time slice of a function differentiable at `(s, z)`. -/
theorem pb_tslice_diffAt {G : ℝ × Plane → ℝ} {s : ℝ} {z : Plane}
    (hG : DifferentiableAt ℝ G (s, z)) :
    DifferentiableAt ℝ (fun t : ℝ => G (t, z)) s := by
  have h : DifferentiableAt ℝ (fun t : ℝ => (t, z)) s := by fun_prop
  exact hG.comp s h

/-! ### Calculus helpers for the transport-diffusion operator -/

theorem pb_partialQ_eq_fderiv {f : Plane → ℝ} (hd : Differentiable ℝ f) (z : Plane) :
    Cyl.partialQ f z = fderiv ℝ f z (1, 0) := by
  have h0 : HasDerivAt (fun q : ℝ => (q, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have h1 : HasDerivAt (fun q : ℝ => f (q, z.2)) (fderiv ℝ f (z.1, z.2) (1, 0)) z.1 :=
    (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h0
  exact h1.deriv

theorem pb_partialEta_eq_fderiv {f : Plane → ℝ} (hd : Differentiable ℝ f) (z : Plane) :
    Cyl.partialEta f z = fderiv ℝ f z (0, 1) := by
  have h0 : HasDerivAt (fun η : ℝ => (z.1, η)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have h1 : HasDerivAt (fun η : ℝ => f (z.1, η)) (fderiv ℝ f (z.1, z.2) (0, 1)) z.2 :=
    (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h0
  exact h1.deriv

theorem pb_partialQ_differentiable {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (Cyl.partialQ f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : Cyl.partialQ f = fun w => fderiv ℝ f w (1, 0) :=
    funext fun w => pb_partialQ_eq_fderiv hd w
  rw [heq]
  exact hfd.clm_apply (differentiable_const _)

theorem pb_partialEta_differentiable {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (Cyl.partialEta f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : Cyl.partialEta f = fun w => fderiv ℝ f w (0, 1) :=
    funext fun w => pb_partialEta_eq_fderiv hd w
  rw [heq]
  exact hfd.clm_apply (differentiable_const _)

theorem pb_partialQ_fun (f g : Plane → ℝ) (σ : ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Cyl.partialQ (fun w => f w - σ * g w) = fun w => Cyl.partialQ f w - σ * Cyl.partialQ g w := by
  funext w
  have h1 : DifferentiableAt ℝ (fun q : ℝ => f (q, w.2)) w.1 := by fun_prop
  have h2 : DifferentiableAt ℝ (fun q : ℝ => g (q, w.2)) w.1 := by fun_prop
  have hC : HasDerivAt (fun q : ℝ => f (q, w.2) - σ * g (q, w.2))
      (deriv (fun q : ℝ => f (q, w.2)) w.1 - σ * deriv (fun q : ℝ => g (q, w.2)) w.1) w.1 :=
    h1.hasDerivAt.sub (h2.hasDerivAt.const_mul σ)
  exact hC.deriv

theorem pb_partialEta_fun (f g : Plane → ℝ) (σ : ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Cyl.partialEta (fun w => f w - σ * g w) = fun w => Cyl.partialEta f w - σ * Cyl.partialEta g w := by
  funext w
  have h1 : DifferentiableAt ℝ (fun η : ℝ => f (w.1, η)) w.2 := by fun_prop
  have h2 : DifferentiableAt ℝ (fun η : ℝ => g (w.1, η)) w.2 := by fun_prop
  have hC : HasDerivAt (fun η : ℝ => f (w.1, η) - σ * g (w.1, η))
      (deriv (fun η : ℝ => f (w.1, η)) w.2 - σ * deriv (fun η : ℝ => g (w.1, η)) w.2) w.2 :=
    h1.hasDerivAt.sub (h2.hasDerivAt.const_mul σ)
  exact hC.deriv

theorem pb_partialQ_pt (f g : Plane → ℝ) (σ : ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : Plane) :
    Cyl.partialQ (fun w => f w - σ * g w) z = Cyl.partialQ f z - σ * Cyl.partialQ g z :=
  congrFun (pb_partialQ_fun f g σ hf hg) z

theorem pb_partialEta_pt (f g : Plane → ℝ) (σ : ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : Plane) :
    Cyl.partialEta (fun w => f w - σ * g w) z = Cyl.partialEta f z - σ * Cyl.partialEta g z :=
  congrFun (pb_partialEta_fun f g σ hf hg) z

theorem pb_lapS_sub (f g : Plane → ℝ) (σ : ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (z : Plane) :
    Train.lapS (fun w => f w - σ * g w) z = Train.lapS f z - σ * Train.lapS g z := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  unfold Train.lapS
  rw [pb_partialQ_fun f g σ hfd hgd, pb_partialEta_fun f g σ hfd hgd]
  rw [pb_partialQ_fun _ _ σ (pb_partialQ_differentiable hf) (pb_partialQ_differentiable hg),
    pb_partialEta_fun _ _ σ (pb_partialEta_differentiable hf) (pb_partialEta_differentiable hg)]
  try dsimp only
  ring

theorem pb_vorticityOp_sub (ν : ℝ) (b : ℝ → Plane → Vec) (F G : ℝ → Plane → ℝ) (σ s : ℝ)
    (z : Plane)
    (hF : ContDiff ℝ 2 (F s)) (hG : ContDiff ℝ 2 (G s))
    (hFt : DifferentiableAt ℝ (fun t => F t z) s)
    (hGt : DifferentiableAt ℝ (fun t => G t z) s) :
    vorticityOp ν b (fun t w => F t w - σ * G t w) s z
      = vorticityOp ν b F s z - σ * vorticityOp ν b G s z := by
  have hFd : Differentiable ℝ (F s) := hF.differentiable (by norm_num)
  have hGd : Differentiable ℝ (G s) := hG.differentiable (by norm_num)
  have ht : deriv (fun t => F t z - σ * G t z) s
      = deriv (fun t => F t z) s - σ * deriv (fun t => G t z) s :=
    (hFt.hasDerivAt.sub (hGt.hasDerivAt.const_mul σ)).deriv
  unfold vorticityOp
  try dsimp only
  rw [ht, pb_partialQ_pt (F s) (G s) σ hFd hGd z, pb_partialEta_pt (F s) (G s) σ hFd hGd z,
    pb_lapS_sub (F s) (G s) σ hF hG z]
  ring

/-! ### Elementary inequalities for the barrier parameters -/

theorem pb_cosh_lower (x : ℝ) (_hx : 0 ≤ x) : (x + 1) / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have h1 := Real.add_one_le_exp x
  have h2 : 0 < Real.exp (-x) := Real.exp_pos _
  linarith

theorem pb_exists_R (a ε M : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ M ≤ ε * Real.cosh (a * R) := by
  have ha' : a ≠ 0 := ha.ne'
  have hε' : ε ≠ 0 := hε.ne'
  have key : ∀ R : ℝ, 0 ≤ R → 2 * |M| / ε ≤ a * R → M ≤ ε * Real.cosh (a * R) := by
    intro R hR0 ht0
    have hcl := pb_cosh_lower (a * R) (mul_nonneg ha.le hR0)
    have hεt : ε * (2 * |M| / ε) = 2 * |M| := by field_simp
    have h3 := mul_le_mul_of_nonneg_left ht0 hε.le
    have h4 := mul_le_mul_of_nonneg_left hcl hε.le
    have h5 := le_abs_self M
    nlinarith
  refine ⟨max 0 ((2 * |M| / ε) / a), le_max_left _ _, key _ (le_max_left _ _) ?_⟩
  have e : a * ((2 * |M| / ε) / a) = 2 * |M| / ε := by field_simp
  have h6 := mul_le_mul_of_nonneg_left (le_max_right 0 ((2 * |M| / ε) / a)) ha.le
  linarith

/-! ### The core minimum-principle step -/

theorem pb_core (h₁ : ParabolicMinPrinciple) (h₂ : SechSupersolution)
    (ν c T β A a K ε R M σ : ℝ) (b : ℝ → Plane → Vec) (om : ℝ → Plane → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hT : 0 < T) (ha : 0 < a) (hA : 0 < A) (hε : 0 < ε)
    (_hβ : 0 ≤ β) (hK0 : 0 ≤ K) (hK : β * a + ν * a ^ 2 < K)
    (hcont : ContinuousOn (fun x : ℝ × Plane => om x.1 x.2) (Icc 0 T ×ˢ univ))
    (hC2 : ContDiffOn ℝ 2 (fun x : ℝ × Plane => om x.1 x.2) (Ioo 0 T ×ˢ univ))
    (hper : ∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (om s))
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, ‖b s z‖ ≤ β)
    (hM : ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |om s z| ≤ M)
    (hop : ∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane, vorticityOp ν b om s z = 0)
    (h0 : ∀ z : Plane, |om 0 z| ≤ A * (Real.cosh (a * z.2))⁻¹)
    (hR0 : 0 ≤ R) (hRM : M ≤ ε * Real.cosh (a * R))
    (hσ : |σ| ≤ 1) :
    ∀ s ∈ Ico (0 : ℝ) T, ∀ z : Plane, σ * om s z ≤ pbF A ε K a s z := by
  have hsig : ∀ x : ℝ, σ * x ≤ |x| := fun x => by
    calc σ * x ≤ |σ * x| := le_abs_self _
      _ = |σ| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hσ (abs_nonneg x)
      _ = |x| := one_mul _
  have hFc : ContinuousOn (fun x : ℝ × Plane => pbF A ε K a x.1 x.2) (Icc 0 T ×ˢ univ) :=
    (pbF_contDiff A ε K a).continuous.continuousOn
  have hσc : ContinuousOn (fun _ : ℝ × Plane => σ) (Icc 0 T ×ˢ univ) := continuousOn_const
  have hD_cont : ContinuousOn (fun x : ℝ × Plane => pbF A ε K a x.1 x.2 - σ * om x.1 x.2)
      (Icc 0 T ×ˢ univ) :=
    hFc.sub (hσc.mul hcont)
  have hσd : ContDiffOn ℝ 2 (fun _ : ℝ × Plane => σ) (Ioo 0 T ×ˢ univ) :=
    (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ × Plane => σ)).contDiffOn
  have hD_cd : ContDiffOn ℝ 2 (fun x : ℝ × Plane => pbF A ε K a x.1 x.2 - σ * om x.1 x.2)
      (Ioo 0 T ×ˢ univ) :=
    (pbF_contDiff A ε K a).contDiffOn.sub (hσd.mul hC2)
  have hD_per : ∀ s ∈ Icc (0 : ℝ) T,
      Cyl.IsPeriodic c (fun w => pbF A ε K a s w - σ * om s w) := by
    intro s hs
    unfold Cyl.IsPeriodic
    intro z
    have hp : om s (z.1 + c, z.2) = om s z := hper s hs z
    have hq : pbF A ε K a s (z.1 + c, z.2) = pbF A ε K a s z := rfl
    show pbF A ε K a s (z.1 + c, z.2) - σ * om s (z.1 + c, z.2)
        = pbF A ε K a s z - σ * om s z
    rw [hp, hq]
  have hD_0 : ∀ z : Plane, 0 ≤ pbF A ε K a 0 z - σ * om 0 z := by
    intro z
    have e0 : pbF A ε K a 0 z = A * (Real.cosh (a * z.2))⁻¹ + coshBarrier ε K a 0 z := by
      unfold pbF sechBarrier
      rw [mul_zero, Real.exp_zero, mul_one]
    have hcB0 : 0 ≤ coshBarrier ε K a 0 z := by
      unfold coshBarrier
      exact mul_nonneg (mul_nonneg hε.le (Real.exp_pos _).le) (Real.cosh_pos _).le
    have hbd := (hsig (om 0 z)).trans (h0 z)
    rw [e0]
    linarith
  have hD_R : ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, R ≤ |z.2| →
      0 ≤ pbF A ε K a s z - σ * om s z := by
    intro s hs z hRz
    have hcosh_le : Real.cosh (a * R) ≤ Real.cosh (a * z.2) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg ha.le hR0), abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left hRz ha.le
    have hexp1 : 1 ≤ Real.exp (K * s) := Real.one_le_exp (mul_nonneg hK0 hs.1)
    have hcB : ε * Real.cosh (a * R) ≤ coshBarrier ε K a s z := by
      unfold coshBarrier
      have h1 : ε * Real.cosh (a * R) ≤ ε * Real.cosh (a * z.2) :=
        mul_le_mul_of_nonneg_left hcosh_le hε.le
      have hcz : 0 ≤ ε * Real.cosh (a * z.2) := mul_nonneg hε.le (Real.cosh_pos _).le
      nlinarith [mul_nonneg hcz (sub_nonneg.mpr hexp1)]
    have hsech : 0 ≤ sechBarrier A K a s z := by
      unfold sechBarrier
      exact mul_nonneg (mul_nonneg hA.le (Real.exp_pos _).le)
        (inv_nonneg.mpr (Real.cosh_pos _).le)
    have hcoshB : 0 ≤ coshBarrier ε K a s z := by
      unfold coshBarrier
      exact mul_nonneg (mul_nonneg hε.le (Real.exp_pos _).le) (Real.cosh_pos _).le
    have hom' : σ * om s z ≤ M := (hsig (om s z)).trans (hM s hs z)
    show 0 ≤ sechBarrier A K a s z + coshBarrier ε K a s z - σ * om s z
    linarith
  have hD_op : ∀ s ∈ Ioo (0 : ℝ) T, ∀ z : Plane,
      (fun t w => pbF A ε K a t w - σ * om t w) s z < 0 →
        0 < vorticityOp ν b (fun t w => pbF A ε K a t w - σ * om t w) s z := by
    intro s hs z _
    have hsIcc : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
    have hFs : ContDiff ℝ 2 (pbF A ε K a s) := pb_slice_contDiff (pbF_contDiff A ε K a) s
    have hOs : ContDiff ℝ 2 (om s) := pb_slice_contDiff_om hC2 hs
    have hFt : DifferentiableAt ℝ (fun t => pbF A ε K a t z) s := by
      have hd : DifferentiableAt ℝ (fun x : ℝ × Plane => pbF A ε K a x.1 x.2) (s, z) :=
        (pbF_contDiff A ε K a).differentiable (by norm_num) (s, z)
      exact pb_tslice_diffAt hd
    have hGt : DifferentiableAt ℝ (fun t => om t z) s := by
      have hd : DifferentiableAt ℝ (fun x : ℝ × Plane => om x.1 x.2) (s, z) :=
        (hC2.differentiableOn (by norm_num)).differentiableAt
          ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ z⟩)
      exact pb_tslice_diffAt hd
    have hlin := pb_vorticityOp_sub ν b (pbF A ε K a) om σ s z hFs hOs hFt hGt
    rw [hop s hs z, mul_zero, sub_zero] at hlin
    rw [hlin]
    have hsechpos : 0 < sechBarrier A K a s z := by
      unfold sechBarrier
      exact mul_pos (mul_pos hA (Real.exp_pos _)) (inv_pos.mpr (Real.cosh_pos _))
    have hcoshB : 0 ≤ coshBarrier ε K a s z := by
      unfold coshBarrier
      exact mul_nonneg (mul_nonneg hε.le (Real.exp_pos _).le) (Real.cosh_pos _).le
    have h2 := h₂ ν β A ε K a b s z hν.le ha hA.le hε.le (hb s hsIcc z)
    have hpos : 0 < (K - β * a - ν * a ^ 2) * (sechBarrier A K a s z + coshBarrier ε K a s z) :=
      mul_pos (by linarith) (by linarith)
    exact lt_of_lt_of_le hpos h2
  have key := h₁ ν c T R b (fun t w => pbF A ε K a t w - σ * om t w) hν hc hT
    hD_cont hD_cd hD_per hD_0 hD_R hD_op
  intro s hs z
  have h : 0 ≤ pbF A ε K a s z - σ * om s z := key s hs z
  linarith

/-! ### The comparison theorem -/

/-- **Comparison theorem for the vorticity equation with a bounded drift** (source lines 276-288),
conditional on the parabolic minimum principle and the sech supersolution property. -/
theorem parabolicSechBarrier_of (h₁ : ParabolicMinPrinciple) (h₂ : SechSupersolution) :
    ParabolicSechBarrier := by
  unfold ParabolicSechBarrier
  intro ν c T β A a K b om hν hc hT ha hA hK hcont hC2 hper hb hM hop h0
  obtain ⟨M, hM'⟩ := hM
  have hT0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hb 0 hT0 (0 : Plane))
  have hK0 : 0 ≤ K := by
    have h1 := mul_nonneg hβ ha.le
    have h2 := mul_nonneg hν.le (sq_nonneg a)
    linarith
  -- For each ε > 0, the barrier bound holds on [0, T).
  have hbarrier : ∀ ε : ℝ, 0 < ε → ∀ s ∈ Ico (0 : ℝ) T, ∀ z : Plane,
      |om s z| ≤ pbF A ε K a s z := by
    intro ε hε
    obtain ⟨R, hR0, hRM⟩ := pb_exists_R a ε M ha hε
    have hp := pb_core h₁ h₂ ν c T β A a K ε R M 1 b om hν hc hT ha hA hε hβ hK0 hK
      hcont hC2 hper hb hM' hop h0 hR0 hRM (by norm_num)
    have hn := pb_core h₁ h₂ ν c T β A a K ε R M (-1) b om hν hc hT ha hA hε hβ hK0 hK
      hcont hC2 hper hb hM' hop h0 hR0 hRM (by norm_num)
    intro s hs z
    rw [abs_le]
    constructor
    · have := hn s hs z
      linarith
    · have := hp s hs z
      linarith
  -- Extension from [0, T) to [0, T] by continuity at T.
  have hbarrierIcc : ∀ ε : ℝ, 0 < ε → ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      |om s z| ≤ pbF A ε K a s z := by
    intro ε hε s hs z
    rcases eq_or_lt_of_le hs.2 with h | h
    · have hcz : ContinuousOn (fun t : ℝ => om t z) (Icc 0 T) := by
        have h2 : ContinuousOn (fun t : ℝ => (t, z)) (Icc 0 T) :=
          (continuous_id.prodMk continuous_const).continuousOn
        exact hcont.comp h2 (fun t ht => mk_mem_prod ht (mem_univ z))
      have hcT : ContinuousWithinAt (fun t : ℝ => |om t z|) (Ico 0 T) T :=
        ContinuousWithinAt.comp (continuous_abs.continuousWithinAt)
          ((hcz T ⟨hT.le, le_refl T⟩).mono Ico_subset_Icc_self) (mapsTo_univ _ _)
      have hFT : ContinuousWithinAt (fun t : ℝ => pbF A ε K a t z) (Ico 0 T) T :=
        ((pbF_contDiff A ε K a).continuous.comp
          (continuous_id.prodMk continuous_const)).continuousWithinAt
      have hx : T ∈ closure (Ico (0 : ℝ) T) := by
        rw [closure_Ico hT.ne]
        exact ⟨hT.le, le_refl T⟩
      have hle := ContinuousWithinAt.closure_le hx hcT hFT
        (fun y hy => hbarrier ε hε y hy z)
      rw [h]
      exact hle
    · exact hbarrier ε hε s ⟨hs.1, h⟩ z
  -- Let ε → 0.
  have hsech_lim : ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |om s z| ≤ sechBarrier A K a s z := by
    intro s hs z
    by_contra hlt
    push_neg at hlt
    have hX : 0 ≤ Real.exp (K * s) * Real.cosh (a * z.2) :=
      mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
    have hδ : 0 < |om s z| - sechBarrier A K a s z := by linarith
    obtain ⟨ε, hε, hεsmall⟩ : ∃ ε : ℝ, 0 < ε ∧
        ε * (Real.exp (K * s) * Real.cosh (a * z.2)) < |om s z| - sechBarrier A K a s z := by
      refine ⟨(|om s z| - sechBarrier A K a s z) / (Real.exp (K * s) * Real.cosh (a * z.2) + 1),
        div_pos hδ (by linarith), ?_⟩
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    have h1 : |om s z| ≤ sechBarrier A K a s z + coshBarrier ε K a s z :=
      hbarrierIcc ε hε s hs z
    have hcb : coshBarrier ε K a s z = ε * (Real.exp (K * s) * Real.cosh (a * z.2)) := by
      unfold coshBarrier
      ring
    linarith
  exact hsech_lim

end UnforcedLeray.Short.PartI
