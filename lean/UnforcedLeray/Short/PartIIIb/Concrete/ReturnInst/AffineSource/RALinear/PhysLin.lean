import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs

/-!
# `RALinear` helper: linearity of the physical operators `D_μ`, `∇` and `div(a⊗b+b⊗a)` in the
field (source 4140-4141, 4985, 5001-5008)

For fields that are jointly `C²` (resp. `C¹` for `∇` and the second slot of `div`), the operators
`physDmu`, `physGrad`, `physDivSym` are additive and homogeneous.  `physDivSym` additivity in the
second slot is `physDivSym_add` of `IIIb-D2_3_2_8`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A `C²` spatial field is differentiable. -/
lemma ra_diff_of_c2 {f : Space → Space} (hf : ContDiff ℝ 2 f) : Differentiable ℝ f :=
  hf.differentiable (by norm_num)

lemma ra_physPd_add (f g : Space → Space) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) :
    physPd (fun y => f y + g y) j = fun y => physPd f j y + physPd g j y := by
  funext y
  have df : fderiv ℝ (fun y => f y + g y) y = fderiv ℝ f y + fderiv ℝ g y :=
    fderiv_add (hf y) (hg y)
  unfold physPd
  rw [df]
  rfl

lemma ra_physPd_smul (f : Space → Space) (hf : Differentiable ℝ f) (r : ℝ) (j : Fin 3) :
    physPd (fun y => r • f y) j = fun y => r • physPd f j y := by
  funext y
  have df : fderiv ℝ (fun y => r • f y) y = r • fderiv ℝ f y := fderiv_const_smul (hf y) r
  unfold physPd
  rw [df]
  rfl

lemma ra_physPd_diff {f : Space → Space} (hf : ContDiff ℝ 2 f) (l : Fin 3) :
    Differentiable ℝ (physPd f l) := by
  have h1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : Differentiable ℝ (fun y => fderiv ℝ f y (coordinateVector l)) :=
    h1.clm_apply (differentiable_const _)
  exact h2

lemma ra_physPd2_add (f g : Space → Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (j l : Fin 3) (y : Space) :
    physPd2 (fun y => f y + g y) j l y = physPd2 f j l y + physPd2 g j l y := by
  unfold physPd2
  rw [ra_physPd_add f g (ra_diff_of_c2 hf) (ra_diff_of_c2 hg) l]
  rw [ra_physPd_add (physPd f l) (physPd g l) (ra_physPd_diff hf l) (ra_physPd_diff hg l) j]

lemma ra_physPd2_smul (f : Space → Space) (hf : ContDiff ℝ 2 f) (r : ℝ) (j l : Fin 3) (y : Space) :
    physPd2 (fun y => r • f y) j l y = r • physPd2 f j l y := by
  unfold physPd2
  rw [ra_physPd_smul f (ra_diff_of_c2 hf) r l]
  rw [ra_physPd_smul (physPd f l) (ra_physPd_diff hf l) r j]

lemma ra_physLap_add (f g : Space → Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Space) :
    physLap (fun y => f y + g y) y = physLap f y + physLap g y := by
  unfold physLap
  simp only [ra_physPd2_add f g hf hg]
  rw [Finset.sum_add_distrib]

lemma ra_physLap_smul (f : Space → Space) (hf : ContDiff ℝ 2 f) (r : ℝ) (y : Space) :
    physLap (fun y => r • f y) y = r • physLap f y := by
  unfold physLap
  simp only [ra_physPd2_smul f hf r]
  rw [Finset.smul_sum]

/-- Additivity of `D_μ` on jointly `C²` fields (source 4140-4141). -/
lemma ra_physDmu_add (ν μ : ℝ) (X Y : ℝ → Space → Space)
    (hX : ContDiff ℝ 2 (fun x : ℝ × Space => X x.1 x.2))
    (hY : ContDiff ℝ 2 (fun x : ℝ × Space => Y x.1 x.2)) (τ : ℝ) (y : Space) :
    physDmu ν μ (fun t y => X t y + Y t y) τ y = physDmu ν μ X τ y + physDmu ν μ Y τ y := by
  have sX : ContDiff ℝ 2 (X τ) := hX.comp (contDiff_const.prodMk contDiff_id)
  have sY : ContDiff ℝ 2 (Y τ) := hY.comp (contDiff_const.prodMk contDiff_id)
  have tX : DifferentiableAt ℝ (fun t => X t y) τ :=
    ((hX.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) τ
  have tY : DifferentiableAt ℝ (fun t => Y t y) τ :=
    ((hY.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) τ
  have dd : deriv (fun t => X t y + Y t y) τ = deriv (fun t => X t y) τ + deriv (fun t => Y t y) τ :=
    deriv_add tX tY
  have df : fderiv ℝ (fun y' => X τ y' + Y τ y') y = fderiv ℝ (X τ) y + fderiv ℝ (Y τ) y :=
    fderiv_add (ra_diff_of_c2 sX y) (ra_diff_of_c2 sY y)
  unfold physDmu
  dsimp only
  rw [dd, df, ra_physLap_add (X τ) (Y τ) sX sY y]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  abel

/-- Homogeneity of `D_μ` on jointly `C²` fields (source 4140-4141). -/
lemma ra_physDmu_smul (ν μ : ℝ) (X : ℝ → Space → Space)
    (hX : ContDiff ℝ 2 (fun x : ℝ × Space => X x.1 x.2)) (r : ℝ) (τ : ℝ) (y : Space) :
    physDmu ν μ (fun t y => r • X t y) τ y = r • physDmu ν μ X τ y := by
  have sX : ContDiff ℝ 2 (X τ) := hX.comp (contDiff_const.prodMk contDiff_id)
  have tX : DifferentiableAt ℝ (fun t => X t y) τ :=
    ((hX.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) τ
  have dd : deriv (fun t => r • X t y) τ = r • deriv (fun t => X t y) τ :=
    deriv_const_smul r tX
  have df : fderiv ℝ (fun y' => r • X τ y') y = r • fderiv ℝ (X τ) y :=
    fderiv_const_smul (ra_diff_of_c2 sX y) r
  unfold physDmu
  dsimp only
  rw [dd, df, ra_physLap_smul (X τ) sX r y]
  simp only [ContinuousLinearMap.smul_apply, smul_add, smul_sub, smul_smul]
  module

/-- Additivity of `∇` on `C¹` scalars. -/
lemma ra_physGrad_add (q q' : Space → ℝ) (hq : Differentiable ℝ q) (hq' : Differentiable ℝ q')
    (y : Space) :
    physGrad (fun y => q y + q' y) y = physGrad q y + physGrad q' y := by
  have df : fderiv ℝ (fun y => q y + q' y) y = fderiv ℝ q y + fderiv ℝ q' y :=
    fderiv_add (hq y) (hq' y)
  unfold physGrad
  rw [df]
  ext j
  simp

/-- Homogeneity of `∇` on `C¹` scalars. -/
lemma ra_physGrad_mul (q : Space → ℝ) (hq : Differentiable ℝ q) (r : ℝ) (y : Space) :
    physGrad (fun y => r * q y) y = r • physGrad q y := by
  have df : fderiv ℝ (fun y => r * q y) y = r • fderiv ℝ q y := fderiv_const_mul (hq y) r
  unfold physGrad
  rw [df]
  ext j
  simp

/-- Homogeneity of `div(a⊗b + b⊗a)` in the second slot. -/
lemma ra_physDivSym_smul (a b : Space → Space) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (r : ℝ) (y : Space) :
    physDivSym a (fun y' => r • b y') y = r • physDivSym a b y := by
  have hcoord : ∀ (f : Space → Space) (k : Fin 3), Differentiable ℝ f →
      Differentiable ℝ (fun y' => f y' k) := fun f k hf =>
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiable.comp hf)
  unfold physDivSym
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfun : (fun y' => (a y') j * (r * (b y') i) + r * (b y') j * (a y') i) =
      fun y' => r * ((a y') j * (b y') i + (b y') j * (a y') i) := by
    funext y'
    ring
  have d1 : Differentiable ℝ (fun y' => (a y') j * (b y') i + (b y') j * (a y') i) :=
    ((hcoord a j ha).mul (hcoord b i hb)).add ((hcoord b j hb).mul (hcoord a i ha))
  rw [hfun, fderiv_const_mul (d1 y) r]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
