import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6

/-!
# `PartIII-b:C/asrc/ra/6/3` : `div(a⊗b + b⊗a)` commutes with linear isometries

Source of record: `the November 2 reference manuscript`; definition
`physDivSym` (Sub/IIIb-D2_3_2/Defs.lean:70).

Writing `Q_y(x,w) = ⟪x,a⟫ ∂_y b·w + ⟪x,∂_y a·w⟫ b + ⟪x,b⟫ ∂_y a·w + ⟪x,∂_y b·w⟫ a` (bilinear in
`(x,w)`), the `i`-th component of `div(a⊗b+b⊗a)` is `∑_j Q_y(e_j,e_j)` paired with `e_i`. Then
`Q_{gy}(gx,gw) = g Q_y(x,w)` and the trace over the orthonormal basis `g⁻¹e_j` is basis-free.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem raS_g_hasFDerivAt (g : Space ≃ₗᵢ[ℝ] Space) (y : Space) :
    HasFDerivAt (fun z : Space => g z) (g.toContinuousLinearEquiv : Space →L[ℝ] Space) y :=
  (g.toContinuousLinearEquiv).hasFDerivAt

theorem raS_fderiv_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : Differentiable ℝ f)
    (hfg : ∀ z, f (g z) = g (f z)) (y v : Space) :
    fderiv ℝ f (g y) (g v) = g (fderiv ℝ f y v) := by
  have h1 : HasFDerivAt (fun z => f (g z))
      ((fderiv ℝ f (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space)) y :=
    (hf (g y)).hasFDerivAt.comp y (raS_g_hasFDerivAt g y)
  have h2 : HasFDerivAt (fun z => g (f z))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ f y)) y :=
    (raS_g_hasFDerivAt g (f y)).comp y (hf y).hasFDerivAt
  have h3 : (fun z => f (g z)) = fun z => g (f z) := funext hfg
  rw [h3] at h1
  have h4 := h1.unique h2
  have h5 := congrArg (fun L : Space →L[ℝ] Space => L v) h4
  simpa using h5

theorem raS_coord (x : Space) (k : Fin 3) : inner ℝ (coordinateVector k) x = x k := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

theorem raS_expand (u : Space) : u = ∑ k : Fin 3, u k • coordinateVector k := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector, EuclideanSpace.single_apply]

/-- Trace of a bilinear map over the orthonormal basis `h⁻¹ e_j`, `h` a linear isometry. -/
theorem raS_trace {F : Type*} [AddCommGroup F] [Module ℝ F] (B : Space →ₗ[ℝ] Space →ₗ[ℝ] F)
    (h : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j : Fin 3, B (h (coordinateVector j)) (h (coordinateVector j)) =
      ∑ j : Fin 3, B (coordinateVector j) (coordinateVector j) := by
  have hexp : ∀ u : Space, u = ∑ k : Fin 3, inner ℝ (coordinateVector k) u • coordinateVector k := by
    intro u
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector, EuclideanSpace.single_apply,
      EuclideanSpace.inner_single_left]
  have hpars : ∀ x y : Space,
      ∑ j : Fin 3, inner ℝ x (coordinateVector j) * inner ℝ (coordinateVector j) y =
        inner ℝ x y := by
    intro x y
    conv_rhs => rw [hexp y]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  have hdelta : ∀ k l : Fin 3,
      inner ℝ (coordinateVector k) (coordinateVector l) = if k = l then 1 else 0 := by
    intro k l
    simp [coordinateVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  have gen : ∀ m j : Fin 3,
      inner ℝ (coordinateVector m) (h (coordinateVector j)) =
        inner ℝ (h.symm (coordinateVector m)) (coordinateVector j) := by
    intro m j
    conv_lhs => rw [← h.apply_symm_apply (coordinateVector m)]
    exact h.inner_map_map _ _
  have hcoef : ∀ k l : Fin 3,
      ∑ j : Fin 3, inner ℝ (coordinateVector k) (h (coordinateVector j)) *
        inner ℝ (coordinateVector l) (h (coordinateVector j)) =
        inner ℝ (coordinateVector k) (coordinateVector l) := by
    intro k l
    have e2 : ∀ j : Fin 3, inner ℝ (coordinateVector l) (h (coordinateVector j)) =
        inner ℝ (coordinateVector j) (h.symm (coordinateVector l)) := by
      intro j
      rw [gen l j, real_inner_comm]
    have hk : ∀ j : Fin 3, inner ℝ (coordinateVector k) (h (coordinateVector j)) =
        inner ℝ (h.symm (coordinateVector k)) (coordinateVector j) := fun j => gen k j
    rw [Finset.sum_congr rfl fun j _ => by rw [hk j, e2 j]]
    rw [hpars (h.symm (coordinateVector k)) (h.symm (coordinateVector l))]
    exact h.symm.inner_map_map _ _
  have hexp2 : ∀ u v : Space, B u v = ∑ k : Fin 3, ∑ l : Fin 3,
      (inner ℝ (coordinateVector k) u * inner ℝ (coordinateVector l) v) •
        B (coordinateVector k) (coordinateVector l) := by
    intro u v
    conv_lhs => rw [hexp u, hexp v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.sum_apply, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  calc ∑ j : Fin 3, B (h (coordinateVector j)) (h (coordinateVector j))
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun j _ => hexp2 _ _
    _ = ∑ k : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) := Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, inner ℝ (coordinateVector k) (coordinateVector l) •
          B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
          rw [← Finset.sum_smul, hcoef k l]
    _ = ∑ k : Fin 3, B (coordinateVector k) (coordinateVector k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hdelta]

theorem raS_deriv (a b : Space → Space) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (u v y w : Space) :
    fderiv ℝ (fun y' => inner ℝ u (a y') * inner ℝ v (b y') + inner ℝ u (b y') * inner ℝ v (a y'))
        y w =
      inner ℝ u (a y) * inner ℝ v (fderiv ℝ b y w) + inner ℝ v (b y) * inner ℝ u (fderiv ℝ a y w) +
      (inner ℝ u (b y) * inner ℝ v (fderiv ℝ a y w) + inner ℝ v (a y) * inner ℝ u (fderiv ℝ b y w)) := by
  have h1 : HasFDerivAt (fun y' => inner ℝ u (a y')) ((innerSL ℝ u).comp (fderiv ℝ a y)) y :=
    (innerSL ℝ u).hasFDerivAt.comp y (ha y).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => inner ℝ v (b y')) ((innerSL ℝ v).comp (fderiv ℝ b y)) y :=
    (innerSL ℝ v).hasFDerivAt.comp y (hb y).hasFDerivAt
  have h3 : HasFDerivAt (fun y' => inner ℝ u (b y')) ((innerSL ℝ u).comp (fderiv ℝ b y)) y :=
    (innerSL ℝ u).hasFDerivAt.comp y (hb y).hasFDerivAt
  have h4 : HasFDerivAt (fun y' => inner ℝ v (a y')) ((innerSL ℝ v).comp (fderiv ℝ a y)) y :=
    (innerSL ℝ v).hasFDerivAt.comp y (ha y).hasFDerivAt
  have h := (h1.mul h2).add (h3.mul h4)
  erw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]

/-- The bilinear form `Q_y(x,w) = ⟪x,a⟫ B w + ⟪x,A w⟫ b + ⟪x,b⟫ A w + ⟪x,B w⟫ a`. -/
def raSQ (a b : Space) (A B : Space →L[ℝ] Space) : Space →ₗ[ℝ] Space →ₗ[ℝ] Space :=
  LinearMap.mk₂ ℝ
    (fun x w => inner ℝ x a • B w + inner ℝ x (A w) • b + inner ℝ x b • A w + inner ℝ x (B w) • a)
    (by
      intro x x' w
      simp only [inner_add_left]
      module)
    (by
      intro c x w
      simp only [real_inner_smul_left]
      module)
    (by
      intro x w w'
      simp only [map_add, inner_add_right]
      module)
    (by
      intro c x w
      simp only [map_smul, real_inner_smul_right]
      module)

theorem raSQ_apply (a b : Space) (A B : Space →L[ℝ] Space) (x w : Space) :
    raSQ a b A B x w = inner ℝ x a • B w + inner ℝ x (A w) • b + inner ℝ x b • A w +
      inner ℝ x (B w) • a := rfl

/-- The vector `∑_j Q_y(e_j,e_j)`. -/
def raSV (a b : Space → Space) (y : Space) : Space :=
  ∑ j : Fin 3, raSQ (a y) (b y) (fderiv ℝ a y) (fderiv ℝ b y) (coordinateVector j) (coordinateVector j)

theorem raS_phys (a b : Space → Space) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (y : Space) : physDivSym a b y = raSV a b y := by
  ext i
  have hL : (physDivSym a b y) i = ∑ j : Fin 3,
      fderiv ℝ (fun y' => a y' j * b y' i + b y' j * a y' i) y (coordinateVector j) := rfl
  rw [hL, ← raS_coord (raSV a b y) i]
  unfold raSV
  simp only [raSQ_apply, inner_sum, inner_add_right, real_inner_smul_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : (fun y' => a y' j * b y' i + b y' j * a y' i) =
      fun y' => inner ℝ (coordinateVector j) (a y') * inner ℝ (coordinateVector i) (b y') +
        inner ℝ (coordinateVector j) (b y') * inner ℝ (coordinateVector i) (a y') := by
    funext y'
    simp only [raS_coord]
  rw [hF, raS_deriv a b ha hb]
  ring

theorem raSV_equiv (g : Space ≃ₗᵢ[ℝ] Space) (a b : Space → Space) (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) (hag : ∀ z, a (g z) = g (a z)) (hbg : ∀ z, b (g z) = g (b z))
    (y : Space) : raSV a b (g y) = g (raSV a b y) := by
  have key : ∀ x w : Space,
      raSQ (a (g y)) (b (g y)) (fderiv ℝ a (g y)) (fderiv ℝ b (g y)) (g x) (g w) =
        g (raSQ (a y) (b y) (fderiv ℝ a y) (fderiv ℝ b y) x w) := by
    intro x w
    rw [raSQ_apply, raSQ_apply, hag y, hbg y, raS_fderiv_equiv g a ha hag y w,
      raS_fderiv_equiv g b hb hbg y w]
    simp only [LinearIsometryEquiv.inner_map_map, map_add, map_smul]
  have hs : ∀ j : Fin 3,
      raSQ (a (g y)) (b (g y)) (fderiv ℝ a (g y)) (fderiv ℝ b (g y))
          (coordinateVector j) (coordinateVector j) =
        g (raSQ (a y) (b y) (fderiv ℝ a y) (fderiv ℝ b y) (g.symm (coordinateVector j))
          (g.symm (coordinateVector j))) := by
    intro j
    have h := key (g.symm (coordinateVector j)) (g.symm (coordinateVector j))
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  unfold raSV
  rw [Finset.sum_congr rfl (fun j _ => hs j), ← map_sum]
  congr 1
  exact raS_trace (raSQ (a y) (b y) (fderiv ℝ a y) (fderiv ℝ b y)) g.symm

theorem physDivSymEquiv : PhysDivSymEquiv := by
  intro g a b ha hb hag hbg y
  have ha' : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hb' : Differentiable ℝ b := hb.differentiable (by norm_num)
  rw [raS_phys a b ha' hb' (g y), raS_phys a b ha' hb' y]
  exact raSV_equiv g a b ha' hb' hag hbg y

end UnforcedLeray.Short.PartIIIb.Concrete
