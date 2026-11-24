import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Fderiv

/-!
# Shared trace and Hessian helpers (`PartIII-b:IIIb-D2/3/2/11/4`, source 6314-6316, 4280-4282)

* `sum_coord`: `∑ l, v l • e_l = v`.
* `coord_expand`, `coord_expand_left`: a map linear in one argument, evaluated on a vector, is the
  coordinate sum over the standard basis.
* `orth_sum_eq`: the trace `∑ j, Ψ (e_j) (e_j)` of a bilinear `Ψ` is independent of the
  orthonormal basis (`OrthonormalBasis.sum_inner_mul_inner`).
* `hessOp`: the second derivative `physPd2 F j l y = hessOp F y e_j e_l`, with linearity and
  equivariance `D²F(gy)(gu)(gv) = g D²F(y)(u)(v)` for `C²` fields commuting with `g`.
* `trace_equiv`: `∑_j Ψ (gy) e_j e_j = g (∑_j Ψ y e_j e_j)` for equivariant bilinear `Ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped RealInnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sum_coord (v : Space) : ∑ l : Fin 3, v l • coordinateVector l = v := by
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b = EuclideanSpace.basisFun (Fin 3) ℝ :=
    ⟨_, rfl⟩
  have h := b.sum_repr v
  have hbj : ∀ j, b j = coordinateVector j := fun j => by
    rw [hb]; simp [coordinateVector]
  have hr : ∀ j, b.repr v j = v j := fun j => by
    rw [hb]; simp
  simp only [hbj, hr] at h
  exact h

theorem coord_expand {Ψ : Space → Space → Space}
    (h3 : ∀ x z z', Ψ x (z + z') = Ψ x z + Ψ x z')
    (h4 : ∀ (c : ℝ) x z, Ψ x (c • z) = c • Ψ x z) (u w : Space) :
    ∑ l : Fin 3, w l • Ψ u (coordinateVector l) = Ψ u w := by
  have hzero : ∀ x, Ψ x 0 = 0 := fun x => by simpa using h4 0 x 0
  have hsum : ∀ (s : Finset (Fin 3)) (f : Fin 3 → ℝ),
      Ψ u (∑ l ∈ s, f l • coordinateVector l) = ∑ l ∈ s, f l • Ψ u (coordinateVector l) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h3, ih, h4]
  conv_rhs => rw [← sum_coord w]
  exact (hsum Finset.univ (fun l => w l)).symm

theorem coord_expand_left {Ψ : Space → Space → Space}
    (h1 : ∀ x x' z, Ψ (x + x') z = Ψ x z + Ψ x' z)
    (h2 : ∀ (c : ℝ) x z, Ψ (c • x) z = c • Ψ x z) (u v : Space) :
    ∑ j : Fin 3, u j • Ψ (coordinateVector j) v = Ψ u v := by
  have hzero : ∀ z, Ψ 0 z = 0 := fun z => by simpa using h2 0 0 z
  have hsum : ∀ (s : Finset (Fin 3)) (f : Fin 3 → ℝ),
      Ψ (∑ l ∈ s, f l • coordinateVector l) v = ∑ l ∈ s, f l • Ψ (coordinateVector l) v := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, ih, h2]
  conv_rhs => rw [← sum_coord u]
  exact (hsum Finset.univ (fun l => u l)).symm

theorem orth_sum_eq {Ψ : Space → Space → Space}
    (h1 : ∀ x x' z, Ψ (x + x') z = Ψ x z + Ψ x' z)
    (h2 : ∀ (c : ℝ) x z, Ψ (c • x) z = c • Ψ x z)
    (h3 : ∀ x z z', Ψ x (z + z') = Ψ x z + Ψ x z')
    (h4 : ∀ (c : ℝ) x z, Ψ x (c • z) = c • Ψ x z)
    (b c : OrthonormalBasis (Fin 3) ℝ Space) :
    ∑ j, Ψ (c j) (c j) = ∑ j, Ψ (b j) (b j) := by
  have hkey : ∀ x z, Ψ x z = ∑ k, ∑ l, (⟪b k, x⟫ * ⟪b l, z⟫) • Ψ (b k) (b l) := by
    intro x z
    let B : Space →ₗ[ℝ] Space →ₗ[ℝ] Space := LinearMap.mk₂ ℝ Ψ h1 h2 h3 h4
    show B x z = _
    calc B x z = B (∑ k, ⟪b k, x⟫ • b k) (∑ l, ⟪b l, z⟫ • b l) := by
          rw [b.sum_repr' x, b.sum_repr' z]
      _ = _ := by
          simp [B, map_sum, map_smul, LinearMap.sum_apply, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hinner : ∀ k l, ∑ j, ⟪b k, c j⟫ * ⟪b l, c j⟫ = if k = l then (1 : ℝ) else 0 := by
    intro k l
    have h := c.sum_inner_mul_inner (b k) (b l)
    rw [orthonormal_iff_ite.mp b.orthonormal k l] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (b l) (c j)]
  calc ∑ j, Ψ (c j) (c j)
      = ∑ j, ∑ k, ∑ l, (⟪b k, c j⟫ * ⟪b l, c j⟫) • Ψ (b k) (b l) :=
        Finset.sum_congr rfl fun j _ => hkey _ _
    _ = ∑ k, ∑ l, (∑ j, ⟪b k, c j⟫ * ⟪b l, c j⟫) • Ψ (b k) (b l) := by
        simp only [Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, (if k = l then (1 : ℝ) else 0) • Ψ (b k) (b l) := by
        simp only [hinner]
    _ = ∑ j, Ψ (b j) (b j) := by
        simp [ite_smul, Finset.sum_ite_eq]

/-- The second derivative pairing `D²F(y)(u, v) = D(y ↦ DF(y) v)(y) u`. -/
def hessOp (F : Space → Space) (y u v : Space) : Space :=
  fderiv ℝ (fun y' => fderiv ℝ F y' v) y u

theorem physPd2_eq_hessOp (F : Space → Space) (j l : Fin 3) (y : Space) :
    physPd2 F j l y = hessOp F y (coordinateVector j) (coordinateVector l) := rfl

theorem K_diff {F : Space → Space} (hF : ContDiff ℝ 2 F) (v : Space) :
    Differentiable ℝ (fun y' => fderiv ℝ F y' v) := by
  have h : ContDiff ℝ 1 (fun y' => fderiv ℝ F y' v) :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact h.differentiable (by norm_num)

theorem hess_add_left (F : Space → Space) (y : Space) :
    ∀ u u' v : Space, hessOp F y (u + u') v = hessOp F y u v + hessOp F y u' v := by
  intro u u' v
  unfold hessOp
  rw [map_add]

theorem hess_smul_left (F : Space → Space) (y : Space) :
    ∀ (c : ℝ) (u v : Space), hessOp F y (c • u) v = c • hessOp F y u v := by
  intro c u v
  unfold hessOp
  rw [map_smul]

theorem hess_add_right {F : Space → Space} (hF : ContDiff ℝ 2 F) (y : Space) :
    ∀ u v v' : Space, hessOp F y u (v + v') = hessOp F y u v + hessOp F y u v' := by
  intro u v v'
  unfold hessOp
  have hfun : (fun y' => fderiv ℝ F y' (v + v')) =
      (fun y' => fderiv ℝ F y' v) + (fun y' => fderiv ℝ F y' v') := by
    funext y'
    simp [map_add]
  rw [hfun, fderiv_add (K_diff hF v y) (K_diff hF v' y), add_apply]

theorem hess_smul_right {F : Space → Space} (hF : ContDiff ℝ 2 F) (y : Space) :
    ∀ (c : ℝ) (u v : Space), hessOp F y u (c • v) = c • hessOp F y u v := by
  intro c u v
  unfold hessOp
  have hfun : (fun y' => fderiv ℝ F y' (c • v)) = c • (fun y' => fderiv ℝ F y' v) := by
    funext y'
    simp [map_smul]
  rw [hfun, fderiv_const_smul (K_diff hF v y) c, smul_apply]

/-- Equivariance of the second derivative pairing (source 6314-6316). -/
theorem hess_equiv (g : Space ≃ₗᵢ[ℝ] Space) (F : Space → Space) (hF : ContDiff ℝ 2 F)
    (hG : GEqv g F) (y u v : Space) :
    hessOp F (g y) (g u) (g v) = g (hessOp F y u v) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hK : (fun y' => fderiv ℝ F (g y') (g v)) = fun y' => g (fderiv ℝ F y' v) :=
    funext fun y' => fderivEqv_proved g F hFd hG y' v
  have hA : HasFDerivAt (fun y' => g (fderiv ℝ F y' v))
      ((g.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (fderiv ℝ (fun y' => fderiv ℝ F y' v) y)) y :=
    (g.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.comp y (K_diff hF v y).hasFDerivAt
  have hB : HasFDerivAt (fun y' => fderiv ℝ F (g y') (g v))
      ((fderiv ℝ (fun y'' => fderiv ℝ F y'' (g v)) (g y)).comp
        (g.toContinuousLinearEquiv.toContinuousLinearMap)) y :=
    (K_diff hF (g v) (g y)).hasFDerivAt.comp y
      (g.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt
  rw [hK] at hB
  have hU := hB.unique hA
  have h := congrArg (fun M : Space →L[ℝ] Space => M u) hU
  simp only [ContinuousLinearMap.comp_apply] at h
  have hL : ∀ w : Space, (g.toContinuousLinearEquiv.toContinuousLinearMap) w = g w :=
    fun w => rfl
  rw [hL, hL] at h
  unfold hessOp
  exact h

/-- Trace invariance: `∑_j Ψ (gy) e_j e_j = g (∑_j Ψ y e_j e_j)` for an equivariant
bilinear `Ψ`. -/
theorem trace_equiv (g : Space ≃ₗᵢ[ℝ] Space) (Ψ : Space → Space → Space → Space)
    (hequiv : ∀ y u v, Ψ (g y) (g u) (g v) = g (Ψ y u v))
    (h1 : ∀ y u u' v, Ψ y (u + u') v = Ψ y u v + Ψ y u' v)
    (h2 : ∀ y (c : ℝ) u v, Ψ y (c • u) v = c • Ψ y u v)
    (h3 : ∀ y u v v', Ψ y u (v + v') = Ψ y u v + Ψ y u v')
    (h4 : ∀ y (c : ℝ) u v, Ψ y u (c • v) = c • Ψ y u v) (y : Space) :
    ∑ j : Fin 3, Ψ (g y) (coordinateVector j) (coordinateVector j) =
      g (∑ j : Fin 3, Ψ y (coordinateVector j) (coordinateVector j)) := by
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b = EuclideanSpace.basisFun (Fin 3) ℝ :=
    ⟨_, rfl⟩
  have hbj : ∀ j, b j = coordinateVector j := fun j => by
    rw [hb]; simp [coordinateVector]
  have hc : ∀ j, b.map g.symm j = g.symm (b j) := fun j => b.map_apply g.symm j
  have hj : ∀ j, coordinateVector j = g (b.map g.symm j) := fun j => by
    rw [hc, LinearIsometryEquiv.apply_symm_apply, hbj]
  have key := orth_sum_eq (Ψ := fun u v => Ψ y u v) (h1 y) (h2 y) (h3 y) (h4 y) b (b.map g.symm)
  calc ∑ j : Fin 3, Ψ (g y) (coordinateVector j) (coordinateVector j)
      = ∑ j : Fin 3, g (Ψ y (b.map g.symm j) (b.map g.symm j)) :=
        Finset.sum_congr rfl fun j _ => by rw [hj j, hequiv]
    _ = g (∑ j : Fin 3, Ψ y (b.map g.symm j) (b.map g.symm j)) := (map_sum g _ _).symm
    _ = g (∑ j : Fin 3, Ψ y (coordinateVector j) (coordinateVector j)) := by
        rw [key]
        exact congrArg g (Finset.sum_congr rfl fun j _ => by rw [hbj j])

end UnforcedLeray.Short.PartIIIb.Concrete
