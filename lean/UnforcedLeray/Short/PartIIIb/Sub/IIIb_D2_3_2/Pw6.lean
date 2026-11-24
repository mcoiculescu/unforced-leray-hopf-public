import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs

/-!
# `PwDmuDivFree`: `D_μ` preserves solenoidality (source 4140-4141)

For a jointly smooth `X` with `div X = 0` for all `(τ, y)`, the divergence of
`D_μ X = ∂_τX - ½ y·∇X - νΔX + (μ - ½)X` vanishes: the time derivative commutes with the spatial
divergence (mixed partials of the joint field), the Euler term contributes `div X + y·∇ div X`, and
the Laplacian contributes `Δ div X`.  Third-order symmetry of the spatial field is obtained from
second-order symmetry of its derivatives (`ContDiffAt.isSymmSndFDerivAt`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

section Generic

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem pw6_cm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : E →L[ℝ] G) {F : D → E} {z : D} (hF : DifferentiableAt ℝ F z) (v : D) :
    fderiv ℝ (fun x => L (F x)) z v = L (fderiv ℝ F z v) := by
  show fderiv ℝ (L ∘ F) z v = _
  rw [fderiv_comp z L.differentiableAt hF, ContinuousLinearMap.fderiv]
  rfl

theorem pw6_comp {f : D → Space} {z : D} (hf : DifferentiableAt ℝ f z) (i : Fin 3) (v : D) :
    fderiv ℝ f z v i = fderiv ℝ (fun w => f w i) z v :=
  (pw6_cm (EuclideanSpace.proj i : Space →L[ℝ] ℝ) hf v).symm

theorem pw6_apply_const {M E : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : D → (M →L[ℝ] E)} {z : D}
    (hF : DifferentiableAt ℝ F z) (u : M) (v : D) :
    fderiv ℝ (fun w => F w u) z v = fderiv ℝ F z v u :=
  pw6_cm (ContinuousLinearMap.apply ℝ E u) hF v

theorem pw6_apply2 {F : D → (Space →L[ℝ] (Space →L[ℝ] ℝ))} {z : D}
    (hF : DifferentiableAt ℝ F z) (u w : Space) (v : D) :
    fderiv ℝ (fun x => F x u w) z v = fderiv ℝ F z v u w := by
  have hF' : DifferentiableAt ℝ (fun x => F x u) z := hF.clm_apply (differentiableAt_const u)
  have h1 := pw6_cm (ContinuousLinearMap.apply ℝ ℝ w) hF' v
  rw [pw6_apply_const hF u v] at h1
  exact h1

theorem pw6_symm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : D → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (z u v : D) :
    fderiv ℝ (fderiv ℝ F) z u v = fderiv ℝ (fderiv ℝ F) z v u := by
  have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z := hF.contDiffAt
  exact (h.isSymmSndFDerivAt (by simp)).eq u v

theorem pw6_dfderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : D → E}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) : Differentiable ℝ (fderiv ℝ g) :=
  (hg.fderiv_right (m := 1) (by simp)).differentiable (by simp)

theorem pw6_chain_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ × Space → E} {τ : ℝ} {y : Space} (hH : DifferentiableAt ℝ H (τ, y)) (v : Space) :
    fderiv ℝ (fun z => H (τ, z)) y v = fderiv ℝ H (τ, y) (0, v) := by
  have hφ : HasFDerivAt (fun z : Space => ((τ, z) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hc := hH.hasFDerivAt.comp y hφ
  rw [show (fun z => H (τ, z)) = H ∘ (fun z : Space => ((τ, z) : ℝ × Space)) from rfl, hc.fderiv]
  simp

theorem pw6_chain_time {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ × Space → E} {τ : ℝ} {y : Space} (hH : DifferentiableAt ℝ H (τ, y)) :
    deriv (fun t => H (t, y)) τ = fderiv ℝ H (τ, y) (1, 0) := by
  have hφ : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (hH.hasFDerivAt.comp_hasDerivAt τ hφ).deriv

end Generic

theorem pw6_coord (k : Fin 3) (z v : Space) : fderiv ℝ (fun w : Space => w k) z v = v k := by
  have h : (fun w : Space => w k) = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  rfl

theorem pw6_dd {g : Space → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (i : Fin 3) :
    Differentiable ℝ (fun u => fderiv ℝ g u (coordinateVector i)) :=
  (pw6_dfderiv hg).clm_apply (differentiable_const _)

theorem pw6_physPd_apply (f : Space → Space) (j i : Fin 3) (z : Space)
    (hf : DifferentiableAt ℝ f z) :
    physPd f j z i = fderiv ℝ (fun w => f w i) z (coordinateVector j) := by
  unfold physPd
  exact pw6_comp hf i _

theorem pw6_decomp (g : Space → ℝ) (z v : Space) :
    fderiv ℝ g z v = ∑ k : Fin 3, v k * fderiv ℝ g z (coordinateVector k) := by
  have hv : v = ∑ k : Fin 3, v k • coordinateVector k := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

theorem pw6_lap_comp (f : Space → Space) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (i : Fin 3)
    (z : Space) :
    (physLap f z) i = ∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ (fun w => f w i)) z (coordinateVector j) (coordinateVector j) := by
  have hfd : ∀ w, DifferentiableAt ℝ f w := fun w => hf.differentiable (by simp) w
  have hfi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => f w i) := (contDiff_piLp 2).1 hf i
  have hg : ∀ j : Fin 3, DifferentiableAt ℝ (fun y' => physPd f j y') z := fun j => by
    have h1 : (fun y' => physPd f j y') = fun y' => fderiv ℝ f y' (coordinateVector j) := rfl
    rw [h1]
    exact ((pw6_dfderiv hf) z).clm_apply (differentiableAt_const _)
  unfold physLap physPd2
  rw [WithLp.ofLp_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pw6_physPd_apply _ j i z (hg j)]
  have hfun : (fun w => physPd f j w i) = fun w => fderiv ℝ (fun u => f u i) w (coordinateVector j) :=
    funext fun w => pw6_physPd_apply f j i w (hfd w)
  rw [show (fun w => (fun y' => physPd f j y') w i) = (fun w => physPd f j w i) from rfl, hfun]
  exact pw6_apply_const ((pw6_dfderiv hfi) z) (coordinateVector j) (coordinateVector j)

theorem pw6_E_deriv (W : Space → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (y v : Space) :
    fderiv ℝ (fun z => ∑ k : Fin 3, z k * fderiv ℝ W z (coordinateVector k)) y v =
      ∑ k : Fin 3, (v k * fderiv ℝ W y (coordinateVector k) +
        y k * fderiv ℝ (fderiv ℝ W) y v (coordinateVector k)) := by
  have hdW := pw6_dfderiv hW
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun z : Space => z k * fderiv ℝ W z (coordinateVector k)) y := by
    intro k _
    have hc : DifferentiableAt ℝ (fun z : Space => z k) y :=
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiableAt
    have hd : DifferentiableAt ℝ (fun z => fderiv ℝ W z (coordinateVector k)) y :=
      (hdW y).clm_apply (differentiableAt_const _)
    exact hc.mul hd
  rw [fderiv_fun_sum hterm, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : DifferentiableAt ℝ (fun z : Space => z k) y :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiableAt
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ W z (coordinateVector k)) y :=
    (hdW y).clm_apply (differentiableAt_const _)
  rw [fderiv_fun_mul hc hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, pw6_coord, pw6_apply_const (hdW y) (coordinateVector k) v]
  simp only [smul_eq_mul]
  ring

theorem pw6_D3_sym12 (W : Space → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (y u v w : Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ W)) y u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ W)) y v u w := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ W) := hW.fderiv_right (by simp)
  exact congrArg (fun A => A w) (pw6_symm hF y u v)

theorem pw6_D3_sym23 (W : Space → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (y u v w : Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ W)) y u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ W)) y u w v := by
  have hF1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ W) := hW.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ W)) y := (pw6_dfderiv hF1) y
  have hfun : (fun z => fderiv ℝ (fderiv ℝ W) z v w) = fun z => fderiv ℝ (fderiv ℝ W) z w v :=
    funext fun z => pw6_symm hW z v w
  have h1 : fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ W) z v w) y u =
      fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ W) z w v) y u := by
    rw [hfun]
  rw [pw6_apply2 hd v w u, pw6_apply2 hd w v u] at h1
  exact h1

theorem pw6_L1 (W : Fin 3 → Space → ℝ) (hW : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W i))
    (hdiv : ∀ z, ∑ i : Fin 3, fderiv ℝ (W i) z (coordinateVector i) = 0) (z : Space) (j : Fin 3) :
    ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W i)) z (coordinateVector j) (coordinateVector i) = 0 := by
  have hfun : (fun x => ∑ i : Fin 3, fderiv ℝ (W i) x (coordinateVector i)) = fun _ => (0 : ℝ) :=
    funext hdiv
  have hterm : ∀ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (W i) x (coordinateVector i)) z
      (coordinateVector j) = fderiv ℝ (fderiv ℝ (W i)) z (coordinateVector j) (coordinateVector i) :=
    fun i => pw6_apply_const ((pw6_dfderiv (hW i)) z) (coordinateVector i) (coordinateVector j)
  have key : fderiv ℝ (fun x => ∑ i : Fin 3, fderiv ℝ (W i) x (coordinateVector i)) z
      (coordinateVector j) = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W i)) z (coordinateVector j)
        (coordinateVector i) := by
    rw [fderiv_fun_sum (fun i _ => (pw6_dd (hW i) i) z), sum_apply]
    exact Finset.sum_congr rfl fun i _ => hterm i
  rw [hfun, fderiv_const_apply, ContinuousLinearMap.zero_apply] at key
  exact key.symm

theorem pw6_L3 (W : Fin 3 → Space → ℝ) (hW : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W i))
    (hdiv : ∀ z, ∑ i : Fin 3, fderiv ℝ (W i) z (coordinateVector i) = 0) (z : Space) (j : Fin 3) :
    ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ (W i))) z (coordinateVector j) (coordinateVector j)
      (coordinateVector i) = 0 := by
  have hpt : ∀ x : Space, ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W i)) x (coordinateVector j)
      (coordinateVector i) = 0 := fun x => pw6_L1 W hW hdiv x j
  have hfun : (fun x => ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W i)) x (coordinateVector j)
      (coordinateVector i)) = fun _ => (0 : ℝ) := funext hpt
  have hF1 : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (W i)) :=
    fun i => (hW i).fderiv_right (by simp)
  have hdiff : ∀ i, DifferentiableAt ℝ
      (fun x => fderiv ℝ (fderiv ℝ (W i)) x (coordinateVector j) (coordinateVector i)) z := by
    intro i
    have h2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (W i))) z := (pw6_dfderiv (hF1 i)) z
    exact (h2.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have key : fderiv ℝ (fun x => ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (W i)) x (coordinateVector j)
      (coordinateVector i)) z (coordinateVector j) = ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ (fderiv ℝ (W i))) z (coordinateVector j) (coordinateVector j)
          (coordinateVector i) := by
    rw [fderiv_fun_sum (fun i _ => hdiff i), sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact pw6_apply2 ((pw6_dfderiv (hF1 i)) z) (coordinateVector j) (coordinateVector i)
      (coordinateVector j)
  rw [hfun, fderiv_const_apply, ContinuousLinearMap.zero_apply] at key
  exact key.symm

theorem pw6_sym_ijj (W : Space → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (y : Space)
    (i j : Fin 3) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ W)) y (coordinateVector i) (coordinateVector j) (coordinateVector j) =
      fderiv ℝ (fderiv ℝ (fderiv ℝ W)) y (coordinateVector j) (coordinateVector j) (coordinateVector i) := by
  rw [pw6_D3_sym12 W hW y (coordinateVector i) (coordinateVector j) (coordinateVector j),
    pw6_D3_sym23 W hW y (coordinateVector j) (coordinateVector i) (coordinateVector j)]

theorem pw6_split (F G H K : Space → ℝ) (a b c : ℝ) (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (hH : Differentiable ℝ H) (hK : Differentiable ℝ K) (y v : Space) :
    fderiv ℝ (fun z => F z + a * G z + b * H z + c * K z) y v =
      fderiv ℝ F y v + a * fderiv ℝ G y v + b * fderiv ℝ H y v + c * fderiv ℝ K y v := by
  have h1 : DifferentiableAt ℝ (fun z => F z + a * G z) y := (hF y).add ((hG y).const_mul a)
  have h2 : DifferentiableAt ℝ (fun z => F z + a * G z + b * H z) y :=
    h1.add ((hH y).const_mul b)
  have h3 : DifferentiableAt ℝ (fun z => c * K z) y := (hK y).const_mul c
  rw [fderiv_fun_add h2 h3, fderiv_fun_add h1 ((hH y).const_mul b), fderiv_fun_add (hF y)
    ((hG y).const_mul a), fderiv_const_mul (hG y) a, fderiv_const_mul (hH y) b,
    fderiv_const_mul (hK y) c]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem pw6_time_sum (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (hdiv : ∀ τ y, ∑ j : Fin 3, physPd (X τ) j y j = 0) (τ : ℝ) (y : Space) :
    ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i)) (τ, y) (1, 0)
      (0, coordinateVector i) = 0 := by
  have hgi : ∀ i : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2 i) :=
    fun i => (contDiff_piLp 2).1 hX i
  have hGd : ∀ t z, DifferentiableAt ℝ (fun x : ℝ × Space => X x.1 x.2) (t, z) :=
    fun t z => hX.differentiable (by simp) (t, z)
  have hXtd : ∀ t z, DifferentiableAt ℝ (X t) z := fun t z =>
    (hGd t z).comp z ((differentiableAt_const t).prodMk differentiableAt_id)
  have hdiv' : ∀ t z, ∑ i : Fin 3, fderiv ℝ (fun w => X t w i) z (coordinateVector i) = 0 :=
    fun t z => (Finset.sum_congr rfl fun i _ =>
      (pw6_physPd_apply (X t) i i z (hXtd t z)).symm).trans (hdiv t z)
  have hQ : ∀ x : ℝ × Space, ∑ i : Fin 3,
      fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (0, coordinateVector i) = 0 := by
    rintro ⟨t, z⟩
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (hdiv' t z)
    exact (pw6_chain_slice (H := fun x : ℝ × Space => X x.1 x.2 i)
      ((hgi i).differentiable (by simp) (t, z)) (coordinateVector i)).symm
  have hdiffQ : ∀ i : Fin 3, DifferentiableAt ℝ (fun x : ℝ × Space =>
      fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (0, coordinateVector i)) (τ, y) :=
    fun i => ((pw6_dfderiv (hgi i)) (τ, y)).clm_apply (differentiableAt_const _)
  have hfun : (fun x : ℝ × Space => ∑ i : Fin 3,
      fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (0, coordinateVector i)) = fun _ => (0 : ℝ) :=
    funext hQ
  have key : fderiv ℝ (fun x : ℝ × Space => ∑ i : Fin 3,
      fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (0, coordinateVector i)) (τ, y) (1, 0) =
      ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i)) (τ, y) (1, 0)
        (0, coordinateVector i) := by
    rw [fderiv_fun_sum (fun i _ => hdiffQ i), sum_apply]
    exact Finset.sum_congr rfl fun i _ =>
      pw6_apply_const ((pw6_dfderiv (hgi i)) (τ, y)) (0, coordinateVector i) (1, 0)
  rw [hfun, fderiv_const_apply, ContinuousLinearMap.zero_apply] at key
  exact key.symm

theorem pw6_cv (i k : Fin 3) : coordinateVector i k = if k = i then 1 else 0 := by
  simp [coordinateVector, Pi.single_apply]

def pw6T (X : ℝ → Space → Space) (τ : ℝ) (i : Fin 3) : Space → ℝ :=
  fun z => fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) (τ, z) (1, 0)

def pw6E (X : ℝ → Space → Space) (τ : ℝ) (i : Fin 3) : Space → ℝ :=
  fun z => ∑ k : Fin 3, z k * fderiv ℝ (fun w => X τ w i) z (coordinateVector k)

def pw6L (X : ℝ → Space → Space) (τ : ℝ) (i : Fin 3) : Space → ℝ :=
  fun z => ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fun w => X τ w i)) z (coordinateVector j)
    (coordinateVector j)

def pw6V (X : ℝ → Space → Space) (τ : ℝ) (i : Fin 3) : Space → ℝ :=
  fun z => X τ z i

theorem pw6_component (ν μ : ℝ) (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (τ : ℝ) (i : Fin 3) (z : Space) :
    physDmu ν μ X τ z i = pw6T X τ i z + (-(1 / 2 : ℝ)) * pw6E X τ i z +
      (-ν) * pw6L X τ i z + (μ - 1 / 2) * pw6V X τ i z := by
  have hGd : DifferentiableAt ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, z) :=
    hX.differentiable (by simp) (τ, z)
  have hXtd : DifferentiableAt ℝ (X τ) z :=
    hGd.comp z ((differentiableAt_const τ).prodMk differentiableAt_id)
  have hXt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X τ) :=
    hX.comp (contDiff_const.prodMk contDiff_id)
  have ht : deriv (fun t => X t z) τ = fderiv ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, z) (1, 0) :=
    pw6_chain_time (H := fun x : ℝ × Space => X x.1 x.2) hGd
  unfold physDmu
  rw [ht]
  simp only [pw6T, pw6E, pw6L, pw6V, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [pw6_comp hGd i (1, 0), pw6_comp hXtd i z, pw6_decomp (fun w => X τ w i) z z,
    pw6_lap_comp (X τ) hXt i z]
  ring

theorem pwDmuDivFree_proved (ν μ : ℝ) : PwDmuDivFree ν μ := by
  intro X hX hdiv τ y
  have hGd : ∀ t z, DifferentiableAt ℝ (fun x : ℝ × Space => X x.1 x.2) (t, z) :=
    fun t z => hX.differentiable (by simp) (t, z)
  have hXt : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X t) := fun t =>
    hX.comp (contDiff_const.prodMk contDiff_id)
  have hgi : ∀ i : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2 i) :=
    fun i => (contDiff_piLp 2).1 hX i
  have hVi : ∀ i : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => X τ w i) :=
    fun i => (contDiff_piLp 2).1 (hXt τ) i
  have hXtd : ∀ t z, DifferentiableAt ℝ (X t) z := fun t z =>
    (hGd t z).comp z ((differentiableAt_const t).prodMk differentiableAt_id)
  have hdivτ : ∀ z, ∑ i : Fin 3, fderiv ℝ (fun w => X τ w i) z (coordinateVector i) = 0 :=
    fun z => (Finset.sum_congr rfl fun i _ =>
      (pw6_physPd_apply (X τ) i i z (hXtd τ z)).symm).trans (hdiv τ z)
  -- differentiability of the four pieces
  have hTd : ∀ i : Fin 3, Differentiable ℝ (pw6T X τ i) := fun i =>
    ((pw6_dfderiv (hgi i)).comp ((differentiable_const τ).prodMk differentiable_id)).clm_apply
      (differentiable_const _)
  have hEd : ∀ i : Fin 3, Differentiable ℝ (pw6E X τ i) := fun i => by
    unfold pw6E
    exact Differentiable.fun_sum fun k _ =>
      ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiable).mul
        ((pw6_dfderiv (hVi i)).clm_apply (differentiable_const _))
  have hLd : ∀ i : Fin 3, Differentiable ℝ (pw6L X τ i) := fun i => by
    have hF1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (fun w => X τ w i)) :=
      (hVi i).fderiv_right (by simp)
    have hF2 := pw6_dfderiv hF1
    unfold pw6L
    exact Differentiable.fun_sum fun j _ =>
      ((hF2.clm_apply (differentiable_const _)).clm_apply (differentiable_const _))
  have hVd : ∀ i : Fin 3, Differentiable ℝ (pw6V X τ i) := fun i =>
    (hVi i).differentiable (by simp)
  have hDiffComp : ∀ i : Fin 3, Differentiable ℝ (fun z => physDmu ν μ X τ z i) := fun i => by
    have hfe : (fun z => physDmu ν μ X τ z i) = fun z => pw6T X τ i z +
        (-(1 / 2 : ℝ)) * pw6E X τ i z + (-ν) * pw6L X τ i z + (μ - 1 / 2) * pw6V X τ i z :=
      funext fun z => pw6_component ν μ X hX τ i z
    rw [hfe]
    exact (((hTd i).add ((hEd i).const_mul _)).add ((hLd i).const_mul _)).add
      ((hVd i).const_mul _)
  have hPDdiff : DifferentiableAt ℝ (physDmu ν μ X τ) y :=
    (differentiableAt_piLp 2).2 fun i => hDiffComp i y
  have hPD : ∀ i : Fin 3, physPd (physDmu ν μ X τ) i y i =
      fderiv ℝ (fun z => physDmu ν μ X τ z i) y (coordinateVector i) :=
    fun i => pw6_physPd_apply _ i i y hPDdiff
  have hsplit : ∀ i : Fin 3, fderiv ℝ (fun z => physDmu ν μ X τ z i) y (coordinateVector i) =
      fderiv ℝ (pw6T X τ i) y (coordinateVector i) + (-(1 / 2 : ℝ)) *
        fderiv ℝ (pw6E X τ i) y (coordinateVector i) + (-ν) *
        fderiv ℝ (pw6L X τ i) y (coordinateVector i) + (μ - 1 / 2) *
        fderiv ℝ (pw6V X τ i) y (coordinateVector i) := by
    intro i
    have hfe : (fun z => physDmu ν μ X τ z i) = fun z => pw6T X τ i z +
        (-(1 / 2 : ℝ)) * pw6E X τ i z + (-ν) * pw6L X τ i z + (μ - 1 / 2) * pw6V X τ i z :=
      funext fun z => pw6_component ν μ X hX τ i z
    rw [hfe]
    exact pw6_split _ _ _ _ _ _ _ (hTd i) (hEd i) (hLd i) (hVd i) y (coordinateVector i)
  -- the time part
  have hT : ∑ i : Fin 3, fderiv ℝ (pw6T X τ i) y (coordinateVector i) = 0 := by
    have hTi : ∀ i : Fin 3, fderiv ℝ (pw6T X τ i) y (coordinateVector i) =
        fderiv ℝ (fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i)) (τ, y) (1, 0) (0, coordinateVector i) := by
      intro i
      have hd : DifferentiableAt ℝ (fun x : ℝ × Space =>
          fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (1, 0)) (τ, y) :=
        ((pw6_dfderiv (hgi i)) (τ, y)).clm_apply (differentiableAt_const _)
      have h1 : fderiv ℝ (pw6T X τ i) y (coordinateVector i) = fderiv ℝ
          (fun x : ℝ × Space => fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (1, 0)) (τ, y)
          (0, coordinateVector i) :=
        pw6_chain_slice (H := fun x : ℝ × Space => fderiv ℝ (fun x : ℝ × Space => X x.1 x.2 i) x (1, 0))
          hd (coordinateVector i)
      rw [h1, pw6_apply_const ((pw6_dfderiv (hgi i)) (τ, y)) (1, 0) (0, coordinateVector i)]
      exact pw6_symm (hgi i) (τ, y) (0, coordinateVector i) (1, 0)
    rw [Finset.sum_congr rfl fun i _ => hTi i]
    exact pw6_time_sum X hX hdiv τ y
  -- the Euler part
  have hE : ∑ i : Fin 3, fderiv ℝ (pw6E X τ i) y (coordinateVector i) = 0 := by
    have hEi : ∀ i : Fin 3, fderiv ℝ (pw6E X τ i) y (coordinateVector i) =
        ∑ k : Fin 3, (coordinateVector i k * fderiv ℝ (fun w => X τ w i) y (coordinateVector k) +
          y k * fderiv ℝ (fderiv ℝ (fun w => X τ w i)) y (coordinateVector i) (coordinateVector k)) :=
      fun i => pw6_E_deriv (fun w => X τ w i) (hVi i) y (coordinateVector i)
    have hL1 : ∀ k : Fin 3, ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (fun w => X τ w i)) y
        (coordinateVector k) (coordinateVector i) = 0 :=
      fun k => pw6_L1 (fun i w => X τ w i) hVi hdivτ y k
    have hsym : ∀ i k : Fin 3, fderiv ℝ (fderiv ℝ (fun w => X τ w i)) y (coordinateVector i)
        (coordinateVector k) = fderiv ℝ (fderiv ℝ (fun w => X τ w i)) y (coordinateVector k)
          (coordinateVector i) :=
      fun i k => pw6_symm (hVi i) y (coordinateVector i) (coordinateVector k)
    have h0 : fderiv ℝ (fun w => X τ w 0) y (coordinateVector 0) +
        fderiv ℝ (fun w => X τ w 1) y (coordinateVector 1) +
        fderiv ℝ (fun w => X τ w 2) y (coordinateVector 2) = 0 := by
      have := hdivτ y
      rwa [Fin.sum_univ_three] at this
    have hL1' : ∀ k : Fin 3, fderiv ℝ (fderiv ℝ (fun w => X τ w 0)) y (coordinateVector k)
        (coordinateVector 0) + fderiv ℝ (fderiv ℝ (fun w => X τ w 1)) y (coordinateVector k)
        (coordinateVector 1) + fderiv ℝ (fderiv ℝ (fun w => X τ w 2)) y (coordinateVector k)
        (coordinateVector 2) = 0 := by
      intro k
      have := hL1 k
      rwa [Fin.sum_univ_three] at this
    rw [Finset.sum_congr rfl fun i _ => hEi i]
    simp only [Fin.sum_univ_three]
    simp (config := { decide := true }) [pw6_cv, Fin.sum_univ_three]
    linear_combination h0 + y 0 * (hL1' 0 + hsym 0 0 + hsym 1 0 + hsym 2 0)
      + y 1 * (hL1' 1 + hsym 0 1 + hsym 1 1 + hsym 2 1)
      + y 2 * (hL1' 2 + hsym 0 2 + hsym 1 2 + hsym 2 2)
  -- the Laplacian part
  have hL : ∑ i : Fin 3, fderiv ℝ (pw6L X τ i) y (coordinateVector i) = 0 := by
    have hLi : ∀ i : Fin 3, fderiv ℝ (pw6L X τ i) y (coordinateVector i) =
        ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ (fun w => X τ w i))) y (coordinateVector i)
          (coordinateVector j) (coordinateVector j) := by
      intro i
      have hF1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (fun w => X τ w i)) :=
        (hVi i).fderiv_right (by simp)
      have hd : ∀ j : Fin 3, DifferentiableAt ℝ (fun z =>
          fderiv ℝ (fderiv ℝ (fun w => X τ w i)) z (coordinateVector j) (coordinateVector j)) y :=
        fun j => (((pw6_dfderiv hF1) y).clm_apply (differentiableAt_const _)).clm_apply
          (differentiableAt_const _)
      unfold pw6L
      rw [fderiv_fun_sum (fun j _ => hd j), sum_apply]
      exact Finset.sum_congr rfl fun j _ =>
        pw6_apply2 ((pw6_dfderiv hF1) y) (coordinateVector j) (coordinateVector j) (coordinateVector i)
    rw [Finset.sum_congr rfl fun i _ => hLi i, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.sum_congr rfl fun i _ => pw6_sym_ijj (fun w => X τ w i) (hVi i) y i j]
    exact pw6_L3 (fun i w => X τ w i) hVi hdivτ y j
  have hV : ∑ i : Fin 3, fderiv ℝ (pw6V X τ i) y (coordinateVector i) = 0 := hdivτ y
  have hsum : ∑ i : Fin 3, physPd (physDmu ν μ X τ) i y i =
      ∑ i : Fin 3, (fderiv ℝ (pw6T X τ i) y (coordinateVector i) + (-(1 / 2 : ℝ)) *
        fderiv ℝ (pw6E X τ i) y (coordinateVector i) + (-ν) *
        fderiv ℝ (pw6L X τ i) y (coordinateVector i) + (μ - 1 / 2) *
        fderiv ℝ (pw6V X τ i) y (coordinateVector i)) :=
    Finset.sum_congr rfl fun i _ => by rw [hPD i, hsplit i]
  rw [hsum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hT, hE, hL, hV]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
