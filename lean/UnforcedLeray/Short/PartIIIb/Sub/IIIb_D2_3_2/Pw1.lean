import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.PointwiseDefs

/-!
# Euler part of `pwProduct` (source 4228-4231)

Frozen-time spatial identity `E[U,X] = [EU,X] + [U,EX] - [U,X]` with `E f = y·∇f`, which is the
term `-½ y·∇[U,X]` of `D_μ` in `PwProduct`.  The full `PwProduct` (target `pwProduct_proved`) is not
yet proved in this file; see the task report for the remaining leaves.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pw1_clm_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Space →L[ℝ] F) (v : Space) :
    L v = ∑ j : Fin 3, v j • L (coordinateVector j) := by
  conv_lhs => rw [show v = ∑ j : Fin 3, v j • coordinateVector j from by
    ext k; simp [coordinateVector, Pi.single_apply]]
  simp [map_sum, map_smul]

/-- Euler commutator identity at a point, for frozen-time smooth spatial fields. -/
theorem pw1_euler (U X : Space → Space) (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (y : Space) :
    fderiv ℝ (physBracket U X) y y =
      physBracket (fun z => fderiv ℝ U z z) X y + physBracket U (fun z => fderiv ℝ X z z) y -
        physBracket U X y := by
  have hue : DifferentiableAt ℝ U y := (hU.differentiable (by simp)) y
  have hXe : DifferentiableAt ℝ X y := (hX.differentiable (by simp)) y
  have hud : DifferentiableAt ℝ (fderiv ℝ U) y :=
    ((hU.fderiv_right (m := 1) (by simp)).differentiable (by simp)) y
  have hXd : DifferentiableAt ℝ (fderiv ℝ X) y :=
    ((hX.fderiv_right (m := 1) (by simp)).differentiable (by simp)) y
  have hsymU : ∀ v w, fderiv ℝ (fderiv ℝ U) y v w = fderiv ℝ (fderiv ℝ U) y w v :=
    (hU.contDiffAt.isSymmSndFDerivAt (by simp))
  have hsymX : ∀ v w, fderiv ℝ (fderiv ℝ X) y v w = fderiv ℝ (fderiv ℝ X) y w v :=
    (hX.contDiffAt.isSymmSndFDerivAt (by simp))
  have hEU : ∀ w, fderiv ℝ (fun z => fderiv ℝ U z z) y w =
      fderiv ℝ U y w + fderiv ℝ (fderiv ℝ U) y w y := by
    intro w
    rw [show (fun z => fderiv ℝ U z z) = fun z => (fderiv ℝ U z) (id z) from rfl,
      fderiv_clm_apply hud differentiableAt_id]
    simp
  have hEX : ∀ w, fderiv ℝ (fun z => fderiv ℝ X z z) y w =
      fderiv ℝ X y w + fderiv ℝ (fderiv ℝ X) y w y := by
    intro w
    rw [show (fun z => fderiv ℝ X z z) = fun z => (fderiv ℝ X z) (id z) from rfl,
      fderiv_clm_apply hXd differentiableAt_id]
    simp
  have hh : ∀ w, fderiv ℝ (physBracket U X) y w =
      fderiv ℝ (fderiv ℝ X) y w (U y) + fderiv ℝ X y (fderiv ℝ U y w) -
        (fderiv ℝ (fderiv ℝ U) y w (X y) + fderiv ℝ U y (fderiv ℝ X y w)) := by
    intro w
    have hfun : physBracket U X = fun z => fderiv ℝ X z (U z) - fderiv ℝ U z (X z) := rfl
    rw [hfun, fderiv_fun_sub (hXd.clm_apply hue) (hud.clm_apply hXe),
      fderiv_clm_apply hXd hue, fderiv_clm_apply hud hXe]
    simp
    abel
  have h1 : physBracket (fun z => fderiv ℝ U z z) X y =
      fderiv ℝ X y (fderiv ℝ U y y) - (fderiv ℝ U y (X y) +
        fderiv ℝ (fderiv ℝ U) y (X y) y) := by
    simp only [physBracket]
    rw [hEU (X y)]
  have h2 : physBracket U (fun z => fderiv ℝ X z z) y =
      (fderiv ℝ (fderiv ℝ X) y (U y) y + fderiv ℝ X y (U y)) - fderiv ℝ U y (fderiv ℝ X y y) := by
    simp only [physBracket]
    rw [hEX (U y)]
    abel
  have h3 : physBracket U X y = fderiv ℝ X y (U y) - fderiv ℝ U y (X y) := rfl
  rw [hh y, h1, h2, h3]
  have hs1 := hsymX y (U y)
  have hs2 := hsymU y (X y)
  rw [hs1, hs2]
  abel

/-! ## Spatial calculus helpers -/

abbrev Smo {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f

theorem smo_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (h : Smo f) : Smo (fderiv ℝ f) :=
  h.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)

theorem smo_diff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (h : Smo f) (y : E) : DifferentiableAt ℝ f y :=
  (h.differentiable (by simp)) y

theorem ev1 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : Space → (Space →L[ℝ] G)} {y : Space} (hc : DifferentiableAt ℝ c y) (v w : Space) :
    fderiv ℝ (fun z => c z v) y w = fderiv ℝ c y w v := by
  rw [fderiv_clm_apply hc (differentiableAt_const v)]; simp

theorem ev2 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : Space → (Space →L[ℝ] G)} {u : Space → Space} {y : Space}
    (hc : DifferentiableAt ℝ c y) (hu : DifferentiableAt ℝ u y) (w : Space) :
    fderiv ℝ (fun z => c z (u z)) y w = fderiv ℝ c y w (u y) + c y (fderiv ℝ u y w) := by
  rw [fderiv_clm_apply hc hu]; simp [add_comm]

theorem pw1_dbr (U X : Space → Space) (hU : Smo U) (hX : Smo X) (z w : Space) :
    fderiv ℝ (physBracket U X) z w =
      fderiv ℝ (fderiv ℝ X) z w (U z) + fderiv ℝ X z (fderiv ℝ U z w) -
        (fderiv ℝ (fderiv ℝ U) z w (X z) + fderiv ℝ U z (fderiv ℝ X z w)) := by
  have hue := smo_diff hU z
  have hXe := smo_diff hX z
  have hud := smo_diff (smo_fderiv hU) z
  have hXd := smo_diff (smo_fderiv hX) z
  have hfun : physBracket U X = fun z => fderiv ℝ X z (U z) - fderiv ℝ U z (X z) := rfl
  rw [hfun, fderiv_fun_sub (hXd.clm_apply hue) (hud.clm_apply hXe),
    fderiv_clm_apply hXd hue, fderiv_clm_apply hud hXe]
  simp
  abel

theorem pw1_ev3 (U : Space → Space) (hU : Smo U) (y a b c : Space) :
    fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ U) z b c) y a =
      fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y a b c := by
  have hT := smo_diff (smo_fderiv (smo_fderiv hU)) y
  have hc' : DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ U) z b) y :=
    hT.clm_apply (differentiableAt_const b)
  have := ev1 (c := fun z => fderiv ℝ (fderiv ℝ U) z b) hc' c a
  rw [this, ev1 hT b a]

/-- Symmetry of the third derivative in its last two slots. -/
theorem pw1_sym_bc (U : Space → Space) (hU : Smo U) (y a b c : Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y a c b := by
  have hall : ∀ z, fderiv ℝ (fderiv ℝ U) z b c = fderiv ℝ (fderiv ℝ U) z c b := fun z =>
    (hU.contDiffAt.isSymmSndFDerivAt (by simp)) b c
  rw [← pw1_ev3 U hU y a b c, ← pw1_ev3 U hU y a c b]
  have : (fun z => fderiv ℝ (fderiv ℝ U) z b c) = fun z => fderiv ℝ (fderiv ℝ U) z c b :=
    funext hall
  rw [this]

theorem pw1_sym_ab (U : Space → Space) (hU : Smo U) (y a b : Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y a b = fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y b a :=
  ((smo_fderiv hU).contDiffAt.isSymmSndFDerivAt (by simp)) a b

/-- Symmetry of the third derivative in the first and third slots. -/
theorem pw1_sym_ac (U : Space → Space) (hU : Smo U) (y a b c : Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y c b a := by
  calc fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y a b c = fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y b a c := by
        rw [pw1_sym_ab U hU y a b]
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y b c a := pw1_sym_bc U hU y b a c
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y c b a := by rw [pw1_sym_ab U hU y b c]

theorem pw1_hess_br (U X : Space → Space) (hU : Smo U) (hX : Smo X) (y w v : Space) :
    fderiv ℝ (fun z => fderiv ℝ (physBracket U X) z w) y v =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y v w (U y) + fderiv ℝ (fderiv ℝ X) y w (fderiv ℝ U y v) +
        (fderiv ℝ (fderiv ℝ X) y v (fderiv ℝ U y w) + fderiv ℝ X y (fderiv ℝ (fderiv ℝ U) y v w))) -
      (fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y v w (X y) + fderiv ℝ (fderiv ℝ U) y w (fderiv ℝ X y v) +
        (fderiv ℝ (fderiv ℝ U) y v (fderiv ℝ X y w) + fderiv ℝ U y (fderiv ℝ (fderiv ℝ X) y v w))) := by
  have hu := smo_diff hU y
  have hx := smo_diff hX y
  have hdu := smo_diff (smo_fderiv hU) y
  have hdx := smo_diff (smo_fderiv hX) y
  have htu := smo_diff (smo_fderiv (smo_fderiv hU)) y
  have htx := smo_diff (smo_fderiv (smo_fderiv hX)) y
  have hc1 : DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ X) z w) y :=
    htx.clm_apply (differentiableAt_const w)
  have hc3 : DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ U) z w) y :=
    htu.clm_apply (differentiableAt_const w)
  have hu2 : DifferentiableAt ℝ (fun z => fderiv ℝ U z w) y := hdu.clm_apply (differentiableAt_const w)
  have hx2 : DifferentiableAt ℝ (fun z => fderiv ℝ X z w) y := hdx.clm_apply (differentiableAt_const w)
  have hfun : (fun z => fderiv ℝ (physBracket U X) z w) = fun z =>
      (fderiv ℝ (fderiv ℝ X) z w (U z) + fderiv ℝ X z (fderiv ℝ U z w)) -
      (fderiv ℝ (fderiv ℝ U) z w (X z) + fderiv ℝ U z (fderiv ℝ X z w)) :=
    funext fun z => pw1_dbr U X hU hX z w
  rw [hfun]
  rw [fderiv_fun_sub ((hc1.clm_apply hu).fun_add (hdx.clm_apply hu2))
      ((hc3.clm_apply hx).fun_add (hdu.clm_apply hx2)),
    fderiv_fun_add (hc1.clm_apply hu) (hdx.clm_apply hu2),
    fderiv_fun_add (hc3.clm_apply hx) (hdu.clm_apply hx2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [ev2 hc1 hu v, ev2 hdx hu2 v, ev2 hc3 hx v, ev2 hdu hx2 v, ev1 htx w v, ev1 hdu w v,
    ev1 htu w v, ev1 hdx w v]

theorem pw1_physLap (F : Space → Space) (hF : Smo F) (z : Space) :
    physLap F z = ∑ j : Fin 3, fderiv ℝ (fderiv ℝ F) z (coordinateVector j) (coordinateVector j) := by
  unfold physLap physPd2 physPd
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ev1 (smo_diff (smo_fderiv hF) z) _ _

theorem pw1_dLap (F : Space → Space) (hF : Smo F) (z w : Space) :
    fderiv ℝ (physLap F) z w =
      ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ F)) z w (coordinateVector j) (coordinateVector j) := by
  have h : physLap F = fun z => ∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ F) z (coordinateVector j) (coordinateVector j) := funext (pw1_physLap F hF)
  have hT := smo_diff (smo_fderiv (smo_fderiv hF)) z
  rw [h, fderiv_fun_sum (fun j _ => (hT.clm_apply (differentiableAt_const _)).clm_apply
    (differentiableAt_const _))]
  simp only [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => pw1_ev3 F hF z w _ _

theorem pw1_physPd2 (F : Space → Space) (hF : Smo F) (y : Space) (j l : Fin 3) :
    physPd2 F j l y = fderiv ℝ (fderiv ℝ F) y (coordinateVector j) (coordinateVector l) := by
  unfold physPd2 physPd
  exact ev1 (smo_diff (smo_fderiv hF) y) _ _

theorem pw1_cdiff (U X : Space → Space) (hU : Smo U) (hX : Smo X) (y : Space) :
    physCdiff U X y = ∑ j : Fin 3, (fderiv ℝ (fderiv ℝ X) y (coordinateVector j)
        (fderiv ℝ U y (coordinateVector j)) -
      fderiv ℝ (fderiv ℝ U) y (coordinateVector j) (fderiv ℝ X y (coordinateVector j))) := by
  unfold physCdiff
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_sub_distrib]
  simp only [pw1_physPd2 U hU, pw1_physPd2 X hX]
  rw [← pw1_clm_sum (fderiv ℝ (fderiv ℝ X) y (coordinateVector j)) (physPd U j y),
    ← pw1_clm_sum (fderiv ℝ (fderiv ℝ U) y (coordinateVector j)) (physPd X j y)]
  rfl

theorem pw1_laplacian (U X : Space → Space) (hU : Smo U) (hX : Smo X) (y : Space) :
    ∑ j : Fin 3, physPd2 (physBracket U X) j j y =
      physBracket (physLap U) X y + physBracket U (physLap X) y +
        (2 : ℝ) • physCdiff U X y := by
  have hL : ∀ j : Fin 3, physPd2 (physBracket U X) j j y =
      fderiv ℝ (fun z => fderiv ℝ (physBracket U X) z (coordinateVector j)) y (coordinateVector j) :=
    fun j => rfl
  simp only [hL, pw1_hess_br U X hU hX]
  simp only [physBracket, pw1_physLap U hU, pw1_physLap X hX, pw1_dLap U hU, pw1_dLap X hX,
    pw1_cdiff U X hU hX, map_sum, Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    smul_sub, two_smul]
  have e1 : ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y (coordinateVector j) (coordinateVector j)
      (U y) = ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y (U y) (coordinateVector j)
        (coordinateVector j) :=
    Finset.sum_congr rfl fun j _ => pw1_sym_ac X hX y _ _ _
  have e2 : ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y (coordinateVector j) (coordinateVector j)
      (X y) = ∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ U)) y (X y) (coordinateVector j)
        (coordinateVector j) :=
    Finset.sum_congr rfl fun j _ => pw1_sym_ac U hU y _ _ _
  rw [e1, e2]
  abel

/-! ## Time derivatives -/

theorem pw1_hasDeriv_t (X : ℝ → Space → Space) (hX : Smo (fun x : ℝ × Space => X x.1 x.2))
    (τ : ℝ) (z : Space) :
    HasDerivAt (fun t => X t z)
      (fderiv ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, z) ((1 : ℝ), (0 : Space))) τ := by
  have h := (smo_diff hX (τ, z)).hasFDerivAt.comp_hasDerivAt τ
    ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ z))
  simpa [Function.comp_def] using h

theorem pw1_clm_x (X : ℝ → Space → Space) (hX : Smo (fun x : ℝ × Space => X x.1 x.2))
    (τ : ℝ) (z : Space) :
    fderiv ℝ (X τ) z = (fderiv ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h := (smo_diff hX (τ, z)).hasFDerivAt.comp z
    ((hasFDerivAt_const τ z).prodMk (hasFDerivAt_id z))
  have h2 := h.fderiv
  refine ContinuousLinearMap.ext fun v => ?_
  have := congrArg (fun L => L v) h2
  simpa [Function.comp_def] using this

theorem pw1_tau_clm (X : ℝ → Space → Space) (hX : Smo (fun x : ℝ × Space => X x.1 x.2))
    (τ : ℝ) (y : Space) :
    HasDerivAt (fun t => fderiv ℝ (X t) y)
      (fderiv ℝ (fun z => deriv (fun t => X t z) τ) y) τ := by
  set Xj : ℝ × Space → Space := fun x => X x.1 x.2 with hXj
  have hG : Smo (fderiv ℝ Xj) := smo_fderiv hX
  have h1 : HasDerivAt (fun t => fderiv ℝ Xj (t, y))
      (fderiv ℝ (fderiv ℝ Xj) (τ, y) ((1 : ℝ), (0 : Space))) τ := by
    have h := (smo_diff hG (τ, y)).hasFDerivAt.comp_hasDerivAt τ
      ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ y))
    simpa [Function.comp_def] using h
  have h2 := h1.clm_comp (hasDerivAt_const τ (ContinuousLinearMap.inr ℝ ℝ Space))
  have hfun : (fun t => fderiv ℝ (X t) y) = fun t =>
      (fderiv ℝ Xj (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    funext fun t => pw1_clm_x X hX t y
  rw [hfun]
  convert h2 using 1
  -- identify the derivative
  have hd : (fun z => deriv (fun t => X t z) τ) = fun z =>
      fderiv ℝ Xj (τ, z) ((1 : ℝ), (0 : Space)) :=
    funext fun z => (pw1_hasDeriv_t X hX τ z).deriv
  rw [hd]
  refine ContinuousLinearMap.ext fun v => ?_
  have hc : DifferentiableAt ℝ (fun z => fderiv ℝ Xj (τ, z)) y :=
    (smo_diff hG (τ, y)).comp y ((differentiableAt_const τ).prodMk differentiableAt_id)
  have h3 : HasFDerivAt (fun z => fderiv ℝ Xj (τ, z)) _ y :=
    (smo_diff hG (τ, y)).hasFDerivAt.comp y ((hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y))
  rw [fderiv_clm_apply hc (differentiableAt_const _), h3.fderiv]
  have hs := (hX.contDiffAt (x := (τ, y)).isSymmSndFDerivAt (by simp)) ((1 : ℝ), (0 : Space))
    ((0 : ℝ), v)
  simp [hs, fderiv_fun_const]

theorem pw1_tau_bracket (U X : ℝ → Space → Space) (hU : Smo (fun x : ℝ × Space => U x.1 x.2))
    (hX : Smo (fun x : ℝ × Space => X x.1 x.2)) (τ : ℝ) (y : Space) :
    deriv (fun t => physBracket (U t) (X t) y) τ =
      physBracket (fun z => deriv (fun t => U t z) τ) (X τ) y +
        physBracket (U τ) (fun z => deriv (fun t => X t z) τ) y := by
  have hX1 := pw1_tau_clm X hX τ y
  have hU1 := pw1_tau_clm U hU τ y
  have hXt := (pw1_hasDeriv_t X hX τ y).differentiableAt.hasDerivAt
  have hUt := (pw1_hasDeriv_t U hU τ y).differentiableAt.hasDerivAt
  have h := (hX1.clm_apply hUt).sub (hU1.clm_apply hXt)
  have h2 : deriv (fun t => physBracket (U t) (X t) y) τ = _ := h.deriv
  rw [h2]
  simp only [physBracket]
  abel

theorem pw1_smo_slice {F : ℝ → Space → Space} (hF : Smo (fun x : ℝ × Space => F x.1 x.2)) (τ : ℝ) :
    Smo (F τ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

theorem pw1_smo_dt {F : ℝ → Space → Space} (hF : Smo (fun x : ℝ × Space => F x.1 x.2)) (τ : ℝ) :
    Smo (fun z => deriv (fun t => F t z) τ) := by
  have : (fun z => deriv (fun t => F t z) τ) = fun z =>
      fderiv ℝ (fun x : ℝ × Space => F x.1 x.2) (τ, z) ((1 : ℝ), (0 : Space)) :=
    funext fun z => (pw1_hasDeriv_t F hF τ z).deriv
  rw [this]
  exact ((smo_fderiv hF).comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const

theorem pw1_smo_E {F : Space → Space} (hF : Smo F) : Smo (fun z => fderiv ℝ F z z) :=
  (smo_fderiv hF).clm_apply contDiff_id

theorem pw1_smo_lap {F : Space → Space} (hF : Smo F) : Smo (physLap F) := by
  have : physLap F = fun z => ∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ F) z (coordinateVector j) (coordinateVector j) :=
    funext (pw1_physLap F hF)
  rw [this]
  exact ContDiff.sum fun j _ =>
    (((smo_fderiv (smo_fderiv hF)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem pw1_br_left (X : Space → Space) (a b c d : Space → Space) (s r q : ℝ) (y : Space)
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) (hc : DifferentiableAt ℝ c y)
    (hd : DifferentiableAt ℝ d y) :
    physBracket (fun z => a z - s • b z - r • c z + q • d z) X y =
      physBracket a X y - s • physBracket b X y - r • physBracket c X y +
        q • physBracket d X y := by
  have hfd : fderiv ℝ (fun z => a z - s • b z - r • c z + q • d z) y =
      fderiv ℝ a y - s • fderiv ℝ b y - r • fderiv ℝ c y + q • fderiv ℝ d y :=
    (((ha.hasFDerivAt.sub (hb.hasFDerivAt.const_smul s)).sub
      (hc.hasFDerivAt.const_smul r)).add (hd.hasFDerivAt.const_smul q)).fderiv
  simp only [physBracket]
  rw [hfd]
  simp only [map_sub, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  module

theorem pw1_br_right (U : Space → Space) (a b c d : Space → Space) (s r q : ℝ) (y : Space)
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) (hc : DifferentiableAt ℝ c y)
    (hd : DifferentiableAt ℝ d y) :
    physBracket U (fun z => a z - s • b z - r • c z + q • d z) y =
      physBracket U a y - s • physBracket U b y - r • physBracket U c y +
        q • physBracket U d y := by
  have hfd : fderiv ℝ (fun z => a z - s • b z - r • c z + q • d z) y =
      fderiv ℝ a y - s • fderiv ℝ b y - r • fderiv ℝ c y + q • fderiv ℝ d y :=
    (((ha.hasFDerivAt.sub (hb.hasFDerivAt.const_smul s)).sub
      (hc.hasFDerivAt.const_smul r)).add (hd.hasFDerivAt.const_smul q)).fderiv
  simp only [physBracket]
  rw [hfd]
  simp only [map_sub, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  module

theorem pwProduct_proved (ν μ : ℝ) : PwProduct ν μ := by
  intro U X hU hX τ y
  have hUτ := pw1_smo_slice hU τ
  have hXτ := pw1_smo_slice hX τ
  have dU := smo_diff (pw1_smo_dt hU τ) y
  have dX := smo_diff (pw1_smo_dt hX τ) y
  have eU := smo_diff (pw1_smo_E hUτ) y
  have eX := smo_diff (pw1_smo_E hXτ) y
  have lU := smo_diff (pw1_smo_lap hUτ) y
  have lX := smo_diff (pw1_smo_lap hXτ) y
  have uU := smo_diff hUτ y
  have uX := smo_diff hXτ y
  have hDU : physDmu ν 0 U τ = fun z => deriv (fun t => U t z) τ - (1 / 2 : ℝ) • fderiv ℝ (U τ) z z -
      ν • physLap (U τ) z + ((0 : ℝ) - 1 / 2) • U τ z := rfl
  have hDX : physDmu ν (μ + 1) X τ = fun z => deriv (fun t => X t z) τ -
      (1 / 2 : ℝ) • fderiv ℝ (X τ) z z - ν • physLap (X τ) z + ((μ + 1) - 1 / 2) • X τ z := rfl
  rw [hDU, hDX, pw1_br_left (X τ) _ _ _ _ _ _ _ y dU eU lU uU,
    pw1_br_right (U τ) _ _ _ _ _ _ _ y dX eX lX uX]
  have hB : physDmu ν μ (fun τ' y' => physBracket (U τ') (X τ') y') τ y =
      deriv (fun t => physBracket (U t) (X t) y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (physBracket (U τ) (X τ)) y y -
        ν • ∑ j : Fin 3, physPd2 (physBracket (U τ) (X τ)) j j y +
        (μ - 1 / 2) • physBracket (U τ) (X τ) y := rfl
  rw [hB, pw1_tau_bracket U X hU hX τ y, pw1_euler (U τ) (X τ) hUτ hXτ y,
    pw1_laplacian (U τ) (X τ) hUτ hXτ y]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
