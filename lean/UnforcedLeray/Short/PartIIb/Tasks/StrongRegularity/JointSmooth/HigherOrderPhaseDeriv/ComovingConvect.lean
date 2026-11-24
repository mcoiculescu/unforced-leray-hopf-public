import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving

set_option autoImplicit false

noncomputable section

open scoped ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

namespace ComovConvSub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Generic iterated directional jet (same recursion as `dirSpatialJet`, any codomain). -/
def gJet (F : Space → E) : List Space → Space → E
  | [] => F
  | w :: ws => fun y => fderiv ℝ (gJet F ws) y w

theorem gJet_nil (F : Space → E) : gJet F [] = F := rfl

theorem gJet_space (F : (Space → Space)) : ∀ ws : List Space, dirSpatialJet F ws = gJet F ws
  | [] => rfl
  | w :: ws => by
      show (fun y => fderiv ℝ (dirSpatialJet F ws) y w) = (fun y => fderiv ℝ (gJet F ws) y w)
      rw [gJet_space F ws]

/-- Directional derivative of a function in a fixed direction. -/
def Dw (w : Space) (P : Space → E) : Space → E := fun y => fderiv ℝ P y w

theorem gJet_append (P : Space → E) (w : Space) :
    ∀ ws : List Space, gJet (gJet P [w]) ws = gJet P (ws ++ [w])
  | [] => rfl
  | v :: r => by
      show (fun y => fderiv ℝ (gJet (gJet P [w]) r) y v) =
        (fun y => fderiv ℝ (gJet P (r ++ [w])) y v)
      rw [gJet_append P w r]

theorem gJet_Dw_append (P : Space → E) (w : Space) (ws : List Space) :
    gJet P (ws ++ [w]) = gJet (Dw w P) ws :=
  (gJet_append P w ws).symm

theorem contDiff_gJet {F : Space → E} (hF : ContDiff ℝ ∞ F) :
    ∀ ws : List Space, ContDiff ℝ ∞ (gJet F ws)
  | [] => hF
  | w :: ws => by
      change ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (gJet F ws) y w)
      exact ((contDiff_infty_iff_fderiv.1 (contDiff_gJet hF ws)).2).clm_apply contDiff_const

theorem contDiff_Dw (w : Space) {P : Space → E} (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (Dw w P) :=
  contDiff_gJet hP [w]

theorem gJet_add {F G : Space → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ∀ ws : List Space, gJet (F + G) ws = gJet F ws + gJet G ws
  | [] => rfl
  | w :: ws => by
      have h1 : Differentiable ℝ (gJet F ws) := (contDiff_gJet hF ws).differentiable (by simp)
      have h2 : Differentiable ℝ (gJet G ws) := (contDiff_gJet hG ws).differentiable (by simp)
      funext y
      show fderiv ℝ (gJet (F + G) ws) y w = fderiv ℝ (gJet F ws) y w + fderiv ℝ (gJet G ws) y w
      rw [gJet_add hF hG ws]
      show fderiv ℝ (fun x => gJet F ws x + gJet G ws x) y w =
        fderiv ℝ (gJet F ws) y w + fderiv ℝ (gJet G ws) y w
      exact congrArg (fun M : Space →L[ℝ] E => M w) ((h1 y).hasFDerivAt.add (h2 y).hasFDerivAt).fderiv

theorem gJet_smul (c : ℝ) {F : Space → E} (hF : ContDiff ℝ ∞ F) :
    ∀ ws : List Space, gJet (c • F) ws = c • gJet F ws
  | [] => rfl
  | w :: ws => by
      have h1 : Differentiable ℝ (gJet F ws) := (contDiff_gJet hF ws).differentiable (by simp)
      funext y
      show fderiv ℝ (gJet (c • F) ws) y w = c • fderiv ℝ (gJet F ws) y w
      rw [gJet_smul c hF ws, fderiv_const_smul (h1 y) c]
      rfl

theorem Dw_add {F G : Space → E} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (w : Space) : Dw w (fun y => F y + G y) = fun y => Dw w F y + Dw w G y := by
  funext y
  show fderiv ℝ (fun y => F y + G y) y w = fderiv ℝ F y w + fderiv ℝ G y w
  exact congrArg (fun M : Space →L[ℝ] E => M w) ((hF y).hasFDerivAt.add (hG y).hasFDerivAt).fderiv

theorem Dw_smul {c : Space → ℝ} {G : Space → E} (hc : Differentiable ℝ c)
    (hG : Differentiable ℝ G) (w : Space) :
    Dw w (fun y => c y • G y) = fun y => Dw w c y • G y + c y • Dw w G y := by
  funext y
  show fderiv ℝ (fun y => c y • G y) y w = fderiv ℝ c y w • G y + c y • fderiv ℝ G y w
  have hh : fderiv ℝ (fun y => c y • G y) y w =
      (c y • fderiv ℝ G y + (fderiv ℝ c y).smulRight (G y)) w :=
    congrArg (fun M : Space →L[ℝ] E => M w) ((hc y).hasFDerivAt.smul (hG y).hasFDerivAt).fderiv
  rw [hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

/-- Comoving jet derivative for a general codomain (same shape as `HasComovingJetDeriv`). -/
def GComov (F F' : ℝ → Space → E) : Prop :=
  ∀ (ws : List Space) (τ : ℝ) (y : Space),
    HasDerivAt (fun t : ℝ => gJet (F (τ + t)) ws (Real.exp (-t / 2) • y))
      (gJet (F' τ) ws y + ((ws.length : ℝ) / 2) • gJet (F τ) ws y) 0

theorem gComov_space_iff {V V' : ℝ → (Space → Space)} :
    GComov V V' ↔ HasComovingJetDeriv V V' := by
  unfold GComov HasComovingJetDeriv
  simp only [gJet_space]

theorem gComov_Dw {F F' : ℝ → Space → E} (hF : ∀ τ, ContDiff ℝ ∞ (F τ))
    (hF' : ∀ τ, ContDiff ℝ ∞ (F' τ)) (w : Space) (h : GComov F F') :
    GComov (fun τ => Dw w (F τ)) (fun τ => Dw w (F' τ) + (1 / 2 : ℝ) • Dw w (F τ)) := by
  unfold GComov
  intro ws τ y
  have hd := h (ws ++ [w]) τ y
  have hfun : (fun t : ℝ => gJet (Dw w (F (τ + t))) ws (Real.exp (-t / 2) • y)) =
      fun t : ℝ => gJet (F (τ + t)) (ws ++ [w]) (Real.exp (-t / 2) • y) := by
    funext t
    rw [gJet_Dw_append]
  have hlin : gJet (Dw w (F' τ) + (1 / 2 : ℝ) • Dw w (F τ)) ws =
      gJet (Dw w (F' τ)) ws + (1 / 2 : ℝ) • gJet (Dw w (F τ)) ws := by
    rw [gJet_add (G := (1 / 2 : ℝ) • Dw w (F τ)) (contDiff_Dw w (hF' τ))
        ((contDiff_Dw w (hF τ)).const_smul (1 / 2 : ℝ)),
      gJet_smul (1 / 2 : ℝ) (contDiff_Dw w (hF τ))]
  have hval : gJet (Dw w (F' τ) + (1 / 2 : ℝ) • Dw w (F τ)) ws y +
      ((ws.length : ℝ) / 2) • gJet (Dw w (F τ)) ws y =
      gJet (F' τ) (ws ++ [w]) y + (((ws ++ [w]).length : ℝ) / 2) • gJet (F τ) (ws ++ [w]) y := by
    rw [hlin, ← gJet_Dw_append, ← gJet_Dw_append]
    simp only [Pi.add_apply, Pi.smul_apply, List.length_append, List.length_singleton,
      Nat.cast_add, Nat.cast_one]
    module
  have hd2 : HasDerivAt (fun t : ℝ => gJet (Dw w (F (τ + t))) ws (Real.exp (-t / 2) • y))
      (gJet (F' τ) (ws ++ [w]) y + (((ws ++ [w]).length : ℝ) / 2) • gJet (F τ) (ws ++ [w]) y) 0 := by
    rw [hfun]
    exact hd
  rw [← hval] at hd2
  exact hd2

theorem prod_claim (ws : List Space) :
    ∀ (f f' : ℝ → Space → ℝ) (g g' : ℝ → Space → E),
      (∀ τ, ContDiff ℝ ∞ (f τ)) → (∀ τ, ContDiff ℝ ∞ (f' τ)) →
      (∀ τ, ContDiff ℝ ∞ (g τ)) → (∀ τ, ContDiff ℝ ∞ (g' τ)) →
      GComov f f' → GComov g g' → ∀ (τ : ℝ) (y : Space),
      HasDerivAt
        (fun t : ℝ => gJet (fun y' => f (τ + t) y' • g (τ + t) y') ws (Real.exp (-t / 2) • y))
        (gJet (fun y' => f' τ y' • g τ y' + f τ y' • g' τ y') ws y +
          ((ws.length : ℝ) / 2) • gJet (fun y' => f τ y' • g τ y') ws y) 0 := by
  induction ws using List.reverseRecOn with
  | nil =>
    intro f f' g g' hf hf' hg hg' Df Dg τ y
    have h1 := Df [] τ y
    have h2 := Dg [] τ y
    simp only [gJet_nil, List.length_nil, Nat.cast_zero, zero_div, zero_smul, add_zero] at h1 h2 ⊢
    convert h1.smul h2 using 1
    all_goals (try simp only [add_zero, neg_zero, zero_div, Real.exp_zero, one_smul])
    all_goals (try abel)
  | append_singleton ws w ih =>
    intro f f' g g' hf hf' hg hg' Df Dg τ y
    have hdf : ∀ s, Differentiable ℝ (f s) := fun s => (hf s).differentiable (by simp)
    have hdg : ∀ s, Differentiable ℝ (g s) := fun s => (hg s).differentiable (by simp)
    have hdf' : ∀ s, Differentiable ℝ (f' s) := fun s => (hf' s).differentiable (by simp)
    have hdg' : ∀ s, Differentiable ℝ (g' s) := fun s => (hg' s).differentiable (by simp)
    have dfw := gComov_Dw hf hf' w Df
    have dgw := gComov_Dw hg hg' w Dg
    have hA := ih (fun s => Dw w (f s)) (fun s => Dw w (f' s) + (1 / 2 : ℝ) • Dw w (f s)) g g'
      (fun s => contDiff_Dw w (hf s))
      (fun s => (contDiff_Dw w (hf' s)).add ((contDiff_Dw w (hf s)).const_smul (1 / 2 : ℝ)))
      hg hg' dfw Dg τ y
    have hB := ih f f' (fun s => Dw w (g s)) (fun s => Dw w (g' s) + (1 / 2 : ℝ) • Dw w (g s))
      hf hf' (fun s => contDiff_Dw w (hg s))
      (fun s => (contDiff_Dw w (hg' s)).add ((contDiff_Dw w (hg s)).const_smul (1 / 2 : ℝ)))
      Df dgw τ y
    have hpt : ∀ s, Dw w (fun y' => f s y' • g s y') =
        (fun y' => Dw w (f s) y' • g s y') + (fun y' => f s y' • Dw w (g s) y') := by
      intro s
      rw [Dw_smul (hdf s) (hdg s) w]
      rfl
    have split : ∀ s, gJet (fun y' => f s y' • g s y') (ws ++ [w]) =
        gJet (fun y' => Dw w (f s) y' • g s y') ws + gJet (fun y' => f s y' • Dw w (g s) y') ws := by
      intro s
      rw [gJet_Dw_append, hpt s,
        gJet_add (F := fun y' => Dw w (f s) y' • g s y') (G := fun y' => f s y' • Dw w (g s) y')
          ((contDiff_Dw w (hf s)).smul (hg s)) ((hf s).smul (contDiff_Dw w (hg s))) ws]
    have hZ : gJet (fun y' => f τ y' • g τ y') (ws ++ [w]) y =
        gJet (fun y' => Dw w (f τ) y' • g τ y') ws y + gJet (fun y' => f τ y' • Dw w (g τ) y') ws y :=
      congrFun (split τ) y
    have dP1 : Differentiable ℝ (fun y' => f' τ y' • g τ y') :=
      ((hf' τ).smul (hg τ)).differentiable (by simp)
    have dP2 : Differentiable ℝ (fun y' => f τ y' • g' τ y') :=
      ((hf τ).smul (hg' τ)).differentiable (by simp)
    have hPd : Dw w (fun y' => f' τ y' • g τ y' + f τ y' • g' τ y') =
        (fun y' => Dw w (f' τ) y' • g τ y' + f' τ y' • Dw w (g τ) y') +
          (fun y' => Dw w (f τ) y' • g' τ y' + f τ y' • Dw w (g' τ) y') := by
      rw [Dw_add dP1 dP2 w, Dw_smul (hdf' τ) (hdg τ) w, Dw_smul (hdf τ) (hdg' τ) w]
      rfl
    have hP : Dw w (fun y' => f τ y' • g τ y') =
        (fun y' => Dw w (f τ) y' • g τ y') + (fun y' => f τ y' • Dw w (g τ) y') := hpt τ
    have c_a' : ContDiff ℝ ∞ (Dw w (f' τ) + (1 / 2 : ℝ) • Dw w (f τ)) :=
      (contDiff_Dw w (hf' τ)).add ((contDiff_Dw w (hf τ)).const_smul (1 / 2 : ℝ))
    have c_b' : ContDiff ℝ ∞ (Dw w (g' τ) + (1 / 2 : ℝ) • Dw w (g τ)) :=
      (contDiff_Dw w (hg' τ)).add ((contDiff_Dw w (hg τ)).const_smul (1 / 2 : ℝ))
    have c_Pa : ContDiff ℝ ∞ (fun y' => (Dw w (f' τ) + (1 / 2 : ℝ) • Dw w (f τ)) y' • g τ y' +
        Dw w (f τ) y' • g' τ y') :=
      (c_a'.smul (hg τ)).add ((contDiff_Dw w (hf τ)).smul (hg' τ))
    have c_Pb : ContDiff ℝ ∞ (fun y' => f' τ y' • Dw w (g τ) y' +
        f τ y' • (Dw w (g' τ) + (1 / 2 : ℝ) • Dw w (g τ)) y') :=
      ((hf' τ).smul (contDiff_Dw w (hg τ))).add ((hf τ).smul c_b')
    have c_DP' : ContDiff ℝ ∞ (Dw w (fun y' => f' τ y' • g τ y' + f τ y' • g' τ y')) :=
      contDiff_Dw w (((hf' τ).smul (hg τ)).add ((hf τ).smul (hg' τ)))
    have c_DP : ContDiff ℝ ∞ (Dw w (fun y' => f τ y' • g τ y')) :=
      contDiff_Dw w ((hf τ).smul (hg τ))
    have hid : (fun y' => (Dw w (f' τ) + (1 / 2 : ℝ) • Dw w (f τ)) y' • g τ y' +
          Dw w (f τ) y' • g' τ y') +
        (fun y' => f' τ y' • Dw w (g τ) y' +
          f τ y' • (Dw w (g' τ) + (1 / 2 : ℝ) • Dw w (g τ)) y') =
        Dw w (fun y' => f' τ y' • g τ y' + f τ y' • g' τ y') +
          (1 / 2 : ℝ) • Dw w (fun y' => f τ y' • g τ y') := by
      rw [hPd, hP]
      funext y'
      simp only [Pi.add_apply, Pi.smul_apply]
      module
    have hL : gJet (fun y' => (Dw w (f' τ) + (1 / 2 : ℝ) • Dw w (f τ)) y' • g τ y' +
          Dw w (f τ) y' • g' τ y') ws +
        gJet (fun y' => f' τ y' • Dw w (g τ) y' +
          f τ y' • (Dw w (g' τ) + (1 / 2 : ℝ) • Dw w (g τ)) y') ws =
        gJet (Dw w (fun y' => f' τ y' • g τ y' + f τ y' • g' τ y')) ws +
          (1 / 2 : ℝ) • gJet (Dw w (fun y' => f τ y' • g τ y')) ws := by
      rw [← gJet_add c_Pa c_Pb ws, hid,
        gJet_add (G := (1 / 2 : ℝ) • Dw w (fun y' => f τ y' • g τ y')) c_DP' (c_DP.const_smul (1 / 2 : ℝ)) ws,
        gJet_smul _ c_DP ws]
    have hLv := congrFun hL y
    have hDP := congrFun (gJet_Dw_append (fun y' => f τ y' • g τ y') w ws).symm y
    have hDP' := congrFun (gJet_Dw_append (fun y' => f' τ y' • g τ y' + f τ y' • g' τ y') w ws).symm y
    have hsum := hA.add hB
    convert hsum using 1
    · funext t
      exact congrFun (split (τ + t)) _
    · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      simp only [Pi.add_apply, Pi.smul_apply] at hLv
      linear_combination (norm := module) (-1 : ℝ) • hDP' + (-(1 / 2 : ℝ)) • hDP +
        ((ws.length : ℝ) / 2) • hZ + (-1 : ℝ) • hLv

theorem gComov_prod {f f' : ℝ → Space → ℝ} {g g' : ℝ → Space → E}
    (hf : ∀ τ, ContDiff ℝ ∞ (f τ)) (hf' : ∀ τ, ContDiff ℝ ∞ (f' τ))
    (hg : ∀ τ, ContDiff ℝ ∞ (g τ)) (hg' : ∀ τ, ContDiff ℝ ∞ (g' τ))
    (Df : GComov f f') (Dg : GComov g g') :
    GComov (fun τ y => f τ y • g τ y) (fun τ y => f' τ y • g τ y + f τ y • g' τ y) := by
  unfold GComov
  intro ws τ y
  exact prod_claim ws f f' g g' hf hf' hg hg' Df Dg τ y

theorem gJet_clm (L : Space →L[ℝ] ℝ) {F : Space → Space} (hF : ContDiff ℝ ∞ F) :
    ∀ ws : List Space, gJet (fun y => L (F y)) ws = fun y => L (gJet F ws y)
  | [] => rfl
  | w :: ws => by
      have ih := gJet_clm L hF ws
      have hd : Differentiable ℝ (gJet F ws) := (contDiff_gJet hF ws).differentiable (by simp)
      funext y
      show fderiv ℝ (gJet (fun y => L (F y)) ws) y w = L (fderiv ℝ (gJet F ws) y w)
      rw [ih]
      exact congrArg (fun M : Space →L[ℝ] ℝ => M w)
        (L.hasFDerivAt.comp y (hd y).hasFDerivAt).fderiv

theorem gComov_comp (j : Fin 3) {V V' : ℝ → Space → Space} (hV : ∀ τ, ContDiff ℝ ∞ (V τ))
    (hV' : ∀ τ, ContDiff ℝ ∞ (V' τ)) (dV : GComov V V') :
    GComov (fun τ y => V τ y j) (fun τ y => V' τ y j) := by
  unfold GComov
  intro ws τ y
  have e1 : ∀ s, gJet (fun y' => V s y' j) ws =
      fun y' => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (gJet (V s) ws y') :=
    fun s => gJet_clm (EuclideanSpace.proj j) (hV s) ws
  have e1' : ∀ s, gJet (fun y' => V' s y' j) ws =
      fun y' => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (gJet (V' s) ws y') :=
    fun s => gJet_clm (EuclideanSpace.proj j) (hV' s) ws
  have h2 := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (dV ws τ y)
  simp only [e1, e1']
  convert h2 using 1
  all_goals (try simp only [map_add, map_smul])
  all_goals (try rfl)

theorem gComov_partial (j : Fin 3) {W W' : ℝ → Space → Space} (hW : ∀ τ, ContDiff ℝ ∞ (W τ))
    (hW' : ∀ τ, ContDiff ℝ ∞ (W' τ)) (dW : GComov W W') :
    GComov (fun τ => spatialPartial j (W τ))
      (fun τ => spatialPartial j (W' τ) + (1 / 2 : ℝ) • spatialPartial j (W τ)) :=
  gComov_Dw hW hW' (EuclideanSpace.single j 1) dW

end ComovConvSub

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.ComovConvSub in
theorem comovingConvectRule_proof : UnforcedLeray.Short.IIb.ComovingConvectRule := by
  unfold UnforcedLeray.Short.IIb.ComovingConvectRule
  intro V V' W W' hV hV' hW hW' dV dW
  have cP : ∀ (j : Fin 3) (F : (Space → Space)), ContDiff ℝ ∞ F →
      ContDiff ℝ ∞ (spatialPartial j F) :=
    fun j F hF => JointSmoothSub.contDiff_infty_dirSpatialJet hF [EuclideanSpace.single j 1]
  have cC : ∀ (j : Fin 3) (F : (Space → Space)), ContDiff ℝ ∞ F →
      ContDiff ℝ ∞ (fun y => F y j) :=
    fun j F hF => (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hF
  have key : ∀ j : Fin 3, HasComovingJetDeriv (fun τ y => V τ y j • spatialPartial j (W τ) y)
      (fun τ y => V' τ y j • spatialPartial j (W τ) y +
        V τ y j • (spatialPartial j (W' τ) y + (1 / 2 : ℝ) • spatialPartial j (W τ) y)) := by
    intro j
    rw [← gComov_space_iff]
    exact gComov_prod (fun τ => cC j (V τ) (hV τ)) (fun τ => cC j (V' τ) (hV' τ))
      (fun τ => cP j (W τ) (hW τ))
      (fun τ => (cP j (W' τ) (hW' τ)).add ((cP j (W τ) (hW τ)).const_smul (1 / 2 : ℝ)))
      (gComov_comp j hV hV' (gComov_space_iff.mpr dV))
      (gComov_partial j hW hW' (gComov_space_iff.mpr dW))
  have hsum := ComovingTowerSub.hasComovingJetDeriv_sum (Finset.univ : Finset (Fin 3))
    (F := fun j τ y => V τ y j • spatialPartial j (W τ) y)
    (F' := fun j τ y => V' τ y j • spatialPartial j (W τ) y +
      V τ y j • (spatialPartial j (W' τ) y + (1 / 2 : ℝ) • spatialPartial j (W τ) y))
    (fun j _ τ => (cC j (V τ) (hV τ)).smul (cP j (W τ) (hW τ)))
    (fun j _ τ => ((cC j (V' τ) (hV' τ)).smul (cP j (W τ) (hW τ))).add
      ((cC j (V τ) (hV τ)).smul ((cP j (W' τ) (hW' τ)).add
        ((cP j (W τ) (hW τ)).const_smul (1 / 2 : ℝ)))))
    (fun j _ => key j)
  have e1 : (fun τ => spatialConvect (V τ) (W τ)) =
      fun τ y => ∑ j ∈ (Finset.univ : Finset (Fin 3)), V τ y j • spatialPartial j (W τ) y := by
    funext τ y
    exact HigherPhaseSub.spatialConvect_eq_sum (V τ) (W τ) y
  have e2 : (fun τ => spatialConvect (V' τ) (W τ) + spatialConvect (V τ) (W' τ) +
      (1 / 2 : ℝ) • spatialConvect (V τ) (W τ)) =
      fun τ y => ∑ j ∈ (Finset.univ : Finset (Fin 3)),
        (V' τ y j • spatialPartial j (W τ) y +
          V τ y j • (spatialPartial j (W' τ) y + (1 / 2 : ℝ) • spatialPartial j (W τ) y)) := by
    funext τ y
    simp only [Pi.add_apply, Pi.smul_apply, HigherPhaseSub.spatialConvect_eq_sum,
      Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    module
  rw [e1, e2]
  exact hsum
