import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel flatDt flatLap lapP)

private abbrev TT : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

private theorem pd_eq_fderiv' (ζ : ℝ → ℝ × ℝ → ℝ)
    (hF : ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2))
    (j : Fin 2) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd j (ζ s) x =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) (0, B0579.dir j) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) (s, x) :=
    (hF.differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => (s, y)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right s x
  have h2 := hd.hasFDerivAt.comp x h1
  have h3 : (ζ s) = (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) ∘ (fun y : ℝ × ℝ => (s, y)) := rfl
  unfold B0579.pd
  rw [h3, h2.fderiv]
  rfl

private theorem pd_contDiff' (ζ : ℝ → ℝ × ℝ → ℝ)
    (hF : ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2))
    (j : Fin 2) :
    ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (ζ p.1) p.2) := by
  have : (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (ζ p.1) p.2) =
      fun p => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => ζ p.1 p.2) p (0, B0579.dir j) := by
    funext p; exact pd_eq_fderiv' ζ hF j p.1 p.2
  rw [this]
  exact (hF.fderiv_right (m := TT) (by simp)).clm_apply contDiff_const

/-- time derivative as a Fréchet derivative -/
private theorem deriv_eq_fderiv (G : ℝ × (ℝ × ℝ) → ℝ) (hG : ContDiff ℝ TT G) (s : ℝ)
    (x : ℝ × ℝ) : deriv (fun t => G (t, x)) s = fderiv ℝ G (s, x) (1, 0) := by
  have hd : DifferentiableAt ℝ G (s, x) := (hG.differentiable (by simp)).differentiableAt
  have h1 : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have := hd.hasFDerivAt.comp_hasDerivAt s h1
  exact this.deriv

private theorem pd_zero' (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (j : Fin 2)
    (h : f =ᶠ[𝓝 x] fun _ => 0) : B0579.pd j f x = 0 := by
  unfold B0579.pd
  rw [h.fderiv_eq]
  simp

private theorem pd_comm (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ TT f) (j k : Fin 2) :
    B0579.pd j (B0579.pd k f) = B0579.pd k (B0579.pd j f) := by
  funext x
  have hs : IsSymmSndFDerivAt ℝ f x := (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  have hdf : ContDiff ℝ TT (fderiv ℝ f) := hf.fderiv_right (m := TT) (by simp)
  have key : ∀ j : Fin 2, ∀ k : Fin 2,
      B0579.pd k (B0579.pd j f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir k) (B0579.dir j) := by
    intro j k
    unfold B0579.pd
    have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hdf.differentiable (by simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hs _ _

private theorem pd_zerofun (j : Fin 2) : B0579.pd j (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 :=
  funext fun x => pd_zero' _ x j EventuallyEq.rfl

private theorem pd_neg (f : ℝ × ℝ → ℝ) (j : Fin 2) :
    B0579.pd j (fun y => -f y) = fun y => -B0579.pd j f y := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_neg]
  simp

private theorem pd_add (f g : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) :
    B0579.pd j (fun y => f y + g y) = fun y => B0579.pd j f y + B0579.pd j g y := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_add (hf x) (hg x)]
  simp

private theorem cyl_add {c : ℝ} {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f)
    (hg : B0579.IsCylTest c g) : B0579.IsCylTest c (fun x => f x + g x) where
  smooth := hf.smooth.add hg.smooth
  periodic x := by simp only [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R1, h1⟩ := hf.band
    obtain ⟨R2, h2⟩ := hg.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    rw [h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)]
    simp

private theorem deriv_zero_of_eventually (g : ℝ → ℝ) (s : ℝ) (h : g =ᶠ[𝓝 s] fun _ => 0) :
    deriv g s = 0 := by
  rw [h.deriv_eq]; simp

theorem sliceCommute : SliceCommute := by
  intro c ζ hζ
  obtain ⟨hF, hcyl, s₁, s₂, R, hs₁, hsupp⟩ := hζ
  set F : ℝ × (ℝ × ℝ) → ℝ := fun p => ζ p.1 p.2 with hFdef
  have hFd : DifferentiableAt ℝ F = DifferentiableAt ℝ F := rfl
  -- the time derivative
  have hD : ∀ s x, deriv (fun t => ζ t x) s = fderiv ℝ F (s, x) (1, 0) := fun s x =>
    deriv_eq_fderiv F hF s x
  have hDsm : ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) => deriv (fun t => ζ t p.2) p.1) := by
    have : (fun p : ℝ × (ℝ × ℝ) => deriv (fun t => ζ t p.2) p.1) =
        fun p => fderiv ℝ F p (1, 0) := by funext p; exact hD p.1 p.2
    rw [this]
    exact (hF.fderiv_right (m := TT) (by simp)).clm_apply contDiff_const
  have hDsm' : ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) =>
      (fun s x => deriv (fun t => ζ t x) s) p.1 p.2) := hDsm
  -- zero sets
  have hband : ∀ x : ℝ × ℝ, R < |x.2| → ∀ t, ζ t x = 0 := fun x hx t =>
    hsupp t x (Or.inr (Or.inr hx))
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const (continuous_snd.abs)
  have hevx : ∀ t x, R < |x.2| → ζ t =ᶠ[𝓝 x] fun _ => 0 := by
    intro t x hx
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hsupp t y (Or.inr (Or.inr hy))
  -- (i)
  have hi : IsStreamTest c (fun s x => deriv (fun t => ζ t x) s) := by
    refine ⟨hDsm', fun s => ?_, s₁ / 2, s₂ + 1, R, by positivity, ?_⟩
    · refine ⟨?_, ?_, ⟨R, ?_⟩⟩
      · exact hDsm.comp (contDiff_const.prodMk contDiff_id)
      · intro x
        have : (fun t => ζ t (x.1 + c, x.2)) = fun t => ζ t x := by
          funext t; exact (hcyl t).periodic x
        show deriv (fun t => ζ t (x.1 + c, x.2)) s = deriv (fun t => ζ t x) s
        rw [this]
      · intro x hx
        show deriv (fun t => ζ t x) s = 0
        have : (fun t => ζ t x) = fun _ => 0 := funext (hband x hx)
        rw [this]; simp
    · intro s x h
      show deriv (fun t => ζ t x) s = 0
      rcases h with h | h | h
      · apply deriv_zero_of_eventually
        filter_upwards [Iio_mem_nhds (show s < s₁ by linarith)] with t ht
        exact hsupp t x (Or.inl ht)
      · apply deriv_zero_of_eventually
        filter_upwards [Ioi_mem_nhds (show s₂ < s by linarith)] with t ht
        exact hsupp t x (Or.inr (Or.inl ht))
      · have : (fun t => ζ t x) = fun _ => 0 := funext (hband x h)
        rw [this]; simp
  -- smoothness of pd's
  have hpdsm : ∀ j s, ContDiff ℝ TT (B0579.pd j (ζ s)) := fun j s => ((hcyl s).pd j).smooth
  have hpdjoint : ∀ j, ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (ζ p.1) p.2) :=
    fun j => pd_contDiff' ζ hF j
  -- (ii)
  have hlap : IsStreamTest c (fun s x => lapP (ζ s) x) := by
    refine ⟨?_, fun s => ?_, s₁, s₂, R, hs₁, ?_⟩
    · have h2 : ∀ j k, ContDiff ℝ TT (fun p : ℝ × (ℝ × ℝ) =>
          B0579.pd j (fun y => B0579.pd k (ζ p.1) y) p.2) := fun j k =>
        pd_contDiff' (fun s x => B0579.pd k (ζ s) x) (hpdjoint k) j
      exact (h2 0 0).add (h2 1 1)
    · exact cyl_add (((hcyl s).pd 0).pd 0) (((hcyl s).pd 1).pd 1)
    · intro s x h
      show B0579.pd 0 (B0579.pd 0 (ζ s)) x + B0579.pd 1 (B0579.pd 1 (ζ s)) x = 0
      rcases h with h | h | h
      · have : ζ s = fun _ => 0 := funext fun y => hsupp s y (Or.inl h)
        rw [this]; simp only [pd_zerofun]; simp [B0579.pd]
      · have : ζ s = fun _ => 0 := funext fun y => hsupp s y (Or.inr (Or.inl h))
        rw [this]; simp only [pd_zerofun]; simp [B0579.pd]
      · have h1 : ∀ k, B0579.pd k (ζ s) =ᶠ[𝓝 x] fun _ => 0 := by
          intro k
          filter_upwards [hopen.mem_nhds h] with y hy
          exact pd_zero' _ y k (hevx s y hy)
        rw [pd_zero' _ x 0 (h1 0), pd_zero' _ x 1 (h1 1)]; simp
  -- (iii) mixed partials
  have hDF : ∀ s x j, B0579.pd j (fun y => deriv (fun t => ζ t y) s) x =
      fderiv ℝ (fderiv ℝ F) (s, x) (0, B0579.dir j) (1, 0) := by
    intro s x j
    have hsm := pd_eq_fderiv' (fun s x => deriv (fun t => ζ t x) s) hDsm' j s x
    have hfun : (fun p : ℝ × (ℝ × ℝ) => deriv (fun t => ζ t p.2) p.1) =
        fun p => fderiv ℝ F p (1, 0) := by funext p; exact hD p.1 p.2
    show B0579.pd j (fun y => deriv (fun t => ζ t y) s) x = _
    rw [show (fun y => deriv (fun t => ζ t y) s) = (fun s x => deriv (fun t => ζ t x) s) s from rfl,
      hsm]
    show fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => deriv (fun t => ζ t p.2) p.1) (s, x) _ = _
    rw [hfun]
    have hd : DifferentiableAt ℝ (fderiv ℝ F) (s, x) :=
      ((hF.fderiv_right (m := TT) (by simp)).differentiable (by simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hPF : ∀ s x j, deriv (fun t => B0579.pd j (ζ t) x) s =
      fderiv ℝ (fderiv ℝ F) (s, x) (1, 0) (0, B0579.dir j) := by
    intro s x j
    have hfun : (fun t => B0579.pd j (ζ t) x) =
        fun t => (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ F p (0, B0579.dir j)) (t, x) := by
      funext t; exact pd_eq_fderiv' ζ hF j t x
    rw [hfun, deriv_eq_fderiv _ ((hF.fderiv_right (m := TT) (by simp)).clm_apply contDiff_const)]
    have hd : DifferentiableAt ℝ (fderiv ℝ F) (s, x) :=
      ((hF.fderiv_right (m := TT) (by simp)).differentiable (by simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hsymm : ∀ s x j, deriv (fun t => B0579.pd j (ζ t) x) s =
      B0579.pd j (fun y => deriv (fun t => ζ t y) s) x := by
    intro s x j
    rw [hPF, hDF]
    have hs : IsSymmSndFDerivAt ℝ F (s, x) := (hF.contDiffAt).isSymmSndFDerivAt (by simp)
    exact hs _ _
  refine ⟨hi, hlap, ?_, ?_⟩
  · intro s x i
    fin_cases i
    · show deriv (fun s' => streamField ζ s' x 0) s =
        streamField (fun s x => deriv (fun t => ζ t x) s) s x 0
      have : (fun s' => streamField ζ s' x 0) = fun s' => -(B0579.pd 1 (ζ s') x) := by
        funext s'; simp [streamField]
      rw [this, deriv.fun_neg, hsymm]
      simp [streamField]
    · show deriv (fun s' => streamField ζ s' x 1) s =
        streamField (fun s x => deriv (fun t => ζ t x) s) s x 1
      have : (fun s' => streamField ζ s' x 1) = fun s' => B0579.pd 0 (ζ s') x := by
        funext s'; simp [streamField]
      rw [this, hsymm]
      simp [streamField]
  · intro s x i
    have hz : ContDiff ℝ TT (ζ s) := (hcyl s).smooth
    have h0 : ContDiff ℝ TT (B0579.pd 0 (ζ s)) := hpdsm 0 s
    have h1 : ContDiff ℝ TT (B0579.pd 1 (ζ s)) := hpdsm 1 s
    have d00 : Differentiable ℝ (B0579.pd 0 (B0579.pd 0 (ζ s))) :=
      ((((hcyl s).pd 0).pd 0).differentiable)
    have d11 : Differentiable ℝ (B0579.pd 1 (B0579.pd 1 (ζ s))) :=
      ((((hcyl s).pd 1).pd 1).differentiable)
    have hlapeq : lapP (ζ s) = fun y => B0579.pd 0 (B0579.pd 0 (ζ s)) y +
        B0579.pd 1 (B0579.pd 1 (ζ s)) y := rfl
    fin_cases i
    · show lapP (fun y => streamField ζ s y 0) x = streamField (fun s x => lapP (ζ s) x) s x 0
      have e1 : (fun y => streamField ζ s y 0) = fun y => -(B0579.pd 1 (ζ s) y) := by
        funext y; simp [streamField]
      have e2 : B0579.pd 1 (fun y => B0579.pd 0 (B0579.pd 0 (ζ s)) y +
          B0579.pd 1 (B0579.pd 1 (ζ s)) y) x =
          B0579.pd 1 (B0579.pd 1 (B0579.pd 1 (ζ s))) x +
            B0579.pd 0 (B0579.pd 0 (B0579.pd 1 (ζ s))) x := by
        rw [pd_add _ _ d00 d11, pd_comm (B0579.pd 0 (ζ s)) h0 1 0,
          pd_comm (ζ s) hz 1 0]
        ring
      unfold lapP
      rw [e1, pd_neg, pd_neg, pd_neg, pd_neg]
      simp only [streamField, ite_true]
      rw [e2]
      ring
    · show lapP (fun y => streamField ζ s y 1) x = streamField (fun s x => lapP (ζ s) x) s x 1
      have e1 : (fun y => streamField ζ s y 1) = B0579.pd 0 (ζ s) := by
        funext y; simp [streamField]
      have e2 : B0579.pd 0 (fun y => B0579.pd 0 (B0579.pd 0 (ζ s)) y +
          B0579.pd 1 (B0579.pd 1 (ζ s)) y) x =
          B0579.pd 0 (B0579.pd 0 (B0579.pd 0 (ζ s))) x +
            B0579.pd 1 (B0579.pd 1 (B0579.pd 0 (ζ s))) x := by
        rw [pd_add _ _ d00 d11, pd_comm (B0579.pd 1 (ζ s)) h1 0 1,
          pd_comm (ζ s) hz 0 1]
      rw [e1]
      simp only [streamField]
      show _ = if (1 : Fin 2) = 0 then _ else _
      rw [if_neg (by decide)]
      unfold lapP
      rw [e2]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
