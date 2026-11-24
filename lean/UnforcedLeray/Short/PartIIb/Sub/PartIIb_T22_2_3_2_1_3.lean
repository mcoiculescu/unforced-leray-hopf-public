import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105 (weighted maximum
principle for the backward problem).

Proof: for `δ > 0` and `s < s' < t` the function `G = U - W - δ(t - r + 1)` is `≤ 0` on
`[s', t] × ℝ²`: otherwise it has a positive maximiser `(r₀, x₀)` (`MpExistsMax`, periodicity in
`q` plus coercivity of `W`), `r₀ < t` by the terminal inequality, the spatial derivatives of `G`
at `x₀` satisfy `∇G = 0`, `ΔG ≤ 0` (`MpSpatial`), and the one-sided time derivative of `G` at
`r₀` is `≤ 0` while the equations give it `≥ δ > 0`.  Let `δ → 0`, `s' → s`; apply to `-U`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- **Leaf `/3/1`**: at a global maximum of a `C²` function on the plane the gradient vanishes
and the Laplacian is `≤ 0`. -/
def MpSpatial : Prop :=
  ∀ (G : B0579.Plane → ℝ) (x0 : B0579.Plane), ContDiff ℝ 2 G → (∀ x, G x ≤ G x0) →
    B0579.pd 0 G x0 = 0 ∧ B0579.pd 1 G x0 = 0 ∧ lapP G x0 ≤ 0

/-- **Leaf `/3/2`**: a function continuous on `[s,t] × ℝ²`, `q`-periodic, nonpositive for `|η|`
large and positive somewhere, attains its maximum over `[s,t] × ℝ²`
(compactness of `[s,t] × [0,c] × [-L,L]` plus reduction of `q` modulo `c`). -/
def MpExistsMax : Prop :=
  ∀ (c s t : ℝ) (G : ℝ → B0579.Plane → ℝ), 0 < c → s ≤ t →
    ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2) (Icc s t ×ˢ univ) →
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane, G r (x.1 + c, x.2) = G r x) →
    (∃ L : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, L ≤ |x.2| → G r x ≤ 0) →
    (∃ r ∈ Icc s t, ∃ x : B0579.Plane, 0 < G r x) →
    ∃ r0 ∈ Icc s t, ∃ x0 : B0579.Plane, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, G r x ≤ G r0 x0

theorem mp_time_step (f : ℝ → ℝ) (D r0 t : ℝ) (hd : HasDerivAt f D r0) (hlt : r0 < t)
    (hmax : ∀ r ∈ Icc r0 t, f r ≤ f r0) : D ≤ 0 := by
  have hloc : IsLocalMaxOn f (Icc r0 t) r0 :=
    IsMaxOn.localize (fun r hr => hmax r hr)
  have hy : (t - r0) ∈ posTangentConeAt (Icc r0 t) r0 :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [show r0 + (t - r0) = t by ring, segment_eq_Icc hlt.le])
  have h := hloc.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt hy
  simp at h
  nlinarith

theorem mp_pd_neg (f : B0579.Plane → ℝ) (j : Fin 2) :
    B0579.pd j (fun x => -f x) = fun x => -B0579.pd j f x := by
  funext x; unfold B0579.pd
  rw [show (fun x => -f x) = -f from rfl, fderiv_neg]; rfl

theorem mp_lapP_neg (f : B0579.Plane → ℝ) (x : B0579.Plane) :
    lapP (fun x => -f x) x = -lapP f x := by
  unfold lapP
  rw [mp_pd_neg, mp_pd_neg, mp_pd_neg, mp_pd_neg]
  simp only [mp_pd_neg]
  ring

theorem mp_pd_diff {G : B0579.Plane → ℝ} (hG : ContDiff ℝ 2 G) (j : Fin 2) :
    Differentiable ℝ (B0579.pd j G) := by
  have hfd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact hfd.clm_apply (differentiable_const _)

theorem mp_pd_sub {f g : B0579.Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (K : ℝ) (j : Fin 2) :
    B0579.pd j (fun x => f x - g x - K) = fun x => B0579.pd j f x - B0579.pd j g x := by
  funext x; unfold B0579.pd
  have h1 : HasFDerivAt (fun x => f x - g x - K) (fderiv ℝ f x - fderiv ℝ g x) x :=
    ((hf x).hasFDerivAt.sub (hg x).hasFDerivAt).sub_const K
  rw [h1.fderiv]; rfl

theorem mp_lapP_sub {f g : B0579.Plane → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (K : ℝ) (x : B0579.Plane) :
    lapP (fun x => f x - g x - K) x = lapP f x - lapP g x := by
  have hf1 := hf.differentiable (by norm_num)
  have hg1 := hg.differentiable (by norm_num)
  unfold lapP
  rw [mp_pd_sub hf1 hg1 K, mp_pd_sub hf1 hg1 K]
  have e : ∀ j : Fin 2, B0579.pd j (fun x => B0579.pd j f x - B0579.pd j g x) x =
      B0579.pd j (B0579.pd j f) x - B0579.pd j (B0579.pd j g) x := by
    intro j
    have := mp_pd_sub (mp_pd_diff hf j) (mp_pd_diff hg j) 0 j
    have h2 := congrFun this x
    simpa using h2
  rw [e 0, e 1]; ring

/-- One-sided maximum principle. -/
theorem mp_one_sided (h1 : MpExistsMax) (h2 : MpSpatial)
    (ν c s t : ℝ) (b0 b1 U W : ℝ → B0579.Plane → ℝ) (hν : 0 < ν) (hc : 0 < c) (hst : s ≤ t)
    (hU : ContDiffOn ℝ 2 (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ))
    (hUp : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, U r (x.1 + c, x.2) = U r x)
    (hUb : ∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |U r x| ≤ M)
    (hUe : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane, HasDerivAt (fun r' => U r' x)
      (-(ν * lapP (U r) x + (b0 r x * B0579.pd 0 (U r) x + b1 r x * B0579.pd 1 (U r) x))) r)
    (hW : IsBwdSuper ν c s t b0 b1 W)
    (hWc : ∀ M : ℝ, ∃ L : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, L ≤ |x.2| → M ≤ W r x)
    (hT : ∀ x : B0579.Plane, U t x ≤ W t x) :
    ∀ r ∈ Icc s t, ∀ x : B0579.Plane, U r x ≤ W r x := by
  obtain ⟨hWd, hWp, hWe⟩ := hW
  obtain ⟨M, hM⟩ := hUb
  have slice : ∀ (F : ℝ → B0579.Plane → ℝ),
      ContDiffOn ℝ 2 (fun z : ℝ × B0579.Plane => F z.1 z.2) (Icc s t ×ˢ univ) →
      ∀ r ∈ Icc s t, ContDiff ℝ 2 (F r) := by
    intro F hF r hr
    exact hF.comp_contDiff (f := fun x : B0579.Plane => (r, x))
      (contDiff_const.prodMk contDiff_id) (fun x => ⟨hr, mem_univ _⟩)
  -- main claim for fixed s' and δ
  have main : ∀ s', s < s' → s' ≤ t → ∀ δ : ℝ, 0 < δ → ∀ r ∈ Icc s' t, ∀ x : B0579.Plane,
      U r x - W r x - δ * (t - r + 1) ≤ 0 := by
    intro s' hs' hs't δ hδ
    have hsub : Icc s' t ⊆ Icc s t := Icc_subset_Icc hs'.le le_rfl
    set G : ℝ → B0579.Plane → ℝ := fun r x => U r x - W r x - δ * (t - r + 1) with hG
    by_contra hcon
    push_neg at hcon
    obtain ⟨r1, hr1, x1, hx1⟩ := hcon
    obtain ⟨L, hL⟩ := hWc M
    obtain ⟨r0, hr0, x0, hmax⟩ := h1 c s' t G hc hs't
      (by
        have h3 : ContinuousOn (fun z : ℝ × B0579.Plane => U z.1 z.2 - W z.1 z.2 -
            δ * (t - z.1 + 1)) (Icc s' t ×ˢ univ) :=
          ((hU.continuousOn.mono (prod_mono hsub subset_rfl)).sub
            (hWd.continuousOn.mono (prod_mono hsub subset_rfl))).sub
            (by fun_prop)
        exact h3)
      (fun r hr x => by simp only [hG]; rw [hUp r (hsub hr) x, hWp r (hsub hr) x])
      ⟨L, fun r hr x hx => by
        have := hL r (hsub hr) x hx
        have := (abs_le.mp (hM r (hsub hr) x)).2
        have : 0 ≤ t - r := by linarith [hr.2]
        simp only [hG]; nlinarith⟩
      ⟨r1, hr1, x1, hx1⟩
    have hpos : 0 < G r0 x0 := lt_of_lt_of_le hx1 (hmax r1 hr1 x1)
    have hr0t : r0 < t := by
      by_contra h
      have : r0 = t := le_antisymm hr0.2 (not_lt.mp h)
      subst this
      simp only [hG] at hpos
      have := hT x0
      linarith
    have hr0s : r0 ∈ Ioo s t := ⟨by linarith [hr0.1], hr0t⟩
    have hr0m : r0 ∈ Icc s t := hsub hr0
    have hUs := slice U hU r0 hr0m
    have hWs := slice W hWd r0 hr0m
    -- spatial
    have hGs : ContDiff ℝ 2 (G r0) := by
      simp only [hG]; exact (hUs.sub hWs).sub contDiff_const
    obtain ⟨p0, p1, lp⟩ := h2 (G r0) x0 hGs (fun x => hmax r0 hr0 x)
    have hgrad0 : B0579.pd 0 (U r0) x0 - B0579.pd 0 (W r0) x0 = 0 := by
      have := p0
      simp only [hG] at this
      rw [mp_pd_sub (hUs.differentiable (by norm_num)) (hWs.differentiable (by norm_num))] at this
      exact this
    have hgrad1 : B0579.pd 1 (U r0) x0 - B0579.pd 1 (W r0) x0 = 0 := by
      have := p1
      simp only [hG] at this
      rw [mp_pd_sub (hUs.differentiable (by norm_num)) (hWs.differentiable (by norm_num))] at this
      exact this
    have hlap : lapP (U r0) x0 - lapP (W r0) x0 ≤ 0 := by
      have := lp
      simp only [hG] at this
      rw [mp_lapP_sub hUs hWs] at this
      exact this
    -- time
    obtain ⟨D, hD, hDle⟩ := hWe r0 hr0s x0
    have hUt := hUe r0 hr0s x0
    have hft : HasDerivAt (fun r => G r x0)
        (-(ν * lapP (U r0) x0 + (b0 r0 x0 * B0579.pd 0 (U r0) x0 + b1 r0 x0 * B0579.pd 1 (U r0) x0))
          - D + δ) r0 := by
      have h4 : HasDerivAt (fun r : ℝ => δ * (t - r + 1)) (-δ) r0 := by
        have := ((hasDerivAt_id r0).const_sub t |>.add_const 1).const_mul δ
        simpa using this
      exact ((hUt.sub hD).sub h4).congr_deriv (by ring)
    have hle := mp_time_step (fun r => G r x0) _ r0 t hft hr0t
      (fun r hr => hmax r ⟨le_trans hr0.1 hr.1, hr.2⟩ x0)
    have hnonneg : 0 ≤ ν * (lapP (W r0) x0 - lapP (U r0) x0) := by
      apply mul_nonneg hν.le; linarith
    have e0 : B0579.pd 0 (U r0) x0 = B0579.pd 0 (W r0) x0 := by linarith
    have e1 : B0579.pd 1 (U r0) x0 = B0579.pd 1 (W r0) x0 := by linarith
    rw [e0, e1] at hle
    nlinarith [hnonneg, hDle, hle, hδ]
  -- conclusion
  have part : ∀ r ∈ Ioc s t, ∀ x : B0579.Plane, U r x ≤ W r x := by
    intro r hr x
    have hrs := hr.1
    have hδ : ∀ δ : ℝ, 0 < δ → U r x - W r x ≤ δ * (t - r + 1) := by
      intro δ hδ
      have := main r hrs hr.2 δ hδ r ⟨le_rfl, hr.2⟩ x
      linarith
    by_contra hcon
    push_neg at hcon
    have hp : 0 < U r x - W r x := by linarith
    set K : ℝ := t - r + 1 with hK
    have hK0 : 0 < K := by have := hr.2; simp only [hK]; linarith
    have := hδ ((U r x - W r x) / (2 * K)) (by positivity)
    have e : (U r x - W r x) / (2 * K) * K = (U r x - W r x) / 2 := by field_simp
    rw [e] at this
    linarith
  intro r hr x
  rcases eq_or_lt_of_le hr.1 with hrs | hrs
  · rcases eq_or_lt_of_le hst with hst' | hst'
    · have : r = t := by linarith [hr.2]
      subst this; exact hT x
    · subst hrs
      have hcU : ContinuousOn (fun s' => U s' x) (Icc s t) :=
        hU.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
          (fun s' hr' => ⟨hr', mem_univ _⟩)
      have hcW : ContinuousOn (fun s' => W s' x) (Icc s t) :=
        hWd.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
          (fun s' hr' => ⟨hr', mem_univ _⟩)
      have hcl : IsClosed (Icc s t ∩ (fun s' => W s' x - U s' x) ⁻¹' Ici 0) :=
        (hcW.sub hcU).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hsub : Ioc s t ⊆ Icc s t ∩ (fun s' => W s' x - U s' x) ⁻¹' Ici 0 := fun s' hr' =>
        ⟨Ioc_subset_Icc_self hr', by
          have := part s' hr' x
          simp only [mem_preimage, mem_Ici]; linarith⟩
      have hcls := closure_minimal hsub hcl
      rw [closure_Ioc hst'.ne] at hcls
      have := (hcls ⟨le_rfl, hst'.le⟩).2
      simp only [mem_preimage, mem_Ici] at this
      linarith
  · exact part r ⟨hrs, hr.2⟩ x

/-- `BwdMaxPrinciple` from the two compactness / calculus leaves. -/
theorem bwdMaxPrinciple_of (h1 : MpExistsMax) (h2 : MpSpatial) : BwdMaxPrinciple := by
  intro ν c s t b0 b1 U W hν hc hst hU hUp hUb hUe hW hWc hT r hr x
  have hpos := mp_one_sided h1 h2 ν c s t b0 b1 U W hν hc hst hU hUp hUb hUe hW hWc
    (fun x => (abs_le.mp (hT x)).2)
  have hneg := mp_one_sided h1 h2 ν c s t b0 b1 (fun r x => -U r x) W hν hc hst
    (by simpa using hU.neg)
    (fun r hr x => by simp [hUp r hr x])
    (by obtain ⟨M, hM⟩ := hUb; exact ⟨M, fun r hr x => by simpa using hM r hr x⟩)
    (fun r hr x => by
      have h : HasDerivAt (fun r' => -U r' x) (-(-(ν * lapP (U r) x +
          (b0 r x * B0579.pd 0 (U r) x + b1 r x * B0579.pd 1 (U r) x)))) r := (hUe r hr x).neg
      refine h.congr_deriv ?_
      show _ = -(ν * lapP (fun y => -U r y) x + (b0 r x * B0579.pd 0 (fun y => -U r y) x +
        b1 r x * B0579.pd 1 (fun y => -U r y) x))
      simp only [mp_lapP_neg, mp_pd_neg]
      ring)
    hW hWc
    (fun x => (abs_le.mp (hT x)).1 |> fun h => by linarith)
  exact abs_le.mpr ⟨by linarith [hneg r hr x], hpos r hr x⟩

end UnforcedLeray.Short.IIb
