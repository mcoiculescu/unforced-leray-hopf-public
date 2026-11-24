import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_2

/-!

bound for the localized Laplacian quantity `Z = ζ_{η₀}(Δφ)² + μ|∇φ|² + κφ²`.

Source: `the November 2 reference manuscript` lines 2100-2105.

The helper lemmas `lz*` are the proofs of the leaves `PdJointSmooth`, `PdPeriodic`, `BandBounded`,
`CutProps` (copied from the sibling `Grad/GradZRegular.lean`, so that this file is self-contained).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-! ## Helper: spatial partials of a jointly smooth function (leaf `PdJointSmooth`) -/

theorem lzPdJointSmooth : UnforcedLeray.Short.IIb.PdJointSmooth := by
  intro s t U j hU
  have hslice : ∀ r ∈ Icc s t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U r) := by
    intro r hr
    have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => (r, x)) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have h := hU.comp hcomp (fun x _ => ⟨hr, mem_univ _⟩)
    exact contDiffOn_univ.1 h
  rcases lt_or_ge s t with hst | hst
  · have hS : UniqueDiffOn ℝ (Icc s t ×ˢ (univ : Set B0579.Plane)) :=
      (uniqueDiffOn_Icc hst).prod uniqueDiffOn_univ
    have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ))
        (Icc s t ×ˢ univ) :=
      hU.fderivWithin hS (by simp)
    have hG : ∀ z ∈ Icc s t ×ˢ (univ : Set B0579.Plane),
        B0579.pd j (U z.1) z.2 =
          fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) z
            (ContinuousLinearMap.inr ℝ ℝ B0579.Plane (B0579.dir j)) := by
      intro z hz
      obtain ⟨r, x⟩ := z
      have hr : r ∈ Icc s t := hz.1
      have hFd : DifferentiableWithinAt ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2)
          (Icc s t ×ˢ univ) (r, x) :=
        hU.differentiableOn (by simp) _ hz
      have hF' := hFd.hasFDerivWithinAt
      have hg : HasFDerivAt (fun y : B0579.Plane => (r, y))
          (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) x :=
        (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
      have hg' : HasFDerivWithinAt (fun y : B0579.Plane => (r, y))
          (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) (univ : Set B0579.Plane) x :=
        hg.hasFDerivWithinAt
      have hcomp := HasFDerivWithinAt.comp x hF' hg'
        (fun y _ => (⟨hr, mem_univ y⟩ : (r, y) ∈ Icc s t ×ˢ (univ : Set B0579.Plane)))
      have hsl := hasFDerivWithinAt_univ.1 hcomp
      have hsl' : HasFDerivAt (U r)
          ((fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) (r, x)).comp
            (ContinuousLinearMap.inr ℝ ℝ B0579.Plane)) x := hsl
      unfold B0579.pd
      show fderiv ℝ (U r) x (B0579.dir j) = _
      rw [hsl'.fderiv]
      rfl
    have hH : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => fderivWithin ℝ (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) z
            (ContinuousLinearMap.inr ℝ ℝ B0579.Plane (B0579.dir j)))
        (Icc s t ×ˢ univ) :=
      hD.clm_apply contDiffOn_const
    exact hH.congr (fun z hz => hG z hz)
  · rcases eq_or_lt_of_le hst with h | h
    · have hsub : ∀ r ∈ Icc s t, r = s := fun r hr => le_antisymm (by linarith [hr.2]) hr.1
      have hsl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U s) :=
        hslice s ⟨le_rfl, by linarith⟩
      have hpd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : B0579.Plane => B0579.pd j (U s) x) := by
        unfold B0579.pd
        exact (hsl.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
      have hcongr : ∀ z ∈ Icc s t ×ˢ (univ : Set B0579.Plane),
          B0579.pd j (U z.1) z.2 = (fun x : B0579.Plane => B0579.pd j (U s) x) z.2 := by
        intro z hz
        rw [hsub z.1 hz.1]
      exact ((hpd.comp contDiff_snd).contDiffOn).congr hcongr
    · have hempty : Icc s t ×ˢ (univ : Set B0579.Plane) = ∅ := by
        rw [Icc_eq_empty (not_le.2 h), empty_prod]
      rw [hempty]
      exact contDiffOn_empty

/-! ## Helper: periodicity of partials (leaf `PdPeriodic`) -/

theorem lzPdPeriodic : UnforcedLeray.Short.IIb.PdPeriodic := by
  intro c f j hf x
  have hfun : (fun y : B0579.Plane => f (y + ((c, 0) : B0579.Plane))) = f := by
    funext y
    have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hf y
  have key : fderiv ℝ f (x + ((c, 0) : B0579.Plane)) = fderiv ℝ f x := by
    have h : fderiv ℝ (fun t : B0579.Plane => f (t + ((c, 0) : B0579.Plane))) x =
        fderiv ℝ f (x + ((c, 0) : B0579.Plane)) := fderiv_comp_add_right _
    rw [hfun] at h
    exact h.symm
  have hx : x + ((c, 0) : B0579.Plane) = (x.1 + c, x.2) := by ext <;> simp
  unfold B0579.pd
  rw [← hx, key]

/-! ## Helper: boundedness on bands (leaf `BandBounded`) -/

theorem lzBandBounded : UnforcedLeray.Short.IIb.BandBounded := by
  intro c s t a b G hc hG hper
  have hK : IsCompact (Icc s t ×ˢ (Icc 0 c ×ˢ Icc a b) : Set (ℝ × B0579.Plane)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hGK : ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2)
      (Icc s t ×ˢ (Icc 0 c ×ˢ Icc a b)) :=
    hG.mono (fun z hz => ⟨hz.1, mem_univ _⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGK
  refine ⟨C, fun r hr x hx => ?_⟩
  set k : ℤ := ⌊x.1 / c⌋ with hk
  have hfl1 : (k : ℝ) ≤ x.1 / c := Int.floor_le _
  have hfl2 : x.1 / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hA : (k : ℝ) * c ≤ x.1 := (le_div_iff₀ hc).1 hfl1
  have hB : x.1 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hfl2
  have hB' : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
  have hy0 : 0 ≤ x.1 - (k : ℝ) * c := by linarith
  have hyc : x.1 - (k : ℝ) * c ≤ c := by linarith
  have hp : Function.Periodic (fun u : ℝ => G r (u, x.2)) c :=
    fun u => hper r hr (u, x.2)
  have hshift : G r (x.1 - (k : ℝ) * c, x.2) = G r x := by
    have h := hp.sub_int_mul_eq (x := x.1) k
    simpa using h
  have hmem : (r, (x.1 - (k : ℝ) * c, x.2)) ∈ Icc s t ×ˢ (Icc 0 c ×ˢ Icc a b) :=
    ⟨hr, ⟨⟨hy0, hyc⟩, hx⟩⟩
  have hbound := hC (r, (x.1 - (k : ℝ) * c, x.2)) hmem
  simp only at hbound
  rw [hshift, Real.norm_eq_abs] at hbound
  exact hbound

/-! ## Helper: properties of the cutoff (leaf `CutProps`) -/

theorem lzCutProps_bdd (g : ℝ → ℝ) (hg : Continuous g) (hgcs : HasCompactSupport g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |g y| ≤ K := by
  obtain ⟨K, hK⟩ := hg.bounded_above_of_compact_support hgcs
  refine ⟨max K 0, le_max_right _ _, fun y => ?_⟩
  rw [← Real.norm_eq_abs]
  exact le_trans (hK y) (le_max_left _ _)

theorem lzCutProps : UnforcedLeray.Short.IIb.CutProps := by
  have hρC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => cutBump y) := cutBump.contDiff
  have hρcs : HasCompactSupport (fun y : ℝ => cutBump y) := cutBump.hasCompactSupport
  have hcut_eq : cutθ = fun y => cutBump y * cutBump y := by
    funext y
    unfold cutθ
    ring
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutθ := by
    rw [hcut_eq]
    exact hρC.mul hρC
  have hcutcs : HasCompactSupport cutθ := by
    rw [hcut_eq]
    exact hρcs.mul_right
  have hcutcs1 : HasCompactSupport (deriv cutθ) := hcutcs.deriv
  have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv cutθ) := by
    have h := ContDiff.iterate_deriv 1 hcutC
    simpa using h
  have hcont1 : Continuous (deriv cutθ) := hcutC.continuous_deriv (by simp)
  have hcont2 : Continuous (deriv (deriv cutθ)) := hc1.continuous_deriv (by simp)
  have hdρ : Differentiable ℝ (fun y : ℝ => cutBump y) := hρC.differentiable (by simp)
  have hdcut : ∀ y : ℝ, deriv cutθ y = 2 * cutBump y * deriv (fun y : ℝ => cutBump y) y := by
    intro y
    rw [hcut_eq]
    have h : HasDerivAt (fun y : ℝ => cutBump y * cutBump y) _ y :=
      (hdρ y).hasDerivAt.mul (hdρ y).hasDerivAt
    rw [h.deriv]
    ring
  obtain ⟨K1, hK1nn, hK1⟩ :=
    lzCutProps_bdd _ (hρC.continuous_deriv (by simp)) hρcs.deriv
  obtain ⟨K2, hK2nn, hK2⟩ := lzCutProps_bdd _ hcont2 hcutcs1.deriv
  have hb0 : cutBump 0 = 1 := cutBump.one_of_mem_closedBall (by norm_num [cutBump])
  have h0 : cutθ 0 = 1 := by
    unfold cutθ
    rw [hb0]
    norm_num
  have hrange : ∀ y : ℝ, 0 ≤ cutθ y ∧ cutθ y ≤ 1 := by
    intro y
    have h1 : 0 ≤ cutBump y := cutBump.nonneg
    have h2 : cutBump y ≤ 1 := cutBump.le_one
    unfold cutθ
    constructor
    · positivity
    · nlinarith
  have hzero : ∀ y : ℝ, 1 ≤ |y| → cutθ y = 0 := by
    intro y hy
    have hdist : cutBump.rOut ≤ dist y 0 := by
      show (1 : ℝ) ≤ dist y 0
      rw [Real.dist_eq, sub_zero]
      exact hy
    have h1 : cutBump y = 0 := cutBump.zero_of_le_dist hdist
    unfold cutθ
    rw [h1]
    norm_num
  refine ⟨hcutC, h0, hrange, hzero, 4 * K1 ^ 2 + K2, ?_, ?_⟩
  · positivity
  · intro y
    refine ⟨?_, ?_⟩
    · rw [hdcut y]
      have hcy : cutθ y = cutBump y * cutBump y := congrFun hcut_eq y
      rw [hcy]
      have hsq : (deriv (fun y : ℝ => cutBump y) y) ^ 2 ≤ K1 ^ 2 := by
        have h1 := hK1 y
        have h2 := sq_abs (deriv (fun y : ℝ => cutBump y) y)
        nlinarith [abs_nonneg (deriv (fun y : ℝ => cutBump y) y)]
      have hnn : 0 ≤ cutBump y * cutBump y := mul_self_nonneg _
      calc (2 * cutBump y * deriv (fun y : ℝ => cutBump y) y) ^ 2
          = 4 * (deriv (fun y : ℝ => cutBump y) y) ^ 2 * (cutBump y * cutBump y) := by ring
        _ ≤ 4 * K1 ^ 2 * (cutBump y * cutBump y) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
        _ ≤ (4 * K1 ^ 2 + K2) * (cutBump y * cutBump y) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
    · have h := hK2 y
      have h4 : 0 ≤ 4 * K1 ^ 2 := by positivity
      linarith

/-! ## Helpers: derivatives and periodicity of the Laplacian -/

/-- Partial derivatives of a smooth slice are smooth. -/
theorem lzPdC (f : B0579.Plane → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (j : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B0579.pd j f) := by
  unfold B0579.pd
  exact (hf.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

/-- The planar Laplacian of a periodic function is periodic. -/
theorem lzLapPer (c : ℝ) (f : B0579.Plane → ℝ) (hf : ∀ x : B0579.Plane, f (x.1 + c, x.2) = f x)
    (x : B0579.Plane) : lapP f (x.1 + c, x.2) = lapP f x := by
  unfold lapP
  rw [lzPdPeriodic c (B0579.pd 0 f) 0 (lzPdPeriodic c f 0 hf) x,
    lzPdPeriodic c (B0579.pd 1 f) 1 (lzPdPeriodic c f 1 hf) x]

/-! ## The main statement -/

theorem lapZRegular : UnforcedLeray.Short.IIb.LapZRegular := by
  intro ν c s t v ψ φ hc hφ hgb mu kap hmu η0
  have hsmooth := hφ.smooth
  have hper := hφ.periodic
  have hcut := lzCutProps
  have hθC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutθ := hcut.1
  -- slices of `φ` are smooth in space
  have hslice : ∀ r ∈ Icc s t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ r) := by
    intro r hr
    have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => (r, x)) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have h := hsmooth.comp hcomp (fun x _ => ⟨hr, mem_univ _⟩)
    exact contDiffOn_univ.1 h
  -- joint smoothness of the first and second spatial partials on the band
  have hJ0 := lzPdJointSmooth s t φ 0 hsmooth
  have hJ1 := lzPdJointSmooth s t φ 1 hsmooth
  have hJ00 := lzPdJointSmooth s t (fun r x => B0579.pd 0 (φ r) x) 0 hJ0
  have hJ11 := lzPdJointSmooth s t (fun r x => B0579.pd 1 (φ r) x) 1 hJ1
  -- continuity of the pieces on the band
  have hζ : ContinuousOn (fun z : ℝ × B0579.Plane => cutζ η0 z.2) (Icc s t ×ˢ univ) :=
    (hθC.continuous.comp ((continuous_snd.comp continuous_snd).sub continuous_const)).continuousOn
  have hLP : ContinuousOn (fun z : ℝ × B0579.Plane => lapP (φ z.1) z.2) (Icc s t ×ˢ univ) :=
    hJ00.continuousOn.add hJ11.continuousOn
  have hLS : ContinuousOn (fun z : ℝ × B0579.Plane => lapSq φ z.1 z.2) (Icc s t ×ˢ univ) :=
    hLP.mul hLP
  have hG : ContinuousOn (fun z : ℝ × B0579.Plane => gradSq φ z.1 z.2) (Icc s t ×ˢ univ) :=
    (hJ0.continuousOn.mul hJ0.continuousOn).add (hJ1.continuousOn.mul hJ1.continuousOn)
  have hφφ : ContinuousOn (fun z : ℝ × B0579.Plane => φ z.1 z.2 * φ z.1 z.2) (Icc s t ×ˢ univ) :=
    hsmooth.continuousOn.mul hsmooth.continuousOn
  -- periodicity of the pieces
  have hGper : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, gradSq φ r (x.1 + c, x.2) = gradSq φ r x := by
    intro r hr x
    unfold gradSq
    rw [lzPdPeriodic c (φ r) 0 (hper r hr) x, lzPdPeriodic c (φ r) 1 (hper r hr) x]
  have hLPer : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, lapSq φ r (x.1 + c, x.2) = lapSq φ r x := by
    intro r hr x
    unfold lapSq
    rw [lzLapPer c (φ r) (hper r hr) x]
  -- smoothness of the localized quantity on each slice
  have hLZC : ∀ r ∈ Icc s t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lapZ mu kap η0 φ r) := by
    intro r hr
    have hsl := hslice r hr
    have hLPc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lapP (φ r)) := by
      unfold lapP
      exact (lzPdC _ (lzPdC _ hsl 0) 0).add (lzPdC _ (lzPdC _ hsl 1) 1)
    have hcutS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => cutθ (x.2 - η0)) :=
      hθC.comp (contDiff_snd.sub contDiff_const)
    have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => gradSq φ r x) := by
      unfold gradSq
      exact ((lzPdC _ hsl 0).mul (lzPdC _ hsl 0)).add ((lzPdC _ hsl 1).mul (lzPdC _ hsl 1))
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane =>
      cutθ (x.2 - η0) * (lapP (φ r) x * lapP (φ r) x) +
        (mu * gradSq φ r x + kap * (φ r x * φ r x)))
    exact (hcutS.mul (hLPc.mul hLPc)).add
      ((contDiff_const.mul hGc).add (contDiff_const.mul (hsl.mul hsl)))
  refine ⟨?_, fun r hr => (hLZC r (Ioo_subset_Icc_self hr)).of_le (by simp), ?_, ?_⟩
  · -- continuity on the band
    exact (hζ.mul hLS).add ((continuousOn_const.mul hG).add (continuousOn_const.mul hφφ))
  · -- periodicity in `x.1`
    intro r hr x
    have hpe := hper r hr x
    dsimp only [lapZ, cutζ]
    rw [hpe, hGper r hr x, hLPer r hr x]
  · -- uniform upper bound
    obtain ⟨M1, hM1⟩ := lzBandBounded c s t (η0 - 1) (η0 + 1) (fun r x => lapSq φ r x) hc hLS
      (fun r hr x => hLPer r hr x)
    obtain ⟨M2, hM2⟩ := hφ.bounded
    obtain ⟨C, hC⟩ := hgb
    refine ⟨max M1 0 + |mu| * |C| + |kap| * (M2 * M2), fun r hr x => ?_⟩
    have hφsq : φ r x * φ r x ≤ M2 * M2 := by
      have h := hM2 r hr x
      have := mul_self_le_mul_self (abs_nonneg (φ r x)) h
      rwa [abs_mul_abs_self] at this
    have hkap : kap * (φ r x * φ r x) ≤ |kap| * (M2 * M2) := by
      calc kap * (φ r x * φ r x) ≤ |kap| * (φ r x * φ r x) :=
            mul_le_mul_of_nonneg_right (le_abs_self kap) (mul_self_nonneg _)
        _ ≤ |kap| * (M2 * M2) := mul_le_mul_of_nonneg_left hφsq (abs_nonneg kap)
    have hG0 : 0 ≤ gradSq φ r x := by
      unfold gradSq
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have hgrad : mu * gradSq φ r x ≤ |mu| * |C| := by
      have h1 : gradSq φ r x ≤ |C| := (hC r hr x).trans (le_abs_self C)
      calc mu * gradSq φ r x ≤ |mu| * gradSq φ r x :=
            mul_le_mul_of_nonneg_right (le_abs_self mu) hG0
        _ ≤ |mu| * |C| := mul_le_mul_of_nonneg_left h1 (abs_nonneg mu)
    have hcutL : cutζ η0 x * lapSq φ r x ≤ max M1 0 := by
      have hL0 : 0 ≤ lapSq φ r x := by
        unfold lapSq
        exact mul_self_nonneg _
      by_cases hx : x.2 ∈ Icc (η0 - 1) (η0 + 1)
      · have hb : |lapSq φ r x| ≤ M1 := hM1 r hr x hx
        have hc1 : cutζ η0 x ≤ 1 := by
          unfold cutζ
          exact (hcut.2.2.1 _).2
        calc cutζ η0 x * lapSq φ r x ≤ 1 * lapSq φ r x :=
              mul_le_mul_of_nonneg_right hc1 hL0
          _ ≤ M1 := by rw [one_mul]; exact (le_abs_self _).trans hb
          _ ≤ max M1 0 := le_max_left _ _
      · have h1 : 1 ≤ |x.2 - η0| := by
          simp only [mem_Icc, not_and_or, not_le] at hx
          rcases hx with h | h
          · exact le_trans (by linarith) (neg_le_abs (x.2 - η0))
          · exact le_trans (by linarith) (le_abs_self (x.2 - η0))
        have hz : cutζ η0 x = 0 := by
          unfold cutζ
          exact hcut.2.2.2.1 _ h1
        rw [hz, zero_mul]
        exact le_max_right _ _
    dsimp only [lapZ]
    linarith [hcutL, hkap, hgrad]

end UnforcedLeray.Short.IIb
