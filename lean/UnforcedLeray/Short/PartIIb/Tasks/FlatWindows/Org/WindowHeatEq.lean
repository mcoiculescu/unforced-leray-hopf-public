import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg
import UnforcedLeray.Short.PartIIb.Sub.T12_7

/-!
Leaf `PartII-b:T13/1/3` (SP 1925, 1928-1930): the cut-off heat equation `WindowHeatEq`,
from the cutoff properties `WinCutProps` and the integrability `deqIntegrableMul`.

Route: test the full flat equation with `ψ = (χ_a(s)/s) φ`, a test of `s > 0`; then
`flatTransposeS ν μ ψ = μ χ φ / s - χ' φ + χ cylHeatT φ` pointwise, and rearrange.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

/-- Helper: a real function's cast to `ℂ`, with the same support facts. -/
theorem whe_ofReal (f : Coord → ℝ) (hc : Continuous f) (hk : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ) ×ˢ univ) :
    Continuous (fun x => (f x : ℂ)) ∧ HasCompactSupport (fun x => (f x : ℂ)) ∧
      tsupport (fun x => (f x : ℂ)) ⊆ Ioi (0 : ℝ) ×ˢ univ := by
  refine ⟨Complex.continuous_ofReal.comp hc, ?_, ?_⟩
  · exact HasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) hk (by simp)
  · exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) (by simp) f).trans hs

/-- Helper: `G_i` times a real continuous compactly supported test in `s > 0` is integrable. -/
theorem whe_int (c r : ℝ) (b : CProf) (hc : 0 < c) (hr : 1 < r) (hb : InHr c r b) (i : Fin 2)
    (f : Coord → ℝ) (hf : Continuous f) (hk : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ) ×ˢ univ) :
    Integrable (fun x => b x i * (f x : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := whe_ofReal f hf hk hs
  exact deqIntegrableMul c r b hc hr hb i _ h1 h2 h3

/-- Helper: a function vanishing for `s < a/2` (`a > 0`) has `tsupport` in `{s > 0}` once it is
compactly supported. -/
theorem whe_tsupport_pos {a : ℝ} (ha : 0 < a) (f : Coord → ℝ)
    (hf : ∀ x : Coord, x.1 < a / 2 → f x = 0) :
    tsupport f ⊆ Ioi (0 : ℝ) ×ˢ univ := by
  have hcl : tsupport f ⊆ {x : Coord | a / 2 ≤ x.1} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_fst)
    intro x hx
    by_contra hlt
    apply hx
    exact hf x (lt_of_not_ge hlt)
  intro x hx
  have h1 : a / 2 ≤ x.1 := hcl hx
  exact ⟨by show (0 : ℝ) < x.1; linarith, mem_univ _⟩

/-- Helper: `s ↦ χ(s)/s` is smooth when `χ` is smooth and vanishes near `s ≤ 0` (`a > 0`). -/
theorem whe_h_contDiff (a : ℝ) (ha : 0 < a) (hχ : ContDiff ℝ ∞ (winCut a))
    (hz : ∀ s : ℝ, s < a / 2 → winCut a =ᶠ[𝓝 s] fun _ => 0) :
    ContDiff ℝ ∞ (fun s : ℝ => winCut a s / s) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    have hev : (fun t : ℝ => winCut a t / t) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hz 0 (by linarith)] with t ht
      simp [ht]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (hχ.contDiffAt).div contDiffAt_id hs

/-- Helper: partial derivatives of a smooth function are smooth. -/
theorem whe_cpd_contDiff {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g) (j : Fin 3) :
    ContDiff ℝ ∞ (fun y => cpd j g y) := by
  unfold cpd
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Helper: partial derivatives of a compactly supported function are compactly supported. -/
theorem whe_cpd_compact {g : Coord → ℝ} (hg : HasCompactSupport g) (j : Fin 3) :
    HasCompactSupport (fun y => cpd j g y) := by
  have k : HasCompactSupport (fderiv ℝ g) := HasCompactSupport.fderiv (𝕜 := ℝ) hg
  exact k.comp_left (g := fun L : Coord →L[ℝ] ℝ => L (cdir j)) (by simp)

/-- Helper: the derivative of `y ↦ h(y.1)` in the `s`-direction. -/
theorem whe_fderiv_fst (h : ℝ → ℝ) (hh : Differentiable ℝ h) (x v : Coord) :
    fderiv ℝ (fun y : Coord => h y.1) x v = deriv h x.1 * v.1 := by
  have h1 : HasDerivAt h (deriv h x.1) x.1 := (hh x.1).hasDerivAt
  have h2 : HasFDerivAt (fun y : Coord => h y.1)
      (deriv h x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    h1.comp_hasFDerivAt x hasFDerivAt_fst
  rw [h2.fderiv]
  simp

/-- Helper: partial derivatives of `h(s) g(x)` (`h` smooth). -/
theorem whe_cpd_h (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (g : Coord → ℝ) (hg : ContDiff ℝ ∞ g)
    (x : Coord) :
    cpd 0 (fun y => h y.1 * g y) x = deriv h x.1 * g x + h x.1 * cpd 0 g x ∧
    cpd 1 (fun y => h y.1 * g y) x = h x.1 * cpd 1 g x ∧
    cpd 2 (fun y => h y.1 * g y) x = h x.1 * cpd 2 g x := by
  have hhd : Differentiable ℝ h := hh.differentiable (by simp)
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  have hfst : DifferentiableAt ℝ (fun y : Coord => h y.1) x :=
    DifferentiableAt.comp x (hhd x.1) differentiableAt_fst
  have hmul : fderiv ℝ (fun y => h y.1 * g y) x
      = h x.1 • fderiv ℝ g x + g x • fderiv ℝ (fun y : Coord => h y.1) x :=
    fderiv_mul hfst hgd
  refine ⟨?_, ?_, ?_⟩
  · unfold cpd
    rw [hmul]
    simp [cdir, whe_fderiv_fst h hhd x] <;> ring
  · unfold cpd
    rw [hmul]
    simp [cdir, whe_fderiv_fst h hhd x]
  · unfold cpd
    rw [hmul]
    simp [cdir, whe_fderiv_fst h hhd x]

/-- Helper: the pointwise identity `flatTransposeS ν μ ψ = μ χ φ/s - χ' φ + χ cylHeatT φ` for
`ψ = (χ/s) φ`. -/
theorem whe_flat_identity (a : ℝ) (ha : 0 < a) (hχ : ContDiff ℝ ∞ (winCut a))
    (hz : ∀ s : ℝ, s < a / 2 → winCut a =ᶠ[𝓝 s] fun _ => 0)
    (ν : ℝ) (μ : ℂ) (φ : Coord → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    flatTransposeS ν μ (fun y => winCut a y.1 / y.1 * φ y) x =
      μ * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ) - ((deriv (winCut a) x.1 * φ x : ℝ) : ℂ) +
        ((winCut a x.1 * cylHeatT ν φ x : ℝ) : ℂ) := by
  have hw0 : winCut a 0 = 0 := (hz 0 (by linarith)).self_of_nhds
  have hd0 : deriv (winCut a) 0 = 0 := by
    rw [(hz 0 (by linarith)).deriv.eq_of_nhds]; simp
  by_cases hs : x.1 = 0
  · simp [flatTransposeS, cylHeatT, hs, hw0, hd0]
  · have hhC : ContDiff ℝ ∞ (fun s : ℝ => winCut a s / s) := whe_h_contDiff a ha hχ hz
    have hχd : HasDerivAt (winCut a) (deriv (winCut a) x.1) x.1 :=
      ((hχ.differentiable (by simp)) x.1).hasDerivAt
    have hd : HasDerivAt (fun y => winCut a y / y)
        ((deriv (winCut a) x.1 * x.1 - winCut a x.1 * 1) / x.1 ^ 2) x.1 :=
      hχd.div (hasDerivAt_id' x.1) hs
    have hdh : deriv (fun y => winCut a y / y) x.1
        = (deriv (winCut a) x.1 * x.1 - winCut a x.1 * 1) / x.1 ^ 2 := hd.deriv
    have eA : x.1 * deriv (fun y => winCut a y / y) x.1
        = deriv (winCut a) x.1 - winCut a x.1 / x.1 := by
      rw [hdh]; field_simp
    have eB : x.1 * (winCut a x.1 / x.1) = winCut a x.1 := by field_simp
    have hφ1 : ContDiff ℝ ∞ (fun y => cpd 1 φ y) := whe_cpd_contDiff hφ 1
    have hφ2 : ContDiff ℝ ∞ (fun y => cpd 2 φ y) := whe_cpd_contDiff hφ 2
    have h0 : cpd 0 (fun y => winCut a y.1 / y.1 * φ y) x
        = deriv (fun s => winCut a s / s) x.1 * φ x + winCut a x.1 / x.1 * cpd 0 φ x :=
      (whe_cpd_h (fun s => winCut a s / s) hhC φ hφ x).1
    have e1 : (fun y => cpd 1 (fun z => winCut a z.1 / z.1 * φ z) y)
        = fun y => winCut a y.1 / y.1 * cpd 1 φ y :=
      funext fun y => (whe_cpd_h (fun s => winCut a s / s) hhC φ hφ y).2.1
    have e2 : (fun y => cpd 2 (fun z => winCut a z.1 / z.1 * φ z) y)
        = fun y => winCut a y.1 / y.1 * cpd 2 φ y :=
      funext fun y => (whe_cpd_h (fun s => winCut a s / s) hhC φ hφ y).2.2
    have key1 : cpd 1 (fun y => cpd 1 (fun z => winCut a z.1 / z.1 * φ z) y) x
        = winCut a x.1 / x.1 * cpd 1 (fun y => cpd 1 φ y) x := by
      rw [e1]
      exact (whe_cpd_h (fun s => winCut a s / s) hhC (fun y => cpd 1 φ y) hφ1 x).2.1
    have key2 : cpd 2 (fun y => cpd 2 (fun z => winCut a z.1 / z.1 * φ z) y) x
        = winCut a x.1 / x.1 * cpd 2 (fun y => cpd 2 φ y) x := by
      rw [e2]
      exact (whe_cpd_h (fun s => winCut a s / s) hhC (fun y => cpd 2 φ y) hφ2 x).2.2
    simp only [flatTransposeS, cylHeatT]
    rw [h0, key1, key2]
    have eAc := congrArg (fun t : ℝ => (t : ℂ)) eA
    have eBc := congrArg (fun t : ℝ => (t : ℂ)) eB
    push_cast at eAc eBc ⊢
    linear_combination (-(φ x : ℂ)) * eAc
      + (-((cpd 0 φ x : ℂ) + (ν : ℂ) * ((cpd 1 (fun y => cpd 1 φ y) x : ℂ)
          + (cpd 2 (fun y => cpd 2 φ y) x : ℂ)))) * eBc

/-- **Leaf `PartII-b:T13/1/3`** (SP 1925, 1928-1930): the cut-off heat equation. -/
theorem windowHeatEq_of (hχ : WinCutProps) : WindowHeatEq := by
  intro c r ν μ hc hr hν G b hG hb hFull a ha i
  obtain ⟨M, -, hM⟩ := hχ
  obtain ⟨hcd, -, hsupp, -, -⟩ := hM a ha
  have hzL : ∀ s : ℝ, s < a / 2 → winCut a s = 0 := fun s hs => by
    by_contra hne
    exact absurd (hsupp (subset_tsupport _ hne)).1 (not_le.2 hs)
  have hz : ∀ s : ℝ, s < a / 2 → winCut a =ᶠ[𝓝 s] fun _ => 0 := fun s hs => by
    filter_upwards [Iio_mem_nhds hs] with t ht using hzL t ht
  have hdz : ∀ s : ℝ, s < a / 2 → deriv (winCut a) s = 0 := fun s hs => by
    rw [(hz s hs).deriv.eq_of_nhds]; simp
  have hhC : ContDiff ℝ ∞ (fun s : ℝ => winCut a s / s) := whe_h_contDiff a ha hcd hz
  have hDc : Continuous (deriv (winCut a)) := hcd.continuous_deriv (by simp)
  unfold IsCylHeat
  intro φ hφ
  have hφs := hφ.smooth
  -- the test `ψ = (χ/s) φ`
  have hψs : ContDiff ℝ ∞ (fun x : Coord => winCut a x.1 / x.1 * φ x) :=
    (hhC.comp contDiff_fst).mul hφs
  have hψc : HasCompactSupport (fun x : Coord => winCut a x.1 / x.1 * φ x) :=
    hφ.compact.mul_left (f := fun x : Coord => winCut a x.1 / x.1)
  have hψsupp : tsupport (fun x : Coord => winCut a x.1 / x.1 * φ x) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    whe_tsupport_pos ha _ (fun x hx => by simp [hzL x.1 hx])
  have hψt : IsCoordTest (fun x : Coord => winCut a x.1 / x.1 * φ x) := ⟨hψs, hψc, hψsupp⟩
  obtain ⟨hI1, hI2, hEq⟩ := hFull i _ hψt
  have hEq' : ∫ x, b x i * flatTransposeS ν μ (fun y => winCut a y.1 / y.1 * φ y) x
      = ∫ x, G x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ) := hEq
  have hψc0 : Continuous (fun x : Coord => winCut a x.1 / x.1 * φ x) := hψs.continuous
  -- the other two integrands
  have hf2c : Continuous (fun x : Coord => deriv (winCut a) x.1 * φ x) :=
    (hDc.comp continuous_fst).mul hφs.continuous
  have hf2k : HasCompactSupport (fun x : Coord => deriv (winCut a) x.1 * φ x) :=
    hφ.compact.mul_left (f := fun x : Coord => deriv (winCut a) x.1)
  have hf2s : tsupport (fun x : Coord => deriv (winCut a) x.1 * φ x) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    whe_tsupport_pos ha _ (fun x hx => by simp [hdz x.1 hx])
  have hφ1 : ContDiff ℝ ∞ (fun y => cpd 1 φ y) := whe_cpd_contDiff hφs 1
  have hφ2 : ContDiff ℝ ∞ (fun y => cpd 2 φ y) := whe_cpd_contDiff hφs 2
  have hcyl : Continuous (cylHeatT ν φ) := by
    unfold cylHeatT
    exact ((whe_cpd_contDiff hφs 0).continuous.neg).sub
      (continuous_const.mul ((whe_cpd_contDiff hφ1 1).continuous.add
        (whe_cpd_contDiff hφ2 2).continuous))
  have hcylk : HasCompactSupport (cylHeatT ν φ) := by
    unfold cylHeatT
    have k0 := whe_cpd_compact hφ.compact 0
    have k1 := whe_cpd_compact (whe_cpd_compact hφ.compact 1) 1
    have k2 := whe_cpd_compact (whe_cpd_compact hφ.compact 2) 2
    exact (k0.neg.sub ((k1.add k2).mul_left (f := fun _ : Coord => ν)))
  have hf3c : Continuous (fun x : Coord => winCut a x.1 * cylHeatT ν φ x) :=
    (hcd.continuous.comp continuous_fst).mul hcyl
  have hf3k : HasCompactSupport (fun x : Coord => winCut a x.1 * cylHeatT ν φ x) :=
    hcylk.mul_left (f := fun x : Coord => winCut a x.1)
  have hf3s : tsupport (fun x : Coord => winCut a x.1 * cylHeatT ν φ x) ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    whe_tsupport_pos ha _ (fun x hx => by simp [hzL x.1 hx])
  have J1 := whe_int c r b hc hr hb i _ hψc0 hψc hψsupp
  have J2 := whe_int c r b hc hr hb i _ hf2c hf2k hf2s
  have J3 := whe_int c r b hc hr hb i _ hf3c hf3k hf3s
  -- the integral of `b · flatTransposeS ψ`
  have hsum : ∫ x, b x i * flatTransposeS ν μ (fun y => winCut a y.1 / y.1 * φ y) x
      = μ * (∫ x, b x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ))
        - (∫ x, b x i * ((deriv (winCut a) x.1 * φ x : ℝ) : ℂ))
        + (∫ x, b x i * ((winCut a x.1 * cylHeatT ν φ x : ℝ) : ℂ)) := by
    have hpt : (fun x : Coord => b x i * flatTransposeS ν μ (fun y => winCut a y.1 / y.1 * φ y) x)
        = fun x => (μ * (b x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ))
          - b x i * ((deriv (winCut a) x.1 * φ x : ℝ) : ℂ))
          + b x i * ((winCut a x.1 * cylHeatT ν φ x : ℝ) : ℂ) := by
      funext x
      rw [whe_flat_identity a ha hcd hz ν μ φ hφs x]
      ring
    have K12 : Integrable (fun x : Coord => μ * (b x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ))
        - b x i * ((deriv (winCut a) x.1 * φ x : ℝ) : ℂ)) := (J1.const_mul μ).sub J2
    rw [hpt, integral_add K12 J3, integral_sub (J1.const_mul μ) J2, integral_const_mul]
  -- the integral of the windowed profile
  have hL : ∫ x, windowProfile a b x i * ((cylHeatT ν φ x : ℝ) : ℂ)
      = ∫ x, b x i * ((winCut a x.1 * cylHeatT ν φ x : ℝ) : ℂ) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [windowProfile, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  -- the integral of the window source
  have hR : ∫ x, windowSource a μ G b x i * ((φ x : ℝ) : ℂ)
      = (∫ x, G x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ))
        - μ * (∫ x, b x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ))
        + (∫ x, b x i * ((deriv (winCut a) x.1 * φ x : ℝ) : ℂ)) := by
    have e : (fun x : Coord => windowSource a μ G b x i * ((φ x : ℝ) : ℂ))
        = fun x => (G x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ)
            - μ * (b x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ)))
          + b x i * ((deriv (winCut a) x.1 * φ x : ℝ) : ℂ) := by
      funext x
      simp only [windowSource, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      push_cast
      ring
    have K1 : Integrable (fun x : Coord => G x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ)
        - μ * (b x i * ((winCut a x.1 / x.1 * φ x : ℝ) : ℂ))) :=
      hI2.sub (J1.const_mul μ)
    rw [e, integral_add K1 J2, integral_sub hI2 (J1.const_mul μ), integral_const_mul]
  show ∫ x, windowProfile a b x i * ((cylHeatT ν φ x : ℝ) : ℂ)
      = ∫ x, windowSource a μ G b x i * ((φ x : ℝ) : ℂ)
  rw [hL, hR]
  linear_combination (-1 : ℂ) * hsum + hEq'

end UnforcedLeray.Short.IIb
