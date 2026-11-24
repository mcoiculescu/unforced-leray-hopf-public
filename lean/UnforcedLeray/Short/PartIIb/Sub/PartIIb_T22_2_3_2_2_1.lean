import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1_3
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!


Source: `the November 2 reference manuscript` lines 2085-2093 (train comparison:
the drift `v_c` has bounded derivatives on `s ≤ Σ/ν`) and 2100-2105 (estimates for the regular
backward problem used by the duality argument).

The first plan for this leaf (Bernstein for `|∇φ|² + λφ²` against the global maximum principle)
needs `∇φ` bounded a priori, which `BwdSol` does not give.  Here the Bernstein quantity is
localized in `η` by the cutoff `ζ_{η₀}(x) = θ(η - η₀)`:
`Z_{η₀} = ζ_{η₀}|∇φ|² + λφ²` is bounded above (cutoff; `φ` bounded), it is a subsolution of the
backward operator `L = ∂_r + νΔ + v·∇` for a `λ` independent of `η₀`
(`L|∇φ|² = 2ν|D²φ|² - 2∇φ·(Dv)∇φ`, `L(φ²) = 2ν|∇φ|²`, cutoff cross term absorbed using
`θ'² ≤ Cθ`), and its terminal value is bounded and supported in `|η| ≤ R`.  The subsolution
maximum principle against the decaying barrier of `BwdBarrier` gives
`Z_{η₀} ≤ C(1+η²)^{-N}` uniformly in `η₀` (`localized_decay`); at `η = η₀`, `ζ = 1`.

Contents:
* `BwdOpAt`: value of `U_r + νΔU + b·∇U` at a point; rules `BwdOpMul`, `BwdOpLin`, `BwdOpPd`
  (differentiated equation, from `PdComm` and `PdTimeDeriv`);
* calculus leaves `PdJointSmooth`, `PdComm`, `LapPMul`, `PdTimeDeriv`, `PdPeriodic`,
  `BandBounded`, `CylTestBounded`; the concrete cutoff `cutθ` with `CutProps`, `CutPlane`;
* `BwdMaxPrincipleSub`, proved here from the leaves `MpExistsMax`, `MpSpatial` of `T22/2/3/2/1/3`;
* `localized_decay` (proved) and `bwdWeightedGrad_of` (proved) from `TrainDriftSmoothBdd`,
  `GradLocalSub`, `GradZRegular`, `GradZTerminal`, `CutProps`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-! ## The backward operator at a point -/

/-- The backward operator `U_r + νΔU + b·∇U` at `(r, x)` exists and takes the value `F`. -/
def BwdOpAt (ν : ℝ) (b0 b1 U : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) (F : ℝ) :
    Prop :=
  ∃ D : ℝ, HasDerivAt (fun r' => U r' x) D r ∧
    D + ν * lapP (U r) x + (b0 r x * B0579.pd 0 (U r) x + b1 r x * B0579.pd 1 (U r) x) = F

/-- A time-independent function: `L ζ = νΔζ + b·∇ζ`. -/
theorem bwdOpAt_static (ν : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (ζ : B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) :
    BwdOpAt ν b0 b1 (fun _ y => ζ y) r x
      (ν * lapP ζ x + (b0 r x * B0579.pd 0 ζ x + b1 r x * B0579.pd 1 ζ x)) :=
  ⟨0, hasDerivAt_const r (ζ x), by simp⟩

/-- Smooth drift slices with values and derivatives of orders `1, 2` bounded by `V` on `[s, t]`
(SP 2085-2093). -/
def DriftSmoothBdd (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (s t V : ℝ) : Prop :=
  (∀ r ∈ Icc s t, ∀ i : Fin 2, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => v r y i)) ∧
  ∀ r ∈ Icc s t, ∀ x : B0579.Plane, ∀ i : Fin 2,
    |v r x i| ≤ V ∧ (∀ j : Fin 2, |B0579.pd j (fun y => v r y i) x| ≤ V) ∧
    ∀ j k : Fin 2, |B0579.pd j (B0579.pd k (fun y => v r y i)) x| ≤ V

/-! ## Calculus leaves -/

/-- **Leaf `/1`**: Schwarz symmetry of second partials. -/
def PdComm : Prop :=
  ∀ (f : B0579.Plane → ℝ) (j k : Fin 2), ContDiff ℝ 2 f →
    B0579.pd j (B0579.pd k f) = B0579.pd k (B0579.pd j f)

/-- **Leaf `/2`**: Laplacian of a product. -/
def LapPMul : Prop :=
  ∀ (f g : B0579.Plane → ℝ) (x : B0579.Plane), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    lapP (fun y => f y * g y) x = f x * lapP g x + g x * lapP f x +
      2 * (B0579.pd 0 f x * B0579.pd 0 g x + B0579.pd 1 f x * B0579.pd 1 g x)

/-- **Leaf `/3`**: time and space derivatives commute for a jointly smooth function. -/
def PdTimeDeriv : Prop :=
  ∀ (s t : ℝ) (U A : ℝ → B0579.Plane → ℝ),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2)
      (Icc s t ×ˢ univ) →
    (∀ r ∈ Ioo s t, ∀ x : B0579.Plane, HasDerivAt (fun r' => U r' x) (A r x) r) →
    ∀ (j : Fin 2), ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
      HasDerivAt (fun r' => B0579.pd j (U r') x) (B0579.pd j (A r) x) r

/-- **Leaf `/4`**: spatial partials of a jointly smooth function are jointly smooth. -/
def PdJointSmooth : Prop :=
  ∀ (s t : ℝ) (U : ℝ → B0579.Plane → ℝ) (j : Fin 2),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2)
      (Icc s t ×ˢ univ) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => B0579.pd j (U z.1) z.2)
      (Icc s t ×ˢ univ)

/-- **Leaf `/5`**: partials of a `q`-periodic function are `q`-periodic. -/
def PdPeriodic : Prop :=
  ∀ (c : ℝ) (f : B0579.Plane → ℝ) (j : Fin 2), (∀ x : B0579.Plane, f (x.1 + c, x.2) = f x) →
    ∀ x : B0579.Plane, B0579.pd j f (x.1 + c, x.2) = B0579.pd j f x

/-- **Leaf `/6`**: a jointly continuous `q`-periodic function is bounded on every band
`[s, t] × ℝ × [a, b]`. -/
def BandBounded : Prop :=
  ∀ (c s t a b : ℝ) (G : ℝ → B0579.Plane → ℝ), 0 < c →
    ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2) (Icc s t ×ˢ univ) →
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane, G r (x.1 + c, x.2) = G r x) →
    ∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, x.2 ∈ Icc a b → |G r x| ≤ M

/-- **Leaf `/7`**: a test function on the cylinder is bounded. -/
def CylTestBounded : Prop :=
  ∀ (c : ℝ) (f : B0579.Plane → ℝ), 0 < c → B0579.IsCylTest c f →
    ∃ M : ℝ, ∀ x : B0579.Plane, |f x| ≤ M

/-! ## The cutoff -/

/-- The fixed bump `ρ`: `ρ = 1` on `[-1/2, 1/2]`, `ρ = 0` off `(-1, 1)`, `0 ≤ ρ ≤ 1`. -/
def cutBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The cutoff `θ = ρ²` (so that `θ'² = 4ρ'²θ ≤ Cθ`). -/
def cutθ (y : ℝ) : ℝ := cutBump y ^ 2

/-- The cutoff centred at `η₀` as a function on the plane. -/
def cutζ (η0 : ℝ) (x : B0579.Plane) : ℝ := cutθ (x.2 - η0)

/-- **Leaf `/8`**: properties of `θ`. -/
def CutProps : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutθ ∧ cutθ 0 = 1 ∧ (∀ y : ℝ, 0 ≤ cutθ y ∧ cutθ y ≤ 1) ∧
    (∀ y : ℝ, 1 ≤ |y| → cutθ y = 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, deriv cutθ y ^ 2 ≤ C * cutθ y ∧ |deriv (deriv cutθ) y| ≤ C

/-- **Leaf `/9`**: partials of the plane cutoff. -/
def CutPlane : Prop :=
  ∀ (η0 : ℝ) (x : B0579.Plane), B0579.pd 0 (cutζ η0) x = 0 ∧
    B0579.pd 1 (cutζ η0) x = deriv cutθ (x.2 - η0) ∧
    lapP (cutζ η0) x = deriv (deriv cutθ) (x.2 - η0)

/-! ## Operator rules -/

/-- **Leaf `/11`**: linearity of the backward operator. -/
def BwdOpLin : Prop :=
  ∀ (ν : ℝ) (b0 b1 U W : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) (a FU FW : ℝ),
    ContDiff ℝ 2 (U r) → ContDiff ℝ 2 (W r) →
    BwdOpAt ν b0 b1 U r x FU → BwdOpAt ν b0 b1 W r x FW →
    BwdOpAt ν b0 b1 (fun r x => a * U r x + W r x) r x (a * FU + FW)

/-- **Leaf `/12`**: product rule `L(UW) = U LW + W LU + 2ν ∇U·∇W` (from `LapPMul`). -/
def BwdOpMul : Prop :=
  ∀ (ν : ℝ) (b0 b1 U W : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) (FU FW : ℝ),
    ContDiff ℝ 2 (U r) → ContDiff ℝ 2 (W r) →
    BwdOpAt ν b0 b1 U r x FU → BwdOpAt ν b0 b1 W r x FW →
    BwdOpAt ν b0 b1 (fun r x => U r x * W r x) r x
      (U r x * FW + W r x * FU +
        2 * ν * (B0579.pd 0 (U r) x * B0579.pd 0 (W r) x +
          B0579.pd 1 (U r) x * B0579.pd 1 (W r) x))

/-- **Leaf `/13`**: differentiated equation: if `LU = F` then
`L(∂_j U) = ∂_j F - ∂_j b·∇U` (from `PdComm`, `PdTimeDeriv`). -/
def BwdOpPd : Prop :=
  ∀ (ν s t : ℝ) (b0 b1 U F : ℝ → B0579.Plane → ℝ),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2)
      (Icc s t ×ˢ univ) →
    (∀ r ∈ Ioo s t, ContDiff ℝ 1 (F r) ∧ ContDiff ℝ 1 (b0 r) ∧ ContDiff ℝ 1 (b1 r)) →
    (∀ r ∈ Ioo s t, ∀ x : B0579.Plane, BwdOpAt ν b0 b1 U r x (F r x)) →
    ∀ (j : Fin 2), ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
      BwdOpAt ν b0 b1 (fun r x => B0579.pd j (U r) x) r x
        (B0579.pd j (F r) x - (B0579.pd j (b0 r) x * B0579.pd 0 (U r) x +
          B0579.pd j (b1 r) x * B0579.pd 1 (U r) x))

/-! ## Maximum principle for subsolutions -/

/-- **Leaf `/18`**: weak maximum principle on the periodic strip for a bounded-above subsolution
`Z` (`LZ ≥ 0`) against a coercive supersolution `W` (SP 2100-2105). -/
def BwdMaxPrincipleSub : Prop :=
  ∀ (ν c s t : ℝ) (b0 b1 Z W : ℝ → B0579.Plane → ℝ), 0 < ν → 0 < c → s ≤ t →
    ContinuousOn (fun z : ℝ × B0579.Plane => Z z.1 z.2) (Icc s t ×ˢ univ) →
    (∀ r ∈ Ioo s t, ContDiff ℝ 2 (Z r)) →
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane, Z r (x.1 + c, x.2) = Z r x) →
    (∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, Z r x ≤ M) →
    (∀ r ∈ Ioo s t, ∀ x : B0579.Plane, ∃ F : ℝ, 0 ≤ F ∧ BwdOpAt ν b0 b1 Z r x F) →
    IsBwdSuper ν c s t b0 b1 W →
    (∀ M : ℝ, ∃ L : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, L ≤ |x.2| → M ≤ W r x) →
    (∀ x : B0579.Plane, Z t x ≤ W t x) →
    ∀ r ∈ Icc s t, ∀ x : B0579.Plane, Z r x ≤ W r x

theorem bwdMaxPrincipleSub_of (h1 : MpExistsMax) (h2 : MpSpatial) : BwdMaxPrincipleSub := by
  intro ν c s t b0 b1 U W hν hc hst hUc hUd hUp hUb hUe hW hWc hT
  obtain ⟨hWd, hWp, hWe⟩ := hW
  obtain ⟨M, hM⟩ := hUb
  have sliceW : ∀ r ∈ Icc s t, ContDiff ℝ 2 (W r) := by
    intro r hr
    exact hWd.comp_contDiff (f := fun x : B0579.Plane => (r, x))
      (contDiff_const.prodMk contDiff_id) (fun x => ⟨hr, mem_univ _⟩)
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
          ((hUc.mono (prod_mono hsub subset_rfl)).sub
            (hWd.continuousOn.mono (prod_mono hsub subset_rfl))).sub
            (by fun_prop)
        exact h3)
      (fun r hr x => by simp only [hG]; rw [hUp r (hsub hr) x, hWp r (hsub hr) x])
      ⟨L, fun r hr x hx => by
        have := hL r (hsub hr) x hx
        have := hM r (hsub hr) x
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
    have hUs := hUd r0 hr0s
    have hWs := sliceW r0 hr0m
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
    obtain ⟨D, hD, hDle⟩ := hWe r0 hr0s x0
    obtain ⟨F, hF0, D', hD', hD'eq⟩ := hUe r0 hr0s x0
    have hft : HasDerivAt (fun r => G r x0) (D' - D + δ) r0 := by
      have h4 : HasDerivAt (fun r : ℝ => δ * (t - r + 1)) (-δ) r0 := by
        have := ((hasDerivAt_id r0).const_sub t |>.add_const 1).const_mul δ
        simpa using this
      exact ((hD'.sub hD).sub h4).congr_deriv (by ring)
    have hle := mp_time_step (fun r => G r x0) _ r0 t hft hr0t
      (fun r hr => hmax r ⟨le_trans hr0.1 hr.1, hr.2⟩ x0)
    have e0 : B0579.pd 0 (U r0) x0 = B0579.pd 0 (W r0) x0 := by linarith
    have e1 : B0579.pd 1 (U r0) x0 = B0579.pd 1 (W r0) x0 := by linarith
    rw [e0, e1] at hD'eq
    have hnn : 0 ≤ ν * lapP (W r0) x0 - ν * lapP (U r0) x0 := by
      rw [← mul_sub]; exact mul_nonneg hν.le (by linarith)
    linarith
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
        hUc.comp (continuousOn_id.prodMk continuousOn_const)
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

/-! ## The barrier argument for a localized family -/

/-- A family `Z_{η₀}` of bounded-above periodic subsolutions with terminal values bounded by `M`
and vanishing for `|η| > R` lies below `C(1+η²)^{-N}` uniformly in `η₀`; so does any `Q` with
`Q(r, x) ≤ Z_{x.2}(r, x)`. -/
theorem localized_decay (hMP : BwdMaxPrincipleSub) (hB : BwdBarrier)
    (ν c s t V : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (hν : 0 < ν) (hc : 0 < c) (hst : s ≤ t)
    (hV : 0 ≤ V) (hb : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |b0 r x| ≤ V ∧ |b1 r x| ≤ V)
    (Z : ℝ → ℝ → B0579.Plane → ℝ)
    (hZc : ∀ η0 : ℝ, ContinuousOn (fun z : ℝ × B0579.Plane => Z η0 z.1 z.2) (Icc s t ×ˢ univ))
    (hZd : ∀ η0 : ℝ, ∀ r ∈ Ioo s t, ContDiff ℝ 2 (Z η0 r))
    (hZp : ∀ η0 : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, Z η0 r (x.1 + c, x.2) = Z η0 r x)
    (hZb : ∀ η0 : ℝ, ∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, Z η0 r x ≤ M)
    (hZs : ∀ η0 : ℝ, ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
      ∃ F : ℝ, 0 ≤ F ∧ BwdOpAt ν b0 b1 (Z η0) r x F)
    (M R : ℝ) (hZt : ∀ η0 : ℝ, ∀ x : B0579.Plane, Z η0 t x ≤ M ∧ (R < |x.2| → Z η0 t x ≤ 0))
    (Q : ℝ → B0579.Plane → ℝ) (hQ : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, Q r x ≤ Z x.2 r x) :
    ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, Q r x * (1 + x.2 ^ 2) ^ N ≤ C := by
  intro N
  set N' : ℝ := max N 0 with hN'
  have hN'0 : 0 ≤ N' := le_max_right _ _
  obtain ⟨K1, K2, hK⟩ := hB ν V N' hν hV
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  set A : ℝ := max M 0 * (1 + R ^ 2) ^ N' with hA
  have hA0 : 0 ≤ A := mul_nonneg hM0 (by positivity)
  have key : ∀ η0 : ℝ, ∀ ε : ℝ, 0 < ε → ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
      Z η0 r x ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') +
        ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
    intro η0 ε hε
    refine hMP ν c s t b0 b1 (Z η0) _ hν hc hst (hZc η0) (hZd η0) (hZp η0) (hZb η0) (hZs η0)
      (hK c s t b0 b1 hb A ε hA0 hε.le) ?_ ?_
    · intro M'
      set m : ℝ := Real.exp (-(|K2| * (t - s))) with hm
      have hm0 : 0 < m := Real.exp_pos _
      have hεm : 0 < ε * m := mul_pos hε hm0
      refine ⟨|M'| / (ε * m), fun r hr x hx => ?_⟩
      have hexp : m ≤ Real.exp (K2 * (t - r)) := by
        apply Real.exp_le_exp.2
        have h1 : -|K2| ≤ K2 := neg_abs_le K2
        have h2 : K2 ≤ |K2| := le_abs_self K2
        have h3 : 0 ≤ t - r := by linarith [hr.2]
        have h4 : t - r ≤ t - s := by linarith [hr.1]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) h3, mul_nonneg (abs_nonneg K2) (sub_nonneg.2 h4),
          mul_nonneg (sub_nonneg.2 h1) h3]
      have hsq : |x.2| ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow]
        calc |x.2| = Real.sqrt (x.2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
      have hg : 0 ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') := by positivity
      have h5 : |M'| / (ε * m) ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := le_trans hx hsq
      have h6 : |M'| ≤ ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
        have : |M'| ≤ (ε * m) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
          have := (div_le_iff₀ hεm).1 h5
          linarith
        refine le_trans this ?_
        have hp : 0 ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by positivity
        have : ε * m ≤ ε * Real.exp (K2 * (t - r)) := by gcongr
        exact mul_le_mul_of_nonneg_right this hp
      show M' ≤ _
      linarith [le_abs_self M']
    · intro x
      have e1 : Real.exp (K1 * (t - t)) = 1 := by simp
      have e2 : Real.exp (K2 * (t - t)) = 1 := by simp
      show Z η0 t x ≤ A * Real.exp (K1 * (t - t)) * (1 + x.2 ^ 2) ^ (-N') +
        ε * Real.exp (K2 * (t - t)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2)
      rw [e1, e2]
      have hp : 0 ≤ ε * 1 * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by positivity
      have hg : 0 ≤ A * 1 * (1 + x.2 ^ 2) ^ (-N') := by positivity
      obtain ⟨hZM, hZR⟩ := hZt η0 x
      by_cases hx : R < |x.2|
      · have := hZR hx; linarith
      · rw [not_lt] at hx
        have hx2 : x.2 ^ 2 ≤ R ^ 2 := by
          have := sq_abs x.2
          nlinarith [abs_nonneg x.2, mul_nonneg (sub_nonneg.2 hx)
            (add_nonneg (abs_nonneg x.2) (le_trans (abs_nonneg _) hx))]
        have hpos : 0 < 1 + x.2 ^ 2 := by positivity
        have hle : (1 + R ^ 2) ^ (-N') ≤ (1 + x.2 ^ 2) ^ (-N') :=
          Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
        have hRpos : 0 < 1 + R ^ 2 := by positivity
        have hid : (1 + R ^ 2) ^ N' * (1 + R ^ 2) ^ (-N') = 1 := by
          rw [← Real.rpow_add hRpos]; simp
        calc Z η0 t x ≤ max M 0 := le_trans hZM (le_max_left _ _)
          _ = A * (1 + R ^ 2) ^ (-N') := by rw [hA, mul_assoc, hid, mul_one]
          _ ≤ A * (1 + x.2 ^ 2) ^ (-N') := mul_le_mul_of_nonneg_left hle hA0
          _ ≤ _ := by linarith
  refine ⟨A * Real.exp (|K1| * (t - s)), fun r hr x => ?_⟩
  have hpos : 0 < 1 + x.2 ^ 2 := by positivity
  have hb' : Q r x ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') := by
    set Phi : ℝ := Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) with hPhi
    have hPhi0 : 0 ≤ Phi := by positivity
    refine le_of_forall_pos_le_add fun e he => ?_
    have := key x.2 (e / (Phi + 1)) (by positivity) r hr x
    have h2 : e / (Phi + 1) * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) ≤ e := by
      rw [mul_assoc, ← hPhi, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith [hQ r hr x]
  have hK1 : Real.exp (K1 * (t - r)) ≤ Real.exp (|K1| * (t - s)) := by
    apply Real.exp_le_exp.2
    have h3 : 0 ≤ t - r := by linarith [hr.2]
    have h4 : t - r ≤ t - s := by linarith [hr.1]
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self K1)) h3,
      mul_nonneg (abs_nonneg K1) (sub_nonneg.2 h4)]
  have hid : (1 + x.2 ^ 2) ^ (-N') * (1 + x.2 ^ 2) ^ N' = 1 := by
    rw [← Real.rpow_add hpos]; simp
  have hC0 : 0 ≤ A * Real.exp (|K1| * (t - s)) := by positivity
  have hwN : 0 ≤ (1 + x.2 ^ 2) ^ N := by positivity
  rcases le_or_gt (Q r x) 0 with hQ0 | hQ0
  · nlinarith
  · have hN : (1 + x.2 ^ 2) ^ N ≤ (1 + x.2 ^ 2) ^ N' :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x.2]) (le_max_left _ _)
    calc Q r x * (1 + x.2 ^ 2) ^ N ≤ Q r x * (1 + x.2 ^ 2) ^ N' :=
          mul_le_mul_of_nonneg_left hN hQ0.le
      _ ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') * (1 + x.2 ^ 2) ^ N' :=
          mul_le_mul_of_nonneg_right hb' (by positivity)
      _ = A * Real.exp (K1 * (t - r)) := by rw [mul_assoc, hid, mul_one]
      _ ≤ A * Real.exp (|K1| * (t - s)) := mul_le_mul_of_nonneg_left hK1 hA0

/-! ## The gradient family and its leaves -/

/-- `|∇φ|²` as a function of `(r, x)`. -/
def gradSq (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) : ℝ :=
  B0579.pd 0 (φ r) x * B0579.pd 0 (φ r) x + B0579.pd 1 (φ r) x * B0579.pd 1 (φ r) x

/-- The localized Bernstein quantity `ζ_{η₀}|∇φ|² + λφ²`. -/
def gradZ (lam η0 : ℝ) (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) : ℝ :=
  cutζ η0 x * gradSq φ r x + lam * (φ r x * φ r x)

/-- **Leaf `/14`** (SP 2085-2093): the train drift restricted to `[s, t] ⊆ [0, Σ/ν]` has smooth
slices and bounded derivatives of orders `≤ 2` (`TrainSol.isTrain.smooth_v`, `DriftC2Bdd`). -/
def TrainDriftSmoothBdd : Prop :=
  ∀ (Sg ν c V : ℝ) (tr : B0140.TrainSol ν c), DriftC2Bdd tr.v (Sg / ν) V →
    ∀ s t : ℝ, 0 ≤ s → t ≤ Sg / ν → DriftSmoothBdd tr.v s t V

/-- **Leaf `/10`**: the pointwise algebra of the gradient Bernstein computation.  With
`P = p₀² + p₁²`, `H_{kj} = ∂_k∂_jφ`, `d_{jk} = ∂_j b_k`, `z = ∇ζ`, `lz = Δζ`:
`ζ(2p·F + 2ν|H|²) ≥ -4VP + 2νζ|H|²`, `P·Lζ ≥ -P(νC + V(1+C))`,
`2νζ|H|² + 4ν z·(Hp) ≥ -2νC P` (sum of squares `Σ(ζH_{kj} + z_k p_j)²` and `|z|² ≤ Cζ`). -/
def GradAlg : Prop :=
  ∀ (ν V Cθ lam ζ z0 z1 lz b0 b1 d00 d01 d10 d11 p0 p1 H00 H01 H10 H11 : ℝ),
    0 < ν → 0 ≤ V → 0 ≤ Cθ → 0 ≤ ζ → ζ ≤ 1 → z0 ^ 2 + z1 ^ 2 ≤ Cθ * ζ → |lz| ≤ Cθ →
    |b0| ≤ V → |b1| ≤ V → |d00| ≤ V → |d01| ≤ V → |d10| ≤ V → |d11| ≤ V →
    5 * V + V * Cθ + 3 * ν * Cθ ≤ 2 * ν * lam →
    0 ≤ ζ * (2 * p0 * (-(d00 * p0 + d01 * p1)) + 2 * ν * (H00 ^ 2 + H10 ^ 2) +
          (2 * p1 * (-(d10 * p0 + d11 * p1)) + 2 * ν * (H01 ^ 2 + H11 ^ 2))) +
        (p0 ^ 2 + p1 ^ 2) * (ν * lz + (b0 * z0 + b1 * z1)) +
        2 * ν * (z0 * (2 * p0 * H00 + 2 * p1 * H01) + z1 * (2 * p0 * H10 + 2 * p1 * H11)) +
        lam * (2 * ν * (p0 ^ 2 + p1 ^ 2))

/-- **Leaf `/15`** (SP 2100-2105): the localized gradient quantity is a subsolution of the
backward operator, for a `λ` independent of the centre `η₀`. -/
def GradLocalSub : Prop :=
  ∀ (ν c s t V : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ψ : B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ), 0 < ν → 0 ≤ V → DriftSmoothBdd v s t V →
    BwdSol ν c s t v ψ φ →
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ η0 : ℝ, ∀ r ∈ Ioo s t, ∀ x : B0579.Plane, ∃ F : ℝ, 0 ≤ F ∧
      BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1) (gradZ lam η0 φ) r x F

/-- **Leaf `/16`**: regularity, periodicity and an upper bound for the gradient family. -/
def GradZRegular : Prop :=
  ∀ (ν c s t : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ψ : B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ), 0 < c → BwdSol ν c s t v ψ φ → ∀ lam η0 : ℝ,
    ContinuousOn (fun z : ℝ × B0579.Plane => gradZ lam η0 φ z.1 z.2) (Icc s t ×ˢ univ) ∧
    (∀ r ∈ Ioo s t, ContDiff ℝ 2 (gradZ lam η0 φ r)) ∧
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane, gradZ lam η0 φ r (x.1 + c, x.2) = gradZ lam η0 φ r x) ∧
    ∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, gradZ lam η0 φ r x ≤ M

/-- **Leaf `/17`**: the terminal values of the gradient family are uniformly bounded and vanish
for `|η| > R`. -/
def GradZTerminal : Prop :=
  ∀ (ν c s t : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (ψ : B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ), 0 < c → B0579.IsCylTest c ψ → BwdSol ν c s t v ψ φ →
    ∀ lam : ℝ, ∃ M R : ℝ, ∀ η0 : ℝ, ∀ x : B0579.Plane,
      gradZ lam η0 φ t x ≤ M ∧ (R < |x.2| → gradZ lam η0 φ t x ≤ 0)

/-- `BwdWeightedGrad` from the leaves. -/
theorem bwdWeightedGrad_of (hMP : BwdMaxPrincipleSub) (hB : BwdBarrier)
    (hD : TrainDriftSmoothBdd) (hGS : GradLocalSub) (hGR : GradZRegular)
    (hGT : GradZTerminal) (hcut : CutProps) : BwdWeightedGrad := by
  intro Sg ν c δ V hSg hν hc hδ tr htr hV2 s t hs hst ht ψ hψ φ hφ _hW
  have hDS := hD Sg ν c V tr hV2 s t hs ht
  have hV0 : 0 ≤ V := le_trans (abs_nonneg _) (hDS.2 s ⟨le_rfl, hst⟩ (0, 0) 0).1
  obtain ⟨lam, hlam0, hsub⟩ := hGS ν c s t V tr.v ψ φ hν hV0 hDS hφ
  obtain ⟨M, R, hMR⟩ := hGT ν c s t tr.v ψ φ hc hψ hφ lam
  have hreg := hGR ν c s t tr.v ψ φ hc hφ lam
  have hdec := localized_decay hMP hB ν c s t V (fun r x => tr.v r x 0) (fun r x => tr.v r x 1)
    hν hc hst hV0 (fun r hr x => ⟨(hDS.2 r hr x 0).1, (hDS.2 r hr x 1).1⟩)
    (fun η0 => gradZ lam η0 φ) (fun η0 => (hreg η0).1) (fun η0 => (hreg η0).2.1)
    (fun η0 => (hreg η0).2.2.1) (fun η0 => (hreg η0).2.2.2) hsub M R hMR (gradSq φ)
    (fun r _ x => by
      have h1 : cutζ x.2 x = 1 := by simp [cutζ, hcut.2.1]
      have h2 : 0 ≤ lam * (φ r x * φ r x) := mul_nonneg hlam0 (mul_self_nonneg _)
      show gradSq φ r x ≤ cutζ x.2 x * gradSq φ r x + lam * (φ r x * φ r x)
      rw [h1, one_mul]; linarith)
  intro N
  obtain ⟨C, hC⟩ := hdec (2 * N)
  refine ⟨1 + 2 * C, fun r hr x => ?_⟩
  have hw0 : 0 ≤ (1 + x.2 ^ 2) ^ N := by positivity
  have hw2 : (1 + x.2 ^ 2) ^ (2 * N) = ((1 + x.2 ^ 2) ^ N) ^ 2 := by
    rw [show (2 : ℝ) * N = N * 2 by ring, Real.rpow_mul (by positivity), Real.rpow_two]
  have hCx := hC r hr x
  rw [hw2] at hCx
  simp only [gradSq] at hCx
  generalize B0579.pd 0 (φ r) x = p0 at hCx ⊢
  generalize B0579.pd 1 (φ r) x = p1 at hCx ⊢
  generalize (1 + x.2 ^ 2) ^ N = w at hCx hw0 ⊢
  have ha : (|p0| + |p1|) ^ 2 ≤ 2 * (p0 * p0 + p1 * p1) := by
    nlinarith [sq_nonneg (|p0| - |p1|), sq_abs p0, sq_abs p1]
  have hq : ((|p0| + |p1|) * w) ^ 2 ≤ 2 * ((p0 * p0 + p1 * p1) * w ^ 2) := by
    rw [mul_pow]; nlinarith [sq_nonneg w]
  nlinarith [sq_nonneg ((|p0| + |p1|) * w - 1), sq_nonneg ((|p0| + |p1|) * w)]

end UnforcedLeray.Short.IIb
