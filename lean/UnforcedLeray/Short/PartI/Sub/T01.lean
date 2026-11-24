import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part I, task `PartI:T01`: the mean equations `sct:mean` of the train (conditional)

Source of record: `the November 2 reference manuscript`, lines 397-404, eq.
`sct:mean`: for the mean stream `S = \bar ψ` of the train,
`S_s - ν S_ηη = g := \overline{v₁ v₂}`, `\bar v₁ = -S_η`, `\bar v₂ = 0`; "the last equality follows
from divergence and finite energy".

Route (all statements for a train `tr : B0140.TrainSol ν c`, `ν, c > 0`).

* `u := \bar v₁` satisfies the averaged first momentum equation `u_s + g_η = ν u_ηη`
  (`TrainMeanMomentumU`: average the first component; the `∂_q`-terms vanish by periodicity).
* With `u = -S_η` (`TrainMeanV1`) and the joint smoothness of `S` (`TrainStreamSmooth` +
  `HmeanContDiff`) this says that `η ↦ S_s - ν S_ηη - g` has zero derivative
  (`TrainMeanMomentumEta`), hence is a constant `C(s)`.
* `C(s) = 0` by `ConstZeroLemma`: `S_s → 0` at `+∞` (`TrainMeanStreamTimeDecay`, from the decay of
  `∂_sψ`), `g ∈ L¹(ℝ)` and `S_η ∈ L²(ℝ)` (`TrainMeanEnergy`, from finite energy). Indeed
  `ν S_ηη = S_s - g - C` would make `S_η` grow linearly if `C ≠ 0`.

`TrainStreamSmooth` is true for the global train of Gallay-Slijepcevic but is NOT a consequence of
the fields of `B0140.IsTrain` alone (which gives no time regularity of the stream `ψ`, only the

the statements that need it are stated for trains of the Gallay-Slijepcevic class `IsBUCTrain`
(`TrainClass.lean`: all spatial derivatives of `v` bounded on `[0,S] × ℝ²`).  For such trains the
smoothness of `ψ` is *derived* (tasks `PartI:T01/1`, `PartI:TC/1-8`): the mean stream satisfies
`S(s,η) = S(s,0) - ∫₀^η \bar v₁(s,t) dt`, and `S(s,0)` is the improper integral
`∫₀^∞ \bar v₁(s,t) dt`, whose increments in `s` are computed from the averaged momentum equation
(`TrainMeanMomentumU`) and the decay of `∂_η \bar v₁`, `g` at `+∞` (a consequence of the decay of
`ψ` and the bounded derivatives).  The same computation gives `S_s = g - ν ∂_η \bar v₁`
(`TrainMeanStreamDeriv`, task `PartI:T01/2`), so no decay of `∂_sψ` is needed
(`TrainStreamTimeDecay` below is not used by this route).

The unconditional statement is the task `PartI:T01`
(`Short/PartI/Tasks/TrainMeanEquations.lean`); the lemma tasks `PartI:T01/1 ... T01/11` prove
each `Prop` below (files `Short/PartI/Tasks/TrainMeanEquations/*.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-! ### The leaf statements -/

/-- **Time regularity of the stream** (source lines 261-288, 397: the train is smooth and its
stream `ψ` is the decaying stream function). For a train of the BUC class, `ψ` is jointly `C^∞`
in `(s, q, η)` for `s > 0`.  Not a consequence of the fields of `B0140.IsTrain` alone; proved from
the class in task `PartI:T01/1`. -/
def TrainStreamSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **Decay of `∂_sψ`** (source lines 397-404): for `s > 0`, `∂_sψ(s, q, η) → 0` as `|η| → ∞`,
uniformly in `q` (the time derivative of the decaying stream decays like the stream). Not a
consequence of the fields of `B0140.IsTrain`.  **Obsolete for the BUC route**: it is not needed
(`TrainMeanStreamDeriv` below gives `S_s → 0` directly); kept as an unproved statement because a
draft file refers to it. -/
def TrainStreamTimeDecay : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    Tendsto (fun z : Plane => deriv (fun r => tr.ψ r z) s)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **Horizontal averaging preserves smoothness**: if `f` is jointly `C^∞` in `(s, q, η)` for
`s > 0`, so is `(s, η) ↦ c⁻¹ ∫_{-c/2}^{c/2} f(s, q, η) dq` (differentiation under the integral
over the compact `q`-interval). -/
def HmeanContDiff : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ → Plane → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => hmean c (f x.1) x.2) (Ioi 0 ×ˢ univ)

/-- **Age derivative commutes with the horizontal average**: for `f` jointly `C^∞` for `s > 0`,
`∂_s \bar f = \overline{∂_s f}`. -/
def HmeanDerivS : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ → Plane → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ s : ℝ, 0 < s → ∀ η : ℝ,
      deriv (fun r => hmean c (f r) η) s = hmean c (fun z => deriv (fun r => f r z) s) η

/-- **`\bar v₁ = -S_η`** (source line 399, from `v = ∇^⊥ψ`, i.e. `v₁ = -∂_ηψ`; differentiate the
`q`-average under the integral). -/
def TrainMeanV1 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s → ∀ η : ℝ,
    hmean c (fun z => tr.v s z 0) η = -deriv (fun e => meanStream tr s e) η

/-- **`\bar v₂ = 0`** (source lines 399-404, "follows from divergence and finite energy").
Route: `v₂ = ∂_qψ`; `ψ(s)` is `c`-periodic in `q` (the difference `ψ(q + c, η) - ψ(q, η)` has
zero gradient and tends to `0` as `|η| → ∞`), so the `q`-average of `∂_qψ` vanishes. -/
def TrainMeanV2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s → ∀ η : ℝ,
    hmean c (fun z => tr.v s z 1) η = 0

/-- **The averaged first momentum equation** (source lines 397-404): `u = \bar v₁` satisfies
`u_s + g_η = ν u_ηη` for `s > 0` (average the first component of `∂_sv + v·∇v - νΔv + ∇p = 0`;
with `div v = 0`, `v·∇v₁ = ∂_q(v₁²) + ∂_η(v₁v₂)`; the `∂_q`-terms `∂_q(v₁²)`, `∂_qp`, `∂_q²v₁`
average to `0` by `c`-periodicity). -/
def TrainMeanMomentumU : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s → ∀ η : ℝ,
    deriv (fun r => hmean c (fun z => tr.v r z 0) η) s + deriv (meanStress tr s) η =
      ν * deriv (deriv (fun e => hmean c (fun z => tr.v s z 0) e)) η

/-- **The averaged momentum equation for the mean stream**: for `s > 0` the function
`η ↦ S_s - ν S_ηη - g` is differentiable with derivative `0` (from `TrainMeanMomentumU`,
`TrainMeanV1`, the smoothness of `S` and the symmetry of mixed partial derivatives). -/
def TrainMeanMomentumEta : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ η : ℝ,
    HasDerivAt (fun η' => deriv (fun r => meanStream tr r η') s -
        ν * deriv (deriv (fun e => meanStream tr s e)) η' - meanStress tr s η') 0 η

/-- **The age derivative of the mean stream** (source lines 397-404; combines `S_s - ν S_ηη = g`
with `\bar v₁ = -S_η`): for a train of the BUC class, `s > 0` and every `η`,
`S_s(s,η) = g(s,η) - ν ∂_η \bar v₁(s,η)`.  Route (task `PartI:T01/2`): `S(s,η) = S(s,0) -
∫₀^η \bar v₁(s,t) dt` (`TrainMeanV1`); `d/ds ∫₀^η \bar v₁ = ν(∂_η\bar v₁(η) - ∂_η\bar v₁(0)) -
(g(η) - g(0))` (`TrainMeanMomentumU`); `d/ds S(s,0) = g(s,0) - ν ∂_η \bar v₁(s,0)`
(`MeanStreamIncrement`, a consequence of the decay of `g` and `∂_η\bar v₁` at `+∞`). -/
def TrainMeanStreamDeriv : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s → ∀ η : ℝ,
    deriv (fun r => meanStream tr r η) s =
      meanStress tr s η - ν * deriv (fun e => hmean c (fun z => tr.v s z 0) e) η

/-- **Finite energy gives integrability** (source lines 397-404): for `s > 0` the mean stress
`g = \overline{v₁v₂}` is in `L¹(ℝ)` (as `|v₁v₂| ≤ |v|²/2`) and `S_η = -\bar v₁` is in `L²(ℝ)`
(Cauchy-Schwarz in `q`), from `finite_energy` of the train. -/
def TrainMeanEnergy : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s →
    Integrable (meanStress tr s) volume ∧
      MemLp (deriv (fun e => meanStream tr s e)) 2 volume

/-- **Decay of the age derivative of the mean stream**: for `s > 0`, `S_s(s, η) → 0` as
`η → +∞` for a train of the BUC class (via `TrainMeanStreamDeriv`: `S_s = g - ν ∂_η \bar v₁`, and
`g`, `∂_η \bar v₁` tend to `0` at `+∞`; the original route `S_s = \overline{∂_sψ}`, `∂_sψ → 0`
(`HmeanDerivS`, `TrainStreamTimeDecay`) is not needed). -/
def TrainMeanStreamTimeDecay : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    Tendsto (fun η : ℝ => deriv (fun r => meanStream tr r η) s) atTop (𝓝 0)

/-- **A bounded-drift lemma** (pure real analysis): if `b ∈ L²(ℝ)` is differentiable with
`ν b' = a - g - C`, where `a` is continuous with `a → 0` at `+∞` and `g ∈ L¹(ℝ)`, then `C = 0`.
(If `C ≠ 0`, then for large `x` one gets `|b(x)| ≥ κ x - K` with `κ > 0`, contradicting
`b ∈ L²`.) -/
def ConstZeroLemma : Prop :=
  ∀ (ν C : ℝ) (a b b' g : ℝ → ℝ), 0 < ν →
    (∀ x, HasDerivAt b (b' x) x) → Continuous a → Integrable g volume → MemLp b 2 volume →
    Tendsto a atTop (𝓝 0) → (∀ x, a x - ν * b' x - g x = C) → C = 0

/-! ### Regularity of slices of a jointly smooth function -/

/-- The slice `e ↦ f (s, e)` of a function that is `C^∞` on `(0, ∞) × ℝ` is `C^∞`. -/
theorem t01_contDiff_slice {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) {s : ℝ}
    (hs : 0 < s) : ContDiff ℝ ∞ (fun e : ℝ => f (s, e)) := by
  have hc : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) := contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun e : ℝ => ((s, e) : ℝ × ℝ)) univ (Ioi 0 ×ˢ univ) := by
    intro e _
    exact ⟨hs, mem_univ e⟩
  exact contDiffOn_univ.1 (hf.comp hc.contDiffOn hmaps)

/-- The age derivative `e ↦ ∂_s f (s, e)` of a function that is `C^∞` on `(0, ∞) × ℝ` is
continuous. -/
theorem t01_continuous_deriv_slice {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) {s : ℝ}
    (hs : 0 < s) : Continuous (fun e : ℝ => deriv (fun r => f (r, e)) s) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ f) (Ioi 0 ×ˢ univ) :=
    hf.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hform : ∀ e : ℝ, deriv (fun r => f (r, e)) s = fderiv ℝ f (s, e) (1, 0) := by
    intro e
    have hmem : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
    have hdiff : DifferentiableAt ℝ f (s, e) :=
      (hf.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    have hpath : HasDerivAt (fun r : ℝ => ((r, e) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s e)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt s hpath).deriv
  have hpt : Continuous (fun e : ℝ => ((s, e) : ℝ × ℝ)) := continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun e : ℝ => ((s, e) : ℝ × ℝ)) univ (Ioi 0 ×ˢ univ) := by
    intro e _
    exact ⟨hs, mem_univ e⟩
  have hcomp : ContinuousOn (fun e : ℝ => fderiv ℝ f (s, e)) univ :=
    hfd.comp hpt.continuousOn hmaps
  have hev : Continuous (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L ((1, 0) : ℝ × ℝ)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous
  have : ContinuousOn (fun e : ℝ => fderiv ℝ f (s, e) ((1, 0) : ℝ × ℝ)) univ :=
    hev.comp_continuousOn hcomp
  simp_rw [hform]
  exact continuousOn_univ.1 this

/-! ### The conditional theorem -/

/-- **`PartI:T01`, conditional form.** The mean equations `sct:mean` of the train follow from the
leaf statements above. -/
theorem trainMeanEquations_of
    (hψ : TrainStreamSmooth) (hH : HmeanContDiff) (hV1 : TrainMeanV1) (hV2 : TrainMeanV2)
    (hMom : TrainMeanMomentumEta) (hEn : TrainMeanEnergy)
    (hDec : TrainMeanStreamTimeDecay) (hZ : ConstZeroLemma) : TrainMeanEquations := by
  intro ν c hν hc tr hbuc
  have hS : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hH c hc tr.ψ (hψ ν c hν hc tr hbuc)
  refine ⟨hS, fun s hs η => ⟨?_, hV1 ν c hν hc tr s hs η, hV2 ν c hν hc tr s hs η⟩⟩
  -- the three functions of `η` entering the identity
  set b : ℝ → ℝ := deriv (fun e => meanStream tr s e) with hb
  have hslice : ContDiff ℝ ∞ (fun e : ℝ => meanStream tr s e) :=
    t01_contDiff_slice (f := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hS hs
  have hbdiff : Differentiable ℝ b := (contDiff_infty_iff_deriv.1 hslice).2.differentiable (by simp)
  have hacont : Continuous (fun e : ℝ => deriv (fun r => meanStream tr r e) s) :=
    t01_continuous_deriv_slice (f := fun x : ℝ × ℝ => meanStream tr x.1 x.2) hS hs
  -- the combination `F η' = S_s - ν S_ηη - g` is constant in `η'`
  have hF : ∀ x, HasDerivAt (fun η' => deriv (fun r => meanStream tr r η') s -
      ν * deriv b η' - meanStress tr s η') 0 x := hMom ν c hν hc tr hbuc s hs
  have hconst : ∀ x y, (deriv (fun r => meanStream tr r x) s - ν * deriv b x - meanStress tr s x) =
      (deriv (fun r => meanStream tr r y) s - ν * deriv b y - meanStress tr s y) :=
    is_const_of_deriv_eq_zero (fun y => (hF y).differentiableAt) (fun y => (hF y).deriv)
  obtain ⟨hg, hb2⟩ := hEn ν c hν hc tr s hs
  have hzero : (deriv (fun r => meanStream tr r 0) s - ν * deriv b 0 - meanStress tr s 0) = 0 :=
    hZ ν _ (fun e => deriv (fun r => meanStream tr r e) s) b (deriv b) (meanStress tr s) hν
      (fun x => (hbdiff x).hasDerivAt) hacont hg hb2 (hDec ν c hν hc tr hbuc s hs)
      (fun x => hconst x 0)
  have := hconst η 0
  rw [hzero] at this
  show deriv (fun r => meanStream tr r η) s - ν * deriv b η = meanStress tr s η
  linarith

end UnforcedLeray.Short.PartI
