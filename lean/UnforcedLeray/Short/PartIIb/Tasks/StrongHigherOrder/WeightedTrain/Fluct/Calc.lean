import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct.Core
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets.Calc
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanDerivS
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceIntegralCalculus
import UnforcedLeray.Cons.C03Background.RawLift

/-!
# The calculus leaf `FluctJetCalc` (step (d) of `sct:transverse`)

Helper of `Tail.lean`.  Source
`the November 2 reference manuscript` 496-502
(`ω = Δψ` for `v = ∇^⊥ψ`; the fluctuation `ψ̃ = ψ - \bar ψ` carries the nonzero `q`-modes).

Notation: `U = (0, ∞) × ℝ²`, `Ψ(s, z) = ψ(s, z)` (jointly `C^∞` on `U`, `PartI.trainStreamSmooth`),
`Ψb(s, z) = \bar ψ(s, η)` (`C^∞`, `PartI.hmeanContDiff`), `G = Ψ - Ψb`.  Directional derivatives
along words of directions are `PartI.AgeDeriv.dW`; the age jet is the word
`(0,u₁) ⋯ (0,u_j) s^ℓ` (`ageJet_eq_dW`).  Then:

* `C²` and `c`-periodicity in `q`: `dW L G` is smooth on `U` and invariant under the translations
  `(0, (c, 0))` because `G` is (`dW_translate`, `Cons.C03.stream_periodic_of_isTrain`);
* zero `q`-means: `G` has zero means, and a derivative of a smooth periodic function with zero
  means has zero means (`dW_zero_mean`: `∂_s` by `PartI.hmeanDerivS`, `∂_η` by
  `PartI.sliceIntegralCalculus`, `∂_q` by the fundamental theorem of calculus over a period);
* `∂_q W_u = W_{(e_q, u)}` (`partialQ_dW`);
* `Δ W_u = (∂_s^ℓ D^j ω)(u) + h(η)`: `ω = ∂_q²Ψ + ∂_η²Ψ` on `U` (`curl_eq_dW`), the words commute
  (`AgeDeriv.dW_perm`), and the `Ψb`-words do not depend on `q` (`dW_translate`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIb.WeightedTrainFluctAux.FluctTail

open UnforcedLeray
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartI.AgeDeriv
open UnforcedLeray.Cyl (Plane)

/-- The open half-space `s > 0` of `ℝ × ℝ²`. -/
abbrev UU : Set (ℝ × Plane) := Ioi (0 : ℝ) ×ˢ (univ : Set Plane)

theorem isOpen_UU : IsOpen UU := isOpen_Ioi.prod isOpen_univ

theorem mem_UU {s : ℝ} (hs : 0 < s) (z : Plane) : ((s, z) : ℝ × Plane) ∈ UU := ⟨hs, mem_univ _⟩

/-- The `q`-direction. -/
def eQ : ℝ × Plane := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))

/-- The `η`-direction. -/
def eH : ℝ × Plane := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))

theorem dW_diffAt {g : ℝ × Plane → ℝ} (hg : ContDiffOn ℝ ∞ g UU) (L : List (ℝ × Plane))
    {x : ℝ × Plane} (hx : x ∈ UU) : DifferentiableAt ℝ (dW L g) x :=
  ((dW_contDiffOn isOpen_UU hg L).contDiffAt (isOpen_UU.mem_nhds hx)).differentiableAt (by simp)

/-- The `q`-line derivative. -/
theorem fderiv_q_line {φ : ℝ × Plane → ℝ} {r q η : ℝ}
    (hφ : DifferentiableAt ℝ φ (r, (q, η))) :
    fderiv ℝ φ (r, (q, η)) eQ = deriv (fun t => φ (r, (t, η))) q := by
  have hl : HasDerivAt (fun t : ℝ => ((r, (t, η)) : ℝ × Plane)) eQ q :=
    (hasDerivAt_const q r).prodMk ((hasDerivAt_id' q).prodMk (hasDerivAt_const q η))
  exact ((hφ.hasFDerivAt).comp_hasDerivAt q hl).deriv.symm

/-- The `η`-line derivative. -/
theorem fderiv_eta_line {φ : ℝ × Plane → ℝ} {r q η : ℝ}
    (hφ : DifferentiableAt ℝ φ (r, (q, η))) :
    fderiv ℝ φ (r, (q, η)) eH = deriv (fun t => φ (r, (q, t))) η := by
  have hl : HasDerivAt (fun t : ℝ => ((r, (q, t)) : ℝ × Plane)) eH η :=
    (hasDerivAt_const η r).prodMk ((hasDerivAt_const η q).prodMk (hasDerivAt_id' η))
  exact ((hφ.hasFDerivAt).comp_hasDerivAt η hl).deriv.symm

/-- `∂_q` of a slice of a word derivative is the word with `e_q` prepended. -/
theorem partialQ_dW {g : ℝ × Plane → ℝ} (hg : ContDiffOn ℝ ∞ g UU) (L : List (ℝ × Plane))
    {s : ℝ} (hs : 0 < s) :
    Cyl.partialQ (fun z : Plane => dW L g (s, z)) = fun z => dW (eQ :: L) g (s, z) := by
  funext z
  obtain ⟨q, η⟩ := z
  rw [dW_cons, fderiv_q_line (dW_diffAt hg L (mem_UU hs _))]
  rfl

/-- `∂_η` of a slice of a word derivative is the word with `e_η` prepended. -/
theorem partialEta_dW {g : ℝ × Plane → ℝ} (hg : ContDiffOn ℝ ∞ g UU) (L : List (ℝ × Plane))
    {s : ℝ} (hs : 0 < s) :
    Cyl.partialEta (fun z : Plane => dW L g (s, z)) = fun z => dW (eH :: L) g (s, z) := by
  funext z
  obtain ⟨q, η⟩ := z
  rw [dW_cons, fderiv_eta_line (dW_diffAt hg L (mem_UU hs _))]
  rfl

/-- **The age jet as a word derivative.** -/
theorem ageJet_eq_dW {F : ℝ → Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) UU) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s)
    (z : Plane) (u : Fin j → Plane) :
    ageJet ℓ j F s z u =
      dW ((List.ofFn u).map (fun v => ((0 : ℝ), v)) ++ List.replicate ℓ (LL 0))
        (fun x : ℝ × Plane => F x.1 x.2) (s, z) := by
  have hKs : ContDiffOn ℝ ∞ (dW (List.replicate ℓ (LL 0)) (fun x : ℝ × Plane => F x.1 x.2)) UU :=
    dW_contDiffOn isOpen_UU hF _
  have hslice : (fun z' : Plane => iteratedDeriv ℓ (fun r => F r z') s) =
      fun z' => dW (List.replicate ℓ (LL 0)) (fun x : ℝ × Plane => F x.1 x.2) (s, z') := by
    funext z'
    exact (dW_rep_s hF ℓ z' s hs).symm
  have hH : ContDiffOn ℝ ∞
      (fun z' : Plane => dW (List.replicate ℓ (LL 0)) (fun x : ℝ × Plane => F x.1 x.2) (s, z'))
      univ :=
    hKs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun z' _ => mem_UU hs z')
  show iteratedFDeriv ℝ j (fun z' => iteratedDeriv ℓ (fun r => F r z') s) z u = _
  rw [hslice, ← dW_ofFn_eq isOpen_univ hH j u z (mem_univ _),
    ← dW_plane_word hKs (List.ofFn u) s hs z, dW_append]

/-- **Translation invariance of word derivatives** on `U`. -/
theorem dW_translate {g : ℝ × Plane → ℝ} {a : ℝ × Plane} (_ha : ∀ x ∈ UU, x + a ∈ UU)
    (hg : ∀ x ∈ UU, g (x + a) = g x) :
    ∀ L : List (ℝ × Plane), ∀ x ∈ UU, dW L g (x + a) = dW L g x := by
  intro L
  induction L with
  | nil => exact hg
  | cons v L ih =>
    intro x hx
    rw [dW_cons, dW_cons]
    have h1 : (fun y => dW L g (y + a)) =ᶠ[𝓝 x] dW L g :=
      Filter.eventually_of_mem (isOpen_UU.mem_nhds hx) (fun y hy => ih y hy)
    have h2 : fderiv ℝ (fun y => dW L g (y + a)) x = fderiv ℝ (dW L g) (x + a) :=
      fderiv_comp_add_right a
    rw [← h2, h1.fderiv_eq]

/-- **Congruence of word derivatives** on `U`. -/
theorem dW_congr {f g : ℝ × Plane → ℝ} (hfg : ∀ x ∈ UU, f x = g x) :
    ∀ L : List (ℝ × Plane), ∀ x ∈ UU, dW L f x = dW L g x := by
  intro L
  induction L with
  | nil => exact hfg
  | cons v L ih =>
    intro x hx
    rw [dW_cons, dW_cons]
    have h1 : dW L f =ᶠ[𝓝 x] dW L g :=
      Filter.eventually_of_mem (isOpen_UU.mem_nhds hx) (fun y hy => ih y hy)
    rw [h1.fderiv_eq]

/-- **Additivity of word derivatives** on `U`. -/
theorem dW_add {f g : ℝ × Plane → ℝ} (hf : ContDiffOn ℝ ∞ f UU) (hg : ContDiffOn ℝ ∞ g UU) :
    ∀ L : List (ℝ × Plane), ∀ x ∈ UU, dW L (fun y => f y + g y) x = dW L f x + dW L g x := by
  intro L
  induction L with
  | nil => intro x _; rfl
  | cons v L ih =>
    intro x hx
    rw [dW_cons, dW_cons, dW_cons]
    have h1 : dW L (fun y => f y + g y) =ᶠ[𝓝 x] fun y => dW L f y + dW L g y :=
      Filter.eventually_of_mem (isOpen_UU.mem_nhds hx) (fun y hy => ih y hy)
    have hd : HasFDerivAt (fun y => dW L f y + dW L g y)
        (fderiv ℝ (dW L f) x + fderiv ℝ (dW L g) x) x :=
      (dW_diffAt hf L hx).hasFDerivAt.add (dW_diffAt hg L hx).hasFDerivAt
    rw [h1.fderiv_eq, hd.fderiv]
    rfl

/-- **Subtractivity of word derivatives** on `U`. -/
theorem dW_sub {f g : ℝ × Plane → ℝ} (hf : ContDiffOn ℝ ∞ f UU) (hg : ContDiffOn ℝ ∞ g UU) :
    ∀ L : List (ℝ × Plane), ∀ x ∈ UU, dW L (fun y => f y - g y) x = dW L f x - dW L g x := by
  intro L
  induction L with
  | nil => intro x _; rfl
  | cons v L ih =>
    intro x hx
    rw [dW_cons, dW_cons, dW_cons]
    have h1 : dW L (fun y => f y - g y) =ᶠ[𝓝 x] fun y => dW L f y - dW L g y :=
      Filter.eventually_of_mem (isOpen_UU.mem_nhds hx) (fun y hy => ih y hy)
    have hd : HasFDerivAt (fun y => dW L f y - dW L g y)
        (fderiv ℝ (dW L f) x - fderiv ℝ (dW L g) x) x :=
      (dW_diffAt hf L hx).hasFDerivAt.sub (dW_diffAt hg L hx).hasFDerivAt
    rw [h1.fderiv_eq, hd.fderiv]
    rfl

/-- A linear functional on `ℝ × ℝ²` in the coordinate directions. -/
theorem clm_decomp (T : ℝ × Plane →L[ℝ] ℝ) (v : ℝ × Plane) :
    T v = v.1 * T (LL 0) + v.2.1 * T eQ + v.2.2 * T eH := by
  have hv : v = v.1 • LL 0 + v.2.1 • eQ + v.2.2 • eH := by
    obtain ⟨a, b, d⟩ := v
    simp [LL, eQ, eH]
  conv_lhs => rw [hv]
  rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- One step of `dW_zero_mean`: the derivative in a direction `v` of a smooth function on `U`,
`c`-periodic in `q`, with zero `q`-means, again has zero `q`-means. -/
theorem fderiv_zero_mean {c : ℝ} (hc : 0 < c) {g : ℝ × Plane → ℝ} (hg : ContDiffOn ℝ ∞ g UU)
    (hper : ∀ x ∈ UU, g (x + ((0 : ℝ), (c, (0 : ℝ)))) = g x)
    (hm0 : ∀ r : ℝ, 0 < r → ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), g (r, (q, η)) = 0)
    (v : ℝ × Plane) :
    ∀ r : ℝ, 0 < r → ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), fderiv ℝ g (r, (q, η)) v = 0 := by
  intro r hr η
  have hfc : ContinuousOn (fderiv ℝ g) UU := hg.continuousOn_fderiv_of_isOpen isOpen_UU (by simp)
  have hcont : ∀ w : ℝ × Plane, Continuous (fun q : ℝ => fderiv ℝ g (r, (q, η)) w) := by
    intro w
    have h1 : Continuous (fun q : ℝ => fderiv ℝ g (r, (q, η))) := by
      apply hfc.comp_continuous (by fun_prop) (fun q => mem_UU hr _)
    exact h1.clm_apply continuous_const
  have hint : ∀ w : ℝ × Plane, Integrable (fun q : ℝ => fderiv ℝ g (r, (q, η)) w)
      (volume.restrict (Ioc (-c / 2) (c / 2))) := fun w => (hcont w).integrableOn_Ioc
  have hdiff : ∀ q : ℝ, DifferentiableAt ℝ g (r, (q, η)) := fun q =>
    (hg.contDiffAt (isOpen_UU.mem_nhds (mem_UU hr _))).differentiableAt (by simp)
  -- the `s`-part
  have hS : ∫ q in Ioc (-c / 2) (c / 2), fderiv ℝ g (r, (q, η)) (LL 0) = 0 := by
    have e1 : ∀ q : ℝ, fderiv ℝ g (r, (q, η)) (LL 0) = deriv (fun t => g (t, (q, η))) r :=
      fun q => fderiv_fst_line3 (hdiff q)
    simp_rw [e1]
    have hD := hmeanDerivS c hc (fun t z => g (t, z)) hg r hr η
    have hz : (fun t => hmean c ((fun t z => g (t, z)) t) η) =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      show c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), g (t, (q, η)) = 0
      rw [hm0 t ht η, smul_zero]
    rw [hz.deriv_eq, deriv_const] at hD
    have h2 : c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), deriv (fun t => g (t, (q, η))) r = 0 := hD.symm
    rw [smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (inv_ne_zero hc.ne')
    · exact h
  -- the `q`-part
  have hQ : ∫ q in Ioc (-c / 2) (c / 2), fderiv ℝ g (r, (q, η)) eQ = 0 := by
    have hle : -c / 2 ≤ c / 2 := by linarith
    rw [← intervalIntegral.integral_of_le hle]
    have hderiv : ∀ q ∈ uIcc (-c / 2) (c / 2),
        HasDerivAt (fun t => g (r, (t, η))) (fderiv ℝ g (r, (q, η)) eQ) q := by
      intro q _
      rw [fderiv_q_line (hdiff q)]
      have hd : DifferentiableAt ℝ (fun t => g (r, (t, η))) q :=
        (hdiff q).comp q ((differentiableAt_const r).prodMk
          (differentiableAt_id.prodMk (differentiableAt_const η)))
      exact hd.hasDerivAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hcont eQ).intervalIntegrable _ _)]
    have hp := hper (r, (-c / 2, η)) (mem_UU hr _)
    have e : ((r, (-c / 2, η)) : ℝ × Plane) + ((0 : ℝ), (c, (0 : ℝ))) = (r, (c / 2, η)) := by
      ext <;> simp <;> ring
    rw [e] at hp
    rw [hp, sub_self]
  -- the `η`-part
  have hE : ∫ q in Ioc (-c / 2) (c / 2), fderiv ℝ g (r, (q, η)) eH = 0 := by
    have e1 : ∀ q : ℝ, fderiv ℝ g (r, (q, η)) eH =
        Cyl.partialEta (fun z : Plane => g (r, z)) (q, η) := fun q => fderiv_eta_line (hdiff q)
    simp_rw [e1]
    have hF : ContDiff ℝ 1 (fun z : Plane => g (r, z)) := by
      have h := hg.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun z => mem_UU hr z)
      exact_mod_cast contDiff_infty.1 h 1
    have hD := (sliceIntegralCalculus c hc).1 (fun z : Plane => g (r, z)) hF η
    have hz : (fun η' => ∫ q in Ioc (-c / 2) (c / 2), g (r, (q, η'))) = fun _ => (0 : ℝ) := by
      funext η'
      exact hm0 r hr η'
    rw [hz] at hD
    exact (hD.unique (hasDerivAt_const η (0 : ℝ)))
  -- assemble
  have e2 : ∀ q : ℝ, fderiv ℝ g (r, (q, η)) v =
      v.1 * fderiv ℝ g (r, (q, η)) (LL 0) + v.2.1 * fderiv ℝ g (r, (q, η)) eQ +
        v.2.2 * fderiv ℝ g (r, (q, η)) eH := fun q => clm_decomp _ v
  simp_rw [e2]
  have i1 : Integrable (fun q : ℝ => v.1 * fderiv ℝ g (r, (q, η)) (LL 0))
      (volume.restrict (Ioc (-c / 2) (c / 2))) := (hint _).const_mul _
  have i2 : Integrable (fun q : ℝ => v.2.1 * fderiv ℝ g (r, (q, η)) eQ)
      (volume.restrict (Ioc (-c / 2) (c / 2))) := (hint _).const_mul _
  have i3 : Integrable (fun q : ℝ => v.2.2 * fderiv ℝ g (r, (q, η)) eH)
      (volume.restrict (Ioc (-c / 2) (c / 2))) := (hint _).const_mul _
  have i12 : Integrable (fun q : ℝ => v.1 * fderiv ℝ g (r, (q, η)) (LL 0) +
      v.2.1 * fderiv ℝ g (r, (q, η)) eQ) (volume.restrict (Ioc (-c / 2) (c / 2))) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, hS, hQ, hE]
  ring

/-- **Zero `q`-means of all word derivatives.** -/
theorem dW_zero_mean {c : ℝ} (hc : 0 < c) {f : ℝ × Plane → ℝ} (hf : ContDiffOn ℝ ∞ f UU)
    (hper : ∀ x ∈ UU, f (x + ((0 : ℝ), (c, (0 : ℝ)))) = f x)
    (hm0 : ∀ r : ℝ, 0 < r → ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2), f (r, (q, η)) = 0) :
    ∀ L : List (ℝ × Plane), ∀ r : ℝ, 0 < r → ∀ η : ℝ,
      ∫ q in Ioc (-c / 2) (c / 2), dW L f (r, (q, η)) = 0 := by
  have ha : ∀ x ∈ UU, x + ((0 : ℝ), (c, (0 : ℝ))) ∈ UU := by
    intro x hx
    refine ⟨?_, mem_univ _⟩
    simpa using hx.1
  intro L
  induction L with
  | nil => exact hm0
  | cons v L ih =>
    intro r hr η
    exact fderiv_zero_mean hc (dW_contDiffOn isOpen_UU hf L) (dW_translate ha hper L) ih v r hr η

/-- **The vorticity is the Laplacian of the stream** on `U`. -/
theorem curl_eq_dW {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) UU) {r : ℝ} (hr : 0 < r)
    (z : Plane) :
    Cyl.curl (tr.v r) z = dW [eQ, eQ] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, z) +
      dW [eH, eH] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, z) := by
  have h1 : (fun w : Plane => tr.v r w 1) =
      fun w => dW [eQ] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, w) := by
    funext w
    obtain ⟨q, η⟩ := w
    have hs := tr.isTrain.stream r hr.le (q, η)
    have e : tr.v r (q, η) 1 = GaussianVortex.partialX (tr.ψ r) (q, η) := by rw [hs]; rfl
    rw [e, dW_cons, fderiv_q_line (dW_diffAt hΨ [] (mem_UU hr _))]
    rfl
  have h0 : (fun w : Plane => tr.v r w 0) =
      fun w => -dW [eH] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, w) := by
    funext w
    obtain ⟨q, η⟩ := w
    have hs := tr.isTrain.stream r hr.le (q, η)
    have e : tr.v r (q, η) 0 = -GaussianVortex.partialY (tr.ψ r) (q, η) := by rw [hs]; rfl
    rw [e, dW_cons, fderiv_eta_line (dW_diffAt hΨ [] (mem_UU hr _))]
    rfl
  have hq := partialQ_dW hΨ [eQ] hr
  have hη := partialEta_dW hΨ [eH] hr
  have hneg : Cyl.partialEta (fun w : Plane => -dW [eH] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, w)) z =
      -Cyl.partialEta (fun w : Plane => dW [eH] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, w)) z := by
    show deriv (fun t => -dW [eH] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, (z.1, t))) z.2 =
      -deriv (fun t => dW [eH] (fun x : ℝ × Plane => tr.ψ x.1 x.2) (r, (z.1, t))) z.2
    exact deriv.neg
  unfold Cyl.curl
  rw [h1, h0, hneg, hq, hη]
  ring

/-- **The calculus leaf `FluctJetCalc`.** -/
theorem fluctJetCalc : FluctJetCalc := by
  intro ν c hν hc tr htr ℓ j s hs u
  -- the three smooth functions on `U`
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) UU :=
    trainStreamSmooth ν c hν hc tr htr
  have hΨb : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => hmean c (tr.ψ x.1) x.2.2) UU := by
    have h := hmeanContDiff c hc tr.ψ hΨ
    exact h.comp (contDiffOn_fst.prodMk (contDiffOn_snd.snd))
      (fun x hx => ⟨hx.1, mem_univ _⟩)
  have hG : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) UU := hΨ.sub hΨb
  set L : List (ℝ × Plane) :=
    (List.ofFn u).map (fun v => ((0 : ℝ), v)) ++ List.replicate ℓ (LL 0) with hL
  have hW : ∀ z : Plane, ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z u =
      dW L (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) (s, z) :=
    fun z => ageJet_eq_dW (F := fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) hG ℓ j hs z u
  have hW1 : ∀ z : Plane, ageJet ℓ (j + 1) (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z
      (Fin.cons ((1 : ℝ), (0 : ℝ)) u) =
      dW (eQ :: L) (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) (s, z) := by
    intro z
    rw [ageJet_eq_dW (F := fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) hG ℓ (j + 1) hs z,
      List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, List.map_cons, List.cons_append]
    rfl
  -- translation invariance of `G` and `Ψb`
  have haC : ∀ x ∈ UU, x + ((0 : ℝ), (c, (0 : ℝ))) ∈ UU := by
    intro x hx
    refine ⟨?_, mem_univ _⟩
    simpa using hx.1
  have hGper : ∀ x ∈ UU, (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2)
      (x + ((0 : ℝ), (c, (0 : ℝ)))) =
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) x := by
    intro x hx
    obtain ⟨r, q, η⟩ := x
    have hp := Cons.C03.stream_periodic_of_isTrain tr.isTrain (le_of_lt hx.1) (q, η)
    simp only [Prod.mk_add_mk, add_zero]
    rw [hp]
  have hGmean : ∀ r : ℝ, 0 < r → ∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2),
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) (r, (q, η)) = 0 := by
    intro r hr η
    have hcont : Continuous (fun q : ℝ => tr.ψ r (q, η)) :=
      (tr.isTrain.stream_differentiable r hr.le).continuous.comp
        (continuous_id.prodMk continuous_const)
    have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
      rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      ring
    show ∫ q in Ioc (-c / 2) (c / 2), (tr.ψ r (q, η) - hmean c (tr.ψ r) η) = 0
    rw [integral_sub hcont.integrableOn_Ioc (integrable_const _), setIntegral_const, hvol,
      smul_eq_mul]
    unfold hmean
    rw [smul_eq_mul]
    field_simp
    ring
  have hΨbT : ∀ (a : ℝ), ∀ x ∈ UU, (fun x : ℝ × Plane => hmean c (tr.ψ x.1) x.2.2)
      (x + ((0 : ℝ), (a, (0 : ℝ)))) = (fun x : ℝ × Plane => hmean c (tr.ψ x.1) x.2.2) x := by
    intro a x _
    obtain ⟨r, q, η⟩ := x
    simp only [Prod.mk_add_mk, add_zero]
  have haA : ∀ (a : ℝ), ∀ x ∈ UU, x + ((0 : ℝ), (a, (0 : ℝ))) ∈ UU := by
    intro a x hx
    refine ⟨?_, mem_univ _⟩
    simpa using hx.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `C²`
    simp only [hW]
    have h := (dW_contDiffOn isOpen_UU hG L).comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun z => mem_UU hs z)
    exact_mod_cast contDiff_infty.1 h 2
  · -- periodicity
    intro z
    simp only [hW]
    have e : ((s, (z.1 + c, z.2)) : ℝ × Plane) = (s, z) + ((0 : ℝ), (c, (0 : ℝ))) := by
      ext <;> simp
    rw [e]
    exact dW_translate haC hGper L (s, z) (mem_UU hs z)
  · -- zero means
    intro η
    simp only [hW]
    exact dW_zero_mean hc hG hGper hGmean L s hs η
  · -- `∂_q`
    intro z
    simp only [hW, hW1]
    rw [partialQ_dW hG L hs]
  · -- the Laplacian
    -- the vorticity as a smooth function on `U`
    set Ψ : ℝ × Plane → ℝ := fun x => tr.ψ x.1 x.2 with hΨdef
    set Ψb : ℝ × Plane → ℝ := fun x => hmean c (tr.ψ x.1) x.2.2 with hΨbdef
    have hΩ' : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => dW [eQ, eQ] Ψ x + dW [eH, eH] Ψ x) UU :=
      (dW_contDiffOn isOpen_UU hΨ _).add (dW_contDiffOn isOpen_UU hΨ _)
    have hΩeq : ∀ x ∈ UU, (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) x =
        (fun x : ℝ × Plane => dW [eQ, eQ] Ψ x + dW [eH, eH] Ψ x) x := by
      intro x hx
      exact curl_eq_dW tr hΨ hx.1 x.2
    have hΩ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) UU :=
      hΩ'.congr hΩeq
    have hω : ∀ z : Plane, ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z u =
        dW (eQ :: eQ :: L) Ψ (s, z) + dW (eH :: eH :: L) Ψ (s, z) := by
      intro z
      rw [ageJet_eq_dW (F := fun r w => Cyl.curl (tr.v r) w) hΩ ℓ j hs z u]
      rw [dW_congr hΩeq L (s, z) (mem_UU hs z)]
      rw [dW_add (dW_contDiffOn isOpen_UU hΨ _) (dW_contDiffOn isOpen_UU hΨ _) L (s, z)
        (mem_UU hs z)]
      rw [← dW_append, ← dW_append]
      rw [dW_perm isOpen_UU hΨ (List.perm_append_comm (l₁ := L) (l₂ := [eQ, eQ])) (s, z)
        (mem_UU hs z)]
      rw [dW_perm isOpen_UU hΨ (List.perm_append_comm (l₁ := L) (l₂ := [eH, eH])) (s, z)
        (mem_UU hs z)]
      rfl
    refine ⟨fun η => -(dW (eQ :: eQ :: L) Ψb (s, (0, η)) + dW (eH :: eH :: L) Ψb (s, (0, η))),
      fun z => ?_⟩
    simp only [hW]
    have hlap : Train.lapS (fun z' : Plane =>
        dW L (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) (s, z')) z =
        dW (eQ :: eQ :: L) (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) (s, z) +
        dW (eH :: eH :: L) (fun x : ℝ × Plane => tr.ψ x.1 x.2 - hmean c (tr.ψ x.1) x.2.2) (s, z) := by
      unfold Train.lapS
      rw [partialQ_dW hG L hs, partialQ_dW hG (eQ :: L) hs, partialEta_dW hG L hs,
        partialEta_dW hG (eH :: L) hs]
    rw [hlap, hω z]
    rw [dW_sub hΨ hΨb (eQ :: eQ :: L) (s, z) (mem_UU hs z),
      dW_sub hΨ hΨb (eH :: eH :: L) (s, z) (mem_UU hs z)]
    have hx : ((s, z) : ℝ × Plane) = (s, ((0 : ℝ), z.2)) + ((0 : ℝ), (z.1, (0 : ℝ))) := by
      ext <;> simp
    have hT1 := dW_translate (haA z.1) (hΨbT z.1) (eQ :: eQ :: L) (s, ((0 : ℝ), z.2))
      (mem_UU hs _)
    have hT2 := dW_translate (haA z.1) (hΨbT z.1) (eH :: eH :: L) (s, ((0 : ℝ), z.2))
      (mem_UU hs _)
    rw [← hx] at hT1 hT2
    rw [hT1, hT2]
    ring

/-- **`FluctTransverseTailFixed` from the vorticity tail and the existing fluctuation bound.** -/
theorem fluctTransverseTailFixed_of_vort (hV : VortJetTailFixed) (hA : TrainFluctAgeJetFixed) :
    FluctTransverseTailFixed :=
  fluctTransverseTailFixed_of hV hA fluctJetCalc

end UnforcedLeray.Short.IIb.WeightedTrainFluctAux.FluctTail
