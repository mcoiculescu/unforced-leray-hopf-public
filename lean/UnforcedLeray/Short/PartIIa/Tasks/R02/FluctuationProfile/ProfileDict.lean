import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `PartII-a:R02/2` (`ProfileDict`): the profile partials of `trainProfile F`

Source of record: `the November 2 reference manuscript`, lines 439-446 (route step
(ii)). Target: `UnforcedLeray.Short.PartIIa.ProfileDict` (`Sub/R02_2.lean`).

For `H` smooth on the open set `{s > 0}` and `y` with `0 < y.2.2`:

* `∂_η^a H y` is the `a`-th derivative in `η` of the η-line through `y` (`profileDict_iter_eta`);
* `∂_q^b H y` is the `b`-th derivative in `q` of the q-line through `y` (`profileDict_iter_q`);
* `∂_s^k H y` is the `k`-th derivative in the age of the age-line through `y`
  (`profileDict_iter_age`).

Each is proved by induction: the outer partial is the derivative of the line through the point
(`profileDict_deriv_line_*`), and the inductive formula holds on that line. The main theorem
composes the three dictionaries, using `trainProfile F (q, (e, r)) = F r (q, e)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190

/-! ### Derivatives along the coordinate lines -/

/-- `∂_η K z` is the derivative of the η-line through `z`. -/
theorem profileDict_deriv_line_eta {K : ProfilePoint → ℝ} {z : ProfilePoint}
    (hK : DifferentiableAt ℝ K z) :
    partialEta K z = deriv (fun e : ℝ => K (z.1, (e, z.2.2))) z.2.1 := by
  have hline : HasDerivAt (fun e : ℝ => ((z.1, (e, z.2.2)) : ProfilePoint)) eηDir z.2.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  exact (hK.hasFDerivAt.comp_hasDerivAt z.2.1 hline).deriv.symm

/-- `∂_q K z` is the derivative of the q-line through `z`. -/
theorem profileDict_deriv_line_q {K : ProfilePoint → ℝ} {z : ProfilePoint}
    (hK : DifferentiableAt ℝ K z) :
    partialQ K z = deriv (fun q : ℝ => K (q, (z.2.1, z.2.2))) z.1 := by
  have hline : HasDerivAt (fun q : ℝ => ((q, (z.2.1, z.2.2)) : ProfilePoint)) eqDir z.1 :=
    (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  exact (hK.hasFDerivAt.comp_hasDerivAt z.1 hline).deriv.symm

/-- `∂_s K z` is the derivative of the age-line through `z`. -/
theorem profileDict_deriv_line_age {K : ProfilePoint → ℝ} {z : ProfilePoint}
    (hK : DifferentiableAt ℝ K z) :
    partialAge K z = deriv (fun r : ℝ => K (z.1, (z.2.1, r))) z.2.2 := by
  have hline : HasDerivAt (fun r : ℝ => ((z.1, (z.2.1, r)) : ProfilePoint)) esDir z.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hK.hasFDerivAt.comp_hasDerivAt z.2.2 hline).deriv.symm

/-- A function that is `C^∞` on `{s > 0}` is differentiable at each point with `s > 0`. -/
theorem profileDict_diffAt {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) {z : ProfilePoint} (hz : 0 < z.2.2) :
    DifferentiableAt ℝ G z := by
  have hz' : z ∈ {y : ProfilePoint | 0 < y.2.2} := hz
  exact (hG.contDiffAt (isOpen_late.mem_nhds hz')).differentiableAt (by simp)

/-- Iterated age derivatives of a function that is `C^∞` on `{s > 0}` stay so. -/
theorem profileDict_contDiffOn_partialAge_iter {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (k : ℕ) :
    ContDiffOn ℝ ∞ (partialAge^[k] G) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_iterate partialAge (fun _ h => contDiffOn_fderiv_apply h esDir) hG k

/-! ### The one-variable dictionaries -/

/-- The η-dictionary: `∂_η^a H y` is the `a`-th η-derivative of the η-line through `y`. -/
theorem profileDict_iter_eta : ∀ (a : ℕ) (H : ProfilePoint → ℝ),
    ContDiffOn ℝ ∞ H {y : ProfilePoint | 0 < y.2.2} → ∀ y : ProfilePoint, 0 < y.2.2 →
      (partialEta^[a] H) y = iteratedDeriv a (fun e : ℝ => H (y.1, (e, y.2.2))) y.2.1 := by
  intro a
  induction a with
  | zero =>
    intro H _ y _
    simp
  | succ a ih =>
    intro H hH y hy
    have hK : ContDiffOn ℝ ∞ (partialEta^[a] H) {y : ProfilePoint | 0 < y.2.2} :=
      contDiffOn_partialEta_iter hH a
    rw [Function.iterate_succ_apply', profileDict_deriv_line_eta (profileDict_diffAt hK hy),
      iteratedDeriv_succ]
    congr 1
    funext e
    exact ih H hH (y.1, (e, y.2.2)) hy

/-- The q-dictionary: `∂_q^b H y` is the `b`-th q-derivative of the q-line through `y`. -/
theorem profileDict_iter_q : ∀ (b : ℕ) (H : ProfilePoint → ℝ),
    ContDiffOn ℝ ∞ H {y : ProfilePoint | 0 < y.2.2} → ∀ y : ProfilePoint, 0 < y.2.2 →
      (partialQ^[b] H) y = iteratedDeriv b (fun q : ℝ => H (q, (y.2.1, y.2.2))) y.1 := by
  intro b
  induction b with
  | zero =>
    intro H _ y _
    simp
  | succ b ih =>
    intro H hH y hy
    have hK : ContDiffOn ℝ ∞ (partialQ^[b] H) {y : ProfilePoint | 0 < y.2.2} :=
      contDiffOn_partialQ_iter hH b
    rw [Function.iterate_succ_apply', profileDict_deriv_line_q (profileDict_diffAt hK hy),
      iteratedDeriv_succ]
    congr 1
    funext q
    exact ih H hH (q, (y.2.1, y.2.2)) hy

/-- The age-dictionary: `∂_s^k H y` is the `k`-th age derivative of the age-line through `y`. -/
theorem profileDict_iter_age : ∀ (k : ℕ) (H : ProfilePoint → ℝ),
    ContDiffOn ℝ ∞ H {y : ProfilePoint | 0 < y.2.2} → ∀ y : ProfilePoint, 0 < y.2.2 →
      (partialAge^[k] H) y = iteratedDeriv k (fun r : ℝ => H (y.1, (y.2.1, r))) y.2.2 := by
  intro k
  induction k with
  | zero =>
    intro H _ y _
    simp
  | succ k ih =>
    intro H hH y hy
    have hK : ContDiffOn ℝ ∞ (partialAge^[k] H) {y : ProfilePoint | 0 < y.2.2} :=
      profileDict_contDiffOn_partialAge_iter hH k
    rw [Function.iterate_succ_apply', profileDict_deriv_line_age (profileDict_diffAt hK hy),
      iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [lt_mem_nhds hy] with r hr
    exact ih H hH (y.1, (y.2.1, r)) hr

/-! ### The dictionary for `trainProfile` -/

/-- **`ProfileDict`** (source lines 439-446, route step (ii)): the profile partials of
`trainProfile F` are nested slice derivatives of `F`. -/
theorem profileDict : UnforcedLeray.Short.PartIIa.ProfileDict := by
  unfold ProfileDict
  intro F hF a b k x hx
  have hH1 : ContDiffOn ℝ ∞ (partialAge^[k] (trainProfile F)) {y : ProfilePoint | 0 < y.2.2} :=
    profileDict_contDiffOn_partialAge_iter hF k
  have hH2 : ContDiffOn ℝ ∞ (partialQ^[b] (partialAge^[k] (trainProfile F)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialQ_iter hH1 b
  rw [profileDict_iter_eta a _ hH2 x hx]
  refine congrArg (fun g : ℝ → ℝ => iteratedDeriv a g x.2.1) (funext fun e : ℝ => ?_)
  have hz : (0 : ℝ) < (x.1, (e, x.2.2)).2.2 := hx
  rw [profileDict_iter_q b _ hH1 (x.1, (e, x.2.2)) hz]
  refine congrArg (fun g : ℝ → ℝ => iteratedDeriv b g x.1) (funext fun q : ℝ => ?_)
  exact profileDict_iter_age k (trainProfile F) hF (q, (e, x.2.2)) hx

end UnforcedLeray.Short.PartIIa
