import UnforcedLeray.Short.PartIIa.Sub.R02_2
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileCommute

/-!
# Part II-a, task `PartII-a:R02/2`: the profile partials commute (`ProfileIterComm`)

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`; route step (i): `∂_s ∂_η = ∂_η ∂_s` on `C^2` functions).

Target: `UnforcedLeray.Short.PartIIa.profileIterComm : ProfileIterComm` (`Sub/R02_2.lean`).

Write `∂_η, ∂_q, ∂_s` for `partialEta, partialQ, partialAge` and `S = {y | 0 < y.2.2}`.

* `profDir_comm`: pointwise symmetry of two directional derivatives of a `C^∞` profile on `S`
  (from `FluctuationProfile.profile_fderiv_comm_at`, `ProfileCommute.lean`).
* `iterCommutes X Y`: `X (Y H) = Y (X H)` on `S` for smooth `H`. Composition
  (`iterCommutes_comp`), iterates on the right (`iterCommutes_iter`) and iterates on the left
  (`iterCommutes_iter_left`) are proved by induction.
* `iterLifts Y`: an operator respects `EqOn` on the open set `S`, so it may be applied to two
  functions that agree on `S`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190

namespace IterComm

/-- The open set `{s > 0}` on which the profile functions are smooth. -/
abbrev lateSet : Set ProfilePoint := {y : ProfilePoint | 0 < y.2.2}

/-- Directional derivative along a fixed profile direction `d`. Definitionally,
`partialEta = profDir eηDir`, `partialQ = profDir eqDir`, `partialAge = profDir esDir`. -/
def profDir (d : ProfilePoint) (F : ProfilePoint → ℝ) : ProfilePoint → ℝ :=
  fun y => fderiv ℝ F y d

/-- An operator on profile functions respects equality on the late set. -/
def iterLifts (Y : (ProfilePoint → ℝ) → ProfilePoint → ℝ) : Prop :=
  ∀ {F F' : ProfilePoint → ℝ}, EqOn F F' lateSet → EqOn (Y F) (Y F') lateSet

/-- `X` commutes with `Y` on smooth functions, on the late set. -/
def iterCommutes (X Y : (ProfilePoint → ℝ) → ProfilePoint → ℝ) : Prop :=
  ∀ H : ProfilePoint → ℝ, ContDiffOn ℝ ∞ H lateSet → EqOn (X (Y H)) (Y (X H)) lateSet

/-- An operator maps functions that are `C^∞` on the late set to such functions. -/
def iterPresSmooth (Z : (ProfilePoint → ℝ) → ProfilePoint → ℝ) : Prop :=
  ∀ H : ProfilePoint → ℝ, ContDiffOn ℝ ∞ H lateSet → ContDiffOn ℝ ∞ (Z H) lateSet

/-! ### Smoothness of the iterates -/

theorem contDiffOn_partialAge_iter {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G lateSet) (k : ℕ) :
    ContDiffOn ℝ ∞ (partialAge^[k] G) lateSet :=
  contDiffOn_iterate partialAge (fun _ h => contDiffOn_fderiv_apply h esDir) hG k

theorem iterPresSmooth_eta (n : ℕ) : iterPresSmooth (partialEta^[n]) :=
  fun _ hH => contDiffOn_partialEta_iter hH n

theorem iterPresSmooth_q (n : ℕ) : iterPresSmooth (partialQ^[n]) :=
  fun _ hH => contDiffOn_partialQ_iter hH n

theorem iterPresSmooth_age (n : ℕ) : iterPresSmooth (partialAge^[n]) :=
  fun _ hH => contDiffOn_partialAge_iter hH n

/-! ### Respecting equality on the late set -/

theorem profDir_eqOn {F F' : ProfilePoint → ℝ} (h : EqOn F F' lateSet) (d : ProfilePoint) :
    EqOn (profDir d F) (profDir d F') lateSet := by
  intro y hy
  have hev : F =ᶠ[𝓝 y] F' :=
    Filter.eventually_of_mem (isOpen_late.mem_nhds hy) (fun z hz => h hz)
  show fderiv ℝ F y d = fderiv ℝ F' y d
  rw [hev.fderiv_eq]

theorem iterLifts_eta : iterLifts partialEta := fun h => profDir_eqOn h eηDir

theorem iterLifts_q : iterLifts partialQ := fun h => profDir_eqOn h eqDir

theorem iterLifts_age : iterLifts partialAge := fun h => profDir_eqOn h esDir

theorem iterLifts_iter {D : (ProfilePoint → ℝ) → ProfilePoint → ℝ} (hD : iterLifts D)
    (n : ℕ) : iterLifts (D^[n]) := by
  intro F F' h
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hD ih

/-! ### Pointwise symmetry of the profile partials -/

theorem profDir_comm {H : ProfilePoint → ℝ} (hH : ContDiffOn ℝ ∞ H lateSet)
    {y : ProfilePoint} (hy : y ∈ lateSet) (d e : ProfilePoint) :
    fderiv ℝ (profDir e H) y d = fderiv ℝ (profDir d H) y e := by
  have hC : ContDiffAt ℝ 2 H y :=
    (hH.contDiffAt (isOpen_late.mem_nhds hy)).of_le (by norm_num)
  exact UnforcedLeray.Short.PartIIa.FluctuationProfile.profile_fderiv_comm_at hC e d

theorem iterCommutes_age_eta : iterCommutes partialAge partialEta := by
  intro H hH y hy
  exact profDir_comm hH hy esDir eηDir

theorem iterCommutes_age_q : iterCommutes partialAge partialQ := by
  intro H hH y hy
  exact profDir_comm hH hy esDir eqDir

/-! ### Composition and iteration of commutation -/

theorem iterCommutes_comp {X Y Z : (ProfilePoint → ℝ) → ProfilePoint → ℝ}
    (hXY : iterCommutes X Y) (hXZ : iterCommutes X Z) (hZ : iterPresSmooth Z)
    (hY : iterLifts Y) : iterCommutes X (fun H => Y (Z H)) := by
  intro H hH y hy
  exact (hXY (Z H) (hZ H hH) hy).trans (hY (hXZ H hH) hy)

/-- Commutation with `Y` passes to the iterates of `Y`. -/
theorem iterCommutes_iter {X Y : (ProfilePoint → ℝ) → ProfilePoint → ℝ}
    (hXY : iterCommutes X Y) (hY : iterLifts Y) (hYs : ∀ n : ℕ, iterPresSmooth (Y^[n]))
    (n : ℕ) : iterCommutes X (Y^[n]) := by
  induction n with
  | zero =>
    intro H _ y _
    simp
  | succ n ih =>
    rw [Function.iterate_succ']
    exact iterCommutes_comp (X := X) (Y := Y) (Z := Y^[n]) hXY ih (hYs n) hY

/-- Commutation with `Y` passes to the iterates of `X` on the left. -/
theorem iterCommutes_iter_left {X Y : (ProfilePoint → ℝ) → ProfilePoint → ℝ}
    (hXY : iterCommutes X Y) (hX : iterLifts X) (hXs : ∀ n : ℕ, iterPresSmooth (X^[n]))
    (k : ℕ) : iterCommutes (X^[k]) Y := by
  induction k with
  | zero =>
    intro H _ y _
    simp
  | succ k ih =>
    intro H hH y hy
    have h1 := hX (ih H hH) hy
    have h2 := hXY (X^[k] H) (hXs k H hH) hy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact h1.trans h2

theorem iterCommutes_age_iter_eta (a : ℕ) : iterCommutes partialAge (partialEta^[a]) :=
  iterCommutes_iter iterCommutes_age_eta iterLifts_eta iterPresSmooth_eta a

theorem iterCommutes_age_iter_q (b : ℕ) : iterCommutes partialAge (partialQ^[b]) :=
  iterCommutes_iter iterCommutes_age_q iterLifts_q iterPresSmooth_q b

theorem iterCommutes_age_comp (a b : ℕ) :
    iterCommutes partialAge (fun H => partialEta^[a] (partialQ^[b] H)) :=
  iterCommutes_comp (iterCommutes_age_iter_eta a) (iterCommutes_age_iter_q b)
    (iterPresSmooth_q b) (iterLifts_iter iterLifts_eta a)

theorem iterCommutes_age_comp_iter (k a b : ℕ) :
    iterCommutes (partialAge^[k]) (fun H => partialEta^[a] (partialQ^[b] H)) :=
  iterCommutes_iter_left (iterCommutes_age_comp a b) iterLifts_age iterPresSmooth_age k

end IterComm

open IterComm in
/-- **Commutation of the profile partials** (`ProfileIterComm`; source lines 439-446):
for `G` smooth on `{s > 0}` and `x` with `s > 0`,
`∂_η^i ∂_s^k ∂_η^a ∂_q^b G = ∂_η^{i+a} ∂_q^b ∂_s^k G` at `x`. -/
theorem profileIterComm : ProfileIterComm := by
  intro G hG i a b k x hx
  have h2 : EqOn (partialAge^[k] (partialEta^[a] (partialQ^[b] G)))
      (partialEta^[a] (partialQ^[b] (partialAge^[k] G))) lateSet :=
    iterCommutes_age_comp_iter k a b G hG
  have h3 := iterLifts_iter iterLifts_eta i h2
  rw [Function.iterate_add_apply]
  exact h3 (show x ∈ lateSet from hx)

end UnforcedLeray.Short.PartIIa
