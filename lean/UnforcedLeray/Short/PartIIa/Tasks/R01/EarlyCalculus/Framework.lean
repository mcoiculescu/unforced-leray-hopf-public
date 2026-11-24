import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIa.Tasks.R02.Commutators
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileCommute

/-!
# Helper for `PartII-a:R01`, target `earlyCalculus`: calculus framework on the age domain

Helpers for `Tasks/R01/EarlyCalculus.lean`: the directional derivatives `Dir v f x = fderiv f x v`
on the age domain `AgeSet = {s > 0}`, their iterates, linearity, commutation (symmetry of the second
derivative), and the closure fields of `EarlyBdd` that need no product rule.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.EarlyCalc

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-- The age domain `{s > 0}`, where the profiles are `C^∞`. -/
abbrev AgeSet : Set ProfilePoint := {x : ProfilePoint | 0 < x.2.2}

theorem isOpen_AgeSet : IsOpen AgeSet :=
  isOpen_lt continuous_const (continuous_snd.comp continuous_snd)

/-- The directional derivative `x ↦ (Df)(x) v`. -/
def Dir (v : ProfilePoint) (f : ProfilePoint → ℝ) : ProfilePoint → ℝ :=
  fun x => fderiv ℝ f x v

theorem smooth_diffAt {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (isOpen_AgeSet.mem_nhds hx)).differentiableAt (by simp)

theorem smooth_Dir (v : ProfilePoint) {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet) :
    ContDiffOn ℝ ∞ (Dir v f) AgeSet := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) AgeSet := hf.fderiv_of_isOpen isOpen_AgeSet (by simp)
  exact h1.clm_apply contDiffOn_const

theorem smooth_iter (v : ProfilePoint) (n : ℕ) {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f AgeSet) : ContDiffOn ℝ ∞ ((Dir v)^[n] f) AgeSet := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact smooth_Dir v ih

theorem Dir_add (v : ProfilePoint) {f g : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    (hg : ContDiffOn ℝ ∞ g AgeSet) {x : ProfilePoint} (hx : x ∈ AgeSet) :
    Dir v (fun y => f y + g y) x = Dir v f x + Dir v g x := by
  simp only [Dir]
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add (smooth_diffAt hf hx)
    (smooth_diffAt hg hx)]
  rfl

theorem Dir_const_mul (v : ProfilePoint) (c : ℝ) {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f AgeSet) {x : ProfilePoint} (hx : x ∈ AgeSet) :
    Dir v (fun y => c * f y) x = c * Dir v f x := by
  simp only [Dir]
  rw [fderiv_const_mul (smooth_diffAt hf hx) c]
  simp

theorem Dir_mul (v : ProfilePoint) {f g : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    (hg : ContDiffOn ℝ ∞ g AgeSet) {x : ProfilePoint} (hx : x ∈ AgeSet) :
    Dir v (fun y => f y * g y) x = Dir v f x * g x + f x * Dir v g x := by
  simp only [Dir]
  rw [show (fun y => f y * g y) = f * g from rfl, fderiv_mul (smooth_diffAt hf hx)
    (smooth_diffAt hg hx)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- Equal functions on the age domain have equal directional derivatives there. -/
theorem Dir_congr (v : ProfilePoint) {f g : ProfilePoint → ℝ} (h : EqOn f g AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) : Dir v f x = Dir v g x := by
  have hev : f =ᶠ[𝓝 x] g := h.eventuallyEq_of_mem (isOpen_AgeSet.mem_nhds hx)
  simp only [Dir]
  rw [hev.fderiv_eq]

theorem iter_congr (v : ProfilePoint) (n : ℕ) {f g : ProfilePoint → ℝ} (h : EqOn f g AgeSet) :
    EqOn ((Dir v)^[n] f) ((Dir v)^[n] g) AgeSet := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Dir_congr v ih hx

theorem iter_add (v : ProfilePoint) (n : ℕ) {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f AgeSet) (hg : ContDiffOn ℝ ∞ g AgeSet) :
    EqOn ((Dir v)^[n] (fun y => f y + g y))
      (fun y => (Dir v)^[n] f y + (Dir v)^[n] g y) AgeSet := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    simp only [Function.iterate_succ_apply']
    rw [Dir_congr v ih hx, Dir_add v (smooth_iter v n hf) (smooth_iter v n hg) hx]

theorem iter_const (v : ProfilePoint) (n : ℕ) (c : ℝ) {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f AgeSet) :
    EqOn ((Dir v)^[n] (fun y => c * f y)) (fun y => c * (Dir v)^[n] f y) AgeSet := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    simp only [Function.iterate_succ_apply']
    rw [Dir_congr v ih hx, Dir_const_mul v c (smooth_iter v n hf) hx]

/-- Symmetry of second directional derivatives on the age domain. -/
theorem Dir_comm (v w : ProfilePoint) {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) : Dir v (Dir w G) x = Dir w (Dir v G) x := by
  have h2 : ContDiffAt ℝ 2 G x :=
    (hG.contDiffAt (isOpen_AgeSet.mem_nhds hx)).of_le (by simp)
  exact UnforcedLeray.Short.PartIIa.FluctuationProfile.profile_fderiv_comm_at h2 w v

/-- Iterated directional derivatives commute with a fixed one on the age domain. -/
theorem iter_comm (v w : ProfilePoint) (n : ℕ) {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G AgeSet) :
    EqOn ((Dir v)^[n] (Dir w G)) (Dir w ((Dir v)^[n] G)) AgeSet := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Dir_congr v ih hx, Dir_comm v w (smooth_iter v n hG) hx]
    simp only [Function.iterate_succ_apply']

/-! ### Jets and the closure of `EarlyBdd` under linear operations -/

/-- The jet `∂_s^ℓ ∂_η^a ∂_q^b f` written with `Dir`. -/
def jet (ℓ a b : ℕ) (f : ProfilePoint → ℝ) : ProfilePoint → ℝ :=
  (Dir esDir)^[ℓ] ((Dir eηDir)^[a] ((Dir eqDir)^[b] f))

theorem jet_eq (ℓ a b : ℕ) (f : ProfilePoint → ℝ) :
    partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f)) = jet ℓ a b f := rfl

theorem jet_add (ℓ a b : ℕ) {f g : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet)
    (hg : ContDiffOn ℝ ∞ g AgeSet) :
    EqOn (jet ℓ a b (fun y => f y + g y))
      (fun y => jet ℓ a b f y + jet ℓ a b g y) AgeSet := by
  have h1 := iter_add eqDir b hf hg
  have h2 := iter_congr eηDir a h1
  have h3 := iter_add eηDir a (smooth_iter eqDir b hf) (smooth_iter eqDir b hg)
  have h4 := iter_congr esDir ℓ (h2.trans h3)
  have h5 := iter_add esDir ℓ (smooth_iter eηDir a (smooth_iter eqDir b hf))
    (smooth_iter eηDir a (smooth_iter eqDir b hg))
  exact h4.trans h5

theorem jet_const (ℓ a b : ℕ) (c : ℝ) {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f AgeSet) :
    EqOn (jet ℓ a b (fun y => c * f y)) (fun y => c * jet ℓ a b f y) AgeSet := by
  have h1 := iter_const eqDir b c hf
  have h2 := iter_congr eηDir a h1
  have h3 := iter_const eηDir a c (smooth_iter eqDir b hf)
  have h4 := iter_congr esDir ℓ (h2.trans h3)
  have h5 := iter_const esDir ℓ c (smooth_iter eηDir a (smooth_iter eqDir b hf))
  exact h4.trans h5

/-- Transport of the zero-age bounds along a pointwise identity of families. -/
theorem earlyBdd_congr {ρ : ℝ} {F G : ProfFam}
    (hFG : ∀ ν ψ p x, F ν ψ p x = G ν ψ p x) (h : EarlyBdd ρ F) : EarlyBdd ρ G := by
  have e : F = G := by
    funext ν ψ p x
    exact hFG ν ψ p x
  rw [← e]
  exact h

theorem polyConst_add_le {C₁ C₂ : ℝ} {d₁ d₂ : ℕ} {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    polyConst C₁ d₁ ν c + polyConst C₂ d₂ ν c ≤
      polyConst (max C₁ 0 + max C₂ 0) (max d₁ d₂) ν c := by
  have hC₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  have h1 : polyConst C₁ d₁ ν c ≤ polyConst (max C₁ 0) (max d₁ d₂) ν c :=
    polyConst_mono hν hc (le_max_left C₁ 0) hC₁ (le_max_left d₁ d₂)
  have h2 : polyConst C₂ d₂ ν c ≤ polyConst (max C₂ 0) (max d₁ d₂) ν c :=
    polyConst_mono hν hc (le_max_left C₂ 0) hC₂ (le_max_right d₁ d₂)
  have e : polyConst (max C₁ 0) (max d₁ d₂) ν c + polyConst (max C₂ 0) (max d₁ d₂) ν c =
      polyConst (max C₁ 0 + max C₂ 0) (max d₁ d₂) ν c := by
    unfold polyConst
    ring
  linarith

end UnforcedLeray.Short.PartIIa.EarlyCalc
