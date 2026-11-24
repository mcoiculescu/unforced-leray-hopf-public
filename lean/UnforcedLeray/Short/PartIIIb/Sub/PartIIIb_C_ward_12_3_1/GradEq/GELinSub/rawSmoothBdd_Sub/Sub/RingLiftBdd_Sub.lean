import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftDerivSource

/-!


Source `the November 2 reference manuscript`
lines 1217-1219, 1322-1325. `Short.PartIIa.RingBoundedDerivs` (StatementsRing.lean:217) places
`ν₀` inside `∀ k`; the source argument is stated order by order. `RingBoundedDerivsUnif` is the
`ρ = 2` form with one `ν₀` for all `k`. This file proves `RingLiftBdd` from it (the lift `U` is
unique by continuity, so it does not depend on `k`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

/-- `k`-uniform threshold form of the bounded-derivative fact (1217-1219, 1322-1325). -/
def RingBoundedDerivsUnif : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : B0184.ProfilePoint → ℝ,
    Short.PartIIa.IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R → ∀ k : ℕ,
      ∃ U : ℝ → Space → Space, (∀ τ, ContDiff ℝ ∞ (U τ)) ∧
        (∀ τ (y : Space), Axi.ϱ y ≠ 0 → U τ y = B0190.simProfile 1 (B0185.liftVelocity R ψ) τ y) ∧
        ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ k (U τ) y‖ ≤ C

theorem ringLiftBdd_of (h : RingBoundedDerivsUnif) : RingLiftBdd := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun ν hν ψ pr hpr R hR => ?_⟩
  obtain ⟨U0, hU0, hoff0, -⟩ := H ν hν ψ pr hpr R hR 0
  refine ⟨fun x => U0 x.1 x.2, fun τ => hU0 τ, fun x hx => hoff0 x.1 x.2 hx, fun k => ?_⟩
  obtain ⟨Uk, hUk, hoffk, C, hC⟩ := H ν hν ψ pr hpr R hR k
  refine ⟨C, fun τ y => ?_⟩
  have heq : Uk τ = U0 τ := by
    refine Continuous.ext_on (UnforcedLeray.Cons.C03.dense_compl_axis) (hUk τ).continuous
      (hU0 τ).continuous (fun z hz => ?_)
    have hz' : Axi.ϱ z ≠ 0 := varrho_ne_zero_iff.2 hz
    rw [hoffk τ z hz', hoff0 τ z hz']
  have := hC τ y
  rwa [heq] at this

/-- **Derivative bounds for the smooth similarity lift** (source lines 1217-1219, 1322-1325): below
a threshold `ν₀` (the threshold of the finite heat-expansion argument; no further smallness of `ν`
is used and none depends on the order `k`), every `C^∞` extension `U(τ)` across the axis of the
similarity lift of the `ρ = 2` exact train has, for each order `k`, a bound
`‖D^k U(τ)(y)‖ ≤ C` uniform in `τ` and `y` (`C = P_k` may depend on `ν`, `R`). The extension is
unique by continuity, so this is a statement about the lift `U_R`. -/
def RingLiftDerivBddOfSmooth : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : B0184.ProfilePoint → ℝ,
    Short.PartIIa.IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R →
      ∀ U : ℝ → Space → Space, (∀ τ, ContDiff ℝ ∞ (U τ)) →
        (∀ τ (y : Space), Axi.ϱ y ≠ 0 → U τ y = B0190.simProfile 1 (B0185.liftVelocity R ψ) τ y) →
        ∀ k : ℕ, ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ k (U τ) y‖ ≤ C

/-- `RingLiftDerivBddOfSmooth` from the off-axis derivative bound: the `C^∞` extension agrees
with the lift on the open dense set `{ϱ ≠ 0}`, so its derivatives there are those of the lift, and
the bound passes to the axis by continuity of `D^k U(τ)`. -/
theorem ringLiftDerivBddOfSmooth_of (h : RingLiftOffAxisDerivBdd) : RingLiftDerivBddOfSmooth := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun ν hν ψ pr hpr R hR U hU hoff k => ?_⟩
  obtain ⟨C, hC⟩ := H ν hν ψ pr hpr R hR k
  refine ⟨C, fun τ => ?_⟩
  have hopen : IsOpen {y : Space | Axi.ϱ y ≠ 0} :=
    isOpen_ne_fun Axi.continuous_ϱ continuous_const
  have hcl : IsClosed {y : Space | ‖iteratedFDeriv ℝ k (U τ) y‖ ≤ C} :=
    isClosed_le ((hU τ).continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm continuous_const
  have hdense : Dense {y : Space | Axi.ϱ y ≠ 0} := by
    refine (UnforcedLeray.Cons.C03.dense_compl_axis).mono ?_
    intro y hy
    exact varrho_ne_zero_iff.2 hy
  have hsub : {y : Space | Axi.ϱ y ≠ 0} ⊆ {y : Space | ‖iteratedFDeriv ℝ k (U τ) y‖ ≤ C} := by
    intro y hy
    have hev : U τ =ᶠ[𝓝 y]
        B0190.simProfile 1 (B0185.liftVelocity R ψ) τ :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) (fun z hz => hoff τ z hz)
    show ‖iteratedFDeriv ℝ k (U τ) y‖ ≤ C
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    exact hC τ y hy
  intro y
  have : y ∈ closure {y : Space | Axi.ϱ y ≠ 0} := hdense y
  exact (hcl.closure_subset_iff.2 hsub) this

/-- The `k`-uniform threshold form from axis smoothness (`ρ = 2`, `ν₀` independent of `k`,
lines 1305-1322) and the derivative bound for the smooth lift. -/
theorem ringBoundedDerivsUnif
    (hs : Short.PartIIa.RingAxisSmooth) (hb : RingLiftDerivBddOfSmooth) :
    RingBoundedDerivsUnif := by
  obtain ⟨ν₁, hν₁, H1⟩ := hs 2 (by norm_num)
  obtain ⟨ν₂, hν₂, H2⟩ := hb
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν ψ pr hpr R hR k => ?_⟩
  have hν1 : ν ∈ Ioo 0 ν₁ := ⟨hν.1, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have hν2 : ν ∈ Ioo 0 ν₂ := ⟨hν.1, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  obtain ⟨u, π, hu, -, hagree⟩ := H1 ν hν1 ψ pr hpr R hR
  set U : ℝ → Space → Space := fun τ y =>
    Real.exp (τ / 2) • u (Real.exp τ, Real.exp (τ / 2) • y) with hU
  have hsm : ∀ τ, ContDiff ℝ ∞ (U τ) := by
    intro τ
    have h1 : ContDiff ℝ ∞ (fun y : Space => (Real.exp τ, Real.exp (τ / 2) • y)) :=
      contDiff_const.prodMk (contDiff_const_smul _)
    have h2 : ContDiff ℝ ∞ (fun y : Space => u (Real.exp τ, Real.exp (τ / 2) • y)) := by
      rw [← contDiffOn_univ]
      exact hu.comp h1.contDiffOn (fun y _ => Real.exp_pos τ)
    exact (contDiff_const (c := Real.exp (τ / 2))).smul h2
  have hoff : ∀ τ (y : Space), Axi.ϱ y ≠ 0 →
      U τ y = B0190.simProfile 1 (B0185.liftVelocity R ψ) τ y := by
    intro τ y hy
    have hx : Real.exp (τ / 2) • y ∉ Axi.axis := by
      rw [← varrho_ne_zero_iff, Axi.ϱ_smul]
      exact mul_ne_zero (by simp [abs_of_pos (Real.exp_pos _)]) hy
    simp only [hU, B0190.simProfile]
    rw [(hagree _ (Real.exp_pos τ) _ hx).1, pow_one]
  obtain ⟨C, hC⟩ := H2 ν hν2 ψ pr hpr R hR U hsm hoff k
  exact ⟨U, hsm, hoff, C, hC⟩

end UnforcedLeray.Short.PartIIIb.Concrete
