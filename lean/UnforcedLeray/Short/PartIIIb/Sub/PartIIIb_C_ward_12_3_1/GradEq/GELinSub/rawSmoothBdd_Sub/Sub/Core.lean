import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RawIsRingLift
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2

/-!
# Source facts behind `rawJointSmooth` and `rawDerivBdd` (tasks `.../6/1/1`, `.../6/1/3`)

Source `the November 2 reference manuscript`
lines 1214, 1217-1219, 1305-1325.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray UnforcedLeray.Short.IIb

/-- **Source fact A** (1214, 1305-1322): the similarity lift `U_R` of an exact planar train at
`ρ = 2` (`c = ν⁻²`), `R ≥ 2`, agrees off the axis with a function `C^∞` jointly in `(τ, y)`. -/
def RingLiftSmoothReal : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : B0184.ProfilePoint → ℝ,
    Short.PartIIa.IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R →
      ∃ U : ℝ × Space → Space, ContDiff ℝ ∞ U ∧
        ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
          U x = B0190.simProfile 1 (B0185.liftVelocity R ψ) x.1 x.2

/-- **Source fact B** (1217-1219, 1322-1325): as A (slice smoothness), and moreover the spatial
derivatives `D^k U(τ)` of orders `k = 0, 1, 2` (`k : Fin 3`, the orders used downstream) are
bounded uniformly in `(τ, y)` (`R ≥ 2`; the bound `P_k` of the source may depend on `ν`). This is
`Short.PartIIa.RingBoundedDerivs` at `ρ = 2` and order `2`. -/
def RingLiftBdd : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioo 0 ν₀, ∀ ψ pr : B0184.ProfilePoint → ℝ,
    Short.PartIIa.IsExactPlanarTrain ν (ν ^ (-(2 : ℝ))) ψ pr → ∀ R : ℝ, 2 ≤ R →
      ∃ U : ℝ × Space → Space, (∀ τ, ContDiff ℝ ∞ (fun y => U (τ, y))) ∧
        (∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
          U x = B0190.simProfile 1 (B0185.liftVelocity R ψ) x.1 x.2) ∧
        ∀ k : Fin 3, ∃ C : ℝ, ∀ (τ : ℝ) (y : Space),
          ‖iteratedFDeriv ℝ (k : ℕ) (fun y => U (τ, y)) y‖ ≤ C

theorem varrho_ne_zero_iff {y : Space} : Axi.ϱ y ≠ 0 ↔ y ∉ Axi.axis := by
  unfold Axi.ϱ Axi.axis
  simp only [Set.mem_setOf_eq, ne_eq, Real.sqrt_eq_zero', not_le, not_and]
  constructor
  · intro h h0 h1
    rw [h0, h1] at h; norm_num at h
  · intro h
    by_contra hle
    push Not at hle
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact h h0 h1

theorem R_ge_two {p : Params} {d dm dp : ℝ} (h : BgRegime p d dm dp) (hν : p.ν ≤ dm) : 2 ≤ p.R := by
  have hν0 := p.ν_pos
  have : p.R = Real.exp (d / p.ν) := by
    unfold Params.R
    rw [h.eps_eq, ← Real.exp_neg]; congr 1; ring
  rw [this]
  have h1 : 1 ≤ d / p.ν := by
    rw [le_div_iff₀ hν0]; linarith [h.dm_le]
  have := Real.add_one_le_exp (d / p.ν)
  linarith

/-- If `U` is continuous in `y` and equals the lift off the axis, `raw τ = U (τ, ·)`. -/
theorem raw_eq_of {p : Params} (hb : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (U : ℝ × Space → Space) (hU : ∀ τ, Continuous (fun y => U (τ, y)))
    (hoff : ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
      U x = B0190.simProfile 1 (B0185.liftVelocity p.R (trainStream p)) x.1 x.2) (τ : ℝ) :
    p.raw τ = fun y => U (τ, y) := by
  have hoffraw : ∀ z : Space, z ∉ Axi.axis → p.raw τ z = U (τ, z) := fun z hz => by
    rw [hoff (τ, z) (varrho_ne_zero_iff.2 hz)]
    exact rawIsRingLift_proof p hb τ z (varrho_ne_zero_iff.2 hz)
  funext y
  by_cases hy : y ∈ Axi.axis
  · have hne := axisCompl_neBot y
    have hev : (fun z => U (τ, z)) =ᶠ[𝓝[Axi.axisᶜ] y]
        Axi.Nv p.R (Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ := by
      refine eventually_nhdsWithin_of_forall fun z hz => ?_
      have hz' : z ∉ Axi.axis := hz
      show U (τ, z) = _
      rw [← hoffraw z hz', Cons.C03.Concrete.Params.raw_eq_off_axis p τ z hz']
      rfl
    have ht : Tendsto (fun z => U (τ, z)) (𝓝[Axi.axisᶜ] y) (𝓝 (U (τ, y))) :=
      ((hU τ).tendsto y).mono_left nhdsWithin_le_nhds
    have := (ht.congr' hev).limUnder_eq
    show Cons.C03.Concrete.axisExt _ y = _
    unfold Cons.C03.Concrete.axisExt
    rw [if_pos hy]
    exact this
  · exact hoffraw y hy

theorem rawJointSmooth_of (h : RingLiftSmoothReal) : RawJointSmooth := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨min (ν₀ / 2) dm, lt_min (by linarith) hdm, fun p d hreg hν => ?_⟩
  have hb := hreg.train_buc
  have hν1 : p.ν ≤ ν₀ / 2 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ dm := hν.trans (min_le_right _ _)
  obtain ⟨U, hU, hoff⟩ := H p.ν ⟨p.ν_pos, by linarith⟩ _ _
    (isExactPlanarTrain_params_rpow p hb hreg.c_eq) p.R (R_ge_two hreg hν2)
  have hcont : ∀ τ, Continuous (fun y => U (τ, y)) := fun τ =>
    hU.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  have : (fun x : ℝ × Space => p.raw x.1 x.2) = U := by
    funext x
    exact congrFun (raw_eq_of hb U hcont hoff x.1) x.2
  rw [this]; exact hU

theorem rawDerivBdd_of (h : RingLiftBdd) : RawDerivBdd := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨min (ν₀ / 2) dm, lt_min (by linarith) hdm, fun p d hreg hν k => ?_⟩
  have hb := hreg.train_buc
  have hν1 : p.ν ≤ ν₀ / 2 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ dm := hν.trans (min_le_right _ _)
  obtain ⟨U, hU, hoff, hB⟩ := H p.ν ⟨p.ν_pos, by linarith⟩ _ _
    (isExactPlanarTrain_params_rpow p hb hreg.c_eq) p.R (R_ge_two hreg hν2)
  have hcont : ∀ τ, Continuous (fun y => U (τ, y)) := fun τ => (hU τ).continuous
  obtain ⟨C, hC⟩ := hB k
  refine ⟨C, fun τ y => ?_⟩
  rw [raw_eq_of hb U hcont hoff τ]
  exact hC τ y

end UnforcedLeray.Short.PartIIIb.Concrete
