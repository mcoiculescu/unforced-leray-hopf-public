import UnforcedLeray.Lib.HeatR3.ConvOp

/-!
# The heat semigroup as a bounded operator on `L^p(μ)` (INF04 T3, `heatLp`)


decision D17 of `scoping/README.md` §3 (`heatLp` is a frozen interface).

For `1 ≤ p ≤ ∞` (`[Fact (1 ≤ p)]`) and `θ > 0`, `heatLp ι hι θ` is the class of
`heatConv ι θ u` (`ConvOp.lean`); for `θ ≤ 0` it is the identity (the manuscript's `e^{0Δ} = I`;
negative times are a convention, as in the compiled `Heat.heatOperator`).

Main results:
* `heatLp`, `heatLp_of_pos`, `heatLp_of_nonpos`, `heatLp_zero`;
* `heatLp_rep`: `heatLp ι hι θ u =ᵐ heatConv ι θ u` for `θ > 0`;
* `norm_heatLp_le`, `norm_heatLp_apply_le`: contraction (tex 7416–7425, B0419);
* `heatLp_add`: the semigroup law `e^{(s+t)Δ} = e^{sΔ}e^{tΔ}` for `s, t ≥ 0` (B0418).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsAddRightInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

/-- The heat operator at a fixed positive time, as a linear map on `Lp`. -/
def heatLpLin (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ) :
    Lp E p μ →ₗ[ℝ] Lp E p μ where
  toFun u := (memLp_heatConv ι hι.measurable hθ hp1.out (Lp.memLp u)).toLp _
  map_add' u v := by
    have h1 : heatConv ι θ (⇑(u + v)) =ᵐ[μ] heatConv ι θ (⇑u + ⇑v) :=
      heatConv_congr_ae ι hι.measurable θ (Lp.coeFn_add u v)
    have h2 := heatConv_add_ae ι hι.measurable hθ hp1.out (Lp.memLp u) (Lp.memLp v)
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (h1.trans h2)
  map_smul' c u := by
    have h1 : heatConv ι θ (⇑(c • u)) =ᵐ[μ] heatConv ι θ (c • ⇑u) :=
      heatConv_congr_ae ι hι.measurable θ (Lp.coeFn_smul c u)
    rw [heatConv_smul] at h1
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ h1

theorem heatLpLin_apply (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ)
    (u : Lp E p μ) : heatLpLin ι hι hθ u =
      (memLp_heatConv ι hι.measurable hθ hp1.out (Lp.memLp u)).toLp _ := rfl

theorem heatLpLin_rep (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ)
    (u : Lp E p μ) : (heatLpLin ι hι hθ u : G → E) =ᵐ[μ] heatConv ι θ u := by
  rw [heatLpLin_apply]
  exact MemLp.coeFn_toLp _

theorem norm_heatLpLin_le (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ)
    (u : Lp E p μ) : ‖heatLpLin ι hι hθ u‖ ≤ 1 * ‖u‖ := by
  rw [one_mul, heatLpLin_apply, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_heatConv_le ι hι.measurable hθ (Lp.aestronglyMeasurable u) hp1.out)

/-- The heat operator at a fixed positive time, as a bounded operator of norm `≤ 1`. -/
def heatLpPos (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ) :
    Lp E p μ →L[ℝ] Lp E p μ :=
  LinearMap.mkContinuous (heatLpLin (E := E) (μ := μ) (p := p) ι hι hθ) 1
    (norm_heatLpLin_le (E := E) (μ := μ) (p := p) ι hι hθ)

open Classical in
/-- **INF04 T3 `heatLp`** (D17 interface). The heat semigroup `e^{θΔ}` on `Lp E p μ`,
`1 ≤ p ≤ ∞`: the class of `heatConv ι θ u` for `θ > 0`, the identity for `θ ≤ 0`. -/
def heatLp (ι : Euc d →+ G) (hι : Continuous ι) (θ : ℝ) : Lp E p μ →L[ℝ] Lp E p μ :=
  if hθ : 0 < θ then heatLpPos ι hι hθ else ContinuousLinearMap.id ℝ _

theorem heatLp_of_pos (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ) :
    (heatLp ι hι θ : Lp E p μ →L[ℝ] Lp E p μ) = heatLpPos ι hι hθ := by
  simp only [heatLp, dif_pos hθ]

theorem heatLp_of_nonpos (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : θ ≤ 0) :
    (heatLp ι hι θ : Lp E p μ →L[ℝ] Lp E p μ) = ContinuousLinearMap.id ℝ _ := by
  simp only [heatLp, dif_neg (not_lt.mpr hθ)]

@[simp] theorem heatLp_zero (ι : Euc d →+ G) (hι : Continuous ι) :
    (heatLp ι hι 0 : Lp E p μ →L[ℝ] Lp E p μ) = ContinuousLinearMap.id ℝ _ :=
  heatLp_of_nonpos ι hι le_rfl

/-- **INF04 T3 `heatLp_rep`.** For `θ > 0`, `heatLp ι hι θ u` is represented by the literal heat
integral `heatConv ι θ u`. -/
theorem heatLp_rep (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ)
    (u : Lp E p μ) : (heatLp ι hι θ u : G → E) =ᵐ[μ] heatConv ι θ u := by
  rw [heatLp_of_pos ι hι hθ, heatLpPos, LinearMap.mkContinuous_apply]
  exact heatLpLin_rep ι hι hθ u

/-- **INF04 T3 `norm_heatLp_le`.** `‖e^{θΔ}‖_{L^p → L^p} ≤ 1` (tex 7416–7425, B0419). -/
theorem norm_heatLp_le (ι : Euc d →+ G) (hι : Continuous ι) (θ : ℝ) :
    ‖(heatLp ι hι θ : Lp E p μ →L[ℝ] Lp E p μ)‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · rw [heatLp_of_pos ι hι hθ, heatLpPos]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · rw [heatLp_of_nonpos ι hι (not_lt.mp hθ)]
    exact ContinuousLinearMap.norm_id_le

theorem norm_heatLp_apply_le (ι : Euc d →+ G) (hι : Continuous ι) (θ : ℝ) (u : Lp E p μ) :
    ‖heatLp ι hι θ u‖ ≤ ‖u‖ :=
  ((heatLp ι hι θ).le_opNorm u).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_heatLp_le ι hι θ) (norm_nonneg u))

/-- **INF04 T3 `heatLp_add`.** The semigroup law on `L^p`, `1 ≤ p ≤ ∞`, for `s, t ≥ 0`
(tex 7416–7425, B0418). -/
theorem heatLp_add (ι : Euc d →+ G) (hι : Continuous ι) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatLp ι hι (s + t) : Lp E p μ →L[ℝ] Lp E p μ) =
      (heatLp ι hι s).comp (heatLp ι hι t) := by
  rcases hs.eq_or_lt with rfl | hs'
  · rw [zero_add, heatLp_zero, ContinuousLinearMap.id_comp]
  rcases ht.eq_or_lt with rfl | ht'
  · rw [add_zero, heatLp_zero, ContinuousLinearMap.comp_id]
  ext1 u
  refine Lp.ext ?_
  rw [ContinuousLinearMap.comp_apply]
  have h1 := heatLp_rep ι hι (add_pos hs' ht') u
  have h2 := heatConv_add_time ι hι.measurable hs' ht' hp1.out (Lp.memLp u)
  have h3 : heatConv ι s (heatConv ι t u) =ᵐ[μ] heatConv ι s (heatLp ι hι t u : G → E) :=
    heatConv_congr_ae ι hι.measurable s (heatLp_rep ι hι ht' u).symm
  have h4 := heatLp_rep ι hι hs' (heatLp ι hι t u)
  exact h1.trans (h2.trans (h3.trans h4.symm))

theorem heatLp_comm_time (ι : Euc d →+ G) (hι : Continuous ι) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    (heatLp ι hι s : Lp E p μ →L[ℝ] Lp E p μ).comp (heatLp ι hι t) =
      (heatLp ι hι t).comp (heatLp ι hι s) := by
  rw [← heatLp_add ι hι hs ht, ← heatLp_add ι hι ht hs, add_comm]

end UnforcedLeray.Heat
