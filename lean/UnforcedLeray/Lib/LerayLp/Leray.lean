import UnforcedLeray.Lib.LerayLp.RieszLp

/-!
# The Leray projection on `L^p(R³; R³)`, `1 < p < ∞` (INF01 T14)

Blueprint: INF01 target T14 (`lerayLp`, `norm_lerayLp_le`, `lerayLp_two`,

§5, Level 2, and §4.2; decision D5 of `scoping/README.md` §3:
`𝔓 := Id + ∂∂(N ∗ ·)` on `L^p`, identified with the compiled `Leray.projection` at `p = 2`.

Manuscript: the Leray projection `𝔓 = I + R ⊗ R` (`paper/main.tex` lines 107–111, and
line 3051: "`𝔓 = I + R⊗R` is bounded on `W^{1,p}`"); unit B0414 (lines 7336–7344): `P_σ` is
bounded on `L^q(R³)` for every `1 < q < ∞` and is the orthogonal projection at `q = 2`;
unit B0430 (lines 3720–3732): the operators at different exponents agree on intersections.
Only real fields are treated here (the `ℂ³` version of B0414 is INF01 T17).

* `coordLp i p`, `embedLp k p`: the `i`-th component and `f ↦ f eₖ` on `L^p`;
* `lerayLp p hp1 hp`: `(𝔓F)ᵢ = Fᵢ + Σₖ R_iR_k Fₖ`, a bounded operator on `L^p(R³;R³)`;
* `norm_lerayLp_le`, `eLpNorm_lerayLp_le`: the bound `‖𝔓F‖_p ≤ C_p ‖F‖_p`, with `C_p`
  depending on `p` only;
* `lerayLp_two`: at `p = 2`, `lerayLp` is the compiled orthogonal projection
  `Leray.projection` (`LerayProjection/Basic.lean`);
* `lerayLp_consistent`: for `F ∈ L^p ∩ L^q` the two projections agree a.e.;
* `lerayLp_toLp_ae_eq_projection`, `lerayLp_ae_eq_projection`: on `L^p ∩ L²`, `lerayLp p`
  agrees a.e. with `Leray.projection`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

/-- `F ↦ Fᵢ` on `L^p(R³;R³)`. -/
def coordLp (i : Fin 3) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp ℝ p (volume : Measure Space) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).compLpL p volume

/-- `f ↦ f eₖ` from scalar to vector `L^p`. -/
def embedLp (k : Fin 3) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector k)).compLpL p volume

/-- **INF01 T14 (decision D5).** The Leray projection on `L^p(R³;R³)`, `1 < p < ∞`:
`(𝔓F)ᵢ = Fᵢ + Σₖ R_iR_k Fₖ`, with `R_iR_k = ∂ᵢ∂ₖ(-Δ)^{-1}` the Newton Hessian operators
(`paper/main.tex` lines 107–111, 3051, 7336–7344). -/
def lerayLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  ContinuousLinearMap.id ℝ _ +
    ∑ i : Fin 3, ∑ k : Fin 3, (embedLp i p).comp ((rieszPairLp i k p hp1 hp).comp (coordLp k p))

section Coord

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem coeFn_embedLp (k : Fin 3) (f : Lp ℝ p (volume : Measure Space)) :
    (embedLp k p f : SpatialField) =ᵐ[volume] fun x => f x • coordinateVector k := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector k)) f] with x hx
  rw [embedLp, hx]
  simp

theorem coeFn_coordLp (i : Fin 3) (F : Lp Space p (volume : Measure Space)) :
    (coordLp i p F : Space → ℝ) =ᵐ[volume] fun x => F x i := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ) F] with x hx
  rw [coordLp, hx]
  rfl

omit [Fact (1 ≤ p)] in
/-- The components of an `L^p` field are in `L^p`. -/
theorem memLp_component {F : SpatialField} (hF : MemLp F p volume) (i : Fin 3) :
    MemLp (fun x => F x i) p volume :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' hF

theorem coordLp_toLp {F : SpatialField} (hF : MemLp F p volume) (i : Fin 3) :
    coordLp i p (hF.toLp F) = (memLp_component p hF i).toLp (fun x => F x i) := by
  apply Lp.ext
  filter_upwards [coeFn_coordLp p i (hF.toLp F), hF.coeFn_toLp,
    (memLp_component p hF i).coeFn_toLp] with x h1 h2 h3
  rw [h1, h3, h2]

end Coord

/-- Pointwise formula: `𝔓F = F + Σᵢ (Σₖ R_iR_k Fₖ) eᵢ` a.e. -/
theorem coeFn_lerayLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) :
    (lerayLp p hp1 hp F : SpatialField) =ᵐ[volume] fun x =>
      F x + ∑ i : Fin 3, (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F) x) •
        coordinateVector i := by
  have e : lerayLp p hp1 hp F =
      F + ∑ i : Fin 3, embedLp i p (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F)) := by
    simp [lerayLp, map_sum]
  rw [e]
  have hi : ∀ᵐ x ∂volume, ∀ i : Fin 3,
      (embedLp i p (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F)) : SpatialField) x =
        (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F) x) • coordinateVector i := by
    refine ae_all_iff.2 fun i => ?_
    filter_upwards [coeFn_embedLp p i (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F)),
      Lp.coeFn_fun_finsetSum Finset.univ
        (fun k : Fin 3 => rieszPairLp i k p hp1 hp (coordLp k p F))] with x h1 h2
    rw [h1, h2]
  filter_upwards [Lp.coeFn_add F (∑ i : Fin 3,
      embedLp i p (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F))),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin 3 =>
      embedLp i p (∑ k : Fin 3, rieszPairLp i k p hp1 hp (coordLp k p F))), hi] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2]
  simp_rw [h3]

/-- **INF01 T14.** `‖𝔓F‖_p ≤ C_p ‖F‖_p` with `C_p = ‖lerayLp p‖` depending on `p` only
(unit B0414, `paper/main.tex` lines 7336–7344). -/
theorem norm_lerayLp_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ F : Lp Space p (volume : Measure Space), ‖lerayLp p hp1 hp F‖ ≤ C * ‖F‖ :=
  ⟨‖lerayLp p hp1 hp‖₊, fun F => (lerayLp p hp1 hp).le_opNorm F⟩

/-- **INF01 T14**, function form: `‖𝔓F‖_{L^p} ≤ ‖lerayLp p‖ ‖F‖_{L^p}`. -/
theorem eLpNorm_lerayLp_toLp_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    {F : SpatialField} (hF : MemLp F p volume) :
    eLpNorm (lerayLp p hp1 hp (hF.toLp F) : SpatialField) p volume ≤
      ‖lerayLp p hp1 hp‖₊ * eLpNorm F p volume := by
  have h : eLpNorm (lerayLp p hp1 hp (hF.toLp F) : SpatialField) p volume ≤
      ‖lerayLp p hp1 hp‖₊ * eLpNorm (hF.toLp F : SpatialField) p volume := by
    rw [← Lp.enorm_def, ← Lp.enorm_def, enorm_eq_nnnorm, enorm_eq_nnnorm]
    exact_mod_cast (lerayLp p hp1 hp).le_opNNNorm (hF.toLp F)
  rwa [eLpNorm_congr_ae hF.coeFn_toLp] at h

/-- **INF01 T14 (decision D5).** At `p = 2`, `lerayLp` is the compiled orthogonal Leray
projection `Leray.projection` (unit B0414 (ii), `paper/main.tex` lines 7340–7342). -/
theorem lerayLp_two :
    lerayLp 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = Leray.projection := by
  rw [← lerayNewtonL2_eq_projection]
  simp only [lerayLp, rieszPairLp_two]
  rfl

/-- **INF01 T14 (consistency across exponents).** For `F ∈ L^p ∩ L^q` the Leray projections at
`p` and at `q` agree a.e. (unit B0430, `paper/main.tex` lines 3720–3732). -/
theorem lerayLp_consistent {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp1 : 1 < p)
    (hp : p ≠ ⊤) (hq1 : 1 < q) (hq : q ≠ ⊤) {F : SpatialField} (hFp : MemLp F p volume)
    (hFq : MemLp F q volume) :
    (lerayLp p hp1 hp (hFp.toLp F) : SpatialField) =ᵐ[volume]
      lerayLp q hq1 hq (hFq.toLp F) := by
  have hc : ∀ᵐ x ∂volume, ∀ i k : Fin 3,
      rieszPairLp i k p hp1 hp (coordLp k p (hFp.toLp F)) x =
        rieszPairLp i k q hq1 hq (coordLp k q (hFq.toLp F)) x := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun k => ?_
    rw [coordLp_toLp p hFp k, coordLp_toLp q hFq k]
    exact rieszPairLp_consistent i k hp1 hp hq1 hq _ _
  filter_upwards [coeFn_lerayLp p hp1 hp (hFp.toLp F), coeFn_lerayLp q hq1 hq (hFq.toLp F),
    hFp.coeFn_toLp, hFq.coeFn_toLp, hc] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4]
  simp_rw [h5]

/-- On `L^p ∩ L²`, `lerayLp p` is the orthogonal Leray projection (function form). -/
theorem lerayLp_toLp_ae_eq_projection {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    {F : SpatialField} (hFp : MemLp F p volume) (hF2 : MemLp F 2 volume) :
    (lerayLp p hp1 hp (hFp.toLp F) : SpatialField) =ᵐ[volume]
      Leray.projection (toL2 F) := by
  have h := lerayLp_consistent hp1 hp ENNReal.one_lt_two ENNReal.ofNat_ne_top hFp hF2
  rw [lerayLp_two] at h
  have e : toL2 F = hF2.toLp F := by
    unfold toL2
    simp [hF2]
  rw [e]
  exact h

/-- On `L^p ∩ L²`, `lerayLp p` is the orthogonal Leray projection (`L^p`-element form). -/
theorem lerayLp_ae_eq_projection {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) (hF2 : MemLp F 2 volume) :
    (lerayLp p hp1 hp F : SpatialField) =ᵐ[volume] Leray.projection (hF2.toLp F) := by
  have h := lerayLp_toLp_ae_eq_projection hp1 hp (Lp.memLp F) hF2
  rw [Lp.toLp_coeFn] at h
  have e : toL2 (F : SpatialField) = hF2.toLp F := by
    unfold toL2
    simp [hF2]
  rwa [e] at h

end UnforcedLeray.RieszLp
