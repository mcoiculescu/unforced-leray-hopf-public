import UnforcedLeray.Lib.LerayLp
import UnforcedLeray.Lib.HeatR3
import UnforcedLeray.Analysis.Heat.Solenoidal

/-!
# Commutations of the `L^p` Leray projection: transfer from `L²`, translations, heat (INF01 T16)

Blueprint: INF01 target T16 (`lerayLp_translate`, `lerayLp_heat`) of

`scoping/README.md` §5 (decision D5: `𝔓 := Id + ∂∂(N ∗ ·)`, identified with the compiled
`Leray.projection` at `p = 2`).

Manuscript: unit B0414 (`paper/main.tex` lines 7336–7344: `P_σ` "commutes with spatial dilations
as well as with the heat semigroup and phase translations"), unit B0429 (lines 3616–3618: "`P`
… commutes with spatial heat, isotropic dilation, and phase translation"), unit B0433
(lines 7550–7576: commutation with the heat flow and with mollifiers).

* `lerayLp_comm_of_projection_comm`: the transfer principle. If a continuous map `A` of `L^p`
  and a map `B` of `L²` agree on common representatives, and `B` commutes with the orthogonal
  projection `Leray.projection`, then `A` commutes with `lerayLp p`. Proof: on the dense set
  `L² ∩ L^p` (`dense_memLp_two_vec`) both projections agree (`lerayLp_ae_eq_projection`), and
  both sides are continuous.
* `lerayLp_translate` (**T16**): `𝔓 τ_y = τ_y 𝔓` for the translation `τ_y u = u(· - y)`
  (`Heat.translateLp` of `Lib/HeatR3`); the `L²` input is the library's
  `Heat.projection_translation`.
* `lerayLp_heat` (**T16**): `𝔓 e^{θΔ} = e^{θΔ} 𝔓` on `L^p(R³;R³)` for every heat time `θ`
  (`heatLp` of `Lib/HeatR3`; identity for `θ ≤ 0`), from `Heat.heatLp_comm` (the heat operator is
  a Bochner average of translations).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Transfer principle (INF01 T16).** Let `A` be a continuous self-map of `L^p(R³;R³)`,
`1 < p < ∞`, and `B` a self-map of `L²(R³;R³)` such that `A u` and `B v` are a.e. equal whenever
`u` and `v` are, and `B` commutes with the orthogonal Leray projection. Then `𝔓_p A = A 𝔓_p`. -/
theorem lerayLp_comm_of_projection_comm (hp1 : 1 < p) (hp : p ≠ ⊤)
    {A : Lp Space p (volume : Measure Space) → Lp Space p (volume : Measure Space)}
    (hA : Continuous A) {B : L2Space → L2Space}
    (hAB : ∀ (u : Lp Space p (volume : Measure Space)) (v : L2Space),
      (u : SpatialField) =ᵐ[volume] (v : SpatialField) →
        (A u : SpatialField) =ᵐ[volume] (B v : SpatialField))
    (hB : ∀ v, Leray.projection (B v) = B (Leray.projection v))
    (F : Lp Space p (volume : Measure Space)) :
    lerayLp p hp1 hp (A F) = A (lerayLp p hp1 hp F) := by
  have key : EqOn (fun F => lerayLp p hp1 hp (A F)) (fun F => A (lerayLp p hp1 hp F))
      {u : Lp Space p (volume : Measure Space) | MemLp u 2 volume} := by
    intro u hu
    have hu : MemLp (u : SpatialField) 2 volume := hu
    have h1 := hAB u (hu.toLp u) hu.coeFn_toLp.symm
    have hAu2 : MemLp (A u : SpatialField) 2 volume := (Lp.memLp (B (hu.toLp u))).ae_eq h1.symm
    have h2 := lerayLp_ae_eq_projection hp1 hp (A u) hAu2
    have e : hAu2.toLp (A u : SpatialField) = B (hu.toLp u) := Lp.ext (hAu2.coeFn_toLp.trans h1)
    rw [e, hB] at h2
    have h3 := lerayLp_ae_eq_projection hp1 hp u hu
    have h4 := hAB (lerayLp p hp1 hp u) (Leray.projection (hu.toLp u)) h3
    exact Lp.ext (h2.trans h4.symm)
  exact congrFun (Continuous.ext_on (dense_memLp_two_vec p hp)
    ((lerayLp p hp1 hp).continuous.comp hA) (hA.comp (lerayLp p hp1 hp).continuous) key) F

/-- Operator form of the transfer principle for a bounded operator `A`. -/
theorem lerayLp_comp_eq_of_projection_comm (hp1 : 1 < p) (hp : p ≠ ⊤)
    (A : Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space))
    {B : L2Space → L2Space}
    (hAB : ∀ (u : Lp Space p (volume : Measure Space)) (v : L2Space),
      (u : SpatialField) =ᵐ[volume] (v : SpatialField) →
        (A u : SpatialField) =ᵐ[volume] (B v : SpatialField))
    (hB : ∀ v, Leray.projection (B v) = B (Leray.projection v)) :
    (lerayLp p hp1 hp).comp A = A.comp (lerayLp p hp1 hp) := by
  ext1 F
  exact lerayLp_comm_of_projection_comm hp1 hp A.continuous hAB hB F

/-! ### Translations -/

/-- The spatial translation `τ_y u = u(· - y)` on `L^p(R³;E)` (`Heat.translateLp` with `ι = id`,
`Lib/HeatR3/Continuity.lean`). -/
abbrev spaceTranslateLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ≥0∞) (y : Space)
    (u : Lp E p (volume : Measure Space)) : Lp E p (volume : Measure Space) :=
  Heat.translateLp (AddMonoidHom.id Space) continuous_id y u

theorem coeFn_spaceTranslateLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (y : Space)
    (u : Lp E p (volume : Measure Space)) :
    (spaceTranslateLp p y u : Space → E) =ᵐ[volume] fun x => u (x - y) :=
  Heat.coeFn_translateLp (AddMonoidHom.id Space) continuous_id y u

theorem continuous_spaceTranslateLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (y : Space) :
    Continuous (spaceTranslateLp (E := E) p y) :=
  (Lp.isometry_compMeasurePreserving _).continuous

/-- Translation respects almost-everywhere equality. -/
theorem ae_eq_comp_sub {E : Type*} {f g : Space → E} (h : f =ᵐ[volume] g) (y : Space) :
    (fun x => f (x - y)) =ᵐ[volume] fun x => g (x - y) :=
  (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae_eq_comp h

/-- **INF01 T16 (translations).** For `1 < p < ∞` and every `y ∈ R³`, the `L^p` Leray projection
commutes with the translation `u ↦ u(· - y)` (B0414, `paper/main.tex` lines 7336–7344). -/
theorem lerayLp_translate (hp1 : 1 < p) (hp : p ≠ ⊤) (y : Space)
    (F : Lp Space p (volume : Measure Space)) :
    lerayLp p hp1 hp (spaceTranslateLp p y F) = spaceTranslateLp p y (lerayLp p hp1 hp F) := by
  refine lerayLp_comm_of_projection_comm hp1 hp (continuous_spaceTranslateLp y)
    (B := Heat.translation y) (fun u v huv => ?_) (fun v => Heat.projection_translation y v) F
  exact (coeFn_spaceTranslateLp y u).trans
    ((ae_eq_comp_sub huv y).trans (Heat.translation_ae y v).symm)

/-! ### The heat semigroup -/

/-- **INF01 T16 (heat semigroup).** For `1 < p < ∞` and every heat time `θ`, the `L^p` Leray
projection commutes with `e^{θΔ}` on `L^p(R³;R³)` (`heatLp` of `Lib/HeatR3`, the class of the
Gaussian average for `θ > 0` and the identity for `θ ≤ 0`; B0414 (iv), `paper/main.tex`
lines 7343–7344; B0429, lines 3616–3618). -/
theorem lerayLp_heat (hp1 : 1 < p) (hp : p ≠ ⊤) (θ : ℝ) :
    (lerayLp p hp1 hp).comp (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ) =
      (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ).comp (lerayLp p hp1 hp) :=
  Heat.heatLp_comm (AddMonoidHom.id Space) continuous_id hp
    (fun y u => lerayLp_translate hp1 hp y u) θ

/-- Pointwise form of `lerayLp_heat`. -/
theorem lerayLp_heat_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (θ : ℝ)
    (F : Lp Space p (volume : Measure Space)) :
    lerayLp p hp1 hp (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ F) =
      Heat.heatLp (AddMonoidHom.id Space) continuous_id θ (lerayLp p hp1 hp F) := by
  have h := congrArg (fun T : Lp Space p (volume : Measure Space) →L[ℝ]
    Lp Space p (volume : Measure Space) => T F) (lerayLp_heat hp1 hp θ)
  simpa using h

end UnforcedLeray.RieszLp
