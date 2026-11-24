import UnforcedLeray.Lib.ParabolicB.Duality

/-!
# `∂_i∂_j (∂_t - Δ)^{-1}` on `L^q`, and eq:free-stress-11 at `ν = 1` (INF02 T8)


target T8; decision D4 of `scoping/README.md` §3 (the operator is the parabolic instance of the
CZ core, extended from `L² ∩ L^q` by `CZ.extendOfBound`). Manuscript: the lemma
eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit B0423) at `ν = 1`, all
second spatial derivatives (scoping note `INF01-CZ.md` §4.5).

* `continuous_integral_mul_Lp`: `G ↦ ∫ G h` is continuous on `L^p` for `h ∈ L^{p'}` (Hölder).
* `secondDerivOpLp hq i j : L^q →L[ℝ] L^q`, the extension of `secondDerivOp 1 i j` from
  `L² ∩ L^q` (`1 < q < ∞`).
* `integral_secondDerivOpLp_mul`: `∫ (T_q G) φ = ∫ G · backTest 1 i j φ` for every `G ∈ L^q` and
  every test `φ` (density of `L² ∩ L^q`, transposition on `L²`).
* `heat_maximal_regularity_one`: eq:free-stress-11 at `ν = 1` for the second spatial
  derivatives: if `u, F ∈ L^q` and `(∂_t - Δ)u = F` against tests, then every weak `∂_i∂_j u`
  exists in `L^q` with `‖∂_i∂_j u‖_q ≤ C ‖F‖_q`, `C = C(d, q)`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

theorem one_le_ofReal_of_one_lt {q : ℝ} (hq : 1 < q) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le

/-- **Hölder continuity of the pairing.** For `h ∈ L^{p'}`, `G ↦ ∫ G h` is (Lipschitz)
continuous on `L^p`. -/
theorem continuous_integral_mul_Lp {p p' : ℝ≥0∞} [Fact (1 ≤ p)] [ENNReal.HolderTriple p p' 1]
    {h : PS d → ℝ} (hh : MemLp h p' volume) :
    Continuous (fun G : Lp ℝ p (volume : Measure (PS d)) => ∫ X, G X * h X) := by
  refine (LipschitzWith.of_dist_le_mul (K := (eLpNorm h p' volume).toNNReal)
    fun G G' => ?_).continuous
  rw [Real.dist_eq, Lp.dist_def, ENNReal.coe_toNNReal_eq_toReal]
  have iG : Integrable (fun X => G X * h X) volume := (Lp.memLp G).integrable_mul hh
  have iG' : Integrable (fun X => G' X * h X) volume := (Lp.memLp G').integrable_mul hh
  have e : (∫ X, G X * h X) - ∫ X, G' X * h X = ∫ X, (⇑G - ⇑G') X * h X := by
    rw [← integral_sub iG iG']
    congr 1; funext X
    rw [Pi.sub_apply, sub_mul]
  rw [e]
  have h1 := UnforcedLeray.CZ.ofReal_abs_integral_mul_le (p := p) (q := p') (μ := volume)
    ((Lp.aestronglyMeasurable G).sub (Lp.aestronglyMeasurable G')) hh.1
  have hfin : eLpNorm (⇑G - ⇑G') p volume * eLpNorm h p' volume ≠ ⊤ :=
    ENNReal.mul_ne_top ((Lp.memLp G).sub (Lp.memLp G')).2.ne hh.2.ne
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
  rw [ENNReal.toReal_mul] at h2
  linarith

section LqOperator

variable {q : ℝ}

/-- **`∂_i∂_j (∂_t - Δ)^{-1}` on `L^q`**, `1 < q < ∞`: the extension of `secondDerivOp 1 i j`
from `L² ∩ L^q` (bounded there by `secondDerivOp_eLpNorm_le`, INF02 T7). -/
def secondDerivOpLp (hq : 1 < q) (i j : Fin d) [Fact (1 ≤ ENNReal.ofReal q)] :
    Lp ℝ (ENNReal.ofReal q) (volume : Measure (PS d)) →L[ℝ]
      Lp ℝ (ENNReal.ofReal q) (volume : Measure (PS d)) :=
  UnforcedLeray.CZ.extendOfBound (secondDerivOp one_pos i j) (ENNReal.ofReal q)
    (Classical.choose (secondDerivOp_eLpNorm_le (d := d) i j hq))
    (Classical.choose_spec (secondDerivOp_eLpNorm_le (d := d) i j hq))

/-- On `L² ∩ L^q`, `secondDerivOpLp` agrees a.e. with `secondDerivOp 1`. -/
theorem secondDerivOpLp_ae_eq (hq : 1 < q) (i j : Fin d) [Fact (1 ≤ ENNReal.ofReal q)]
    (G : Lp ℝ (ENNReal.ofReal q) (volume : Measure (PS d))) (hG2 : MemLp (⇑G) 2 volume) :
    ⇑(secondDerivOpLp hq i j G) =ᵐ[volume] ⇑(secondDerivOp one_pos i j (hG2.toLp G)) := by
  have h := UnforcedLeray.CZ.extendOfBound_toLp (secondDerivOp one_pos i j) (ENNReal.ofReal q)
    (Classical.choose (secondDerivOp_eLpNorm_le (d := d) i j hq))
    (Classical.choose_spec (secondDerivOp_eLpNorm_le (d := d) i j hq)) ENNReal.ofReal_ne_top
    hG2 (Lp.memLp G)
  rwa [Lp.toLp_coeFn] at h

/-- **Transposition on `L^q`.** `∫ (T_q G) φ = ∫ G · backTest 1 i j φ` for every `G ∈ L^q` and
every test `φ`. -/
theorem integral_secondDerivOpLp_mul (hq : 1 < q) (i j : Fin d) [Fact (1 ≤ ENNReal.ofReal q)]
    (G : Lp ℝ (ENNReal.ofReal q) (volume : Measure (PS d))) {φ : PS d → ℝ} (hφ : IsSTTest φ) :
    ∫ X, secondDerivOpLp hq i j G X * φ X = ∫ X, G X * backTest 1 i j φ X := by
  have := holderTriple_ofReal hq
  have hq' : 1 < q.conjExponent := (Real.HolderConjugate.conjExponent hq).symm.lt
  have c1 : Continuous (fun G : Lp ℝ (ENNReal.ofReal q) (volume : Measure (PS d)) =>
      ∫ X, secondDerivOpLp hq i j G X * φ X) :=
    (continuous_integral_mul_Lp (p' := ENNReal.ofReal q.conjExponent)
      (hφ.memLp _)).comp (secondDerivOpLp hq i j).continuous
  have c2 : Continuous (fun G : Lp ℝ (ENNReal.ofReal q) (volume : Measure (PS d)) =>
      ∫ X, G X * backTest 1 i j φ X) :=
    continuous_integral_mul_Lp (memLp_backTest_rpow hφ i j hq')
  have hd := UnforcedLeray.CZ.dense_lpTwo (μ := (volume : Measure (PS d)))
    (p := ENNReal.ofReal q) ENNReal.ofReal_ne_top
  refine congrFun (Continuous.ext_on hd c1 c2 fun G hG => ?_) G
  have hG2 : MemLp (⇑G) 2 volume := hG
  have e1 : ∫ X, secondDerivOpLp hq i j G X * φ X =
      ∫ X, secondDerivOp one_pos i j (hG2.toLp G) X * ((hφ.memLp 2).toLp φ :
        Lp ℝ 2 (volume : Measure (PS d))) X := by
    refine integral_congr_ae ?_
    filter_upwards [secondDerivOpLp_ae_eq hq i j G hG2, (hφ.memLp 2).coeFn_toLp] with X h1 h2
    rw [h1, h2]
  rw [e1, integral_secondDerivOp_mul, backOp_toLp one_pos hφ i j]
  refine integral_congr_ae ?_
  filter_upwards [hG2.coeFn_toLp, (memLp_backTest one_pos hφ i j).coeFn_toLp] with X h1 h2
  rw [h1, h2]

end LqOperator

section MainOne

variable {u F : PS d → ℝ}

/-- **INF02 T8 at `ν = 1` (eq:free-stress-11, second spatial derivatives).** For
`1 < q < ∞` there is `C = C(d, q)` such that: if `u, F ∈ L^q(ℝ × ℝ^d)` and `(∂_t - Δ)u = F`
against tests, then for all `i, j` the weak derivative `∂_i∂_j u` exists in `L^q`, with
`‖∂_i∂_j u‖_q ≤ C ‖F‖_q`. -/
theorem heat_maximal_regularity_one {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ {u F : PS d → ℝ}, MemLp u (ENNReal.ofReal q) volume →
      MemLp F (ENNReal.ofReal q) volume →
      (∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * (-tD φ X - 1 * sLap φ X) = ∫ X, F X * φ X) →
      ∃ D2 : Fin d → Fin d → PS d → ℝ, ∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧
        (∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X) ∧
        eLpNorm (D2 i j) (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_lt hq⟩
  refine ⟨∑ i : Fin d, ∑ j : Fin d, ‖secondDerivOpLp (d := d) hq i j‖₊,
    fun {u F} hu hF heq => ?_⟩
  refine ⟨fun i j => ⇑(secondDerivOpLp hq i j (hF.toLp F)), fun i j =>
    ⟨Lp.memLp _, fun φ hφ => ?_, ?_⟩⟩
  · rw [integral_mul_sD2_eq_rpow hq hu hF heq hφ i j, integral_secondDerivOpLp_mul hq i j _ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp] with X hX
    rw [hX]
  · have hle : ‖secondDerivOpLp (d := d) hq i j‖₊ ≤
        ∑ i : Fin d, ∑ j : Fin d, ‖secondDerivOpLp (d := d) hq i j‖₊ :=
      (Finset.single_le_sum (f := fun j' => ‖secondDerivOpLp (d := d) hq i j'‖₊)
        (fun _ _ => zero_le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i' => ∑ j' : Fin d, ‖secondDerivOpLp (d := d) hq i' j'‖₊)
          (fun _ _ => zero_le) (Finset.mem_univ i))
    calc eLpNorm (⇑(secondDerivOpLp hq i j (hF.toLp F))) (ENNReal.ofReal q) volume
        ≤ ‖secondDerivOpLp (d := d) hq i j‖₊ * eLpNorm (⇑(hF.toLp F)) (ENNReal.ofReal q) volume :=
          UnforcedLeray.CZ.eLpNorm_apply_le_of_Lp _ _
      _ ≤ (∑ i : Fin d, ∑ j : Fin d, ‖secondDerivOpLp (d := d) hq i j‖₊ : ℝ≥0) *
            eLpNorm F (ENNReal.ofReal q) volume := by
          rw [eLpNorm_congr_ae hF.coeFn_toLp]
          gcongr

end MainOne

end UnforcedLeray.Parabolic
