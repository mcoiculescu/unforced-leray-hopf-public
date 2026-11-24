import UnforcedLeray.Lib.ParabolicB.Duality
import UnforcedLeray.Lib.ParabolicB.LqOp
import UnforcedLeray.Lib.ParabolicB.Scaling

/-!
# Parabolic maximal `L^q` regularity, distributional form (Wave 3, block 3D PARAB2: INF02 T8)

Main file of block 3D of the Lean build plan

(`heat_maximal_regularity`) of the scoping note `scoping/INF02-FabesRiviere.md` §5, for every
`1 < q < ∞`, stated with every second spatial derivative (`scoping/INF01-CZ.md` §4.5), built under
decision D4 (the parabolic instance of the CZ core `Lib/CZCore`, through `Lib/Parabolic` T5–T7).
Namespace `UnforcedLeray.Parabolic`.

Manuscript: the lemma eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit
B0423): if `d ≥ 1`, `1 < q < ∞`, `ν > 0`, and `u, F ∈ L^q(ℝ × ℝ^d)` satisfy
`(∂_θ - νΔ_x)u = F` distributionally (with `u` compactly supported in time), then
`‖ν D_x² u‖_q + ‖∂_θ u‖_q ≤ C_{d,q} ‖F‖_q`, with `C_{d,q}` independent of `ν`. The manuscript
cites Fabes–Rivière for the singular-integral bound of the causal kernel (line 7466); here it is
the CZ bound `secondDerivOp_eLpNorm_le` of `Lib/Parabolic/LqBound`. Nothing here proves Theorem A
or `UnforcedLeray.MainClaim`.

| Step (tex 7464–7477) | Module | Main declarations |
|---|---|---|
| `L^{q'}` bound of the transpose | `ParabolicB/Duality` | `backOp_eLpNorm_le`, `memLp_backTest_rpow`, `memLp_sD_backTest_rpow` |
| identification ("mollify `u, F`", 7472–7476) | `ParabolicB/Duality` | `integral_mul_sD2_eq_of_integrable`, `integral_mul_sD2_eq_rpow` |
| the operator on `L^q`, `ν = 1` | `ParabolicB/LqOp` | `continuous_integral_mul_Lp`, `secondDerivOpLp`, `integral_secondDerivOpLp_mul`, `heat_maximal_regularity_one` |
| viscosity scaling (7469–7470) | `ParabolicB/Scaling` | `tsc`, `map_tsc`, `integral_comp_tsc`, `eLpNorm_comp_tsc`, `heatEq_tsc`, `weakSD2_of_tsc`, `eLpNorm_smul_comp_tsc_le` |
| `∂_θ u` from the equation (7476–7477) | this file | `exists_timeDeriv_of_sD2` |
| eq:free-stress-11 | this file | `heat_maximal_regularity`, `heat_maximal_regularity_of_timeCompact` |

Deviations from the manuscript and from the indicative signature of `INF02-FabesRiviere.md` §5:

* The compact time support of `u` is not assumed by `heat_maximal_regularity` (it is not needed:
  the backward test `backTest 1 i j φ` and its spatial gradient lie in `L^{q'}` globally, by the
  CZ bound of the transpose). `heat_maximal_regularity_of_timeCompact` keeps the manuscript's
  hypothesis literally.
* Weak derivatives are stated as integral identities against `IsSTTest` tests
  (`ContDiff ℝ ∞` with compact support), as in `heat_maximal_regularity_two` (`Lib/Parabolic/QTwo`).
* The bound is given componentwise: `‖ν ∂_i∂_j u‖_q ≤ C ‖F‖_q` for every `i, j`, and
  `‖∂_θ u‖_q ≤ C ‖F‖_q`, with one `C = C(d, q)` independent of `ν`, `u`, `F`.
* The manuscript's spatial dilation `x = √ν z` is replaced by the time dilation `θ = s / ν`
  (`tsc`), which needs no Gaussian rescaling.
* The identification is by duality against the backward test (as at `q = 2` in `QTwo`), not by
  mollification of `u, F`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

section TimeDerivative

variable {q ν : ℝ} {u F : PS d → ℝ}

/-- **`∂_θ u` from the equation.** If `(∂_t - νΔ)u = F` against tests and `u` has weak second
derivatives `D2 i j ∈ L^q` with `‖ν D2 i i‖_q ≤ C ‖F‖_q`, then `Dt = F + ν Σᵢ D2 i i` is the weak
time derivative of `u`, `Dt ∈ L^q` and `‖Dt‖_q ≤ (1 + d C) ‖F‖_q` (tex 7476–7477, "the equation
then gives `∂_θ u`"). -/
theorem exists_timeDeriv_of_sD2 (hq : 1 < q) (hu : MemLp u (ENNReal.ofReal q) volume)
    (hF : MemLp F (ENNReal.ofReal q) volume)
    (heq : ∀ φ : PS d → ℝ, IsSTTest φ →
      ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X)
    {D2 : Fin d → Fin d → PS d → ℝ} (hD2m : ∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume)
    (hweak : ∀ i j (φ : PS d → ℝ), IsSTTest φ → ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X)
    {C : ℝ≥0}
    (hb : ∀ i, eLpNorm (fun X => ν * D2 i i X) (ENNReal.ofReal q) volume ≤
      C * eLpNorm F (ENNReal.ofReal q) volume) :
    MemLp (fun X => F X + ν * ∑ i : Fin d, D2 i i X) (ENNReal.ofReal q) volume ∧
      (∀ φ : PS d → ℝ, IsSTTest φ →
        ∫ X, u X * tD φ X = -∫ X, (F X + ν * ∑ i : Fin d, D2 i i X) * φ X) ∧
      eLpNorm (fun X => F X + ν * ∑ i : Fin d, D2 i i X) (ENNReal.ofReal q) volume ≤
        ((1 + d * C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
  have hq1 := one_le_ofReal_of_one_lt hq
  set Dt : PS d → ℝ := fun X => F X + ν * ∑ i : Fin d, D2 i i X with hDt
  have hDtm : MemLp Dt (ENNReal.ofReal q) volume := by
    have hs : MemLp (fun X => ∑ i : Fin d, D2 i i X) (ENNReal.ofReal q) volume :=
      memLp_finsetSum (f := fun i => D2 i i) Finset.univ fun i _ => hD2m i i
    exact hF.add (hs.const_mul ν)
  refine ⟨hDtm, fun φ hφ => ?_, ?_⟩
  · have iT : Integrable (fun X => u X * tD φ X) volume :=
      integrable_mul_test_of_memLp hq hu (isSTTest_tD hφ)
    have iL : ∀ k : Fin d, Integrable (fun X => u X * sD2 k k φ X) volume :=
      fun k => integrable_mul_test_of_memLp hq hu (hφ.sD2 k k)
    have iD : ∀ k : Fin d, Integrable (fun X => D2 k k X * φ X) volume :=
      fun k => integrable_mul_test_of_memLp hq (hD2m k k) hφ
    have iFφ : Integrable (fun X => F X * φ X) volume := integrable_mul_test_of_memLp hq hF hφ
    have h1 := heq φ hφ
    have e1 : ∫ X, u X * (-tD φ X - ν * sLap φ X) =
        -(∫ X, u X * tD φ X) - ν * ∑ k : Fin d, ∫ X, u X * sD2 k k φ X := by
      have hpt : ∀ X, u X * (-tD φ X - ν * sLap φ X) =
          -(u X * tD φ X) - ν * ∑ k : Fin d, u X * sD2 k k φ X := by
        intro X
        simp only [sLap]
        rw [← Finset.mul_sum]; ring
      have iTn : Integrable (fun X => -(u X * tD φ X)) volume := iT.neg
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iTn
        ((integrable_finsetSum _ fun k _ => iL k).const_mul ν), integral_neg,
        integral_const_mul, integral_finsetSum _ fun k _ => iL k]
    have e2 : ∫ X, Dt X * φ X = (∫ X, F X * φ X) + ν * ∑ k : Fin d, ∫ X, D2 k k X * φ X := by
      have hpt : ∀ X, Dt X * φ X = F X * φ X + ν * ∑ k : Fin d, D2 k k X * φ X := by
        intro X
        simp only [hDt]
        rw [add_mul, mul_assoc, Finset.sum_mul]
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_add iFφ
        ((integrable_finsetSum _ fun k _ => iD k).const_mul ν), integral_const_mul,
        integral_finsetSum _ fun k _ => iD k]
    have e3 : ∀ k : Fin d, ∫ X, u X * sD2 k k φ X = ∫ X, D2 k k X * φ X :=
      fun k => hweak k k φ hφ
    simp_rw [e3] at e1
    rw [e2]
    linarith
  · have hm : ∀ i : Fin d, AEStronglyMeasurable (fun X => ν * D2 i i X) volume :=
      fun i => ((hD2m i i).1.const_mul ν)
    have hsum : (fun X => ν * ∑ i : Fin d, D2 i i X) = ∑ i : Fin d, fun X => ν * D2 i i X := by
      funext X; rw [Finset.sum_apply, Finset.mul_sum]
    have hDt' : Dt = F + ∑ i : Fin d, fun X => ν * D2 i i X := by
      funext X; simp only [hDt, Pi.add_apply]; rw [← hsum]
    rw [hDt']
    calc eLpNorm (F + ∑ i : Fin d, fun X => ν * D2 i i X) (ENNReal.ofReal q) volume
        ≤ eLpNorm F (ENNReal.ofReal q) volume +
            eLpNorm (∑ i : Fin d, fun X => ν * D2 i i X) (ENNReal.ofReal q) volume :=
          eLpNorm_add_le hF.1 (Finset.aestronglyMeasurable_sum _ fun i _ => hm i) hq1
      _ ≤ eLpNorm F (ENNReal.ofReal q) volume +
            ∑ i : Fin d, eLpNorm (fun X => ν * D2 i i X) (ENNReal.ofReal q) volume := by
          gcongr
          exact eLpNorm_sum_le (fun i _ => hm i) hq1
      _ ≤ eLpNorm F (ENNReal.ofReal q) volume +
            ∑ _i : Fin d, (C : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
          gcongr with i
          exact hb i
      _ = ((1 + d * C : ℝ≥0) : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal q) volume := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

end TimeDerivative

section Main

/-- **INF02 T8: eq:free-stress-11 for `1 < q < ∞`** (`paper/main.tex` lines 7447–7477,
blueprint unit B0423), with every second spatial derivative. For `1 < q < ∞` there is a constant
`C = C(d, q)` such that for every `ν > 0` and all `u, F ∈ L^q(ℝ × ℝ^d)` with
`(∂_t - νΔ)u = F` against tests (`∫ u (-∂_t φ - νΔφ) = ∫ F φ`): `u` has weak second spatial
derivatives `D2 i j ∈ L^q` and a weak time derivative `Dt ∈ L^q`, with
`‖ν D2 i j‖_q ≤ C ‖F‖_q` for all `i, j` and `‖Dt‖_q ≤ C ‖F‖_q`. The constant does not depend on
`ν`. (The manuscript's compact time support of `u` is not needed; see
`heat_maximal_regularity_of_timeCompact` for the literal form.) -/
theorem heat_maximal_regularity {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ {ν : ℝ}, 0 < ν → ∀ {u F : PS d → ℝ},
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      (∀ φ : PS d → ℝ, IsSTTest φ →
        ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X) →
      ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧
          ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧
        (∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * tD φ X = -∫ X, Dt X * φ X) ∧
        (∀ i j, eLpNorm (fun X => ν * D2 i j X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume) ∧
        eLpNorm Dt (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C₁, hC₁⟩ := heat_maximal_regularity_one (d := d) hq
  refine ⟨C₁ + (1 + d * C₁), fun {ν} hν {u F} hu hF heq => ?_⟩
  have hν' : ν⁻¹ ≠ 0 := inv_ne_zero hν.ne'
  have hus : MemLp (u ∘ tsc d ν⁻¹) (ENNReal.ofReal q) volume := memLp_comp_tsc hν' hu
  have hFs : MemLp (fun Y => ν⁻¹ * F (tsc d ν⁻¹ Y)) (ENNReal.ofReal q) volume :=
    (memLp_comp_tsc hν' hF).const_mul ν⁻¹
  obtain ⟨Ds, hDs⟩ := hC₁ hus hFs (heatEq_tsc hν heq)
  set D2 : Fin d → Fin d → PS d → ℝ := fun i j => Ds i j ∘ tsc d ν with hD2
  have hD2m : ∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume :=
    fun i j => memLp_comp_tsc hν.ne' (hDs i j).1
  have hweak : ∀ i j (φ : PS d → ℝ), IsSTTest φ →
      ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X :=
    fun i j φ hφ => weakSD2_of_tsc hν (hDs i j).2.1 hφ
  have hb : ∀ i j, eLpNorm (fun X => ν * D2 i j X) (ENNReal.ofReal q) volume ≤
      C₁ * eLpNorm F (ENNReal.ofReal q) volume :=
    fun i j => eLpNorm_smul_comp_tsc_le hν ENNReal.ofReal_ne_top (hDs i j).2.2
  obtain ⟨hDtm, hDtw, hDtb⟩ := exists_timeDeriv_of_sD2 hq hu hF heq hD2m hweak (fun i => hb i i)
  refine ⟨D2, _, fun i j => ⟨hD2m i j, hweak i j⟩, hDtm, hDtw, fun i j => (hb i j).trans ?_,
    hDtb.trans ?_⟩
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (le_self_add : C₁ ≤ C₁ + (1 + d * C₁))
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (le_add_self : 1 + d * C₁ ≤ C₁ + (1 + d * C₁))

/-- **eq:free-stress-11 with the manuscript's hypotheses, literally** (`paper/main.tex` lines
7452–7461, blueprint unit B0423): the same conclusion as `heat_maximal_regularity` when `u` is in
addition compactly supported in time (a hypothesis the proof does not use). -/
theorem heat_maximal_regularity_of_timeCompact {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ {ν : ℝ}, 0 < ν → ∀ {u F : PS d → ℝ},
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      (∃ R : ℝ, ∀ X : PS d, R < |X.1| → u X = 0) →
      (∀ φ : PS d → ℝ, IsSTTest φ →
        ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X) →
      ∃ D2 : Fin d → Fin d → PS d → ℝ, ∃ Dt : PS d → ℝ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧
          ∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * sD2 i j φ X = ∫ X, D2 i j X * φ X) ∧
        MemLp Dt (ENNReal.ofReal q) volume ∧
        (∀ φ : PS d → ℝ, IsSTTest φ → ∫ X, u X * tD φ X = -∫ X, Dt X * φ X) ∧
        (∀ i j, eLpNorm (fun X => ν * D2 i j X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume) ∧
        eLpNorm Dt (ENNReal.ofReal q) volume ≤ C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := heat_maximal_regularity (d := d) hq
  exact ⟨C, fun {ν} hν {u F} hu hF _ heq => hC hν hu hF heq⟩

end Main

end UnforcedLeray.Parabolic
