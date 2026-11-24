import UnforcedLeray.Units.B0423

/-!
# Part II-a, task `PartII-a:F09/2/org`: the reflected heat estimate

Source `the November 2 reference manuscript`
lines 1377-1382 (the local heat estimate `‖νD²u‖_r ≤ C_{d,r}‖F‖_r` for `u_t - νΔu = F`),
1417-1418 ("the reflected kernel has the same bounds") and 1467-1469 ("At `r = 2`, reverse the
phase window ... for `L^* = -𝒯 - νΔ + 1`").

A distributional solution of the *backward* heat equation, `(∂_θ + νΔ_x) u = F`
(`B0423.IsWeakHeatSolC (-ν) u F` with `ν > 0`), has the same second-derivative bound as a forward
one. Proof: the reflection `θ ↦ -θ` (`Parabolic.trev`, measure preserving) turns it into
`(∂_θ - νΔ_x)(u ∘ trev) = -(F ∘ trev)` (`isWeakHeatSolC_trev`); apply
`B0423.heat_estimate_complex_laplacian` and reflect the weak second derivatives back
(`Parabolic.sD2_comp_trev`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.Parabolic

variable {d : ℕ}

/-- The reflection `trev (θ, x) = (-θ, x)` as a homeomorphism of `ℝ × ℝ^d`. -/
def trevHomeo (d : ℕ) : PS d ≃ₜ PS d :=
  Homeomorph.mk ⟨trev, trev, trev_trev, trev_trev⟩ continuous_trev continuous_trev

theorem measurableEmbedding_trev : MeasurableEmbedding (trev : PS d → PS d) :=
  (trevHomeo d).measurableEmbedding

/-- Change of variables `X ↦ trev X` (measure preserving involution). -/
theorem integral_comp_trev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : PS d → E) : ∫ X, g (trev X) = ∫ X, g X :=
  measurePreserving_trev.integral_comp measurableEmbedding_trev g

/-- **Reflection of a backward heat solution** (source 1467-1469): if `(∂_θ + νΔ_x) u = F`
weakly (`IsWeakHeatSolC (-ν) u F`), then `(∂_θ - νΔ_x)(u ∘ trev) = -(F ∘ trev)` weakly. -/
theorem isWeakHeatSolC_trev {ν : ℝ} {u F : PS d → ℂ} (h : B0423.IsWeakHeatSolC (-ν) u F) :
    B0423.IsWeakHeatSolC ν (u ∘ trev) (fun X => -F (trev X)) := by
  intro φ hφ
  have hφ' : IsSTTest (φ ∘ trev) := hφ.comp_trev
  have key := h (φ ∘ trev) hφ'
  have htD : tD (φ ∘ trev) = fun X => -tD φ (trev X) := tD_comp_trev hφ.differentiable
  have hsL : sLap (φ ∘ trev) = (sLap φ) ∘ trev := sLap_comp_trev hφ.1
  rw [htD, hsL] at key
  have e1 : ∫ X, (u ∘ trev) X * ((-tD φ X - ν * sLap φ X : ℝ) : ℂ) =
      ∫ Y, u Y * ((-tD φ (trev Y) - ν * sLap φ (trev Y) : ℝ) : ℂ) := by
    rw [← integral_comp_trev (fun Y => u Y * ((-tD φ (trev Y) - ν * sLap φ (trev Y) : ℝ) : ℂ))]
    simp only [Function.comp_apply, trev_trev]
  have e2 : ∫ Y, u Y * ((-tD φ (trev Y) - ν * sLap φ (trev Y) : ℝ) : ℂ) =
      -∫ Y, u Y * ((-(-tD φ (trev Y)) - -ν * (sLap φ ∘ trev) Y : ℝ) : ℂ) := by
    rw [← integral_neg]
    congr 1
    funext Y
    simp only [Function.comp_apply]
    push_cast
    ring
  have e3 : ∫ X, -F (trev X) * (φ X : ℂ) = -∫ Y, F Y * ((φ ∘ trev) Y : ℂ) := by
    rw [← integral_neg, ← integral_comp_trev (fun Y => -(F Y * ((φ ∘ trev) Y : ℂ)))]
    congr 1
    funext X
    simp only [Function.comp_apply, trev_trev]
    ring
  rw [e1, e2, key, e3]

/-- **The reflected heat estimate** (source 1377-1382, 1417-1418, 1467-1469): for `1 < q < ∞`
there is `C = C(d, q)` such that for every `ν > 0` and all complex `u, F ∈ L^q(ℝ × ℝ^d)` with
`(∂_θ + νΔ_x) u = F` in distributions (`IsWeakHeatSolC (-ν) u F`), `u` has weak second spatial
derivatives `D2 i j ∈ L^q` with `‖ν Σ_i D2 i i‖_q ≤ C ‖F‖_q`. -/
theorem heat_estimate_complex_laplacian_neg {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ≥0, ∀ ν : ℝ, 0 < ν → ∀ u F : PS d → ℂ,
      MemLp u (ENNReal.ofReal q) volume → MemLp F (ENNReal.ofReal q) volume →
      B0423.IsWeakHeatSolC (-ν) u F →
      ∃ D2 : Fin d → Fin d → PS d → ℂ,
        (∀ i j, MemLp (D2 i j) (ENNReal.ofReal q) volume ∧
          B0423.HasWeakSpaceDeriv2C u i j (D2 i j)) ∧
        eLpNorm (fun X => (ν : ℂ) * ∑ i, D2 i i X) (ENNReal.ofReal q) volume ≤
          C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := B0423.heat_estimate_complex_laplacian (d := d) hq
  refine ⟨C, fun ν hν u F hu hF heq => ?_⟩
  have hu' : MemLp (u ∘ trev) (ENNReal.ofReal q) volume :=
    hu.comp_measurePreserving measurePreserving_trev
  have hF' : MemLp (fun X => -F (trev X)) (ENNReal.ofReal q) volume :=
    (hF.comp_measurePreserving measurePreserving_trev).neg
  obtain ⟨D2, -, hD2, -, -, hb, -⟩ :=
    hC ν hν (u ∘ trev) (fun X => -F (trev X)) hu' hF' (isWeakHeatSolC_trev heq)
  refine ⟨fun i j => D2 i j ∘ trev,
    fun i j => ⟨(hD2 i j).1.comp_measurePreserving measurePreserving_trev, ?_⟩, ?_⟩
  · intro φ hφ
    have h := (hD2 i j).2 (φ ∘ trev) hφ.comp_trev
    rw [sD2_comp_trev hφ i j] at h
    calc ∫ X, u X * (sD2 i j φ X : ℂ)
        = ∫ X, (u ∘ trev) X * ((sD2 i j φ ∘ trev) X : ℂ) := by
          rw [← integral_comp_trev (fun X => u X * (sD2 i j φ X : ℂ))]
          rfl
      _ = ∫ X, D2 i j X * ((φ ∘ trev) X : ℂ) := h
      _ = ∫ X, (D2 i j ∘ trev) X * (φ X : ℂ) := by
          rw [← integral_comp_trev (fun X => (D2 i j ∘ trev) X * (φ X : ℂ))]
          simp only [Function.comp_apply, trev_trev]
  · have hm : AEStronglyMeasurable (fun X => (ν : ℂ) * ∑ i, D2 i i X) volume :=
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hD2 i i).1.1).const_mul _
    have e : (fun X => (ν : ℂ) * ∑ i, (fun i j => D2 i j ∘ trev) i i X) =
        (fun X => (ν : ℂ) * ∑ i, D2 i i X) ∘ trev := rfl
    rw [e, eLpNorm_comp_measurePreserving hm measurePreserving_trev]
    refine hb.trans (le_of_eq ?_)
    congr 1
    have e' : (fun X => -F (trev X)) = -(F ∘ trev) := rfl
    rw [e', eLpNorm_neg, eLpNorm_comp_measurePreserving hF.1 measurePreserving_trev]

end UnforcedLeray.Short.PartIIa
