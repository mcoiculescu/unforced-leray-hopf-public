import UnforcedLeray.Short.PartIIb.Tasks.FreeCylinderBound.SmallC

/-!
# `PartII-b:T24` (`FreeCylinderBound.lean`): assembly of `FreeCylinderBound`

Source of record: `the November 2 reference manuscript`, lines 2074-2118
(`short-bg:free-cylinder`).

Combines:
* `free_cyl_energy` (`PartII-b:T22`, `Tasks/CylEnergy.lean`) for smooth cylinder test data when
  `1 ≤ p.c`,
* `small_c_energy_bound` (`Tasks/FreeCylinderBound/SmallC.lean`) for smooth cylinder test data when
  `p.c ≤ 1`,
* `free_cyl_exists_approx` and `free_cyl_unique` (`PartII-b:T23`, `Tasks/CylExistence.lean`,
  `Sub/PartII-b_T23.lean`) for existence, uniqueness, and `X_{m,c}`-density of smooth cylinder test
  approximants `(fn n, ωn n) → (f, ω)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- Triangle inequality helper: `eLpNorm g 2 μ ≤ eLpNorm (gn - g) 2 μ + eLpNorm gn 2 μ`. -/
private theorem eLpNorm_le_sub_add {c m : ℝ} {g gn : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hgn : MemLp gn 2 (B0579.cellMeasure c m)) :
    eLpNorm g 2 (B0579.cellMeasure c m) ≤
      eLpNorm (gn - g) 2 (B0579.cellMeasure c m) + eLpNorm gn 2 (B0579.cellMeasure c m) := by
  have heq : g = (g - gn) + gn := by funext x; simp
  have hneg : g - gn = -(gn - g) := by funext x; simp
  calc eLpNorm g 2 (B0579.cellMeasure c m)
      = eLpNorm ((g - gn) + gn) 2 (B0579.cellMeasure c m) := by rw [← heq]
    _ ≤ eLpNorm (g - gn) 2 (B0579.cellMeasure c m) +
          eLpNorm gn 2 (B0579.cellMeasure c m) :=
        eLpNorm_add_le (hg.sub hgn).aestronglyMeasurable hgn.aestronglyMeasurable one_le_two
    _ = eLpNorm (gn - g) 2 (B0579.cellMeasure c m) +
          eLpNorm gn 2 (B0579.cellMeasure c m) := by rw [hneg, eLpNorm_neg]

/-- Triangle inequality helper: `eLpNorm gn 2 μ ≤ eLpNorm (gn - g) 2 μ + eLpNorm g 2 μ`. -/
private theorem eLpNorm_le_sub_add_right {c m : ℝ} {g gn : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hgn : MemLp gn 2 (B0579.cellMeasure c m)) :
    eLpNorm gn 2 (B0579.cellMeasure c m) ≤
      eLpNorm (gn - g) 2 (B0579.cellMeasure c m) + eLpNorm g 2 (B0579.cellMeasure c m) := by
  have heq : gn = (gn - g) + g := by funext x; simp
  calc eLpNorm gn 2 (B0579.cellMeasure c m)
      = eLpNorm ((gn - g) + g) 2 (B0579.cellMeasure c m) := by rw [← heq]
    _ ≤ eLpNorm (gn - g) 2 (B0579.cellMeasure c m) +
          eLpNorm g 2 (B0579.cellMeasure c m) :=
        eLpNorm_add_le (hgn.sub hg).aestronglyMeasurable hg.aestronglyMeasurable one_le_two

/-- **Main theorem (`PartII-b:T24`)**: existence, uniqueness, and weighted `L²` growth bound for the
free cylinder evolution `IsFreeCylFlow`. -/
theorem freeCylinderBound_proof : UnforcedLeray.Short.IIb.FreeCylinderBound := by
  intro m hm Sg hSg
  obtain ⟨Cm₁, C₁, b, hCm₁, hC₁, hb, hE₁⟩ := free_cyl_energy m hm Sg hSg
  obtain ⟨Cm₂, C₂, hCm₂, hC₂, hE₂⟩ := small_c_energy_bound hm hSg
  set Cm : ℝ := max Cm₁ Cm₂
  set C : ℝ := max C₁ (C₂ * Real.exp b + C₂)
  have hCm_pos : 0 < Cm := lt_of_lt_of_le hCm₁ (le_max_left _ _)
  have hC_pos : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨Cm, C, b, hCm_pos, hC_pos, hb, ?_⟩
  intro p d dm dp hreg δ hδ hclose s t hs hst htT f hf
  have hν : 0 < p.ν := p.ν_pos
  have hc0 : 0 < p.c := p.c_pos
  have hts_nn : 0 ≤ t - s := sub_nonneg.2 hst
  set K : ℝ := Cm * p.ν + C * δ + C * Real.exp (-b * p.c ^ 2)
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (K * (t - s)))
  -- Smooth-datum bound for all p.c > 0
  have hSmooth : ∀ (g : B0579.Plane → ℝ), B0579.IsCylTest p.c g →
      ∀ (u : ℝ → B0579.Plane → ℝ), IsFreeCylFlow m p.train s g u →
        eLpNorm (u t) 2 (B0579.cellMeasure p.c m) ≤
          A * eLpNorm g 2 (B0579.cellMeasure p.c m) := by
    intro g hg u hu
    rcases le_total 1 p.c with hc1 | hc1
    · have hbd := (hE₁ p hc1 δ hδ hclose s hs g hg u hu).2 t hst htT
      have hCm_le : Cm₁ ≤ Cm := le_max_left _ _
      have hC_le : C₁ ≤ C := le_max_left _ _
      have hexp_nn : 0 ≤ Real.exp (-b * p.c ^ 2) := (Real.exp_pos _).le
      have hK_le : (Cm₁ * p.ν + C₁ * δ + C₁ * Real.exp (-b * p.c ^ 2)) * (t - s) ≤
          K * (t - s) := by
        apply mul_le_mul_of_nonneg_right _ hts_nn
        dsimp [K]
        nlinarith
      have hA_le : ENNReal.ofReal (Real.exp
          ((Cm₁ * p.ν + C₁ * δ + C₁ * Real.exp (-b * p.c ^ 2)) * (t - s))) ≤ A :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hK_le)
      exact hbd.trans (mul_le_mul_of_nonneg_right hA_le zero_le)
    · have hbd := hE₂ p hc1 hreg.train_buc δ hδ hclose s t hs hst htT g hg u hu
      have hCm_le : Cm₂ ≤ Cm := le_max_right _ _
      have hC_le : C₂ * Real.exp b + C₂ ≤ C := le_max_right _ _
      have hC2_le : C₂ ≤ C := by
        have : 0 ≤ C₂ * Real.exp b := mul_nonneg hC₂.le (Real.exp_pos _).le
        linarith
      have hc2_le : p.c ^ 2 ≤ 1 := by nlinarith
      have hexp_b : 1 ≤ Real.exp b * Real.exp (-b * p.c ^ 2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      have hC2_exp : C₂ ≤ C * Real.exp (-b * p.c ^ 2) := by
        calc C₂ = C₂ * 1 := (mul_one _).symm
          _ ≤ C₂ * (Real.exp b * Real.exp (-b * p.c ^ 2)) :=
              mul_le_mul_of_nonneg_left hexp_b hC₂.le
          _ = (C₂ * Real.exp b) * Real.exp (-b * p.c ^ 2) := by ring
          _ ≤ C * Real.exp (-b * p.c ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      have hK_le : (Cm₂ * p.ν + C₂ * δ + C₂) * (t - s) ≤ K * (t - s) := by
        apply mul_le_mul_of_nonneg_right _ hts_nn
        dsimp [K]
        nlinarith
      have hA_le : ENNReal.ofReal (Real.exp ((Cm₂ * p.ν + C₂ * δ + C₂) * (t - s))) ≤ A :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hK_le)
      exact hbd.trans (mul_le_mul_of_nonneg_right hA_le zero_le)
  -- Existence and smooth approximation from T23
  obtain ⟨ω, fn, ωn, hω, hfn, hfn_conv, hωn, hωn_conv⟩ :=
    free_cyl_exists_approx m p.ν p.c hm hν hc0 p.train hreg.train_buc s hs f hf
  refine ⟨ω, hω, fun ω' hω' t' ht' =>
    free_cyl_unique m p.ν p.c hm hν hc0 p.train hreg.train_buc s hs f ω' ω hω' hω t' ht', ?_⟩
  -- Pass the bound to the limit as n → ∞
  have hstep : ∀ n : ℕ, eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≤
      eLpNorm (ωn n t - ω t) 2 (B0579.cellMeasure p.c m) +
        A * (eLpNorm (fn n - f) 2 (B0579.cellMeasure p.c m) +
          eLpNorm f 2 (B0579.cellMeasure p.c m)) := by
    intro n
    have h1 := eLpNorm_le_sub_add (hω.memX t hst) ((hωn n).memX t hst)
    have h2 := hSmooth (fn n) (hfn n) (ωn n) (hωn n)
    have h3 := eLpNorm_le_sub_add_right hf ((hfn n).memLp m)
    calc eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)
        ≤ eLpNorm (ωn n t - ω t) 2 (B0579.cellMeasure p.c m) +
            eLpNorm (ωn n t) 2 (B0579.cellMeasure p.c m) := h1
      _ ≤ eLpNorm (ωn n t - ω t) 2 (B0579.cellMeasure p.c m) +
            A * eLpNorm (fn n) 2 (B0579.cellMeasure p.c m) :=
          add_le_add le_rfl h2
      _ ≤ eLpNorm (ωn n t - ω t) 2 (B0579.cellMeasure p.c m) +
            A * (eLpNorm (fn n - f) 2 (B0579.cellMeasure p.c m) +
              eLpNorm f 2 (B0579.cellMeasure p.c m)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 zero_le)
  have hA_ne_top : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlim_inner : Tendsto (fun n => eLpNorm (fn n - f) 2 (B0579.cellMeasure p.c m) +
      eLpNorm f 2 (B0579.cellMeasure p.c m)) atTop
      (𝓝 (0 + eLpNorm f 2 (B0579.cellMeasure p.c m))) :=
    hfn_conv.add tendsto_const_nhds
  rw [zero_add] at hlim_inner
  have hlim_mul : Tendsto (fun n => A * (eLpNorm (fn n - f) 2 (B0579.cellMeasure p.c m) +
      eLpNorm f 2 (B0579.cellMeasure p.c m))) atTop
      (𝓝 (A * eLpNorm f 2 (B0579.cellMeasure p.c m))) :=
    ENNReal.Tendsto.const_mul hlim_inner (Or.inr hA_ne_top)
  have hlim_tot : Tendsto (fun n => eLpNorm (ωn n t - ω t) 2 (B0579.cellMeasure p.c m) +
      A * (eLpNorm (fn n - f) 2 (B0579.cellMeasure p.c m) +
        eLpNorm f 2 (B0579.cellMeasure p.c m))) atTop
      (𝓝 (0 + A * eLpNorm f 2 (B0579.cellMeasure p.c m))) :=
    (hωn_conv t hst).add hlim_mul
  rw [zero_add] at hlim_tot
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim_tot hstep

end UnforcedLeray.Short.IIb

end
