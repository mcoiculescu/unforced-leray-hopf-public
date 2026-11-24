import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStability

/-!
# Block-uniform strong small-diffusion limit (helper for `PartI:C03/2`)

Copy of `UnforcedLeray.Cons.G3b.exists_delta_canonicalTransportDysonFamily_uniform_strong_small`
(`Cons/L2/CanonicalBranch/DysonStability.lean:966`). The only change is that the block `[a,b]` is
quantified after `∃ δ`, so the threshold `δ` is chosen once for all blocks of length `B`. The proof
never uses `a` or `b` before the `intro` line: the threshold is built from `hB`, `x`, `ε` alone
(`freeDiffusion_uniform_strong_small_on_compact`, `exists_delta_freeDiffusion_small_on_boundedGeneratorOrbit`),
and the block only enters through the hypotheses and the family.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0012 UnforcedLeray.B0123 UnforcedLeray.Evolution

set_option maxHeartbeats 600000 in
/-- Block-uniform actual strong convergence of the concrete first Dyson stage to its inviscid
transport-minus-λ evolution: the threshold `δ` does not depend on the block `[a,b]`. -/
theorem exists_delta_canonicalTransportDysonFamily_uniform_strong_small_blocks {B : ℝ}
    (hB : 0 < B) (lam κ : ℂ) (x : XG) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a b : ℝ) (β : ℝ → ℝ)
      (hβi : ∀ u v, IntervalIntegrable β volume u v)
      (hβ0 : ∀ τ, 0 ≤ β τ)
      (hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
      (hβM : ∀ r, |β r| ≤ δ) (s t : ℝ),
      a ≤ s → s ≤ t → t ≤ b → t - s ≤ B →
      ‖(canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm
        (⟨δ, fun r _ => hβM r⟩ : ∃ C₀ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₀)).U t s x -
          (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s x‖ < ε := by
  let G := canonicalTransportLimitGenerator lam
  let L : ℝ := ‖(-2 * Complex.I) • omegaOp‖ + ‖lam‖ + ‖κ‖
  let C : ℝ := Real.exp (‖G‖ * B) * ‖x‖
  let R : ℝ := Real.exp (L * B)
  let ρ : ℝ := ε / (2 * R)
  let η₀ : ℝ := ρ / 2
  let η : ℝ := ρ / (4 * B)
  let δp : ℝ := ρ / (4 * B * (‖κ‖ * C + 1))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 < R := Real.exp_pos _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hδp : 0 < δp := by dsimp [δp]; positivity
  obtain ⟨δi, hδi, hsmalli⟩ := freeDiffusion_uniform_strong_small_on_compact hB
    (isCompact_singleton : IsCompact ({x} : Set XG)) hη₀
  obtain ⟨δo, hδo, hsmallo⟩ :=
    exists_delta_freeDiffusion_small_on_boundedGeneratorOrbit hB G x hη
  let δ := min δi (min δo (min δp 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδi (lt_min hδo (lt_min hδp zero_lt_one))
  have hδi' : δ ≤ δi := by dsimp [δ]; exact min_le_left _ _
  have hδo' : δ ≤ δo := by
    dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδp' : δ ≤ δp := by
    dsimp [δ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨δ, hδ, ?_⟩
  intro a b β hβi hβ0 hβsm hβM s t hs hst ht hspan
  have hβδi : ∀ r, β r ≤ δi := fun r => (le_abs_self (β r)).trans (hβM r) |>.trans hδi'
  have hβδo : ∀ r, β r ≤ δo := fun r => (le_abs_self (β r)).trans (hβM r) |>.trans hδo'
  have hβblock : ∃ C₀ : ℝ, ∀ r ∈ Set.Icc a b, |β r| ≤ C₀ :=
    ⟨δ, fun r _ => hβM r⟩
  let F := canonicalTransportDysonFamily lam κ β hβi hβ0 δ hβM hβsm hβblock
  let V := canonicalTransportLimitFamily (a := a) (b := b) lam
  have hinit : ∀ u, s ≤ u → u ≤ t → ‖freeDiffusion β u s x - x‖ ≤ η₀ := by
    intro u hsu hut
    have hspanu : u - s ≤ B := (sub_le_sub_right hut s).trans hspan
    have hsmall := hsmalli β s u hsu hspanu (hβi s u) hβ0 hβδi x (Set.mem_singleton x)
    exact hsmall.le
  have horbit : ∀ u, s ≤ u → u ≤ t → ∀ r, s ≤ r → r ≤ u →
      ‖(freeDiffusion β u r - 1) (G (V.U r s x))‖ ≤ η := by
    intro u hsu hut r hsr hru
    have hspanu : u - s ≤ B := (sub_le_sub_right hut s).trans hspan
    have hspanur : u - r ≤ B := by linarith
    have hspanr : r - s ≤ B := by linarith
    have hu' : r - s ∈ Set.Icc (0 : ℝ) B := ⟨sub_nonneg.mpr hsr, hspanr⟩
    have hsmall := hsmallo β r u hru hspanur (hβi r u) hβ0 hβδo (r - s) hu'
    have hrepr : V.U r s x = NormedSpace.exp (((r - s : ℝ) : ℂ) • G) x := by
      simp [V, G, canonicalTransportLimitFamily,
      UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
      UnforcedLeray.Infra.ExpSemigroup.ofExp_T]
    simpa [ContinuousLinearMap.sub_apply, hrepr] using hsmall.le
  have hVbound : ∀ u, s ≤ u → u ≤ t → ∀ r, s ≤ r → r ≤ u → ‖V.U r s x‖ ≤ C := by
    intro u hsu hut r hsr hru
    have hspanr : r - s ≤ B := by linarith
    have h := canonicalTransportLimitFamily_apply_norm_le lam hs hsr (le_trans hru (le_trans hut ht)) hspanr x
    simpa [C, G] using h
  have hGron := canonicalTransportDysonFamily_difference_gronwall
    lam κ β hβi hβ0 δ hβM hβsm hβblock hs hst ht
    hB hspan (le_of_lt hδ) hδ1 hβM (le_of_lt hη) (le_of_lt hη₀) hC x
    hinit horbit hVbound
  have hηB : B * η = ρ / 4 := by
    dsimp [η]
    field_simp
  have hκC : 0 ≤ ‖κ‖ * C := mul_nonneg (norm_nonneg _) hC
  have hpert : B * δ * ‖κ‖ * C ≤ ρ / 4 := by
    have hδterm : B * δ * (‖κ‖ * C) ≤ B * δp * (‖κ‖ * C) := by
      calc
        B * δ * (‖κ‖ * C) = B * (δ * (‖κ‖ * C)) := by ring
        _ ≤ B * (δp * (‖κ‖ * C)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδp' hκC) hB.le
        _ = B * δp * (‖κ‖ * C) := by ring
    have hratio : B * δp * (‖κ‖ * C) ≤ ρ / 4 := by
      dsimp [δp]
      have hden : 4 * B * (‖κ‖ * C + 1) ≠ 0 := by positivity
      field_simp
      nlinarith [hρ, hB, hκC]
    calc
      B * δ * ‖κ‖ * C = B * δ * (‖κ‖ * C) := by ring
      _ ≤ B * δp * (‖κ‖ * C) := hδterm
      _ ≤ ρ / 4 := hratio
  have hA : η₀ + B * η + B * δ * ‖κ‖ * C ≤ ρ := by
    dsimp [η₀]
    rw [hηB]
    linarith
  have hExp : Real.exp (L * (t - s)) ≤ R := by
    dsimp [R]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hspan hL)
  have hbound : ‖F.U t s x - V.U t s x‖ ≤ ρ * R := by
    calc
      ‖F.U t s x - V.U t s x‖ ≤
          (η₀ + B * η + B * δ * ‖κ‖ * C) * Real.exp (L * (t - s)) := by
            simpa [F, V, L] using hGron
      _ ≤ ρ * R := by
        calc
          (η₀ + B * η + B * δ * ‖κ‖ * C) * Real.exp (L * (t - s)) ≤
              ρ * Real.exp (L * (t - s)) :=
                mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
          _ ≤ ρ * R := mul_le_mul_of_nonneg_left hExp hρ.le
  have hρR : ρ * R = ε / 2 := by dsimp [ρ]; field_simp
  rw [hρR] at hbound
  have hFinal : ‖F.U t s x - V.U t s x‖ < ε := by linarith
  simpa [F, V] using hFinal

end UnforcedLeray.Cons.G3b
