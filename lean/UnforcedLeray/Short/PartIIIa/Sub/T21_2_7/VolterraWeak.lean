import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

/-!
# Part III-a, `PartIII-a:T21/2/7/1`: mild solutions of the Volterra problem are weak

Source of record: `the November 2 reference manuscript`, lines 2819-2836 (the
Duhamel form of the Volterra iteration). Statement `VolterraWeakForm` in `AdjWeakDefs.lean`.

On a strip `[k, τ] ⊆ [k, k+1]` the evolution `u(r) = E(r, 0)x` satisfies the mild equation
`u(r) = S₀(r-k)u(k) + ∫_k^r S(r-σ)B(σ)u(σ)` (evolution law + `evolution_volterra`); applying `ℓ` and
the two hypotheses gives `ℓ(u(τ)) = ℓ(u(k)) + ∫_k^τ (ℓ'(u) + ℓB(Bu))` (`vw_strip`); induction over
the strips `[n, n+1]` gives the identity on `[0, τ]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Infra.VolterraEvolution

section VW

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X]
  [SMulCommClass ℝ ℂ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The integrand `r ↦ ℓ'(u r) + ℓB(B r (u r))` is continuous on `[0, ∞)`. -/
theorem vw_cont (D : VolterraData ℂ X Y) (hD : D.Compatible) (ℓ' : X →L[ℂ] ℂ)
    (ℓB : Y →L[ℂ] ℂ) (x : X) :
    ContinuousOn (fun r => ℓ' (D.evolution r 0 x) + ℓB (D.B r (D.evolution r 0 x))) (Ici 0) := by
  have hu : ContinuousOn (fun r => D.evolution r 0 x) (Ici 0) :=
    VolterraData.continuousOn_evolution hD 0 x
  have hF : ContinuousOn (fun r => D.B r (D.evolution r 0 x)) (Ici 0) :=
    continuousOn_clm_apply (fun e => (D.continuous_B e).continuousOn)
      (fun _ _ => ⟨D.β, Eventually.of_forall fun σ => D.norm_B_le σ⟩) hu
  exact (ℓ'.continuous.comp_continuousOn hu).add (ℓB.continuous.comp_continuousOn hF)

/-- The mild equation from an intermediate age `k ≥ 0`. -/
theorem vw_mild (D : VolterraData ℂ X Y) (hD : D.Compatible) (x : X) {k r : ℝ} (hk : 0 ≤ k)
    (hr : r ∈ Icc k (k + 1)) :
    D.evolution r 0 x = D.S₀ (r - k) (D.evolution k 0 x) +
      ∫ σ in k..r, D.S (r - σ) (D.B σ (D.evolution σ 0 x)) := by
  rw [← VolterraData.evolution_apply_comp hD hk hr.1 x, VolterraData.evolution_volterra hD hr]
  congr 1
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hr.1] at hσ
  simp only [VolterraData.evolution_apply_comp hD hk hσ.1 x]

/-- **One strip.** -/
theorem vw_strip (D : VolterraData ℂ X Y) (hD : D.Compatible) (ℓ ℓ' : X →L[ℂ] ℂ)
    (ℓB : Y →L[ℂ] ℂ)
    (h0 : ∀ x : X, ∀ τ ∈ Icc (0 : ℝ) 1, ℓ (D.S₀ τ x) = ℓ x + ∫ r in (0 : ℝ)..τ, ℓ' (D.S₀ r x))
    (h1 : ∀ (F : ℝ → Y) (a b : ℝ), a ≤ b → b ≤ a + 1 → ContinuousOn F (Icc a b) →
      ∀ τ ∈ Icc a b,
        ℓ (∫ r in a..τ, D.S (τ - r) (F r)) =
          (∫ r in a..τ, ℓ' (∫ σ in a..r, D.S (r - σ) (F σ))) + ∫ r in a..τ, ℓB (F r))
    (x : X) {k τ : ℝ} (hk : 0 ≤ k) (hkτ : k ≤ τ) (hτ : τ ≤ k + 1) :
    ℓ (D.evolution τ 0 x) = ℓ (D.evolution k 0 x) +
      ∫ r in k..τ, (ℓ' (D.evolution r 0 x) + ℓB (D.B r (D.evolution r 0 x))) := by
  have hu : ContinuousOn (fun r => D.evolution r 0 x) (Ici 0) :=
    VolterraData.continuousOn_evolution hD 0 x
  have hF : ContinuousOn (fun r => D.B r (D.evolution r 0 x)) (Ici 0) :=
    continuousOn_clm_apply (fun e => (D.continuous_B e).continuousOn)
      (fun _ _ => ⟨D.β, Eventually.of_forall fun σ => D.norm_B_le σ⟩) hu
  have hsubI : Icc k τ ⊆ Ici (0 : ℝ) := fun r hr => hk.trans hr.1
  have hFk : ContinuousOn (fun r => D.B r (D.evolution r 0 x)) (Icc k τ) := hF.mono hsubI
  -- the free part, shifted
  have hS0 : ContinuousOn (fun r => D.S₀ (r - k) (D.evolution k 0 x)) (Icc k τ) :=
    (D.continuousOn_S₀ (D.evolution k 0 x)).comp (continuousOn_id.sub continuousOn_const)
      fun r hr => show r - k ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hS0c : ContinuousOn (fun r => ℓ' (D.S₀ (r - k) (D.evolution k 0 x))) (Icc k τ) :=
    ℓ'.continuous.comp_continuousOn hS0
  -- the Duhamel part is `u - S₀(· - k) y` on the strip
  have hDuh : ∀ r ∈ Icc k τ, ∫ σ in k..r, D.S (r - σ) (D.B σ (D.evolution σ 0 x)) =
      D.evolution r 0 x - D.S₀ (r - k) (D.evolution k 0 x) := by
    intro r hr
    rw [vw_mild D hD x hk ⟨hr.1, hr.2.trans hτ⟩]
    abel
  have hDuhc : ContinuousOn (fun r => ℓ' (∫ σ in k..r, D.S (r - σ) (D.B σ (D.evolution σ 0 x))))
      (Icc k τ) := by
    refine (ℓ'.continuous.comp_continuousOn ((hu.mono hsubI).sub hS0)).congr fun r hr => ?_
    simp only [Function.comp_apply, Pi.sub_apply, hDuh r hr]
  have hBc : ContinuousOn (fun r => ℓB (D.B r (D.evolution r 0 x))) (Icc k τ) :=
    ℓB.continuous.comp_continuousOn hFk
  have hUc : ContinuousOn (fun r => ℓ' (D.evolution r 0 x)) (Icc k τ) :=
    ℓ'.continuous.comp_continuousOn (hu.mono hsubI)
  -- the two hypotheses
  have e0 := h0 (D.evolution k 0 x) (τ - k) ⟨by linarith, by linarith⟩
  have eshift : ∫ r in k..τ, ℓ' (D.S₀ (r - k) (D.evolution k 0 x)) = ∫ r in (0 : ℝ)..(τ - k), ℓ' (D.S₀ r (D.evolution k 0 x)) := by
    rw [intervalIntegral.integral_comp_sub_right (fun r => ℓ' (D.S₀ r (D.evolution k 0 x))) k, sub_self]
  have e1 := h1 (fun r => D.B r (D.evolution r 0 x)) k τ hkτ hτ hFk τ ⟨hkτ, le_rfl⟩
  have hsplit : ∫ r in k..τ, ℓ' (D.evolution r 0 x) =
      (∫ r in k..τ, ℓ' (D.S₀ (r - k) (D.evolution k 0 x))) +
        ∫ r in k..τ, ℓ' (∫ σ in k..r, D.S (r - σ) (D.B σ (D.evolution σ 0 x))) := by
    rw [← intervalIntegral.integral_add (hS0c.intervalIntegrable_of_Icc hkτ)
      (hDuhc.intervalIntegrable_of_Icc hkτ)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hkτ] at hr
    simp only [hDuh r hr, map_sub]
    ring
  rw [intervalIntegral.integral_add (hUc.intervalIntegrable_of_Icc hkτ)
      (hBc.intervalIntegrable_of_Icc hkτ), hsplit, vw_mild D hD x hk ⟨hkτ, hτ⟩, map_add, e0,
    ← eshift, e1]
  ring

/-- `E(0, 0) = 1`. -/
theorem vw_zero (D : VolterraData ℂ X Y) (hD : D.Compatible)
    (h00 : D.S₀ 0 = ContinuousLinearMap.id ℂ X) (x : X) : D.evolution 0 0 x = x := by
  have h := VolterraData.evolution_volterra hD (s := 0) (τ := 0) ⟨le_rfl, by norm_num⟩ x
  rw [h, sub_self, h00, intervalIntegral.integral_same, add_zero, ContinuousLinearMap.id_apply]

end VW

/-- **(c) Mild solutions of the Volterra problem are weak** (SP 2819-2836). -/
theorem volterraWeakForm : VolterraWeakForm := by
  intro X Y _ _ _ _ _ _ _ D hD h00 ℓ ℓ' ℓB h0 h1 x
  set f : ℝ → ℂ := fun r => ℓ' (D.evolution r 0 x) + ℓB (D.B r (D.evolution r 0 x)) with hf
  have hfc : ContinuousOn f (Ici 0) := vw_cont D hD ℓ' ℓB x
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b ha hab => (hfc.mono fun r hr => ha.trans hr.1).intervalIntegrable_of_Icc hab
  have key : ∀ n : ℕ, ∀ τ ∈ Icc (0 : ℝ) n,
      ℓ (D.evolution τ 0 x) = ℓ x + ∫ r in (0 : ℝ)..τ, f r := by
    intro n
    induction n with
    | zero =>
      intro τ hτ
      have hτ0 : τ = 0 := le_antisymm (by simpa using hτ.2) hτ.1
      subst hτ0
      rw [vw_zero D hD h00 x, intervalIntegral.integral_same, add_zero]
    | succ n ih =>
      intro τ hτ
      rcases le_total τ n with hτn | hτn
      · exact ih τ ⟨hτ.1, hτn⟩
      · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hτ1 : τ ≤ (n : ℝ) + 1 := by simpa using hτ.2
        rw [vw_strip D hD ℓ ℓ' ℓB h0 h1 x hn hτn hτ1, ih n ⟨hn, le_rfl⟩, add_assoc,
          intervalIntegral.integral_add_adjacent_intervals (hint 0 n le_rfl hn)
            (hint n τ hn hτn)]
  intro τ hτ
  exact key ⌈τ⌉₊ τ ⟨hτ, Nat.le_ceil τ⟩

end UnforcedLeray.Short.IIIa
