import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.EnergyChain
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/1/5`: the spatial bootstrap from its leaves

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3073
(the energies `E_j`, the inequalities `E_j' + βE_{j+1} ≤ C(E_j + ⋯ + E_0)` in the reverse time, and
"integrate the first inequality and then the inequality for `rE_1(r)`"), 3044-3050, 3052-3058.

* `adjHkGainOn_of`: one gain of regularity on a closed interval `[a, b] ⊆ [t, s)`, from the energy
  inequalities of the mollified adjoint (`AdjMollEnergy`), the scalar chain `adjointEnergyChain`
  (proved, SP 3072-3073) in the reverse time `ζ = b₁ - r`, `b₁ = min b (r + 1)`, and the passage to
  the limit of the regularization (`CellWeakDerivOfMollBound`);
* `gain_jet`: the next fields chosen pointwise (`jetExt`) form a level-`(k + 1)` jet with a uniform
  bound (`WeakCellAeUnique` identifies the chosen derivative with the bounded one);
* `adjHkStepOn_of`: `C(I; H^k) → C(I; H^{k+1})` on every `I` whose points have closed neighbourhoods
  `[a, b] ⊆ I`, `t ≤ a`, `b < s`: two gains give level-`(k + 2)` bounds near each point, and the
  interpolation inequality `CellInterp` gives the continuity of the new fields;
* `adjHkStep_of` (`I = (t, s)`) and `adjHkStepEnd_of` (`I = [t, s)`, the end-age form
  `AdjHkStepEnd` of `Sub/PartIII-a_T21_2_7_2_1_2.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Elementary facts -/

theorem hasWeakCellDerivC_sub {c : ℝ} {j : Fin 2} {f₁ f₂ g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : HasWeakCellDerivC c j f₁ g₁) (h₂ : HasWeakCellDerivC c j f₂ g₂) :
    HasWeakCellDerivC c j (f₁ - f₂) (g₁ - g₂) := by
  have ef : ∀ ψ : ℝ × ℝ → ℝ, (fun x => (f₁ - f₂) x * (B0579.pd j ψ x : ℂ)) =
      fun x => f₁ x * (B0579.pd j ψ x : ℂ) - f₂ x * (B0579.pd j ψ x : ℂ) :=
    fun ψ => funext fun x => by simp only [Pi.sub_apply, sub_mul]
  have eg : ∀ ψ : ℝ × ℝ → ℝ, (fun x => (g₁ - g₂) x * (ψ x : ℂ)) =
      fun x => g₁ x * (ψ x : ℂ) - g₂ x * (ψ x : ℂ) :=
    fun ψ => funext fun x => by simp only [Pi.sub_apply, sub_mul]
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · rw [ef ψ]
    exact Integrable.sub (h₁.1 ψ hψ).1 (h₂.1 ψ hψ).1
  · rw [eg ψ]
    exact Integrable.sub (h₁.1 ψ hψ).2 (h₂.1 ψ hψ).2
  · rw [ef ψ, eg ψ, integral_sub (h₁.1 ψ hψ).1 (h₂.1 ψ hψ).1,
      integral_sub (h₁.1 ψ hψ).2 (h₂.1 ψ hψ).2, h₁.2 ψ hψ, h₂.2 ψ hψ]
    ring

theorem xNorm_sub_le {c m : ℝ} {u v : ℝ × ℝ → ℂ} (hu : MemLp u 2 (B0579.cellMeasure c (-m)))
    (hv : MemLp v 2 (B0579.cellMeasure c (-m))) :
    xNorm c (-m) (u - v) ≤ xNorm c (-m) u + xNorm c (-m) v := by
  unfold xNorm
  exact eLpNorm_sub_le hu.1 hv.1 (by norm_num)

theorem xNorm_ne_top {c m : ℝ} {u : ℝ × ℝ → ℂ} (hu : MemLp u 2 (B0579.cellMeasure c (-m))) :
    xNorm c (-m) u ≠ ⊤ := by
  unfold xNorm
  exact hu.2.ne

/-- `x² ≤ y B` with `B` finite and `y → 0` forces `x → 0` (in `ℝ≥0∞`). -/
theorem tendsto_of_sq_le_mul {α : Type*} {l : Filter α} {x y : α → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hy : Tendsto y l (𝓝 0)) (hxy : ∀ᶠ a in l, x a ^ 2 ≤ y a * B) :
    Tendsto x l (𝓝 0) := by
  have h1 : Tendsto (fun a => y a * B) l (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hy (Or.inr hB)
    simpa using this
  have h2 : Tendsto (fun a => x a ^ 2) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
      (Eventually.of_forall fun a => (zero_le : (0 : ℝ≥0∞) ≤ x a ^ 2)) hxy
  have h3 : Tendsto (fun a => (x a ^ 2) ^ (((2 : ℕ) : ℝ))⁻¹) l
      (𝓝 ((0 : ℝ≥0∞) ^ (((2 : ℕ) : ℝ))⁻¹)) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h2
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  have e : (fun a => (x a ^ 2) ^ (((2 : ℕ) : ℝ))⁻¹) = x :=
    funext fun a => ENNReal.pow_rpow_inv_natCast two_ne_zero (x a)
  rwa [e] at h3

/-! ## Mollified jets and their energies -/

/-- The classical partials of the mollification of a jet are the mollified fields
(`CellMollWeakDeriv`, by induction on the word). -/
theorem adjSpatial_cellMoll_jet (hW : CellMollWeakDeriv) {c m : ℝ} (hc : 0 < c) {k : ℕ}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : IsCellJet c m k f D) (n : ℕ) :
    ∀ w : List (Fin 2), w.length ≤ k → adjSpatial w (cellMoll n f) = cellMoll n (D w)
  | [], _ => by rw [hJ.base]; rfl
  | j :: w, hw => by
    have hw' : w.length < k := by simpa using hw
    show pdCx j (adjSpatial w (cellMoll n f)) = cellMoll n (D (j :: w))
    rw [adjSpatial_cellMoll_jet hW hc hJ n w hw'.le]
    exact hW c m j (D w) (D (j :: w)) hc (hJ.periodic w hw'.le) (hJ.periodic (j :: w) hw)
      (hJ.memX w hw'.le) (hJ.memX (j :: w) hw) (hJ.deriv j w hw') n

/-- The mollified energy of order `k` of a jet bounded by `M` is bounded uniformly in `n`
(`CellMollBound`). -/
theorem cellEnergy_jet_le (hW : CellMollWeakDeriv) {c m : ℝ} (hc : 0 < c) {k : ℕ}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : IsCellJet c m k f D) {Cm M : ℝ}
    (hCm0 : 0 ≤ Cm) (hM0 : 0 ≤ M)
    (hCm : ∀ (n : ℕ) (u : ℝ × ℝ → ℂ), (∀ x : ℝ × ℝ, u (x.1 + c, x.2) = u x) →
      MemLp u 2 (B0579.cellMeasure c (-m)) →
      xNorm c (-m) (cellMoll n u) ≤ ENNReal.ofReal Cm * xNorm c (-m) u)
    (hDM : ∀ w : List (Fin 2), w.length ≤ k → xNorm c (-m) (D w) ≤ ENNReal.ofReal M) (n : ℕ) :
    cellEnergy c m k (cellMoll n f) ≤ ((wordsLE k).card : ℝ) * (Cm * M) ^ 2 := by
  unfold cellEnergy
  have hterm : ∀ w ∈ wordsLE k,
      (xNorm c (-m) (adjSpatial w (cellMoll n f))).toReal ^ 2 ≤ (Cm * M) ^ 2 := by
    intro w hw
    have hwl := mem_wordsLE.1 hw
    rw [adjSpatial_cellMoll_jet hW hc hJ n w hwl]
    have h1 : xNorm c (-m) (cellMoll n (D w)) ≤ ENNReal.ofReal (Cm * M) := by
      calc xNorm c (-m) (cellMoll n (D w)) ≤ ENNReal.ofReal Cm * xNorm c (-m) (D w) :=
            hCm n (D w) (hJ.periodic w hwl) (hJ.memX w hwl)
        _ ≤ ENNReal.ofReal Cm * ENNReal.ofReal M := by gcongr; exact hDM w hwl
        _ = ENNReal.ofReal (Cm * M) := (ENNReal.ofReal_mul hCm0).symm
    have h2 := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCm0 hM0) h1
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg h2 2
  calc ∑ w ∈ wordsLE k, (xNorm c (-m) (adjSpatial w (cellMoll n f))).toReal ^ 2
      ≤ ∑ _w ∈ wordsLE k, (Cm * M) ^ 2 := Finset.sum_le_sum hterm
    _ = ((wordsLE k).card : ℝ) * (Cm * M) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## One gain of regularity -/

/-- **`AdjHkGainOn` from its leaves** (SP 3060-3073). -/
theorem adjHkGainOn_of (m : ℝ) (hE : AdjMollEnergy m) (hS : CellMollSmooth) (hB : CellMollBound)
    (hW : CellMollWeakDeriv) (hP : CellWeakDerivOfMollBound) : AdjHkGainOn m := by
  intro ν hν hν1 tr hTB hTJ t s ht hts g φ hφ hTD k a b hta hab hbs D M hDj hDM b' hb'
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨C, β, hC0, hβ, hEn⟩ :=
    hE ν hν hν1 tr hTB hTJ t s ht hts g φ hφ hTD k a b hta hab hbs D M hDj hDM
  obtain ⟨K, hK0, hK⟩ := adjointEnergyChain C hC0
  obtain ⟨Cm, hCm0, hCm⟩ := hB _ m hc
  set c := ν ^ (-2 : ℝ) with hc_def
  set Mp := max M 0 with hMp
  have hMp0 : 0 ≤ Mp := le_max_right _ _
  have hDMp : ∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k →
      xNorm c (-m) (D r w) ≤ ENNReal.ofReal Mp :=
    fun r hr w hw => (hDM r hr w hw).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set β' := min β 1 with hβ'
  have hβ'0 : 0 < β' := lt_min hβ one_pos
  have hβ'β : β' ≤ β := min_le_left _ _
  set δ := min (b - b') 1 with hδ
  have hδ0 : 0 < δ := lt_min (sub_pos.2 hb') one_pos
  set E0 := ((wordsLE k).card : ℝ) * (Cm * Mp) ^ 2 + M ^ 2 with hE0
  have hE00 : 0 ≤ E0 := by positivity
  set Bnd := K * (β' * δ)⁻¹ * E0 with hBnd
  have hBnd0 : 0 ≤ Bnd :=
    mul_nonneg (mul_nonneg hK0 (inv_nonneg.2 (mul_pos hβ'0 hδ0).le)) hE00
  refine ⟨2 * Real.sqrt Bnd, fun r₀ hr₀ w hw j => ?_⟩
  have hr₀ab : r₀ ∈ Icc a b := ⟨hr₀.1, hr₀.2.trans hb'.le⟩
  have hper : ∀ r ∈ Icc a b, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x :=
    fun r hr x => hφ.periodic r ⟨hta.trans hr.1, hr.2.trans_lt hbs⟩ x
  have hmem : ∀ r ∈ Icc a b, MemLp (φ r) 2 (B0579.cellMeasure c (-m)) :=
    fun r hr => hφ.memX r ⟨hta.trans hr.1, (hr.2.trans_lt hbs).le⟩
  -- the energy of order `k + 1` at `r₀`, uniformly in the regularization
  have hN : ∀ n : ℕ, cellEnergy c m (k + 1) (cellMoll n (φ r₀)) ≤ Bnd := by
    intro n
    set b₁ := min b (r₀ + 1) with hb₁
    have hr₀b₁ : r₀ < b₁ := lt_min (hr₀.2.trans_lt hb') (lt_add_one r₀)
    have hb₁b : b₁ ≤ b := min_le_left _ _
    set Δ := b₁ - r₀ with hΔ
    have hΔ0 : 0 < Δ := sub_pos.2 hr₀b₁
    have hΔ1 : Δ ≤ 1 := by
      have : b₁ ≤ r₀ + 1 := min_le_right _ _
      linarith
    have hδΔ : δ ≤ Δ := by
      rcases le_total b (r₀ + 1) with h | h
      · have h1 : b₁ = b := min_eq_left h
        have h2 : δ ≤ b - b' := min_le_left _ _
        have h3 : r₀ ≤ b' := hr₀.2
        linarith
      · have h1 : b₁ = r₀ + 1 := min_eq_right h
        have h2 : δ ≤ 1 := min_le_right _ _
        linarith
    have hmaps : MapsTo (fun ζ : ℝ => b₁ - ζ) (Icc 0 Δ) (Icc a b) := by
      intro ζ hζ
      exact ⟨by linarith [hζ.2, hr₀.1], by linarith [hζ.1]⟩
    have hsubIoo : ∀ ζ ∈ Ioo 0 Δ, b₁ - ζ ∈ Ioo a b := by
      intro ζ hζ
      exact ⟨by linarith [hζ.2, hr₀.1], by linarith [hζ.1]⟩
    have hcont : ContinuousOn (fun ζ : ℝ => b₁ - ζ) (Icc 0 Δ) :=
      (continuous_const.sub continuous_id).continuousOn
    obtain ⟨hc0, hd0⟩ := hEn n k (Nat.le_succ k)
    obtain ⟨hc1, hd1⟩ := hEn n (k + 1) le_rfl
    have hD0 : ∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ,
        HasDerivAt (fun ζ => cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2) D ζ ∧
        D + β' * cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) ≤
          C * (cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2) := by
      intro ζ hζ
      obtain ⟨d, hd, hineq⟩ := hd0 (b₁ - ζ) (hsubIoo ζ hζ)
      refine ⟨-d, (HasDerivAt.comp_const_sub b₁ ζ hd).add_const _, ?_⟩
      have h1 : β' * cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) ≤
          β * cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) :=
        mul_le_mul_of_nonneg_right hβ'β (cellEnergy_nonneg _ _ _ _)
      linarith
    have hD1 : ∀ ζ ∈ Ioo 0 Δ, ∃ D : ℝ,
        HasDerivAt (fun ζ => cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ)))) D ζ ∧
        D + β' * cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))) ≤
          C * (cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) +
            (cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2)) := by
      intro ζ hζ
      obtain ⟨d, hd, hineq⟩ := hd1 (b₁ - ζ) (hsubIoo ζ hζ)
      refine ⟨-d, HasDerivAt.comp_const_sub b₁ ζ hd, ?_⟩
      have h1 : β' * cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))) ≤
          β * cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))) :=
        mul_le_mul_of_nonneg_right hβ'β (cellEnergy_nonneg _ _ _ _)
      have h2 : C * (cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) + M ^ 2) ≤
          C * (cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))) +
            (cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2)) := by
        have := cellEnergy_nonneg c m k (cellMoll n (φ (b₁ - ζ)))
        exact mul_le_mul_of_nonneg_left (by linarith) hC0
      linarith
    have hchain := (hK β' Δ hβ'0 (min_le_right _ _) hΔ0 hΔ1
      (fun ζ => cellEnergy c m k (cellMoll n (φ (b₁ - ζ))) + M ^ 2)
      (fun ζ => cellEnergy c m (k + 1) (cellMoll n (φ (b₁ - ζ))))
      (fun ζ => cellEnergy c m (k + 1 + 1) (cellMoll n (φ (b₁ - ζ))))
      ((hc0.comp hcont hmaps).add continuousOn_const)
      ((hc1.comp hcont hmaps).mono Ioc_subset_Icc_self)
      (fun ζ _ => add_nonneg (cellEnergy_nonneg _ _ _ _) (sq_nonneg _))
      (fun ζ _ => cellEnergy_nonneg _ _ _ _)
      (fun ζ _ => cellEnergy_nonneg _ _ _ _) hD0 hD1).2
    have e1 : b₁ - Δ = r₀ := by simp only [hΔ]; ring
    simp only [e1, sub_zero] at hchain
    have hb₁ab : b₁ ∈ Icc a b := ⟨hr₀.1.trans hr₀b₁.le, hb₁b⟩
    have hEk : cellEnergy c m k (cellMoll n (φ b₁)) + M ^ 2 ≤ E0 := by
      have := cellEnergy_jet_le hW hc (hDj b₁ hb₁ab) hCm0 hMp0 hCm (hDMp b₁ hb₁ab) n
      simp only [hE0]
      linarith
    have hinv : (β' * Δ)⁻¹ ≤ (β' * δ)⁻¹ :=
      inv_anti₀ (mul_pos hβ'0 hδ0) (mul_le_mul_of_nonneg_left hδΔ hβ'0.le)
    calc cellEnergy c m (k + 1) (cellMoll n (φ r₀))
        ≤ K * (β' * Δ)⁻¹ * (cellEnergy c m k (cellMoll n (φ b₁)) + M ^ 2) := hchain
      _ ≤ K * (β' * δ)⁻¹ * E0 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hinv hK0) hEk
            (add_nonneg (cellEnergy_nonneg _ _ _ _) (sq_nonneg _))
            (mul_nonneg hK0 (inv_nonneg.2 (mul_pos hβ'0 hδ0).le))
  -- the mollified derivatives of the top field `D r₀ w` are bounded uniformly in `n`
  have hJ := hDj r₀ hr₀ab
  have hjw : ∀ n : ℕ,
      xNorm c (-m) (pdCx j (cellMoll n (D r₀ w))) ≤ ENNReal.ofReal (Real.sqrt Bnd) := by
    intro n
    have e : pdCx j (cellMoll n (D r₀ w)) = adjSpatial (j :: w) (cellMoll n (φ r₀)) := by
      show pdCx j (cellMoll n (D r₀ w)) = pdCx j (adjSpatial w (cellMoll n (φ r₀)))
      rw [adjSpatial_cellMoll_jet hW hc hJ n w hw.le]
    rw [e]
    have hmemw : MemLp (adjSpatial (j :: w) (cellMoll n (φ r₀))) 2
        (B0579.cellMeasure c (-m)) :=
      (hS c m n (φ r₀) hc (hper r₀ hr₀ab) (hmem r₀ hr₀ab)).2.2 (j :: w)
    have hsq : (xNorm c (-m) (adjSpatial (j :: w) (cellMoll n (φ r₀)))).toReal ^ 2 ≤ Bnd :=
      (sq_toReal_le_cellEnergy c m _ (by simp [hw])).trans (hN n)
    rw [← ENNReal.ofReal_toReal (xNorm_ne_top hmemw)]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.abs_le_sqrt hsq))
  obtain ⟨G, hG1, hG2, hG3, hG4⟩ := hP c m j (D r₀ w) (Real.sqrt Bnd) hc
    (hJ.periodic w hw.le) (hJ.memX w hw.le) hjw
  exact ⟨G, hG1, hG2, hG3, hG4⟩

/-- **The gain as a jet**: the next fields chosen pointwise (`jetExt`) form a level-`(k + 1)` jet on
`[a, b']` with a uniform bound (the chosen weak derivative agrees almost everywhere with the bounded
one, `WeakCellAeUnique`). -/
theorem gain_jet {m : ℝ} (hG : AdjHkGainOn m) (hU : WeakCellAeUnique) {ν : ℝ} (hν : 0 < ν)
    (hν1 : ν ≤ 1) {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hB : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    (hJ : ∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ)
    (hD : AdjTestedDeriv tr t s φ) (k : ℕ) {a b : ℝ} (hta : t ≤ a) (hab : a < b) (hbs : b < s)
    {D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} {M : ℝ}
    (hDj : ∀ r ∈ Icc a b, IsCellJet (ν ^ (-2 : ℝ)) m k (φ r) (D r))
    (hDM : ∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k →
      xNorm (ν ^ (-2 : ℝ)) (-m) (D r w) ≤ ENNReal.ofReal M)
    {b' : ℝ} (hb' : b' < b) :
    ∃ M' : ℝ, ∀ r ∈ Icc a b',
      IsCellJet (ν ^ (-2 : ℝ)) m (k + 1) (φ r) (jetExt (ν ^ (-2 : ℝ)) m k (D r)) ∧
      ∀ w : List (Fin 2), w.length ≤ k + 1 →
        xNorm (ν ^ (-2 : ℝ)) (-m) (jetExt (ν ^ (-2 : ℝ)) m k (D r) w) ≤ ENNReal.ofReal M' := by
  obtain ⟨M₁, hM₁⟩ := hG ν hν hν1 tr hB hJ t s ht hts g φ hφ hD k a b hta hab hbs D M hDj hDM b' hb'
  refine ⟨max M M₁, fun r hr => ?_⟩
  have hrab : r ∈ Icc a b := ⟨hr.1, hr.2.trans hb'.le⟩
  have hex : ∀ w : List (Fin 2), w.length = k → ∀ j : Fin 2, ∃ G : ℝ × ℝ → ℂ,
      (∀ x : ℝ × ℝ, G (x.1 + ν ^ (-2 : ℝ), x.2) = G x) ∧
        MemLp G 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
        HasWeakCellDerivC (ν ^ (-2 : ℝ)) j (D r w) G := fun w hw j => by
    obtain ⟨G, h1, h2, h3, -⟩ := hM₁ r hr w hw j
    exact ⟨G, h1, h2, h3⟩
  refine ⟨isCellJet_jetExt (hDj r hrab) hex, fun w hw => ?_⟩
  rcases Nat.lt_or_ge w.length (k + 1) with h | h
  · rw [jetExt_of_le _ m k (D r) w (by omega)]
    exact (hDM r hrab w (by omega)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · cases w with
    | nil => simp at h
    | cons j w =>
      have hwk : w.length = k := by simp at hw h; omega
      rw [jetExt_cons_of_length _ m k (D r) j hwk]
      obtain ⟨G, -, -, hGd, hGb⟩ := hM₁ r hr w hwk j
      have hspec := cellWeakD_spec (hex w hwk j)
      have hae := hU _ j (D r w) _ _ hspec.2.2 hGd
      have hae' : cellWeakD (ν ^ (-2 : ℝ)) m j (D r w) =ᵐ[B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)] G :=
        (B0579.cellMeasure_ac _ _).ae_le hae
      have e : xNorm (ν ^ (-2 : ℝ)) (-m) (cellWeakD (ν ^ (-2 : ℝ)) m j (D r w)) =
          xNorm (ν ^ (-2 : ℝ)) (-m) G := eLpNorm_congr_ae hae'
      rw [e]
      exact hGb.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-! ## The bootstrap step -/

/-- **The bootstrap step on an interval with closed neighbourhoods** (SP 3060-3073):
`C(I; H^k_{-m,c}) → C(I; H^{k+1}_{-m,c})` for every `I` each of whose points `r` has a closed
neighbourhood `[a, b] ⊆ I` within `I`, `t ≤ a ≤ r < b < s`. -/
theorem adjHkStepOn_of {m : ℝ} (hG : AdjHkGainOn m) (hI : CellInterp) (hU : WeakCellAeUnique)
    (hK : CompactJetBound) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hB : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    (hJ : ∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ)
    (hD : AdjTestedDeriv tr t s φ) {I : Set ℝ}
    (hloc : ∀ r ∈ I, ∃ a b : ℝ, t ≤ a ∧ a ≤ r ∧ r < b ∧ b < s ∧ Icc a b ⊆ I ∧
      Icc a b ∈ 𝓝[I] r)
    (k : ℕ) (hk : AdjHkOn (ν ^ (-2 : ℝ)) m k I φ) : AdjHkOn (ν ^ (-2 : ℝ)) m (k + 1) I φ := by
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨D, hDj, hDc⟩ := hk
  set c := ν ^ (-2 : ℝ) with hc_def
  -- near every point: two gains (level `k + 1` and `k + 2` jets with uniform bounds)
  have loc : ∀ r₀ ∈ I, ∃ a b'' : ℝ, a ≤ r₀ ∧ r₀ < b'' ∧ Icc a b'' ∈ 𝓝[I] r₀ ∧
      ∃ M₁ M₂ : ℝ, ∀ r ∈ Icc a b'',
        IsCellJet c m (k + 1) (φ r) (jetExt c m k (D r)) ∧
        IsCellJet c m (k + 1 + 1) (φ r) (jetExt c m (k + 1) (jetExt c m k (D r))) ∧
        (∀ w : List (Fin 2), w.length ≤ k + 1 →
          xNorm c (-m) (jetExt c m k (D r) w) ≤ ENNReal.ofReal M₁) ∧
        (∀ w : List (Fin 2), w.length ≤ k + 1 + 1 →
          xNorm c (-m) (jetExt c m (k + 1) (jetExt c m k (D r)) w) ≤ ENNReal.ofReal M₂) := by
    intro r₀ hr₀
    obtain ⟨a, b, hta, har, hrb, hbs, hsub, hnhds⟩ := hloc r₀ hr₀
    have hab : a < b := lt_of_le_of_lt har hrb
    set b' := (r₀ + b) / 2 with hb'
    set b'' := (r₀ + b') / 2 with hb''
    have hr₀b'' : r₀ < b'' := by simp only [hb'', hb']; linarith
    have hb''b' : b'' < b' := by simp only [hb'', hb']; linarith
    have hb'b : b' < b := by simp only [hb']; linarith
    obtain ⟨M, hM⟩ := hK c m k I (Icc a b) φ D hDj hDc isCompact_Icc hsub
    obtain ⟨M₁, hM₁⟩ := gain_jet hG hU hν hν1 hB hJ ht hts hφ hD k hta hab hbs
      (fun r hr => hDj r (hsub hr)) hM hb'b
    have hab' : a < b' := lt_of_le_of_lt har (hr₀b''.trans hb''b')
    obtain ⟨M₂, hM₂⟩ := gain_jet hG hU hν hν1 hB hJ ht hts hφ hD (k + 1) hta hab'
      (hb'b.trans hbs) (fun r hr => (hM₁ r hr).1) (fun r hr => (hM₁ r hr).2) hb''b'
    refine ⟨a, b'', har, hr₀b'', ?_, M₁, M₂, fun r hr => ?_⟩
    · have h1 : Iio b'' ∈ 𝓝[I] r₀ := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr₀b'')
      filter_upwards [hnhds, h1] with x hx1 hx2
      exact ⟨hx1.1, le_of_lt hx2⟩
    · have hr' : r ∈ Icc a b' := ⟨hr.1, hr.2.trans hb''b'.le⟩
      exact ⟨(hM₁ r hr').1, (hM₂ r hr).1, (hM₁ r hr').2, (hM₂ r hr).2⟩
  refine ⟨fun r => jetExt c m k (D r), fun r hr => ?_, fun w hw r₀ hr₀ => ?_⟩
  · obtain ⟨a, b'', har, hrb, -, M₁, M₂, hL⟩ := loc r hr
    exact (hL r ⟨har, hrb.le⟩).1
  · rcases Nat.lt_or_ge w.length (k + 1) with h | h
    · -- the fields of order `≤ k` are the given ones
      have e : ∀ r, jetExt c m k (D r) w = D r w := fun r => jetExt_of_le c m k (D r) w (by omega)
      simp only [e]
      exact hDc w (by omega) r₀ hr₀
    · -- the top fields: interpolation against the level-`k` continuity
      cases w with
      | nil => simp at h
      | cons j w =>
        have hwk : w.length = k := by simp at hw h; omega
        obtain ⟨a, b'', har, hrb, hnhds, M₁, M₂, hL⟩ := loc r₀ hr₀
        have hr₀mem : r₀ ∈ Icc a b'' := ⟨har, hrb.le⟩
        obtain ⟨J1₀, J2₀, B1₀, B2₀⟩ := hL r₀ hr₀mem
        have hBfin : ENNReal.ofReal (2 * |m|) * (2 * ENNReal.ofReal M₁) +
            2 * ENNReal.ofReal M₂ ≠ ⊤ :=
          ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),
            ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
        refine tendsto_of_sq_le_mul hBfin (hDc w (by omega) r₀ hr₀) ?_
        filter_upwards [hnhds] with r hr
        obtain ⟨J1, J2, B1, B2⟩ := hL r hr
        -- the three fields at `r` and at `r₀`
        have eD : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ},
            jetExt c m k E w = E w := fun {E} => jetExt_of_le c m k E w (by omega)
        have eD1 : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ},
            jetExt c m (k + 1) (jetExt c m k E) (j :: w) = jetExt c m k E (j :: w) :=
          fun {E} => jetExt_of_le c m (k + 1) (jetExt c m k E) (j :: w) (by simp [hwk])
        have hlw : w.length ≤ k + 1 := by omega
        have hljw : (j :: w).length ≤ k + 1 := by simp [hwk]
        have hljjw : (j :: j :: w).length ≤ k + 1 + 1 := by simp [hwk]
        have hperf : ∀ x : ℝ × ℝ, (D r w - D r₀ w) (x.1 + c, x.2) = (D r w - D r₀ w) x := by
          intro x
          have h1 := J1.periodic w hlw x
          have h2 := J1₀.periodic w hlw x
          rw [eD] at h1 h2
          simp only [Pi.sub_apply, h1, h2]
        have hperg : ∀ x : ℝ × ℝ, (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w))
            (x.1 + c, x.2) = (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w)) x := by
          intro x
          simp only [Pi.sub_apply, J1.periodic (j :: w) hljw x, J1₀.periodic (j :: w) hljw x]
        have hperh : ∀ x : ℝ × ℝ,
            (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
              jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) (x.1 + c, x.2) =
            (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
              jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) x := by
          intro x
          simp only [Pi.sub_apply, J2.periodic (j :: j :: w) hljjw x,
            J2₀.periodic (j :: j :: w) hljjw x]
        have hmf : MemLp (D r w - D r₀ w) 2 (B0579.cellMeasure c (-m)) := by
          have h1 := J1.memX w hlw
          have h2 := J1₀.memX w hlw
          rw [eD] at h1 h2
          exact h1.sub h2
        have hmg1 := J1.memX (j :: w) hljw
        have hmg2 := J1₀.memX (j :: w) hljw
        have hmh1 := J2.memX (j :: j :: w) hljjw
        have hmh2 := J2₀.memX (j :: j :: w) hljjw
        have hdf : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ}, IsCellJet c m (k + 1) (φ r) (jetExt c m k E) →
            HasWeakCellDerivC c j (E w) (jetExt c m k E (j :: w)) := by
          intro E hE
          have := hE.deriv j w (by omega)
          rwa [eD] at this
        have hdf₀ : ∀ {E : List (Fin 2) → ℝ × ℝ → ℂ},
            IsCellJet c m (k + 1) (φ r₀) (jetExt c m k E) →
            HasWeakCellDerivC c j (E w) (jetExt c m k E (j :: w)) := by
          intro E hE
          have := hE.deriv j w (by omega)
          rwa [eD] at this
        have hdg : HasWeakCellDerivC c j (jetExt c m k (D r) (j :: w))
            (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w)) := by
          have := J2.deriv j (j :: w) (by simp [hwk])
          rwa [eD1] at this
        have hdg₀ : HasWeakCellDerivC c j (jetExt c m k (D r₀) (j :: w))
            (jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) := by
          have := J2₀.deriv j (j :: w) (by simp [hwk])
          rwa [eD1] at this
        have key := hI c m j (D r w - D r₀ w)
          (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w))
          (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
            jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w))
          hc hperf hperg hperh hmf (hmg1.sub hmg2) (hmh1.sub hmh2)
          (hasWeakCellDerivC_sub (hdf J1) (hdf₀ J1₀)) (hasWeakCellDerivC_sub hdg hdg₀)
        refine key.trans ?_
        have hgb : xNorm c (-m) (jetExt c m k (D r) (j :: w) - jetExt c m k (D r₀) (j :: w)) ≤
            2 * ENNReal.ofReal M₁ :=
          (xNorm_sub_le hmg1 hmg2).trans (by rw [two_mul]; exact add_le_add (B1 _ hljw) (B1₀ _ hljw))
        have hhb : xNorm c (-m) (jetExt c m (k + 1) (jetExt c m k (D r)) (j :: j :: w) -
            jetExt c m (k + 1) (jetExt c m k (D r₀)) (j :: j :: w)) ≤ 2 * ENNReal.ofReal M₂ :=
          (xNorm_sub_le hmh1 hmh2).trans
            (by rw [two_mul]; exact add_le_add (B2 _ hljjw) (B2₀ _ hljjw))
        gcongr

/-- **`AdjHkStep` from its leaves** (`I = (t, s)`, closed neighbourhoods `[(t + r)/2, (r + s)/2]`). -/
theorem adjHkStep_of (m : ℝ) (hG : AdjHkGainOn m) (hI : CellInterp) (hU : WeakCellAeUnique)
    (hK : CompactJetBound) : AdjHkStep m := by
  intro ν hν hν1 tr hB hJ t s ht hts g φ hφ hD k hk
  refine adjHkStepOn_of hG hI hU hK hν hν1 hB hJ ht hts hφ hD (fun r hr => ?_) k hk
  refine ⟨(t + r) / 2, (r + s) / 2, by linarith [hr.1], by linarith [hr.1], by linarith [hr.2],
    by linarith [hr.2], ?_, ?_⟩
  · intro x hx
    exact ⟨by linarith [hx.1, hr.1], by linarith [hx.2, hr.2]⟩
  · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith [hr.1]) (by linarith [hr.2]))

/-- **`AdjHkStepEnd` from the same leaves** (`I = [t, s)`, closed neighbourhoods
`[t, (r + s)/2]`; the end-age form of `Sub/PartIII-a_T21_2_7_2_1_2.lean`). -/
theorem adjHkStepEnd_of (m : ℝ) (hG : AdjHkGainOn m) (hI : CellInterp) (hU : WeakCellAeUnique)
    (hK : CompactJetBound) : AdjHkStepEnd m := by
  intro ν hν hν1 tr hB hJ t s ht hts g φ hφ hD k hk
  refine adjHkStepOn_of hG hI hU hK hν hν1 hB hJ ht hts hφ hD (fun r hr => ?_) k hk
  refine ⟨t, (r + s) / 2, le_rfl, hr.1, by linarith [hr.2], by linarith [hr.2], ?_, ?_⟩
  · intro x hx
    exact ⟨hx.1, by linarith [hx.2, hr.2]⟩
  · have h1 : Iio ((r + s) / 2) ∈ 𝓝[Ico t s] r :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith [hr.2]))
    filter_upwards [self_mem_nhdsWithin, h1] with x hx1 hx2
    exact ⟨hx1.1, le_of_lt hx2⟩

end UnforcedLeray.Short.IIIa
