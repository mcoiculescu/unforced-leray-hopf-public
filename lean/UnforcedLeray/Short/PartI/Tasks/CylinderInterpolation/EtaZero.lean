import UnforcedLeray.Short.PartI.Sub.T07

/-!
# Part I, task `PartI:T07`, target `CylCellEtaZero`: `η`-integration by parts on the cell

Source of record: `the November 2 reference manuscript`, lines 355-357 (the
period-independent integration by parts). Proves the Prop `UnforcedLeray.Short.PartI.CylCellEtaZero`
of `Sub/T07.lean` exactly as stated.

Route:
* Fubini on the cell with the `η`-integral inside (`Cyl.cellμ_eq_prod`, `integral_prod`).
* For almost every `q`, the slice `η ↦ H (q, η)` lies in `L^x(ℝ)` (`integrable_norm_rpow_iff`,
  from `Integrable.prod_right_ae` applied to `‖H‖^x`) and has integrable derivative
  `η ↦ ∂_η H (q, η)` (`Integrable.prod_right_ae` applied to `∂_η H`).
* One-dimensional lemma `cylEtaZero_oneD`: a `C¹` function on `ℝ` with integrable derivative and
  `L^x` norm (`0 < x < ∞`) has integral-zero derivative. The limits at `±∞` exist
  (`tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi/Iic`), and they vanish because `‖φ‖^x` is
  integrable on a set of infinite measure (`IntegrableAtFilter.eq_zero_of_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Helper 1: limits of integrable powers vanish -/

/-- Every set in `atTop` has infinite Lebesgue measure. -/
theorem cylEtaZero_volume_eq_top_atTop {s : Set ℝ} (hs : s ∈ atTop) : volume s = ⊤ := by
  obtain ⟨a, ha⟩ := mem_atTop_sets.1 hs
  have h : volume (Ici a) ≤ volume s := measure_mono (fun b (hb : b ∈ Ici a) => ha b hb)
  rw [Real.volume_Ici] at h
  exact top_le_iff.1 h

/-- Every set in `atBot` has infinite Lebesgue measure. -/
theorem cylEtaZero_volume_eq_top_atBot {s : Set ℝ} (hs : s ∈ atBot) : volume s = ⊤ := by
  obtain ⟨a, ha⟩ := mem_atBot_sets.1 hs
  have h : volume (Iic a) ≤ volume s := measure_mono (fun b (hb : b ∈ Iic a) => ha b hb)
  rw [Real.volume_Iic] at h
  exact top_le_iff.1 h

/-- A limit `ℓ` of `φ` along a filter `l` that only sees sets of infinite measure is zero, when
`‖φ‖^p` is integrable. -/
theorem cylEtaZero_limit_eq_zero {l : Filter ℝ} (hl : ∀ s ∈ l, volume s = ⊤) {φ : ℝ → ℝ}
    {p ℓ : ℝ} (hp : 0 < p) (hg : Integrable (fun η => ‖φ η‖ ^ p) volume)
    (hφ : Tendsto φ l (𝓝 ℓ)) : ℓ = 0 := by
  have h1 : Tendsto (fun η => ‖φ η‖ ^ p) l (𝓝 (‖ℓ‖ ^ p)) :=
    hφ.norm.rpow_const (Or.inr hp.le)
  have hI : IntegrableAtFilter (fun η => ‖φ η‖ ^ p) l volume :=
    ⟨Set.univ, Filter.univ_mem, hg.integrableOn⟩
  have h2 : ‖ℓ‖ ^ p = 0 := IntegrableAtFilter.eq_zero_of_tendsto hI hl h1
  have h3 : ‖ℓ‖ = 0 := ((Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg ℓ)).1 h2).1
  exact norm_eq_zero.1 h3

/-! ### Helper 2: the one-dimensional integration by parts -/

/-- **One-dimensional lemma.** If `φ` has derivative `φ'` everywhere on `ℝ`, `φ'` is integrable,
and `φ ∈ L^x(ℝ)` for some `0 < x < ∞`, then `∫ φ' = 0`. -/
theorem cylEtaZero_oneD {φ φ' : ℝ → ℝ} (hd : ∀ η, HasDerivAt φ (φ' η) η) (hi : Integrable φ')
    {x : ℝ≥0∞} (hx0 : x ≠ 0) (hxtop : x ≠ ⊤) (hφ : MemLp φ x volume) :
    ∫ η, φ' η = 0 := by
  have hp : 0 < x.toReal := ENNReal.toReal_pos hx0 hxtop
  have hg : Integrable (fun η => ‖φ η‖ ^ x.toReal) volume := hφ.integrable_norm_rpow hx0 hxtop
  have hA : Tendsto φ atTop (𝓝 (limUnder atTop φ)) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun η _ => hd η) hi.integrableOn
  have hB : Tendsto φ atBot (𝓝 (limUnder atBot φ)) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun η _ => hd η) hi.integrableOn
  have hn : limUnder atTop φ = 0 :=
    cylEtaZero_limit_eq_zero (fun s hs => cylEtaZero_volume_eq_top_atTop hs) hp hg hA
  have hm : limUnder atBot φ = 0 :=
    cylEtaZero_limit_eq_zero (fun s hs => cylEtaZero_volume_eq_top_atBot hs) hp hg hB
  have key := integral_of_hasDerivAt_of_tendsto hd hi hB hA
  rw [hn, hm, sub_zero] at key
  exact key

/-! ### The target -/

/-- **`PartI:T07`, `CylCellEtaZero`.** For `c > 0`, a `C¹` function `H` on the plane with
`H ∈ L^x(cell c)` for some `0 < x < ∞` and `∂_η H ∈ L¹(cell c)` has `∫_cell ∂_η H = 0`. -/
theorem cylCellEtaZero_proof : UnforcedLeray.Short.PartI.CylCellEtaZero := by
  intro c _hc H hH x hx0 hxtop hHx hint
  have hx0' : x ≠ 0 := hx0.ne'
  have hdiff : Differentiable ℝ H := hH.differentiable (by simp)
  have hcont : Continuous H := hH.continuous
  have hG : Integrable (fun z => ‖H z‖ ^ x.toReal)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) := by
    rw [← Cyl.cellμ_eq_prod c]
    exact hHx.integrable_norm_rpow hx0' hxtop
  have hD : Integrable (Cyl.partialEta H)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ)) := by
    rw [← Cyl.cellμ_eq_prod c]
    exact hint
  rw [Cyl.cellμ_eq_prod c, integral_prod _ hD]
  have h0 : ∀ᵐ q ∂(volume.restrict (Ico (-c / 2) (c / 2))),
      ∫ η, Cyl.partialEta H (q, η) = 0 := by
    filter_upwards [hG.prod_right_ae, hD.prod_right_ae] with q hGq hDq
    have hqc : Continuous fun η : ℝ => ((q, η) : ℝ × ℝ) := by fun_prop
    have hcq : Continuous (fun η : ℝ => H (q, η)) := hcont.comp hqc
    have hφ : MemLp (fun η : ℝ => H (q, η)) x volume :=
      (integrable_norm_rpow_iff hcq.aestronglyMeasurable hx0' hxtop).1 hGq
    have hsl : ∀ η : ℝ, HasDerivAt (fun η' : ℝ => H (q, η')) (Cyl.partialEta H (q, η)) η := by
      intro η
      have h1 : DifferentiableAt ℝ (fun η' : ℝ => H (q, η')) η :=
        (hdiff (q, η)).comp η ((differentiableAt_const q).prodMk differentiableAt_id)
      exact h1.hasDerivAt
    exact cylEtaZero_oneD (φ := fun η : ℝ => H (q, η))
      (φ' := fun η : ℝ => Cyl.partialEta H (q, η)) hsl hDq hx0' hxtop hφ
  exact integral_eq_zero_of_ae h0

end UnforcedLeray.Short.PartI
