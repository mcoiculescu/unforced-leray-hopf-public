import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org

/-!
# `PartIII-b:IIIb-D3/2/G6/4`: `ℓ_μ` reads its stress only on the old region

Source of record: `the November 2 reference manuscript`, lines 4584-4587 and
4766-4770.  `χ_o = 0` on `(-∞, 6/5]` (`IsOutwardCutoff.zero`), so `ellMuAt` only depends on the
class of `M` for `du × dq/c dη` on `u > 6/5/ν` (`oldMeasure`).
-/

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

open ConcreteYF

/-- The cell integral only sees the class of `F` for the averaged cell measure. -/
lemma cellInt_congr_of_ae_avg {c : ℝ} (hc : 0 < c) (F G : ℝ × ℝ → ℝ)
    (h : ∀ᵐ p ∂(Cyl.avgμ c), F p = G p) : cellInt c F = cellInt c G := by
  unfold cellInt
  congr 1
  have hc0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have h1 : ∀ᵐ p ∂(volume.restrict (Cyl.cell c)), F p = G p := by
    unfold Cyl.avgμ Cyl.cellμ at h
    exact (Measure.ae_ennreal_smul_measure_iff hc0).1 h
  have hS : (Ioo (-c / 2) (c / 2)) ×ˢ (univ : Set ℝ) ⊆ Cyl.cell c :=
    Set.prod_mono Ioo_subset_Ico_self subset_rfl
  have h2 : ∀ᵐ p ∂(volume.restrict ((Ioo (-c / 2) (c / 2)) ×ˢ (univ : Set ℝ))), F p = G p :=
    ae_restrict_of_ae_restrict_of_subset hS h1
  exact setIntegral_congr_ae ((measurableSet_Ioo).prod MeasurableSet.univ)
    ((ae_restrict_iff' ((measurableSet_Ioo).prod MeasurableSet.univ)).1 h2)

/-- The outer integral of `ℓ_μ` for two stresses that agree a.e. on the old region. -/
lemma oldInt_congr {ν : ℝ} (χ : ℝ → ℝ) (hχ : ∀ t, t ≤ 6 / 5 → χ t = 0)
    (M M' : Chart → Mat3) (h : M =ᵐ[oldMeasure (cOf ν) ν] M') :
    ∫ s in Ioi (0 : ℝ), χ (ν * s) * s ^ (-(3 / 2 : ℝ)) *
        cellInt (cOf ν) (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0)
      = ∫ s in Ioi (0 : ℝ), χ (ν * s) * s ^ (-(3 / 2 : ℝ)) *
        cellInt (cOf ν) (fun p => 2 * M' (s, p) 2 2 - M' (s, p) 0 0) := by
  by_cases hν : 0 < ν
  · have hc : 0 < cOf ν := by
      unfold cOf
      exact inv_pos.2 (pow_pos hν 2)
    have hae : ∀ᵐ s ∂(volume.restrict (Ioi (6 / 5 / ν))),
        ∀ᵐ p ∂(Cyl.avgμ (cOf ν)), M (s, p) = M' (s, p) := by
      unfold oldMeasure at h
      exact Measure.ae_ae_of_ae_prod h
    have hae2 : ∀ᵐ s ∂volume, s ∈ Ioi (6 / 5 / ν) →
        ∀ᵐ p ∂(Cyl.avgμ (cOf ν)), M (s, p) = M' (s, p) :=
      (ae_restrict_iff' measurableSet_Ioi).1 hae
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [hae2] with s hs hs0
    by_cases hs1 : s ∈ Ioi (6 / 5 / ν)
    · have key := cellInt_congr_of_ae_avg hc (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0)
        (fun p => 2 * M' (s, p) 2 2 - M' (s, p) 0 0)
        (by
          filter_upwards [hs hs1] with p hp
          simp only [hp])
      rw [key]
    · rw [Set.mem_Ioi, not_lt] at hs1
      have hχs : χ (ν * s) = 0 := by
        apply hχ
        have := (le_div_iff₀ hν).1 hs1
        rw [mul_comm]
        exact this
      simp [hχs]
  · have hz : ∀ s ∈ Ioi (0 : ℝ), χ (ν * s) = 0 := by
      intro s hs
      apply hχ
      have hs' : (0 : ℝ) < s := hs
      have hν' : ν ≤ 0 := not_lt.1 hν
      nlinarith [mul_nonneg (neg_nonneg.2 hν') hs'.le]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp [hz s hs]

/-- **`ℓ_μ` reads its stress only on the old region** (source 4584-4587, 4766-4770). -/
theorem ellMuAtCongr : FlatUnif.G6.EllMuAtCongr := by
  intro D n μ M M' h
  unfold ellMuAt
  rw [oldInt_congr D.K.χo D.K.hχo.zero M M' h]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
