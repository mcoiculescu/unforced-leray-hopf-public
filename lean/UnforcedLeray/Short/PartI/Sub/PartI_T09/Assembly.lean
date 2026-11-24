import UnforcedLeray.Short.PartI.Sub.PartI_T09

/-!
# `PartI:T09`: assembly of `TrainComparison` from the leaves of `Sub/PartI_T09.lean`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

theorem train_comparison_of
    (h8 : DifferentiatedEnergyInequality) (h0 : TrainErrBasic)
    (h1 : ComparisonGronwall) (h2 : BootstrapContinuity)
    (h3a : JetL2Bridge) (h3b : JetSupBridge)
    (h4 : TrainErrInitial) (h4c : TrainErrGradSup)
    (h5 : TrainPeriodAsymptotics) (h6 : JetArithmetic) (h7 : GradClosing) :
    TrainComparison := by
  intro ρ hρ j
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = j + 3 := ⟨_, rfl⟩
  have hN3 : 3 ≤ N := by omega
  obtain ⟨CT, bT, hCT, hbT, hT⟩ := h8 N hN3
  obtain ⟨K, b', R, hK, hb', hR, hGr⟩ := h1 CT bT hCT hbT
  obtain ⟨Cj, hCj, hAr⟩ := h6 N j K b' hN3 (by omega) hK hb'
  obtain ⟨C1, hC1, hAr1⟩ := h6 N 1 K b' hN3 (by omega) hK hb'
  obtain ⟨Ca, hCa0, hCa⟩ := h3a j
  obtain ⟨Cb, hCb0, hCb⟩ := h3b j
  obtain ⟨Cb1, hCb10, hCb1⟩ := h3b 1
  obtain ⟨R2, hR2, hCl⟩ := h7 (Cb1 * C1 + 1) (b' / 2) (by positivity) (by positivity)
  obtain ⟨ν1, hν1, hν11, hper⟩ := h5 ρ hρ (max R R2) (lt_max_of_lt_left hR)
  refine ⟨Ca * Cj + Cb * Cj + 1, b' / 2, ν1, by positivity, by positivity, hν1, ?_⟩
  intro ν hν hνν1 tr htr s hs hsc
  obtain ⟨hc1, hRc⟩ := hper ν hν hνν1
  have hν1' : ν ≤ 1 := hνν1.trans hν11
  have main : ∀ c : ℝ, 1 ≤ c → max R R2 ≤ ν * c ^ 2 → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
      ∀ s : ℝ, 0 ≤ s → width ν s ≤ c ^ 2 →
        Train.cellL2 c (Train.jet j (trainErr tr s)) ≤
          ENNReal.ofReal ((Ca * Cj + Cb * Cj + 1) * ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
            Real.exp (-(b' / 2 * c ^ 2 / width ν s))) ∧
        B0277.supNormD j (trainErr tr s) ≤
          ENNReal.ofReal ((Ca * Cj + Cb * Cj + 1) * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
            Real.exp (-(b' / 2 * c ^ 2 / width ν s))) := by
    intro c hc1 hRc tr htr s hs hsc
    have hc0 : 0 < c := by linarith
    have hRc1 : R ≤ ν * c ^ 2 := (le_max_left _ _).trans hRc
    have hRc2 : R2 ≤ ν * c ^ 2 := (le_max_right _ _).trans hRc
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (4 * (N : ℝ)) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hwpos : ∀ r : ℝ, 0 ≤ r → 0 < width ν r := fun r hr => Train.width_pos hν.le hr
    have hw1 : ∀ r : ℝ, 0 ≤ r → 1 ≤ width ν r := fun r hr => by
      simp only [Train.width]; nlinarith
    have hwmono : ∀ r r' : ℝ, r ≤ r' → width ν r ≤ width ν r' := fun r r' h => by
      simp only [Train.width]; nlinarith
    obtain ⟨hbdd, hg0, hgc⟩ := h4c ν c hν hc1 tr htr
    obtain ⟨hI0, hIc, hI2⟩ := h4 ν c hν hc1 tr htr
    have entries : ∀ r : ℝ, 0 ≤ r → ∀ B : ℝ, gradErrSup tr r ≤ B →
        ∀ (β : Bool) (k : Fin 2) (z : Plane), |wordComp [β] (trainErr tr r) k z| ≤ B :=
      fun r hr B hB β k z => (le_csSup (hbdd r hr) ⟨β, k, z, rfl⟩).trans hB
    -- the T08 package at a good age
    have hTr : ∀ r : ℝ, 0 < r → width ν r ≤ c ^ 2 →
        (∀ (β : Bool) (k : Fin 2) (z : Plane),
          |wordComp [β] (trainErr tr r) k z| ≤ (width ν r ^ 2)⁻¹) →
        (∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (trainErr tr r) k) 2 (Cyl.cellμ c)) ∧
        ∃ D : ℝ, HasDerivAt (fun r => weightedEnergy c δ (width ν r) N (trainErr tr r)) D r ∧
          ν⁻¹ * D + weightedDissipation c δ (width ν r) N (trainErr tr r) ≤
            CT / (ν * width ν r ^ 2) * weightedEnergy c δ (width ν r) N (trainErr tr r) +
              CT / (ν ^ 2 * width ν r ^ 5) * Real.exp (-(bT * c ^ 2 / width ν r)) :=
      fun r hr hrc hb => hT ν c δ hν hν1' hc1 hδpos (by rw [hδdef]) tr htr r hr hrc hb
    -- the energy bound under the bootstrap hypothesis on `[0, S]`
    have key : ∀ S : ℝ, 0 ≤ S → width ν S ≤ c ^ 2 →
        (∀ r ∈ Icc 0 S, ∀ (β : Bool) (k : Fin 2) (z : Plane),
          |wordComp [β] (trainErr tr r) k z| ≤ (width ν r ^ 2)⁻¹) →
        ∀ r ∈ Icc 0 S, weightedEnergy c δ (width ν r) N (trainErr tr r) ≤
          K / (ν ^ 2 * width ν r ^ 4) * Real.exp (-(b' * c ^ 2 / width ν r)) := by
      intro S hS hSc hboot
      refine hGr ν c S hν hc1 hRc1 hS hSc _ ?_ ?_ ?_
      · intro r hr
        rcases eq_or_lt_of_le hr.1 with h0r | hpos
        · subst h0r
          exact (hIc N δ).mono Icc_subset_Ici_self
        · obtain ⟨-, D, hD, -⟩ := hTr r hpos ((hwmono r S hr.2).trans hSc) (hboot r hr)
          exact hD.continuousAt.continuousWithinAt
      · simp [weightedEnergy, hI0]
      · intro r hr
        have hrI : r ∈ Icc 0 S := ⟨hr.1.le, hr.2.le⟩
        obtain ⟨-, D, hD, hineq⟩ := hTr r hr.1 ((hwmono r S hr.2.le).trans hSc) (hboot r hrI)
        refine ⟨D, hD, ?_⟩
        have hdis : 0 ≤ weightedDissipation c δ (width ν r) N (trainErr tr r) :=
          Finset.sum_nonneg fun i _ =>
            mul_nonneg (pow_nonneg (mul_nonneg hδpos.le (hwpos r hr.1.le).le) _)
              (jetEnergy_nonneg c _ _)
        linarith
    -- cell regularity of the error
    have cellsm : ∀ r : ℝ, 0 ≤ r → width ν r ≤ c ^ 2 →
        (∀ (β : Bool) (k : Fin 2) (z : Plane),
          |wordComp [β] (trainErr tr r) k z| ≤ (width ν r ^ 2)⁻¹) →
        CellSmoothL2 c (trainErr tr r) := by
      intro r hr hrc hb
      rcases eq_or_lt_of_le hr with h0r | hpos
      · subst h0r; exact hI2
      · obtain ⟨hes, hep, -⟩ := h0 ν c hν hc1 tr htr r hpos hrc
        exact ⟨hes, hep, (hTr r hpos hrc hb).1⟩
    -- the consequences of the energy bound at one age
    have conseq : ∀ r : ℝ, 0 ≤ r → width ν r ≤ c ^ 2 →
        weightedEnergy c δ (width ν r) N (trainErr tr r) ≤
          K / (ν ^ 2 * width ν r ^ 4) * Real.exp (-(b' * c ^ 2 / width ν r)) →
        ∀ i : ℕ, i ≤ N → (1 / (4 * (N : ℝ)) * width ν r) ^ i * jetEnergy c i (trainErr tr r) ≤
          weightedEnergy c δ (width ν r) N (trainErr tr r) := by
      intro r hr hrc hE i hi
      rw [← hδdef]
      unfold weightedEnergy
      exact Finset.single_le_sum (f := fun i => (δ * width ν r) ^ i * jetEnergy c i (trainErr tr r))
        (fun i _ => mul_nonneg (pow_nonneg (mul_nonneg hδpos.le (hwpos r hr).le) _)
          (jetEnergy_nonneg c _ _)) (Finset.mem_range.2 (by omega))
    -- the gradient step of the bootstrap
    have step : ∀ r : ℝ, 0 ≤ r → width ν r ≤ c ^ 2 →
        (∀ r' ∈ Icc 0 r, gradErrSup tr r' ≤ (width ν r' ^ 2)⁻¹) →
        gradErrSup tr r ≤ (width ν r ^ 2)⁻¹ / 2 := by
      intro r hr hrc hg
      have hwr := hwpos r hr
      have hboot : ∀ r' ∈ Icc 0 r, ∀ (β : Bool) (k : Fin 2) (z : Plane),
          |wordComp [β] (trainErr tr r') k z| ≤ (width ν r' ^ 2)⁻¹ :=
        fun r' hr' => entries r' hr'.1 _ (hg r' hr')
      have hE := key r hr hrc hboot r ⟨hr, le_rfl⟩
      have hJ := conseq r hr hrc hE
      have hcs := cellsm r hr hrc (hboot r ⟨hr, le_rfl⟩)
      obtain ⟨-, hS1⟩ := hAr1 ν c (width ν r) _ hν hc1 (hw1 r hr) hrc
        (fun i => jetEnergy c i (trainErr tr r)) (fun i => jetEnergy_nonneg c i _) hE hJ
      have hent := (hCb1 c hc1 _ hcs).1 [true] rfl
      have hpos : 0 < ν⁻¹ * width ν r ^ (-((5 + ((1 : ℕ) : ℝ)) / 2)) *
          Real.exp (-(b' / 2 * c ^ 2 / width ν r)) := by positivity
      have hcl := hCl ν c (width ν r) hν (hw1 r hr) hrc (hRc2)
      have hrw : (width ν r) ^ (-((5 + ((1 : ℕ) : ℝ)) / 2)) = width ν r ^ (-(3 : ℝ)) := by
        norm_num
      rw [hrw] at hS1 hpos
      have hb : ∀ (β : Bool) (k : Fin 2) (z : Plane),
          |wordComp [β] (trainErr tr r) k z| ≤ (width ν r ^ 2)⁻¹ / 2 := by
        intro β k z
        have h1' := (hCb1 c hc1 _ hcs).1 [β] rfl k z
        unfold supRhs at h1'
        refine h1'.trans ?_
        refine le_trans ?_ hcl
        calc _ ≤ Cb1 * (C1 * ν⁻¹ * width ν r ^ (-(3 : ℝ)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν r))) :=
              mul_le_mul_of_nonneg_left hS1 hCb10
          _ = (Cb1 * C1) * (ν⁻¹ * width ν r ^ (-(3 : ℝ)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν r))) := by ring
          _ ≤ (Cb1 * C1 + 1) * (ν⁻¹ * width ν r ^ (-(3 : ℝ)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν r))) :=
              mul_le_mul_of_nonneg_right (by linarith) hpos.le
          _ = _ := by ring
      exact csSup_le ⟨_, true, 0, 0, rfl⟩ (by
        rintro x ⟨β, k, z, rfl⟩; exact hb β k z)
    -- the bootstrap closes on `[0, s]`
    have hhc : ContinuousOn (fun r => (width ν r ^ 2)⁻¹) (Icc 0 s) := by
      refine ContinuousOn.inv₀ (Continuous.continuousOn ?_) (fun r hr => ?_)
      · simp only [Train.width]; fun_prop
      · exact (pow_pos (hwpos r hr.1) 2).ne'
    have hgood := h2 s hs (gradErrSup tr) (fun r => (width ν r ^ 2)⁻¹)
      (hgc.mono Icc_subset_Ici_self) hhc
      (fun r hr => inv_pos.2 (pow_pos (hwpos r hr.1) 2))
      (by rw [hg0]; exact (inv_pos.2 (pow_pos (hwpos 0 le_rfl) 2)).le)
      (fun r hr hh => step r hr.1 ((hwmono r s hr.2).trans hsc) hh)
    have hgood' : ∀ r ∈ Icc 0 s, gradErrSup tr r ≤ (width ν r ^ 2)⁻¹ := fun r hr =>
      (hgood r hr).trans (by
        have := inv_pos.2 (pow_pos (hwpos r hr.1) 2); linarith)
    have hboot : ∀ r ∈ Icc 0 s, ∀ (β : Bool) (k : Fin 2) (z : Plane),
        |wordComp [β] (trainErr tr r) k z| ≤ (width ν r ^ 2)⁻¹ :=
      fun r hr => entries r hr.1 _ (hgood' r hr)
    have hE := key s hs hsc hboot s ⟨hs, le_rfl⟩
    have hJ := conseq s hs hsc hE
    have hcs := cellsm s hs hsc (hboot s ⟨hs, le_rfl⟩)
    have hws := hwpos s hs
    obtain ⟨hS0, hS2⟩ := hAr ν c (width ν s) _ hν hc1 (hw1 s hs) hsc
      (fun i => jetEnergy c i (trainErr tr s)) (fun i => jetEnergy_nonneg c i _) hE hJ
    have hpos2 : 0 ≤ ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
        Real.exp (-(b' / 2 * c ^ 2 / width ν s)) := by positivity
    have hpos3 : 0 ≤ ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
        Real.exp (-(b' / 2 * c ^ 2 / width ν s)) := by positivity
    constructor
    · refine (hCa c hc1 _ hcs).trans (ENNReal.ofReal_le_ofReal ?_)
      calc Ca * Real.sqrt (jetEnergy c j (trainErr tr s))
          ≤ Ca * (Cj * ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν s))) :=
            mul_le_mul_of_nonneg_left hS0 hCa0
        _ = (Ca * Cj) * (ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν s))) := by ring
        _ ≤ (Ca * Cj + Cb * Cj + 1) * (ν⁻¹ * width ν s ^ (-(2 + (j : ℝ) / 2)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν s))) :=
            mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCb0 hCj.le]) hpos2
        _ = _ := by ring
    · refine (hCb c hc1 _ hcs).2.trans (ENNReal.ofReal_le_ofReal ?_)
      unfold supRhs
      calc Cb * ((Real.sqrt (jetEnergy c j (trainErr tr s)) *
              Real.sqrt (jetEnergy c (j + 2) (trainErr tr s))) ^ (1 / 2 : ℝ) +
            c ^ (-(1 / 2 : ℝ)) * (Real.sqrt (jetEnergy c j (trainErr tr s)) *
              Real.sqrt (jetEnergy c (j + 1) (trainErr tr s))) ^ (1 / 2 : ℝ))
          ≤ Cb * (Cj * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν s))) :=
            mul_le_mul_of_nonneg_left hS2 hCb0
        _ = (Cb * Cj) * (ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν s))) := by ring
        _ ≤ (Ca * Cj + Cb * Cj + 1) * (ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(b' / 2 * c ^ 2 / width ν s))) :=
            mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCa0 hCj.le]) hpos3
        _ = _ := by ring
  exact main (trainPeriod ρ ν) hc1 hRc tr htr s hs hsc

end UnforcedLeray.Short.PartI
