import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.SliceTaylor.Calc

/-!
# Part II-a, task `PartII-a:F02/9`, helper: uniform slice bounds, measurability and the
decomposition of `adjC` on a phase test.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.SliceCalc

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

theorem norm_clmGen_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (K : E₁ →L[ℝ] E₂) (hK : ‖K‖ ≤ 1) (x : E₁) : ‖K x‖ ≤ ‖x‖ :=
  (K.le_opNorm x).trans (by nlinarith [norm_nonneg x])

theorem eLpNorm_clm_le (K : Space →L[ℝ] CVec3) (hK : ‖K‖ ≤ 1) (X : Space → Space)
    (p : ℝ≥0∞) :
    eLpNorm (fun y => K (X y)) p volume ≤ eLpNorm X p volume := by
  calc eLpNorm (fun y => K (X y)) p volume ≤ eLpNorm (fun y => ‖X y‖) p volume :=
        eLpNorm_mono_real fun y => norm_clmGen_le K hK (X y)
    _ = eLpNorm X p volume := eLpNorm_norm X

/-- The real-valued transposed generator applied to a slice, as a function on space. -/
def Xk (ν s : ℝ) (K : CVec3 →L[ℝ] Space) (t : ℝ) (Φ : ℝ × Space → CVec3) (y : Space) : Space :=
  adjFree ν s (fun z => K (Φ (t, z))) y - K (Φ (t, y)) -
    s • adjGen ν (fun z => K (Φ (t, z))) y

theorem ofReV_smul_real (s : ℝ) (g : Space) : ofReV (s • g) = (s : ℂ) • ofReV g := by
  ext i
  simp [ofReV_apply]

theorem ofImV_smul_real (s : ℝ) (g : Space) : ofImV (s • g) = (s : ℂ) • ofImV g := by
  ext i
  simp [ofImV_apply]

theorem alg_decomp (a1 a2 u1 u2 g1 g2 : Space) (s : ℝ) :
    ofReV a1 + ofImV a2 - (ofReV u1 + ofImV u2) - (s : ℂ) • (ofReV g1 + ofImV g2) =
      ofReV (a1 - u1 - s • g1) + ofImV (a2 - u2 - s • g2) := by
  simp only [map_sub, ofReV_smul_real, ofImV_smul_real, smul_add]
  abel

theorem continuous_adjGen (ν : ℝ) {u : Space → Space} (hu : ContDiff ℝ ∞ u) :
    Continuous (adjGen ν u) := by
  unfold adjGen
  have hcL : Continuous (UnforcedLeray.B0418.vecLaplacian u) :=
    UnforcedLeray.B0418.continuous_vecLaplacian hu
  have hcD : Continuous (fun y : Space => fderiv ℝ u y y) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_id
  have hc1 : Continuous (fun y : Space => ν • UnforcedLeray.B0418.vecLaplacian u y) :=
    hcL.const_smul ν
  have hc2 : Continuous (fun y : Space => (1 / 2 : ℝ) • fderiv ℝ u y y) :=
    hcD.const_smul (1 / 2 : ℝ)
  exact (hc1.sub hc2).sub hu.continuous

theorem measurable_adjFree {u : Space → Space} (hu : Continuous u) (ν s : ℝ) :
    Measurable (adjFree ν s u) := by
  have h1 := UnforcedLeray.B0418.measurable_flow_uncurry hu
  have h2 : Measurable (fun y : Space => (Real.exp (-s / 2) • y, ν * (1 - Real.exp (-s)))) :=
    (measurable_const_smul _).prodMk measurable_const
  have h3 : Measurable (fun y : Space =>
      UnforcedLeray.Heat.flow u (ν * (1 - Real.exp (-s))) (Real.exp (-s / 2) • y)) :=
    h1.comp h2
  exact h3.const_smul (Real.exp (-s))

theorem adjGen_clm (ν : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (K : CVec3 →L[ℝ] Space) (t : ℝ) (y : Space) :
    K (F02.genT ν Φ (t, y)) = adjGen ν (fun z => K (Φ (t, z))) y := by
  have hL := vecLaplacian_clm_slice hΦ K t y
  have hR := fderiv_clm_slice_self (hΦ.differentiable (by simp)) K t y
  unfold adjGen F02.genT
  simp only [nuLapT, Pi.sub_apply, Pi.smul_apply, map_sub, map_smul, hL, hR]

theorem measurable_Xk (ν s : ℝ) (K : CVec3 →L[ℝ] Space) (t : ℝ) {Φ : ℝ × Space → CVec3}
    (hΦ : ContDiff ℝ ∞ Φ) : Measurable (Xk ν s K t Φ) := by
  have hu : ContDiff ℝ ∞ (fun z : Space => K (Φ (t, z))) :=
    K.contDiff.comp (hΦ.comp (contDiff_const.prodMk contDiff_id))
  have hcu : Continuous (fun z : Space => K (Φ (t, z))) := hu.continuous
  have h1 := measurable_adjFree hcu ν s
  have h2 : Measurable (fun y : Space => K (Φ (t, y))) := hcu.measurable
  have h3 : Measurable (fun y : Space => s • adjGen ν (fun z => K (Φ (t, z))) y) :=
    (continuous_adjGen ν hu).measurable.const_smul s
  unfold Xk
  exact (h1.sub h2).sub h3

theorem decomp_adjC (ν s t : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (y : Space) :
    adjC ν s (fun z => Φ (t, z)) y - Φ (t, y) - (s : ℂ) • F02.genT ν Φ (t, y) =
      ofReV (Xk ν s reV t Φ y) + ofImV (Xk ν s imV t Φ y) := by
  have e1 := ofReV_reV_add_ofImV_imV (Φ (t, y))
  have e2 := ofReV_reV_add_ofImV_imV (F02.genT ν Φ (t, y))
  have g1 := adjGen_clm ν hΦ reV t y
  have g2 := adjGen_clm ν hΦ imV t y
  unfold adjC Xk
  conv_lhs => rw [← e1, ← e2]
  rw [g1, g2]
  exact alg_decomp _ _ _ _ _ _ s

theorem exists_uniform_bound {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K : CVec3 →L[ℝ] Space, ‖K‖ ≤ 1 → ∀ t : ℝ, ∀ y : Space,
      ‖K (Φ (t, y))‖ ≤ M ∧
      ‖fderiv ℝ (fun z : Space => K (Φ (t, z))) y‖ ≤ M ∧
      ‖fderiv ℝ (fderiv ℝ (fun z : Space => K (Φ (t, z)))) y‖ ≤ M ∧
      ‖UnforcedLeray.B0418.vecLaplacian (fun z : Space => K (Φ (t, z))) y‖ ≤ M ∧
      ‖fderiv ℝ (UnforcedLeray.B0418.vecLaplacian (fun z : Space => K (Φ (t, z)))) y‖ ≤ M ∧
      ‖UnforcedLeray.B0418.vecLaplacian
        (UnforcedLeray.B0418.vecLaplacian (fun z : Space => K (Φ (t, z)))) y‖ ≤ M := by
  obtain ⟨A, hA0, hA⟩ := F02.exists_bound_of_phaseTest hΦ
  have hB : ∀ j : Fin 3, ∃ c : ℝ, 0 ≤ c ∧ ∀ p : ℝ × Space, ‖PhaseSpace.dy j Φ p‖ ≤ c :=
    fun j => F02.exists_bound_of_phaseTest (hΦ.dy j)
  choose B hB0 hBb using hB
  have hC : ∀ j k : Fin 3, ∃ c : ℝ, 0 ≤ c ∧
      ∀ p : ℝ × Space, ‖PhaseSpace.dy j (PhaseSpace.dy k Φ) p‖ ≤ c :=
    fun j k => F02.exists_bound_of_phaseTest ((hΦ.dy k).dy j)
  choose C hC0 hCb using hC
  obtain ⟨D, hD0, hD⟩ := F02.exists_bound_of_phaseTest hΦ.lapT
  have hE : ∀ j : Fin 3, ∃ c : ℝ, 0 ≤ c ∧
      ∀ p : ℝ × Space, ‖PhaseSpace.dy j (PhaseSpace.lapT Φ) p‖ ≤ c :=
    fun j => F02.exists_bound_of_phaseTest (hΦ.lapT.dy j)
  choose E hE0 hEb using hE
  obtain ⟨Fb, hF0, hF⟩ := F02.exists_bound_of_phaseTest hΦ.lapT.lapT
  have sB : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun j _ => hB0 j
  have sC : 0 ≤ ∑ j, ∑ k, C j k :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hC0 j k
  have sE : 0 ≤ ∑ j, E j := Finset.sum_nonneg fun j _ => hE0 j
  refine ⟨A + (∑ j, B j) + (∑ j, ∑ k, C j k) + D + (∑ j, E j) + Fb, by linarith,
    fun K hK t y => ?_⟩
  have hs := hΦ.smooth
  have hV : UnforcedLeray.B0418.vecLaplacian (fun z : Space => K (Φ (t, z))) =
      fun z => K (PhaseSpace.lapT Φ (t, z)) :=
    funext fun z => vecLaplacian_clm_slice hs K t z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := norm_clmGen_le K hK (Φ (t, y))
    have h2 := hA (t, y)
    linarith
  · refine (norm_fderiv_slice_le hs K hK t y).trans ?_
    have h3 : ∑ j : Fin 3, ‖PhaseSpace.dy j Φ (t, y)‖ ≤ ∑ j, B j :=
      Finset.sum_le_sum fun j _ => hBb j (t, y)
    linarith
  · refine (norm_fderiv_fderiv_slice_le hs K hK t y).trans ?_
    have h3 : ∑ j : Fin 3, ∑ k : Fin 3, ‖PhaseSpace.dy j (PhaseSpace.dy k Φ) (t, y)‖ ≤
        ∑ j, ∑ k, C j k :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hCb j k (t, y)
    linarith
  · rw [vecLaplacian_clm_slice hs K t y]
    have h4 := hD (t, y)
    have h5 := norm_clmGen_le K hK (PhaseSpace.lapT Φ (t, y))
    linarith
  · rw [hV]
    refine (norm_fderiv_slice_le hΦ.lapT.smooth K hK t y).trans ?_
    have h3 : ∑ j : Fin 3, ‖PhaseSpace.dy j (PhaseSpace.lapT Φ) (t, y)‖ ≤ ∑ j, E j :=
      Finset.sum_le_sum fun j _ => hEb j (t, y)
    linarith
  · rw [hV, vecLaplacian_clm_slice hΦ.lapT.smooth K t y]
    have h4 := hF (t, y)
    have h5 := norm_clmGen_le K hK (PhaseSpace.lapT (PhaseSpace.lapT Φ) (t, y))
    linarith

end UnforcedLeray.Short.PartIIa.SliceCalc
