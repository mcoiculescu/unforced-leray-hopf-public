import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.PrimInt3

/-!
# `primInt_main`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem primInt_main {A : Space → ℝ} (hA : ContDiff ℝ 2 A) (w : Space) {K ρ₀ δ : ℝ} (hK : 0 ≤ K)
    (hρ₀ : 0 ≤ ρ₀) (hδ : 0 < δ) (hw : w 0 ≤ ρ₀)
    (b0 : ∀ x : Space, x ≠ 0 → |A x| ≤ K * (‖x‖ ^ 4)⁻¹)
    (b1 : ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 1 A x‖ ≤ K * (‖x‖ ^ 5)⁻¹)
    (b2 : ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 2 A x‖ ≤ K * (‖x‖ ^ 6)⁻¹) :
    ContDiffOn ℝ 2 (primInt A w) {q : Space | ρ₀ + δ < q 0} ∧
    ∀ q : Space, ρ₀ + δ < q 0 →
      ‖iteratedFDeriv ℝ 0 (primInt A w) q‖ ≤
        primCp ρ₀ δ * K * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - w 2) ^ 2))) ∧
      ‖iteratedFDeriv ℝ 1 (primInt A w) q‖ ≤
        primCp ρ₀ δ * K * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - w 2) ^ 2))) ∧
      ‖iteratedFDeriv ℝ 2 (primInt A w) q‖ ≤
        primCp ρ₀ δ * K * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - w 2) ^ 2))) := by
  set U : Set Space := {q : Space | ρ₀ + δ < q 0} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const
    ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous)
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F : Space → ℝ → ℝ := fun q u => primF A w q u with hF
  set F1 : Space → ℝ → (Space →L[ℝ] ℝ) := fun q u => fderiv ℝ (fun q' => primF A w q' u) q with hF1
  set F2 : Space → ℝ → (Space →L[ℝ] Space →L[ℝ] ℝ) :=
    fun q u => fderiv ℝ (fun q' => fderiv ℝ (fun q'' => primF A w q'' u) q') q with hF2
  set Cp := primCp ρ₀ δ with hCp
  have hCp0 : 0 ≤ Cp := primCp_nonneg hρ₀ hδ
  -- the crude majorant
  have hJ0 := primJ2 hδ 0
  set Bm : ℝ → ℝ := fun u => Cp * K * ((δ + u) * (((δ + u) ^ 2 + 0 ^ 2) ^ 2)⁻¹) with hBm
  have hBmi : Integrable Bm μ := hJ0.1.const_mul (Cp * K)
  -- pointwise bounds on U
  have hpt : ∀ u : ℝ, 0 < u → ∀ q ∈ U, ∀ b : ℝ, b ^ 2 ≤ (q 2 - w 2) ^ 2 →
      ‖F q u‖ ≤ Cp * K * ((q 0 + u - ρ₀) * ((((q 0 + u - ρ₀) ^ 2 + b ^ 2) ^ 2)⁻¹)) ∧
      ‖F1 q u‖ ≤ Cp * K * ((q 0 + u - ρ₀) * ((((q 0 + u - ρ₀) ^ 2 + b ^ 2) ^ 2)⁻¹)) ∧
      ‖F2 q u‖ ≤ Cp * K * ((q 0 + u - ρ₀) * ((((q 0 + u - ρ₀) ^ 2 + b ^ 2) ^ 2)⁻¹)) := by
    intro u hu q hq b hb
    obtain ⟨p0, p1, p2⟩ := prim_pt hA w q hK hρ₀ hδ hw b0 b1 b2 u hu.le (le_of_lt hq) b hb
    have hFc : ContDiff ℝ 2 (fun q' : Space => primF A w q' u) := primF_contDiff_q hA w u
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_iteratedFDeriv_zero] at p0; exact p0
    · rw [norm_iteratedFDeriv_one] at p1; exact p1
    · have e : ‖F2 q u‖ = ‖iteratedFDeriv ℝ 2 (fun q' => primF A w q' u) q‖ := by
        rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun q' : Space => primF A w q' u) (x := q)
          (n := 1), norm_iteratedFDeriv_one]
      rw [e]; exact p2
  have hdom : ∀ u : ℝ, 0 < u → ∀ q ∈ U, ‖F q u‖ ≤ Bm u ∧ ‖F1 q u‖ ≤ Bm u ∧ ‖F2 q u‖ ≤ Bm u := by
    intro u hu q hq
    obtain ⟨p0, p1, p2⟩ := hpt u hu q hq 0 (by have := sq_nonneg (q 2 - w 2); simpa using this)
    have hv : δ + u ≤ q 0 + u - ρ₀ := by have : ρ₀ + δ < q 0 := hq; linarith
    have hd := prim_dec (by linarith : 0 < δ + u) hv
    have hc : 0 ≤ Cp * K := mul_nonneg hCp0 hK
    have hm := mul_le_mul_of_nonneg_left hd hc
    exact ⟨p0.trans hm, p1.trans hm, p2.trans hm⟩
  have hae : ∀ᵐ u ∂μ, 0 < u := by
    rw [hμ]; exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => hu)
  have ae_dom : ∀ q ∈ U, ∀ᵐ u ∂μ, ‖F q u‖ ≤ Bm u ∧ ‖F1 q u‖ ≤ Bm u ∧ ‖F2 q u‖ ≤ Bm u :=
    fun q hq => hae.mono fun u hu => hdom u hu q hq
  -- apply the generic lemma
  obtain ⟨d1, d2, d3⟩ := paramInt_two μ hU F F1 F2 Bm Bm Bm hBmi hBmi hBmi
    (hae.mono fun u _ q _ => ((primF_contDiff_q hA w u).differentiable (by norm_num) q).hasFDerivAt)
    (hae.mono fun u _ q _ => by
      have h1 : ContDiff ℝ 1 (fderiv ℝ (fun q' : Space => primF A w q' u)) :=
        (primF_contDiff_q hA w u).fderiv_right (by norm_num)
      exact ((h1.differentiable one_ne_zero) q).hasFDerivAt)
    (hae.mono fun u _ => by
      have h1 : ContDiff ℝ 1 (fderiv ℝ (fun q' : Space => primF A w q' u)) :=
        (primF_contDiff_q hA w u).fderiv_right (by norm_num)
      exact (h1.continuous_fderiv one_ne_zero).continuousOn)
    (fun q _ => (prim_partials_continuous hA w q).1.aestronglyMeasurable)
    (fun q _ => (prim_partials_continuous hA w q).2.1.aestronglyMeasurable)
    (fun q _ => (prim_partials_continuous hA w q).2.2.aestronglyMeasurable)
    (fun q hq => hae.mono fun u hu => (hdom u hu q hq).1)
    (hae.mono fun u hu q hq => (hdom u hu q hq).2.1)
    (hae.mono fun u hu q hq => (hdom u hu q hq).2.2)
  set G : Space → (Space →L[ℝ] ℝ) := fun q => ∫ u, F1 q u ∂μ with hG
  have hΨ : primInt A w = fun q => ∫ u, F q u ∂μ := rfl
  have hfder : ∀ p ∈ U, fderiv ℝ (primInt A w) p = G p := fun p hp => (d1 p hp).fderiv
  have hGfder : ∀ p ∈ U, fderiv ℝ G p = ∫ u, F2 p u ∂μ := fun p hp => (d2 p hp).fderiv
  have hG1 : ContDiffOn ℝ 1 G U := by
    have : ContDiffOn ℝ ((0 : ℕ) + 1) G U := by
      refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2 ⟨?_, fun h => absurd h (by simp), ?_⟩
      · exact fun p hp => (d2 p hp).differentiableAt.differentiableWithinAt
      · refine contDiffOn_zero.2 ?_
        exact d3.congr (fun p hp => hGfder p hp)
    simpa using this
  refine ⟨?_, fun q hq => ?_⟩
  · have : ContDiffOn ℝ ((1 : ℕ) + 1) (primInt A w) U := by
      refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2 ⟨?_, fun h => absurd h (by simp), ?_⟩
      · exact fun p hp => (d1 p hp).differentiableAt.differentiableWithinAt
      · simpa using hG1.congr (fun p hp => hfder p hp)
    have e : ((1 : ℕ) : WithTop ℕ∞) + 1 = 2 := by norm_num
    rwa [e] at this
  · have ha : 0 < q 0 - ρ₀ := by have : ρ₀ + δ < q 0 := hq; linarith
    obtain ⟨hJi, hJv⟩ := primJ2 ha (q 2 - w 2)
    have hI : ∫ u in Ioi (0 : ℝ), Cp * K * ((q 0 - ρ₀ + u) * ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹))
        = Cp * K * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - w 2) ^ 2))) := by
      rw [integral_const_mul, hJv]
    have hIi : Integrable (fun u : ℝ => Cp * K * ((q 0 - ρ₀ + u) *
        ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹))) μ := hJi.const_mul (Cp * K)
    have hsharp : ∀ᵐ u ∂μ, ‖F q u‖ ≤ Cp * K * ((q 0 - ρ₀ + u) *
        ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹)) ∧
        ‖F1 q u‖ ≤ Cp * K * ((q 0 - ρ₀ + u) *
        ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹)) ∧
        ‖F2 q u‖ ≤ Cp * K * ((q 0 - ρ₀ + u) *
        ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹)) := by
      refine hae.mono fun u hu => ?_
      have := hpt u hu q hq (q 2 - w 2) le_rfl
      have e : q 0 + u - ρ₀ = q 0 - ρ₀ + u := by ring
      rw [e] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_iteratedFDeriv_zero, hΨ]
      refine (norm_integral_le_of_norm_le hIi (hsharp.mono fun u hu => hu.1)).trans (le_of_eq hI)
    · rw [norm_iteratedFDeriv_one, hfder q hq]
      refine (norm_integral_le_of_norm_le hIi (hsharp.mono fun u hu => hu.2.1)).trans (le_of_eq hI)
    · rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := primInt A w) (x := q) (n := 1),
        norm_iteratedFDeriv_one]
      have hev : fderiv ℝ (primInt A w) =ᶠ[𝓝 q] G :=
        Filter.eventually_of_mem (hU.mem_nhds hq) fun p hp => hfder p hp
      rw [hev.fderiv_eq, hGfder q hq]
      exact (norm_integral_le_of_norm_le hIi (hsharp.mono fun u hu => hu.2.2)).trans (le_of_eq hI)

end UnforcedLeray.Short.PartIIIb.Concrete

end
