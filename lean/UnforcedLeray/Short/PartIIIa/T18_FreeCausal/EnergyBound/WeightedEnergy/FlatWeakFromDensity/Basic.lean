import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/2` helpers: elementary facts for `FlatWeakFromDensity`

Basic facts used in the proof of `flatWeakFromDensity`: compact supports of the time weight,
derivatives of products with a function of `s`, the cylinder test class of a spatial flat field,
and the pointwise decomposition of the extended integrand into the flat integrand plus an error
term that integrates to zero by the weak gradient identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A compactly supported time weight with `tsupport ⊆ (0,∞)` lies in some `[a, b]`, `a > 0`. -/
lemma exists_Icc_of_tsupport {ψ : ℝ → ℝ} (hc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ tsupport ψ ⊆ Icc a b := by
  rcases (tsupport ψ).eq_empty_or_nonempty with h | hne
  · exact ⟨1, 1, one_pos, by rw [h]; exact empty_subset _⟩
  · obtain ⟨x, hx, hmin⟩ := hc.isCompact.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨y, hy, hmax⟩ := hc.isCompact.exists_isMaxOn hne continuous_id.continuousOn
    exact ⟨x, y, hts hx, fun z hz => ⟨hmin hz, hmax hz⟩⟩

/-- Outside `[a, b] ⊇ tsupport ψ` the weight and its derivative vanish. -/
lemma weight_zero_of_not_mem_Icc {ψ : ℝ → ℝ} {a b : ℝ} (hts : tsupport ψ ⊆ Icc a b) {s : ℝ}
    (hs : s ∉ Icc a b) : ψ s = 0 ∧ deriv ψ s = 0 := by
  have hn : s ∉ tsupport ψ := fun h => hs (hts h)
  refine ⟨image_eq_zero_of_notMem_tsupport hn, ?_⟩
  by_contra h
  exact hn (support_deriv_subset h)

/-- The partial derivative commutes with multiplication by a constant. -/
lemma pd_const_mul_fun {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (j : Fin 2) (k : ℝ) :
    B0579.pd j (fun y => k * f y) = fun y => k * B0579.pd j f y := by
  funext x
  simp only [B0579.pd]
  rw [fderiv_const_mul (hf x) k]
  simp [smul_eq_mul]

/-- The planar Laplacian commutes with multiplication by a constant. -/
lemma lapP_const_mul {f : ℝ × ℝ → ℝ} {c : ℝ} (hf : B0579.IsCylTest c f) (k : ℝ) (x : ℝ × ℝ) :
    lapP (fun y => k * f y) x = k * lapP f x := by
  unfold lapP
  rw [pd_const_mul_fun hf.differentiable 0, pd_const_mul_fun (hf.pd 0).differentiable 0,
    pd_const_mul_fun hf.differentiable 1, pd_const_mul_fun (hf.pd 1).differentiable 1]
  simp only [mul_add]

/-- A component of a spatial flat test is a cylinder test. -/
lemma isCylTest_component {c : ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsFlatSpatialTest c φ)
    (i : Fin 2) : B0579.IsCylTest c (fun y => φ y i) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  exact ⟨hφ.smooth i, fun x => hφ.periodic x i, ⟨R, fun x hx => hR x i hx⟩⟩

/-- A spatial flat test times a time weight is a space-time flat test. -/
lemma isFlatTest_mul_spatial {c : ℝ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioi 0) {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hφ : IsFlatSpatialTest c φ) : IsFlatTest c (fun s x i => ψ s * φ x i) := by
  obtain ⟨a, b, ha, hab⟩ := exists_Icc_of_tsupport hc hts
  obtain ⟨R, hR⟩ := hφ.bounded
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (hψ.comp contDiff_fst).mul ((hφ.smooth i).comp contDiff_snd)
  · intro s x i
    simp [hφ.periodic x i]
  · refine ⟨a, b, R, ha, fun s x i h => ?_⟩
    rcases h with h | h | h
    · have hs : s ∉ Icc a b := fun hm => absurd hm.1 (not_le.2 h)
      simp [(weight_zero_of_not_mem_Icc hab hs).1]
    · have hs : s ∉ Icc a b := fun hm => absurd hm.2 (not_le.2 h)
      simp [(weight_zero_of_not_mem_Icc hab hs).1]
    · simp [hR x i h]
  · intro s x
    have hd : ∀ j : Fin 2, B0579.pd j (fun y => ψ s * φ y j) x = ψ s * B0579.pd j (fun y => φ y j) x :=
      fun j => by
        rw [pd_const_mul_fun (isCylTest_component hφ j).differentiable j (ψ s)]
    simp only [hd]
    have h0 := hφ.divFree x
    calc ψ s * B0579.pd 0 (fun y => φ y 0) x + ψ s * B0579.pd 1 (fun y => φ y 1) x
        = ψ s * (B0579.pd 0 (fun y => φ y 0) x + B0579.pd 1 (fun y => φ y 1) x) := by ring
      _ = 0 := by rw [h0, mul_zero]

end UnforcedLeray.Short.IIIa
