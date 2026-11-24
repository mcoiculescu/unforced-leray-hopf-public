import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt

/-!
# `PartIII-a:T21/2/7/2/1/1/5/6`: periodization of a compactly supported kernel

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3058
(pairings on the cylinder). For a smooth compactly supported real kernel `K`, the periodization
`perKer c K(y) = Σ_k K(y₁ + kc, y₂)` is a cylinder test, commutes with `∂_j`, and pairs with every
`c`-periodic `f ∈ X_{-m,c}` as the cell integral `∫_{C_c} (perKer c K) f`.

Proof structure: `K` is supported in a box `|z₁| ≤ R`, `|z₂| ≤ R`. The sum over `k` is locally
finite: on `{|y₁| < L}` only `|k| ≤ N` contribute, `N = ⌈(R+L)/c⌉`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `⌈a/c⌉ c ≥ a` for `c > 0`. -/
theorem ceil_mul_ge_cp {c : ℝ} (hc : 0 < c) (a : ℝ) : a ≤ (⌈a / c⌉ : ℝ) * c :=
  (div_le_iff₀ hc).1 (Int.le_ceil _)

/-- Vanishing of a kernel outside the box `[-R, R]²` (for the sup norm). -/
theorem supp_bound_cp {K : ℝ × ℝ → ℝ} (hKc : HasCompactSupport K) :
    ∃ R : ℝ, ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → K z = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1
    hKc.isCompact.isBounded
  refine ⟨R, fun z hz => ?_⟩
  by_contra hne
  have hmem : z ∈ tsupport K := subset_tsupport K (Function.mem_support.2 hne)
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hmem)
  have h1 : |z.1| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_fst_le z
  have h2 : |z.2| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_snd_le z
  rcases hz with hz | hz <;> linarith

/-- Tail terms vanish: if `|y₁| < L` and `R + L ≤ N c`, then `G(y₁ + kc, y₂) = 0` for `k ∉ [-N, N]`. -/
theorem tail_cp {c R L : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℝ}
    (hG : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → G z = 0)
    {N : ℤ} (hN : R + L ≤ N * c) (y : ℝ × ℝ) (hy : |y.1| < L) (k : ℤ)
    (hk : k ∉ Finset.Icc (-N) N) : G (y.1 + k * c, y.2) = 0 := by
  apply hG
  left
  show R < |y.1 + k * c|
  have hyL := abs_lt.1 hy
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · have h1 : k + 1 ≤ -N := by omega
    have h2 : (k : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast h1
    have h3 : ((k : ℝ) + 1) * c ≤ (-(N : ℝ)) * c := mul_le_mul_of_nonneg_right h2 hc.le
    have h4 : ((k : ℝ) + 1) * c = k * c + c := by ring
    have h5 : (-(N : ℝ)) * c = -((N : ℝ) * c) := by ring
    apply lt_abs.2
    right
    linarith [hyL.2]
  · have h1 : N + 1 ≤ k := by omega
    have h2 : (N : ℝ) + 1 ≤ k := by exact_mod_cast h1
    have h3 : ((N : ℝ) + 1) * c ≤ k * c := mul_le_mul_of_nonneg_right h2 hc.le
    have h4 : ((N : ℝ) + 1) * c = (N : ℝ) * c + c := by ring
    apply lt_abs.2
    left
    linarith [hyL.1]

/-- Locally finite form of the periodization. -/
theorem perKer_fin_cp {c R L : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℝ}
    (hG : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → G z = 0)
    {N : ℤ} (hN : R + L ≤ N * c) (y : ℝ × ℝ) (hy : |y.1| < L) :
    perKer c G y = ∑ k ∈ Finset.Icc (-N) N, G (y.1 + k * c, y.2) := by
  unfold perKer
  exact tsum_eq_sum (fun k hk => tail_cp hc hG hN y hy k hk)

/-- The periodization vanishes for `|y₂| > R`. -/
theorem perKer_band_cp {c R : ℝ} {G : ℝ × ℝ → ℝ}
    (hG : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → G z = 0) (y : ℝ × ℝ) (hy : R < |y.2|) :
    perKer c G y = 0 := by
  unfold perKer
  have h0 : ∀ k : ℤ, G (y.1 + k * c, y.2) = 0 := fun k => hG _ (Or.inr hy)
  simp only [h0, tsum_zero]

/-- The periodization is `c`-periodic in `y₁`. -/
theorem perKer_periodic_cp {c : ℝ} (G : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    perKer c G (y.1 + c, y.2) = perKer c G y := by
  unfold perKer
  have e : ∀ k : ℤ, ((y.1 + c, y.2).1 + k * c, (y.1 + c, y.2).2) =
      (y.1 + ((k + 1 : ℤ) : ℝ) * c, y.2) := by
    intro k
    ext <;> simp <;> ring
  calc ∑' k : ℤ, G ((y.1 + c, y.2).1 + k * c, (y.1 + c, y.2).2)
      = ∑' k : ℤ, G (y.1 + ((k + 1 : ℤ) : ℝ) * c, y.2) := tsum_congr fun k => by rw [e k]
    _ = ∑' k : ℤ, G (y.1 + (k : ℝ) * c, y.2) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => G (y.1 + (k : ℝ) * c, y.2))

/-- Smoothness of a shifted kernel. -/
theorem shift_contDiff_cp {K : ℝ × ℝ → ℝ} (hK : ContDiff ℝ ∞ K) (a : ℝ) :
    ContDiff ℝ ∞ (fun w : ℝ × ℝ => K (w.1 + a, w.2)) :=
  hK.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

/-- The periodization is smooth. -/
theorem perKer_contDiff_cp {c R : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℝ} (hG0 : ContDiff ℝ ∞ G)
    (hG : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → G z = 0) :
    ContDiff ℝ ∞ (perKer c G) := by
  rw [contDiff_iff_contDiffAt]
  intro x0
  set L : ℝ := |x0.1| + 1 with hL
  set N : ℤ := ⌈(R + L) / c⌉ with hNd
  have hN : R + L ≤ N * c := ceil_mul_ge_cp hc _
  have hsm : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, G (y.1 + k * c, y.2)) := by
    apply ContDiff.sum
    intro k _
    exact hG0.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  have hx0 : |x0.1| < L := by rw [hL]; linarith
  have hev : perKer c G =ᶠ[𝓝 x0] (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, G (y.1 + k * c, y.2)) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds hx0)
      (fun w hw => perKer_fin_cp hc hG hN w hw)
  exact hsm.contDiffAt.congr_of_eventuallyEq hev

/-- A partial derivative of a kernel vanishes where the kernel vanishes near. -/
theorem pd_zero_cp {R : ℝ} {K : ℝ × ℝ → ℝ}
    (hKR : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → K z = 0) (j : Fin 2) (z : ℝ × ℝ)
    (hz : R < |z.1| ∨ R < |z.2|) : B0579.pd j K z = 0 := by
  have hopen : IsOpen {w : ℝ × ℝ | R < |w.1| ∨ R < |w.2|} :=
    (isOpen_lt continuous_const continuous_fst.abs).union
      (isOpen_lt continuous_const continuous_snd.abs)
  have hev : K =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) (fun w hw => hKR w hw)
  have hfd : fderiv ℝ K z = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp [B0579.pd, hfd]

/-- The derivative of the periodization is the periodization of the derivative. -/
theorem pd_perKer_cp {c R : ℝ} (hc : 0 < c) {K : ℝ × ℝ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hKR : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → K z = 0) (j : Fin 2) :
    B0579.pd j (perKer c K) = perKer c (B0579.pd j K) := by
  funext y
  set L : ℝ := |y.1| + 1 with hL
  have hyL : |y.1| < L := by rw [hL]; linarith
  set N : ℤ := ⌈(R + L) / c⌉ with hNd
  have hN : R + L ≤ N * c := ceil_mul_ge_cp hc _
  have hpdR : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → B0579.pd j K z = 0 :=
    fun z hz => pd_zero_cp hKR j z hz
  have hev : perKer c K =ᶠ[𝓝 y]
      (fun w : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, K (w.1 + k * c, w.2)) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds hyL)
      (fun w hw => perKer_fin_cp hc hKR hN w hw)
  show fderiv ℝ (perKer c K) y (B0579.dir j) = perKer c (B0579.pd j K) y
  rw [hev.fderiv_eq, perKer_fin_cp hc hpdR hN y hyL]
  have hsum : HasFDerivAt (fun w : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, K (w.1 + k * c, w.2))
      (∑ k ∈ Finset.Icc (-N) N, fderiv ℝ (fun w : ℝ × ℝ => K (w.1 + k * c, w.2)) y) y :=
    HasFDerivAt.fun_sum (fun k _ =>
      ((shift_contDiff_cp hK ((k : ℝ) * c)).differentiable (by simp)).differentiableAt.hasFDerivAt)
  rw [hsum.fderiv, sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hfun : (fun w : ℝ × ℝ => K (w.1 + k * c, w.2)) = fun w => K (w + ((k : ℝ) * c, 0)) := by
    funext w
    congr 1
    ext <;> simp
  rw [hfun, fderiv_comp_add_right]
  have e : y + ((k : ℝ) * c, 0) = (y.1 + k * c, y.2) := by
    ext <;> simp
  show fderiv ℝ K (y + ((k : ℝ) * c, 0)) (B0579.dir j) = fderiv ℝ K (y.1 + k * c, y.2) (B0579.dir j)
  rw [e]

/-- Disjointness of the translated cells. -/
theorem perTile_disj_cp {c : ℝ} (hc : 0 < c) {k k' : ℤ} (hne : k ≠ k') :
    Disjoint (perTile c k) (perTile c k') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [perTile, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hz hz'
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h3, h4⟩ := hz'
  rcases lt_or_gt_of_ne hne with h | h
  · have h5 : (k : ℝ) + 1 ≤ k' := by exact_mod_cast (show k + 1 ≤ k' by omega)
    have h6 : ((k : ℝ) + 1) * c ≤ k' * c := mul_le_mul_of_nonneg_right h5 hc.le
    have h7 : ((k : ℝ) + 1) * c = k * c + c := by ring
    linarith
  · have h5 : (k' : ℝ) + 1 ≤ k := by exact_mod_cast (show k' + 1 ≤ k by omega)
    have h6 : ((k' : ℝ) + 1) * c ≤ k * c := mul_le_mul_of_nonneg_right h5 hc.le
    have h7 : ((k' : ℝ) + 1) * c = k' * c + c := by ring
    linarith

theorem perTile_meas_cp (c : ℝ) (k : ℤ) : MeasurableSet (perTile c k) := by
  unfold perTile
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- The pairing: `∫_{ℝ²} K f = ∫_{C_c} (perKer c K) f`, and `K f` is integrable. -/
theorem pair_cp {c m R : ℝ} (hc : 0 < c) {K : ℝ × ℝ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hKc : HasCompactSupport K)
    (hKR : ∀ z : ℝ × ℝ, R < |z.1| ∨ R < |z.2| → K z = 0)
    (f : ℝ × ℝ → ℂ) (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    Integrable (fun y => K y • f y) ∧
      ∫ y, K y • f y = ∫ y in B0579.cell c, perKer c K y • f y := by
  have hloc : LocallyIntegrable f volume := (cellPeriodicLocInt c m f hc hper hf).2
  have hl : LocallyIntegrable (fun y => K y • f y) volume :=
    LocallyIntegrable.continuous_smul hK.continuous hloc
  have hsub : Function.support (fun y => K y • f y) ⊆ tsupport K :=
    fun y hy => subset_tsupport K (fun h => Function.mem_support.1 hy (by simp [h]))
  have hG : Integrable (fun y => K y • f y) volume :=
    (integrableOn_iff_integrable_of_support_subset hsub).1
      (hl.integrableOn_isCompact hKc.isCompact)
  set N : ℤ := ⌈(R + (c / 2 + 1)) / c⌉ with hNd
  have hN : R + (c / 2 + 1) ≤ N * c := ceil_mul_ge_cp hc _
  have htile : ∀ k : ℤ, k ∉ Finset.Icc (-N) N → ∀ z ∈ perTile c k, K z = 0 := by
    intro k hk z hz
    have hz' := hz
    simp only [perTile, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hz'
    obtain ⟨h1, h2⟩ := hz'
    have hy : |(z.1 - k * c, z.2).1| < c / 2 + 1 := by
      show |z.1 - k * c| < c / 2 + 1
      rw [abs_lt]
      constructor <;> linarith
    have h := tail_cp hc hKR hN (z.1 - k * c, z.2) hy k hk
    simpa using h
  have hU : ∫ y, K y • f y = ∫ y in (⋃ k ∈ Finset.Icc (-N) N, perTile c k), K y • f y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hcov : x ∈ ⋃ k : ℤ, perTile c k := by
      rw [perTile_cover c hc]
      trivial
    obtain ⟨k0, hk0⟩ := Set.mem_iUnion.1 hcov
    have hk0S : k0 ∉ Finset.Icc (-N) N := fun h => hx (Set.mem_biUnion h hk0)
    show K x • f x = 0
    rw [htile k0 hk0S x hk0, zero_smul]
  have hsum : ∫ y in (⋃ k ∈ Finset.Icc (-N) N, perTile c k), K y • f y =
      ∑ k ∈ Finset.Icc (-N) N, ∫ y in perTile c k, K y • f y :=
    integral_biUnion_finset _ (fun k _ => perTile_meas_cp c k)
      (fun k _ k' _ hne => perTile_disj_cp hc hne)
      (fun k _ => hG.integrableOn)
  have htrans : ∀ k : ℤ, ∫ y in perTile c k, K y • f y =
      ∫ y in B0579.cell c, K (y.1 + k * c, y.2) • f y := by
    intro k
    have hv := (perTile_mp c k).integral_comp
      (measurableEmbedding_subRight ((k : ℝ) * c, 0))
      (fun z => K (z + ((k : ℝ) * c, 0)) • f (z + ((k : ℝ) * c, 0)))
    simp only [sub_add_cancel] at hv
    rw [hv]
    apply setIntegral_congr_fun (B0579.measurableSet_cell c)
    intro y _
    show K (y + ((k : ℝ) * c, 0)) • f (y + ((k : ℝ) * c, 0)) = K (y.1 + k * c, y.2) • f y
    have e : y + ((k : ℝ) * c, 0) = (y.1 + k * c, y.2) := by
      ext <;> simp
    rw [e, per_shift' hper k y]
  have hHk : ∀ k : ℤ, Integrable (fun y => K (y.1 + k * c, y.2) • f y) volume := by
    intro k
    have h1 := ((measurePreserving_add_right volume ((k : ℝ) * c, 0)).integrable_comp_emb
      (measurableEmbedding_addRight ((k : ℝ) * c, 0))).2 hG
    refine h1.congr (ae_of_all _ fun y => ?_)
    show K (y + ((k : ℝ) * c, 0)) • f (y + ((k : ℝ) * c, 0)) = K (y.1 + k * c, y.2) • f y
    have e : y + ((k : ℝ) * c, 0) = (y.1 + k * c, y.2) := by
      ext <;> simp
    rw [e, per_shift' hper k y]
  have hfs : ∑ k ∈ Finset.Icc (-N) N, ∫ y in B0579.cell c, K (y.1 + k * c, y.2) • f y =
      ∫ y in B0579.cell c, perKer c K y • f y := by
    rw [← integral_finsetSum _ (fun k _ => (hHk k).integrableOn)]
    apply setIntegral_congr_fun (B0579.measurableSet_cell c)
    intro y hy
    have hy' := hy
    simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hy'
    have hyL : |y.1| < c / 2 + 1 := by
      rw [abs_lt]
      constructor <;> linarith [hy'.1, hy'.2]
    show ∑ k ∈ Finset.Icc (-N) N, K (y.1 + k * c, y.2) • f y = perKer c K y • f y
    rw [perKer_fin_cp hc hKR hN y hyL, Finset.sum_smul]
  refine ⟨hG, ?_⟩
  rw [hU, hsum, Finset.sum_congr rfl (fun k _ => htrans k), hfs]

theorem cellPeriodize : CellPeriodize := by
  intro c m K hc hK hKc
  obtain ⟨R, hKR⟩ := supp_bound_cp hKc
  refine ⟨⟨perKer_contDiff_cp hc hK hKR, fun y => perKer_periodic_cp K y,
    ⟨R, fun y hy => perKer_band_cp hKR y hy⟩⟩, fun j => pd_perKer_cp hc hK hKR j, ?_⟩
  intro f hper hf
  exact pair_cp (m := m) hc hK hKc hKR f hper hf

end UnforcedLeray.Short.IIIa
