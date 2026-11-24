import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair.PhaseChartBochner

/-!
# `PartII-b:T10/7/1/2/2/3` (`ct_unfold`), SP 1639-1668

Unfolding of the `q`-periodization: tiles `T n = {s > 0, q + n c ∈ cell}` of `{s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CTU

open UnforcedLeray UnforcedLeray.Axi UnforcedLeray.Short.IIb.PCAux UnforcedLeray.Short.IIb.PCB

/-- The base region `(0,∞) × cell`. -/
abbrev S (c : ℝ) : Set Coord := Ioi (0 : ℝ) ×ˢ qCell c

/-- Tiles. -/
def T (c : ℝ) (n : ℤ) : Set Coord := sh c (-n) ⁻¹' S c

lemma measurableSet_S (c : ℝ) : MeasurableSet (S c) := meas_Ioi_cell c

lemma measurableSet_T (c : ℝ) (n : ℤ) : MeasurableSet (T c n) :=
  measurable_sh c (-n) (measurableSet_S c)

lemma mem_T {c : ℝ} {n : ℤ} {x : Coord} :
    x ∈ T c n ↔ 0 < x.1 ∧ -c / 2 ≤ x.2.1 + (-(n : ℝ)) * c ∧ x.2.1 + (-(n : ℝ)) * c < c / 2 := by
  simp [T, S, qCell, sh]

lemma sh_preimage_T (c : ℝ) (n : ℤ) : sh c n ⁻¹' T c n = S c := by
  ext x
  simp only [T, mem_preimage, sh_sh, neg_add_cancel, sh_zero]

lemma pairwise_T {c : ℝ} (hc : 0 < c) : Pairwise (Function.onFun Disjoint (T c)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  intro x hn hm
  rw [mem_T] at hn hm
  have h1 : ((n : ℝ) - m) * c < c := by nlinarith [hn.2.1, hn.2.2, hm.2.1, hm.2.2]
  have h2 : -c < ((n : ℝ) - m) * c := by nlinarith [hn.2.1, hn.2.2, hm.2.1, hm.2.2]
  have h3 : (n : ℝ) - m < 1 := by
    by_contra h; push_neg at h; nlinarith
  have h4 : -1 < (n : ℝ) - m := by
    by_contra h; push_neg at h; nlinarith
  have h5 : n - m < 1 := by exact_mod_cast h3
  have h6 : -1 < n - m := by exact_mod_cast h4
  exact hnm (by omega)

lemma iUnion_T {c : ℝ} (hc : 0 < c) : (⋃ n : ℤ, T c n) = {x : Coord | 0 < x.1} := by
  ext x
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩; exact (mem_T.1 hn).1
  · intro hx
    refine ⟨kk c x.2.1, ?_⟩
    have := red_mem hc x
    simp only [red, sh, Cyl.cell, mem_prod, mem_Ico, mem_univ, and_true] at this
    rw [mem_T]
    refine ⟨hx, ?_, ?_⟩
    · have := this.1; push_cast at this; linarith
    · have := this.2; push_cast at this; linarith

/-- `sh c n` as a measurable equivalence. -/
def shE (c : ℝ) (n : ℤ) : Coord ≃ᵐ Coord where
  toFun := sh c n
  invFun := sh c (-n)
  left_inv x := by simp [sh_sh, sh_zero]
  right_inv x := by simp [sh_sh, sh_zero]
  measurable_toFun := measurable_sh c n
  measurable_invFun := measurable_sh c (-n)

lemma setIntegral_sh {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (n : ℤ)
    (K : Coord → E) :
    ∫ p in S c, K (sh c n p) = ∫ y in T c n, K y := by
  have := (mp_sh c n).setIntegral_preimage_emb (shE c n).measurableEmbedding K (T c n)
  rw [sh_preimage_T] at this
  exact this

lemma meas_rho (c a : ℝ) : Measurable (fun p : Coord => ENNReal.ofReal (c⁻¹ * p.1 ^ a)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const a))

lemma ageμ_eq {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ageμ c a = (volume.restrict (S c)).withDensity (fun p => ENNReal.ofReal (c⁻¹ * p.1 ^ a)) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_ageμ hc a hf, lintegral_withDensity_eq_lintegral_mul _ ?_ hf]
  · rfl
  · exact ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const a))

lemma integral_ageμ {c : ℝ} (hc : 0 < c) (a : ℝ) (F : Coord → ℂ) :
    ∫ p, F p ∂(ageμ c a) = ∫ p in S c, (c⁻¹ * p.1 ^ a) • F p := by
  rw [ageμ_eq hc a, integral_withDensity_eq_integral_toReal_smul (meas_rho c a)
    (by simp)]
  refine setIntegral_congr_fun (measurableSet_S c) fun p hp => ?_
  have : 0 ≤ c⁻¹ * p.1 ^ a := by have := hp.1; simp only [mem_Ioi] at this; positivity
  simp only [ENNReal.toReal_ofReal this]

lemma integrable_ageμ {c : ℝ} (hc : 0 < c) (a : ℝ) (F : Coord → ℂ)
    (h : Integrable (fun p => (c⁻¹ * p.1 ^ a) • F p) (volume.restrict (S c))) :
    Integrable F (ageμ c a) := by
  rw [ageμ_eq hc a, integrable_withDensity_iff_integrable_smul' (meas_rho c a)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine h.congr ?_
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_S c)]
  refine Filter.Eventually.of_forall fun p hp => ?_
  have : 0 ≤ c⁻¹ * p.1 ^ a := by have := hp.1; simp only [mem_Ioi] at this; positivity
  simp only [ENNReal.toReal_ofReal this]


lemma phi_box {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ σ H R L : ℝ, 0 < σ ∧ ∀ x, φ x ≠ 0 →
      x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hb : ∀ x, φ x ≠ 0 → |x.1| ≤ C ∧ |x.2.1| ≤ C ∧ |x.2.2| ≤ C := by
    intro x hx
    have h := hC x (subset_tsupport _ (Function.mem_support.2 hx))
    refine ⟨?_, ?_, ?_⟩
    · exact (Real.norm_eq_abs _ ▸ norm_fst_le x).trans h
    · exact (Real.norm_eq_abs _ ▸ ((norm_fst_le x.2).trans (norm_snd_le x))).trans h
    · exact (Real.norm_eq_abs _ ▸ ((norm_snd_le x.2).trans (norm_snd_le x))).trans h
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨σ, hσ, hmin⟩ := (hK.image continuous_fst).exists_isLeast (hne.image _)
    obtain ⟨y, hy, rfl⟩ := hσ
    have hpos : 0 < y.1 := hφ.supp hy |>.1
    refine ⟨y.1, C, C, C, hpos, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb x hx
    have hs : y.1 ≤ x.1 := hmin ⟨x, subset_tsupport _ (Function.mem_support.2 hx), rfl⟩
    exact ⟨⟨hs, (abs_le.1 h1).2⟩, ⟨(abs_le.1 h2).1, (abs_le.1 h2).2⟩,
      ⟨(abs_le.1 h3).1, (abs_le.1 h3).2⟩⟩
  · refine ⟨1, 0, 0, 0, one_pos, fun x hx => ?_⟩
    exact absurd ⟨x, subset_tsupport _ (Function.mem_support.2 hx)⟩ hne

lemma K_integrable {c : ℝ} {φ : Coord → ℝ} (a : ℝ) (hφ : IsCoordTest φ) (g : Coord → ℂ)
    (hbox : ∀ σ H R L : ℝ, 0 < σ →
      IntegrableOn g (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume) :
    Integrable (fun x : Coord => (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g x * (φ x : ℂ)) volume := by
  obtain ⟨σ, H, R, L, hσ, hB⟩ := phi_box hφ
  set B : Set Coord := Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L) with hBdef
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hm : ContinuousOn (fun x : Coord => (((x.1 ^ (a - 2) : ℝ)) : ℂ) * (φ x : ℂ)) B := by
    refine ContinuousOn.mul ?_ (Complex.continuous_ofReal.comp hφ.smooth.continuous).continuousOn
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.rpow_const continuous_fst.continuousOn fun x hx => Or.inl ?_
    exact (lt_of_lt_of_le hσ hx.1.1).ne'
  have h1 : IntegrableOn (fun x : Coord => (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g x * (φ x : ℂ)) B
      volume :=
    (IntegrableOn.continuousOn_mul hm (hbox σ H R L hσ) hBc).congr_fun
      (fun x _ => by ring) hBc.measurableSet
  rw [integrableOn_iff_integrable_of_support_subset] at h1
  · exact h1
  · intro x hx
    by_contra hxB
    apply hx
    have : φ x = 0 := by
      by_contra h; exact hxB (hB x h)
    simp [this]

lemma finite_range {c : ℝ} (hc : 0 < c) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ N : ℤ, ∀ p ∈ S c, ∀ n : ℤ, n ∉ Finset.Icc (-N) N → φ (sh c n p) = 0 := by
  obtain ⟨σ, H, R, L, hσ, hB⟩ := phi_box hφ
  refine ⟨⌈(R + c / 2) / c⌉, fun p hp n hn => ?_⟩
  by_contra hne
  have h := (hB _ hne).2.1
  have hq := hp.2.1
  simp only [sh, mem_Icc, mem_Ico] at h hq
  have hup : (n : ℝ) ≤ ⌈(R + c / 2) / c⌉ := by
    refine le_trans ?_ (Int.le_ceil _)
    rw [le_div_iff₀ hc]; nlinarith [h.1, h.2, hq.1, hq.2]
  have hlo : -(n : ℝ) ≤ ⌈(R + c / 2) / c⌉ := by
    refine le_trans ?_ (Int.le_ceil _)
    rw [le_div_iff₀ hc]; nlinarith [h.1, h.2, hq.1, hq.2]
  apply hn
  rw [Finset.mem_Icc]
  constructor
  · have : (-(n : ℝ)) ≤ ((⌈(R + c / 2) / c⌉ : ℤ) : ℝ) := hlo
    have : -n ≤ ⌈(R + c / 2) / c⌉ := by exact_mod_cast this
    omega
  · exact_mod_cast hup

lemma rpow_id {s : ℝ} (hs : 0 < s) (a : ℝ) :
    s ^ (-(5 / 2 : ℝ)) * (s ^ a * Real.sqrt s) = s ^ (a - 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs, ← Real.rpow_add hs]
  congr 1; ring

lemma cLift_eq (c a : ℝ) (φ : Coord → ℝ) (x : Coord) :
    cLift c a φ x = ∑' n : ℤ, x.1 ^ a * φ (sh c n x) := rfl

lemma cLift_qShift (c a : ℝ) (φ : Coord → ℝ) (x : Coord) :
    cLift c a φ (qShift c x) = cLift c a φ x := by
  rw [cLift_eq, cLift_eq]
  have e : ∀ n : ℤ, sh c n (qShift c x) = sh c (n + 1) x := by
    intro n; rw [← sh_one, sh_sh]
  simp only [e]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => x.1 ^ a * φ (sh c n x))

lemma pt_identity {c : ℝ} (a : ℝ) (φ : Coord → ℝ) (g : Coord → ℂ) (N : ℤ)
    (hN : ∀ p ∈ S c, ∀ n : ℤ, n ∉ Finset.Icc (-N) N → φ (sh c n p) = 0)
    (p : Coord) (hp : p ∈ S c) (hg : ∀ n : ℤ, g (sh c n p) = g p) :
    (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) •
        (((cLift c a φ p : ℝ) : ℂ) * ((Real.sqrt p.1 : ℝ) : ℂ) * g p) =
      ((c⁻¹ : ℝ) : ℂ) * ∑ n ∈ Finset.Icc (-N) N,
        (((sh c n p).1 ^ (a - 2) : ℝ) : ℂ) * g (sh c n p) * (φ (sh c n p) : ℂ) := by
  have hpos : 0 < p.1 := hp.1
  rw [cLift_eq, tsum_eq_sum (s := Finset.Icc (-N) N)
    (fun n hn => by rw [hN p hp n hn, mul_zero])]
  have key : ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * (((p.1 ^ a : ℝ) : ℂ) * ((Real.sqrt p.1 : ℝ) : ℂ))
      = ((p.1 ^ (a - 2) : ℝ) : ℂ) := by
    exact_mod_cast rpow_id hpos a
  rw [Complex.real_smul, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hg n]
  have hf : (sh c n p).1 = p.1 := rfl
  rw [hf]
  push_cast
  linear_combination ((c⁻¹ : ℂ) * (φ (sh c n p) : ℂ) * g p) * key

end UnforcedLeray.Short.IIb.CTU

open UnforcedLeray UnforcedLeray.Axi UnforcedLeray.Short.IIb.PCAux UnforcedLeray.Short.IIb.PCB
  UnforcedLeray.Short.IIb.CTU in
theorem UnforcedLeray.Short.IIb.ct_unfold : UnforcedLeray.Short.IIb.CTUnfold := by
  intro c a φ g hc hφ hg hbox
  obtain ⟨N, hN⟩ := finite_range hc hφ
  have hKi := K_integrable (c := c) a hφ g hbox
  set K : Coord → ℂ := fun x => (((x.1 ^ (a - 2) : ℝ)) : ℂ) * g x * (φ x : ℂ) with hK
  have hgood : ∀ᵐ x ∂(volume : Measure Coord), ∀ n : ℤ, 0 < x.1 → g (sh c n x) = g x :=
    ae_good (by filter_upwards [hg] with x hx _ using hx)
  set Gf : Coord → ℂ := fun x : Coord =>
    ((cLift c a φ x : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * g x with hGf
  have hae : (fun p => (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) • Gf p) =ᵐ[volume.restrict (S c)]
      fun p => ((c⁻¹ : ℝ) : ℂ) * ∑ n ∈ Finset.Icc (-N) N, K (sh c n p) := by
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_S c)]
    filter_upwards [hgood] with p hp hpS
    exact pt_identity a φ g N hN p hpS (fun n => hp n hpS.1)
  have hint2 : Integrable (fun p => ((c⁻¹ : ℝ) : ℂ) * ∑ n ∈ Finset.Icc (-N) N, K (sh c n p))
      (volume.restrict (S c)) :=
    (integrable_finsetSum _ (fun n _ =>
      ((mp_sh c n).integrable_comp_of_integrable hKi).restrict)).const_mul _
  refine ⟨integrable_ageμ hc _ Gf (hint2.congr hae.symm), ?_, ?_⟩
  · filter_upwards [hg] with x hx _
    rw [cLift_qShift, hx]
    rfl
  · have hs := integral_finsetSum (μ := volume.restrict (S c)) (Finset.Icc (-N) N)
      (f := fun n p => K (sh c n p))
      (fun n _ => ((mp_sh c n).integrable_comp_of_integrable hKi).restrict)
    beta_reduce at hs
    rw [integral_ageμ hc _ Gf, integral_congr_ae hae, integral_const_mul, hs]
    have hK0 : ∀ x, x ∉ {x : Coord | 0 < x.1} → K x = 0 := by
      intro x hx
      have : φ x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h; exact hx (hφ.supp h).1
      simp [hK, this]
    have h1 : ∫ x, K x = ∫ x in ⋃ n : ℤ, T c n, K x := by
      rw [iUnion_T hc]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hK0).symm
    rw [h1, integral_iUnion (measurableSet_T c) (pairwise_T hc) hKi.integrableOn,
      tsum_eq_sum (s := Finset.Icc (-N) N)]
    · congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      exact setIntegral_sh c n K
    · intro n hn
      rw [← setIntegral_sh c n K]
      refine setIntegral_eq_zero_of_forall_eq_zero fun p hp => ?_
      simp [hK, hN p hp n hn]

theorem ct_unfold : UnforcedLeray.Short.IIb.CTUnfold := UnforcedLeray.Short.IIb.ct_unfold

#print axioms ct_unfold
