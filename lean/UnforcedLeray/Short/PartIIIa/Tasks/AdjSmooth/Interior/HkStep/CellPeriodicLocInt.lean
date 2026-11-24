import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

/-!
# `PartIII-a:T21/2/7/2/1/1/5/2`: periodic fields of `X_{-m,c}` are locally integrable

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3047,
3060-3061. The plane is tiled by the translates `perTile c k = [-c/2 + kc, c/2 + kc) × ℝ` of the
cell; a `c`-periodic `f` is a translate of its restriction to the cell (`perTile_shift`), so it is
measurable on each tile and hence on the plane. Local integrability: a compact set lies in a box
covered by finitely many tiles; on the cell band `cell ∩ (ℝ × [-ρ, ρ])`, the weight `⟨x⟩^{-2m}` is
bounded below, so `f ∈ L²(cell ∩ band)` and the band has finite measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `k`-th translate of the cell. -/
def perTile (c : ℝ) (k : ℤ) : Set (ℝ × ℝ) :=
  Ico (-(c / 2) + k * c) (c / 2 + k * c) ×ˢ univ

theorem per_shift' {c : ℝ} {f : ℝ × ℝ → ℂ} (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (k : ℤ) (x : ℝ × ℝ) : f (x.1 + k * c, x.2) = f x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have e : x.1 + ((i + 1 : ℤ) : ℝ) * c = (x.1 + ((i : ℤ) : ℝ) * c) + c := by push_cast; ring
    have h := hper (x.1 + ((i : ℤ) : ℝ) * c, x.2)
    dsimp only at h
    rw [e, h, ih]
  | pred i ih =>
    have e : (x.1 + ((-(i : ℤ) - 1 : ℤ) : ℝ) * c) + c = x.1 + ((-(i : ℤ) : ℤ) : ℝ) * c := by
      push_cast; ring
    have h := hper (x.1 + ((-(i : ℤ) - 1 : ℤ) : ℝ) * c, x.2)
    rw [e] at h
    rw [← h, ih]

theorem perTile_shift {c : ℝ} {f : ℝ × ℝ → ℂ} (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (k : ℤ) : f ∘ (fun g : ℝ × ℝ => g - ((k : ℝ) * c, 0)) = f := by
  funext x
  have h := per_shift' hper k (x - ((k : ℝ) * c, 0))
  simpa using h.symm

theorem perTile_mp (c : ℝ) (k : ℤ) :
    MeasurePreserving (fun g : ℝ × ℝ => g - ((k : ℝ) * c, 0))
      (volume.restrict (perTile c k)) (volume.restrict (B0579.cell c)) := by
  have hpre : (fun g : ℝ × ℝ => g - ((k : ℝ) * c, 0)) ⁻¹' B0579.cell c = perTile c k := by
    ext x
    simp only [mem_preimage, B0579.cell, perTile, mem_prod, mem_Ico, mem_univ, and_true,
      Prod.fst_sub, Prod.snd_sub, sub_zero]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← hpre]
  exact (measurePreserving_sub_right volume ((k : ℝ) * c, 0)).restrict_preimage
    (B0579.measurableSet_cell c)

theorem perTile_aesm {c : ℝ} {f : ℝ × ℝ → ℂ} (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (hfv : AEStronglyMeasurable f (volume.restrict (B0579.cell c))) (k : ℤ) :
    AEStronglyMeasurable f (volume.restrict (perTile c k)) := by
  have h := hfv.comp_measurePreserving (perTile_mp c k)
  rwa [perTile_shift hper k] at h

theorem perTile_cover (c : ℝ) (hc : 0 < c) : (⋃ k : ℤ, perTile c k) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  refine ⟨⌊(x.1 + c / 2) / c⌋, ?_⟩
  have h1 : ((⌊(x.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ (x.1 + c / 2) / c := Int.floor_le _
  have h2 : (x.1 + c / 2) / c < ((⌊(x.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  have h3 : (((⌊(x.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1) * c =
      ((⌊(x.1 + c / 2) / c⌋ : ℤ) : ℝ) * c + c := by ring
  rw [h3] at h2
  simp only [perTile, mem_prod, mem_Ico, mem_univ, and_true]
  constructor <;> linarith

/-- Periodic fields of `X_{-m,c}` are a.e. strongly measurable on the plane. -/
theorem perField_aesm {c m : ℝ} {f : ℝ × ℝ → ℂ} (hc : 0 < c)
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    AEStronglyMeasurable f volume := by
  have hfv : AEStronglyMeasurable f (volume.restrict (B0579.cell c)) :=
    hf.1.mono_ac (B0579.ac_cellMeasure c (-m))
  rw [← Measure.restrict_univ (μ := volume), ← perTile_cover c hc]
  exact aestronglyMeasurable_iUnion_iff.2 (fun k => perTile_aesm hper hfv k)

/-- The weight `⟨x⟩^{-m}` is bounded below by `1/C` on the set where `⟨x⟩^m ≤ C`. -/
theorem density_lower_bound {m C : ℝ} {S : Set (ℝ × ℝ)} (hS : ∀ x ∈ S, B0579.jb x ^ m ≤ C)
    (x : ℝ × ℝ) (hx : x ∈ S) (hC : 0 ≤ C) : 1 ≤ C * B0579.jb x ^ (-m) := by
  have hpos : 0 < B0579.jb x ^ (-m) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
  have hprod := B0579.jb_rpow_mul x (-m) m
  rw [show -m + m = 0 by ring, Real.rpow_zero] at hprod
  have h1 := hS x hx
  have h2 : 1 ≤ B0579.jb x ^ (-m) * C := by
    calc (1 : ℝ) = B0579.jb x ^ (-m) * B0579.jb x ^ m := hprod.symm
      _ ≤ B0579.jb x ^ (-m) * C := mul_le_mul_of_nonneg_left h1 hpos.le
  linarith [mul_comm (B0579.jb x ^ (-m)) C]

/-- Restriction of the cell measure: on a subset of the cell, Lebesgue measure is dominated by
`C` times `cellMeasure c (-m)`, once the density is bounded below by `1/C`. -/
theorem restrict_le_cellMeasure {c m C : ℝ} (hC : 0 ≤ C) {S : Set (ℝ × ℝ)}
    (hSm : MeasurableSet S) (hS : S ⊆ B0579.cell c)
    (hD : ∀ x ∈ S, 1 ≤ C * B0579.jb x ^ (-m)) :
    volume.restrict S ≤ ENNReal.ofReal C • B0579.cellMeasure c (-m) := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.restrict_apply' hSm, Measure.smul_apply, smul_eq_mul, B0579.cellMeasure,
    withDensity_apply _ hA, Measure.restrict_restrict hA]
  calc volume (A ∩ S) = ∫⁻ _ in A ∩ S, 1 := by rw [setLIntegral_const, one_mul]
    _ ≤ ∫⁻ x in A ∩ S, ENNReal.ofReal C * ((B0579.density (-m) x : NNReal) : ℝ≥0∞) := by
      refine setLIntegral_mono' (hA.inter hSm) (fun x hx => ?_)
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
        _ ≤ ENNReal.ofReal (C * B0579.jb x ^ (-m)) := ENNReal.ofReal_le_ofReal (hD x hx.2)
        _ = ENNReal.ofReal C * ENNReal.ofReal (B0579.jb x ^ (-m)) :=
          ENNReal.ofReal_mul hC
        _ = ENNReal.ofReal C * ((B0579.density (-m) x : NNReal) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal, B0579.coe_density]
    _ = ENNReal.ofReal C * ∫⁻ x in A ∩ S, ((B0579.density (-m) x : NNReal) : ℝ≥0∞) :=
      lintegral_const_mul _ ((B0579.measurable_density (-m)).coe_nnreal_ennreal)
    _ ≤ ENNReal.ofReal C * ∫⁻ x in A ∩ B0579.cell c, ((B0579.density (-m) x : NNReal) : ℝ≥0∞) :=
      by gcongr

/-- The base piece: `f ∈ L¹` on `cell ∩ (ℝ × [-ρ, ρ])`, from `f ∈ L²(cellMeasure)` and the lower bound
of the weight on the bounded band. -/
theorem perBase_integrableOn {c m ρ : ℝ} (f : ℝ × ℝ → ℂ)
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn f (B0579.cell c ∩ (univ ×ˢ Icc (-ρ) ρ)) volume := by
  set S := B0579.cell c ∩ (univ ×ˢ Icc (-ρ) ρ) with hSdef
  set box' : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-ρ) ρ with hbox
  have hbox_c : IsCompact box' := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hbox_c.exists_bound_of_continuousOn
    (B0579.continuous_jb_rpow m).continuousOn
  set C' := max C 1 with hC'
  have hC'0 : 0 ≤ C' := zero_le_one.trans (le_max_right _ _)
  have hC2 : ∀ y ∈ box', B0579.jb y ^ m ≤ C' := fun y hy => by
    have h := hC y hy
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_max_left _ _))
  have hSsub : S ⊆ box' := fun x hx => ⟨Ico_subset_Icc_self hx.1.1, hx.2.2⟩
  have hSm : MeasurableSet S :=
    (B0579.measurableSet_cell c).inter (MeasurableSet.univ.prod measurableSet_Icc)
  have hD : ∀ x ∈ S, 1 ≤ C' * B0579.jb x ^ (-m) := fun x hx =>
    density_lower_bound (fun y hy => hC2 y (hSsub hy)) x hx hC'0
  have hmeas : volume.restrict S ≤ ENNReal.ofReal C' • B0579.cellMeasure c (-m) :=
    restrict_le_cellMeasure hC'0 hSm inter_subset_left hD
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hSsub).trans_lt hbox_c.measure_lt_top⟩
  have hL2 : MemLp f 2 (volume.restrict S) :=
    (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hmeas
  exact hL2.integrable one_le_two

theorem perTile_integrableOn {c m ρ : ℝ} {f : ℝ × ℝ → ℂ} (hc : 0 < c)
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (k : ℤ) :
    IntegrableOn f (perTile c k ∩ (univ ×ˢ Icc (-ρ) ρ)) volume := by
  have hset : perTile c k ∩ (univ ×ˢ Icc (-ρ) ρ) =
      (fun g : ℝ × ℝ => g - ((k : ℝ) * c, 0)) ⁻¹' (B0579.cell c ∩ (univ ×ˢ Icc (-ρ) ρ)) := by
    ext x
    simp only [perTile, mem_inter_iff, mem_prod, mem_Ico, mem_univ, true_and, mem_preimage,
      B0579.cell, Prod.fst_sub, Prod.snd_sub, sub_zero]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, trivial⟩, h3⟩
    · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, trivial⟩, h3⟩
  rw [hset]
  have hint := (measurePreserving_sub_right volume ((k : ℝ) * c, 0)).integrableOn_comp_preimage
    (measurableEmbedding_subRight ((k : ℝ) * c, 0))
    (f := f) (s := B0579.cell c ∩ (univ ×ˢ Icc (-ρ) ρ))
  have h2 := hint.2 (perBase_integrableOn f hf)
  rwa [perTile_shift hper k] at h2

theorem perBox_cover (c ρ : ℝ) (hc : 0 < c) :
    Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ ⊆
      ⋃ k ∈ Finset.Icc (-(⌈(ρ + c) / c⌉ + 1)) (⌈(ρ + c) / c⌉ + 1),
        (perTile c k ∩ (univ ×ˢ Icc (-ρ) ρ)) := by
  rintro x ⟨⟨hx1a, hx1b⟩, ⟨hx2a, hx2b⟩⟩
  set M : ℤ := ⌈(ρ + c) / c⌉ with hM
  set k : ℤ := ⌊(x.1 + c / 2) / c⌋ with hk
  have h1 : (k : ℝ) * c ≤ x.1 + c / 2 := by
    have := Int.floor_le ((x.1 + c / 2) / c)
    rw [le_div_iff₀ hc] at this
    exact this
  have h2 : x.1 + c / 2 < (k : ℝ) * c + c := by
    have := Int.lt_floor_add_one ((x.1 + c / 2) / c)
    rw [div_lt_iff₀ hc] at this
    linarith
  have hMc : ρ + c ≤ (M : ℝ) * c := by
    have := Int.le_ceil ((ρ + c) / c)
    rw [div_le_iff₀ hc] at this
    exact this
  have hkM : (k : ℝ) < M := by
    have : (k : ℝ) * c < (M : ℝ) * c := by linarith
    exact lt_of_mul_lt_mul_right this hc.le
  have hMk : -(M : ℝ) < k := by
    have : -(M : ℝ) * c < (k : ℝ) * c := by linarith
    exact lt_of_mul_lt_mul_right this hc.le
  have hkM' : k ≤ M := by exact_mod_cast hkM.le
  have hMk' : -M < k := by exact_mod_cast hMk
  exact mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 ⟨by omega, by omega⟩,
    ⟨⟨⟨by linarith, by linarith⟩, trivial⟩, trivial, hx2a, hx2b⟩⟩

theorem cellPeriodicLocInt : CellPeriodicLocInt := by
  intro c m f hc hper hf
  refine ⟨perField_aesm hc hper hf, ?_⟩
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 hK.isBounded
  have hKB : K ⊆ Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ := by
    intro x hx
    have hn : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.1 (hρ hx)
    have h1 : ‖x.1‖ ≤ ρ := (norm_fst_le x).trans hn
    have h2 : ‖x.2‖ ≤ ρ := (norm_snd_le x).trans hn
    rw [Real.norm_eq_abs] at h1 h2
    exact ⟨abs_le.1 h1, abs_le.1 h2⟩
  have hU : IntegrableOn f (⋃ k ∈ Finset.Icc (-(⌈(ρ + c) / c⌉ + 1)) (⌈(ρ + c) / c⌉ + 1),
      (perTile c k ∩ (univ ×ˢ Icc (-ρ) ρ))) volume :=
    integrableOn_finset_iUnion.2 (fun k _ => perTile_integrableOn (ρ := ρ) hc hper hf k)
  exact IntegrableOn.mono_set hU (hKB.trans (perBox_cover c ρ hc))

end UnforcedLeray.Short.IIIa
