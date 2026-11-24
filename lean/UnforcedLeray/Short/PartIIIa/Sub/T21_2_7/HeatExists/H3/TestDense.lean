import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Units.B0656.Sobolev
import UnforcedLeray.Units.B0579
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/3/2`: (H3.2) complexified cylinder tests are dense in `X_{-m,c}`

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050.  Statement: `HeatExists/Leaves.lean` (`AdjCylTestDense`).

Route: smooth compactly supported functions are dense in `L²(μ)`, `μ = cellMeasure c (-m)`
(`Lp.dense_hasCompactSupport_contDiff`).  For such `f`, the cut-off `χ_n(q) f` with
`χ_n(q) = smoothTransition((n+1)(c²/4 - q²) - 1)` has support in the open cell and tends to `f`
in `L²(μ)` (dominated convergence; the seams `q = ±c/2` are `μ`-null).  A function `h` smooth with
compact support in the open cell periodizes (`B0656.periodize`) to a cylinder test agreeing with
`h` on the cell, and its real and imaginary parts give an element of `IsCylTestC`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The `q`-cut-off -/

/-- The smooth cut-off in `q` at level `n`: `1` for `q² ≤ c²/4 - 2/(n+1)`, `0` for
`q² ≥ c²/4 - 1/(n+1)`. -/
def tdCut (c : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * (c ^ 2 / 4 - q ^ 2) - 1)

theorem tdCut_contDiff (c : ℝ) (n : ℕ) : ContDiff ℝ ∞ (tdCut c n) := by
  unfold tdCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem tdCut_continuous (c : ℝ) (n : ℕ) : Continuous (tdCut c n) :=
  (tdCut_contDiff c n).continuous

theorem tdCut_nonneg (c : ℝ) (n : ℕ) (q : ℝ) : 0 ≤ tdCut c n q :=
  Real.smoothTransition.nonneg _

theorem tdCut_le_one (c : ℝ) (n : ℕ) (q : ℝ) : tdCut c n q ≤ 1 :=
  Real.smoothTransition.le_one _

theorem tdCut_eq_one {c : ℝ} {n : ℕ} {q : ℝ}
    (h : q ^ 2 ≤ c ^ 2 / 4 - 2 / ((n : ℝ) + 1)) : tdCut c n q = 1 := by
  unfold tdCut
  apply Real.smoothTransition.one_of_one_le
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 2 / ((n : ℝ) + 1) ≤ c ^ 2 / 4 - q ^ 2 := by linarith
  have h3 : 2 ≤ ((n : ℝ) + 1) * (c ^ 2 / 4 - q ^ 2) := by
    calc (2 : ℝ) = ((n : ℝ) + 1) * (2 / ((n : ℝ) + 1)) := by field_simp
      _ ≤ ((n : ℝ) + 1) * (c ^ 2 / 4 - q ^ 2) := mul_le_mul_of_nonneg_left h2 hN.le
  linarith

theorem tdCut_eq_zero_of {c : ℝ} {n : ℕ} {q : ℝ}
    (h : c ^ 2 / 4 - 1 / ((n : ℝ) + 1) ≤ q ^ 2) : tdCut c n q = 0 := by
  unfold tdCut
  apply Real.smoothTransition.zero_of_nonpos
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : ((n : ℝ) + 1) * (c ^ 2 / 4 - q ^ 2) ≤ 1 := by
    calc ((n : ℝ) + 1) * (c ^ 2 / 4 - q ^ 2) ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hN.le
      _ = 1 := by field_simp
  linarith

/-- The support of the `q`-cut-off lies in the open centered cell. -/
theorem tdCut_tsupport_sub {c : ℝ} (hc : 0 < c) (n : ℕ) :
    tsupport (fun z : ℝ × ℝ => (tdCut c n z.1 : ℂ)) ⊆ UnforcedLeray.B0656.cell c := by
  have hS : IsClosed {z : ℝ × ℝ | z.1 ^ 2 ≤ c ^ 2 / 4 - 1 / ((n : ℝ) + 1)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsupp : Function.support (fun z : ℝ × ℝ => (tdCut c n z.1 : ℂ)) ⊆
      {z : ℝ × ℝ | z.1 ^ 2 ≤ c ^ 2 / 4 - 1 / ((n : ℝ) + 1)} := by
    intro z hz
    by_contra hcon
    apply hz
    have hlt : c ^ 2 / 4 - 1 / ((n : ℝ) + 1) ≤ z.1 ^ 2 := by
      simp only [Set.mem_setOf_eq, not_le] at hcon
      linarith
    have : tdCut c n z.1 = 0 := tdCut_eq_zero_of hlt
    simp [this]
  refine (closure_minimal hsupp hS).trans ?_
  intro z hz
  have hN : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h1 : z.1 ^ 2 < (c / 2) ^ 2 := by
    have := hz
    simp only [Set.mem_setOf_eq] at this
    nlinarith
  have h2 := abs_lt_of_sq_lt_sq h1 (by positivity)
  obtain ⟨h3, h4⟩ := abs_lt.1 h2
  exact ⟨⟨h3, h4⟩, Set.mem_univ _⟩

/-! ## Cylinder tests from compact support in the open cell -/

/-- A smooth function with compact support in the open cell is a cylinder test (complexified)
agreeing with itself on the cell. -/
theorem td_cyl_of_compact {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hcs : HasCompactSupport h) (hsub : tsupport h ⊆ UnforcedLeray.B0656.cell c) :
    ∃ g : ℝ × ℝ → ℂ, IsCylTestC c g ∧ ∀ z ∈ UnforcedLeray.B0656.cell c, g z = h z := by
  have hre : ContDiff ℝ ∞ (fun z => (h z).re) := Complex.reCLM.contDiff.comp hh
  have him : ContDiff ℝ ∞ (fun z => (h z).im) := Complex.imCLM.contDiff.comp hh
  have hcre : HasCompactSupport (fun z => (h z).re) := hcs.comp_left (g := Complex.re) rfl
  have hcim : HasCompactSupport (fun z => (h z).im) := hcs.comp_left (g := Complex.im) rfl
  have hsre : tsupport (fun z => (h z).re) ⊆ UnforcedLeray.B0656.cell c :=
    (tsupport_comp_subset (g := Complex.re) rfl h).trans hsub
  have hsim : tsupport (fun z => (h z).im) ⊆ UnforcedLeray.B0656.cell c :=
    (tsupport_comp_subset (g := Complex.im) rfl h).trans hsub
  have P1 := UnforcedLeray.B0656.isPeriodicTest_periodize hc hre hcre hsre
  have P2 := UnforcedLeray.B0656.isPeriodicTest_periodize hc him hcim hsim
  have t1 : UnforcedLeray.B0579.IsCylTest c (UnforcedLeray.B0656.periodize hc (fun z => (h z).re)) :=
    ⟨P1.smooth, fun x => P1.periodic x.1 x.2, P1.bounded⟩
  have t2 : UnforcedLeray.B0579.IsCylTest c (UnforcedLeray.B0656.periodize hc (fun z => (h z).im)) :=
    ⟨P2.smooth, fun x => P2.periodic x.1 x.2, P2.bounded⟩
  refine ⟨fun z => ((UnforcedLeray.B0656.periodize hc (fun z => (h z).re) z : ℝ) : ℂ) +
    Complex.I * ((UnforcedLeray.B0656.periodize hc (fun z => (h z).im) z : ℝ) : ℂ),
    ⟨_, _, t1, t2, rfl⟩, ?_⟩
  intro z hz
  have e1 := UnforcedLeray.B0656.periodize_eq_on_cell hc (fun z => (h z).re) hz
  have e2 := UnforcedLeray.B0656.periodize_eq_on_cell hc (fun z => (h z).im) hz
  show ((UnforcedLeray.B0656.periodize hc (fun z => (h z).re) z : ℝ) : ℂ) +
    Complex.I * ((UnforcedLeray.B0656.periodize hc (fun z => (h z).im) z : ℝ) : ℂ) = h z
  rw [e1, e2, mul_comm Complex.I]
  exact Complex.re_add_im (h z)

/-! ## The null seams and the finiteness of the cell measure -/

theorem td_cell_lt_top {c m : ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    UnforcedLeray.B0579.cellMeasure c m K < ⊤ := by
  have hcont : ContinuousOn (fun x : ℝ × ℝ => UnforcedLeray.B0579.jb x ^ m) K :=
    (UnforcedLeray.B0579.continuous_jb_rpow m).continuousOn
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hcont).bddAbove
  rw [UnforcedLeray.B0579.cellMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, (UnforcedLeray.B0579.density m x : ℝ≥0∞)
        ∂(volume.restrict (UnforcedLeray.B0579.cell c))
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂(volume.restrict (UnforcedLeray.B0579.cell c)) := by
        refine setLIntegral_mono' hK.measurableSet (fun x hx => ?_)
        show ENNReal.ofReal (UnforcedLeray.B0579.jb x ^ m) ≤ ENNReal.ofReal C
        exact ENNReal.ofReal_le_ofReal (hC (Set.mem_image_of_mem _ hx))
    _ = ENNReal.ofReal C * (volume.restrict (UnforcedLeray.B0579.cell c)) K :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)

/-- The cell measure is finite on compact sets. -/
instance td_isFiniteMeasureOnCompacts (c m : ℝ) :
    IsFiniteMeasureOnCompacts (UnforcedLeray.B0579.cellMeasure c m) :=
  ⟨fun _ hK => td_cell_lt_top hK⟩


/-- The `μ`-a.e. point lies in the open cell `(-c/2, c/2) × ℝ`: the seam `q = -c/2` and the
complement of the cell are `μ`-null. -/
theorem td_ae_mem_cell (c m : ℝ) :
    ∀ᵐ z ∂(UnforcedLeray.B0579.cellMeasure c m), z ∈ UnforcedLeray.B0656.cell c := by
  rw [ae_iff]
  have hA : (volume.restrict (UnforcedLeray.B0579.cell c))
      ((UnforcedLeray.B0579.cell c)ᶜ) = 0 := by
    rw [Measure.restrict_apply' (UnforcedLeray.B0579.measurableSet_cell c), compl_inter_self,
      measure_empty]
  have hA' : UnforcedLeray.B0579.cellMeasure c m ((UnforcedLeray.B0579.cell c)ᶜ) = 0 :=
    UnforcedLeray.B0579.cellMeasure_ac c m hA
  have hL : (volume : Measure (ℝ × ℝ)) {z : ℝ × ℝ | z.1 = -(c / 2)} = 0 := by
    have : {z : ℝ × ℝ | z.1 = -(c / 2)} = ({-(c / 2)} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext z
      simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hB : UnforcedLeray.B0579.cellMeasure c m {z : ℝ × ℝ | z.1 = -(c / 2)} = 0 := by
    apply UnforcedLeray.B0579.cellMeasure_ac c m
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans hL.le) zero_le
  have hsub : {z : ℝ × ℝ | ¬ z ∈ UnforcedLeray.B0656.cell c} ⊆
      (UnforcedLeray.B0579.cell c)ᶜ ∪ {z : ℝ × ℝ | z.1 = -(c / 2)} := by
    intro z hz
    by_cases h1 : z.1 = -(c / 2)
    · exact Or.inr h1
    · left
      intro hmem
      apply hz
      exact ⟨⟨lt_of_le_of_ne hmem.1.1 (Ne.symm h1), hmem.1.2⟩, Set.mem_univ _⟩
  exact measure_mono_null hsub (measure_union_null hA' hB)

/-! ## Cut-off approximation in `L²(μ)` -/

/-- The cut-off approximant `χ_n(q) h(z)`. -/
def tdH (c : ℝ) (f : ℝ × ℝ → ℂ) (n : ℕ) : ℝ × ℝ → ℂ :=
  fun z => ((tdCut c n z.1 : ℝ) : ℂ) * f z

/-- The residual `f - χ_n f`. -/
def tdRes (c : ℝ) (f : ℝ × ℝ → ℂ) (n : ℕ) : ℝ × ℝ → ℂ :=
  fun z => f z - tdH c f n z

theorem tdH_continuous {c : ℝ} {f : ℝ × ℝ → ℂ} (hfc : Continuous f) (n : ℕ) :
    Continuous (tdH c f n) :=
  (Complex.continuous_ofReal.comp ((tdCut_continuous c n).comp continuous_fst)).mul hfc

theorem tdH_contDiff {c : ℝ} {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (tdH c f n) :=
  (Complex.ofRealCLM.contDiff.comp ((tdCut_contDiff c n).comp contDiff_fst)).mul hf

theorem tdH_hasCompactSupport {c : ℝ} {f : ℝ × ℝ → ℂ} (hfs : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (tdH c f n) :=
  hfs.mul_left

theorem tdH_tsupport {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (n : ℕ) :
    tsupport (tdH c f n) ⊆ UnforcedLeray.B0656.cell c :=
  (tsupport_mul_subset_left).trans (tdCut_tsupport_sub hc n)

/-- **Cut-off convergence in `L²(μ)`.** For `f` continuous with compact support and `μ`-a.e. point
in the open cell, the residual `f - χ_n f` tends to `0` in `L²(μ)`. -/
theorem td_tendsto_res {c : ℝ} {μ : Measure (ℝ × ℝ)}
    (hcell : ∀ᵐ z ∂μ, z.1 ∈ Ioo (-(c / 2)) (c / 2)) {f : ℝ × ℝ → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) (hfL : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => eLpNorm (tdRes c f n) 2 μ) atTop (𝓝 0) := by
  have hEq : ∀ G : ℝ × ℝ → ℂ, eLpNorm G 2 μ = (∫⁻ z, ‖G z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    intro G
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    norm_num
  have hfin : ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    have h := hfL.2
    rw [hEq f] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h).ne
  have hlin : Tendsto (fun n : ℕ => ∫⁻ z, ‖tdRes c f n z‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have hdom := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun (n : ℕ) (z : ℝ × ℝ) => ‖tdRes c f n z‖ₑ ^ (2 : ℝ))
      (f := fun _ => (0 : ℝ≥0∞)) (fun z => ‖f z‖ₑ ^ (2 : ℝ))
      (fun n => ((continuous_enorm.comp (hfc.sub (tdH_continuous hfc n))).measurable).pow_const _)
      (fun n => Eventually.of_forall fun z => ?_) hfin ?_
    · simpa using hdom
    · -- pointwise domination
      have hle : ‖tdRes c f n z‖ₑ ≤ ‖f z‖ₑ := by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        apply ENNReal.ofReal_le_ofReal
        have e : tdRes c f n z = ((1 - tdCut c n z.1 : ℝ) : ℂ) * f z := by
          simp only [tdRes, tdH]
          push_cast
          ring
        rw [e, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.2 (tdCut_le_one c n z.1))]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [tdCut_nonneg c n z.1])
      exact ENNReal.rpow_le_rpow hle (by norm_num)
    · filter_upwards [hcell] with z hz
      have hd : 0 < c ^ 2 / 4 - z.1 ^ 2 := by
        nlinarith [hz.1, hz.2]
      have ht : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
        rw [mul_zero] at this
        exact this
      have hev : ∀ᶠ n : ℕ in atTop, tdCut c n z.1 = 1 := by
        filter_upwards [ht.eventually (gt_mem_nhds hd)] with n hn
        apply tdCut_eq_one
        have e : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
        linarith
      have hz0 : ∀ᶠ n : ℕ in atTop, ‖tdRes c f n z‖ₑ ^ (2 : ℝ) = 0 := by
        filter_upwards [hev] with n hn
        simp [tdRes, tdH, hn]
      exact tendsto_const_nhds.congr' (hz0.mono fun n hn => hn.symm)
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0 |>.comp hlin
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hpow
  have e : (fun n : ℕ => eLpNorm (tdRes c f n) 2 μ) =
      fun n : ℕ => (∫⁻ z, ‖tdRes c f n z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
    funext fun n => hEq (tdRes c f n)
  rw [e]
  exact hpow

/-- **(H3.2) Complexified cylinder tests are dense in `X_{-m,c}`** (SP 2819-2836). -/
theorem adjCylTestDense (m : ℝ) (hm : 8 < m) : AdjCylTestDense m := by
  intro c hc
  intro w
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v0, ⟨f, hfv, hfc, hfs⟩, hd0⟩ :=
    (Lp.dense_hasCompactSupport_contDiff (μ := UnforcedLeray.B0579.cellMeasure c (-m))
      (p := 2) (by norm_num)).exists_dist_lt w (half_pos hε)
  have hfcont : Continuous f := hfs.continuous
  have hfL : MemLp f 2 (UnforcedLeray.B0579.cellMeasure c (-m)) :=
    hfcont.memLp_of_hasCompactSupport hfc
  have hcell : ∀ᵐ z ∂(UnforcedLeray.B0579.cellMeasure c (-m)), z.1 ∈ Ioo (-(c / 2)) (c / 2) :=
    (td_ae_mem_cell c (-m)).mono fun z hz => (Set.mem_prod.1 hz).1
  have hT := td_tendsto_res hcell hfcont hfc hfL
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (half_pos hε)
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds hε2)).exists
  have hHL : MemLp (tdH c f n) 2 (UnforcedLeray.B0579.cellMeasure c (-m)) :=
    (tdH_continuous hfcont n).memLp_of_hasCompactSupport (tdH_hasCompactSupport hfc n)
  obtain ⟨g, hg, hgeq⟩ := td_cyl_of_compact hc (tdH_contDiff hfs n)
    (tdH_hasCompactSupport hfc n) (tdH_tsupport hc n)
  have hg_ae : g =ᵐ[UnforcedLeray.B0579.cellMeasure c (-m)] tdH c f n :=
    (td_ae_mem_cell c (-m)).mono fun z hz => hgeq z hz
  have hgL : MemLp g 2 (UnforcedLeray.B0579.cellMeasure c (-m)) := hHL.ae_eq hg_ae.symm
  refine ⟨hgL.toLp g, ⟨g, hg, hgL.coeFn_toLp⟩, ?_⟩
  have hdist_vg : dist v0 (hgL.toLp g) < ε / 2 := by
    rw [Lp.dist_def]
    apply ENNReal.toReal_lt_of_lt_ofReal
    have e : eLpNorm (⇑v0 - ⇑(hgL.toLp g)) 2 (UnforcedLeray.B0579.cellMeasure c (-m)) =
        eLpNorm (tdRes c f n) 2 (UnforcedLeray.B0579.cellMeasure c (-m)) := by
      apply eLpNorm_congr_ae
      filter_upwards [hfv, hgL.coeFn_toLp, hg_ae] with z h1 h2 h3
      simp only [Pi.sub_apply, tdRes]
      rw [h1, h2, h3]
    rw [e]
    exact hn
  have htri := dist_triangle w v0 (hgL.toLp g)
  linarith

end UnforcedLeray.Short.IIIa
