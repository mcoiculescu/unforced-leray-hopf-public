import UnforcedLeray.Short.PartIIIa.Sub.T18_2_3
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Part III-a, task `PartIII-a:T18/2/3/3`: proof of `NiceSmoothDensity`

Source of record: `the November 2 reference manuscript`, lines 3427-3440.

Route. The entries of `F` lie in `L²` because `‖F i j‖ ≤ tnorm2 (F ·)`. Mathlib's
`MeasureTheory.MemLp.exist_eLpNorm_sub_le` gives smooth compactly supported approximants `g_ij`
of the three independent entries `F₀₀, F₀₁, F₁₁` with error `ε/8` each. The approximant of the
symmetric field is `G = χ · g`, where `χ` is a product of three one-dimensional smooth cutoffs,
equal to `1` on the box `α ≤ s ≤ β`, `|q| ≤ r`, `|η| ≤ R` (which contains the support of `F`),
and vanishing outside the enlarged box. Since `F = χ F`, the entrywise error `G - F = χ (g - F)`
is bounded by `g - F`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- One-dimensional smooth cutoff: equal to `1` on `[a, b]`, with values in `[0, 1]`, and
vanishing for `x ≤ a'` or `x ≥ b'`. -/
theorem niceSD_cutoff1 {a a' b b' : ℝ} (ha : a' < a) (hab : a ≤ b) (hb : b < b') :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x, a ≤ x → x ≤ b → ψ x = 1) ∧ (∀ x, x ≤ a' ∨ b' ≤ x → ψ x = 0) := by
  have hpos1 : 0 < a - a' := by linarith
  have hpos2 : 0 < b' - b := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (a - a') (b' - b) / 4 := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    exact div_pos (lt_min hpos1 hpos2) (by norm_num)
  have hη1 : 4 * η ≤ a - a' := by
    rw [hηdef]
    have := min_le_left (a - a') (b' - b)
    linarith
  have hη2 : 4 * η ≤ b' - b := by
    rw [hηdef]
    have := min_le_right (a - a') (b' - b)
    linarith
  let f : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 2 + η
      rOut := (b - a) / 2 + 2 * η
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨f, f.contDiff, fun x => ⟨f.nonneg, f.le_one⟩, ?_, ?_⟩
  · intro x hx1 hx2
    apply f.one_of_mem_closedBall
    show x ∈ Metric.closedBall ((a + b) / 2) ((b - a) / 2 + η)
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith
  · intro x hx
    apply f.zero_of_le_dist
    show (b - a) / 2 + 2 * η ≤ dist x ((a + b) / 2)
    rw [Real.dist_eq]
    rcases hx with hx | hx
    · linarith [neg_le_abs (x - (a + b) / 2)]
    · linarith [le_abs_self (x - (a + b) / 2)]

theorem niceSD_tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T :=
  Real.sqrt_nonneg _

/-- A single entry is bounded by the Frobenius norm. -/
theorem niceSD_entry_le (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) : ‖T i j‖ ≤ ‖tnorm2 T‖ := by
  rw [Real.norm_of_nonneg (niceSD_tnorm2_nonneg T)]
  unfold tnorm2
  have h1 : ‖T i j‖ ^ 2 ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, ‖T i' j'‖ ^ 2 := by
    calc ‖T i j‖ ^ 2 ≤ ∑ j' : Fin 2, ‖T i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' : Fin 2 => ‖T i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2, ‖T i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' : Fin 2 => ∑ j' : Fin 2, ‖T i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖T i j‖ = Real.sqrt (‖T i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i' : Fin 2, ∑ j' : Fin 2, ‖T i' j'‖ ^ 2) := Real.sqrt_le_sqrt h1

/-- The Frobenius norm is bounded by the sum of the moduli of the entries. -/
theorem niceSD_tnorm2_le (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ≤ ‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖ := by
  have hA : 0 ≤ ‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖ := by positivity
  have hsq : ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 ≤
      (‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖) ^ 2 := by
    simp only [Fin.sum_univ_two]
    nlinarith [mul_nonneg (norm_nonneg (T 0 0)) (norm_nonneg (T 0 1)),
      mul_nonneg (norm_nonneg (T 0 0)) (norm_nonneg (T 1 0)),
      mul_nonneg (norm_nonneg (T 0 0)) (norm_nonneg (T 1 1)),
      mul_nonneg (norm_nonneg (T 0 1)) (norm_nonneg (T 1 0)),
      mul_nonneg (norm_nonneg (T 0 1)) (norm_nonneg (T 1 1)),
      mul_nonneg (norm_nonneg (T 1 0)) (norm_nonneg (T 1 1))]
  unfold tnorm2
  calc Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2)
      ≤ Real.sqrt ((‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖T 0 0‖ + ‖T 0 1‖ + ‖T 1 0‖ + ‖T 1 1‖ := Real.sqrt_sq hA

theorem niceSD_measurable_tnorm2 (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hF : ∀ i j, Measurable fun p => F p i j) : Measurable fun p => tnorm2 (F p) := by
  unfold tnorm2
  simp only [Fin.sum_univ_two]
  have h00 := (hF 0 0).norm.pow_const 2
  have h01 := (hF 0 1).norm.pow_const 2
  have h10 := (hF 1 0).norm.pow_const 2
  have h11 := (hF 1 1).norm.pow_const 2
  exact ((h00.add h01).add (h10.add h11)).sqrt

/-- Each entry of a field of finite `𝒯`-type `L²` norm is in `L²(ℝ³)`. -/
theorem niceSD_memLp_entry (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hF : ∀ i j, Measurable fun p => F p i j)
    (hfin : eLpNorm (fun p => tnorm2 (F p)) 2 (volume : Measure (ℝ × (ℝ × ℝ))) < ⊤)
    (i j : Fin 2) : MemLp (fun p => F p i j) 2 (volume : Measure (ℝ × (ℝ × ℝ))) := by
  have hT : MemLp (fun p => tnorm2 (F p)) 2 (volume : Measure (ℝ × (ℝ × ℝ))) :=
    ⟨(niceSD_measurable_tnorm2 F hF).aestronglyMeasurable, hfin⟩
  exact MemLp.of_le hT (hF i j).aestronglyMeasurable
    (Eventually.of_forall fun p => niceSD_entry_le (F p) i j)

/-- Smooth compactly supported approximation of a scalar `L²` function. -/
theorem niceSD_approx_scalar (f : ℝ × (ℝ × ℝ) → ℂ)
    (hf : MemLp f 2 (volume : Measure (ℝ × (ℝ × ℝ)))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℝ × (ℝ × ℝ) → ℂ, ContDiff ℝ ∞ g ∧
      eLpNorm (f - g) 2 (volume : Measure (ℝ × (ℝ × ℝ))) ≤ ENNReal.ofReal δ := by
  obtain ⟨g, -, hg, hgl⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hf hδ
  exact ⟨g, hg, hgl⟩

/-- Pointwise bound: `G - F = c (g - F)` with `0 ≤ c ≤ 1` and `F = c F`. -/
theorem niceSD_D_le (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) (Gv Fv gv : ℂ)
    (hcut : Fv = (c : ℂ) * Fv) (hG : Gv = (c : ℂ) * gv) : ‖Gv - Fv‖ ≤ ‖Fv - gv‖ := by
  have e : Gv - Fv = (c : ℂ) * (gv - Fv) := by
    rw [hG, mul_sub, ← hcut]
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_sub_rev Fv gv]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- Four-term Minkowski inequality in `L²`. -/
theorem niceSD_eLpNorm_four {f₁ f₂ f₃ f₄ : ℝ × (ℝ × ℝ) → ℝ} (h₁ : Measurable f₁)
    (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄) :
    eLpNorm (fun p => f₁ p + f₂ p + f₃ p + f₄ p) 2 (volume : Measure (ℝ × (ℝ × ℝ))) ≤
      eLpNorm f₁ 2 (volume : Measure (ℝ × (ℝ × ℝ))) + eLpNorm f₂ 2 (volume : Measure (ℝ × (ℝ × ℝ)))
        + eLpNorm f₃ 2 (volume : Measure (ℝ × (ℝ × ℝ)))
        + eLpNorm f₄ 2 (volume : Measure (ℝ × (ℝ × ℝ))) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have step : ∀ g h : ℝ × (ℝ × ℝ) → ℝ, Measurable g → Measurable h →
      eLpNorm (fun p => g p + h p) 2 (volume : Measure (ℝ × (ℝ × ℝ))) ≤
        eLpNorm g 2 (volume : Measure (ℝ × (ℝ × ℝ))) + eLpNorm h 2 (volume : Measure (ℝ × (ℝ × ℝ))) :=
    fun g h hg hh => eLpNorm_add_le hg.aestronglyMeasurable hh.aestronglyMeasurable hp
  have s12 := step f₁ f₂ h₁ h₂
  have s123 := step (fun p => f₁ p + f₂ p) f₃ (h₁.add h₂) h₃
  have s1234 := step (fun p => f₁ p + f₂ p + f₃ p) f₄ ((h₁.add h₂).add h₃) h₄
  exact s1234.trans (add_le_add (s123.trans (add_le_add s12 le_rfl)) le_rfl)

theorem niceSmoothDensity : NiceSmoothDensity := by
  intro α β r r' R hα hrr' F hsym hmeas hvan hfin ε hε
  by_cases hall : ∀ p i j, F p i j = 0
  · refine ⟨fun _ _ _ => 0, fun _ _ _ => rfl, fun i j => contDiff_const, fun _ _ _ _ _ => rfl, ?_⟩
    simp [hall, tnorm2, hε]
  · simp only [not_forall] at hall
    obtain ⟨p₀, i₀, j₀, hp₀⟩ := hall
    have hbox : α ≤ p₀.1 ∧ p₀.1 ≤ β ∧ |p₀.2.1| ≤ r ∧ |p₀.2.2| ≤ R := by
      by_contra h
      apply hp₀
      apply hvan p₀.1 p₀.2 i₀ j₀
      simp only [not_and_or, not_le] at h
      exact h
    obtain ⟨hαp, hpβ, hq, hη⟩ := hbox
    have hαβ : α ≤ β := hαp.trans hpβ
    have hr0 : 0 ≤ r := (abs_nonneg _).trans hq
    have hR0 : 0 ≤ R := (abs_nonneg _).trans hη
    obtain ⟨ψs, hψs1, hψs2, hψs3, hψs4⟩ :=
      niceSD_cutoff1 (a := α) (a' := α / 2) (b := β) (b' := β + 1) (by linarith) hαβ (by linarith)
    obtain ⟨ψq, hψq1, hψq2, hψq3, hψq4⟩ :=
      niceSD_cutoff1 (a := -r) (a' := -r') (b := r) (b' := r') (by linarith) (by linarith) hrr'
    obtain ⟨ψη, hψη1, hψη2, hψη3, hψη4⟩ :=
      niceSD_cutoff1 (a := -R) (a' := -(R + 1)) (b := R) (b' := R + 1)
        (by linarith) (by linarith) (by linarith)
    obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ × (ℝ × ℝ) → ℝ, χ = fun p => ψs p.1 * (ψq p.2.1 * ψη p.2.2) :=
      ⟨_, rfl⟩
    have hχsm : ContDiff ℝ ∞ χ := by
      rw [hχdef]
      exact (hψs1.comp contDiff_fst).mul
        ((hψq1.comp (contDiff_fst.comp contDiff_snd)).mul
          (hψη1.comp (contDiff_snd.comp contDiff_snd)))
    have hχ01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1 := by
      intro p
      rw [hχdef]
      obtain ⟨a1, a2⟩ := hψs2 p.1
      obtain ⟨b1, b2⟩ := hψq2 p.2.1
      obtain ⟨c1, c2⟩ := hψη2 p.2.2
      exact ⟨mul_nonneg a1 (mul_nonneg b1 c1),
        mul_le_one₀ a2 (mul_nonneg b1 c1) (mul_le_one₀ b2 c1 c2)⟩
    have hχone : ∀ p : ℝ × (ℝ × ℝ), α ≤ p.1 → p.1 ≤ β → |p.2.1| ≤ r → |p.2.2| ≤ R → χ p = 1 := by
      intro p h1 h2 h3 h4
      obtain ⟨h3a, h3b⟩ := abs_le.mp h3
      obtain ⟨h4a, h4b⟩ := abs_le.mp h4
      rw [hχdef]
      show ψs p.1 * (ψq p.2.1 * ψη p.2.2) = 1
      simp only [hψs3 p.1 h1 h2, hψq3 p.2.1 h3a h3b, hψη3 p.2.2 h4a h4b, mul_one]
    have hχzero : ∀ s x, (s < α / 2 ∨ β + 1 < s ∨ r' < |x.1| ∨ R + 1 < |x.2|) → χ (s, x) = 0 := by
      intro s x h
      rw [hχdef]
      show ψs s * (ψq x.1 * ψη x.2) = 0
      rcases h with h | h | h | h
      · rw [hψs4 s (Or.inl h.le), zero_mul]
      · rw [hψs4 s (Or.inr h.le), zero_mul]
      · have hq' : x.1 ≤ -r' ∨ r' ≤ x.1 := by
          rcases le_total 0 x.1 with h0 | h0
          · rw [abs_of_nonneg h0] at h
            exact Or.inr h.le
          · rw [abs_of_nonpos h0] at h
            exact Or.inl (by linarith)
        rw [hψq4 x.1 hq', zero_mul, mul_zero]
      · have hη' : x.2 ≤ -(R + 1) ∨ R + 1 ≤ x.2 := by
          rcases le_total 0 x.2 with h0 | h0
          · rw [abs_of_nonneg h0] at h
            exact Or.inr h.le
          · rw [abs_of_nonpos h0] at h
            exact Or.inl (by linarith)
        rw [hψη4 x.2 hη', mul_zero, mul_zero]
    have hcut : ∀ p i j, F p i j = ((χ p : ℝ) : ℂ) * F p i j := by
      intro p i j
      by_cases hb : α ≤ p.1 ∧ p.1 ≤ β ∧ |p.2.1| ≤ r ∧ |p.2.2| ≤ R
      · simp [hχone p hb.1 hb.2.1 hb.2.2.1 hb.2.2.2]
      · have h0 : F p i j = 0 := by
          apply hvan p.1 p.2 i j
          simp only [not_and_or, not_le] at hb
          exact hb
        simp [h0]
    -- smooth approximants of the three independent entries
    have hf00 := niceSD_memLp_entry F hmeas hfin 0 0
    have hf01 := niceSD_memLp_entry F hmeas hfin 0 1
    have hf11 := niceSD_memLp_entry F hmeas hfin 1 1
    have h8 : (0 : ℝ) < ε / 8 := by linarith
    obtain ⟨g00, hg00c, hg00e⟩ := niceSD_approx_scalar _ hf00 h8
    obtain ⟨g01, hg01c, hg01e⟩ := niceSD_approx_scalar _ hf01 h8
    obtain ⟨g11, hg11c, hg11e⟩ := niceSD_approx_scalar _ hf11 h8
    have hg00m : Measurable g00 := hg00c.continuous.measurable
    have hg01m : Measurable g01 := hg01c.continuous.measurable
    have hg11m : Measurable g11 := hg11c.continuous.measurable
    have hm00 : Measurable fun p => ‖F p 0 0 - g00 p‖ := ((hmeas 0 0).sub hg00m).norm
    have hm01 : Measurable fun p => ‖F p 0 1 - g01 p‖ := ((hmeas 0 1).sub hg01m).norm
    have hm11 : Measurable fun p => ‖F p 1 1 - g11 p‖ := ((hmeas 1 1).sub hg11m).norm
    have hn00 : eLpNorm (fun p => ‖F p 0 0 - g00 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ)))
        ≤ ENNReal.ofReal (ε / 8) := by
      rw [eLpNorm_norm]
      exact hg00e
    have hn01 : eLpNorm (fun p => ‖F p 0 1 - g01 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ)))
        ≤ ENNReal.ofReal (ε / 8) := by
      rw [eLpNorm_norm]
      exact hg01e
    have hn11 : eLpNorm (fun p => ‖F p 1 1 - g11 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ)))
        ≤ ENNReal.ofReal (ε / 8) := by
      rw [eLpNorm_norm]
      exact hg11e
    -- the symmetric smooth field `G = χ · g`
    obtain ⟨G, hGdef⟩ : ∃ G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
        G = fun p i j => ((χ p : ℝ) : ℂ) * ![![g00, g01], ![g01, g11]] i j p := ⟨_, rfl⟩
    have hGval : ∀ p i j, G p i j = ((χ p : ℝ) : ℂ) * ![![g00, g01], ![g01, g11]] i j p := by
      intro p i j
      rw [hGdef]
    have hGsym : ∀ p i j, G p i j = G p j i := by
      intro p i j
      rw [hGval, hGval]
      fin_cases i <;> fin_cases j <;> simp
    have hMsm : ∀ i j : Fin 2, ContDiff ℝ ∞ (![![g00, g01], ![g01, g11]] i j) := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hg00c, hg01c, hg11c]
    have hχC : ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => ((χ p : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp hχsm
    have hGsm : ∀ i j, ContDiff ℝ ∞ fun p => G p i j := by
      intro i j
      simp only [hGval]
      exact hχC.mul (hMsm i j)
    have hGvan : ∀ s x i j, (s < α / 2 ∨ β + 1 < s ∨ r' < |x.1| ∨ R + 1 < |x.2|) →
        G (s, x) i j = 0 := by
      intro s x i j h
      rw [hGval, hχzero s x h, Complex.ofReal_zero, zero_mul]
    refine ⟨G, hGsym, hGsm, hGvan, ?_⟩
    have hpt : ∀ p : ℝ × (ℝ × ℝ),
        ‖tnorm2 (fun i j => G p i j - F p i j)‖ ≤
          ‖F p 0 0 - g00 p‖ + ‖F p 0 1 - g01 p‖ + ‖F p 0 1 - g01 p‖ + ‖F p 1 1 - g11 p‖ := by
      intro p
      have hT : tnorm2 (fun i j => G p i j - F p i j) ≤
          ‖G p 0 0 - F p 0 0‖ + ‖G p 0 1 - F p 0 1‖ + ‖G p 1 0 - F p 1 0‖
            + ‖G p 1 1 - F p 1 1‖ :=
        niceSD_tnorm2_le (fun i j => G p i j - F p i j)
      have e00 : ‖G p 0 0 - F p 0 0‖ ≤ ‖F p 0 0 - g00 p‖ :=
        niceSD_D_le (χ p) (hχ01 p).1 (hχ01 p).2 _ _ _ (hcut p 0 0) (hGval p 0 0)
      have e01 : ‖G p 0 1 - F p 0 1‖ ≤ ‖F p 0 1 - g01 p‖ :=
        niceSD_D_le (χ p) (hχ01 p).1 (hχ01 p).2 _ _ _ (hcut p 0 1) (hGval p 0 1)
      have e11 : ‖G p 1 1 - F p 1 1‖ ≤ ‖F p 1 1 - g11 p‖ :=
        niceSD_D_le (χ p) (hχ01 p).1 (hχ01 p).2 _ _ _ (hcut p 1 1) (hGval p 1 1)
      have e10 : ‖G p 1 0 - F p 1 0‖ = ‖G p 0 1 - F p 0 1‖ := by
        rw [hGsym p 1 0, hsym p 1 0]
      rw [Real.norm_of_nonneg (niceSD_tnorm2_nonneg _)]
      linarith
    have key : ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8)
        + ENNReal.ofReal (ε / 8) = ENNReal.ofReal (ε / 2) := by
      have h8' : (0 : ℝ) ≤ ε / 8 := by linarith
      rw [← ENNReal.ofReal_add h8' h8', ← ENNReal.ofReal_add (add_nonneg h8' h8') h8',
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg h8' h8') h8') h8']
      congr 1
      ring
    calc eLpNorm (fun p => tnorm2 (fun i j => G p i j - F p i j)) 2
          (volume : Measure (ℝ × (ℝ × ℝ)))
        ≤ eLpNorm (fun p => ‖F p 0 0 - g00 p‖ + ‖F p 0 1 - g01 p‖ + ‖F p 0 1 - g01 p‖
            + ‖F p 1 1 - g11 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ))) :=
          eLpNorm_mono_real hpt
      _ ≤ eLpNorm (fun p => ‖F p 0 0 - g00 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ)))
          + eLpNorm (fun p => ‖F p 0 1 - g01 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ)))
          + eLpNorm (fun p => ‖F p 0 1 - g01 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ)))
          + eLpNorm (fun p => ‖F p 1 1 - g11 p‖) 2 (volume : Measure (ℝ × (ℝ × ℝ))) :=
          niceSD_eLpNorm_four hm00 hm01 hm01 hm11
      _ ≤ ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8)
          + ENNReal.ofReal (ε / 8) :=
          add_le_add (add_le_add (add_le_add hn00 hn01) hn01) hn11
      _ = ENNReal.ofReal (ε / 2) := key
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

end UnforcedLeray.Short.IIIa
