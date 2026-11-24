import UnforcedLeray.Units.B0221.Consistency

/-!
# B0221 helper: smooth band-supported profiles and their images under `A_ε` lie in `H`

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346; the space
`H = L²(s^{-3/2} ds dq dη)` is that of B0220 (tex lines 3304–3307).

`conjOp_eq_Aeps` (file `Consistency.lean`) takes the `H`-classes of a test profile `b` and of
`A_ε b` as inputs. This file shows that these classes exist, so that statement is never vacuous:
a `C²` profile on the open age half-space `s > 0` whose support lies in an age band
`s ∈ [s₀, S₁]` (`s₀ > 0`) and a bounded range `|η| ≤ Z` is in `H` (`memLp_testProfile`), and so
is `A_ε b` (`memLp_Aeps_testProfile`), because `A_ε b` is continuous on `s > 0`
(`continuousOn_Aeps`) and vanishes where `b` vanishes near the point (`Aeps_support`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal
open UnforcedLeray.B0220

namespace UnforcedLeray.B0221

/-- The open age half-space `s > 0` is open. -/
theorem isOpen_agePos : IsOpen {p : Profile | 0 < p.1} :=
  isOpen_lt continuous_const continuous_fst

/-- The compact box `[s₀, S₁] × [0, c] × [-Z, Z]` containing the support of a test profile
inside one `q`-cell. -/
def bandBox (s0 S1 c Z : ℝ) : Set Profile := Icc s0 S1 ×ˢ (Icc 0 c ×ˢ Icc (-Z) Z)

theorem isCompact_bandBox (s0 S1 c Z : ℝ) : IsCompact (bandBox s0 S1 c Z) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- The box has finite `H`-measure: on it the weight `s^{-3/2}` is at most `s₀^{-3/2}`. -/
theorem measureH_bandBox_lt_top {c s0 S1 Z : ℝ} (hs0 : 0 < s0) :
    measureH c (bandBox s0 S1 c Z) < ∞ := by
  have hK := isCompact_bandBox s0 S1 c Z
  have hKm : MeasurableSet (bandBox s0 S1 c Z) := hK.isClosed.measurableSet
  rw [measureH, withDensity_apply _ hKm]
  calc ∫⁻ p in bandBox s0 S1 c Z, weightH p ∂cellMeasure c
      ≤ ∫⁻ _ in bandBox s0 S1 c Z, ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) ∂cellMeasure c := by
        refine setLIntegral_mono measurable_const fun p hp => ?_
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hp.1.1 (by norm_num))
    _ = ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) * cellMeasure c (bandBox s0 S1 c Z) :=
        setLIntegral_const _ _
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        calc cellMeasure c (bandBox s0 S1 c Z) ≤ volume (bandBox s0 S1 c Z) :=
              Measure.restrict_apply_le _ _
          _ < ∞ := hK.measure_lt_top

/-- A function continuous on `s > 0` and supported in the band `s ∈ [s₀, S₁]`, `|η| ≤ Z`
(`s₀ > 0`) lies in `H = L²(s^{-3/2} ds dq dη)`. -/
theorem memLp_measureH_of_band {c s0 S1 Z : ℝ} (hs0 : 0 < s0) {f : Profile → ℝ}
    (hf : ContinuousOn f {p | 0 < p.1})
    (hsupp : ∀ p : Profile, 0 < p.1 → f p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z) :
    MemLp f 2 (measureH c) := by
  set K := bandBox s0 S1 c Z with hK_def
  have hK : IsCompact K := isCompact_bandBox s0 S1 c Z
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKpos : K ⊆ {p | 0 < p.1} := fun p hp => hs0.trans_le hp.1.1
  have hfK : ContinuousOn f K := hf.mono hKpos
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hfK
  have hind : K.indicator f =ᵐ[measureH c] f := by
    filter_upwards [ae_cell_measureH c] with p hp
    by_cases hp0 : f p = 0
    · simp [hp0]
    · obtain ⟨h1, h2⟩ := hsupp p hp.1 hp0
      have hpK : p ∈ K := ⟨h1, ⟨hp.2.1.1.le, hp.2.1.2⟩, abs_le.1 h2⟩
      exact indicator_of_mem hpK f
  refine (memLp_congr_ae hind).1 ?_
  rw [memLp_indicator_iff_restrict hKm]
  have : IsFiniteMeasure ((measureH c).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measureH_bandBox_lt_top hs0⟩
  refine MemLp.of_bound (hfK.aestronglyMeasurable hKm) M ?_
  filter_upwards [ae_restrict_mem hKm] with p hp
  exact hM p hp

/-- `A_ε b` is continuous on `s > 0` when `b` is `C²` there. -/
theorem continuousOn_Aeps (ν ε : ℝ) {b : Profile → ℝ} (hb : ContDiffOn ℝ 2 b {p | 0 < p.1}) :
    ContinuousOn (Aeps ν ε b) {p | 0 < p.1} := by
  have hU := isOpen_agePos
  have h0 : ContinuousOn b {p | 0 < p.1} := hb.continuousOn
  have h1 : ContinuousOn (fderiv ℝ b) {p | 0 < p.1} :=
    hb.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ b)) {p | 0 < p.1} :=
    (hb.fderiv_of_isOpen (m := 1) hU (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  have hD1 : ∀ v : Profile, ContinuousOn (fun p => fderiv ℝ b p v) {p | 0 < p.1} :=
    fun v => h1.clm_apply continuousOn_const
  have hD2 : ∀ v w : Profile,
      ContinuousOn (fun p => fderiv ℝ (fderiv ℝ b) p v w) {p | 0 < p.1} :=
    fun v w => (h2.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hfst : ContinuousOn (fun p : Profile => p.1) {p | 0 < p.1} :=
    continuous_fst.continuousOn
  have hthd : ContinuousOn (fun p : Profile => p.2.2) {p | 0 < p.1} :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hS := hD1 eS
  have hQ := hD1 eQ
  have hE := hD1 eEta
  have hQQ := hD2 eQ eQ
  have hQS := hD2 eQ eS
  have hQE := hD2 eQ eEta
  have hSQ := hD2 eS eQ
  have hSS := hD2 eS eS
  have hSE := hD2 eS eEta
  have hEQ := hD2 eEta eQ
  have hES := hD2 eEta eS
  have hEE := hD2 eEta eEta
  refine ContinuousOn.congr ?_ fun p hp => Aeps_expand ν ε (hb.contDiffAt (hU.mem_nhds hp))
  fun_prop

/-- `A_ε b` vanishes off the support band of `b`: if `b` is `C²` on `s > 0` and supported in
`s ∈ [s₀, S₁]`, `|η| ≤ Z`, so is `A_ε b`. -/
theorem Aeps_support (ν ε : ℝ) {b : Profile → ℝ} {s0 S1 Z : ℝ}
    (hb : ContDiffOn ℝ 2 b {p | 0 < p.1})
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z) :
    ∀ p : Profile, 0 < p.1 → Aeps ν ε b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z := by
  intro p hp hA
  by_contra hout
  set O : Set Profile :=
    {p | 0 < p.1} ∩ (({p | p.1 < s0} ∪ {p | S1 < p.1}) ∪ {p | Z < |p.2.2|}) with hO_def
  have hO : IsOpen O :=
    isOpen_agePos.inter (((isOpen_lt continuous_fst continuous_const).union
      (isOpen_lt continuous_const continuous_fst)).union
      (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hzero : ∀ p' ∈ O, b p' = 0 := by
    rintro p' ⟨h0, h⟩
    by_contra hne
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsupp p' h0 hne
    rcases h with (h | h) | h <;> simp only [mem_ofPred_eq] at h <;> linarith
  have hpO : p ∈ O := by
    refine ⟨hp, ?_⟩
    simp only [mem_Icc, not_and_or, not_le] at hout
    rcases hout with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hev : b =ᶠ[𝓝 p] fun _ => (0 : ℝ) := eventually_of_mem (hO.mem_nhds hpO) hzero
  have h1 : b p = 0 := hzero p hpO
  have h2 : fderiv ℝ b p = 0 := by rw [hev.fderiv_eq]; simp
  have h3 : fderiv ℝ (fderiv ℝ b) p = 0 := by rw [hev.fderiv.fderiv_eq]; simp
  apply hA
  rw [Aeps_expand ν ε (hb.contDiffAt (isOpen_agePos.mem_nhds hp)), h1, h2, h3]
  simp

/-- A `C²` profile supported in the band `s ∈ [s₀, S₁]`, `|η| ≤ Z` (`s₀ > 0`) lies in `H`. -/
theorem memLp_testProfile {c s0 S1 Z : ℝ} (hs0 : 0 < s0) {b : Profile → ℝ}
    (hb : ContDiffOn ℝ 2 b {p | 0 < p.1})
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z) :
    MemLp b 2 (measureH c) :=
  memLp_measureH_of_band hs0 hb.continuousOn hsupp

/-- For such a profile, `A_ε b` lies in `H`. -/
theorem memLp_Aeps_testProfile (ν ε : ℝ) {c s0 S1 Z : ℝ} (hs0 : 0 < s0) {b : Profile → ℝ}
    (hb : ContDiffOn ℝ 2 b {p | 0 < p.1})
    (hsupp : ∀ p : Profile, 0 < p.1 → b p ≠ 0 → p.1 ∈ Icc s0 S1 ∧ |p.2.2| ≤ Z) :
    MemLp (Aeps ν ε b) 2 (measureH c) :=
  memLp_measureH_of_band hs0 (continuousOn_Aeps ν ε hb) (Aeps_support ν ε hb hsupp)

end UnforcedLeray.B0221
